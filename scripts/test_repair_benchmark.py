"""Feedback isolation and corrupted-log controls; no model calls."""
import copy
import json
from pathlib import Path
import random
import shutil
import tempfile
import unittest

from grouping_reference import evaluate
from grouping_tool import load_receipt, read_json, result_record, sha256
from repair_tasks import build_dataset, encode, grade, solve
from run_repair_benchmark import (
    DATASET, PROTOCOL, RECEIPT, check_artifacts, check_header, parse_events,
    prompt_for, proposal_feedback, register_thread, replay, source_manifest, summarize, write_json,
)


TASK = {"id": "example", "operation": [0, 2, 2, 3],
        "initial_labels": [0, 0, 1, 2], "separate": [0, 3]}


def native(labels, task=TASK):
    word = encode(task["operation"], labels)
    return {"word": word, **evaluate(word)}


def events(answer, extra=None):
    rows = [{"type": "thread.started", "thread_id": "fixture"}, {"type": "turn.started"}]
    if extra:
        rows.append(extra)
    rows.extend([
        {"type": "item.completed", "item": {"type": "agent_message", "text": json.dumps(answer)}},
        {"type": "turn.completed", "usage": {"input_tokens": 10, "output_tokens": 4}},
    ])
    return "\n".join(map(json.dumps, rows))


class FeedbackTests(unittest.TestCase):
    def test_only_witness_differs_for_failed_preservation(self):
        for task in build_dataset()["tasks"]:
            answer = {"status": "repair", "group_labels": task["initial_labels"]}
            row = native(task["initial_labels"], task)
            plain = proposal_feedback(task, answer, "pass_fail", row)
            detailed = proposal_feedback(task, answer, "counterexample", row)
            witness = detailed.pop("violating_pair")
            self.assertEqual(plain, detailed)
            a, b = witness
            g, f = task["initial_labels"], task["operation"]
            self.assertEqual(g[a], g[b])
            self.assertNotEqual(g[f[a]], g[f[b]])

    def test_constraint_feedback_identical_in_both_arms(self):
        for answer in ({"status": "repair", "group_labels": [0, 1, 2, 3]},
                       {"status": "repair", "group_labels": [0, 0, 0, 0]},
                       {"status": "repair", "group_labels": [False, 0, 1, 2]},
                       {"status": "repair", "group_labels": [0, 0, 1, 2], "operation": [0]*4}):
            plain = proposal_feedback(TASK, answer, "pass_fail")
            self.assertIn("constraint_error", plain)
            self.assertEqual(plain, proposal_feedback(TASK, answer, "counterexample"))

    def test_impossible_does_not_leak_oracle(self):
        for task in build_dataset()["tasks"]:
            for arm in ("pass_fail", "counterexample"):
                self.assertEqual(proposal_feedback(task, {"status": "impossible", "group_labels": None}, arm),
                                 {"terminal": True})

    def test_legal_repair_requires_matching_native_result(self):
        answer = {"status": "repair", "group_labels": [0, 0, 0, 2]}
        with self.assertRaises(ValueError):
            proposal_feedback(TASK, answer, "pass_fail")
        with self.assertRaises(ValueError):
            proposal_feedback(TASK, answer, "pass_fail", native([0, 0, 1, 2]))
        row = native(answer["group_labels"])
        self.assertTrue(proposal_feedback(TASK, answer, "pass_fail", row)["accepted"])
        row["preserves"] = False
        with self.assertRaises(ValueError):
            proposal_feedback(TASK, answer, "pass_fail", row)

    def test_prompt_excludes_oracle_and_other_tasks(self):
        task = copy.deepcopy(build_dataset()["tasks"][0])
        task["oracle"]["private_fixture"] = "oracle fixture excluded from prompts"
        prompt = prompt_for(task, [])
        self.assertNotIn("oracle fixture excluded from prompts", prompt)
        self.assertNotIn('"oracle"', prompt)
        self.assertNotIn('"split"', prompt)
        self.assertNotIn('"answer_class"', prompt)


class EventTests(unittest.TestCase):
    def test_fresh_thread_required_for_every_decision(self):
        seen = set()
        source = events({"status": "impossible", "group_labels": None})
        register_thread(source, seen)
        with self.assertRaisesRegex(ValueError, "reused"):
            register_thread(source, seen)
        register_thread(source.replace('"fixture"', '"different"'), seen)
        for value in ('null', '""', '7'):
            with self.assertRaises(ValueError):
                parse_events(source.replace('"fixture"', value))

    def test_valid_events(self):
        answer = {"status": "repair", "group_labels": [0, 0, 0, 2]}
        self.assertEqual(parse_events(events(answer)), (answer, {"input_tokens": 10, "output_tokens": 4}))

    def test_any_tool_use_invalidates_trial(self):
        for kind in ("command_execution", "mcp_tool_call", "web_search", "file_change"):
            with self.assertRaises(ValueError):
                parse_events(events({}, {"type": "item.started", "item": {"type": kind}}))

    def test_error_incomplete_duplicate_and_non_json(self):
        source = events({"status": "impossible", "group_labels": None})
        for text in (source + '\n{"type":"turn.completed"}',
                     source + '\n{"type":"turn.started"}',
                     source + '\n{"type":"turn.failed"}',
                     "\n".join(source.splitlines()[:-1]),
                     source.replace('\\"impossible\\"', 'undefined')):
            with self.assertRaises((ValueError, json.JSONDecodeError)):
                parse_events(text)
        rows = [json.loads(s) for s in source.splitlines()]
        rows[2]["item"]["text"] = '{"status":"repair","status":"impossible","group_labels":null}'
        with self.assertRaises(ValueError):
            parse_events("\n".join(map(json.dumps, rows)))


class ReplayIntegrityTests(unittest.TestCase):
    def test_complete_replay_and_semantic_corruption_controls(self):
        """Synthetic transcripts exercise multi-decision replay, without model calls."""
        cached = load_receipt(RECEIPT)
        tasks = [t for t in read_json(DATASET)["tasks"] if t["split"] == "dev"]
        order = [(t, a) for t in tasks for a in ("pass_fail", "counterexample")]
        random.Random(read_json(PROTOCOL)["trial_order_seed"] + ":dev").shuffle(order)
        def record(task, labels):
            word = encode(task["operation"], labels)
            return result_record(word, RECEIPT, cached[0], cached[1][word], cached[2])
        def seal(root, header):
            header["artifacts"] = {p.relative_to(root).as_posix(): sha256(p)
                                   for p in root.rglob("*") if p.is_file() and p.name != "run.json"}
            write_json(root / "run.json", header)
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "fixture"
            root.mkdir()
            trials = []
            for i, (task, arm) in enumerate(order):
                initial_answer = {"status": "repair", "group_labels": task["initial_labels"]}
                initial_row = cached[1][encode(task["operation"], task["initial_labels"]) ]
                history = [{"initial_feedback": proposal_feedback(task, initial_answer, arm, initial_row)}]
                solutions = solve(task)
                correct_answer = ({"status": "repair", "group_labels": solutions[0]} if solutions
                                  else {"status": "impossible", "group_labels": None})
                trial = {"task_id": task["id"], "arm": arm, "satisfiable": bool(solutions),
                         "initial_record": record(task, task["initial_labels"]),
                         "decisions": [], "first_correct": False, "correct": True}
                for n, answer in enumerate((initial_answer, correct_answer)):
                    directory = root / f"trial-{i:02d}/decision-{n}"
                    directory.mkdir(parents=True)
                    event_text = events(answer).replace('"fixture"', f'"fixture-{i}-{n}"')
                    _, usage = parse_events(event_text)
                    labels = answer["group_labels"]
                    row = cached[1][encode(task["operation"], labels)] if labels is not None else None
                    feedback = proposal_feedback(task, answer, arm, row)
                    process = {"returncode": 0, "elapsed_seconds": 0}
                    decision = {"answer": answer, "grade": grade(task, answer), "feedback": feedback,
                                "native_record": record(task, labels) if labels is not None else None,
                                "usage": usage, "process": process}
                    (directory / "prompt.txt").write_text(prompt_for(task, history), encoding="utf-8")
                    (directory / "events.jsonl").write_text(event_text, encoding="utf-8")
                    (directory / "stderr.txt").write_text("", encoding="utf-8")
                    write_json(directory / "process.json", process)
                    trial["decisions"].append(decision)
                    history.append({"answer": answer, "feedback": feedback})
                write_json(root / f"trial-{i:02d}/trial.json", trial)
                trials.append(trial)
            header = {"schema_version": 1, "experiment_id": "merge-repair-v1",
                      "passed_integrity": True, "source_manifest": source_manifest(),
                      "receipt_sha256": sha256(RECEIPT), "binary_sha256": cached[0]["binary"]["sha256"],
                      "source_tree_dirty": False, "auth_mode": "ChatGPT", "split": "dev",
                      "trial_order": [[t["id"], arm] for t, arm in order], "summary": summarize(trials)}
            seal(root, header)
            self.assertEqual(replay(root), header["summary"])
            for mutation in ("grade", "feedback", "prompt", "usage", "native", "reused_thread"):
                with self.subTest(mutation=mutation):
                    copy_root = Path(temp) / mutation
                    shutil.copytree(root, copy_root)
                    path = copy_root / "trial-00/trial.json"
                    trial = read_json(path)
                    if mutation == "grade":
                        trial["decisions"][0]["grade"]["correct"] = True
                    elif mutation == "feedback":
                        trial["decisions"][0]["feedback"]["accepted"] = True
                    elif mutation == "usage":
                        trial["decisions"][0]["usage"]["input_tokens"] += 1
                    elif mutation == "native":
                        trial["initial_record"]["input"]["word"] = 0
                    elif mutation == "prompt":
                        (copy_root / "trial-00/decision-0/prompt.txt").write_text("leaked oracle", encoding="utf-8")
                    else:
                        event_path = copy_root / "trial-00/decision-1/events.jsonl"
                        event_path.write_text(event_path.read_text(encoding="utf-8").replace("fixture-0-1", "fixture-0-0"), encoding="utf-8")
                    write_json(path, trial)
                    seal(copy_root, copy.deepcopy(header))
                    with self.assertRaises(ValueError):
                        replay(copy_root)

    def test_header_binds_binary_order_and_frozen_sources(self):
        protocol = read_json(PROTOCOL)
        order = [(t["id"], a) for t in read_json(DATASET)["tasks"] if t["split"] == "test"
                 for a in protocol["arms"]]
        random.Random(protocol["trial_order_seed"] + ":test").shuffle(order)
        header = {"schema_version": 1, "experiment_id": protocol["experiment_id"],
                  "passed_integrity": True, "source_manifest": source_manifest(),
                  "receipt_sha256": sha256(RECEIPT), "binary_sha256": "fixture-digest",
                  "source_tree_dirty": False, "auth_mode": "ChatGPT", "split": "test",
                  "trial_order": order}
        check_header(header, "fixture-digest")
        mutations = {"binary_sha256": "wrong", "receipt_sha256": "wrong",
                     "source_manifest": {}, "source_tree_dirty": True,
                     "trial_order": list(reversed(order)), "split": "unknown",
                     "passed_integrity": False, "experiment_id": "other", "auth_mode": "API"}
        for key, value in mutations.items():
            with self.subTest(key=key), self.assertRaises(ValueError):
                check_header({**header, key: value}, "fixture-digest")

    def test_artifact_manifest_cannot_omit_or_add_files(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            directory = root / "trial-00/decision-0"
            directory.mkdir(parents=True)
            for name in ("prompt.txt", "events.jsonl", "stderr.txt", "process.json"):
                (directory / name).write_text("fixture", encoding="utf-8")
            write_json(root / "trial-00/trial.json", {"decisions": [{}]})
            write_json(root / "run.json", {})
            header = {"trial_order": [["fixture", "pass_fail"]], "artifacts": {
                p.relative_to(root).as_posix(): sha256(p) for p in root.rglob("*")
                if p.is_file() and p.name != "run.json"}}
            check_artifacts(root, header)
            for manifest in ({}, {**header["artifacts"], "../escape": "wrong"}):
                with self.assertRaises(ValueError):
                    check_artifacts(root, {**header, "artifacts": manifest})
            (directory / "prompt.txt").write_text("changed", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "hash mismatch"):
                check_artifacts(root, header)
            (root / "unexpected.txt").write_text("extra", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "unexpected"):
                check_artifacts(root, header)


if __name__ == "__main__":
    unittest.main()
