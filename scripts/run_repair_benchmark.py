"""Local Codex/ChatGPT repair pilot. No API key, credential copying, or paid CI job.

Run consumes the signed-in user's Codex allowance. Replay performs no model calls.
Every accepted repair is checked with the native binary identified by the receipt.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import random
import re
import shutil
import subprocess
import tempfile
import time

from grouping_tool import load_receipt, read_json, result_record, sha256, validate_result
from repair_tasks import build_dataset, encode, grade, public_task, solve

ROOT = Path(__file__).resolve().parents[1]
DATASET = ROOT / "benchmarks/repair-v1/tasks.json"
PROTOCOL = ROOT / "benchmarks/repair-v1/protocol.json"
RECEIPT = ROOT / "evidence/grouping-checker-v1/summary.json"
ANSWER_SCHEMA = {
    "type": "object", "additionalProperties": False,
    "properties": {
        "status": {"type": "string", "enum": ["repair", "impossible"]},
        "group_labels": {"anyOf": [
            {"type": "array", "items": {"type": "integer", "minimum": 0, "maximum": 3},
             "minItems": 4, "maxItems": 4}, {"type": "null"}]},
    }, "required": ["status", "group_labels"],
}
INSTRUCTIONS = """Solve this finite grouping repair task. Objects are 0,1,2,3.
operation[x] is the fixed output of object x. Equal group labels mean together.
A grouping g respects the rule exactly when, for every x,y, g[x]=g[y] implies
g[operation[x]]=g[operation[y]]. The initial grouping fails this condition.
You may merge whole original groups, but you may never split an original group:
initial_labels[x]=initial_labels[y] must imply new_labels[x]=new_labels[y].
The two objects in separate MUST remain in different groups. The rule cannot change.
Return {"status":"repair","group_labels":[four integers 0..3]} if a valid repair
exists, or {"status":"impossible","group_labels":null} if no permitted repair
exists. Impossibility is a final answer, not an oracle query. Labels need not be
consecutive. You have at most three decisions; a rejected repair receives feedback.
Use only the task and feedback below. Do not use tools, files, network, or other
agents. Return only the JSON answer, without a rationale or Markdown.
"""


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8", newline="\n")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def source_manifest() -> dict:
    paths = [DATASET, PROTOCOL, Path(__file__), ROOT / "scripts/repair_tasks.py"]
    return {p.relative_to(ROOT).as_posix(): sha256(p) for p in paths}


def proposal_feedback(task, answer, arm, row=None) -> dict:
    """Arms differ only in the native preservation witness, never in oracle truth."""
    require(arm in ("pass_fail", "counterexample"), "unknown arm")
    assessed = grade(task, answer)
    reason = assessed["reason"]
    # The grader's satisfiability judgement must never reach model feedback.
    if isinstance(answer, dict) and answer.get("status") == "impossible":
        return {"terminal": True}
    labels = answer.get("group_labels") if isinstance(answer, dict) else None
    well_formed = (isinstance(answer, dict) and set(answer) == {"status", "group_labels"}
                   and answer["status"] == "repair" and type(labels) is list
                   and len(labels) == 4 and all(type(x) is int and 0 <= x < 4 for x in labels))
    if not well_formed:
        return {"accepted": False, "constraint_error": "invalid_answer"}
    old = task["initial_labels"]
    if any(old[x] == old[y] and labels[x] != labels[y] for x in range(4) for y in range(4)):
        return {"accepted": False, "constraint_error": "split_original_group"}
    x, y = task["separate"]
    if labels[x] == labels[y]:
        return {"accepted": False, "constraint_error": "required_separation_lost"}
    require(row is not None, "native row required for a legal repair")
    require(row["word"] == encode(task["operation"], labels), "native row refers to a different proposal")
    feedback = {"accepted": row["preserves"], "preserves": row["preserves"]}
    if not row["preserves"] and arm == "counterexample":
        feedback["violating_pair"] = row["violating_pair"]
    require(assessed["correct"] == row["preserves"], f"oracle/native disagreement: {reason}")
    return feedback


def prompt_for(task, history: list) -> str:
    return INSTRUCTIONS + "\n" + json.dumps({"task": public_task(task), "history": history}, sort_keys=True)


def register_thread(text: str, seen: set[str]) -> None:
    events = [json.loads(line) for line in text.splitlines() if line.strip()]
    threads = [e.get("thread_id") for e in events if e.get("type") == "thread.started"]
    require(len(threads) == 1 and isinstance(threads[0], str) and bool(threads[0]),
            "expected one identified fresh thread")
    require(threads[0] not in seen, "thread reused across decisions")
    seen.add(threads[0])


def parse_events(text: str) -> tuple[dict, dict]:
    events = [json.loads(line) for line in text.splitlines() if line.strip()]
    register_thread(text, set())
    require(sum(e.get("type") == "turn.started" for e in events) == 1, "expected one started turn")
    require(sum(e.get("type") == "turn.completed" for e in events) == 1, "expected one completed turn")
    require(not any(e.get("type") in ("error", "turn.failed") for e in events), "model turn failed")
    messages = []
    for event in events:
        if event.get("type", "").startswith("item."):
            item = event.get("item", {})
            require(item.get("type") in ("agent_message", "reasoning"),
                    "tool use or error invalidates a no-tools trial")
            if event["type"] == "item.completed" and item["type"] == "agent_message":
                messages.append(item["text"])
    require(len(messages) == 1, "expected one final JSON answer")
    def unique(items):
        result = {}
        for key, value in items:
            require(key not in result, "duplicate answer key")
            result[key] = value
        return result
    answer = json.loads(messages[0], object_pairs_hook=unique)
    usage = next(e.get("usage", {}) for e in events if e["type"] == "turn.completed")
    return answer, usage


class NativeChecker:
    def __init__(self, binary, wsl=None):
        self.binary = binary.resolve()
        self.cached = load_receipt(RECEIPT)
        self.digest = sha256(self.binary)
        require(self.digest == self.cached[0]["binary"]["sha256"], "binary does not match receipt")
        self.command = [str(self.binary)]
        if wsl:
            path = self.binary.as_posix()
            require(re.match(r"^[A-Za-z]:/", path) is not None, "WSL needs a Windows drive path")
            self.command = ["wsl", "-d", wsl, "--exec", "/mnt/" + path[0].lower() + path[2:]]

    def check(self, word):
        process = subprocess.run(self.command + [str(word)], capture_output=True,
                                 text=True, encoding="utf-8", timeout=30)
        require(process.returncode == 0 and not process.stderr.strip(), "native invocation failed")
        row = json.loads(process.stdout)
        require(row == self.cached[1][word], "native output differs from exhaustive receipt")
        record = result_record(word, RECEIPT, self.cached[0], row, self.cached[2])
        validate_result(record, self.cached)
        return row, record

    def finish(self):
        require(sha256(self.binary) == self.digest, "binary changed during run")


def model_command(executable, model, effort, cwd, schema):
    command = [executable, "exec", "--ignore-user-config", "--ephemeral",
               "--skip-git-repo-check", "--sandbox", "read-only", "-C", str(cwd),
               "-c", "model=" + json.dumps(model),
               "-c", "model_reasoning_effort=" + json.dumps(effort),
               "-c", "project_doc_max_bytes=0", "-c", 'web_search="disabled"']
    for feature in ("shell_tool", "unified_exec", "multi_agent", "plugins", "apps"):
        command += ["--disable", feature]
    return command + ["--output-schema", str(schema), "--json", "-"]


def run_model(command, prompt, directory, timeout):
    env = dict(os.environ)
    # Preserve the user's native auth store; remove parent-session routing only.
    for key in ("CODEX_THREAD_ID", "CODEX_SESSION_ID", "CODEX_TOOL_CALL_ID",
                "CODEX_APP_TOOLS_PIPE_PATH", "CODEX_INTERNAL_ORIGINATOR_OVERRIDE"):
        env.pop(key, None)
    directory.mkdir()
    (directory / "prompt.txt").write_text(prompt, encoding="utf-8", newline="\n")
    start = time.monotonic()
    try:
        process = subprocess.run(command, input=prompt, capture_output=True, text=True,
                                 encoding="utf-8", env=env, timeout=timeout)
        stdout, stderr, code = process.stdout, process.stderr, process.returncode
    except subprocess.TimeoutExpired as exc:
        def decoded(value):
            return value.decode("utf-8", errors="replace") if isinstance(value, bytes) else value or ""
        stdout, stderr, code = decoded(exc.stdout), decoded(exc.stderr), None
    (directory / "events.jsonl").write_text(stdout, encoding="utf-8", newline="\n")
    (directory / "stderr.txt").write_text(stderr, encoding="utf-8", newline="\n")
    meta = {"returncode": code, "elapsed_seconds": round(time.monotonic() - start, 3)}
    write_json(directory / "process.json", meta)
    require(code == 0, "Codex failed or timed out; logs retained, no automatic retry")
    return (*parse_events(stdout), meta)


def summarize(trials):
    result = {}
    for arm in ("pass_fail", "counterexample"):
        rows = [t for t in trials if t["arm"] == arm]
        result[arm] = {"trials": len(rows), "first_correct": sum(t["first_correct"] for t in rows),
                       "final_correct": sum(t["correct"] for t in rows),
                       "model_calls": sum(len(t["decisions"]) for t in rows)}
        result[arm]["by_satisfiability"] = {
            label: {"trials": sum(t["satisfiable"] == value for t in rows),
                    "first_correct": sum(t["first_correct"] for t in rows if t["satisfiable"] == value),
                    "final_correct": sum(t["correct"] for t in rows if t["satisfiable"] == value)}
            for label, value in (("sat", True), ("unsat", False))}
        result[arm]["reported_usage"] = dict(sum(
            (Counter(d["usage"]) for t in rows for d in t["decisions"]), Counter()))
        result[arm]["constraint_violations"] = sum(
            "constraint_error" in d["feedback"] for t in rows for d in t["decisions"])
        result[arm]["false_impossibility_claims"] = sum(
            isinstance(d["answer"], dict) and d["answer"].get("status") == "impossible"
            and not d["grade"]["correct"] for t in rows for d in t["decisions"])
    pairs = {t["task_id"]: {} for t in trials}
    for trial in trials:
        pairs[trial["task_id"]][trial["arm"]] = trial["first_correct"]
    require(all(set(v) == {"pass_fail", "counterexample"} for v in pairs.values()), "incomplete paired trial")
    result["paired_first_decision"] = dict(Counter(
        "both_correct" if all(v.values()) else "both_wrong" if not any(v.values()) else
        "counterexample_only" if v["counterexample"] else "pass_fail_only" for v in pairs.values()))
    return result


def run(args):
    require(not args.out.exists(), "choose a new output directory")
    require(read_json(DATASET) == build_dataset(), "dataset is stale")
    protocol = read_json(PROTOCOL)
    dataset = read_json(DATASET)
    tasks = [t for t in dataset["tasks"] if t["split"] == args.split]
    require(bool(tasks), "empty split")
    dirty = bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True).strip())
    require(args.split != "test" or not dirty, "commit the frozen protocol and implementation before test runs")
    executable = shutil.which("codex")
    require(executable is not None, "Codex CLI not found")
    auth = subprocess.run([executable, "login", "status"], capture_output=True, text=True, timeout=20)
    require(auth.returncode == 0 and "Logged in using ChatGPT" in auth.stdout + auth.stderr,
            "this runner requires existing ChatGPT login; it does not provision or reuse API keys")
    version = subprocess.check_output([executable, "--version"], text=True, timeout=20).strip()
    checker = NativeChecker(args.binary, args.wsl_distribution)
    args.out.mkdir(parents=True)
    manifest = source_manifest()
    global_instructions = Path(os.environ.get("CODEX_HOME", str(Path.home() / ".codex"))) / "AGENTS.md"
    inherited = {"present": global_instructions.exists(),
                 "sha256": sha256(global_instructions) if global_instructions.exists() else None,
                 "bytes": global_instructions.stat().st_size if global_instructions.exists() else 0}
    trials = [(t, arm) for t in tasks for arm in protocol["arms"]]
    random.Random(protocol["trial_order_seed"] + ":" + args.split).shuffle(trials)
    meta = {"schema_version": 1, "experiment_id": protocol["experiment_id"],
            "started_utc": datetime.now(timezone.utc).isoformat(), "source_manifest": manifest,
            "source_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
            "source_tree_dirty": dirty,
            "codex_version": version, "requested_model": args.model, "requested_reasoning_effort": args.effort,
            "auth_mode": "ChatGPT", "split": args.split, "timeout_seconds_per_decision": args.timeout,
            "binary_sha256": checker.digest, "receipt_sha256": sha256(RECEIPT),
            "global_instructions": inherited, "trial_order": [[t["id"], arm] for t, arm in trials],
            "limits": protocol["limits"], "passed_integrity": False}
    write_json(args.out / "run.json", meta)
    completed = []
    seen_threads = set()
    # No oracle, repository, or other trial is placed in the temporary model cwd.
    with tempfile.TemporaryDirectory(prefix="finite-repair-pilot-") as temp:
        schema = Path(temp) / "answer.schema.json"
        write_json(schema, ANSWER_SCHEMA)
        command = model_command(executable, args.model, args.effort, temp, schema)
        meta["command_template"] = [s.replace(temp, "<isolated-cwd>") for s in command]
        write_json(args.out / "run.json", meta)
        for index, (task, arm) in enumerate(trials):
            directory = args.out / f"trial-{index:02d}"
            directory.mkdir()
            word = encode(task["operation"], task["initial_labels"])
            row, record = checker.check(word)
            initial = proposal_feedback(task, {"status": "repair", "group_labels": task["initial_labels"]}, arm, row)
            history = [{"initial_feedback": initial}]
            trial = {"task_id": task["id"], "arm": arm, "satisfiable": bool(solve(task)),
                     "initial_record": record, "decisions": [], "correct": False, "first_correct": False}
            write_json(directory / "trial.json", trial)
            for attempt in range(protocol["max_decisions"]):
                answer, usage, process = run_model(command, prompt_for(task, history),
                                                   directory / f"decision-{attempt}", args.timeout)
                register_thread((directory / f"decision-{attempt}/events.jsonl").read_text(encoding="utf-8"), seen_threads)
                assessment = grade(task, answer)
                row, record = None, None
                if isinstance(answer, dict) and answer.get("status") == "repair":
                    try:
                        proposal_word = encode(task["operation"], answer.get("group_labels"))
                    except (ValueError, TypeError):
                        pass
                    else:
                        row, record = checker.check(proposal_word)
                feedback = proposal_feedback(task, answer, arm, row)
                decision = {"answer": answer, "grade": assessment, "feedback": feedback,
                            "native_record": record, "usage": usage, "process": process}
                trial["decisions"].append(decision)
                trial["correct"] = assessment["correct"]
                if attempt == 0:
                    trial["first_correct"] = assessment["correct"]
                write_json(directory / "trial.json", trial)
                history.append({"answer": answer, "feedback": feedback})
                if feedback.get("terminal") or feedback.get("accepted"):
                    break
            completed.append(trial)
            print(json.dumps({"completed": index + 1, "total": len(trials), "arm": arm,
                              "first_correct": trial["first_correct"], "correct": trial["correct"]}), flush=True)
    checker.finish()
    require(source_manifest() == manifest, "benchmark source changed during run")
    require(inherited["sha256"] == (sha256(global_instructions) if global_instructions.exists() else None),
            "global instructions changed during run")
    meta["passed_integrity"] = True
    meta["summary"] = summarize(completed)
    meta["artifacts"] = {p.relative_to(args.out).as_posix(): sha256(p)
                         for p in sorted(args.out.rglob("*")) if p.is_file() and p.name != "run.json"}
    write_json(args.out / "run.json", meta)
    print(json.dumps(meta["summary"], indent=2))


def check_artifacts(path, run):
    """Require all and only the recorded trial files, then verify their hashes."""
    expected = set()
    for index in range(len(run["trial_order"])):
        prefix = f"trial-{index:02d}"
        expected.add(f"{prefix}/trial.json")
        trial = read_json(path / prefix / "trial.json")
        for n in range(len(trial["decisions"])):
            expected.update(f"{prefix}/decision-{n}/{name}" for name in
                            ("prompt.txt", "events.jsonl", "stderr.txt", "process.json"))
    actual = {p.relative_to(path).as_posix() for p in path.rglob("*") if p.is_file()}
    require(actual == expected | {"run.json"}, "missing or unexpected run artifact")
    require(set(run["artifacts"]) == expected, "artifact manifest is incomplete or contains extras")
    for name, digest in run["artifacts"].items():
        p = (path / name).resolve()
        require(p.is_relative_to(path.resolve()), "artifact escapes run")
        require(sha256(p) == digest, f"artifact hash mismatch: {name}")


def check_header(run, binary_digest):
    require(run["passed_integrity"] is True, "run is incomplete")
    require(run["source_manifest"] == source_manifest(), "benchmark source changed")
    require(run["receipt_sha256"] == sha256(RECEIPT), "receipt changed")
    require(run["binary_sha256"] == binary_digest, "run binary digest mismatch")
    protocol = read_json(PROTOCOL)
    require(run["schema_version"] == 1 and run["experiment_id"] == protocol["experiment_id"], "wrong experiment")
    require(run["split"] in ("dev", "test"), "unknown split")
    require(run["split"] != "test" or run["source_tree_dirty"] is False, "test source was not frozen")
    require(run["auth_mode"] == "ChatGPT", "unexpected authentication route")
    tasks = {t["id"]: t for t in read_json(DATASET)["tasks"]}
    prescribed_order = [(t["id"], arm) for t in tasks.values() if t["split"] == run["split"]
                        for arm in protocol["arms"]]
    random.Random(protocol["trial_order_seed"] + ":" + run["split"]).shuffle(prescribed_order)
    require(list(map(tuple, run["trial_order"])) == prescribed_order, "trial order differs from protocol")
    return tasks


def replay(path):
    """Re-score saved answers, hashes, prompts, event usage, and native claim records."""
    run = read_json(path / "run.json")
    cached = load_receipt(RECEIPT)
    tasks = check_header(run, cached[0]["binary"]["sha256"])
    check_artifacts(path, run)
    trials = []
    seen_threads = set()
    for index, (task_id, arm) in enumerate(run["trial_order"]):
        directory = path / f"trial-{index:02d}"
        trial = read_json(directory / "trial.json")
        require((trial["task_id"], trial["arm"]) == (task_id, arm), "trial identity changed")
        task = tasks[task_id]
        require(task["split"] == run["split"], "wrong split")
        initial = trial["initial_record"]
        validate_result(initial, cached)
        word = encode(task["operation"], task["initial_labels"])
        require(initial["input"]["word"] == word, "initial claim mismatch")
        history = [{"initial_feedback": proposal_feedback(task, {"status": "repair", "group_labels": task["initial_labels"]}, arm, cached[1][word])}]
        decisions = trial["decisions"]
        require(1 <= len(decisions) <= read_json(PROTOCOL)["max_decisions"], "invalid decision budget")
        for n, decision in enumerate(decisions):
            d = directory / f"decision-{n}"
            require((d / "prompt.txt").read_text(encoding="utf-8") == prompt_for(task, history), "prompt changed or leaked scoring")
            event_text = (d / "events.jsonl").read_text(encoding="utf-8")
            register_thread(event_text, seen_threads)
            answer, usage = parse_events(event_text)
            require(answer == decision["answer"] and usage == decision["usage"], "events differ from scored answer")
            require(grade(task, answer) == decision["grade"], "grade mismatch")
            require(read_json(d / "process.json") == decision["process"] and decision["process"]["returncode"] == 0, "process mismatch")
            record = decision["native_record"]
            row = None
            if record:
                validate_result(record, cached)
                word = encode(task["operation"], answer["group_labels"])
                require(record["input"]["word"] == word, "proposal claim mismatch")
                row = cached[1][word]
            feedback = proposal_feedback(task, answer, arm, row)
            require(feedback == decision["feedback"], "feedback mismatch")
            require(n == len(decisions) - 1 or not (feedback.get("terminal") or feedback.get("accepted")), "continued after terminal answer")
            history.append({"answer": answer, "feedback": feedback})
        last = decisions[-1]["feedback"]
        require(len(decisions) == read_json(PROTOCOL)["max_decisions"] or last.get("terminal") or last.get("accepted"), "stopped early")
        require(trial["correct"] == decisions[-1]["grade"]["correct"] and trial["first_correct"] == decisions[0]["grade"]["correct"], "summary score mismatch")
        require(trial["satisfiable"] == bool(solve(task)), "oracle class mismatch")
        trials.append(trial)
    expected = {(t["id"], a) for t in tasks.values() if t["split"] == run["split"] for a in read_json(PROTOCOL)["arms"]}
    require(len(run["trial_order"]) == len(expected) and set(map(tuple, run["trial_order"])) == expected, "missing or duplicate trial")
    require(summarize(trials) == run["summary"], "summary mismatch")
    return run["summary"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    live = sub.add_parser("run")
    live.add_argument("--model", required=True, help="explicit model identifier recorded with the run")
    live.add_argument("--effort", required=True)
    live.add_argument("--split", choices=["dev", "test"], default="test")
    live.add_argument("--timeout", type=int, default=180)
    live.add_argument("--out", type=Path, required=True)
    live.add_argument("--binary", type=Path, default=ROOT / "lean/.lake/build/bin/grouping_checker")
    live.add_argument("--wsl-distribution")
    saved = sub.add_parser("replay")
    saved.add_argument("directory", type=Path)
    args = parser.parse_args()
    if args.action == "run":
        run(args)
    else:
        print(json.dumps(replay(args.directory), indent=2))


if __name__ == "__main__":
    main()
