"""Offline preparation controls. These are not answering-agent trials."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

import applicability_packets as packets

spec = importlib.util.spec_from_file_location("applicability_broker", packets.BROKER)
broker_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(broker_module)


class PreparationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = packets.prepare()

    def broker(self, arm, **kw):
        return broker_module.Broker(self.data["inventory"], self.data["views"][arm], **kw)

    def test_frozen_sources_and_packets(self):
        report = packets.check(self.data)
        self.assertEqual(report["reference_count"], 26)
        self.assertEqual(report["shared_raw_references"], 18)

    def test_record_values_and_all_fact_spans(self):
        for ref, record in self.data["records"].items():
            with self.subTest(reference=ref):
                self.assertEqual(json.loads(self.data["views"]["atlas"][ref]), record)
                doc, spans = packets.documentation(record)
                self.assertEqual(self.data["views"]["documentation"][ref], doc)
                for span in spans:
                    value = packets.pointer(record, span["pointer"])
                    self.assertEqual(span["kind"], type(value).__name__)
                    self.assertEqual(span["value_sha256"], packets.digest(packets.encoded(value)))
                    lo, hi = span["span"]
                    self.assertTrue(0 <= lo < hi <= len(doc))

    def test_identical_source_units_and_search_results(self):
        for ref in self.data["views"]["atlas"]:
            if ref not in self.data["records"]:
                self.assertEqual(self.data["views"]["atlas"][ref], self.data["views"]["documentation"][ref])
        for query in ("N5", "rotation permutation", "n4-E16457", "Tiny-stay", "halted_fixed", "not-present-918"):
            answers = [self.broker(arm).call("search", {"query": query}) for arm in self.data["views"]]
            self.assertEqual(*answers)

    def test_documentation_distinguishes_string_labels_from_values(self):
        for value in (0, 1, -2, 1.5, True, False, None, [], {}):
            spelling = json.dumps(value)
            with self.subTest(value=spelling):
                rendered, _ = packets.documentation({"value": value})
                label, _ = packets.documentation({"value": spelling})
                self.assertNotEqual(rendered, label)
                self.assertIn(json.dumps(spelling), label)
        empty, _ = packets.documentation({"value": ""})
        self.assertIn('**value:** ""', empty)
        quoted, _ = packets.documentation({"value": '"0"'})
        plain, _ = packets.documentation({"value": "0"})
        self.assertNotEqual(quoted, plain)

    def test_changed_fact_or_omitted_limit_fails_freeze(self):
        for arm in ("documentation", "atlas"):
            changed = copy.deepcopy(self.data)
            changed["views"][arm]["R01"] = changed["views"][arm]["R01"].replace("total unary", "partial binary")
            with self.assertRaises(ValueError):
                packets.check(changed)
        changed = copy.deepcopy(self.data)
        del changed["views"]["atlas"]["R03"]
        with self.assertRaises(ValueError):
            packets.check(changed)

    def test_no_task_key_or_other_arm_capabilities(self):
        for arm in self.data["views"]:
            broker = self.broker(arm, max_calls=10)
            for ref in ("../answer-key.json", "tasks.json", "fact-map.json", "atlas/texts.json", "documentation/texts.json"):
                result = broker.call("read", {"reference": ref, "page": 0})
                self.assertEqual(result, {"error": "unknown reference"})
            self.assertEqual(broker.call("shell", {"command": "pwd"}), {"error": "unknown tool"})

    def test_pages_reassemble_and_limits_count_denials(self):
        for arm, texts in self.data["views"].items():
            for ref, text in texts.items():
                broker = self.broker(arm, max_calls=50, max_bytes=200000)
                first = broker.call("read", {"reference": ref, "page": 0})
                pages = [first] + [broker.call("read", {"reference": ref, "page": p}) for p in range(1, first["pages"])]
                self.assertEqual("".join(p["text"] for p in pages), text)
                self.assertTrue(all(e["returned_bytes"] <= 12000 for e in broker.log))
        broker = self.broker("atlas", max_calls=1)
        broker.call("read", {"reference": "not-known", "page": 0})
        with self.assertRaises(broker_module.LimitReached):
            broker.call("read", {"reference": "R01", "page": 0})

    def test_source_selections_reconstruct(self):
        for unit in self.data["inventory"]:
            source, ref = unit["source"], unit["id"]
            raw = packets.blob(source["path"])
            self.assertEqual(packets.digest(raw), source["sha256"])
            if "json_pointer" in source:
                self.assertEqual(packets.pointer(json.loads(raw), source["json_pointer"]), self.data["records"][ref])
            elif isinstance(source.get("selection"), list):
                self.assertEqual([packets.pointer(json.loads(raw), p) for p in source["selection"]], self.data["records"][ref])
            elif "selection" in source:
                rows = raw.decode("utf-8").splitlines(keepends=True)
                self.assertEqual("".join(rows[n-1] for n in source["selection"]["one_based_lines"]), self.data["views"]["atlas"][ref])

    def test_no_reserved_object_records_or_benchmark_answers(self):
        self.assertEqual({p["id"] for p in [self.data["records"]["R06"]]}, {"tm-pair:tiny-stay:v1"})
        for ref in ("R04", "R05"):
            self.assertEqual(self.data["records"][ref]["name"], "C4")
        for unit in self.data["inventory"]:
            self.assertNotIn("benchmarks/", unit["source"]["path"])
            self.assertNotIn("test_", Path(unit["source"]["path"]).name)
        protocol = json.loads((packets.BASE / "protocol.json").read_text(encoding="utf-8"))
        self.assertEqual(protocol["scheduled_answering_sessions"], 0)
        self.assertIsNone(protocol["usage"]["actual_model_tokens"])

    def test_each_common_prompt_contains_only_one_assigned_task(self):
        files = packets.packet_files(self.data)
        task_ids = [f"EA{i:02}" for i in range(1, 9)]
        for task in task_ids:
            raw = files[f"prompts/{task}.json"]
            parsed = json.loads(raw)
            self.assertEqual(parsed["assigned_task"]["id"], task)
            self.assertEqual(set(parsed), {"instructions", "assigned_task", "answer_format", "rubric", "resources"})
            for other in task_ids:
                if other != task:
                    self.assertNotIn(other, raw)
            self.assertNotIn("suggested_source_ids", raw)
            self.assertNotIn("critical_errors", raw)


if __name__ == "__main__":
    unittest.main()
