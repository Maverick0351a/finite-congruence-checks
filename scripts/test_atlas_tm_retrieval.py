"""Adversarial admission checks for the TM retrieval exercise.

These are synthetic structured answers and citation fixtures, not model calls
or measurements of an agent's mathematical reasoning.
"""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import check_tm_retrieval as checker
import tm_atlas


class CitationBoundaryTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="tm-citation-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.path = self.root / "fixture.json"
        self.path.write_text(json.dumps({"claims": [{"value": 7}]}), encoding="utf-8")
        self.citation = {"path": "fixture.json", "json_pointer": "/claims/0",
                         "sha256": checker.digest(self.path)}

    def test_exact_citation_resolves(self):
        self.assertEqual(checker.check_citation(self.citation, self.root), {"value": 7})

    def test_changed_artifact_or_hash_rejected(self):
        citation = dict(self.citation, sha256="0" * 64)
        with self.assertRaises(ValueError):
            checker.check_citation(citation, self.root)
        self.path.write_text(json.dumps({"claims": [{"value": 8}]}), encoding="utf-8")
        with self.assertRaises(ValueError):
            checker.check_citation(self.citation, self.root)

    def test_absolute_and_parent_paths_rejected(self):
        for path in (str(self.path.resolve()), "../fixture.json"):
            with self.subTest(path=path):
                with self.assertRaises(ValueError):
                    checker.check_citation(dict(self.citation, path=path), self.root)

    def test_nonexistent_pointer_rejected(self):
        for pointer in ("claims/0", "/claims/1", "/missing"):
            with self.subTest(pointer=pointer):
                with self.assertRaises((ValueError, IndexError, KeyError)):
                    checker.check_citation(dict(self.citation, json_pointer=pointer), self.root)


class StructuredAnswerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Admit real retained data once. Subsequent mutations exercise the
        # grader against that admitted snapshot, without replaying 2,857 native
        # records for every individual answer-field mutation.
        cls.dataset = tm_atlas.load_dataset()
        cls.claims = {claim["id"]: claim for claim in cls.dataset["claims"]}
        cls.limits_citation = {"path": checker.DATA, "json_pointer": "/limits",
                               "sha256": checker.digest(checker.ROOT / checker.DATA)}
        protocol = (
            ("bb2-property-separation", "refuted", "bb2", ("halting_time", "tape", "head_position")),
            ("bb4-output-separation", "refuted", "bb4", ("tape", "head_position")),
            ("tiny-property-separation", "refuted", "tiny-stay", ("halting_time", "tape", "head_position")),
            ("missing-instruction-lemma", "supported", "tiny-stay", ("tape",)),
            ("bounded-to-universal", "unsupported", None, ()),
            ("unsupported-pair", "unsupported", None, ()),
        )
        answers = []
        for identifier, verdict, pair, properties in protocol:
            ids = sorted(f"tm:{pair}:{prop}:v1" for prop in properties)
            citations = {}
            for key in ids:
                for cite in cls.claims[key]["citations"]:
                    citations[checker.citation_key(cite)] = copy.deepcopy(cite)
            if not ids:
                citations[checker.citation_key(cls.limits_citation)] = cls.limits_citation
            answers.append({
                "id": identifier, "verdict": verdict, "claim_ids": ids,
                "observations": [{"claim_id": key, **copy.deepcopy(cls.claims[key]["observation"])}
                                 for key in ids],
                "citations": list(citations.values()), "general_equivalence": False,
                "scope": "These exact saved pairs and blank input only.",
                "explanation": "Synthetic structured-answer fixture; prose quality is not measured.",
            })
        missing = next(answer for answer in answers if answer["id"] == "missing-instruction-lemma")
        application = next(item for item in cls.claims["tm:tiny-stay:tape:v1"]["applicable_lemmas"]
                           if item["theorem"] == "TMOracle.Checks.missing_instruction")
        cls.exact_lemma_citation = next(cite for cite in application["citations"]
                                       if cite["path"] == tm_atlas.TRACE_PATH
                                       and "/applicable_lemmas/" in cite["json_pointer"])
        missing["lemma"] = {"name": "TMOracle.Checks.missing_instruction",
                            "hypotheses": ["The configuration is not already halting.",
                                           "The instruction lookup at its state and head symbol is none."],
                            "citation": copy.deepcopy(cls.exact_lemma_citation)}
        cls.baseline = {"answers": answers}

    def setUp(self):
        self.document = copy.deepcopy(self.baseline)

    def answer(self, identifier):
        return next(answer for answer in self.document["answers"] if answer["id"] == identifier)

    def grade(self):
        with mock.patch.object(tm_atlas, "load_dataset", return_value=self.dataset):
            return checker.grade(self.document)

    def assert_rejected(self, identifier):
        report = self.grade()
        self.assertFalse(report["passed"])
        row = next(row for row in report["results"] if row["id"] == identifier)
        self.assertFalse(row["passed"])
        self.assertTrue(row["errors"])

    def test_consistent_synthetic_answers_are_admitted(self):
        report = self.grade()
        self.assertTrue(report["passed"], report)
        self.assertEqual((report["correct"], report["total"]), (6, 6))

    def test_wrong_pair_or_property_cannot_replace_required_claim(self):
        identifier = "bb4-output-separation"
        for replacement in ("tm:bb2:tape:v1", "tm:bb4:halting_time:v1", "tm:bb5:tape:v1"):
            with self.subTest(replacement=replacement):
                self.document = copy.deepcopy(self.baseline)
                self.answer(identifier)["claim_ids"][0] = replacement
                self.assert_rejected(identifier)

    def test_wrong_observation_or_boolean_for_integer_rejected(self):
        identifier = "bb2-property-separation"
        for value in (7, True, 6.0):
            with self.subTest(value=value):
                self.document = copy.deepcopy(self.baseline)
                observation = next(row for row in self.answer(identifier)["observations"]
                                   if row["claim_id"] == "tm:bb2:halting_time:v1")
                observation["left"] = value
                self.assert_rejected(identifier)

    def test_missing_first_halt_prefix_citations_rejected(self):
        identifier = "bb2-property-separation"
        answer = self.answer(identifier)
        prefixes = [cite for cite in answer["citations"]
                    if cite["json_pointer"].endswith(("/left/trace", "/right/trace"))]
        self.assertEqual(len(prefixes), 2, "First-halt claims must cite both complete prefixes")
        answer["citations"] = [cite for cite in answer["citations"] if cite not in prefixes]
        self.assert_rejected(identifier)

    def test_forged_hash_or_resolvable_wrong_property_citation_rejected(self):
        identifier = "bb4-output-separation"
        self.answer(identifier)["citations"][0]["sha256"] = "0" * 64
        self.assert_rejected(identifier)
        self.document = copy.deepcopy(self.baseline)
        # A valid artifact/pointer is insufficient when it cites another pair.
        wrong = self.claims["tm:bb2:tape:v1"]["citations"][0]
        self.answer(identifier)["citations"].append(copy.deepcopy(wrong))
        self.assert_rejected(identifier)

    def test_general_equivalence_assertion_or_numeric_flag_rejected(self):
        identifier = "bounded-to-universal"
        for value in (True, 0, None):
            with self.subTest(value=value):
                self.document = copy.deepcopy(self.baseline)
                self.answer(identifier)["general_equivalence"] = value
                self.assert_rejected(identifier)

    def test_scope_only_answer_requires_limits_and_no_fabricated_claim(self):
        identifier = "unsupported-pair"
        self.answer(identifier)["citations"] = []
        self.assert_rejected(identifier)
        self.document = copy.deepcopy(self.baseline)
        self.answer(identifier)["claim_ids"] = ["tm:bb5:tape:v1"]
        self.assert_rejected(identifier)

    def test_duplicate_or_missing_task_rejected(self):
        self.document["answers"][-1] = copy.deepcopy(self.document["answers"][0])
        with self.assertRaises(ValueError):
            self.grade()
        self.document = copy.deepcopy(self.baseline)
        self.document["answers"].pop()
        with self.assertRaises(ValueError):
            self.grade()

    def test_broad_or_other_pair_lemma_citation_rejected(self):
        identifier = "missing-instruction-lemma"
        other_application = next(item for item in self.claims["tm:bb2:tape:v1"]["applicable_lemmas"]
                                 if item["theorem"] == "TMOracle.Checks.missing_instruction")
        other_citation = next(cite for cite in other_application["citations"]
                              if cite["path"] == tm_atlas.TRACE_PATH
                              and "/applicable_lemmas/" in cite["json_pointer"])
        variants = [dict(self.exact_lemma_citation, json_pointer=""),
                    dict(self.exact_lemma_citation, json_pointer="/pairs/0"), other_citation]
        for citation in variants:
            with self.subTest(pointer=citation["json_pointer"]):
                self.document = copy.deepcopy(self.baseline)
                self.answer(identifier)["lemma"]["citation"] = copy.deepcopy(citation)
                self.assert_rejected(identifier)


if __name__ == "__main__":
    unittest.main()
