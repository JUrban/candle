#!/usr/bin/env python3
"""Static, single-core tests for the Great 100 inventory contract."""

import json
import unittest

import top100_manifest


class Top100ManifestTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads(
            top100_manifest.MANIFEST.read_text(encoding="utf-8")
        )

    def test_generated_manifest_is_current(self):
        self.assertEqual(self.manifest, top100_manifest.build_manifest())

    def test_actual_suite_shape_is_explicit(self):
        self.assertEqual(self.manifest["target_count"], 65)
        self.assertEqual(self.manifest["covered_source_count"], 66)
        self.assertEqual(
            self.manifest["excluded_100_sources"],
            [{
                "path": "100/sqrt.ml",
                "reason": "absent_from_upstream_GREAT_100_THEOREMS",
                "approval_status": "unreviewed",
                "flyspeck_dependency_impact": "unassessed",
            }],
        )

    def test_no_hidden_skips(self):
        self.assertTrue(all(target["skip"] is None
                            for target in self.manifest["targets"]))
        self.assertTrue(all(target["expected_status"] == "pass"
                            for target in self.manifest["targets"]))

    def test_missing_s1_evidence_is_not_misreported_as_success(self):
        for target in self.manifest["targets"]:
            request = target["fingerprint_request"]
            self.assertTrue(request["theorems"])
            self.assertIsNone(request["expected_identities"])
            self.assertIn(target["fingerprints"]["status"],
                          {"missing", "not_reached"})
            self.assertIsNone(target["fingerprints"]["theorems"])
            self.assertIsNone(target["fingerprints"]["assumptions"])

    def test_all_named_results_resolve_and_manual_review_is_explicit(self):
        manual = {}
        for target in self.manifest["targets"]:
            request = target["fingerprint_request"]
            for theorem in request["theorems"]:
                declaration = theorem["resolved_declaration"]
                self.assertIn(declaration["path"], target["load_files"])
                self.assertGreater(declaration["line"], 0)
            if request["mapping_status"] == "manual_review":
                self.assertTrue(request["review_note"])
                manual[target["name"]] = request["review_note"]
            else:
                self.assertEqual(request["mapping_status"], "audited")
                self.assertIsNone(request["review_note"])
        self.assertEqual(set(manual), set(top100_manifest.MANUAL_REVIEW_MAPPINGS))

    def test_observed_failure_links_to_minimized_ledger_entry(self):
        targets = {target["name"]: target for target in self.manifest["targets"]}
        observation = targets["100/bertrand-primerecip"]["baseline_observation"]
        self.assertEqual(observation["status"], "fail")
        self.assertEqual(
            observation["ledger_id"], "CANDLE-OCAML-FLOAT-LITERAL-001")
        ledger = json.loads(
            (top100_manifest.ROOT / "candle" / "compatibility" / "ledger.json")
            .read_text(encoding="utf-8")
        )
        self.assertIn(observation["ledger_id"],
                      {entry["id"] for entry in ledger["entries"]})

    def test_module_scoped_theorem_request_is_qualified(self):
        target = next(target for target in self.manifest["targets"]
                      if target["name"] == "100/e_is_transcendental")
        theorem = target["fingerprint_request"]["theorems"][0]
        self.assertEqual(theorem["name"], "Finale.TRANSCENDENTAL_E")
        self.assertEqual(theorem["resolved_declaration"]["line"], 2903)
        self.assertIn(
            {"path": "100/e_is_transcendental.ml", "line": 2910},
            theorem["qualified_references"])


if __name__ == "__main__":
    unittest.main()
