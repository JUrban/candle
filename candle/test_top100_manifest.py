#!/usr/bin/env python3
"""Static, single-core tests for the Great 100 inventory contract."""

import json
import re
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

    def test_piseries_mapping_is_source_designated(self):
        target = next(target for target in self.manifest["targets"]
                      if target["name"] == "100/piseries")
        request = target["fingerprint_request"]
        self.assertEqual(request["mapping_status"], "audited")
        self.assertIn("most famous special case", request["mapping_basis"])
        self.assertEqual(
            request["theorems"], [{
                "name": "EULER_HARMONIC_SUM",
                "resolved_declaration": {
                    "path": "100/piseries.ml", "line": 2699},
                "shadowed_declarations": [],
            }])
        source = (top100_manifest.ROOT / "100/piseries.ml").read_text()
        self.assertRegex(
            source,
            r"Isolate the most famous special case[\s\S]*?"
            r"let EULER_HARMONIC_SUM = mk_harmonic 2;;")

    def test_quartic_final_rebinding_preserves_theorem_statement(self):
        target = next(target for target in self.manifest["targets"]
                      if target["name"] == "100/quartic")
        request = target["fingerprint_request"]
        self.assertEqual(request["mapping_status"], "audited")
        self.assertIn("changes only the proof", request["mapping_basis"])
        theorem = request["theorems"][0]
        self.assertEqual(
            theorem["resolved_declaration"],
            {"path": "100/quartic.ml", "line": 186})
        self.assertEqual(
            theorem["shadowed_declarations"],
            [{"path": "100/quartic.ml", "line": 140},
             {"path": "100/quartic.ml", "line": 163}])
        source = (top100_manifest.ROOT / "100/quartic.ml").read_text()
        statements = re.findall(
            r"let QUARTIC_CASES = prove\n \(`(.*?)`,\n", source, re.DOTALL)
        self.assertEqual(len(statements), 3)
        self.assertNotEqual(statements[0], statements[1])
        self.assertEqual(statements[1], statements[2])

    def test_cantor_and_fourier_ambiguities_remain_fail_closed(self):
        targets = {target["name"]: target for target in self.manifest["targets"]}
        cantor = targets["100/cantor"]["fingerprint_request"]
        self.assertEqual(cantor["mapping_status"], "manual_review")
        self.assertIn("f83edb4", cantor["review_note"])
        self.assertEqual(
            [item["line"] for item in cantor["theorems"][0][
                "shadowed_declarations"]], [25])
        self.assertEqual(
            cantor["theorems"][0]["resolved_declaration"]["line"], 62)

        fourier = targets["100/fourier"]["fingerprint_request"]
        self.assertEqual(fourier["mapping_status"], "manual_review")
        self.assertIn("never designates", fourier["review_note"])
        self.assertEqual(
            [item["name"] for item in fourier["theorems"]],
            ["FOURIER_SERIES_L2", "FOURIER_DINI_TEST",
             "FOURIER_JORDAN_BOUNDED_VARIATION",
             "FOURIER_FEJER_CESARO_SUMMABLE_SIMPLE"])

    def test_reference_candidate_cannot_enter_expected_identities(self):
        candidate = {
            "schema": "candle-s1-reference-candidate-v1",
            "artifact_kind": "reference_identity_candidate",
            "approval_status": "candidate_unapproved",
            "promotion_allowed": False,
            "candidate_identities": {"status": "observed_uncompared"},
        }
        with self.assertRaisesRegex(ValueError, "malformed expected"):
            top100_manifest._validate_expected_identity_object(
                "100/gcd", ["EGCD"], candidate)

        approved_shape = {
            "serializer_sha256": "0" * 64,
            "theorems": [{
                "name": "EGCD",
                "theorem_sha256": "1" * 64,
                "hypotheses_sha256": "2" * 64,
                "conclusion_sha256": "3" * 64,
                "global_axioms_sha256": "4" * 64,
                "hypothesis_count": 0,
                "global_axiom_count": 3,
            }],
        }
        self.assertIs(
            top100_manifest._validate_expected_identity_object(
                "100/gcd", ["EGCD"], approved_shape),
            approved_shape)


if __name__ == "__main__":
    unittest.main()
