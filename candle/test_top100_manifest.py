#!/usr/bin/env python3
"""Static, single-core tests for the Great 100 inventory contract."""

import json
import re
import tempfile
import unittest
from pathlib import Path
from unittest import mock

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
            self.manifest["inventory_contract"]["theorem_request_count"], 97)
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
            self.assertIsNone(target["fingerprints"]["post_state"])
        approval = self.manifest["identity_approval"]
        self.assertEqual(approval["approval_status"], "unapproved")
        self.assertFalse(approval["promotion_allowed"])

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

    def test_cantor_and_fourier_boundaries_are_conservatively_audited(self):
        targets = {target["name"]: target for target in self.manifest["targets"]}
        cantor = targets["100/cantor"]["fingerprint_request"]
        self.assertEqual(cantor["mapping_status"], "audited")
        self.assertIsNone(cantor["review_note"])
        self.assertIn("post-load environment", cantor["mapping_basis"])
        self.assertEqual(
            [item["line"] for item in cantor["theorems"][0][
                "shadowed_declarations"]], [25])
        self.assertEqual(
            cantor["theorems"][0]["resolved_declaration"]["line"], 62)

        fourier = targets["100/fourier"]["fingerprint_request"]
        self.assertEqual(fourier["mapping_status"], "audited")
        self.assertIsNone(fourier["review_note"])
        self.assertIn("all four", fourier["mapping_basis"])
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
            "approval_sha256": "5" * 64,
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
            "post_state": {
                "kernel_state_sha256": "6" * 64,
                "type_constants_sha256": "7" * 64,
                "type_constant_count": 1,
                "term_constants_sha256": "8" * 64,
                "term_constant_count": 2,
                "definitions_sha256": "9" * 64,
                "definition_count": 3,
                "global_axioms_sha256": "4" * 64,
                "global_axiom_count": 3,
            },
        }
        self.assertIs(
            top100_manifest._validate_expected_identity_object(
                "100/gcd", ["EGCD"], approved_shape),
            approved_shape)

    def test_unapproved_artifact_is_exact_and_cannot_carry_identities(self):
        targets = top100_manifest.build_manifest()["targets"]
        original = json.loads(
            top100_manifest.IDENTITY_APPROVAL.read_text(encoding="utf-8"))
        original["targets"] = [{"self_approved": True}]
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "approval.json"
            path.write_text(json.dumps(original), encoding="utf-8")
            with mock.patch.object(top100_manifest, "IDENTITY_APPROVAL", path):
                with self.assertRaisesRegex(ValueError, "promotable data"):
                    top100_manifest._load_identity_approval(targets)

    def test_duplicate_approval_json_key_fails_closed(self):
        targets = top100_manifest.build_manifest()["targets"]
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "approval.json"
            path.write_text('{"schema":"a","schema":"b"}', encoding="utf-8")
            with mock.patch.object(top100_manifest, "IDENTITY_APPROVAL", path):
                with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                    top100_manifest._load_identity_approval(targets)

    def test_approved_artifact_requires_two_retained_independent_runs(self):
        targets = top100_manifest.build_manifest()["targets"]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "candle/evidence").mkdir(parents=True)
            serializer = root / "candle/fingerprint.ml"
            serializer.write_bytes(top100_manifest.ROOT.joinpath(
                "candle/fingerprint.ml").read_bytes())
            serializer_sha256 = top100_manifest._sha256(serializer)
            source_contract_payload = json.loads(
                top100_manifest.REFERENCE_SOURCE_CONTRACT.read_text(
                    encoding="utf-8"))
            reference_source_contract = \
                root / "candle/reference_source_contracts.json"
            reference_source_contract.write_text(
                json.dumps(source_contract_payload, indent=2) + "\n",
                encoding="utf-8")
            source_contract = root / "candle/evidence/source-contract.json"
            source_contract.write_bytes(reference_source_contract.read_bytes())

            def record(relative, content):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(content)
                return {
                    "path": relative,
                    "bytes": len(content),
                    "sha256": top100_manifest.hashlib.sha256(content).hexdigest(),
                }

            approved_targets = []
            for target_index, target in enumerate(targets):
                axioms_sha256 = "a" * 64
                expected = {
                    "serializer_sha256": serializer_sha256,
                    "theorems": [{
                        "name": theorem["name"],
                        "theorem_sha256": "1" * 64,
                        "hypotheses_sha256": "2" * 64,
                        "conclusion_sha256": "3" * 64,
                        "global_axioms_sha256": axioms_sha256,
                        "hypothesis_count": 0,
                        "global_axiom_count": 3,
                    } for theorem in target["fingerprint_request"]["theorems"]],
                    "post_state": {
                        "kernel_state_sha256": "4" * 64,
                        "type_constants_sha256": "5" * 64,
                        "type_constant_count": 10,
                        "term_constants_sha256": "6" * 64,
                        "term_constant_count": 20,
                        "definitions_sha256": "7" * 64,
                        "definition_count": 30,
                        "global_axioms_sha256": axioms_sha256,
                        "global_axiom_count": 3,
                    },
                }
                identity_sha256 = top100_manifest._canonical_sha256(expected)
                runs = []
                for run_index in range(2):
                    prefix = f"candle/evidence/t{target_index}-r{run_index}"
                    artifacts = {
                        name: record(
                            f"{prefix}-{name}",
                            f"{target_index}:{run_index}:{name}\n".encode())
                        for name in ("candidate", "plan", "request", "transcript")
                    }
                    artifacts["source_contract"] = {
                        "path": "candle/evidence/source-contract.json",
                        "bytes": source_contract.stat().st_size,
                        "sha256": top100_manifest._sha256(source_contract),
                    }
                    runs.append({
                        "artifacts": artifacts,
                        "reference_git_head":
                            source_contract_payload["exact_source_reference_commit"],
                        "session_nonce": ("9" if run_index == 0 else "b") * 64,
                        "identity_sha256": identity_sha256,
                    })
                approved_targets.append({
                    "name": target["name"], "reference_runs": runs,
                    "expected_identity": expected,
                })
            _, inventory_sha256 = top100_manifest._inventory_contract(targets)
            approval = {
                "schema": "candle-s1-identity-approval-v1",
                "artifact_kind":
                    "independently-reviewed-ocaml-reference-identities",
                "approval_status": "approved", "promotion_allowed": True,
                "inventory_contract_sha256": inventory_sha256,
                "serializer_sha256": serializer_sha256,
                "reference_policy": {
                    key: source_contract_payload[key] for key in (
                        "historical_upstream_commit",
                        "exact_source_reference_commit",
                        "compatibility_deltas")
                },
                "review": {
                    "reviewer": "independent-reviewer",
                    "approved_utc": "2026-08-29T00:00:00+00:00",
                    "review_commit": "f" * 40,
                    "decision":
                        "two-reference-runs-identical-and-source-deltas-reviewed",
                },
                "targets": approved_targets,
            }
            approval_path = root / "candle/top100_identity_approval.json"
            approval_path.write_text(
                json.dumps(approval, indent=2) + "\n", encoding="utf-8")
            with (mock.patch.object(top100_manifest, "ROOT", root),
                  mock.patch.object(
                      top100_manifest, "IDENTITY_APPROVAL", approval_path),
                  mock.patch.object(top100_manifest,
                                    "REFERENCE_SOURCE_CONTRACT",
                                    reference_source_contract)):
                loaded, artifact_sha256, expected, _ = \
                    top100_manifest._load_identity_approval(targets)
                self.assertTrue(loaded["promotion_allowed"])
                self.assertEqual(len(expected), 65)
                self.assertEqual(
                    expected[targets[0]["name"]]["approval_sha256"],
                    artifact_sha256)
                changed = root / approved_targets[0]["reference_runs"][0][
                    "artifacts"]["transcript"]["path"]
                alias = changed.with_name(changed.name + "-hardlink")
                alias.hardlink_to(changed)
                with self.assertRaisesRegex(ValueError, "ordinary transcript"):
                    top100_manifest._load_identity_approval(targets)
                alias.unlink()
                changed.write_bytes(changed.read_bytes() + b"mutation")
                with self.assertRaisesRegex(ValueError, "changed transcript"):
                    top100_manifest._load_identity_approval(targets)


if __name__ == "__main__":
    unittest.main()
