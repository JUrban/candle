#!/usr/bin/env python3
"""Deterministic tests for S1 fingerprint request/report plumbing."""

import hashlib
from pathlib import Path
import tempfile
import unittest

import regression


class FingerprintPlumbingTest(unittest.TestCase):
    @staticmethod
    def state_fields(axioms=b"axiom-serialization"):
        return [
            regression.STATE_FINGERPRINT_MARKER,
            b"kernel-state".hex(), b"types".hex(), b"constants".hex(),
            b"definitions".hex(), axioms.hex(), "11", "22", "33", "3",
        ]

    def test_request_source_accepts_only_safe_value_paths(self):
        self.assertEqual(
            regression._fingerprint_request_source(
                ("THM", "theorem'", "Finale.TRANSCENDENTAL_E")),
            ('candle_s1_emit_fingerprint "THM" THM;;\n'
             'candle_s1_emit_fingerprint "theorem\'" theorem\';;\n'
             'candle_s1_emit_fingerprint "Finale.TRANSCENDENTAL_E" '
             'Finale.TRANSCENDENTAL_E;;\n'
             'candle_s1_emit_state_fingerprint ();;\n'))
        with self.assertRaises(ValueError):
            regression._fingerprint_request_source(("THM; failwith",))

    def test_structural_records_become_compact_hashes(self):
        fields = [
            regression.FINGERPRINT_MARKER,
            b"THM".hex(),
            b"theorem-serialization".hex(),
            regression.EMPTY_HYPOTHESES_WIRE.hex(),
            b"conclusion-serialization".hex(),
            b"axiom-serialization".hex(),
            "0",
            "3",
        ]
        with tempfile.NamedTemporaryFile(
                mode="w", encoding="utf-8", delete=False) as logfile:
            logfile.write("ordinary Candle output\n")
            logfile.write("\t".join(fields) + "\n")
            logfile.write("\t".join(self.state_fields()) + "\n")
            path = Path(logfile.name)
        try:
            report = regression._read_fingerprint_records(
                path, ("THM",), "audited")
        finally:
            path.unlink()

        self.assertEqual(report["status"], "observed_uncompared")
        self.assertFalse(report["expected_identities_present"])
        record = report["theorems"][0]
        self.assertEqual(record["hypothesis_count"], 0)
        self.assertEqual(record["global_axiom_count"], 3)
        self.assertEqual(
            record["theorem_sha256"],
            hashlib.sha256(b"theorem-serialization").hexdigest())
        self.assertEqual(report["post_state"]["definition_count"], 33)

    def test_exact_approved_identity_becomes_a_match(self):
        fields = [
            regression.FINGERPRINT_MARKER,
            b"THM".hex(), b"theorem".hex(),
            regression.EMPTY_HYPOTHESES_WIRE.hex(),
            b"conclusion".hex(), b"axioms".hex(), "0", "3",
        ]
        with tempfile.NamedTemporaryFile(
                mode="w", encoding="utf-8", delete=False) as logfile:
            logfile.write("\t".join(fields) + "\n")
            logfile.write("\t".join(self.state_fields(b"axioms")) + "\n")
            path = Path(logfile.name)
        serializer_sha256 = hashlib.sha256(
            regression.FINGERPRINT_HELPER.read_bytes()).hexdigest()
        record = {
            "name": "THM",
            "theorem_sha256": hashlib.sha256(b"theorem").hexdigest(),
            "hypotheses_sha256": hashlib.sha256(
                regression.EMPTY_HYPOTHESES_WIRE).hexdigest(),
            "conclusion_sha256": hashlib.sha256(b"conclusion").hexdigest(),
            "global_axioms_sha256": hashlib.sha256(b"axioms").hexdigest(),
            "hypothesis_count": 0,
            "global_axiom_count": 3,
        }
        post_state = {
            "kernel_state_sha256": hashlib.sha256(b"kernel-state").hexdigest(),
            "type_constants_sha256": hashlib.sha256(b"types").hexdigest(),
            "type_constant_count": 11,
            "term_constants_sha256": hashlib.sha256(b"constants").hexdigest(),
            "term_constant_count": 22,
            "definitions_sha256": hashlib.sha256(b"definitions").hexdigest(),
            "definition_count": 33,
            "global_axioms_sha256": hashlib.sha256(b"axioms").hexdigest(),
            "global_axiom_count": 3,
        }
        try:
            report = regression._read_fingerprint_records(
                path, ("THM",), "audited", {
                    "approval_sha256": "f" * 64,
                    "serializer_sha256": serializer_sha256,
                    "theorems": [record],
                    "post_state": post_state,
                })
        finally:
            path.unlink()
        self.assertEqual(report["status"], "matched")
        self.assertTrue(report["expected_identities_present"])

    def test_expected_identity_mismatch_fails_closed(self):
        fields = [
            regression.FINGERPRINT_MARKER,
            b"THM".hex(), b"observed".hex(),
            regression.EMPTY_HYPOTHESES_WIRE.hex(),
            b"conclusion".hex(), b"axioms".hex(), "0", "3",
        ]
        with tempfile.NamedTemporaryFile(
                mode="w", encoding="utf-8", delete=False) as logfile:
            logfile.write("\t".join(fields) + "\n")
            logfile.write("\t".join(self.state_fields(b"axioms")) + "\n")
            path = Path(logfile.name)
        serializer_sha256 = hashlib.sha256(
            regression.FINGERPRINT_HELPER.read_bytes()).hexdigest()
        try:
            with self.assertRaisesRegex(
                    regression.LoadFailure, "fingerprint mismatch"):
                regression._read_fingerprint_records(
                    path, ("THM",), "audited", {
                        "approval_sha256": "f" * 64,
                        "serializer_sha256": serializer_sha256,
                        "theorems": [],
                        "post_state": {},
                    })
        finally:
            path.unlink()

    def test_manual_review_mapping_cannot_be_approved(self):
        with self.assertRaisesRegex(
                regression.LoadFailure, "manual-review mapping"):
            regression._match_expected_identities(
                [], {}, {
                    "approval_sha256": "0" * 64,
                    "serializer_sha256": "0" * 64,
                    "theorems": [], "post_state": {}},
                "0" * 64, "manual_review")

    def test_report_summary_never_counts_load_only_as_s1(self):
        tests = [
            regression.Test("matched", (), ("A",), "audited", {"x": 1}),
            regression.Test("observed", (), ("B",), "audited", None),
            regression.Test("failed", (), ("C",), "audited", None),
            regression.Test("review", (), ("D",), "manual_review", None),
        ]
        results = [
            regression.TestResult(
                "matched", regression.TestStatus.PASS,
                fingerprints={"status": "matched"}),
            regression.TestResult(
                "observed", regression.TestStatus.PASS,
                fingerprints={"status": "observed_uncompared"}),
            regression.TestResult("failed", regression.TestStatus.FAIL),
            regression.TestResult("review", regression.TestStatus.PASS),
        ]
        summary = regression.Reporter.s1_evidence_summary(
            results, tests, "top100")
        self.assertEqual(summary["expected_identity_target_count"], 1)
        self.assertEqual(summary["manual_review_mapping_target_count"], 1)
        self.assertEqual(summary["matched_target_count"], 1)
        self.assertEqual(summary["observed_uncompared_target_count"], 1)
        self.assertEqual(summary["missing_or_failed_fingerprint_target_count"], 2)
        self.assertFalse(summary["suite_closed"])

        partial = regression.Reporter.s1_evidence_summary(
            results[:1], tests, "top100")
        self.assertEqual(
            partial["missing_or_failed_fingerprint_target_count"], 3)
        self.assertFalse(partial["suite_closed"])

    def test_malformed_wire_encoding_fails_closed(self):
        fields = [
            regression.FINGERPRINT_MARKER,
            "THM",  # not hexadecimal
            b"theorem".hex(),
            b"hypotheses".hex(),
            b"conclusion".hex(),
            b"axioms".hex(),
            "0",
            "0",
        ]
        with tempfile.NamedTemporaryFile(
                mode="w", encoding="utf-8", delete=False) as logfile:
            logfile.write("\t".join(fields) + "\n")
            logfile.write("\t".join(self.state_fields()) + "\n")
            path = Path(logfile.name)
        try:
            with self.assertRaisesRegex(
                    regression.LoadFailure, "malformed hexadecimal"):
                regression._read_fingerprint_records(
                    path, ("THM",), "audited")
        finally:
            path.unlink()

    def test_positive_or_inconsistent_hypotheses_fail_closed(self):
        for hypotheses, count in (
                (b"nonempty", "1"),
                (regression.EMPTY_HYPOTHESES_WIRE, "1"),
                (b"nonempty", "0")):
            fields = [
                regression.FINGERPRINT_MARKER, b"EGCD".hex(),
                b"theorem".hex(), hypotheses.hex(), b"conclusion".hex(),
                b"axioms".hex(), count, "3",
            ]
            with tempfile.NamedTemporaryFile(
                    mode="w", encoding="utf-8", delete=False) as logfile:
                logfile.write("\t".join(fields) + "\n")
                logfile.write("\t".join(self.state_fields(b"axioms")) + "\n")
                path = Path(logfile.name)
            try:
                with self.assertRaisesRegex(
                        regression.LoadFailure, "theorem is not closed"):
                    regression._read_fingerprint_records(
                        path, ("EGCD",), "audited")
            finally:
                path.unlink()

    def test_missing_record_is_not_a_load_success_fingerprint(self):
        with tempfile.NamedTemporaryFile(
                mode="w", encoding="utf-8", delete=False) as logfile:
            logfile.write("target loaded, but emitted no identity\n")
            path = Path(logfile.name)
        try:
            with self.assertRaises(regression.LoadFailure):
                regression._read_fingerprint_records(
                    path, ("MISSING",), "audited")
        finally:
            path.unlink()


if __name__ == "__main__":
    unittest.main()
