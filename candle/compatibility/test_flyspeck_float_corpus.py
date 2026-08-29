#!/usr/bin/env python3
"""Static fail-closed tests for the direct Flyspeck float corpus."""

import json
import os
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import flyspeck_float_corpus as subject


class FlyspeckFloatCorpusTests(unittest.TestCase):
    def test_rejects_failed_staging_with_only_pending_receipt(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "overlay.tmp.nonce"
            root.mkdir(mode=0o700)
            pending = root / ".flyspeck_normalization_receipt.json.pending"
            pending.write_text("{}", encoding="utf-8")
            os.chmod(pending, 0o444)
            os.chmod(root, 0o555)
            with self.assertRaises(subject.CorpusError):
                subject.validate_materialized_tree(
                    root, {"flyspeck_normalization_receipt.json": 0o444},
                    "normalization overlay",
                )

    def test_scanner_separates_code_from_non_ocaml_float_contexts(self):
        source = (
            b"let a = 2.;;\n"
            b"(* 3.0 (* nested 4.0 *) *)\n"
            b'let s = "5.0foo and escaped \\\" 6.0";;\n'
            b"let q = `#7.0 + #8.0`;;\n"
            b"let identifier2.0 = 0;;\n"
            b"let b = 1.0e-8;;\n"
        )
        observed = subject.scan_source("fixture:test.ml", source)
        self.assertEqual(
            [site["literal"] for site in observed["sites"]],
            ["2.", "1.0e-8"],
        )
        self.assertEqual(observed["raw_context_counts"], {
            "code": 2, "comment": 2, "string": 2, "quotation": 2,
        })
        self.assertEqual(
            observed["invalid_suffix_context_counts"], {"string": 1}
        )

    def test_hex_candidates_are_reported_but_never_decimal_sites(self):
        observed = subject.scan_source(
            "fixture:hex.ml", b"let x = 0x1.0p0;; (* 0x2.0p1 *)\n"
        )
        self.assertEqual(observed["sites"], [])
        self.assertEqual(observed["hex_context_counts"], {
            "code": 1, "comment": 1,
        })

    def test_unterminated_excluded_contexts_fail_closed(self):
        for source in (b"(* 1.0", b'"1.0', b"`#1.0"):
            with self.subTest(source=source):
                with self.assertRaises(subject.CorpusError):
                    subject.scan_source("fixture:bad.ml", source)

    def test_committed_artifact_has_exact_audit_anchors(self):
        payload = json.loads(
            (HERE / "flyspeck_float_corpus.json").read_text(encoding="utf-8")
        )
        subject.validate_artifact_shape(payload)
        inventory = payload["inventory"]
        self.assertEqual(inventory["raw_context_counts"],
                         subject.EXPECTED_RAW_CONTEXT_COUNTS)
        self.assertEqual(inventory["invalid_suffix_context_counts"],
                         subject.EXPECTED_INVALID_SUFFIX_COUNTS)
        self.assertEqual(inventory["hex_float_context_counts"], {})
        self.assertEqual(inventory["earliest_stratum_counts"], {
            "base": 4,
            "nonlinear_support": 127,
            "lp_support": 2,
            "final_assembly": 15_642,
        })
        self.assertEqual(payload["reference"]["host_strtod_erange_count"], 0)
        self.assertEqual(
            payload["reference"]["host_strtod_word_mismatch_count"], 0
        )

    def test_dominant_and_exponent_spellings_are_pinned(self):
        payload = json.loads(
            (HERE / "flyspeck_float_corpus.json").read_text(encoding="utf-8")
        )
        spellings = {record["literal"]: record
                     for record in payload["spellings"]}
        self.assertEqual(spellings["0.5000"]["occurrence_count"], 11_640)
        self.assertEqual(spellings["1.0e-12"]["occurrence_count"], 5)
        self.assertEqual(spellings["1.0e-8"]["occurrence_count"], 3)
        self.assertEqual(spellings["1.0e-10"]["occurrence_count"], 1)

    def test_artifact_rejects_count_or_claim_mutation(self):
        payload = json.loads(
            (HERE / "flyspeck_float_corpus.json").read_text(encoding="utf-8")
        )
        payload["inventory"]["occurrence_count"] -= 1
        with self.assertRaises(subject.CorpusError):
            subject.validate_artifact_shape(payload)

        payload = json.loads(
            (HERE / "flyspeck_float_corpus.json").read_text(encoding="utf-8")
        )
        payload["claim"] = "compiled Candle PASS"
        with self.assertRaises(subject.CorpusError):
            subject.validate_artifact_shape(payload)


if __name__ == "__main__":
    unittest.main()
