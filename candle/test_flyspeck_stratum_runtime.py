#!/usr/bin/env python3

import copy
import hashlib
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import flyspeck_stratum_runtime as subject


class StratumRuntimeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.actions = [
            {
                "index": 0,
                "target": "general/a.hl",
                "source_sha256": "1" * 64,
            },
            {
                "index": 1,
                "target": "../formal_lp/b.ml",
                "source_sha256": "2" * 64,
            },
        ]
        self.prefix = (
            b"(* exact leading material *)\n"
            b'#flyspeck_needs "general/a.hl";;\n'
            b"(* retained boundary comment *)\n"
            b'#flyspeck_needs "../formal_lp/b.ml";;\n'
        )

    def test_instrumentation_is_ordered_and_output_only(self) -> None:
        result = subject.instrument_prefix(self.prefix, self.actions).decode()
        self.assertIn(self.prefix.splitlines()[0].decode(), result)
        first_action = result.index('#flyspeck_needs "general/a.hl";;')
        first_marker = result.index(subject.ACTION_PREFIX + " 000")
        second_action = result.index('#flyspeck_needs "../formal_lp/b.ml";;')
        second_marker = result.index(subject.ACTION_PREFIX + " 001")
        self.assertLess(first_action, first_marker)
        self.assertLess(first_marker, second_action)
        self.assertLess(second_action, second_marker)
        self.assertEqual(result.count("print_endline"), 2)

    def test_instrumentation_rejects_target_drift(self) -> None:
        actions = copy.deepcopy(self.actions)
        actions[1]["target"] = "wrong.ml"
        with self.assertRaisesRegex(subject.ContractError, "directive drift: 1"):
            subject.instrument_prefix(self.prefix, actions)

    def test_log_requires_every_exact_marker_in_order(self) -> None:
        boundary = "00-test-through-001"
        log = "\n".join([
            subject.PREFLIGHT_MARKER,
            f"{subject.ACTION_PREFIX} 000 {'1' * 64}",
            f"{subject.ACTION_PREFIX} 001 {'2' * 64}",
            f"{subject.SUCCESS_MARKER} {boundary} 2",
        ])
        subject.validate_log(log, self.actions, boundary)

    def test_log_rejects_duplicate_or_late_marker(self) -> None:
        boundary = "00-test-through-001"
        marker0 = f"{subject.ACTION_PREFIX} 000 {'1' * 64}"
        marker1 = f"{subject.ACTION_PREFIX} 001 {'2' * 64}"
        final = f"{subject.SUCCESS_MARKER} {boundary} 2"
        with self.assertRaisesRegex(subject.ContractError, "duplicate action marker: 0"):
            subject.validate_log(
                "\n".join([subject.PREFLIGHT_MARKER, marker0, marker0, marker1, final]),
                self.actions, boundary,
            )
        with self.assertRaisesRegex(subject.ContractError, "out of order"):
            subject.validate_log(
                "\n".join([subject.PREFLIGHT_MARKER, marker1, marker0, final]),
                self.actions, boundary,
            )

    def test_log_rejects_top_level_exception(self) -> None:
        boundary = "00-test-through-001"
        log = "\n".join([
            subject.PREFLIGHT_MARKER,
            f"{subject.ACTION_PREFIX} 000 {'1' * 64}",
            f"{subject.ACTION_PREFIX} 001 {'2' * 64}",
            f"{subject.SUCCESS_MARKER} {boundary} 2",
            "EXCEPTION: injected",
        ])
        with self.assertRaisesRegex(subject.ContractError, "top-level error"):
            subject.validate_log(log, self.actions, boundary)

    def test_exact_boundary_fingerprint_requests(self) -> None:
        self.assertEqual(subject.fingerprint_requests("00-base-through-029"), [])
        self.assertEqual(
            subject.fingerprint_requests("05-lp_support-through-184"),
            ["Linear_programming_results.linear_programming_results_th"],
        )
        final = subject.fingerprint_requests("07-final_assembly-through-296")
        self.assertEqual(len(final), 4)
        self.assertEqual(final[-1], "Candle_flyspeck_l2.tame_imp_kepler_conjecture")

    def test_candidate_fingerprint_parser_is_fail_closed(self) -> None:
        name = "Linear_programming_results.linear_programming_results_th"
        fields = [
            subject.FINGERPRINT_MARKER,
            name.encode().hex(),
            b"theorem".hex(), b"hypotheses".hex(), b"conclusion".hex(),
            b"axioms".hex(), "0", "3",
        ]
        report = subject.parse_fingerprints(
            "\t".join(fields), [name], Path(subject.__file__).resolve(),
        )
        self.assertEqual(report["status"], "observed_uncompared")
        self.assertFalse(report["approved_reference_present"])
        self.assertEqual(
            report["theorems"][0]["theorem_sha256"],
            hashlib.sha256(b"theorem").hexdigest(),
        )
        bad = fields.copy()
        bad[-1] = "4"
        with self.assertRaisesRegex(subject.ContractError, "global axiom count"):
            subject.parse_fingerprints(
                "\t".join(bad), [name], Path(subject.__file__).resolve(),
            )

    def test_fingerprint_boundary_requires_terminal_marker(self) -> None:
        boundary = "05-lp_support-through-184"
        theorem_names = subject.fingerprint_requests(boundary)
        source_log = "\n".join([
            subject.PREFLIGHT_MARKER,
            f"{subject.ACTION_PREFIX} 000 {'1' * 64}",
            f"{subject.ACTION_PREFIX} 001 {'2' * 64}",
            f"{subject.SUCCESS_MARKER} {boundary} 2",
        ])
        with self.assertRaisesRegex(subject.ContractError, "fingerprint success marker"):
            subject.validate_log(source_log, self.actions, boundary, theorem_names)
        subject.validate_log(
            source_log + "\n" +
            f"{subject.FINGERPRINT_SUCCESS_MARKER} {boundary} 1",
            self.actions, boundary, theorem_names,
        )


if __name__ == "__main__":
    unittest.main()
