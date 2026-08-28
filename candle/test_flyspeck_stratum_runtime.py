#!/usr/bin/env python3

import copy
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


if __name__ == "__main__":
    unittest.main()
