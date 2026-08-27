#!/usr/bin/env python3
"""Deterministic tests for inactivity and total-wall timeout semantics."""

import json
from pathlib import Path
import unittest

import regression


class TimeoutPolicyTest(unittest.TestCase):
    def test_unbounded_wall_uses_inactivity_limit(self):
        self.assertEqual(
            regression._effective_expect_timeout(10, None, now=100),
            (10.0, False))

    def test_wall_deadline_never_resets_with_progress(self):
        deadline = 130
        self.assertEqual(
            regression._effective_expect_timeout(10, deadline, now=100),
            (10.0, False))
        # A progress event can begin another inactivity window, but only the
        # nine seconds remaining on the original wall deadline are available.
        self.assertEqual(
            regression._effective_expect_timeout(10, deadline, now=121),
            (9, True))
        with self.assertRaises(regression.WallTimeout):
            regression._effective_expect_timeout(10, deadline, now=130)

    def test_report_contract_distinguishes_both_limits(self):
        self.assertEqual(
            regression._timeout_policy(1800, None),
            {
                "inactivity_timeout_seconds": 1800,
                "inactivity_resets_on": (
                    "each recognized Loading, val, or Finished progress event"),
                "inactivity_scope": (
                    "each REPL expect wait, including initial boot"),
                "total_wall_timeout_seconds": None,
                "total_wall_scope": (
                    "process spawn through fingerprint capture"),
                "progress_extends_total_wall_deadline": False,
            })

    def test_total_elapsed_includes_boot(self):
        result = regression.TestResult(
            "target", regression.TestStatus.TIMEOUT,
            boot_elapsed=1, hol_elapsed=2, test_elapsed=3,
            fingerprint_elapsed=4, timeout_kind="wall")
        self.assertEqual(result.total, 10)
        self.assertEqual(result.timeout_kind, "wall")
        record = regression.Reporter.result_record(result, ("target.ml",))
        self.assertEqual(record["boot_elapsed_seconds"], 1)
        self.assertEqual(record["total_elapsed_seconds"], 10)
        self.assertEqual(record["timeout_kind"], "wall")

    def test_live_baseline_is_recorded_as_unbounded_wall(self):
        manifest = json.loads(
            Path(regression.CANDLE_ROOT / "candle" / "top100_manifest.json")
            .read_text(encoding="utf-8"))
        policy = manifest["execution_contract"][
            "recorded_live_baseline_timeout_policy"]
        self.assertEqual(policy["boot_inactivity_timeout_seconds"], 30)
        self.assertEqual(policy["load_inactivity_timeout_seconds"], 1800)
        self.assertIsNone(policy["total_wall_timeout_seconds"])
        self.assertEqual(policy["wall_policy"], "unbounded")


if __name__ == "__main__":
    unittest.main()
