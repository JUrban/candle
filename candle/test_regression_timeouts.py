#!/usr/bin/env python3
"""Deterministic tests for inactivity and total-wall timeout semantics."""

import json
from pathlib import Path
import sys
import time
import unittest
from unittest import mock

import pexpect

import regression


class _FakeProcess:
    def __init__(self, pid):
        self.pid = pid
        self.close_calls = []

    def close(self, force=False):
        self.close_calls.append(force)


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
                "inactivity_resets_on": "each complete REPL output line",
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

    def test_teardown_kills_verified_pexpect_process_group(self):
        repl = object.__new__(regression.CandleREPL)
        repl.process = _FakeProcess(123)
        with (
            mock.patch.object(regression.os, "getpgid", return_value=123),
            mock.patch.object(regression.os, "getsid", return_value=123),
            mock.patch.object(regression.os, "killpg") as killpg,
        ):
            repl.kill()
        killpg.assert_called_once_with(123, regression.signal.SIGKILL)
        self.assertEqual(repl.process.close_calls, [True])

    def test_teardown_never_kills_an_unrelated_process_group(self):
        repl = object.__new__(regression.CandleREPL)
        repl.process = _FakeProcess(123)
        with (
            mock.patch.object(regression.os, "getpgid", return_value=99),
            mock.patch.object(regression.os, "getsid", return_value=99),
            mock.patch.object(regression.os, "killpg") as killpg,
        ):
            repl.kill()
        killpg.assert_not_called()
        self.assertEqual(repl.process.close_calls, [True])

    @staticmethod
    def _stream_repl(script, inactivity_timeout, wall_timeout=None):
        repl = object.__new__(regression.CandleREPL)
        repl.inactivity_timeout = inactivity_timeout
        repl.wall_deadline = (
            time.monotonic() + wall_timeout
            if wall_timeout is not None else None)
        repl.load_stack = ["long.ml"]
        repl.last_val = None
        repl.process = pexpect.spawn(
            sys.executable, ["-c", script], encoding="utf-8")
        return repl

    def test_complete_progress_lines_refresh_inactivity(self):
        repl = self._stream_repl(
            "import time\n"
            "print('phase one', flush=True)\n"
            "time.sleep(0.06)\n"
            "print('phase two', flush=True)\n"
            "time.sleep(0.06)\n"
            "print('- Finished loading long.ml', flush=True)\n",
            inactivity_timeout=0.1)
        try:
            repl._check_output()
            self.assertEqual(repl.load_stack, [])
        finally:
            repl.kill()

    def test_progress_never_extends_absolute_wall_deadline(self):
        repl = self._stream_repl(
            "import time\n"
            "print('phase one', flush=True)\n"
            "time.sleep(0.06)\n"
            "print('phase two', flush=True)\n"
            "time.sleep(0.06)\n"
            "print('phase three', flush=True)\n"
            "time.sleep(0.06)\n"
            "print('- Finished loading long.ml', flush=True)\n",
            inactivity_timeout=1, wall_timeout=0.15)
        try:
            with self.assertRaises(regression.WallTimeout):
                repl._check_output()
        finally:
            repl.kill()

    def test_error_sentinel_precedes_generic_progress(self):
        repl = self._stream_repl(
            "print('still working', flush=True)\n"
            "print('ERROR: deterministic failure', flush=True)\n",
            inactivity_timeout=1)
        try:
            with self.assertRaisesRegex(
                    regression.LoadFailure, "deterministic failure"):
                repl._check_output()
        finally:
            repl.kill()


if __name__ == "__main__":
    unittest.main()
