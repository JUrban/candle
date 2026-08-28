"""Focused tests for the regression runner's streaming protocol."""

import sys
import unittest

import pexpect

import regression


class OutputInactivityTests(unittest.TestCase):
    @staticmethod
    def _repl_for_script(script):
        repl = regression.CandleREPL.__new__(regression.CandleREPL)
        repl.process = pexpect.spawn(
            sys.executable,
            ["-c", script],
            encoding="utf-8",
        )
        repl.load_stack = ["long.ml"]
        repl.last_val = None
        return repl

    def test_progress_lines_refresh_timeout(self):
        repl = self._repl_for_script(
            "import time\n"
            "print('phase one', flush=True)\n"
            "time.sleep(0.06)\n"
            "print('phase two', flush=True)\n"
            "time.sleep(0.06)\n"
            "print('- Finished loading long.ml', flush=True)\n"
        )
        try:
            repl._check_output(timeout=0.1)
            self.assertEqual(repl.load_stack, [])
        finally:
            repl.kill()

    def test_error_sentinel_precedes_generic_progress(self):
        repl = self._repl_for_script(
            "print('still working', flush=True)\n"
            "print('ERROR: deterministic failure', flush=True)\n"
        )
        try:
            with self.assertRaisesRegex(
                    regression.LoadFailure, "deterministic failure"):
                repl._check_output(timeout=1)
        finally:
            repl.kill()

    def test_load_stack_and_value_sentinels_are_preserved(self):
        repl = self._repl_for_script(
            "print('- Loading dependency.ml', flush=True)\n"
            "print('val witness = true', flush=True)\n"
            "print('- Finished loading dependency.ml', flush=True)\n"
            "print('- Finished loading long.ml', flush=True)\n"
        )
        try:
            repl._check_output(timeout=1)
            self.assertEqual(repl.load_stack, ["long.ml", "dependency.ml"])
            repl._check_output(timeout=1)
            self.assertEqual(repl.last_val, "witness")
            repl._check_output(timeout=1)
            repl._check_output(timeout=1)
            self.assertEqual(repl.load_stack, [])
        finally:
            repl.kill()


if __name__ == "__main__":
    unittest.main()
