#!/usr/bin/env python3

import importlib.util
import os
from pathlib import Path
import unittest


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "certificate_phase_profile", HERE / "certificate_phase_profile.py",
)
assert SPEC and SPEC.loader
SUBJECT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SUBJECT)


class CertificatePhaseProfileTests(unittest.TestCase):
    def test_marker_parser_preserves_scope_and_phase(self) -> None:
        line = (
            "# CANDLE_CERT_PROFILE lane=nonlinear-leaf scope=target "
            "phase=formal-verification event=end"
        )
        match = SUBJECT.MARKER.search(line)
        self.assertIsNotNone(match)
        assert match is not None
        self.assertEqual(match["lane"], "nonlinear-leaf")
        self.assertEqual(match["scope"], "target")
        self.assertEqual(match["phase"], "formal-verification")
        self.assertEqual(match["event"], "end")

    def test_proc_sample_is_read_only_and_reports_this_process(self) -> None:
        sample = SUBJECT.proc_sample(os.getpid(), os.sysconf("SC_CLK_TCK"))
        self.assertIsNotNone(sample)
        assert sample is not None
        self.assertGreater(sample["vmsize_kib"], 0)
        self.assertGreater(sample["rss_kib"], 0)


if __name__ == "__main__":
    unittest.main()
