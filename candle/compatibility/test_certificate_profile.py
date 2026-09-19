#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
from pathlib import Path
import tempfile
import unittest


HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "certificate_profile_instrument",
    HERE / "certificate_profile_instrument.py",
)
assert SPEC and SPEC.loader
SUBJECT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SUBJECT)
OBSERVER_SPEC = importlib.util.spec_from_file_location(
    "certificate_phase_profile",
    HERE / "certificate_phase_profile.py",
)
assert OBSERVER_SPEC and OBSERVER_SPEC.loader
OBSERVER = importlib.util.module_from_spec(OBSERVER_SPEC)
OBSERVER_SPEC.loader.exec_module(OBSERVER)


class InstrumentationTests(unittest.TestCase):
    def test_hash_helper(self) -> None:
        self.assertEqual(
            SUBJECT.sha256(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        )

    def test_replace_once_fails_closed(self) -> None:
        with self.assertRaisesRegex(SUBJECT.InstrumentationError, "found 0"):
            SUBJECT.replace_once("hello", "missing", "replacement", "anchor")
        with self.assertRaisesRegex(SUBJECT.InstrumentationError, "found 2"):
            SUBJECT.replace_once("xx", "x", "replacement", "anchor")

    def test_marker_parser_preserves_nonlinear_case_names(self) -> None:
        line = (
            "# CANDLE_CERT_PROFILE lane=nonlinear "
            "scope=prep-QITNPEA  5400790175 b split(3/4) "
            "phase=iarg-tree-reconstruction event=end"
        )
        match = OBSERVER.MARKER.search(line)
        self.assertIsNotNone(match)
        assert match is not None
        self.assertEqual(match["scope"], "prep-QITNPEA  5400790175 b split(3/4)")
        self.assertEqual(match["phase"], "iarg-tree-reconstruction")

    def test_exact_current_sources_instrument(self) -> None:
        root = Path("/project/flyspeck-candle-runs")
        lp = (
            root
            / "v246-focused-action292-through295-pre296-v66-001"
            / "overlay/formal_lp/hypermap/main/prove_flyspeck_lp.hl"
        )
        nonlinear = (
            root
            / "v247-focused-action296-nonlinear-v66-001"
            / "overlay/text_formalization/nonlinear"
        )
        if not lp.exists() or not nonlinear.exists():
            self.skipTest("current development overlays are unavailable")
        lp_result = SUBJECT.instrument_lp(lp.read_text())
        break_result = SUBJECT.instrument_nonlinear_break(
            (nonlinear / "break_case_exec.hl").read_text()
        )
        assembly_result = SUBJECT.instrument_nonlinear_assembly(
            (nonlinear / "mk_all_ineq.hl").read_text()
        )
        self.assertIn("phase=", lp_result)
        self.assertNotIn("incr candle_lp_profile_terminal", lp_result)
        self.assertEqual(lp_result.count("CANDLE_CERT_PROFILE"), 1)
        self.assertIn("iarg-tree-reconstruction", break_result)
        self.assertIn("serialized-prep-cases", assembly_result)


if __name__ == "__main__":
    unittest.main()
