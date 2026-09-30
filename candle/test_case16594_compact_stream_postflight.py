#!/usr/bin/env python3

from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


SCRIPT = (
    Path(__file__).parent
    / "compatibility"
    / "case16594_compact_stream_postflight.py"
)
SPEC = importlib.util.spec_from_file_location("case16594_postflight", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
POSTFLIGHT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(POSTFLIGHT)


READY = "CASE16594_TEST_READY"


def complete_log() -> str:
    lines: list[str] = []
    for index in range(POSTFLIGHT.SEGMENTS):
        cells = 3 if index == POSTFLIGHT.SEGMENTS - 1 else 4
        token_items = 5 if index == POSTFLIGHT.SEGMENTS - 1 else 8
        lines.append(
            "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_COMPLETE_CHUNK "
            f"event=begin index={index} total=219 cells={cells}"
        )
        lines.append(
            "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_COMPLETE_CHUNK "
            f"event=end index={index} total=219 cells={cells} "
            f"token_items={token_items} active_roots=1"
        )
    lines.extend([
        "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_STACK_COMPLETE_RESULT "
        "authenticated_leaves=860 numerical_cells=875 glue_nodes=874 "
        "numerical_computes=219 topology_segments=219 root_handoffs=1 "
        "assumptions=0 theorem_digest=8bb2c1bf3d1c1944d497c0da68b88207",
        "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_STACK_COMPLETE_OK "
        "DEVELOPMENT_NON_RELEASE",
        "# " + READY,
    ])
    return "\n".join(lines) + "\n"


class CompletedLogTest(unittest.TestCase):
    def test_accepts_complete_exact_stream(self) -> None:
        result = POSTFLIGHT.parse_completed_log(complete_log(), READY)
        self.assertEqual(result["segments"], 219)
        self.assertEqual(result["numerical_cells"], 875)
        self.assertEqual(result["token_items"], 1749)
        self.assertEqual(result["final_active_roots"], 1)

    def test_rejects_missing_segment(self) -> None:
        log = complete_log().replace(
            "CANDLE_CV_DISJUNCTIVE_CASE16594_COMPACT_COMPLETE_CHUNK "
            "event=end index=17 total=219 cells=4 token_items=8 active_roots=1\n",
            "",
        )
        with self.assertRaisesRegex(ValueError, "out-of-order|unmatched"):
            POSTFLIGHT.parse_completed_log(log, READY)

    def test_rejects_changed_digest(self) -> None:
        log = complete_log().replace(
            POSTFLIGHT.THEOREM_DIGEST,
            "0" * 32,
        )
        with self.assertRaisesRegex(ValueError, "terminal theorem result mismatch"):
            POSTFLIGHT.parse_completed_log(log, READY)

    def test_rejects_result_before_last_segment(self) -> None:
        lines = complete_log().splitlines()
        result = lines.pop(-3)
        lines.insert(-5, result)
        with self.assertRaisesRegex(ValueError, "terminal marker ordering mismatch"):
            POSTFLIGHT.parse_completed_log("\n".join(lines) + "\n", READY)

    def test_rejects_runtime_error(self) -> None:
        with self.assertRaisesRegex(ValueError, "error marker"):
            POSTFLIGHT.parse_completed_log(
                complete_log() + "EXCEPTION: synthetic\n", READY
            )

    def test_rejects_duplicate_ok(self) -> None:
        log = complete_log().replace(
            READY,
            POSTFLIGHT.OK_MARKER + "\n" + READY,
        )
        with self.assertRaisesRegex(ValueError, "duplicate OK"):
            POSTFLIGHT.parse_completed_log(log, READY)

    def test_phase_profile_aggregates_late_observations(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            log = root / "base.log"
            log.write_text("retained proof log\n", encoding="utf-8")
            profile = root / "profile.json"
            phases = [
                {
                    "lane": POSTFLIGHT.PROFILE_LANE,
                    "scope": "",
                    "phase": "batch-compute",
                    "result": "end",
                    "wall_seconds": wall,
                    "cpu_seconds": wall - 0.1,
                }
                for wall in (1.0, 2.0)
            ]
            profile.write_text(json.dumps({
                "schema": "candle-certificate-phase-profile-v1",
                "log": str(log),
                "start_at_end": True,
                "start_log_offset": 19,
                "stop_key": None,
                "stop_text": POSTFLIGHT.PROFILE_STOP_TEXT,
                "stop_seen": True,
                "skipped_leading_end_events": 1,
                "unclosed_phases": [],
                "events": [{}, {}, {}, {}, {}],
                "phases": phases,
                "samples": [{}],
                "duration_seconds": 3.0,
                "peak_sampled_rss_kib": 100,
            }), encoding="utf-8")
            result = POSTFLIGHT._validate_phase_profile(profile, log)
            aggregate = result["aggregates"]["batch-compute"]
            self.assertEqual(aggregate["count"], 2)
            self.assertEqual(aggregate["wall_seconds"], 3.0)
            self.assertEqual(aggregate["mean_wall_seconds"], 1.5)


if __name__ == "__main__":
    unittest.main()
