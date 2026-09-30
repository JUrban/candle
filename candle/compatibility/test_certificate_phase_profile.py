#!/usr/bin/env python3

import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
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

    def test_inline_event_marker_has_empty_scope(self) -> None:
        fields = SUBJECT.marker_fields(
            "CANDLE_CERT_PROFILE lane=compact-stream "
            "phase=batch-compute-begin"
        )
        self.assertEqual(fields, {
            "lane": "compact-stream",
            "scope": "",
            "phase": "batch-compute",
            "event": "begin",
        })

    def test_scoped_marker_fields_remain_unchanged(self) -> None:
        fields = SUBJECT.marker_fields(
            "CANDLE_CERT_PROFILE lane=nonlinear-leaf scope=target "
            "phase=formal-verification event=end"
        )
        self.assertEqual(fields, {
            "lane": "nonlinear-leaf",
            "scope": "target",
            "phase": "formal-verification",
            "event": "end",
        })

    def test_proc_sample_is_read_only_and_reports_this_process(self) -> None:
        sample = SUBJECT.proc_sample(os.getpid(), os.sysconf("SC_CLK_TCK"))
        self.assertIsNotNone(sample)
        assert sample is not None
        self.assertGreater(sample["vmsize_kib"], 0)
        self.assertGreater(sample["rss_kib"], 0)

    def test_observer_closes_a_real_external_phase(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            log = root / "proof.log"
            output = root / "profile.json"
            child_code = (
                "from pathlib import Path; import time; "
                f"p=Path({str(log)!r}); "
                "p.write_text('CANDLE_CERT_PROFILE lane=nonlinear-leaf "
                "scope=target phase=total event=begin\\n'); "
                "time.sleep(0.3); "
                "p.open('a').write('CANDLE_CERT_PROFILE lane=nonlinear-leaf "
                "scope=target phase=total event=end\\n'); "
                "time.sleep(0.3)"
            )
            child = subprocess.Popen([sys.executable, "-c", child_code])
            observed = subprocess.run(
                [
                    sys.executable,
                    str(HERE / "certificate_phase_profile.py"),
                    "--pid", str(child.pid),
                    "--log", str(log),
                    "--output", str(output),
                    "--poll-seconds", "0.02",
                    "--stop-key", "nonlinear-leaf/target/total",
                    "--wait-for-log-seconds", "2",
                ],
                check=False,
                capture_output=True,
                text=True,
                timeout=3,
            )
            self.assertEqual(child.wait(timeout=2), 0)
            self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
            data = json.loads(output.read_bytes())
            self.assertTrue(data["stop_seen"])
            self.assertEqual(data["unclosed_phases"], [])
            self.assertEqual(len(data["phases"]), 1)
            self.assertEqual(data["phases"][0]["phase"], "total")
            self.assertGreater(data["phases"][0]["wall_seconds"], 0.1)

    def test_observer_can_begin_on_a_future_log_marker(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            log = root / "proof.log"
            output = root / "profile.json"
            child_code = (
                "from pathlib import Path; import time; "
                f"p=Path({str(log)!r}); "
                "p.write_text('ignored history\\n'); time.sleep(0.2); "
                "p.open('a').write('SAMPLE_BEGIN\\n'); time.sleep(0.1); "
                "p.open('a').write('CANDLE_CERT_PROFILE lane=sample "
                "phase=work-begin\\n'); time.sleep(0.2); "
                "p.open('a').write('CANDLE_CERT_PROFILE lane=sample "
                "phase=work-end\\n'); time.sleep(0.2)"
            )
            child = subprocess.Popen([sys.executable, "-c", child_code])
            observed = subprocess.run(
                [
                    sys.executable,
                    str(HERE / "certificate_phase_profile.py"),
                    "--pid", str(child.pid),
                    "--log", str(log),
                    "--output", str(output),
                    "--poll-seconds", "0.02",
                    "--start-at-end",
                    "--start-text", "SAMPLE_BEGIN",
                    "--stop-key", "sample//work",
                    "--wait-for-log-seconds", "2",
                ],
                check=False,
                capture_output=True,
                text=True,
                timeout=3,
            )
            self.assertEqual(child.wait(timeout=2), 0)
            self.assertEqual(observed.returncode, 0, observed.stdout + observed.stderr)
            data = json.loads(output.read_bytes())
            self.assertTrue(data["start_seen"])
            self.assertEqual(data["start_text"], "SAMPLE_BEGIN")
            self.assertTrue(data["stop_seen"])
            self.assertEqual(len(data["phases"]), 1)
            self.assertEqual(data["skipped_leading_end_events"], 0)


if __name__ == "__main__":
    unittest.main()
