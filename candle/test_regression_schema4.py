#!/usr/bin/env python3
"""Static and adversarial tests for the promotable Great 100 schema-4 gate."""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock
from datetime import datetime, timezone

import regression


class Great100Schema4Test(unittest.TestCase):
    def _transcript(self, suite, process, linked, fingerprint_inside=True):
        fingerprint = "\t".join([
            regression.FINGERPRINT_MARKER, b"T".hex(), b"t".hex(),
            b"h".hex(), b"c".hex(), b"a".hex(), "0", "3"])
        state = "\t".join([
            regression.STATE_FINGERPRINT_MARKER, b"s".hex(), b"y".hex(),
            b"c".hex(), b"d".hex(), b"a".hex(), "1", "2", "3", "3"])
        lines = [
            f"{regression.SUITE_MARKER}\t{suite}",
            f"{regression.PROCESS_MARKER}\t{suite}\t{process}\tSTART",
            f"{regression.LINKED_RECORD_MARKER}\t{linked}",
        ]
        if fingerprint_inside:
            lines.extend([fingerprint, state])
        lines.append(
            f"{regression.PROCESS_MARKER}\t{suite}\t{process}\tCOMPLETE")
        if not fingerprint_inside:
            lines.extend([fingerprint, state])
        return "\n".join(lines) + "\n"

    def test_marker_order_and_exact_linked_observation(self):
        suite, process, linked = "1" * 64, "2" * 64, "3" * 64
        with tempfile.NamedTemporaryFile(
                mode="w", encoding="utf-8", delete=False) as stream:
            stream.write(self._transcript(suite, process, linked))
            path = Path(stream.name)
        try:
            self.assertEqual(
                regression._read_process_markers(path, suite, process, linked),
                {"suite_line": 0, "start_line": 1, "linked_line": 2,
                 "complete_line": 5})
            with self.assertRaisesRegex(regression.LoadFailure, "linked marker"):
                regression._read_process_markers(
                    path, suite, process, "4" * 64)
        finally:
            path.unlink()

    def test_fingerprint_outside_process_interval_fails(self):
        suite, process, linked = "1" * 64, "2" * 64, "3" * 64
        with tempfile.NamedTemporaryFile(
                mode="w", encoding="utf-8", delete=False) as stream:
            stream.write(self._transcript(
                suite, process, linked, fingerprint_inside=False))
            path = Path(stream.name)
        try:
            with self.assertRaisesRegex(regression.LoadFailure, "outside"):
                regression._read_process_markers(path, suite, process, linked)
        finally:
            path.unlink()

    def test_completion_marker_is_nonce_bound(self):
        suite, process = "a" * 64, "b" * 64
        source = regression._fingerprint_request_source(
            ("EGCD",), suite, process)
        self.assertIn(
            f"{regression.PROCESS_MARKER}\\t{suite}\\t{process}\\tCOMPLETE",
            source)
        with self.assertRaisesRegex(ValueError, "nonce"):
            regression._fingerprint_request_source(("EGCD",), suite, "bad")

    def test_manifest_source_closure_is_exact_65_66_97(self):
        manifest = json.loads((
            regression.CANDLE_ROOT / "candle/top100_manifest.json"
        ).read_text(encoding="utf-8"))
        closure = regression._source_closure(manifest)
        self.assertEqual(
            (closure["target_count"], closure["source_file_count"],
             closure["fingerprint_request_count"]), (65, 66, 97))
        digest_input = dict(closure)
        del digest_input["sha256"]
        self.assertEqual(closure["sha256"],
                         regression._canonical_digest(digest_input))

    def test_runtime_state_rejects_any_contract_mutation(self):
        base = {
            "candle_git_head": "0" * 40, "candle_git_status": [],
            "execution_contract": {}, "execution_contract_sha256": "1" * 64,
            "source_closure": {"sha256": "2" * 64},
            "independent_approval": {"sha256": "3" * 64},
            "linked_record": {"sha256": "4" * 64},
            "candle_executable": {"sha256": "5" * 64},
        }
        changed = json.loads(json.dumps(base))
        changed["execution_contract_sha256"] = "6" * 64
        with mock.patch.object(
                regression, "_capture_suite_contract", return_value=changed):
            with self.assertRaisesRegex(ValueError, "execution_contract"):
                regression._runtime_state(base)

    def test_shell_emits_all_authenticated_startup_markers(self):
        source = (regression.CANDLE_ROOT / "candle.sh").read_text(encoding="utf-8")
        self.assertIn("CANDLE_GREAT100_SUITE_V1\\t%s", source)
        self.assertIn("CANDLE_GREAT100_PROCESS_V1\\t%s\\t%s\\tSTART", source)
        self.assertIn("CANDLE_LINKED_PROVENANCE_V1\\t%s", source)
        self.assertLess(source.index("CANDLE_GREAT100_SUITE_V1"),
                        source.index("check-linked"))
        self.assertLess(source.index("check-linked"),
                        source.index("CANDLE_LINKED_PROVENANCE_V1"))

    def test_ordinary_file_record_rejects_symlink(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            target = root / "target"
            target.write_bytes(b"evidence")
            link = root / "link"
            link.symlink_to(target)
            with self.assertRaisesRegex(ValueError, "ordinary file"):
                regression._ordinary_file_record(link)
            hardlink = root / "hardlink"
            hardlink.hardlink_to(target)
            with self.assertRaisesRegex(ValueError, "ordinary file"):
                regression._ordinary_file_record(target)
            hardlink.unlink()
            record = regression._ordinary_file_record(target)
            self.assertEqual(record["bytes"], 8)
            self.assertEqual(record["sha256"], hashlib.sha256(b"evidence").hexdigest())

    def test_completed_suite_rehashes_transcripts_and_rejects_nonce_reuse(self):
        suite_nonce = "a" * 64
        approval_sha256 = "b" * 64
        linked_sha256 = "c" * 64
        contract = {
            "linked_record": {"sha256": linked_sha256},
            "independent_approval": {"sha256": approval_sha256},
        }
        runtime = {
            "candle_git_head": "d" * 40, "candle_git_status": [],
            "linked_record_sha256": linked_sha256,
            "candle_executable": {"path": "/cake", "bytes": 1,
                                  "sha256": "e" * 64},
            "execution_contract_sha256": "f" * 64,
            "source_closure_sha256": "0" * 64,
        }
        expected = {
            "approval_sha256": approval_sha256,
            "serializer_sha256": "1" * 64,
            "theorems": [], "post_state": {},
        }
        tests = []
        results = []
        with tempfile.TemporaryDirectory() as temporary:
            for index in range(65):
                name = f"100/t{index:02d}"
                log_path = Path(temporary) / f"{index}.log"
                log_path.write_text(f"transcript {index}\n", encoding="utf-8")
                transcript = regression._ordinary_file_record(log_path)
                process_nonce = f"{index + 1:064x}"
                evidence = {
                    "suite_nonce": suite_nonce,
                    "process_nonce": process_nonce,
                    "pid": index + 100,
                    "started_utc": datetime.now(timezone.utc).isoformat(),
                    "completed_utc": datetime.now(timezone.utc).isoformat(),
                    "exit_code": 0,
                    "markers": {"suite_line": 0, "start_line": 1,
                                "linked_line": 2, "complete_line": 5},
                    "linked_record_sha256": linked_sha256,
                    "transcript": transcript,
                    "pre_runtime_state": runtime,
                    "post_runtime_state": runtime,
                    "resource_sampling": {
                        "interval_seconds": 0.25, "sample_count": 2,
                        "root_observed": True, "sampler_completed": True,
                        "peak_process_rss_kib": 1,
                        "peak_tree_rss_kib": 1,
                    },
                }
                tests.append(regression.Test(
                    name, (), (), "audited", expected))
                results.append(regression.TestResult(
                    name, regression.TestStatus.PASS, log_path=str(log_path),
                    fingerprints={
                        "status": "matched", "mapping_status": "audited",
                        "expected_identities_present": True,
                        "serializer": {"path": "candle/fingerprint.ml",
                                       "sha256": "1" * 64},
                        "theorems": [], "post_state": {},
                        "approval_sha256": approval_sha256,
                    }, process_evidence=evidence))
            with mock.patch.object(
                    regression, "_runtime_state", return_value=runtime):
                regression._validate_top100_results(
                    results, tests, suite_nonce, contract)
                Path(results[0].log_path).write_text(
                    "persistent mutation\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "transcript changed"):
                    regression._validate_top100_results(
                        results, tests, suite_nonce, contract)
                Path(results[0].log_path).write_text(
                    "transcript 0\n", encoding="utf-8")
                results[1].process_evidence["process_nonce"] = \
                    results[0].process_evidence["process_nonce"]
                with self.assertRaisesRegex(ValueError, "reused process nonce"):
                    regression._validate_top100_results(
                        results, tests, suite_nonce, contract)

    def test_promotable_output_paths_are_new_canonical_and_unaliased(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            report = root / "run.json"
            logs = root / "logs"
            self.assertEqual(
                regression._prepare_top100_evidence_paths(report, logs),
                (report, logs))
            self.assertTrue(logs.is_dir())
            report.write_text("existing\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "must not already exist"):
                regression._prepare_top100_evidence_paths(report, logs)
            report.unlink()
            (logs / "old.log").write_text("old\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "must be empty"):
                regression._prepare_top100_evidence_paths(report, logs)
            (logs / "old.log").unlink()
            logs.rmdir()
            alias = root / "alias"
            alias.symlink_to(root, target_is_directory=True)
            with self.assertRaisesRegex(ValueError, "ordinary directory"):
                regression._prepare_top100_evidence_paths(
                    report, alias / "logs")
            with self.assertRaisesRegex(ValueError, "must be absolute"):
                regression._prepare_top100_evidence_paths(
                    Path("relative.json"), Path("relative-logs"))


if __name__ == "__main__":
    unittest.main()
