#!/usr/bin/env python3
"""Focused tests for Great100 source normalization and CSDP integration."""

import hashlib
import json
from pathlib import Path
import stat
import tempfile
import types
import unittest
from unittest import mock

import regression


class _ReplyProcess:
    def __init__(self):
        self.lines = []

    def sendline(self, value):
        self.lines.append(value)


class Great100NormalizationTest(unittest.TestCase):
    EXPECTED = {
        "100/ceva": (
            "Examples/sos.ml",
            "7618018fe0437d3ebaa77c56ed17f7fdfd9612aedacee980f0efe2274a6adfd3",
        ),
        "100/thales": (
            "Examples/sos.ml",
            "7618018fe0437d3ebaa77c56ed17f7fdfd9612aedacee980f0efe2274a6adfd3",
        ),
        "100/ramsey": (
            "100/ramsey.ml",
            "d48947f2ffb6b5dc20da21eafcc704e08cf709b40bdb2236f8fe81b315cae17c",
        ),
        "100/heron": (
            "100/heron.ml",
            "c8a2de1a36931331d156196fa1578f14ffa85043f3b541393ae1f553f813bc59",
        ),
    }

    def test_exact_g100_s_normalizations_materialize_and_rehash(self):
        original_hashes = {
            source: hashlib.sha256(
                (regression.CANDLE_ROOT / source).read_bytes()).hexdigest()
            for source, _digest in self.EXPECTED.values()
        }
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for target, (source, expected_hash) in self.EXPECTED.items():
                with self.subTest(target=target):
                    log_path = root / target.replace("/", "_") / "test.log"
                    log_path.parent.mkdir()
                    overlay = regression._prepare_normalization_overlay(
                        regression.Test(target, ()), log_path)
                    self.assertEqual(len(overlay["records"]), 1)
                    record = overlay["records"][0]
                    self.assertEqual(record["source"], source)
                    self.assertEqual(
                        record["normalized"]["sha256"], expected_hash)
                    self.assertEqual(
                        overlay["aliases"][record["normalized"]["path"]],
                        source)
                    regression._finish_normalization_overlay(overlay)
                    self.assertEqual(
                        json.loads(Path(overlay["receipt"]["path"]).read_text(
                            encoding="utf-8"))["schema"],
                        "candle-great100-normalization-overlay-v1")
        self.assertEqual(
            {
                source: hashlib.sha256(
                    (regression.CANDLE_ROOT / source).read_bytes()).hexdigest()
                for source in original_hashes
            },
            original_hashes,
        )

    def test_unselected_target_has_no_overlay(self):
        with tempfile.TemporaryDirectory() as temporary:
            self.assertIsNone(regression._prepare_normalization_overlay(
                regression.Test("100/arithmetic", ()),
                Path(temporary) / "test.log"))

    def test_original_hash_drift_fails_before_materialization(self):
        specification = regression.SourceNormalization(
            targets=("100/test",), source="100/test.ml",
            expected_sha256="0" * 64, normalized_sha256="1" * 64,
            replacements=((b"old", b"new"),))
        with tempfile.TemporaryDirectory() as source_directory, \
                tempfile.TemporaryDirectory() as log_directory:
            root = Path(source_directory)
            (root / "100").mkdir()
            (root / "100/test.ml").write_bytes(b"old")
            with mock.patch.object(regression, "CANDLE_ROOT", root), \
                    mock.patch.object(
                        regression, "TOP100_NORMALIZATIONS", (specification,)):
                with self.assertRaisesRegex(ValueError, "identity mismatch"):
                    regression._prepare_normalization_overlay(
                        regression.Test("100/test", ()),
                        Path(log_directory) / "test.log")

    def test_nonunique_rewrite_fails_closed(self):
        source = b"old old"
        specification = regression.SourceNormalization(
            targets=("100/test",), source="100/test.ml",
            expected_sha256=hashlib.sha256(source).hexdigest(),
            normalized_sha256="1" * 64,
            replacements=((b"old", b"new"),))
        with tempfile.TemporaryDirectory() as source_directory, \
                tempfile.TemporaryDirectory() as log_directory:
            root = Path(source_directory)
            (root / "100").mkdir()
            (root / "100/test.ml").write_bytes(source)
            with mock.patch.object(regression, "CANDLE_ROOT", root), \
                    mock.patch.object(
                        regression, "TOP100_NORMALIZATIONS", (specification,)):
                with self.assertRaisesRegex(ValueError, "replacement count"):
                    regression._prepare_normalization_overlay(
                        regression.Test("100/test", ()),
                        Path(log_directory) / "test.log")


class Great100CsdpBridgeTest(unittest.TestCase):
    def _bridge(self, directory, return_codes=(2,)):
        directory = Path(directory)
        setup = directory / "setup.ml"
        setup.write_text("setup\n", encoding="ascii")
        binary = directory / "csdp"
        binary.write_bytes(b"solver")
        binary.chmod(0o555)
        binary_record = regression._ordinary_file_record(binary)
        return {
            "target": "100/ceva",
            "binary": binary,
            "binary_record": binary_record,
            "directory": directory,
            "setup": setup,
            "setup_record": regression._ordinary_file_record(setup),
            "expected_return_codes": return_codes,
            "requests": [],
            "receipt": None,
        }

    @staticmethod
    def _repl(bridge):
        return types.SimpleNamespace(
            _great100_csdp_bridge=bridge,
            inactivity_timeout=10,
            wall_deadline=None,
            process=_ReplyProcess(),
        )

    @staticmethod
    def _solver_run(return_code):
        def run(arguments, **kwargs):
            kwargs["stdout"].write(b"solver stdout\n")
            kwargs["stderr"].write(b"solver stderr\n")
            Path(arguments[2]).write_bytes(b"solution")
            return types.SimpleNamespace(returncode=return_code)
        return run

    @staticmethod
    def _validate_test_binary(path):
        path = Path(path).resolve(strict=True)
        return path, regression._ordinary_file_record(path)

    def test_prepare_bridge_is_targeted_and_private(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            binary = root / "solver"
            binary.write_bytes(b"solver")
            binary.chmod(0o555)
            binary_record = regression._ordinary_file_record(binary)
            with mock.patch.object(
                    regression, "_validated_csdp_binary",
                    return_value=(binary, binary_record)):
                self.assertIsNone(regression._prepare_csdp_bridge(
                    regression.Test("100/arithmetic", ()),
                    root / "ordinary.log"))
                bridge = regression._prepare_csdp_bridge(
                    regression.Test("100/ceva", ()), root / "ceva.log")
            self.assertEqual(
                stat.S_IMODE(bridge["directory"].stat().st_mode), 0o700)
            self.assertEqual(
                bridge["expected_return_codes"],
                regression.CSDP_TARGET_RETURN_CODES["100/ceva"])
            self.assertIn(str(bridge["directory"]),
                          bridge["setup"].read_text(encoding="ascii"))

    def test_exact_request_runs_solver_and_retains_receipt(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            bridge = self._bridge(directory)
            (directory / "sos.dat-s").write_bytes(b"input")
            (directory / "param.csdp").write_bytes(b"parameters")
            repl = self._repl(bridge)
            marker = "\t".join((
                regression.CSDP_REQUEST_MARKER,
                str(directory / "sos.dat-s"), str(directory / "sos.out")))
            with mock.patch.object(
                    regression, "_validated_csdp_binary",
                    side_effect=self._validate_test_binary), \
                    mock.patch.object(
                        regression.subprocess, "run",
                        side_effect=self._solver_run(2)) as run:
                regression._csdp_progress_handler(repl, marker)
                regression._finish_csdp_bridge(bridge)
            self.assertEqual(repl.process.lines, ["2"])
            self.assertEqual(len(bridge["requests"]), 1)
            self.assertEqual(
                bridge["requests"][0]["output"]["sha256"],
                hashlib.sha256(b"solution").hexdigest())
            self.assertEqual(run.call_count, 1)
            receipt = json.loads(
                Path(bridge["receipt"]["path"]).read_text(encoding="utf-8"))
            self.assertEqual(receipt["expected_return_codes"], [2])
            self.assertEqual(receipt["requests"][0]["return_code"], 2)

    def test_escaped_and_malformed_requests_fail(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            repl = self._repl(self._bridge(directory))
            cases = (
                regression.CSDP_REQUEST_MARKER + "\tonly-one-path",
                "\t".join((regression.CSDP_REQUEST_MARKER,
                            str(directory / "../escape"),
                            str(directory / "sos.out"))),
            )
            for marker in cases:
                with self.subTest(marker=marker), self.assertRaises(
                        regression.LoadFailure):
                    regression._csdp_progress_handler(repl, marker)

    def test_return_code_sequence_mismatch_fails_without_reply(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            bridge = self._bridge(directory, return_codes=(0,))
            (directory / "sos.dat-s").write_bytes(b"input")
            (directory / "param.csdp").write_bytes(b"parameters")
            repl = self._repl(bridge)
            marker = "\t".join((
                regression.CSDP_REQUEST_MARKER,
                str(directory / "sos.dat-s"), str(directory / "sos.out")))
            with mock.patch.object(
                    regression, "_validated_csdp_binary",
                    side_effect=self._validate_test_binary), \
                    mock.patch.object(
                        regression.subprocess, "run",
                        side_effect=self._solver_run(2)):
                with self.assertRaisesRegex(
                        regression.LoadFailure, "sequence mismatch"):
                    regression._csdp_progress_handler(repl, marker)
            self.assertEqual(repl.process.lines, [])
            self.assertEqual(bridge["requests"], [])

    def test_incomplete_sequence_and_evidence_drift_fail(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            bridge = self._bridge(directory, return_codes=(2, 0))
            with self.assertRaisesRegex(
                    regression.LoadFailure, "incomplete"):
                regression._finish_csdp_bridge(bridge)

            bridge["expected_return_codes"] = ()
            bridge["setup"].write_text("changed\n", encoding="ascii")
            with mock.patch.object(
                    regression, "_validated_csdp_binary",
                    side_effect=self._validate_test_binary):
                with self.assertRaisesRegex(
                        regression.LoadFailure, "setup changed"):
                    regression._finish_csdp_bridge(bridge)


class Great100RunnerIntegrationTest(unittest.TestCase):
    def test_run_test_loads_both_setups_before_the_target(self):
        instances = []

        class FakeRepl:
            def __init__(self, **_kwargs):
                self.process = types.SimpleNamespace(pid=123)
                self.loads = []
                self.load_stack = []
                self.last_val = None
                instances.append(self)

            def load(self, path):
                self.loads.append(path)

            def finish(self):
                return 0

            def kill(self):
                pass

        class FakeSampler:
            peak_process_rss_kib = 1
            peak_tree_rss_kib = 1

            def __init__(self, _pid):
                pass

            def start(self):
                pass

            def stop(self):
                pass

        overlay = {
            "setup": Path("/derived/normalization-setup.ml"),
            "aliases": {"/derived/Examples/sos.ml": "Examples/sos.ml"},
        }
        bridge = {"setup": Path("/derived/csdp-setup.ml")}
        test = regression.Test("100/ceva", ("100/ceva.ml",))
        with tempfile.TemporaryDirectory() as temporary, \
                mock.patch.object(
                    regression, "_prepare_normalization_overlay",
                    return_value=overlay), \
                mock.patch.object(
                    regression, "_prepare_csdp_bridge", return_value=bridge), \
                mock.patch.object(
                    regression, "_finish_normalization_overlay") as finish_overlay, \
                mock.patch.object(
                    regression, "_finish_csdp_bridge") as finish_bridge, \
                mock.patch.object(regression, "CandleREPL", FakeRepl), \
                mock.patch.object(regression, "ProcessTreeSampler", FakeSampler):
            result = regression.run_test(
                test, inactivity_timeout=10, log_dir=temporary)

        self.assertIs(result.status, regression.TestStatus.PASS)
        self.assertEqual(instances[0].loads, [
            "hol.ml",
            "/derived/normalization-setup.ml",
            "/derived/csdp-setup.ml",
            "100/ceva.ml",
        ])
        self.assertEqual(
            instances[0]._normalization_finish_aliases, overlay["aliases"])
        self.assertIs(
            instances[0]._progress_line_handler,
            regression._csdp_progress_handler)
        self.assertIs(instances[0]._great100_csdp_bridge, bridge)
        finish_overlay.assert_called_once_with(overlay)
        finish_bridge.assert_called_once_with(bridge)


if __name__ == "__main__":
    unittest.main()
