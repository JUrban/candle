#!/usr/bin/env python3
"""Host tests for the Flyspeck float performance input and gate contracts."""

from __future__ import annotations

import argparse
import hashlib
import inspect
import json
import os
from collections import Counter
from pathlib import Path
import struct
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import generate_flyspeck_float_performance as generator
import run_flyspeck_float_performance_gate as gate


class FloatPerformanceInputTests(unittest.TestCase):
    def test_pinned_break_case_contract_is_exact(self):
        self.assertEqual(generator.EXPECTED_FACET_COUNT, 15462)
        self.assertEqual(generator.EXPECTED_HALF_SPELLING_COUNT, 11640)
        self.assertEqual(generator.EXPECTED_LEAF_COUNT, 7479)
        self.assertEqual(generator.EXPECTED_ADD_CASE_COUNT, 463)
        self.assertEqual(generator.EXPECTED_UNIQUE_FLOAT_SPELLINGS, 1705)
        self.assertEqual(
            generator.EXPECTED_MANIFEST_SHA256,
            "2bb61e249baa2e8158da4b57f419a269504c7617f6bccefdec5465fcaab85380",
        )
        self.assertEqual(
            generator.EXPECTED_SOURCE["sha256"],
            "2b3c74156a5ee9a6b3b5b6905ff28a7fb21e7c50052ad37887b90b9ed3d5e499",
        )

    def test_histogram_masks_nested_comments_and_strings(self):
        source = '''
          (* Iarg_facet ((0,true),9.0000,0,Iarg_leaf 0)
             (* 8.0000 *) *)
          let ignored = "Iarg_facet 7.0000";;
          add_case ("real",
            Iarg_facet ((0,true),0.5000,0,Iarg_leaf 0));;
        '''
        encoded = json.dumps(
            {"0.5000": 1}, sort_keys=True, separators=(",", ":"),
        ).encode("utf-8")
        with mock.patch.multiple(
            generator,
            EXPECTED_FACET_COUNT=1,
            EXPECTED_LEAF_COUNT=1,
            EXPECTED_ADD_CASE_COUNT=1,
            EXPECTED_HALF_SPELLING_COUNT=1,
            EXPECTED_UNIQUE_FLOAT_SPELLINGS=1,
            EXPECTED_HISTOGRAM_SHA256=hashlib.sha256(encoded).hexdigest(),
        ):
            record = generator.histogram_record(source)
        self.assertEqual(record["histogram"], {"0.5000": 1})
        self.assertEqual(record["decimal_term_count"], 1)
        self.assertEqual(record["iarg_facet_count"], 1)

    def test_manifest_and_source_drift_fail_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            candle_root = root / "candle-root"
            flyspeck_root = root / "flyspeck-root"
            (candle_root / "candle").mkdir(parents=True)
            source_path = flyspeck_root / generator.SOURCE_PATH
            source_path.parent.mkdir(parents=True)
            source = b"Iarg_facet ((0,true),0.5000,0,Iarg_leaf 0);;\n"
            source_path.write_bytes(source)
            source_record = {
                "bytes": len(source),
                "md5": hashlib.md5(source).hexdigest(),  # nosec: test identity
                "sha256": hashlib.sha256(source).hexdigest(),
            }
            manifest = {
                "schema": 1,
                "repositories": {"flyspeck": {"commit": "a" * 40}},
                "source_node_count": 1,
                "build_sequence_count": 0,
                "source_nodes": {
                    generator.SOURCE_KEY: {
                        "repository": "flyspeck",
                        "path": generator.SOURCE_PATH.as_posix(),
                        **source_record,
                    },
                },
            }
            manifest_path = candle_root / "candle/flyspeck_manifest.json"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            manifest_sha256 = hashlib.sha256(
                manifest_path.read_bytes(),
            ).hexdigest()

            def fake_git(_, *arguments):
                if arguments == ("rev-parse", "HEAD"):
                    return "a" * 40
                if arguments == ("status", "--porcelain", "--untracked-files=all"):
                    return ""
                self.fail(f"unexpected git arguments: {arguments}")

            with mock.patch.multiple(
                    generator,
                    EXPECTED_FLYSPECK_COMMIT="a" * 40,
                    EXPECTED_MANIFEST_SHA256=manifest_sha256,
                    EXPECTED_SOURCE=source_record,
                    _fixed_git=fake_git):
                validated = generator.validate_inputs(candle_root, flyspeck_root)
                self.assertEqual(validated["flyspeck"]["sha256"],
                                 source_record["sha256"])
                manifest["source_nodes"][generator.SOURCE_KEY]["sha256"] = "0" * 64
                manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
                with self.assertRaisesRegex(generator.InputError,
                                            "manifest sha256 drift"):
                    generator.validate_inputs(candle_root, flyspeck_root)

    def test_call_time_literals_stay_inside_function_and_hoisted_do_not(self):
        call_time = generator._loop_source("call_time", 17)
        hoisted = generator._loop_source("hoisted", 17)
        call_observe = call_time.index("let candle_float_perf_call_time_observe")
        hoisted_observe = hoisted.index("let candle_float_perf_hoisted_observe")
        call_matches = list(generator.FLOAT_TOKEN.finditer(call_time))
        hoisted_matches = list(generator.FLOAT_TOKEN.finditer(hoisted))
        expected_tokens = Counter(list(generator.FLOAT_WORDS))
        self.assertEqual(Counter(match.group() for match in call_matches),
                         expected_tokens)
        self.assertEqual(Counter(match.group() for match in hoisted_matches),
                         expected_tokens)
        for literal in generator.FLOAT_WORDS:
            with self.subTest(literal=literal):
                call_position = next(match.start() for match in call_matches
                                     if match.group() == literal)
                hoisted_position = next(match.start() for match in hoisted_matches
                                        if match.group() == literal)
                self.assertGreater(call_position, call_observe)
                self.assertLess(hoisted_position, hoisted_observe)
        self.assertIn("candle_float_perf_call_time_loop 17", call_time)
        self.assertIn("candle_float_perf_hoisted_loop 17", hoisted)
        self.assertIn("not semantic, S2, or S3 evidence", call_time)

    def test_observed_words_are_host_ieee_binary64_bits(self):
        for literal, expected in generator.FLOAT_WORDS.items():
            with self.subTest(literal=literal):
                observed = struct.unpack(
                    ">Q", struct.pack(">d", float(literal)),
                )[0]
                self.assertEqual(observed, expected)

    def test_materialized_receipt_binds_every_output(self):
        histogram = {
            "decimal_term_count": 15462,
            "iarg_facet_count": 15462,
            "iarg_leaf_count": 7479,
            "add_case_count": 463,
            "unique_spelling_count": 1705,
            "zero_point_5000_count": 11640,
            "canonical_histogram_sha256": generator.EXPECTED_HISTOGRAM_SHA256,
            "histogram": {"0.5000": 11640},
        }
        validated = {
            "manifest": {"path": "candle/flyspeck_manifest.json",
                         "sha256": "1" * 64},
            "flyspeck": {"commit": generator.EXPECTED_FLYSPECK_COMMIT,
                         "source_path": generator.SOURCE_PATH.as_posix()},
            "source_text": "unused",
        }
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "generated"
            with mock.patch.object(generator, "validate_inputs",
                                   return_value=validated), \
                    mock.patch.object(generator, "histogram_record",
                                      return_value=histogram):
                receipt = generator.materialize(
                    Path("/candle"), Path("/flyspeck"), output, iterations=23,
                )
            self.assertEqual(receipt["iterations"], 23)
            self.assertEqual(set(receipt["outputs"]), {
                "break_case_log_float_histogram.json",
                "candle_float_call_time_loop.ml",
                "candle_float_hoisted_loop.ml",
            })
            for name, record in receipt["outputs"].items():
                self.assertEqual(record, generator.file_record(output / name))
            persisted = json.loads(
                (output / "flyspeck_float_performance_inputs.json").read_text()
            )
            self.assertEqual(persisted, receipt)

    def test_materialization_cannot_dirty_source_trees(self):
        validated = {
            "manifest": {"path": "candle/flyspeck_manifest.json",
                         "sha256": "1" * 64},
            "flyspeck": {"commit": generator.EXPECTED_FLYSPECK_COMMIT},
            "source_text": "unused",
        }
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            candle_root = root / "candle"
            flyspeck_root = root / "flyspeck"
            candle_root.mkdir()
            flyspeck_root.mkdir()
            with mock.patch.object(generator, "validate_inputs",
                                   return_value=validated):
                with self.assertRaisesRegex(
                        generator.InputError, "inside the Candle source tree"):
                    generator.materialize(
                        candle_root, flyspeck_root,
                        candle_root / "generated", iterations=1,
                    )


class FloatPerformanceGateTests(unittest.TestCase):
    def scenarios(self, break_seconds=5.0, call_seconds=4.0,
                  hoisted_seconds=2.0):
        return {
            "break_case_log": {"elapsed_seconds": break_seconds},
            "call_time": {"elapsed_seconds": call_seconds},
            "hoisted": {"elapsed_seconds": hoisted_seconds},
        }

    def test_thresholds_are_optional_but_never_hidden(self):
        self.assertEqual(gate.threshold_failures(
            self.scenarios(), None, None, None,
        ), [])
        self.assertEqual(gate.threshold_failures(
            self.scenarios(), 4.0, 3.0, 1.5,
        ), [
            "break_case_log elapsed threshold exceeded",
            "call_time elapsed threshold exceeded",
            "call_time/hoisted ratio threshold exceeded",
        ])
        self.assertEqual(gate.observation_outcome(
            generator.DEFAULT_ITERATIONS, [], None, None, None,
        ), ("observation_complete", False))
        self.assertEqual(gate.observation_outcome(
            generator.DEFAULT_ITERATIONS, [], 5.0, 4.0, 2.0,
        ), ("thresholds_satisfied", True))
        self.assertEqual(gate.observation_outcome(
            1, [], 5.0, 4.0, 2.0,
        ), ("observation_complete", False))
        self.assertEqual(gate.observation_outcome(
            generator.DEFAULT_ITERATIONS, ["too slow"], 5.0, 4.0, 2.0,
        ), ("thresholds_failed", True))

    def test_thresholds_must_be_positive_and_finite(self):
        self.assertEqual(gate._positive_float("0.125"), 0.125)
        for value in ("0", "-1", "nan", "inf", "-inf"):
            with self.subTest(value=value):
                with self.assertRaises(argparse.ArgumentTypeError):
                    gate._positive_float(value)

    def test_command_line_thresholds_never_self_certify_acceptance(self):
        source = inspect.getsource(gate._run_attempt)
        self.assertIn('"performance_accepted": False', source)
        self.assertIn('"reviewed_acceptance_contract": None', source)
        self.assertIn("transcript_dir.relative_to(evidence_dir)", source)

    def test_rss_scope_does_not_claim_attribution(self):
        self.assertIn("includes full-HOL baseline",
                      inspect.getsource(gate._measure_load))
        self.assertIn("check_axioms", inspect.getsource(
            gate.CandleSession.full_hol_preflight))
        self.assertIn("check_axioms", inspect.getsource(
            gate.CandleSession.axioms_postflight))
        self.assertIn("not semantic, S2, or S3", gate.CLAIM)

    def test_process_rss_is_root_not_largest_descendant(self):
        parents = {100: 1, 101: 100, 102: 101, 200: 1}
        rss = {100: 120, 101: 450, 102: 30, 200: 900}
        with mock.patch.object(gate.ProcessTreeSampler, "_snapshot",
                               return_value=(parents, rss)):
            self.assertEqual(gate.ProcessTreeSampler.tree_rss(100), (120, 600))

    def test_successful_session_requires_clean_exit(self):
        source = inspect.getsource(gate._run_one)
        self.assertIn("session.finish()", source)
        self.assertIn("session.abort()", source)
        self.assertIn("exitstatus == 0", inspect.getsource(
            gate.CandleSession.finish))

    def test_evidence_layout_is_retained_and_fail_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            candle_root = root / "candle"
            flyspeck_root = root / "flyspeck"
            candle_root.mkdir()
            flyspeck_root.mkdir()
            evidence = root / "evidence"
            generated, transcripts, report = gate._create_evidence_layout(
                evidence.resolve(), candle_root.resolve(),
                flyspeck_root.resolve(),
            )
            self.assertEqual(generated, evidence / "generated")
            self.assertTrue(transcripts.is_dir())
            self.assertEqual(report, evidence / "report.json")
            self.assertTrue(evidence.is_dir())
            with self.assertRaisesRegex(gate.GateError, "refusing to overwrite"):
                gate._create_evidence_layout(
                    evidence.resolve(), candle_root.resolve(),
                    flyspeck_root.resolve(),
                )
            with self.assertRaisesRegex(
                    gate.GateError, "inside the Candle source tree"):
                gate._create_evidence_layout(
                    (candle_root / "evidence").resolve(),
                    candle_root.resolve(), flyspeck_root.resolve(),
                )

    def test_failure_lifecycle_records_completed_scenarios(self):
        with tempfile.TemporaryDirectory() as temporary:
            evidence = Path(temporary) / "evidence"
            evidence.mkdir()
            attempt = {
                "schema": 1,
                "kind": "flyspeck-float-performance-attempt",
                "started_utc": "2026-01-01T00:00:00+00:00",
            }
            gate._write_json(evidence / "attempt.json", attempt)
            first = {"outcome": "pass", "elapsed_seconds": 1.25}
            gate._write_json(evidence / "scenario-call_time.json", first)
            arguments = mock.Mock(
                evidence_dir=evidence,
                candle_root=Path(temporary) / "candle",
                flyspeck_root=Path(temporary) / "flyspeck",
            )
            with mock.patch.object(gate, "_run_attempt",
                                   side_effect=gate.GateError("second failed")), \
                    mock.patch.object(gate.runtime_lock, "acquire_build_lock",
                                      return_value=mock.Mock()), \
                    mock.patch.object(gate, "_failure_postflight",
                                      return_value={"linked": False}):
                with self.assertRaisesRegex(gate.GateError,
                                            "retained evidence"):
                    gate.run(arguments)
            receipt = json.loads(
                (evidence / "receipt.json").read_text(encoding="utf-8")
            )
            self.assertEqual(receipt["state"], "failed")
            self.assertEqual(receipt["completed_scenarios"]["call_time"], first)
            self.assertEqual(receipt["validation_error"]["type"], "GateError")
            self.assertEqual(receipt["kind"],
                             "flyspeck-float-performance-receipt")

    def test_malformed_scenario_journal_is_recorded_in_failure_receipt(self):
        with tempfile.TemporaryDirectory() as temporary:
            evidence = Path(temporary) / "evidence"
            evidence.mkdir()
            gate._write_json(evidence / "attempt.json", {
                "schema": 1,
                "kind": "flyspeck-float-performance-attempt",
                "started_utc": "2026-01-01T00:00:00+00:00",
            })
            (evidence / "scenario-call_time.json").write_text(
                '{"outcome":', encoding="utf-8",
            )
            arguments = mock.Mock(
                evidence_dir=evidence,
                candle_root=Path(temporary) / "candle",
                flyspeck_root=Path(temporary) / "flyspeck",
            )
            with mock.patch.object(gate, "_run_attempt",
                                   side_effect=gate.GateError("failed")), \
                    mock.patch.object(gate.runtime_lock, "acquire_build_lock",
                                      return_value=mock.Mock()), \
                    mock.patch.object(gate, "_failure_postflight",
                                      return_value={}):
                with self.assertRaises(gate.GateError):
                    gate.run(arguments)
            receipt = json.loads(
                (evidence / "receipt.json").read_text(encoding="utf-8")
            )
            self.assertEqual(receipt["completed_scenarios"], {})
            self.assertIn("call_time", receipt["scenario_journal_errors"])
            self.assertIn("record",
                          receipt["scenario_journal_errors"]["call_time"])

    def test_postflight_rehashes_linked_source_and_generated_inputs(self):
        source = inspect.getsource(gate._run_attempt)
        failure_source = inspect.getsource(gate._failure_postflight)
        self.assertIn("validate_linked_record", source)
        self.assertIn("validate_linked_record", failure_source)
        self.assertIn("validate_inputs", source)
        self.assertIn("_verify_generated_inputs", source)
        self.assertIn("_verify_linked_runtime_archive", source)
        self.assertIn("_verify_performance_source_archive", source)

    def test_linked_runtime_archive_retains_and_rehashes_exact_inputs(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            candle_root = root / "candle"
            evidence = root / "evidence"
            build = candle_root / "candle/build"
            build.mkdir(parents=True)
            evidence.mkdir()
            linked_path = build / "cakeml-build-provenance.json"
            bootstrap_path = build / "bootstrap-provenance.json"
            bootstrap_log = build / "bootstrap.log"
            elf_path = root / "libm.so.6"
            bootstrap_path.write_text("{}\n", encoding="utf-8")
            bootstrap_log.write_text("successful bootstrap\n", encoding="utf-8")
            elf_path.write_bytes(b"elf")
            linked = {
                "bootstrap_record": generator.file_record(bootstrap_path),
                "bootstrap_log": generator.file_record(bootstrap_log),
                "runtime_elf_closure": {
                    "files": {
                        str(elf_path): generator.file_record(elf_path),
                    },
                },
            }
            linked_path.write_text(
                json.dumps(linked, sort_keys=True) + "\n", encoding="utf-8",
            )
            archived = gate._archive_linked_runtime(
                candle_root, evidence, linked,
            )
            gate._verify_linked_runtime_archive(evidence, archived, linked)
            self.assertEqual(
                {record["source_path"]
                 for record in archived["runtime_elf_objects"]},
                {str(elf_path)},
            )
            os.chmod(evidence / archived["bootstrap_log"]["path"], 0o644)
            (evidence / archived["bootstrap_log"]["path"]).write_text(
                "mutated\n", encoding="utf-8",
            )
            with self.assertRaisesRegex(gate.GateError,
                                        "bootstrap_log changed"):
                gate._verify_linked_runtime_archive(
                    evidence, archived, linked,
                )

    def test_real_source_archive_is_manifest_bound_and_loaded_by_gate(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            candle_root = root / "candle-root"
            flyspeck_root = root / "flyspeck-root"
            evidence = root / "evidence"
            (candle_root / "candle").mkdir(parents=True)
            evidence.mkdir()
            files = {
                "break_case_log": generator.SOURCE_PATH,
                "break_case_type": Path(
                    "text_formalization/nonlinear/break_case_type.hl"
                ),
            }
            records = {}
            for label, relative in files.items():
                path = flyspeck_root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(f"let {label} = true;;\n", encoding="utf-8")
                records[label] = generator.file_record(path)
            type_key = (
                "flyspeck:text_formalization/nonlinear/break_case_type.hl"
            )
            manifest = {
                "source_nodes": {
                    generator.SOURCE_KEY: {
                        "repository": "flyspeck",
                        "path": generator.SOURCE_PATH.as_posix(),
                        **records["break_case_log"],
                    },
                    type_key: {
                        "repository": "flyspeck",
                        "path": files["break_case_type"].as_posix(),
                        **records["break_case_type"],
                    },
                },
            }
            manifest_path = candle_root / "candle/flyspeck_manifest.json"
            manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
            linked = {"manifest_sha256": generator.file_record(
                manifest_path)["sha256"]}
            receipt = {"flyspeck": records["break_case_log"]}
            archived = gate._archive_performance_sources(
                candle_root, flyspeck_root, evidence, receipt, linked,
            )
            gate._verify_performance_source_archive(
                evidence, archived, linked,
            )
            implementation = inspect.getsource(gate._run_attempt)
            self.assertIn("source_paths", implementation)
            self.assertIn("archived_sources", implementation)
            retained = (
                evidence /
                archived["flyspeck"]["break_case_type"]["path"]
            )
            os.chmod(retained, 0o644)
            retained.write_text("mutated\n", encoding="utf-8")
            with self.assertRaisesRegex(gate.GateError,
                                        "break_case_type changed"):
                gate._verify_performance_source_archive(
                    evidence, archived, linked,
                )


if __name__ == "__main__":
    unittest.main()
