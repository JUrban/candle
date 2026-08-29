#!/usr/bin/env python3

import copy
import hashlib
import importlib
import json
import os
import py_compile
import signal
import subprocess
import sys
import tempfile
import types
import unittest
from unittest import mock
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import flyspeck_stratum_runtime as subject


class StratumRuntimeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.actions = [
            {
                "index": 0,
                "target": "general/a.hl",
                "source_sha256": "1" * 64,
                "identity_basename": "a.hl",
                "identity_md5": "3" * 32,
            },
            {
                "index": 1,
                "target": "../formal_lp/b.ml",
                "source_sha256": "2" * 64,
                "identity_basename": "b.ml",
                "identity_md5": "4" * 32,
            },
        ]
        for action in self.actions:
            ledger_delta = [{
                "key": f"flyspeck:{action['target']}",
                "classification": "observed-outer-source",
                "source_sha256": action["source_sha256"],
                "identity_basename": action["identity_basename"],
                "identity_md5": action["identity_md5"],
            }]
            action["logical_source_delta"] = ledger_delta
            action["logical_source_delta_sha256"] = subject.canonical_sha256(
                ledger_delta
            )
        self.prefix = (
            b"(* exact leading material *)\n"
            b'#flyspeck_needs "general/a.hl";;\n'
            b"(* retained boundary comment *)\n"
            b'#flyspeck_needs "../formal_lp/b.ml";;\n'
        )
        self.nonce = "a" * 32
        self.runtime_temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.runtime_temporary.cleanup)
        self.runtime_executable_path = (
            Path(self.runtime_temporary.name) /
            "snapshot/candle/candle/build/cake"
        )
        self.runtime_executable_path.parent.mkdir(parents=True)
        self.runtime_executable_path.write_bytes(b"compiled Candle test runtime")
        self.runtime_executable_path.chmod(0o555)
        closure_records = [
            {
                "index": 0,
                "key": "flyspeck:../formal_lp/b.ml",
                "classification": "observed-outer-source",
                "source_sha256": "2" * 64,
                "source_md5": "4" * 32,
                "execution_normalization": {
                    "id": "TEST-NORMALIZATION-001",
                    "normalized_sha256": "9" * 64,
                    "normalized_md5": "b" * 32,
                },
            },
            {
                "index": 1,
                "key": "flyspeck:general/a.hl",
                "classification": "observed-outer-source",
                "source_sha256": "1" * 64,
                "source_md5": "3" * 32,
                "execution_normalization": None,
            },
        ]
        self.logical_source_closure = {
            "schema": 3,
            "kind": "candle-flyspeck-selected-nested-logical-source-closure",
            "policy": subject.SOURCE_CLOSURE_POLICY,
            "order": subject.SOURCE_CLOSURE_ORDER,
            "completed_action_count": 2,
            "final_target_selected": False,
            "record_count": len(closure_records),
            "ordered_record_sha256": subject.canonical_sha256(closure_records),
            "records": closure_records,
            "physical_loader_cache_trace": False,
            "execution_observation": subject.SOURCE_CLOSURE_OBSERVATION,
            "self_certifies_nested_execution": False,
            "s2_s3_evidence": False,
        }
        self.generated_control_records = {
            "candle:candle/build/insulate.ml": {
                "bytes": 1,
                "sha256": "c" * 64,
                "md5": "d" * 32,
            },
            "candle:candle/flyspeck_source_digests.ml": {
                "bytes": 1,
                "sha256":
                    "343ac5686f3163eb4fe6512bdbfe316999aba500d60d40cca4209d7d4263e562",
                "md5": "6e7e5f9291886516c4daf79605620176",
            },
        }
        trace_bindings = []
        for index, key in enumerate(subject.SOURCE_TRACE_TOP_LEVEL_CONTROLS):
            path = f"/trace/{index:02d}.ml"
            payload = {
                "resolved": path,
                "canonical": path,
                "key": key,
                "basename": Path(path).name,
                "source_md5": f"{index + 1:032x}",
                "source_sha256": f"{index + 1:064x}",
                "selected": path,
                "selected_sha256": f"{index + 1:064x}",
                "normalization": "-",
            }
            trace_bindings.append({
                "binding_id": subject.canonical_sha256(payload), **payload,
            })
        for index, record in enumerate(closure_records, start=4):
            path = f"/trace/{index:02d}.ml"
            normalization = record["execution_normalization"]
            payload = {
                "resolved": path,
                "canonical": path,
                "key": record["key"],
                "basename": Path(path).name,
                "source_md5": record["source_md5"],
                "source_sha256": record["source_sha256"],
                "selected": path,
                "selected_sha256": (
                    record["source_sha256"] if normalization is None else
                    normalization["normalized_sha256"]
                ),
                "normalization": (
                    "-" if normalization is None else normalization["id"]
                ),
            }
            trace_bindings.append({
                "binding_id": subject.canonical_sha256(payload), **payload,
            })
        trace_binding_by_key = {item["key"]: item for item in trace_bindings}
        trace_events = []
        request_specs = (
            ("control:runtime-setup", None),
            (closure_records[0]["key"], 0),
            ("control:instrumented-prefix", None),
            (closure_records[1]["key"], 2),
            ("control:stratum-check", None),
            ("control:postlude", None),
        )
        for request_id, (key, parent) in enumerate(request_specs):
            binding = trace_binding_by_key[key]
            trace_events.append({
                "event": "request",
                "id": request_id,
                "parent": parent,
                "kind": "#use" if parent is None else "needs",
                "binding_id": binding["binding_id"],
                "key": binding["key"],
                "cache_before": "fresh-cache",
            })
            if parent is not None:
                trace_events.append({
                    "event": "outcome", "id": request_id,
                    "outcome": "evaluated",
                })
                trace_events.append({
                    "event": "outcome", "id": parent,
                    "outcome": "evaluated",
                })
            elif key in ("control:stratum-check", "control:postlude"):
                trace_events.append({
                    "event": "outcome", "id": request_id,
                    "outcome": "evaluated",
                })
        trace_events.append({
            "event": "terminal", "request_count": len(request_specs),
        })
        required_keys = sorted({
            *subject.SOURCE_TRACE_TOP_LEVEL_CONTROLS,
            *(record["key"] for record in closure_records),
        })
        self.source_trace_contract = {
            "schema": 1,
            "protocol": subject.SOURCE_TRACE_PROTOCOL,
            "nonce": self.nonce,
            "activation": subject.SOURCE_TRACE_ACTIVATION,
            "binding_count": len(trace_bindings),
            "ordered_binding_sha256": subject.canonical_sha256(trace_bindings),
            "bindings": trace_bindings,
            "required_key_count": len(required_keys),
            "ordered_required_key_sha256":
                subject.canonical_sha256(required_keys),
            "required_keys": required_keys,
            "top_level_control_keys":
                list(subject.SOURCE_TRACE_TOP_LEVEL_CONTROLS),
        }
        self.source_trace_observation = {
            "schema": 1,
            "protocol": subject.SOURCE_TRACE_PROTOCOL,
            "nonce": self.nonce,
            "event_count": len(trace_events),
            "ordered_event_sha256": subject.canonical_sha256(trace_events),
            "events": trace_events,
            "request_count": len(request_specs),
            "cache_skip_count": 0,
            "observed_key_count": len(required_keys),
            "ordered_observed_key_sha256":
                subject.canonical_sha256(required_keys),
            "observed_keys": required_keys,
            "status": "closed-loader-owned-session",
        }

    def action_marker(self, index: int, outcome: str) -> str:
        action = self.actions[index]
        return (
            f"{subject.ACTION_PREFIX} {self.nonce} {index:03d} "
            f"{action['source_sha256']} "
            f"{action['logical_source_delta_sha256']} {outcome}"
        )

    def direct_attempt(
        self, expected_actions: list[dict],
        boundary_id: str = "00-test-through-001",
    ) -> dict:
        digest = {"bytes": 1, "sha256": "a" * 64, "md5": "b" * 32}
        inputs = {
            field: copy.deepcopy(digest)
            for field in subject.DIRECT_INPUT_FIELDS
            if field not in {
                "controller_execution", "authenticated_prefix",
                "runtime_executable",
            }
        }
        inputs["authenticated_prefix"] = {
            "path": "prefix.ml", **copy.deepcopy(digest),
        }
        inputs["runtime_executable"] = {
            "path": str(self.runtime_executable_path),
            **subject.hash_file(self.runtime_executable_path),
        }
        source_root = "/candle/candle"
        source_bindings = {
            "cakeml_artifact_provenance.py":
                "compiled-from-captured-source-bytes",
            "flyspeck_stratum_plan.py":
                "compiled-from-captured-source-bytes",
            "flyspeck_stratum_runtime.py":
                "startup-captured-after-initial-compilation",
            "reference_protocol.py":
                "compiled-from-captured-source-bytes",
            "runtime_lock.py": "compiled-from-captured-source-bytes",
        }
        local_sources = []
        committed_sources = {}
        for index, (label, binding) in enumerate(source_bindings.items(), start=1):
            retained = {
                "bytes": index,
                "sha256": f"{index:064x}",
                "md5": f"{index:032x}",
            }
            local_sources.append({
                "label": label,
                "source_path": f"{source_root}/{label}",
                "execution_binding": binding,
                "path": f"controller/python-source/{label}",
                **retained,
            })
            committed_sources[label] = {
                "repository_path": f"candle/{label}",
                "index_tag": "H",
                **retained,
            }
        expected_executable = subject.EXPECTED_PYTHON_RUNTIME["executable"]
        expected_elf = subject.EXPECTED_PYTHON_RUNTIME["elf_closure"]
        elf_objects = []
        for index, (path, expected) in enumerate(
            sorted(expected_elf["files"].items()), start=10,
        ):
            elf_objects.append({
                "source_path": path,
                "path": (
                    "controller/python-runtime-elf/" +
                    f"{expected['sha256'][:16]}-{Path(path).name}"
                ),
                "bytes": expected["bytes"],
                "sha256": expected["sha256"],
                "md5": f"{index:032x}",
            })
        host_tools = []
        for index, (label, expected) in enumerate(
            sorted(subject.EXPECTED_CONTROLLER_TOOLS.items()), start=20,
        ):
            host_tools.append({
                "label": label,
                **expected,
                "path": (
                    f"controller/host-tools/{label}-" +
                    Path(expected["resolved_path"]).name
                ),
                "md5": f"{index:032x}",
            })
        inputs["controller_execution"] = {
            "source_root": source_root,
            "direct_script_startup": {
                "module_name": "__main__",
                "spec_is_none": True,
                "cached_is_none": True,
                "argv0": f"{source_root}/flyspeck_stratum_runtime.py",
                "source_path": f"{source_root}/flyspeck_stratum_runtime.py",
            },
            "commit_binding": {
                "candle_commit": "c" * 40,
                "sources": committed_sources,
            },
            "python_startup_flags":
                copy.deepcopy(subject.EXPECTED_PYTHON_STARTUP_FLAGS),
            "python_startup_options":
                copy.deepcopy(subject.EXPECTED_PYTHON_STARTUP_OPTIONS),
            "initial_top_level_compilation_in_host_trust_boundary": True,
            "local_sources": local_sources,
            "python_runtime": {
                "execution_binding":
                    subject.EXPECTED_PYTHON_RUNTIME["execution_binding"],
                "version": subject.EXPECTED_PYTHON_RUNTIME["version"],
                "executable": {
                    "source_path": expected_executable["path"],
                    "path": "controller/python-runtime/python3.12",
                    "bytes": expected_executable["bytes"],
                    "sha256": expected_executable["sha256"],
                    "md5": "a" * 32,
                },
                "elf_policy": expected_elf["policy"],
                "elf_dynamic_path_tags": expected_elf["dynamic_path_tags"],
                "elf_roles": expected_elf["roles"],
                "virtual_elf_objects": expected_elf["virtual_objects"],
                "elf_objects": elf_objects,
            },
            "host_tools": host_tools,
            "git_environment": {
                "LC_ALL": "C", "PATH": "/usr/bin:/bin",
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_CONFIG_GLOBAL": "/dev/null",
                "GIT_TERMINAL_PROMPT": "0",
                "GIT_NO_REPLACE_OBJECTS": "1",
                "GIT_OPTIONAL_LOCKS": "0",
            },
            "broader_python_standard_library_in_host_trust_boundary": True,
        }
        return {
            "schema": 4,
            "kind": "candle-flyspeck-compiled-stratum-attempt",
            "claim": subject.DIRECT_EVIDENCE_CLAIM,
            "state": "running",
            "started_utc": "2026-08-29T00:00:00Z",
            "boundary_id": boundary_id,
            "diagnostic_only": False,
            "attempt_nonce": self.nonce,
            "action_count": len(expected_actions),
            "ordered_expected_action_sha256":
                subject.canonical_sha256(expected_actions),
            "expected_action_events": expected_actions,
            "timeout_seconds": 60,
            "resource_limits": {
                "cpu_seconds": 60,
                "address_space_bytes": subject.GIB,
                "output_file_bytes": subject.GIB,
            },
            "fresh_process_replay_from_action_zero": True,
            "cooperative_build_run_lock_held": True,
            "runtime_lock": {
                "path": "/candle/build", "object": "directory_inode",
                "mode": "shared", "device": 0, "inode": 1,
            },
            "concurrent_mutation_model": (
                "cooperating build/launcher processes serialized; hostile "
                "same-user path mutation is outside this evidence model"
            ),
            "process_state_checkpoint": None,
            "evidence_contract": {
                "schema": "candle-flyspeck-direct-runtime-evidence-v4",
                "allowed_action_outcomes": list(subject.ACTION_OUTCOMES),
                "physical_loader_cache_skip_allowed":
                    "only loader-authenticated needs cache-skip events",
                "logical_source_closure_policy": subject.SOURCE_CLOSURE_POLICY,
                "logical_source_closure_order": subject.SOURCE_CLOSURE_ORDER,
                "selected_loadt_ledger_delta_included": True,
                "physical_loader_cache_trace_included": True,
                "physical_source_trace_protocol": subject.SOURCE_TRACE_PROTOCOL,
                "pre_trace_control_exclusion": "control:runtime-config",
                "s2_s3_approval_included": False,
            },
            "expected_logical_source_closure": self.logical_source_closure,
            "expected_physical_source_trace": self.source_trace_contract,
            "runtime_environment_policy": (
                "minimal PATH/LC_ALL=C/CML sizes; reject LD_*, GLIBC_TUNABLES, "
                "BASH_ENV, and ENV"
            ),
            "runtime_environment": {"LC_ALL": "C", "PATH": "/usr/bin:/bin"},
            "inputs": inputs,
            "repositories": {"candle": "c" * 40, "flyspeck": "f" * 40},
        }

    def direct_receipt_envelope(self, attempt: dict) -> dict:
        log_record = subject.data_record(
            self.direct_log_text(attempt["boundary_id"]).encode("utf-8")
        )
        return {
            **attempt,
            "state": "completed",
            "finished_utc": "2026-08-29T00:00:01Z",
            "timed_out": False,
            "exit_code": 0,
            "command": [
                attempt["inputs"]["runtime_executable"]["path"], "--candle",
            ],
            "child_resources": {
                "user_cpu_seconds": 1.0,
                "system_cpu_seconds": 0.1,
                "max_rss_kib": 1,
                "major_page_faults": 0,
                "minor_page_faults": 1,
            },
            "log": {
                "path": "candle.log", **log_record,
            },
            "initial_attempt": {
                "path": "attempt.json",
                **subject.data_record(subject.json_bytes(attempt)),
            },
            "action_markers_validated": len(attempt["expected_action_events"]),
            "action_events": None,
            "logical_source_closure": None,
            "physical_source_trace": None,
            "semantic_fingerprints": None,
            "s2_s3_evidence": False,
            "validation_error": None,
            "postflight_reauthenticated": True,
        }

    def direct_log_text(self, boundary_id: str) -> str:
        binding_by_id = {
            item["binding_id"]: item
            for item in self.source_trace_contract["bindings"]
        }
        lines = [f"{subject.PREFLIGHT_MARKER} {self.nonce}"]
        for event in self.source_trace_observation["events"]:
            if event["event"] == "request":
                binding = binding_by_id[event["binding_id"]]
                lines.append("\t".join((
                    subject.SOURCE_TRACE_PREFIX,
                    self.nonce,
                    "REQUEST",
                    str(event["id"]),
                    "-" if event["parent"] is None else str(event["parent"]),
                    event["kind"],
                    event["binding_id"],
                    event["key"],
                    binding["basename"],
                    binding["source_md5"],
                    binding["source_sha256"],
                    binding["selected_sha256"],
                    binding["normalization"],
                    event["cache_before"],
                )))
            elif event["event"] == "outcome":
                lines.append("\t".join((
                    subject.SOURCE_TRACE_PREFIX,
                    self.nonce,
                    "OUTCOME",
                    str(event["id"]),
                    event["outcome"],
                )))
            else:
                lines.append("\t".join((
                    subject.SOURCE_TRACE_PREFIX,
                    self.nonce,
                    "TERMINAL",
                    str(event["request_count"]),
                )))
        lines.extend((
            self.action_marker(0, "load"),
            self.action_marker(1, "skip-ledger"),
            f"{subject.SUCCESS_MARKER} {self.nonce} {boundary_id} 2",
        ))
        lines.extend(
            subject.logical_source_marker(self.nonce, record)
            for record in self.logical_source_closure["records"]
        )
        lines.append(subject.logical_source_terminal(
            self.nonce, boundary_id, self.logical_source_closure,
        ))
        return "\n".join(lines) + "\n"

    def validate_receipt(self, receipt: dict) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            log_path = Path(temporary) / "candle.log"
            log_path.write_text(
                self.direct_log_text(receipt["boundary_id"]), encoding="utf-8",
            )
            log_path.chmod(0o444)
            subject.validate_direct_evidence_v4_artifact(
                receipt, receipt=True, log_path=log_path,
                runtime_executable_path=self.runtime_executable_path,
            )

    def test_pinned_python_elf_contract_tracks_provenance_schema(self) -> None:
        closure = subject.EXPECTED_PYTHON_RUNTIME["elf_closure"]
        helper = subject.cakeml_artifact_provenance
        self.assertEqual(set(closure), helper.ELF_DYNAMIC_CLOSURE_FIELDS)
        self.assertEqual(closure["policy"], helper.ELF_DYNAMIC_CLOSURE_POLICY)
        helper.validate_elf_closure_record(
            closure, "pinned Python runtime", allowed_dynamic_path_tags={},
        )
        stale = copy.deepcopy(closure)
        stale.pop("dynamic_path_tags")
        with self.assertRaisesRegex(
            helper.ProvenanceError, "malformed pinned Python runtime",
        ):
            helper.validate_elf_closure_record(
                stale, "pinned Python runtime", allowed_dynamic_path_tags={},
            )
    def test_instrumentation_is_ordered_and_output_only(self) -> None:
        result = subject.instrument_prefix(self.prefix, self.actions, self.nonce).decode()
        self.assertIn(self.prefix.splitlines()[0].decode(), result)
        first_action = result.index('#flyspeck_needs "general/a.hl";;')
        first_marker = result.index(subject.ACTION_PREFIX + f" {self.nonce} 000")
        second_action = result.index('#flyspeck_needs "../formal_lp/b.ml";;')
        second_marker = result.index(subject.ACTION_PREFIX + f" {self.nonce} 001")
        self.assertLess(first_action, first_marker)
        self.assertLess(first_marker, second_action)
        self.assertLess(second_action, second_marker)
        self.assertEqual(result.count("candle_flyspeck_stratum_commit_action"), 2)
        self.assertNotIn("print_endline", result)

    def test_instrumentation_rejects_target_drift(self) -> None:
        actions = copy.deepcopy(self.actions)
        actions[1]["target"] = "wrong.ml"
        with self.assertRaisesRegex(subject.ContractError, "directive drift: 1"):
            subject.instrument_prefix(self.prefix, actions, self.nonce)

    def test_log_requires_every_exact_marker_in_order(self) -> None:
        boundary = "00-test-through-001"
        log = "\n".join([
            f"{subject.PREFLIGHT_MARKER} {self.nonce}",
            self.action_marker(0, "load"),
            self.action_marker(1, "skip-ledger"),
            f"{subject.SUCCESS_MARKER} {self.nonce} {boundary} 2",
        ])
        events = subject.validate_log(log, self.actions, boundary, self.nonce)
        self.assertEqual([event["outcome"] for event in events],
                         ["load", "skip-ledger"])

    def test_exact_setup_action_transition_runs_in_compiled_ocaml_fixture(self) -> None:
        setup = (
            Path(subject.__file__).parent / "flyspeck_stratum_setup.ml"
        ).read_text(encoding="utf-8")
        start_text = (
            "let candle_flyspeck_stratum_previous_loaded_files = "
            "ref !loaded_files;;"
        )
        end_text = '    print_endline (marker ^ " " ^ outcome);;'
        start = setup.index(start_text)
        end = setup.index(end_text, start) + len(end_text)
        exact_transition_source = setup[start:end]
        fixture = "\n".join((
            "let loaded_files = ref ([] : (string * string) list);;",
            'let first = ("a.hl","11111111111111111111111111111111");;',
            'let second = ("b.ml","22222222222222222222222222222222");;',
            'let outer = ("serialization.hl","33333333333333333333333333333333");;',
            'let nested = ("update_database_400.ml",',
            '              "44444444444444444444444444444444");;',
            "let candle_flyspeck_stratum_action_identities =",
            "  [first;first;outer;second];;",
            "let candle_flyspeck_stratum_action_ledger_deltas =",
            "  [[first];[first];[outer;nested];[second]];;",
            exact_transition_source,
            "loaded_files := [first];;",
            'candle_flyspeck_stratum_commit_action 0 first "ACTION0";;',
            'candle_flyspeck_stratum_commit_action 1 first "ACTION1";;',
            "loaded_files := outer :: nested :: !loaded_files;;",
            'candle_flyspeck_stratum_commit_action 2 outer "ACTION2";;',
            "(try",
            '   candle_flyspeck_stratum_commit_action 3 second "ACTION3"',
            " with Failure message ->",
            '   print_endline ("MISMATCH " ^ message));;',
            "",
        ))
        compiler = Path("/usr/bin/ocamlc")
        self.assertTrue(compiler.is_file(), "missing pinned OCaml compiler")
        version = subprocess.run(
            [str(compiler), "-version"], check=True, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        ).stdout.strip()
        self.assertEqual(version, "4.14.1")
        with tempfile.TemporaryDirectory() as temporary:
            fixture_path = Path(temporary) / "action_transition.ml"
            executable = Path(temporary) / "action_transition"
            fixture_path.write_text(fixture, encoding="utf-8")
            subprocess.run(
                [str(compiler), "-o", str(executable), str(fixture_path)],
                check=True, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            result = subprocess.run(
                [str(executable)], check=True, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            )
        self.assertEqual(result.stderr, "")
        self.assertEqual(result.stdout.splitlines(), [
            "ACTION0 load",
            "ACTION1 skip-ledger",
            "ACTION2 load",
            "MISMATCH Flyspeck action was skipped by the physical loader "
            "cache without its logical identity",
        ])

    def test_exact_check_action_identity_projection_compiles_and_runs(self) -> None:
        check = (
            Path(subject.__file__).parent / "flyspeck_stratum_check.ml"
        ).read_text(encoding="utf-8")
        start_text = (
            "let candle_flyspeck_stratum_observed_action_identities ="
        )
        end_text = (
            '  failwith "Flyspeck stratum action event order mismatch";;'
        )
        start = check.index(start_text)
        end = check.index(end_text, start) + len(end_text)
        exact_projection_source = check[start:end]
        fixture = "\n".join((
            "let rev = List.rev;;",
            "let map = List.map;;",
            'let first = ("a.hl","11111111111111111111111111111111");;',
            'let second = ("b.ml","22222222222222222222222222222222");;',
            "let candle_flyspeck_stratum_action_events =",
            '  ref [(1,second,[second],"load");',
            '       (0,first,[first],"load")];;',
            "let candle_flyspeck_stratum_action_identities = [first;second];;",
            exact_projection_source,
            'print_endline "PROJECTION_OK";;',
            "",
        ))
        compiler = Path("/usr/bin/ocamlc")
        self.assertTrue(compiler.is_file(), "missing pinned OCaml compiler")
        version = subprocess.run(
            [str(compiler), "-version"], check=True, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        ).stdout.strip()
        self.assertEqual(version, "4.14.1")
        with tempfile.TemporaryDirectory() as temporary:
            fixture_path = Path(temporary) / "action_projection.ml"
            executable = Path(temporary) / "action_projection"
            fixture_path.write_text(fixture, encoding="utf-8")
            subprocess.run(
                [str(compiler), "-o", str(executable), str(fixture_path)],
                check=True, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
            result = subprocess.run(
                [str(executable)], check=True, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            )
        self.assertEqual(result.stdout, "PROJECTION_OK\n")
        self.assertEqual(result.stderr, "")

    def test_log_rejects_duplicate_or_late_marker(self) -> None:
        boundary = "00-test-through-001"
        marker0 = self.action_marker(0, "load")
        marker1 = self.action_marker(1, "load")
        final = f"{subject.SUCCESS_MARKER} {self.nonce} {boundary} 2"
        preflight = f"{subject.PREFLIGHT_MARKER} {self.nonce}"
        with self.assertRaisesRegex(subject.ContractError, "duplicate action 0 marker"):
            subject.validate_log(
                "\n".join([preflight, marker0, marker0, marker1, final]),
                self.actions, boundary, self.nonce,
            )
        with self.assertRaisesRegex(subject.ContractError, "out of order"):
            subject.validate_log(
                "\n".join([preflight, marker1, marker0, final]),
                self.actions, boundary, self.nonce,
            )

    def test_log_rejects_loader_cache_skip_and_unknown_action_outcomes(self) -> None:
        boundary = "00-test-through-001"
        preflight = f"{subject.PREFLIGHT_MARKER} {self.nonce}"
        marker1 = self.action_marker(1, "load")
        final = f"{subject.SUCCESS_MARKER} {self.nonce} {boundary} 2"
        for outcome in ("skip-loader-cache", "forged"):
            marker0 = (
                self.action_marker(0, outcome)
            )
            with self.assertRaisesRegex(
                subject.ContractError, f"unsupported action 0 outcome: {outcome}",
            ):
                subject.validate_log(
                    "\n".join([preflight, marker0, marker1, final]),
                    self.actions, boundary, self.nonce,
                )

    def test_log_rejects_top_level_exception(self) -> None:
        boundary = "00-test-through-001"
        log = "\n".join([
            f"{subject.PREFLIGHT_MARKER} {self.nonce}",
            self.action_marker(0, "load"),
            self.action_marker(1, "load"),
            f"{subject.SUCCESS_MARKER} {self.nonce} {boundary} 2",
            "EXCEPTION: injected",
        ])
        with self.assertRaisesRegex(subject.ContractError, "top-level error"):
            subject.validate_log(log, self.actions, boundary, self.nonce)

    def test_quoted_or_prefixed_marker_text_is_not_an_event(self) -> None:
        boundary = "00-test-through-001"
        quoted = "\n".join([
            f'source "{subject.PREFLIGHT_MARKER} {self.nonce}"',
            f'print_endline "{self.action_marker(0, "load")}";;',
            f'prefix {self.action_marker(1, "load")}',
            f'quoted {subject.SUCCESS_MARKER} {self.nonce} {boundary} 2',
        ])
        with self.assertRaisesRegex(subject.ContractError, "stratum preflight marker"):
            subject.validate_log(quoted, self.actions, boundary, self.nonce)

    def test_exact_boundary_fingerprint_requests(self) -> None:
        self.assertEqual(subject.fingerprint_requests("00-base-through-029"), [])
        self.assertEqual(subject.fingerprint_requests("d1-diagnostic-through-018"), [])
        self.assertEqual(
            subject.fingerprint_requests("05-lp_support-through-184"),
            ["Linear_programming_results.linear_programming_results_th"],
        )
        final = subject.fingerprint_requests("07-final_assembly-through-296")
        self.assertEqual(len(final), 4)
        self.assertEqual(final[-1], "Candle_flyspeck_l2.tame_imp_kepler_conjecture")
        self.assertEqual(
            subject.dependency_history_requests("05-lp_support-through-184"),
            [],
        )
        self.assertEqual(
            subject.dependency_history_requests("07-final_assembly-through-296"),
            final,
        )

    def test_dependency_history_protocol_is_exact_ordered_and_unapproved(self) -> None:
        boundary = "07-final_assembly-through-296"
        names = subject.dependency_history_requests(boundary)
        records = [
            subject.dependency_history_marker_prefix(
                self.nonce, index, name,
            ) + f"{index + 1:032x}"
            for index, name in enumerate(names)
        ]
        terminal = subject.dependency_history_terminal(
            self.nonce, boundary, names,
        )
        report = subject.parse_dependency_history_text(
            "\n".join([*records, terminal]) + "\n",
            names, boundary, self.nonce,
        )
        self.assertEqual(report["status"], "observed_uncompared")
        self.assertEqual(report["record_count"], 4)
        self.assertFalse(report["approved_reference_present"])
        self.assertFalse(report["dependency_history_is_kernel_trace"])
        self.assertFalse(report["pft_used"])
        self.assertFalse(report["s2_s3_evidence"])
        for label, forged in (
            ("missing", records[1:] + [terminal]),
            ("extra", records + [records[-1], terminal]),
            ("reordered", [records[1], records[0], *records[2:], terminal]),
            ("tampered digest", [records[0][:-1] + "g", *records[1:], terminal]),
            ("wrong nonce", [records[0].replace(self.nonce, "b" * 32),
                             *records[1:], terminal]),
            ("wrong terminal", [*records, terminal + "0"]),
        ):
            with self.subTest(label=label), self.assertRaises(
                subject.ContractError,
            ):
                subject.parse_dependency_history_text(
                    "\n".join(forged) + "\n",
                    names, boundary, self.nonce,
                )
        with self.assertRaisesRegex(
            subject.ContractError, "unexpected dependency-history",
        ):
            subject.parse_dependency_history_text(
                records[0] + "\n", [], "05-lp_support-through-184",
                self.nonce,
            )

    def test_final_postlude_emits_serialization_dependency_history_last(self) -> None:
        boundary = "07-final_assembly-through-296"
        names = subject.fingerprint_requests(boundary)
        dependency_names = subject.dependency_history_requests(boundary)
        with tempfile.TemporaryDirectory() as temporary:
            postlude = Path(temporary) / "postlude.ml"
            subject.write_postlude(
                postlude, Path(temporary), boundary, names, self.nonce,
                self.logical_source_closure, dependency_names,
            )
            source = postlude.read_text(encoding="utf-8")
        self.assertEqual(source.count("Serialization.full_digest_thm"), 4)
        self.assertEqual(
            source.count(subject.DEPENDENCY_HISTORY_PREFIX + " "), 4,
        )
        self.assertEqual(
            source.count(subject.DEPENDENCY_HISTORY_SUCCESS_MARKER), 1,
        )
        self.assertLess(
            source.index(subject.FINGERPRINT_SUCCESS_MARKER),
            source.index(subject.DEPENDENCY_HISTORY_PREFIX),
        )
        self.assertLess(
            source.index(subject.DEPENDENCY_HISTORY_SUCCESS_MARKER),
            source.index("Cakeml.requestSourceTraceFinish"),
        )

    def test_manifest_closure_is_complete_ordered_and_excludes_full_loader(self) -> None:
        manifest = json.loads(
            (Path(subject.__file__).parent / "flyspeck_manifest.json").read_text(
                encoding="utf-8",
            )
        )
        closure = subject.derive_logical_source_closure(
            manifest, 297, True, self.generated_control_records,
        )
        self.assertEqual(closure["record_count"], 399)
        keys = [record["key"] for record in closure["records"]]
        self.assertEqual(keys, sorted(keys))
        self.assertEqual(closure["order"], subject.SOURCE_CLOSURE_ORDER)
        self.assertNotIn(subject.SOURCE_CLOSURE_EXCLUDED_LOADER, keys)
        self.assertIn(subject.SOURCE_CLOSURE_FINAL_KEY, keys)
        self.assertNotIn(subject.STRICTBUILD_SERIALIZATION_OPT_IN_KEY, keys)
        self.assertNotIn(
            "flyspeck:text_formalization/general/update_database_310.ml", keys,
        )
        records = {record["key"]: record for record in closure["records"]}
        self.assertEqual(
            records["candle:candle/flyspeck_full_build.ml"]["classification"],
            "derivation-only-input",
        )
        for key in subject.SOURCE_CLOSURE_GENERATED_KEYS:
            self.assertEqual(
                records[key]["classification"], "generated-executed-control",
            )
        self.assertEqual(
            records["flyspeck:text_formalization/general/serialization.hl"][
                "classification"
            ], "observed-outer-source",
        )
        self.assertEqual(
            records[
                "flyspeck:text_formalization/general/update_database_400.ml"
            ]["classification"],
            "observed-nested-source",
        )
        self.assertEqual(
            records[subject.STRICTBUILD_SOURCE_KEY]["classification"],
            "expected-nested-source",
        )
        self.assertEqual(
            closure["ordered_record_sha256"],
            subject.canonical_sha256(closure["records"]),
        )
        diagnostic = subject.derive_logical_source_closure(
            manifest, 19, False, self.generated_control_records,
        )
        self.assertEqual(diagnostic["record_count"], 117)
        self.assertNotIn(
            subject.SOURCE_CLOSURE_FINAL_KEY,
            [record["key"] for record in diagnostic["records"]],
        )

    def test_manifest_closure_selects_serialization_only_at_action_295(self) -> None:
        manifest = json.loads(
            (Path(subject.__file__).parent / "flyspeck_manifest.json").read_text(
                encoding="utf-8",
            )
        )
        serialization = subject.SERIALIZATION_SOURCE_KEY
        selected_branch = (
            "flyspeck:text_formalization/general/update_database_400.ml"
        )
        unselected = "flyspeck:text_formalization/general/update_database_310.ml"
        strictbuild_actions = {
            "flyspeck:text_formalization/general/parser_verbose.hl",
            "flyspeck:text_formalization/general/debug.hl",
            "flyspeck:text_formalization/general/state_manager.hl",
        }
        deltas = subject.derive_action_ledger_delta_keys(manifest, 296)
        self.assertTrue(all(len(delta) == 1 for delta in deltas[:295]))
        self.assertEqual(deltas[295], [serialization, selected_branch])

        def keys(count: int, final: bool = False) -> set[str]:
            return {
                record["key"] for record in
                subject.derive_logical_source_closure(
                    manifest, count, final, self.generated_control_records,
                )["records"]
            }

        action0 = keys(1)
        self.assertLessEqual(strictbuild_actions, action0)
        self.assertTrue({
            serialization, selected_branch, unselected,
            subject.STRICTBUILD_SERIALIZATION_OPT_IN_KEY,
        }.isdisjoint(action0))
        pre_295 = keys(295)
        self.assertNotIn(serialization, pre_295)
        self.assertNotIn(selected_branch, pre_295)
        post_295 = keys(296)
        self.assertIn(serialization, post_295)
        self.assertIn(selected_branch, post_295)
        self.assertNotIn(unselected, post_295)
        self.assertNotIn(subject.STRICTBUILD_SERIALIZATION_OPT_IN_KEY, post_295)
        post_295_records = {
            record["key"]: record
            for record in subject.derive_logical_source_closure(
                manifest, 296, False, self.generated_control_records,
            )["records"]
        }
        self.assertEqual(
            post_295_records[selected_branch]["classification"],
            "observed-nested-source",
        )
        final = keys(297, True)
        self.assertIn(subject.SOURCE_CLOSURE_FINAL_KEY, final)
        self.assertIn(serialization, final)
        self.assertIn(selected_branch, final)
        self.assertNotIn(unselected, final)

    def test_logical_source_closure_rejects_missing_extra_reorder_and_tamper(self) -> None:
        boundary = "00-test-through-001"
        success = f"{subject.SUCCESS_MARKER} {self.nonce} {boundary} 2"
        records = [
            subject.logical_source_marker(self.nonce, record)
            for record in self.logical_source_closure["records"]
        ]
        terminal = subject.logical_source_terminal(
            self.nonce, boundary, self.logical_source_closure,
        )
        valid = [success, *records, terminal]
        observed = subject.validate_logical_source_closure(
            "\n".join(valid), self.logical_source_closure, boundary, self.nonce,
        )
        self.assertEqual(observed["status"],
                         "expected-closure-emitted-unapproved")
        self.assertFalse(observed["physical_loader_cache_trace"])
        self.assertFalse(observed["self_certifies_nested_execution"])
        self.assertEqual(observed["execution_observation"],
                         subject.SOURCE_CLOSURE_OBSERVATION)

        invalid_cases = (
            ([success, records[1], terminal], "logical source record 0"),
            ([success, *records, records[0], terminal], "logical source record 0"),
            ([success, records[1], records[0], terminal], "out of order"),
            ([success, records[0][:-1] + "0", records[1], terminal],
             "logical source record 0"),
        )
        for lines, message in invalid_cases:
            with self.subTest(message=message, lines=lines):
                with self.assertRaisesRegex(subject.ContractError, message):
                    subject.validate_logical_source_closure(
                        "\n".join(lines), self.logical_source_closure,
                        boundary, self.nonce,
                    )

        forged = records[0].replace(
                                    "flyspeck:../formal_lp/b.ml".encode().hex(),
                                    "candle:extra.ml".encode().hex())
        with self.assertRaisesRegex(
            subject.ContractError, "unexpected logical source closure record",
        ):
            subject.validate_logical_source_closure(
                "\n".join([success, *records, forged, terminal]),
                self.logical_source_closure, boundary, self.nonce,
            )

    def test_evidence_v4_artifact_validator_rejects_legacy_and_partial_upgrade(self) -> None:
        expected_actions = [
            {
                "index": index,
                "source_sha256": action["source_sha256"],
                "logical_source_delta": action["logical_source_delta"],
                "logical_source_delta_sha256":
                    action["logical_source_delta_sha256"],
            }
            for index, action in enumerate(self.actions)
        ]
        attempt = self.direct_attempt(expected_actions)
        subject.validate_direct_evidence_v4_artifact(attempt, receipt=False)
        for label, mutate in (
            ("controller source root", lambda item: item["inputs"][
                "controller_execution"
            ].update(source_root=False)),
            ("controller source closure", lambda item: item["inputs"][
                "controller_execution"
            ].update(local_sources="forged")),
            ("controller Python runtime", lambda item: item["inputs"][
                "controller_execution"
            ].update(python_runtime={})),
            ("duplicate controller ELF", lambda item: item["inputs"][
                "controller_execution"
            ]["python_runtime"]["elf_objects"].append(copy.deepcopy(
                item["inputs"]["controller_execution"]["python_runtime"]
                ["elf_objects"][0]
            ))),
            ("duplicate controller host tool", lambda item: item["inputs"][
                "controller_execution"
            ]["host_tools"].append(copy.deepcopy(
                item["inputs"]["controller_execution"]["host_tools"][0]
            ))),
            ("integer startup boolean", lambda item: item["inputs"][
                "controller_execution"
            ]["direct_script_startup"].update(spec_is_none=1)),
            ("boolean startup integer", lambda item: item["inputs"][
                "controller_execution"
            ]["python_startup_flags"].update(debug=False)),
            ("integer dev-mode boolean", lambda item: item["inputs"][
                "controller_execution"
            ]["python_startup_flags"].update(dev_mode=0)),
            ("integer stdio boolean", lambda item: item["inputs"][
                "controller_execution"
            ]["python_startup_options"]["stdio_write_through"].update(
                stdin=0,
            )),
            ("parent-traversing source root", lambda item: item["inputs"][
                "controller_execution"
            ].update(source_root="/candle/../candle")),
            ("absolute prefix path", lambda item: item["inputs"][
                "authenticated_prefix"
            ].update(path="/prefix.ml")),
            ("dot prefix path", lambda item: item["inputs"][
                "authenticated_prefix"
            ].update(path=".")),
            ("parent-traversing lock path", lambda item: item[
                "runtime_lock"
            ].update(path="/candle/../candle/build")),
            ("double-leading-slash executable", lambda item: item["inputs"][
                "runtime_executable"
            ].update(path="//evil/snapshot/candle/candle/build/cake")),
            ("integer final-target flag", lambda item: item[
                "expected_logical_source_closure"
            ].update(final_target_selected=0)),
        ):
            forged = copy.deepcopy(attempt)
            mutate(forged)
            with self.subTest(label=label), self.assertRaises(
                subject.ContractError,
            ):
                subject.validate_direct_evidence_v4_artifact(
                    forged, receipt=False,
                )
        missing_claim = copy.deepcopy(attempt)
        missing_claim.pop("claim")
        with self.assertRaisesRegex(subject.ContractError, "evidence envelope"):
            subject.validate_direct_evidence_v4_artifact(
                missing_claim, receipt=False,
            )
        schema3 = copy.deepcopy(attempt)
        schema3["schema"] = 3
        with self.assertRaisesRegex(subject.ContractError, "disjoint schema 4"):
            subject.validate_direct_evidence_v4_artifact(schema3, receipt=False)
        partial = copy.deepcopy(attempt)
        partial["evidence_contract"].pop("physical_loader_cache_trace_included")
        with self.assertRaisesRegex(subject.ContractError, "evidence-v4 contract"):
            subject.validate_direct_evidence_v4_artifact(partial, receipt=False)
        omitted_sources = copy.deepcopy(attempt)
        trace = omitted_sources["expected_physical_source_trace"]
        trace["bindings"] = [
            binding for binding in trace["bindings"]
            if binding["key"] in subject.SOURCE_TRACE_TOP_LEVEL_CONTROLS
        ]
        trace["binding_count"] = len(trace["bindings"])
        trace["ordered_binding_sha256"] = subject.canonical_sha256(
            trace["bindings"]
        )
        trace["required_keys"] = sorted(subject.SOURCE_TRACE_TOP_LEVEL_CONTROLS)
        trace["required_key_count"] = len(trace["required_keys"])
        trace["ordered_required_key_sha256"] = subject.canonical_sha256(
            trace["required_keys"]
        )
        with self.assertRaisesRegex(
            subject.ContractError, "differs from logical source closure",
        ):
            subject.validate_direct_evidence_v4_artifact(
                omitted_sources, receipt=False,
            )

        receipt = {
            **self.direct_receipt_envelope(attempt),
            "logical_source_closure": {
                **self.logical_source_closure,
                "status": "expected-closure-emitted-unapproved",
            },
            "action_events": [
                {"index": 0, "source_sha256": "1" * 64,
                 "logical_source_delta_sha256":
                    self.actions[0]["logical_source_delta_sha256"],
                 "outcome": "load"},
                {"index": 1, "source_sha256": "2" * 64,
                 "logical_source_delta_sha256":
                    self.actions[1]["logical_source_delta_sha256"],
                 "outcome": "skip-ledger"},
            ],
            "physical_source_trace": self.source_trace_observation,
            "semantic_fingerprints": {
                "status": "not_requested",
                "approved_reference_present": False,
                "serializer": None,
                "theorems": [],
                "post_state": None,
            },
        }
        self.validate_receipt(receipt)
        receipt["logical_source_closure"]["self_certifies_nested_execution"] = True
        with self.assertRaisesRegex(subject.ContractError, "differs"):
            self.validate_receipt(receipt)

    def test_evidence_v4_completed_receipt_rejects_forged_state_flips(self) -> None:
        expected_actions = [
            {
                "index": index,
                "source_sha256": action["source_sha256"],
                "logical_source_delta": action["logical_source_delta"],
                "logical_source_delta_sha256":
                    action["logical_source_delta_sha256"],
            }
            for index, action in enumerate(self.actions)
        ]
        attempt = self.direct_attempt(expected_actions)
        valid = {
            **self.direct_receipt_envelope(attempt),
            "logical_source_closure": {
                **self.logical_source_closure,
                "status": "expected-closure-emitted-unapproved",
            },
            "action_events": [
                {"index": 0, "source_sha256": "1" * 64,
                 "logical_source_delta_sha256":
                    self.actions[0]["logical_source_delta_sha256"],
                 "outcome": "load"},
                {"index": 1, "source_sha256": "2" * 64,
                 "logical_source_delta_sha256":
                    self.actions[1]["logical_source_delta_sha256"],
                 "outcome": "skip-ledger"},
            ],
            "physical_source_trace": self.source_trace_observation,
            "semantic_fingerprints": {
                "status": "not_requested",
                "approved_reference_present": False,
                "serializer": None,
                "theorems": [],
                "post_state": None,
            },
        }
        self.validate_receipt(valid)
        float_initial_size = copy.deepcopy(valid)
        float_initial_size["initial_attempt"]["bytes"] = float(
            float_initial_size["initial_attempt"]["bytes"]
        )
        with self.assertRaisesRegex(subject.ContractError, "initial attempt"):
            self.validate_receipt(float_initial_size)
        for label, mutate in (
            ("float closure schema", lambda item: item[
                "logical_source_closure"
            ].update(schema=3.0)),
            ("float closure count", lambda item: item[
                "logical_source_closure"
            ].update(record_count=2.0)),
            ("integer closure boolean", lambda item: item[
                "logical_source_closure"
            ].update(physical_loader_cache_trace=0)),
            ("integer fingerprint boolean", lambda item: item[
                "semantic_fingerprints"
            ].update(approved_reference_present=0)),
            ("infinite child CPU", lambda item: item[
                "child_resources"
            ].update(user_cpu_seconds=float("inf"))),
        ):
            forged = copy.deepcopy(valid)
            mutate(forged)
            with self.subTest(label=label), self.assertRaises(
                subject.ContractError,
            ):
                self.validate_receipt(forged)
        forged_runtime = copy.deepcopy(valid)
        forged_runtime["inputs"]["runtime_executable"] = {
            "path": "/forged/snapshot/candle/candle/build/cake",
            "bytes": 1,
            "sha256": "0" * 64,
            "md5": "0" * 32,
        }
        forged_runtime["command"][0] = forged_runtime["inputs"][
            "runtime_executable"
        ]["path"]
        initial_projection = {
            field: forged_runtime[field]
            for field in subject.DIRECT_ATTEMPT_FIELDS
        }
        initial_projection["state"] = "running"
        forged_runtime["initial_attempt"] = {
            "path": "attempt.json",
            **subject.data_record(subject.json_bytes(initial_projection)),
        }
        with self.assertRaisesRegex(
            subject.ContractError, "requires its executable bytes",
        ):
            self.validate_receipt(forged_runtime)
        with self.assertRaisesRegex(
            subject.ContractError, "requires its log bytes",
        ):
            subject.validate_direct_evidence_v4_artifact(
                valid, receipt=True,
                runtime_executable_path=self.runtime_executable_path,
            )
        empty_log = copy.deepcopy(valid)
        empty_log["log"] = {
            "path": "candle.log", **subject.data_record(b""),
        }
        with self.assertRaisesRegex(subject.ContractError, "success invariants"):
            self.validate_receipt(empty_log)
        forged_log_text = self.direct_log_text(valid["boundary_id"]).replace(
            self.action_marker(0, "load"),
            self.action_marker(0, "skip-ledger"),
        )
        forged_log = copy.deepcopy(valid)
        forged_log["log"] = {
            "path": "candle.log",
            **subject.data_record(forged_log_text.encode("utf-8")),
        }
        with tempfile.TemporaryDirectory() as temporary:
            forged_path = Path(temporary) / "candle.log"
            forged_path.write_text(forged_log_text, encoding="utf-8")
            forged_path.chmod(0o444)
            with self.assertRaisesRegex(
                subject.ContractError, "action events differ from bound log",
            ):
                subject.validate_direct_evidence_v4_artifact(
                    forged_log, receipt=True, log_path=forged_path,
                    runtime_executable_path=self.runtime_executable_path,
                )
        missing_log = copy.deepcopy(valid)
        missing_log.pop("log")
        with self.assertRaisesRegex(subject.ContractError, "evidence envelope"):
            self.validate_receipt(missing_log)
        for label, mutate in (
            ("exit 137", lambda item: item.update(exit_code=137)),
            ("timeout", lambda item: item.update(timed_out=True)),
            ("validation error", lambda item: item.update(
                validation_error="ContractError: forged")),
            ("postflight false", lambda item: item.update(
                postflight_reauthenticated=False)),
            ("zero markers", lambda item: item.update(
                action_markers_validated=0)),
            ("forged event", lambda item: item["action_events"][0].update(
                source_sha256="f" * 64)),
            ("empty closure records", lambda item: item[
                "logical_source_closure"
            ].update(records=[])),
            ("failed state flip", lambda item: item.update(state="failed")),
            ("unbound executable", lambda item: item.update(
                command=["/bin/false", "--candle"])),
            ("requested boundary lacks fingerprints", lambda item: item.update(
                boundary_id="05-lp_support-through-184")),
        ):
            forged = copy.deepcopy(valid)
            mutate(forged)
            with self.subTest(label=label), self.assertRaises(subject.ContractError):
                self.validate_receipt(forged)

        for label, mutate in (
            ("missing physical trace", lambda item: item.update(
                physical_source_trace=None)),
            ("forged physical trace event", lambda item: item[
                "physical_source_trace"
            ]["events"][0].update(cache_before="prior-cache")),
        ):
            forged = copy.deepcopy(valid)
            mutate(forged)
            with self.subTest(label=label), self.assertRaises(subject.ContractError):
                self.validate_receipt(forged)

        failed = {
            **self.direct_receipt_envelope(attempt),
            "state": "failed",
            "timed_out": True,
            "exit_code": 137,
            "postflight_reauthenticated": False,
            "action_markers_validated": 0,
            "validation_error": "ContractError: timed out",
            "logical_source_closure": None,
            "action_events": None,
            "physical_source_trace": None,
            "semantic_fingerprints": None,
        }
        self.validate_receipt(failed)
        late_failed = {
            **copy.deepcopy(valid),
            "state": "failed",
            "action_markers_validated": 0,
            "validation_error": "InterruptedError: pending signal after validation",
        }
        self.validate_receipt(late_failed)

    def test_candidate_fingerprint_parser_is_fail_closed(self) -> None:
        name = "Linear_programming_results.linear_programming_results_th"
        axioms = b"axioms"
        fields = [
            subject.FINGERPRINT_MARKER,
            name.encode().hex(),
            b"theorem".hex(), subject.reference_protocol.EMPTY_HYPOTHESES_WIRE.hex(),
            b"conclusion".hex(), axioms.hex(), "0", "3",
        ]
        state = [
            subject.STATE_FINGERPRINT_MARKER,
            b"state".hex(), b"types".hex(), b"terms".hex(),
            b"definitions".hex(), axioms.hex(), "1", "2", "3", "3",
        ]
        serializer = subject.reference_protocol.FINGERPRINT_HELPER
        with tempfile.TemporaryDirectory() as temporary:
            log = Path(temporary) / "fingerprints.log"
            log.write_text(
                "\t".join(fields) + "\n" + "\t".join(state) + "\n",
                encoding="utf-8",
            )
            report = subject.parse_fingerprints(log, [name], serializer)
            self.assertEqual(report["status"], "observed_uncompared")
            self.assertFalse(report["approved_reference_present"])
            self.assertEqual(
                report["theorems"][0]["theorem_sha256"],
                hashlib.sha256(b"theorem").hexdigest(),
            )
            self.assertEqual(
                report["post_state"]["definitions_sha256"],
                hashlib.sha256(b"definitions").hexdigest(),
            )
            bad = fields.copy()
            bad[-1] = "4"
            log.write_text(
                "\t".join(bad) + "\n" + "\t".join(state) + "\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(subject.ContractError, "three axioms"):
                subject.parse_fingerprints(log, [name], serializer)

    def test_receipt_fingerprint_scalars_have_exact_json_types(self) -> None:
        name = "Linear_programming_results.linear_programming_results_th"
        expected_actions = [
            {
                "index": index,
                "source_sha256": action["source_sha256"],
                "logical_source_delta": action["logical_source_delta"],
                "logical_source_delta_sha256":
                    action["logical_source_delta_sha256"],
            }
            for index, action in enumerate(self.actions)
        ]
        attempt = self.direct_attempt(expected_actions)
        serializer_sha256 = "7" * 64
        attempt["inputs"]["fingerprint_serializer"]["sha256"] = (
            serializer_sha256
        )
        fingerprints = {
            "status": "observed_uncompared",
            "approved_reference_present": False,
            "serializer": {
                "path": subject.FINGERPRINT_RELATIVE.as_posix(),
                "sha256": serializer_sha256,
            },
            "theorems": [{
                "name": name,
                "theorem_sha256": "1" * 64,
                "hypotheses_sha256": "2" * 64,
                "conclusion_sha256": "3" * 64,
                "global_axioms_sha256": "4" * 64,
                "hypothesis_count": 0,
                "global_axiom_count": 3,
            }],
            "post_state": {
                "kernel_state_sha256": "5" * 64,
                "type_constants_sha256": "6" * 64,
                "term_constants_sha256": "7" * 64,
                "definitions_sha256": "8" * 64,
                "global_axioms_sha256": "4" * 64,
                "type_constant_count": 1,
                "term_constant_count": 2,
                "definition_count": 3,
                "global_axiom_count": 3,
            },
        }
        receipt = {
            **self.direct_receipt_envelope(attempt),
            "logical_source_closure": {
                **self.logical_source_closure,
                "status": "expected-closure-emitted-unapproved",
            },
            "action_events": [
                {"index": 0, "source_sha256": "1" * 64,
                 "logical_source_delta_sha256":
                    self.actions[0]["logical_source_delta_sha256"],
                 "outcome": "load"},
                {"index": 1, "source_sha256": "2" * 64,
                 "logical_source_delta_sha256":
                    self.actions[1]["logical_source_delta_sha256"],
                 "outcome": "skip-ledger"},
            ],
            "physical_source_trace": self.source_trace_observation,
            "semantic_fingerprints": fingerprints,
        }
        for label, mutate in (
            ("boolean hypothesis count", lambda value: value[
                "semantic_fingerprints"
            ]["theorems"][0].update(hypothesis_count=False)),
            ("float axiom count", lambda value: value[
                "semantic_fingerprints"
            ]["theorems"][0].update(global_axiom_count=3.0)),
            ("integer theorem digest", lambda value: value[
                "semantic_fingerprints"
            ]["theorems"][0].update(theorem_sha256=int("9" * 64))),
            ("integer state digest", lambda value: value[
                "semantic_fingerprints"
            ]["post_state"].update(kernel_state_sha256=int("9" * 64))),
        ):
            forged = copy.deepcopy(receipt)
            mutate(forged)
            with self.subTest(label=label), mock.patch.object(
                subject, "fingerprint_requests", side_effect=[[], [name]],
            ), self.assertRaises(subject.ContractError):
                subject.validate_direct_evidence_v4_artifact(
                    forged, receipt=True,
                    runtime_executable_path=self.runtime_executable_path,
                )

    def test_postlude_uses_actual_v2_theorem_and_state_serializer(self) -> None:
        serializer_source = subject.reference_protocol.FINGERPRINT_HELPER.read_text(
            encoding="utf-8",
        )
        self.assertIn(f'"{subject.FINGERPRINT_MARKER}\\t"', serializer_source)
        self.assertIn(f'"{subject.STATE_FINGERPRINT_MARKER}\\t"', serializer_source)
        with tempfile.TemporaryDirectory() as temporary:
            postlude = Path(temporary) / "postlude.ml"
            subject.write_postlude(
                postlude, Path(temporary), "05-lp_support-through-184",
                ["Linear_programming_results.linear_programming_results_th"],
                self.nonce,
                self.logical_source_closure,
            )
            source = postlude.read_text(encoding="utf-8")
        self.assertIn("candle_s1_emit_fingerprint", source)
        self.assertEqual(source.count(subject.SOURCE_CLOSURE_PREFIX), 2)
        self.assertEqual(source.count(subject.SOURCE_CLOSURE_SUCCESS_MARKER), 1)
        self.assertLess(
            source.index(subject.SOURCE_CLOSURE_SUCCESS_MARKER),
            source.index("candle_s1_emit_fingerprint"),
        )
        self.assertEqual(source.count("candle_s1_emit_state_fingerprint ();;"), 1)
        self.assertLess(
            source.index("candle_s1_emit_fingerprint"),
            source.index("candle_s1_emit_state_fingerprint"),
        )

    def test_fingerprint_boundary_requires_terminal_marker(self) -> None:
        boundary = "05-lp_support-through-184"
        theorem_names = subject.fingerprint_requests(boundary)
        source_log = "\n".join([
            f"{subject.PREFLIGHT_MARKER} {self.nonce}",
            self.action_marker(0, "load"),
            self.action_marker(1, "load"),
            f"{subject.SUCCESS_MARKER} {self.nonce} {boundary} 2",
        ])
        with self.assertRaisesRegex(subject.ContractError, "fingerprint success marker"):
            subject.validate_log(
                source_log, self.actions, boundary, self.nonce, theorem_names,
            )
        subject.validate_log(
            source_log + "\n" +
            f"{subject.FINGERPRINT_SUCCESS_MARKER} {self.nonce} {boundary} 1",
            self.actions, boundary, self.nonce, theorem_names,
        )

    def test_fingerprint_protocol_namespace_and_session_are_closed(self) -> None:
        boundary = "05-lp_support-through-184"
        theorem_names = subject.fingerprint_requests(boundary)
        preflight = f"{subject.PREFLIGHT_MARKER} {self.nonce}"
        action0 = self.action_marker(0, "load")
        action1 = self.action_marker(1, "load")
        success = f"{subject.SUCCESS_MARKER} {self.nonce} {boundary} 2"
        terminal = (
            f"{subject.FINGERPRINT_SUCCESS_MARKER} {self.nonce} {boundary} 1"
        )
        v2_record = f"{subject.FINGERPRINT_MARKER}\t00"
        valid = [preflight, action0, action1, success, v2_record, terminal]
        subject.validate_log(
            "\n".join(valid), self.actions, boundary, self.nonce, theorem_names,
        )
        for forged in (
            ["CANDLE_FINGERPRINT_V1\t00", *valid],
            [*valid, "CANDLE_STATE_FINGERPRINT_V3\t00"],
            [v2_record, *valid],
            [*valid, v2_record],
            [*valid, f"{subject.FINGERPRINT_SUCCESS_MARKER} {'b' * 32} forged 99"],
        ):
            with self.assertRaisesRegex(
                subject.ContractError,
                "unsupported or unexpected|outside its boundary session|terminal marker",
            ):
                subject.validate_log(
                    "\n".join(forged), self.actions, boundary, self.nonce,
                    theorem_names,
                )
        with self.assertRaisesRegex(
            subject.ContractError, "unsupported or unexpected stratum control record",
        ):
            subject.validate_log(
                "\n".join([
                    preflight, action0, action1, success,
                    f"{subject.FINGERPRINT_SUCCESS_MARKER} {self.nonce} {boundary} 0",
                ]), self.actions, boundary, self.nonce,
            )

    def test_runtime_config_provides_exact_lp_certificate_list(self) -> None:
        certificates = [
            {"path": f"/inputs/easy_{index}.dat", "md5": f"{index:032x}"}
            for index in range(1, 40)
        ]
        prepared = {
            "flyspeck_root": Path("/flyspeck"),
            "overlay_root": Path("/overlay"),
            "generated_root": Path("/generated"),
            "boundary": {"boundary_id": "05-lp_support-through-184"},
            "actions": [
                {
                    "identity_basename": "a.hl",
                    "identity_md5": "1" * 32,
                    "logical_source_delta": [{
                        "identity_basename": "a.hl",
                        "identity_md5": "1" * 32,
                    }],
                },
            ],
            "attempt_nonce": self.nonce,
            "source_trace_contract": self.source_trace_contract,
            "source_alias_runtime": [{
                "alias": "/flyspeck/text/../canonical/a.hl",
                "canonical": "/flyspeck/canonical/a.hl",
            }],
            "normalized_runtime": [
                {"original": f"/o/{index}", "output": f"/n/{index}", "md5": "2" * 32}
                for index in range(18)
            ],
            "generated_runtime": certificates + [
                {"path": f"/inputs/other_{index}", "md5": "3" * 32}
                for index in range(4)
            ],
            "lp_certificate_runtime": certificates,
            "process_runtime": [
                {"path": "/metadata/date", "md5": "4" * 32},
                {"path": "/metadata/user", "md5": "5" * 32},
            ],
        }
        with tempfile.TemporaryDirectory() as temporary:
            config = Path(temporary) / "config.ml"
            subject.write_config(
                config, Path("/candle"), prepared,
                Path("/attempt/program.ml"), "6" * 32,
            )
            source = config.read_text(encoding="utf-8")
        certificate_block = source.split(
            "let candle_flyspeck_lp_certificate_files = [", 1
        )[1].split("];;", 1)[0]
        self.assertEqual(certificate_block.count("/inputs/easy_"), 39)
        self.assertNotIn("/inputs/other_", certificate_block)
        self.assertIn("let candle_flyspeck_stratum_normalization_count = 18;;", source)
        self.assertIn("let candle_flyspeck_stratum_source_alias_count = 1;;", source)
        self.assertIn(
            '("/flyspeck/text/../canonical/a.hl",'
            '"/flyspeck/canonical/a.hl");',
            source,
        )
        self.assertIn(
            "let candle_flyspeck_stratum_action_ledger_deltas = [", source,
        )

    def test_source_alias_contract_binds_one_lexical_path_to_canonical(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            candle = root / "candle"
            flyspeck = root / "flyspeck"
            candle.mkdir()
            (flyspeck / "text_formalization").mkdir(parents=True)
            (flyspeck / "jHOLLight").mkdir()
            (flyspeck / "formal_ineqs").mkdir()
            canonical = flyspeck / "external/a.ml"
            canonical.parent.mkdir()
            canonical.write_bytes(b"source")
            record = {
                "target": "../external/a.ml",
                "search_root_index": 0,
                "alias_repository": "flyspeck",
                "alias_path": (
                    "text_formalization/../jHOLLight//../external/a.ml"
                ),
                "selected": "flyspeck:external/a.ml",
                "canonical_repository": "flyspeck",
                "canonical_path": "external/a.ml",
                "occurrence_count": 1,
                "uses": [{"kind": "build-sequence-root", "action_index": 0}],
            }
            manifest = {
                "load_path_order": list(subject.SOURCE_ALIAS_LOAD_PATH_ORDER),
                "build_sequence_roots": [{
                    "index": 0,
                    "target": "../external/a.ml",
                    "status": "resolved",
                    "selected": "flyspeck:external/a.ml",
                }],
                "source_nodes": {},
                "source_alias_contract": {
                    "schema": 1,
                    "policy": subject.SOURCE_ALIAS_POLICY,
                    "record_count": 1,
                    "occurrence_count": 1,
                    "records": [record],
                },
            }
            observed = subject.validate_source_alias_contract(
                manifest, {"flyspeck:external/a.ml": {}}, candle, flyspeck,
            )
            self.assertEqual(len(observed), 1)
            self.assertEqual(observed[0]["canonical"], str(canonical))
            mutations = {
                "policy": lambda value: value["source_alias_contract"].__setitem__(
                    "policy", "forged",
                ),
                "target": lambda value: value["source_alias_contract"]["records"][
                    0
                ].__setitem__("target", "../external/forged.ml"),
                "search root": lambda value: value["source_alias_contract"][
                    "records"
                ][0].__setitem__("search_root_index", 1),
                "uses": lambda value: value["source_alias_contract"]["records"][
                    0
                ].__setitem__("uses", [{"kind": "forged"}]),
                "boolean count": lambda value: value["source_alias_contract"][
                    "records"
                ][0].__setitem__("occurrence_count", True),
                "string count": lambda value: value["source_alias_contract"].__setitem__(
                    "occurrence_count", "1",
                ),
                "canonical path": lambda value: value["source_alias_contract"][
                    "records"
                ][0].__setitem__("canonical_path", "external/other.ml"),
            }
            for label, mutate in mutations.items():
                with self.subTest(label=label):
                    forged = copy.deepcopy(manifest)
                    mutate(forged)
                    with self.assertRaisesRegex(
                        subject.ContractError,
                        "source alias contract differs from derived provenance closure",
                    ):
                        subject.validate_source_alias_contract(
                            forged, {"flyspeck:external/a.ml": {}}, candle, flyspeck,
                        )

    def test_snapshot_is_complete_deduplicated_and_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            candle = root / "candle-root"
            flyspeck = root / "flyspeck-root"
            overlay = root / "overlay-root"
            generated = root / "generated-root"
            output = root / "attempt"
            for directory in (candle, flyspeck, overlay, generated, output):
                directory.mkdir()

            def write(relative_root: Path, relative: Path | str,
                      content: bytes) -> tuple[Path, dict[str, object]]:
                path = relative_root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(content)
                return path, subject.hash_file(path)

            harness_records = {}
            for relative in (
                subject.SOURCE_DIGEST_RELATIVE,
                subject.SETUP_RELATIVE,
                subject.CHECK_RELATIVE,
                subject.FINGERPRINT_RELATIVE,
                subject.L2_TARGET_RELATIVE,
            ):
                _, record = write(candle, relative, relative.as_posix().encode())
                harness_records[relative.as_posix()] = record

            linked_outputs = {}
            for name in ("cake", "config_enc_str.txt", "candle_boot.ml"):
                path, record = write(candle, Path("candle/build") / name, name.encode())
                if name == "cake":
                    path.chmod(0o755)
                linked_outputs[name] = record
            _, linked_record = write(
                candle, subject.LINKED_RECORD_RELATIVE,
                json.dumps({"schema": 2}).encode(),
            )
            bootstrap_log, bootstrap_log_record = write(
                candle, "candle/build/bootstrap.log",
                b"verified bootstrap transcript",
            )
            bootstrap_record_value = {
                "schema": 1,
                "bootstrap_log": {
                    "path": "bootstrap.log",
                    "bytes": bootstrap_log_record["bytes"],
                    "sha256": bootstrap_log_record["sha256"],
                },
            }
            bootstrap_record, bootstrap_record_digest = write(
                candle, "candle/build/bootstrap-provenance.json",
                json.dumps(bootstrap_record_value).encode(),
            )
            linked_outputs["bootstrap.log"] = bootstrap_log_record
            linked_outputs["bootstrap-provenance.json"] = bootstrap_record_digest
            transition_copy, transition_copy_record = write(
                candle, "candle/build/bootstrap-transition.json",
                b'{"schema":1,"kind":"retained-transition"}\n',
            )
            linked_outputs["bootstrap-transition.json"] = transition_copy_record
            runtime_object, runtime_object_record = write(
                root, "libc.so.6", b"runtime object",
            )

            controller_sources = {}
            for module in subject.local_python_modules():
                label = Path(module.__file__).name
                source_bytes = module.__candle_source_bytes__
                source_path, source_record = write(
                    candle, Path("candle") / label, source_bytes,
                )
                controller_sources[label] = {
                    "source_path": str(source_path),
                    "execution_binding":
                        "compiled-from-captured-source-bytes",
                    "source_bytes": source_bytes,
                    **source_record,
                }
            runner_path, runner_record = write(
                candle, "candle/flyspeck_stratum_runtime.py",
                subject.RUNNER_SOURCE_BYTES,
            )
            controller_sources["flyspeck_stratum_runtime.py"] = {
                "source_path": str(runner_path),
                "execution_binding":
                    "startup-captured-after-initial-compilation",
                "source_bytes": subject.RUNNER_SOURCE_BYTES,
                **runner_record,
            }
            controller_execution = {
                "source_root": str(candle / "candle"),
                "direct_script_startup": {
                    "module_name": "__main__",
                    "spec_is_none": True,
                    "cached_is_none": True,
                    "argv0": str(runner_path),
                    "source_path": str(runner_path),
                },
                "commit_binding": {
                    "candle_commit": "f" * 40,
                    "sources": {
                        label: {
                            "repository_path": f"candle/{label}",
                            "index_tag": "H",
                            **{field: record[field]
                               for field in ("bytes", "sha256", "md5")},
                        }
                        for label, record in controller_sources.items()
                    },
                },
                "python_startup_flags": subject.EXPECTED_PYTHON_STARTUP_FLAGS,
                "python_startup_options":
                    subject.EXPECTED_PYTHON_STARTUP_OPTIONS,
                "initial_top_level_compilation_in_host_trust_boundary": True,
                "local_sources": controller_sources,
                "python_runtime": subject.validate_python_runtime(),
                "host_tools": subject.validate_controller_tools(),
                "git_environment": {
                    "LC_ALL": "C",
                    "PATH": "/usr/bin:/bin",
                    "GIT_CONFIG_NOSYSTEM": "1",
                    "GIT_CONFIG_GLOBAL": "/dev/null",
                    "GIT_TERMINAL_PROMPT": "0",
                    "GIT_NO_REPLACE_OBJECTS": "1",
                    "GIT_OPTIONAL_LOCKS": "0",
                },
            }

            source, source_record = write(flyspeck, "source.ml", b"source")
            normalized, normalized_record = write(overlay, "source.ml", b"normalized")
            certificate, certificate_record = write(generated, "cert.out", b"certificate")
            process_input, process_record = write(candle, "metadata/date", b"fixed date")
            prefix, prefix_record = write(root, "prefix.ml", b'#flyspeck_needs "source.ml";;\n')
            prefix_record = {"path": "prefix.ml", **prefix_record}

            prepared = {
                "source_runtime": [{
                    "repository": "flyspeck", "path": "source.ml",
                    "absolute": str(source), **source_record,
                }],
                "source_alias_runtime": [],
                "harness_records": harness_records,
                "normalized_runtime": [{
                    "relative": "source.ml", "original_relative": "source.ml",
                    "original": str(source), "output": str(normalized),
                    **normalized_record,
                }],
                "generated_runtime": [{
                    "class": "lp-certificate-prepared", "relative": "cert.out",
                    "path": str(certificate), **certificate_record,
                }],
                "lp_certificate_runtime": [{"relative": "cert.out"}],
                "process_runtime": [{
                    "relative": "metadata/date", "path": str(process_input),
                    **process_record,
                }],
                "prefix_path": prefix,
                "prefix_record": prefix_record,
                "linked_record": linked_record,
            }
            runtime, snapshot = subject.create_runtime_snapshot(
                output, candle, prepared, {
                    "outputs": linked_outputs,
                    "runtime_elf_closure": {
                        "policy":
                            subject.cakeml_artifact_provenance
                            .ELF_DYNAMIC_CLOSURE_POLICY,
                        "dynamic_path_tags": {},
                        "files": {
                            str(runtime_object): runtime_object_record,
                        },
                        "roles": {"libc.so.6": str(runtime_object)},
                        "virtual_objects": [],
                    },
                }, controller_execution,
            )
            subject.validate_runtime_snapshot(snapshot, output)
            archived_transition = (
                output / "snapshot/candle/candle/build/bootstrap-transition.json"
            )
            self.assertTrue(
                archived_transition.is_file(),
            )
            self.assertEqual(
                archived_transition.read_bytes(),
                transition_copy.read_bytes(),
            )
            self.assertEqual(
                runtime["prefix_path"].read_bytes(), prefix.read_bytes(),
            )
            source_entry = next(
                record for record in snapshot["files"]
                if record["path"] == "flyspeck/source.ml"
            )
            self.assertEqual(source_entry["classes"], ["source:flyspeck"])
            self.assertEqual(len({item["path"] for item in snapshot["files"]}),
                             snapshot["file_count"])
            self.assertTrue(any(
                item["path"] ==
                "candle/candle/build/cakeml-build-provenance.json"
                and item["classes"] == ["linked-provenance-record"]
                for item in snapshot["files"]
            ))
            self.assertTrue(any(
                item["path"].startswith("runtime-elf/")
                and item["classes"] == ["archived-runtime-elf"]
                for item in snapshot["files"]
            ))
            self.assertTrue(any(
                item["path"] ==
                "candle/candle/build/bootstrap-provenance.json"
                and item["classes"] == ["linked-runtime"]
                for item in snapshot["files"]
            ))
            self.assertTrue(any(
                item["path"] == "candle/candle/build/bootstrap.log"
                and item["classes"] == ["linked-runtime"]
                for item in snapshot["files"]
            ))
            retained_runner = next(
                item for item in snapshot["controller_execution"]["local_sources"]
                if item["label"] == "flyspeck_stratum_runtime.py"
            )
            self.assertEqual(
                (output / "snapshot" / retained_runner["path"]).read_bytes(),
                subject.RUNNER_SOURCE_BYTES,
            )
            self.assertTrue(any(
                item["classes"] == ["controller-python-executable"]
                for item in snapshot["files"]
            ))
            self.assertEqual(
                {item["label"] for item in
                 snapshot["controller_execution"]["host_tools"]},
                set(subject.EXPECTED_CONTROLLER_TOOLS),
            )
            self.assertEqual(
                snapshot["controller_execution"]["python_runtime"]
                ["elf_dynamic_path_tags"],
                {},
            )

            malformed = copy.deepcopy(snapshot)
            malformed["schema"] = 1
            with self.assertRaisesRegex(subject.ContractError, "snapshot schema"):
                subject.validate_runtime_snapshot(malformed, output)
            malformed = copy.deepcopy(snapshot)
            malformed["controller_execution"]["python_runtime"]["version"] = "other"
            with self.assertRaisesRegex(
                subject.ContractError, "Python execution identity mismatch",
            ):
                subject.validate_runtime_snapshot(malformed, output)
            malformed = copy.deepcopy(snapshot)
            malformed["controller_execution"]["python_runtime"][
                "elf_dynamic_path_tags"
            ] = {"RUNPATH": ["/injected"]}
            with self.assertRaisesRegex(
                subject.ContractError, "Python ELF metadata mismatch",
            ):
                subject.validate_runtime_snapshot(malformed, output)

            snapshot_root = output / "snapshot"
            snapshot_root.chmod(0o755)
            extra = snapshot_root / "unrecorded"
            extra.write_bytes(b"not in the closure")
            with self.assertRaisesRegex(subject.ContractError, "unrecorded.*files"):
                subject.validate_runtime_snapshot(snapshot, output)
            extra.unlink()
            extra.mkdir()
            with self.assertRaisesRegex(subject.ContractError, "unrecorded.*directories"):
                subject.validate_runtime_snapshot(snapshot, output)
            extra.rmdir()
            extra.symlink_to(snapshot_root / "flyspeck/source.ml")
            with self.assertRaisesRegex(subject.ContractError, "contains a symlink"):
                subject.validate_runtime_snapshot(snapshot, output)
            extra.unlink()
            snapshot_root.chmod(0o555)

            retained_runner_path = snapshot_root / retained_runner["path"]
            retained_runner_path.chmod(0o644)
            retained_runner_path.write_bytes(b"tampered controller")
            with self.assertRaisesRegex(subject.ContractError, "mismatch"):
                subject.validate_runtime_snapshot(snapshot, output)
            retained_runner_path.write_bytes(subject.RUNNER_SOURCE_BYTES)
            retained_runner_path.chmod(0o444)

            snapshot_source = output / "snapshot/flyspeck/source.ml"
            snapshot_source.chmod(0o644)
            snapshot_source.write_bytes(b"tampered")
            with self.assertRaisesRegex(subject.ContractError, "mismatch"):
                subject.validate_runtime_snapshot(snapshot, output)

    def test_runner_cli_requires_isolated_python(self) -> None:
        runner = Path(subject.__file__).resolve()
        ordinary = subprocess.run(
            ["/usr/bin/python3", str(runner), "--help"],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
        self.assertNotEqual(ordinary.returncode, 0)
        self.assertIn("Python startup flags mismatch", ordinary.stdout)
        for flags in (
            ("-I",),
            ("-S",),
            ("-I", "-S", "-O"),
            ("-I", "-S", "-X", "tracemalloc"),
            ("-I", "-S", "-W", "error"),
            ("-I", "-S", "-u"),
        ):
            rejected = subprocess.run(
                ["/usr/bin/python3", *flags, str(runner), "--help"],
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            )
            self.assertNotEqual(rejected.returncode, 0)
            self.assertRegex(
                rejected.stdout, r"Python startup (?:flags|options) mismatch",
            )
        isolated = subprocess.run(
            ["/usr/bin/python3", "-I", "-S", str(runner), "--help"],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
        self.assertEqual(isolated.returncode, 0, isolated.stdout)

        imported = subprocess.run(
            [
                "/usr/bin/python3", "-I", "-S", "-c",
                (
                    "import importlib.util,pathlib;"
                    f"p=pathlib.Path({str(runner)!r});"
                    "s=importlib.util.spec_from_file_location('imported_runner',p);"
                    "m=importlib.util.module_from_spec(s);s.loader.exec_module(m);"
                    "m.main()"
                ),
            ],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
        self.assertNotEqual(imported.returncode, 0)
        self.assertIn("execute directly from its .py source", imported.stdout)

    def test_local_modules_execute_from_captured_source_bytes(self) -> None:
        for module in subject.local_python_modules():
            source = module.__candle_source_bytes__
            self.assertEqual(
                hashlib.sha256(source).hexdigest(),
                module.__candle_source_sha256__,
            )
            self.assertEqual(Path(module.__file__).read_bytes(), source)

    def test_all_controller_git_calls_share_the_fail_closed_policy(self) -> None:
        expected_environment = subject.flyspeck_stratum_plan.GIT_ENVIRONMENT
        self.assertEqual(
            subject.cakeml_artifact_provenance.git_environment(),
            expected_environment,
        )
        command = subject.cakeml_artifact_provenance.git_command(
            Path("/repository"), "status",
        )
        self.assertEqual(
            tuple(command[1:7]), subject.flyspeck_stratum_plan.GIT_OPTIONS,
        )

    def test_exact_source_loader_ignores_adjacent_bytecode(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "helper.py"
            cache = root / "__pycache__/helper.cpython-312.pyc"
            cache.parent.mkdir()
            source.write_text("VALUE = 'cached!'\n", encoding="utf-8")
            source_stat = source.stat()
            py_compile.compile(str(source), cfile=str(cache), doraise=True)
            source.write_text("VALUE = 'source!'\n", encoding="utf-8")
            os.utime(
                source,
                ns=(source_stat.st_atime_ns, source_stat.st_mtime_ns),
            )
            sys.path.insert(0, str(root))
            try:
                ordinary = importlib.import_module("helper")
                self.assertEqual(ordinary.VALUE, "cached!")
            finally:
                sys.modules.pop("helper", None)
                sys.path.pop(0)
            name = "_candle_stratum_test_exact_source"
            try:
                module = subject._load_local_source(name, source.resolve())
                self.assertEqual(module.VALUE, "source!")
                self.assertEqual(
                    module.__candle_source_bytes__, source.read_bytes(),
                )
            finally:
                sys.modules.pop(name, None)

    def test_exact_source_loader_rejects_preloaded_collision(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / "helper.py"
            source.write_text("VALUE = 1\n", encoding="utf-8")
            name = "_candle_stratum_test_preloaded"
            sys.modules[name] = types.ModuleType(name)
            try:
                with self.assertRaisesRegex(RuntimeError, "untrusted preloaded"):
                    subject._load_local_source(name, source.resolve())
            finally:
                sys.modules.pop(name, None)

    def test_snapshot_copy_rejects_bytes_not_bound_by_expected_digest(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "source"
            source.write_bytes(b"changed after validation")
            expected = subject.hash_file(source)
            expected["sha256"] = "0" * 64
            with self.assertRaisesRegex(subject.ContractError, "snapshot sha256 mismatch"):
                subject.snapshot_copy(source, root / "snapshot", "source", expected)

    def test_pre_attempt_failure_removes_only_new_incomplete_output(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "new-attempt"

            def fail_preflight(*arguments):
                ownership = arguments[-1]
                snapshot = output / "snapshot/readonly"
                snapshot.mkdir(parents=True)
                (snapshot / "partial").write_bytes(b"partial")
                snapshot.chmod(0o555)
                opened = output.stat()
                marker = output / ".candle-preflight-owner"
                marker.write_text(ownership["nonce"] + "\n", encoding="ascii")
                ownership.update({
                    "created": True,
                    "device": opened.st_dev,
                    "inode": opened.st_ino,
                    "marker_path": marker,
                    "marker_ready": True,
                })
                raise subject.ContractError("injected preflight failure")

            with mock.patch.object(
                subject, "_run_attempt_impl", side_effect=fail_preflight,
            ):
                with self.assertRaisesRegex(
                    subject.ContractError, "injected preflight failure",
                ):
                    subject.run_attempt(
                        Path("candle.sh"), Path("plan"), "boundary", output,
                        1, 1, 1, 1,
                    )
            self.assertFalse(output.exists())

    def test_lost_output_race_never_deletes_competing_tree(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "competing-attempt"

            def lose_race(*_arguments):
                output.mkdir()
                (output / "competitor").write_bytes(b"owned elsewhere")
                raise subject.ContractError("output already exists")

            with mock.patch.object(
                subject, "_run_attempt_impl", side_effect=lose_race,
            ):
                with self.assertRaisesRegex(
                    subject.ContractError, "output already exists",
                ):
                    subject.run_attempt(
                        Path("candle.sh"), Path("plan"), "boundary", output,
                        1, 1, 1, 1,
                    )
            self.assertEqual(
                (output / "competitor").read_bytes(), b"owned elsewhere",
            )

    def test_owned_empty_directory_is_cleaned_if_marker_creation_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "attempt"

            def fail_marker(*arguments):
                ownership = arguments[-1]
                output.mkdir()
                opened = output.stat()
                ownership.update({
                    "created": True,
                    "device": opened.st_dev,
                    "inode": opened.st_ino,
                    "marker_ready": False,
                })
                raise OSError("injected marker failure")

            with mock.patch.object(
                subject, "_run_attempt_impl", side_effect=fail_marker,
            ):
                with self.assertRaisesRegex(OSError, "injected marker failure"):
                    subject.run_attempt(
                        Path("candle.sh"), Path("plan"), "boundary", output,
                        1, 1, 1, 1,
                    )
            self.assertFalse(output.exists())

    def test_outer_wrapper_restores_handlers_after_internal_escape(self) -> None:
        original_term = signal.getsignal(signal.SIGTERM)
        original_int = signal.getsignal(signal.SIGINT)
        original_mask = signal.pthread_sigmask(signal.SIG_BLOCK, set())

        def escape(*_arguments):
            signal.signal(signal.SIGTERM, lambda *_ignored: None)
            signal.signal(signal.SIGINT, lambda *_ignored: None)
            signal.pthread_sigmask(
                signal.SIG_BLOCK, {signal.SIGTERM, signal.SIGINT},
            )
            raise RuntimeError("injected internal escape")

        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "attempt"
            with mock.patch.object(
                subject, "_run_attempt_impl", side_effect=escape,
            ):
                with self.assertRaisesRegex(
                    RuntimeError, "injected internal escape",
                ):
                    subject.run_attempt(
                        Path("candle.sh"), Path("plan"), "boundary", output,
                        1, 1, 1, 1,
                    )
        self.assertIs(signal.getsignal(signal.SIGTERM), original_term)
        self.assertIs(signal.getsignal(signal.SIGINT), original_int)
        self.assertEqual(
            signal.pthread_sigmask(signal.SIG_BLOCK, set()), original_mask,
        )

    def test_internal_attempt_rejects_raw_plan_root_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            target = root / "plan-target"
            target.mkdir()
            plan_link = root / "plan-link"
            plan_link.symlink_to(target, target_is_directory=True)
            with self.assertRaisesRegex(
                subject.ContractError, "stratum plan root must not be a symlink",
            ):
                subject._run_attempt_impl(
                    root / "missing-candle.sh", plan_link, "boundary",
                    root / "attempt", 1, 1, 1, 1,
                )

    def test_lp_certificate_runtime_uses_contract_order_not_source_order(self) -> None:
        expected = [f"easy_{index}.dat" for index in range(1, 39)] + [
            "hard_7.dat",
        ]
        source_order = [
            {
                "class": "lp-certificate-prepared" if name == "hard_7.dat"
                else "lp-certificate",
                "relative": f"formal_lp/glpk/binary/{name}",
            }
            for name in reversed(expected)
        ]
        ordered = subject.order_lp_certificate_runtime(source_order, expected)
        self.assertEqual(
            [Path(item["relative"]).name for item in ordered], expected,
        )
        source_order[-1]["relative"] = "formal_lp/glpk/binary/unexpected.dat"
        with self.assertRaisesRegex(subject.ContractError,
                                    "certificate basename set mismatch"):
            subject.order_lp_certificate_runtime(source_order, expected)

    def test_child_resource_limiter_installs_all_three_limits(self) -> None:
        cpu_seconds = 17
        address_space = 2 * subject.GIB
        output_file = subject.GIB
        installer = subject.process_limit_preexec(
            cpu_seconds, address_space, output_file,
        )
        code = (
            "import json,resource; "
            "print(json.dumps([resource.getrlimit(resource.RLIMIT_CPU),"
            "resource.getrlimit(resource.RLIMIT_AS),"
            "resource.getrlimit(resource.RLIMIT_FSIZE)]))"
        )
        completed = subprocess.run(
            [sys.executable, "-c", code], check=True, text=True,
            stdout=subprocess.PIPE, preexec_fn=installer,
        )
        self.assertEqual(json.loads(completed.stdout), [
            [cpu_seconds, cpu_seconds],
            [address_space, address_space],
            [output_file, output_file],
        ])


if __name__ == "__main__":
    unittest.main()
