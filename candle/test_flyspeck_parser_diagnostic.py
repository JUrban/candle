#!/usr/bin/env python3

import copy
import importlib.util
import json
import os
import resource
import stat
import subprocess
import tempfile
import time
import unittest
from pathlib import Path
from unittest import mock


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SPEC = importlib.util.spec_from_file_location(
    "flyspeck_parser_diagnostic", HERE / "flyspeck_parser_diagnostic.py",
)
subject = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(subject)


class ParserDiagnosticTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.manifest_path = ROOT / subject.MANIFEST_RELATIVE
        cls.manifest_data = cls.manifest_path.read_bytes()
        cls.manifest = subject.load_object(cls.manifest_path, "test manifest")
        cls.pilot = subject.load_object(
            ROOT / subject.PILOT_RELATIVE, "test pilot",
        )

    def build_real_plan(self):
        return subject.build_plan(
            ROOT, Path("/unused-flyspeck-root"), "1" * 40,
            self.manifest, self.manifest_data, self.pilot,
        )

    def publish_plan_tree(self, root, plan, inputs, host):
        root.mkdir()
        subject._write_tree(
            root,
            {
                subject.PLAN_NAME: subject.json_bytes(plan),
                subject.HOST_RECEIPT_NAME: subject.json_bytes(host),
                **inputs,
            },
            subject.PLAN_ROOT_MODE,
            subject.PLAN_FILE_MODE,
        )

    def make_tree_removable(self, root):
        for current, directories, _files in os.walk(root):
            Path(current).chmod(0o755)
            for name in directories:
                (Path(current) / name).chmod(0o755)

    def test_committed_pilot_is_current(self) -> None:
        self.assertEqual(
            self.pilot,
            subject.build_pilot_descriptor(self.manifest, self.manifest_data),
        )

    def test_pilot_is_exactly_twenty_manifest_first_discoveries(self) -> None:
        keys = [entry["source_key"] for entry in self.pilot["inputs"]]
        self.assertEqual(len(keys), 20)
        self.assertEqual(keys[0], "candle:hol.ml")
        self.assertEqual(keys[9], "candle:candle/kernel.ml")
        self.assertEqual(keys[-1], "candle:itab.ml")
        self.assertEqual(
            self.pilot["selection"]["ordered_source_key_sha256"],
            subject.canonical_sha256(keys),
        )
        self.assertIn("bootstrap/core", self.pilot["selection"]["coverage"])
        self.assertIn("not representative", self.pilot["selection"]["coverage"])

    def test_all_eight_non_discovered_nodes_are_bound_with_reasons(self) -> None:
        exclusions = self.pilot["excluded_from_first_discovery"]
        self.assertEqual(self.pilot["selection"]["excluded_source_count"], 8)
        self.assertEqual(len(exclusions), 8)
        self.assertEqual(
            {entry["source_key"] for entry in exclusions},
            set(self.manifest["source_nodes"]) - {
                entry["source_key"]
                for entry in subject.derive_manifest_node_order(self.manifest)
            },
        )
        self.assertTrue(all(entry["reason"] for entry in exclusions))
        self.assertTrue(any(
            entry["source_key"].endswith("parser_verbose.hl") and
            entry["incoming_nontraversed_actions"][0]["status"] == "resolved-dynamic"
            for entry in exclusions
        ))

    def test_manifest_action_order_tamper_changes_selection(self) -> None:
        altered = copy.deepcopy(self.manifest)
        altered["source_nodes"]["candle:hol.ml"]["dependencies"].reverse()
        descriptor = subject.build_pilot_descriptor(altered, self.manifest_data)
        self.assertNotEqual(
            [entry["source_key"] for entry in descriptor["inputs"]],
            [entry["source_key"] for entry in self.pilot["inputs"]],
        )

    def test_standalone_action_is_masked_without_offset_drift(self) -> None:
        source = b"let before = 1;;\nloads \"dep.ml\";; (* loader *)\nlet after = 2;;\n"
        dependency = {
            "kind": "loads", "line": 2, "literal": "dep.ml",
            "status": "resolved", "syntax_position": "standalone-phrase",
        }
        prepared, actions, unsupported = subject.prepare_source(
            "candle:test.ml", source, [dependency],
        )
        self.assertEqual(unsupported, [])
        self.assertIsNotNone(prepared)
        assert prepared is not None
        self.assertEqual(len(prepared), len(source))
        self.assertNotIn(b"loads", prepared)
        self.assertEqual(prepared.count(b"\n"), source.count(b"\n"))
        self.assertEqual(actions[0]["action_semantics_executed"], False)

    def test_embedded_action_is_retained_but_never_executed(self) -> None:
        source = b"let f s = needs s;;\n"
        dependency = {
            "kind": "needs", "line": 1, "expression": "needs s",
            "status": "generated-runtime", "syntax_position": "embedded-expression",
        }
        prepared, actions, unsupported = subject.prepare_source(
            "candle:test.ml", source, [dependency],
        )
        self.assertEqual(prepared, source)
        self.assertEqual(unsupported, [])
        self.assertEqual(
            actions[0]["handling"],
            "retained-as-parser-input-but-never-executed-by-gate",
        )
        self.assertFalse(actions[0]["action_semantics_executed"])

    def test_unknown_action_is_explicitly_unsupported(self) -> None:
        dependency = {
            "kind": "loadt", "line": 1,
            "status": "resolved-dynamic", "syntax_position": "standalone-phrase",
        }
        prepared, actions, unsupported = subject.prepare_source(
            "candle:test.ml", b"loadt (select ());;\n", [dependency],
        )
        self.assertIsNone(prepared)
        self.assertTrue(unsupported)
        self.assertEqual(actions[0]["handling"], "unsupported-no-parser-launch-for-source")

    def test_masking_rejects_manifest_literal_rebinding(self) -> None:
        dependency = {
            "kind": "needs", "line": 1, "literal": "expected.ml",
            "status": "resolved", "syntax_position": "standalone-phrase",
        }
        with self.assertRaisesRegex(subject.ContractError, "literal mismatch"):
            subject.prepare_source(
                "candle:test.ml", b"needs \"other.ml\";;\n", [dependency],
            )

    def test_real_plan_is_ready_and_preserves_kernel_trigger(self) -> None:
        plan, files = self.build_real_plan()
        self.assertEqual(plan["input_count"], 20)
        self.assertEqual(plan["ready_count"], 20)
        self.assertEqual(plan["unsupported_count"], 0)
        kernel = plan["inputs"][9]
        kernel_bytes = files[kernel["prepared_input"]["path"]]
        self.assertIn(b"Kernel.EQ_MP", kernel_bytes)
        self.assertFalse(plan["promotion"]["eligible"])
        self.assertFalse(plan["promotion"]["s2_evidence"])

    def test_real_plan_masks_loader_lines_and_binds_generated_inventory(self) -> None:
        plan, files = self.build_real_plan()
        hol = plan["inputs"][0]
        hol_bytes = files[hol["prepared_input"]["path"]]
        self.assertNotIn(b'loads "hol_loader.ml"', hol_bytes)
        self.assertGreater(plan["generated_inputs"]["entry_count"], 1)
        self.assertFalse(plan["generated_inputs"]["semantics_checked"])
        self.assertTrue(all(
            row["handling"] == "not-consumed-by-parser-only-diagnostic"
            for row in plan["generated_inputs"]["bindings"]
        ))

    def test_normalized_source_fails_closed_in_pilot(self) -> None:
        altered = copy.deepcopy(self.manifest)
        altered["source_nodes"]["candle:candle/kernel.ml"]["execution_normalization"] = {
            "id": "test-only",
        }
        plan, files = subject.build_plan(
            ROOT, Path("/unused-flyspeck-root"), "1" * 40,
            altered, self.manifest_data, self.pilot,
        )
        self.assertEqual(plan["unsupported_count"], 1)
        self.assertEqual(plan["inputs"][9]["status"], "unsupported-no-launch")
        self.assertNotIn("inputs/009.ml", files)

    def test_validate_file_rejects_source_tamper(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source.ml"
            path.write_bytes(b"let x = 1;;\n")
            expected = subject.bytes_record(b"let x = 2;;\n")
            with self.assertRaisesRegex(subject.ContractError, "SHA-256 mismatch"):
                subject.validate_file(path, expected, "test source")

    def test_duplicate_json_key_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.json"
            path.write_text('{"schema":1,"schema":2}\n', encoding="utf-8")
            with self.assertRaisesRegex(subject.ContractError, "duplicate JSON key"):
                subject.load_object(path)

    def test_protocol_accepts_only_bound_ok_marker(self) -> None:
        nonce = "a" * 64
        result = subprocess.CompletedProcess(
            [], 0,
            subject.RESULT_PREFIX + nonce.encode() + b"\tOK\n",
            b"",
        )
        self.assertEqual(subject.parse_protocol_result(nonce, result), "parse-ok")
        rebound = subprocess.CompletedProcess(
            [], 0,
            subject.RESULT_PREFIX + ("b" * 64).encode() + b"\tOK\n",
            b"",
        )
        with self.assertRaisesRegex(subject.ContractError, "violates protocol"):
            subject.parse_protocol_result(nonce, rebound)

    def test_protocol_accepts_bounded_parser_error(self) -> None:
        nonce = "c" * 64
        stderr = b"parser detail\n"
        digest = subject.hashlib.sha256(
            subject.ERROR_DIGEST_DOMAIN + stderr,
        ).hexdigest().encode()
        result = subprocess.CompletedProcess(
            [], subject.PARSER_ERROR_EXIT,
            subject.RESULT_PREFIX + nonce.encode() + b"\tPARSE_ERROR\t" + digest + b"\n",
            stderr,
        )
        self.assertEqual(subject.parse_protocol_result(nonce, result), "parse-error")

    def test_parser_error_requires_exit_code_exactly_65(self) -> None:
        nonce = "d" * 64
        stderr = b"parse error\n"
        digest = subject.hashlib.sha256(
            subject.ERROR_DIGEST_DOMAIN + stderr,
        ).hexdigest().encode()
        result = subprocess.CompletedProcess(
            [], 1,
            subject.RESULT_PREFIX + nonce.encode() + b"\tPARSE_ERROR\t" + digest + b"\n",
            stderr,
        )
        with self.assertRaisesRegex(subject.ContractError, "violates protocol"):
            subject.parse_protocol_result(nonce, result)

    def test_parser_error_requires_canonical_utf8_stderr(self) -> None:
        nonce = "e" * 64
        stderr = b"\xff"
        digest = subject.hashlib.sha256(
            subject.ERROR_DIGEST_DOMAIN + stderr,
        ).hexdigest().encode()
        result = subprocess.CompletedProcess(
            [], subject.PARSER_ERROR_EXIT,
            subject.RESULT_PREFIX + nonce.encode() + b"\tPARSE_ERROR\t" + digest + b"\n",
            stderr,
        )
        with self.assertRaisesRegex(subject.ContractError, "well-formed UTF-8"):
            subject.parse_protocol_result(nonce, result)

    def test_capability_mismatch_stops_at_empty_handshake(self) -> None:
        response = subprocess.CompletedProcess([], 0, b"generic compiler\n", b"")
        sentinel = object()
        with tempfile.TemporaryDirectory() as directory:
            io_root = Path(directory)
            io_root.chmod(subject.PRIVATE_IO_MODE)
            with mock.patch.object(
                subject, "run_child_capped", return_value=response,
            ) as invoked:
                with self.assertRaisesRegex(subject.ContractError, "capability mismatch"):
                    subject.capability_handshake(
                        Path("/fake/cake"), 1, subject.EXECUTION_ENVIRONMENT,
                        sentinel, io_root, 1024,
                    )
        self.assertEqual(invoked.call_count, 1)
        self.assertEqual(invoked.call_args.args[0][-1], subject.CAPABILITY_ARGUMENT)
        self.assertEqual(invoked.call_args.args[1], b"")
        self.assertIs(invoked.call_args.args[5], sentinel)

    def test_real_over_cap_subprocess_is_file_bounded_and_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            io_root = root / "io"
            io_root.mkdir(mode=subject.PRIVATE_IO_MODE)
            emitter = root / "emitter.py"
            emitter.write_text(
                "#!/usr/bin/python3\n"
                "import os\n"
                "while True:\n"
                "    os.write(1, b'x' * 4096)\n",
                encoding="utf-8",
            )
            emitter.chmod(0o755)

            def limit_output() -> None:
                resource.setrlimit(resource.RLIMIT_FSIZE, (1024, 1024))
                resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

            with self.assertRaisesRegex(
                subject.ContractError, "capability command failed",
            ):
                subject.capability_handshake(
                    emitter, 5, subject.EXECUTION_ENVIRONMENT,
                    limit_output, io_root, 1024,
                )
            self.assertEqual((io_root / "capability.stdout").stat().st_size, 1024)
            self.assertLessEqual(
                (io_root / "capability.stderr").stat().st_size, 1024,
            )
            self.assertEqual(
                stat.S_IMODE((io_root / "capability.stdout").stat().st_mode),
                subject.PRIVATE_IO_FILE_MODE,
            )

    def test_timeout_kills_spawned_process_group_descendant(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            io_root = root / "io"
            io_root.mkdir(mode=subject.PRIVATE_IO_MODE)
            child_pid_path = root / "child.pid"
            marker = root / "escaped.marker"
            program = root / "process-tree.py"
            program.write_text(
                "#!/usr/bin/python3\n"
                "import os, signal, sys, time\n"
                "child = os.fork()\n"
                "if child == 0:\n"
                "    signal.signal(signal.SIGTERM, signal.SIG_IGN)\n"
                "    time.sleep(10)\n"
                "    open(sys.argv[2], 'wb').write(b'escaped')\n"
                "    os._exit(0)\n"
                "open(sys.argv[1], 'w').write(str(child))\n"
                "signal.signal(signal.SIGTERM, signal.SIG_IGN)\n"
                "time.sleep(10)\n",
                encoding="utf-8",
            )
            program.chmod(0o755)
            with self.assertRaises(subprocess.TimeoutExpired):
                subject.run_child_capped(
                    [str(program), str(child_pid_path), str(marker)], b"",
                    root, 1, subject.EXECUTION_ENVIRONMENT, None,
                    io_root, "timeout-tree", 1024,
                )
            child_pid = int(child_pid_path.read_text())
            for _attempt in range(20):
                status = Path(f"/proc/{child_pid}/stat")
                try:
                    process_state = status.read_text().split()[2]
                except (FileNotFoundError, ProcessLookupError):
                    break
                if process_state == "Z":
                    break
                time.sleep(0.05)
            else:
                self.fail("timed-out parser descendant remained runnable")
            self.assertFalse(marker.exists())

    def test_unsupported_plan_launches_no_process(self) -> None:
        plan = {"unsupported_count": 1}
        with mock.patch.object(subject, "capability_handshake") as handshake:
            with self.assertRaisesRegex(subject.ContractError, "unsupported actions"):
                subject.run_runtime(
                    Path("/fake/cake"), Path("/fake/plan"), plan, 1,
                    subject.EXECUTION_ENVIRONMENT, None, Path("/fake/io"), 1024,
                )
        handshake.assert_not_called()

    def test_plan_root_symlink_alias_is_rejected_before_resolution(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            real = base / "real"
            real.mkdir()
            real.chmod(subject.PLAN_ROOT_MODE)
            alias = base / "alias"
            os.symlink(real, alias)
            with self.assertRaisesRegex(subject.ContractError, "symlink component"):
                subject.validate_plan_root(alias, {}, {}, {})

    def test_output_root_final_dangling_symlink_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "output"
            os.symlink(root / "missing", output)
            with self.assertRaisesRegex(subject.ContractError, "symlink alias"):
                subject.validate_fresh_output_root(output, "test output")

    def test_output_root_symlink_ancestor_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            real = root / "real"
            real.mkdir()
            alias = root / "alias"
            os.symlink(real, alias)
            with self.assertRaisesRegex(subject.ContractError, "symlink component"):
                subject.validate_fresh_output_root(alias / "output", "test output")

    def test_materialize_rejects_output_inside_either_authority_root(self) -> None:
        flyspeck_root = Path("/project/worktrees/flyspeck-v13-source")
        for label, authority_root in (
            ("Candle", ROOT), ("Flyspeck", flyspeck_root),
        ):
            output = authority_root / f".parser-output-test-{os.getpid()}"
            self.assertFalse(os.path.lexists(output))
            with mock.patch.object(subject, "reconstruct_plan_authority") as reconstruct:
                with self.assertRaisesRegex(
                    subject.ContractError, f"outside {label} root",
                ):
                    subject.materialize(ROOT, flyspeck_root, output)
            reconstruct.assert_not_called()
            self.assertFalse(os.path.lexists(output))

    def test_fully_rehashed_prepared_input_plan_is_rejected(self) -> None:
        expected_plan, expected_inputs = self.build_real_plan()
        execution = {"test-only": "authenticated controller execution"}
        expected_host = subject.build_host_receipt(
            ROOT, Path("/unused-flyspeck-root"),
            subject.json_bytes(expected_plan), execution,
        )
        forged_plan = copy.deepcopy(expected_plan)
        forged_inputs = dict(expected_inputs)
        selected = forged_plan["inputs"][0]
        relative = selected["prepared_input"]["path"]
        forged_inputs[relative] += b" (* forged *)"
        selected["prepared_input"] = subject.bytes_record(
            forged_inputs[relative], relative,
        )
        forged_plan["ordered_input_sha256"] = subject.canonical_sha256(
            forged_plan["inputs"],
        )
        forged_host = subject.build_host_receipt(
            ROOT, Path("/unused-flyspeck-root"),
            subject.json_bytes(forged_plan), execution,
        )
        with tempfile.TemporaryDirectory() as directory:
            plan_root = Path(directory) / "forged-plan"
            self.publish_plan_tree(
                plan_root, forged_plan, forged_inputs, forged_host,
            )
            try:
                with self.assertRaisesRegex(
                    subject.ContractError, "differs from reconstructed authority",
                ):
                    subject.validate_plan_root(
                        plan_root, expected_plan, expected_inputs, expected_host,
                    )
            finally:
                self.make_tree_removable(plan_root)

    def test_fully_rehashed_controller_and_promotion_claims_are_rejected(self) -> None:
        expected_plan, expected_inputs = self.build_real_plan()
        execution = {"test-only": "authenticated controller execution"}
        expected_host = subject.build_host_receipt(
            ROOT, Path("/unused-flyspeck-root"),
            subject.json_bytes(expected_plan), execution,
        )
        forged_plan = copy.deepcopy(expected_plan)
        forged_plan["controller"] = subject.bytes_record(
            b"forged controller", subject.CONTROLLER_RELATIVE.as_posix(),
        )
        forged_plan["promotion"] = {
            "eligible": False,
            "s1_evidence": True,
            "s2_evidence": True,
            "s3_evidence": True,
            "reason": "forged promotion claim",
        }
        forged_host = subject.build_host_receipt(
            ROOT, Path("/unused-flyspeck-root"),
            subject.json_bytes(forged_plan), execution,
        )
        with tempfile.TemporaryDirectory() as directory:
            plan_root = Path(directory) / "forged-controller-plan"
            self.publish_plan_tree(
                plan_root, forged_plan, expected_inputs, forged_host,
            )
            try:
                with self.assertRaisesRegex(
                    subject.ContractError, "differs from reconstructed authority",
                ):
                    subject.validate_plan_root(
                        plan_root, expected_plan, expected_inputs, expected_host,
                    )
            finally:
                self.make_tree_removable(plan_root)

    def test_fully_rehashed_host_root_rebinding_is_rejected(self) -> None:
        plan, inputs = self.build_real_plan()
        execution = {"test-only": "authenticated controller execution"}
        expected_host = subject.build_host_receipt(
            ROOT, Path("/unused-flyspeck-root"), subject.json_bytes(plan), execution,
        )
        forged_host = subject.build_host_receipt(
            Path("/forged/candle"), Path("/forged/flyspeck"),
            subject.json_bytes(plan), execution,
        )
        with tempfile.TemporaryDirectory() as directory:
            plan_root = Path(directory) / "forged-host-plan"
            self.publish_plan_tree(plan_root, plan, inputs, forged_host)
            try:
                with self.assertRaisesRegex(
                    subject.ContractError, "differs from reconstructed authority",
                ):
                    subject.validate_plan_root(
                        plan_root, plan, inputs, expected_host,
                    )
            finally:
                self.make_tree_removable(plan_root)

    def test_rehashed_transition_checker_binding_is_rejected(self) -> None:
        plan, _inputs = self.build_real_plan()
        forged = copy.deepcopy(plan)
        relative = subject.TRANSITION_CHECKER_RELATIVE.as_posix()
        forged["authority_sources"][relative] = subject.bytes_record(
            b"forged transition checker", relative,
        )
        head = subprocess.run(
            ["/usr/bin/git", "-C", str(ROOT), "rev-parse", "HEAD"],
            check=True, stdout=subprocess.PIPE, text=True,
        ).stdout.strip()
        with self.assertRaisesRegex(
            subject.ContractError, "plan authority source differs from commit",
        ):
            subject._load_direct_runtime_policy(ROOT, head, forged)

    def test_exact_module_loader_rejects_same_bytes_from_rebound_root(self) -> None:
        module_name = "_candle_parser_diagnostic_test_collision"
        source = b"VALUE = 1\n"
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first = root / "first.py"
            second = root / "second.py"
            first.write_bytes(source)
            second.write_bytes(source)
            try:
                subject._load_exact_source_module(module_name, first, source)
                with self.assertRaisesRegex(
                    subject.ContractError, "untrusted preloaded local module",
                ):
                    subject._load_exact_source_module(module_name, second, source)
            finally:
                subject.sys.modules.pop(module_name, None)

    def test_durable_snapshot_closed_inventory_rejects_omission_and_tamper(self) -> None:
        files = {
            "snapshot/plan/plan.json": b"plan\n",
            "snapshot/linked/outputs/cake": b"runtime\n",
        }
        inventory = subject.snapshot_inventory(files)
        for mutation in ("omission", "tamper"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory) / "result"
                root.mkdir()
                subject._write_tree(
                    root, files, subject.RESULT_ROOT_MODE, subject.RESULT_FILE_MODE,
                )
                subject.validate_snapshot_tree(root, inventory)
                target = root / "snapshot/linked/outputs/cake"
                if mutation == "omission":
                    target.parent.chmod(0o755)
                    target.unlink()
                    target.parent.chmod(subject.RESULT_ROOT_MODE)
                    expected = "inventory is incomplete"
                else:
                    target.chmod(0o644)
                    target.write_bytes(b"tampered\n")
                    target.chmod(subject.RESULT_FILE_MODE)
                    expected = "mismatch"
                try:
                    with self.assertRaisesRegex(subject.ContractError, expected):
                        subject.validate_snapshot_tree(root, inventory)
                finally:
                    self.make_tree_removable(root)

    def test_streamed_snapshot_copy_is_not_a_hardlink(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "source"
            source.write_bytes(b"large-output-placeholder\n")
            staging = root / "staging"
            staging.mkdir()
            expected = subject.bytes_record(source.read_bytes())
            record = subject.copy_snapshot_file(
                source, staging, "snapshot/linked/outputs/cake",
                expected, "test linked runtime",
            )
            destination = staging / record["path"]
            self.assertNotEqual(source.stat().st_ino, destination.stat().st_ino)
            self.assertEqual(record, subject.bytes_record(
                source.read_bytes(), "snapshot/linked/outputs/cake",
            ))

    def test_executing_controller_bytes_must_match_authenticated_blob(self) -> None:
        candle_head = subprocess.run(
            ["/usr/bin/git", "-C", str(ROOT), "rev-parse", "HEAD"],
            check=True, stdout=subprocess.PIPE, text=True,
        ).stdout.strip()
        flyspeck_root = Path("/project/worktrees/flyspeck-v13-source")
        flyspeck_head = self.manifest["repositories"]["flyspeck"]["commit"]
        with mock.patch.object(subject, "validate_git_blob"), mock.patch.object(
            subject, "SOURCE_BYTES", b"forged executing controller",
        ):
            with self.assertRaisesRegex(
                subject.ContractError, "executing controller differs",
            ):
                subject.reconstruct_plan_authority(
                    ROOT, candle_head, flyspeck_root, flyspeck_head,
                )

    def test_authenticated_candle_root_symlink_rebinding_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            alias = Path(directory) / "candle-alias"
            os.symlink(ROOT, alias)
            with self.assertRaisesRegex(subject.ContractError, "symlink component"):
                subject.reconstruct_plan_authority(
                    alias, "1" * 40,
                    Path("/project/worktrees/flyspeck-v13-source"), "2" * 40,
                )

    def test_direct_cli_rejects_nonisolated_python_before_work(self) -> None:
        result = subprocess.run(
            [
                "/usr/bin/python3",
                str(ROOT / subject.CONTROLLER_RELATIVE),
                "check-pilot", "--candle-root", str(ROOT),
            ],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=subject.EXECUTION_ENVIRONMENT,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn(b"requires /usr/bin/python3 -I -S", result.stderr)


if __name__ == "__main__":
    unittest.main()
