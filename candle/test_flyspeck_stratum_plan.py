#!/usr/bin/env python3

import copy
import hashlib
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import flyspeck_stratum_plan as subject


class StratumPlanTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.candle_root = Path(__file__).resolve().parent.parent
        cls.audit = subject.audit_manifest(cls.candle_root)

    def test_exact_contiguous_boundaries_and_prefixes(self) -> None:
        records, prefixes = subject.boundary_records(self.audit)
        self.assertEqual(len(records), 8)
        self.assertEqual(
            [entry["completed_action_count"] for entry in records],
            [30, 38, 50, 61, 152, 185, 291, 297],
        )
        self.assertEqual(records[0]["next_action_index"], 30)
        self.assertIsNone(records[-1]["next_action_index"])
        self.assertEqual(records[-1]["cumulative_prefix"]["sha256"],
                         hashlib.sha256(self.audit["driver"]).hexdigest())
        for entry in records:
            prefix = prefixes[entry["cumulative_prefix"]["path"]]
            self.assertTrue(self.audit["driver"].startswith(prefix))
            self.assertEqual(entry["restart_mode"], "fresh-process-replay-from-action-0")
            self.assertFalse(entry["suffix_launch_authorized"])
            self.assertEqual(entry["process_state_checkpoint"], "not-captured")

    def test_action_order_binds_original_and_normalized_hashes(self) -> None:
        actions = self.audit["actions"]
        self.assertEqual([action["index"] for action in actions], list(range(297)))
        normalized = [action for action in actions if "execution_normalization" in action]
        self.assertGreater(len(normalized), 0)
        for action in actions:
            self.assertRegex(action["source_sha256"], r"^[0-9a-f]{64}$")
            self.assertRegex(action["source_md5"], r"^[0-9a-f]{32}$")
        for action in normalized:
            self.assertRegex(
                action["execution_normalization"]["normalized_sha256"],
                r"^[0-9a-f]{64}$",
            )

    def test_diagnostic_cutpoints_are_exact_cumulative_prefixes(self) -> None:
        records, prefixes = subject.diagnostic_records(self.audit)
        self.assertEqual([entry["completed_action_count"] for entry in records], [3, 19])
        self.assertEqual(
            [entry["boundary_id"] for entry in records],
            ["d0-diagnostic-through-002", "d1-diagnostic-through-018"],
        )
        for entry in records:
            self.assertTrue(entry["diagnostic_only"])
            self.assertIn("not S2/S3", entry["assurance_limit"])
            prefix = prefixes[entry["cumulative_prefix"]["path"]]
            self.assertTrue(self.audit["driver"].startswith(prefix))
            self.assertEqual(
                prefix.count(b"\n#flyspeck_needs "),
                entry["completed_action_count"],
            )

    def test_ordered_stratum_digest_rejects_mutation(self) -> None:
        manifest = copy.deepcopy(self.audit["manifest"])
        manifest["build_sequence_roots"][0]["target"] = "general/not-the-root.hl"
        with self.assertRaisesRegex(subject.ContractError, "root target drift"):
            # Exercise the same invariant without writing a mutated repository.
            sequence = manifest["build_sequence"]
            root = manifest["build_sequence_roots"][0]
            subject.require(root["target"] == sequence[0], "root target drift: 0")

    def test_plan_separates_host_status_from_execution_evidence(self) -> None:
        bindings = {
            "candle_head": "f" * 40,
            "source_bindings": [],
            "normalization_bindings": [],
            "generated_bindings": [],
            "normalization_contract_sha256": "1" * 64,
            "normalization_receipt_sha256": "2" * 64,
            "generated_contract_sha256": "3" * 64,
            "generated_receipt_sha256": "4" * 64,
        }
        plan, _ = subject.make_plan("0" * 40, self.audit, bindings)
        self.assertIn("not Candle execution", plan["claim"])
        self.assertFalse(plan["resume_contract"]["saved_process_or_kernel_state"])
        self.assertFalse(plan["resume_contract"]["suffix_only_programs_emitted"])
        self.assertFalse(plan["resume_contract"]["checkpoint_replay_claim"])
        self.assertEqual(len(plan["diagnostic_cutpoints"]), 2)
        self.assertEqual(plan["evidence_boundary"]["host_plan_or_schedule"],
                         "not S2/S3 evidence")

    def test_rejects_failed_staging_with_only_pending_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary) / "overlay.tmp.nonce"
            root.mkdir(mode=0o700)
            pending = root / ".flyspeck_normalization_receipt.json.pending"
            pending.write_text("{}", encoding="utf-8")
            os.chmod(pending, 0o444)
            os.chmod(root, 0o555)
            with self.assertRaises(subject.ContractError):
                subject.validate_materialized_tree(
                    root, {"flyspeck_normalization_receipt.json": 0o444},
                    "normalization overlay",
                )

    def materialization_fixture(
        self, root: Path,
    ) -> tuple[list[Path], dict, dict, dict[str, bytes]]:
        candle = root / "candle"
        flyspeck = root / "flyspeck"
        overlay = root / "overlay"
        generated = root / "generated"
        for directory in (candle, flyspeck, overlay, generated):
            directory.mkdir()
        audit = {"actions": [{"index": 0}]}
        validated = {
            "source_bindings": [{}],
            "normalization_bindings": [{}],
            "generated_bindings": [{}],
        }
        prefix = b"#use authenticated-prefix;;\n"
        plan = {
            "schema": 1,
            "kind": "candle-flyspeck-cumulative-stratum-plan",
            "boundaries": [{
                "boundary_id": "s0",
                "cumulative_prefix": {
                    "path": "stratum-s0.ml",
                    "sha256": hashlib.sha256(prefix).hexdigest(),
                },
            }],
            "diagnostic_cutpoints": [],
        }
        return [candle, flyspeck, overlay, generated], audit, validated, {
            "stratum-s0.ml": prefix,
        } | {"__plan__": plan}

    def materialize_fixture_plan(self, root: Path, output: Path) -> dict:
        roots, audit, validated, combined = self.materialization_fixture(root)
        plan = combined.pop("__plan__")
        with (
            mock.patch.object(subject, "audit_manifest", return_value=audit),
            mock.patch.object(subject, "validate_inputs", return_value=validated),
            mock.patch.object(subject, "make_plan", return_value=(plan, combined)),
        ):
            return subject.materialize(
                roots[0], "a" * 40, roots[1], roots[2], roots[3], output,
            )

    def test_plan_publication_is_exact_and_umask_independent(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            output = root / "plan-output"
            original_umask = os.umask(0)
            try:
                result = self.materialize_fixture_plan(root, output)
            finally:
                os.umask(original_umask)
            self.assertEqual(output.stat().st_mode & 0o777, subject.PLAN_ROOT_MODE)
            expected = {
                "stratum-s0.ml", "plan.json", "host-schedule-template.json",
                subject.HOST_MATERIALIZATION,
            }
            self.assertEqual({path.name for path in output.iterdir()}, expected)
            for path in output.iterdir():
                self.assertTrue(path.is_file() and not path.is_symlink())
                self.assertEqual(path.stat().st_mode & 0o777,
                                 subject.PLAN_FILE_MODE)
            receipt = json.loads(
                (output / subject.HOST_MATERIALIZATION).read_text(
                    encoding="utf-8",
                )
            )
            self.assertEqual(receipt["schema"], 2)
            self.assertEqual(receipt["publication"], subject.PLAN_PUBLICATION)
            self.assertEqual(receipt["plan_sha256"], result["plan_sha256"])

    def test_plan_publication_race_preserves_collision_and_staging(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            output = root / "plan-output"
            original_rename = subject._rename_noreplace

            def collide(source_path: Path, destination_path: Path) -> None:
                destination_path.mkdir()
                (destination_path / "unrelated").write_text(
                    "preserved", encoding="utf-8",
                )
                original_rename(source_path, destination_path)

            with (
                mock.patch.object(subject, "_rename_noreplace",
                                  side_effect=collide),
                self.assertRaises(FileExistsError),
            ):
                self.materialize_fixture_plan(root, output)
            self.assertEqual((output / "unrelated").read_text(encoding="utf-8"),
                             "preserved")
            staging = list(root.glob(".plan-output.tmp.*"))
            self.assertEqual(len(staging), 1)
            self.assertTrue((staging[0] / subject.PENDING_HOST_MATERIALIZATION).is_file())
            self.assertFalse((staging[0] / subject.HOST_MATERIALIZATION).exists())

    def test_plan_output_symlink_fails_before_validation(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            roots, _, _, _ = self.materialization_fixture(root)
            output = root / "plan-output"
            output.symlink_to(roots[0], target_is_directory=True)
            with self.assertRaisesRegex(subject.ContractError,
                                        "plan output root is a symlink"):
                subject.materialize(
                    roots[0], "a" * 40, roots[1], roots[2], roots[3], output,
                )

    def test_plan_tree_validator_rejects_extra_and_wrong_mode(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            output = root / "plan-output"
            self.materialize_fixture_plan(root, output)
            expected = {
                path.name: subject.PLAN_FILE_MODE for path in output.iterdir()
            }
            os.chmod(output, 0o755)
            with self.assertRaisesRegex(subject.ContractError, "root mode mismatch"):
                subject.validate_materialized_tree(output, expected, "stratum plan")
            extra = output / "extra"
            extra.write_bytes(b"unrecorded")
            os.chmod(extra, subject.PLAN_FILE_MODE)
            os.chmod(output, subject.PLAN_ROOT_MODE)
            with self.assertRaisesRegex(subject.ContractError, "unexpected file"):
                subject.validate_materialized_tree(output, expected, "stratum plan")


if __name__ == "__main__":
    unittest.main()
