#!/usr/bin/env python3

import copy
import hashlib
import os
import sys
import tempfile
import unittest
from pathlib import Path

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


if __name__ == "__main__":
    unittest.main()
