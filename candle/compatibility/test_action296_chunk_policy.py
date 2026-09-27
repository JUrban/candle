import tempfile
import unittest
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import action296_chunk_policy as policy


class Action296ChunkPolicyTests(unittest.TestCase):
    def test_direct_one_split_and_depth_two(self) -> None:
        lines = [
            "CANDLE_CV_ACTION296_CHUNK_SCAN_LEAF label=t index=1 depth=0 "
            "final_cells=1 first_axis=none "
            "depth1_flags=1,1,1,1,1,1,1,1,1,1,1,1,1 depth2=",
            "CANDLE_CV_ACTION296_CHUNK_SCAN_LEAF label=t index=2 depth=1 "
            "final_cells=2 first_axis=4 "
            "depth1_flags=0,0,0,0,0,0,0,1,1,0,0,0,0 depth2=",
            "CANDLE_CV_ACTION296_CHUNK_SCAN_LEAF label=t index=3 depth=2 "
            "final_cells=3 first_axis=6 "
            "depth1_flags=0,0,0,0,0,0,0,0,0,0,0,0,1 "
            "depth2=0:4:1,1,1,1,1,1,1,1,1,1,1,1",
        ]
        leaves = [policy.parse_leaf(line) for line in lines]
        rendered = policy.render_ml(leaves, "candle_test_plan")
        self.assertIn(
            "open Candle_cv_action296_adaptive_forest_prove;;", rendered
        )
        self.assertIn("(1,Candle_action296_forest_leaf)", rendered)
        self.assertIn("Candle_action296_forest_split (6,", rendered)
        self.assertIn("let candle_test_plan_final_cells = 6;;", rendered)
        self.assertIn("let candle_test_plan_expected_digest = None;;", rendered)

        pinned = policy.render_ml(
            leaves,
            "candle_test_plan",
            expected_digest="0123456789abcdef0123456789abcdef",
        )
        self.assertIn(
            'let candle_test_plan_expected_digest = '
            'Some "0123456789abcdef0123456789abcdef";;',
            pinned,
        )
        with self.assertRaisesRegex(ValueError, "theorem digest"):
            policy.render_ml(
                leaves,
                "candle_test_plan",
                expected_digest="not-a-digest",
            )

    def test_wrong_selected_axis_is_rejected(self) -> None:
        line = (
            "CANDLE_CV_ACTION296_CHUNK_SCAN_LEAF label=t index=2 depth=1 "
            "final_cells=2 first_axis=1 "
            "depth1_flags=0,0,0,0,0,0,0,1,1,0,0,0,0 depth2="
        )
        with self.assertRaisesRegex(ValueError, "invalid depth-one"):
            policy.parse_leaf(line)

    def test_complete_log_and_range(self) -> None:
        record = (
            "CANDLE_CV_ACTION296_CHUNK_SCAN_LEAF label=t index=4 depth=0 "
            "final_cells=1 first_axis=none "
            "depth1_flags=1,1,1,1,1,1,1,1,1,1,1,1,1 depth2=\n"
        )
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "candle.log"
            path.write_text(record + policy.OK_MARKER + "\n", encoding="utf-8")
            leaves = policy.read_logs([path])
            policy.validate_range(leaves, 4, 4)
            with self.assertRaisesRegex(ValueError, "range mismatch"):
                policy.validate_range(leaves, 4, 5)

    def test_multiple_logs_merge_and_duplicate_rejection(self) -> None:
        def record(index: int) -> str:
            return (
                "CANDLE_CV_ACTION296_CHUNK_SCAN_LEAF label=t "
                f"index={index} depth=0 final_cells=1 first_axis=none "
                "depth1_flags=1,1,1,1,1,1,1,1,1,1,1,1,1 depth2=\n"
            )

        with tempfile.TemporaryDirectory() as directory:
            first = Path(directory) / "first.log"
            second = Path(directory) / "second.log"
            first.write_text(
                record(4) + policy.OK_MARKER + "\n", encoding="utf-8"
            )
            second.write_text(
                record(5) + policy.OK_MARKER + "\n", encoding="utf-8"
            )
            leaves = policy.read_logs([second, first])
            policy.validate_range(leaves, 4, 5)
            self.assertEqual([leaf.index for leaf in leaves], [4, 5])
            with self.assertRaisesRegex(ValueError, "duplicate leaf index 4"):
                policy.read_logs([first, first])

    def test_unresolved_plan_cannot_be_rendered(self) -> None:
        line = (
            "CANDLE_CV_ACTION296_CHUNK_SCAN_LEAF label=t index=6 "
            "depth=unresolved final_cells=0 first_axis=4 "
            "depth1_flags=0,0,0,0,0,0,0,0,0,0,0,0,0 "
            "depth2=0:none:0,0,0,0,0,0,0,0,0,0,0,0;"
            "1:1:1,1,1,1,1,1,1,1,1,1,1,1"
        )
        leaf = policy.parse_leaf(line)
        self.assertIsNone(leaf.depth)
        with self.assertRaisesRegex(ValueError, "unresolved plan"):
            policy.render_ml([leaf], "candle_test_plan")


if __name__ == "__main__":
    unittest.main()
