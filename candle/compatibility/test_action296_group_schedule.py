import tempfile
import unittest
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import action296_group_schedule as schedule


class Action296GroupScheduleTests(unittest.TestCase):
    RESULT = (
        "CANDLE_CV_ACTION296_BOUNDED_GROUPED_POLICY_RESULT "
        "original_leaves=8 final_cells=12 attempts=5 successful_groups=3 "
        "group_sizes=4,2,2 theorem_digest=0123456789abcdef0123456789abcdef"
    )

    def test_parse_and_render(self) -> None:
        parsed = schedule.parse_result("#   " + self.RESULT)
        self.assertEqual(parsed.group_sizes, (4, 2, 2))
        self.assertEqual(parsed.original_leaves, 8)
        self.assertIn(
            "let candle_action296_generated_group_sizes = [4;2;2];;",
            schedule.render_ml(parsed),
        )

    def test_parse_fixed_outer_discovery_result(self) -> None:
        result = self.RESULT.replace(
            "CANDLE_CV_ACTION296_BOUNDED_GROUPED_POLICY_RESULT",
            "CANDLE_CV_ACTION296_FIXED_OUTER_GROUPED_DISCOVERY_RESULT",
        )
        parsed = schedule.parse_result(result)
        self.assertEqual(parsed.group_sizes, (4, 2, 2))

    def test_inconsistent_counts_are_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "leaf count mismatch"):
            schedule.parse_result(self.RESULT.replace("4,2,2", "4,2,1"))
        with self.assertRaisesRegex(ValueError, "success count mismatch"):
            schedule.parse_result(
                self.RESULT.replace("successful_groups=3", "successful_groups=4")
            )
        with self.assertRaisesRegex(ValueError, "attempt count mismatch"):
            schedule.parse_result(self.RESULT.replace("attempts=5", "attempts=2"))

    def test_complete_log_is_required(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "candle.log"
            path.write_text(self.RESULT + "\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "incomplete"):
                schedule.read_schedule(path)
            path.write_text(
                self.RESULT + "\n" + schedule.OK_MARKER + "\n",
                encoding="utf-8",
            )
            self.assertEqual(schedule.read_schedule(path).group_sizes, (4, 2, 2))


if __name__ == "__main__":
    unittest.main()
