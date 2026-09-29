#!/usr/bin/env python3

import tempfile
import unittest
from pathlib import Path

import case10173_parent_scan as subject


def log(label: str, start: int, flags: list[int]) -> str:
    records = "\n".join(
        f"# {subject.ROOT_MARKER} label={label} index={start + offset} "
        f"flags={flag}"
        for offset, flag in enumerate(flags)
    )
    return (
        f"{records}\n"
        f"{subject.RESULT_MARKER} label={label} roots={len(flags)} "
        f"verdicts={len(flags)} theorem_authority=none\n"
        f"{subject.OK_MARKER}\n"
    )


class Case10173ParentScanTest(unittest.TestCase):
    def test_reads_complete_disjoint_range_and_renders_rejections(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            first = Path(directory) / "first.log"
            second = Path(directory) / "second.log"
            first.write_text(log("first", 0, [1, 0]), encoding="utf-8")
            second.write_text(log("second", 2, [1, 0]), encoding="utf-8")
            roots = subject.read_logs([first, second])
            subject.validate_parent_range(roots, 0, 3)
            rendered = subject.render_ml(roots)
            self.assertIn("[1;3]", rendered)
            self.assertIn("include_children = true", rendered)

    def test_rejects_duplicate_index(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            first = Path(directory) / "first.log"
            second = Path(directory) / "second.log"
            first.write_text(log("first", 0, [1]), encoding="utf-8")
            second.write_text(log("second", 0, [0]), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "duplicate root index 0"):
                subject.read_logs([first, second])

    def test_rejects_incomplete_log_and_child_flags(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "bad.log"
            path.write_text(
                f"{subject.ROOT_MARKER} label=x index=0 flags=1,1\n"
                f"{subject.RESULT_MARKER} label=x roots=1 verdicts=2 "
                "theorem_authority=none\n"
                f"{subject.OK_MARKER}\n",
                encoding="utf-8",
            )
            roots = subject.read_logs([path])
            with self.assertRaisesRegex(ValueError, "contains child verdicts"):
                subject.validate_parent_range(roots, 0, 0)
            path.write_text("partial\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "incomplete"):
                subject.read_logs([path])


if __name__ == "__main__":
    unittest.main()
