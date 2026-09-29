#!/usr/bin/env python3

import unittest

import case10173_axis4_scan as subject
import case10173_parent_scan as parent_scan


def root(index: int, flags: tuple[bool, ...]) -> parent_scan.RootVerdict:
    return parent_scan.RootVerdict(label="test", index=index, flags=flags)


class Case10173Axis4ScanTest(unittest.TestCase):
    def test_validation_and_fallback(self) -> None:
        parents = [root(0, (True,)), root(1, (False,)), root(2, (False,))]
        children = [root(1, (False, True, True)),
                    root(2, (False, True, False))]
        subject.validate_axis4_scans(parents, children)
        self.assertEqual(subject.fallback_indices(children), [2])
        rendered = subject.render_json(children, [])
        self.assertIn('"axis4_closed": 1', rendered)

    def test_rejects_incomplete_or_malformed_scan(self) -> None:
        parents = [root(0, (False,)), root(1, (False,))]
        with self.assertRaisesRegex(ValueError, "axis-4 scan mismatch"):
            subject.validate_axis4_scans(
                parents, [root(0, (False, True, True))],
            )
        with self.assertRaisesRegex(ValueError, "parent plus two"):
            subject.validate_axis4_scans(
                parents,
                [root(0, (False, True)), root(1, (False, True, True))],
            )

    def test_chunks_require_real_fallback_work(self) -> None:
        self.assertEqual(subject.chunks([1, 2, 3], 2), [[1], [2, 3]])
        with self.assertRaisesRegex(ValueError, "more fallback"):
            subject.chunks([1], 2)


if __name__ == "__main__":
    unittest.main()
