#!/usr/bin/env python3

import hashlib
import sys
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import flyspeck_nonlinear_direct_get_dim_overlay as subject


FLYSPECK_ROOT = Path(
    "/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6"
)


class DirectGetDimOverlayTest(unittest.TestCase):
    def test_exact_authenticated_replacement(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output_root = Path(temporary) / "overlay"
            payload = subject.run(FLYSPECK_ROOT, output_root)
            destination = (
                output_root / "flyspeck" / payload["logical_relative_path"]
            )
            result = destination.read_bytes()
            self.assertEqual(result.count(subject.BEFORE), 0)
            self.assertEqual(result.count(subject.AFTER), 1)
            self.assertEqual(result.count(subject.INLINE_BEFORE), 0)
            self.assertEqual(
                result.count(subject.INLINE_AFTER),
                subject.INLINE_AFTER_BASE_COUNT + 2,
            )
            self.assertEqual(
                hashlib.sha256(result).hexdigest(),
                payload["output"]["sha256"],
            )
            self.assertEqual(payload["input"]["sha256"], subject.INPUT_SHA256)
            self.assertEqual(payload["operation"]["replacement_count"], 1)
            self.assertEqual(payload["operation"]["inline_reuse_count"], 2)

    def test_existing_output_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            output_root = Path(temporary) / "overlay"
            output_root.mkdir()
            with self.assertRaisesRegex(ValueError, "already exists"):
                subject.run(FLYSPECK_ROOT, output_root)


if __name__ == "__main__":
    unittest.main()
