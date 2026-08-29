#!/usr/bin/env python3
"""Tests for fail-closed Candle build-directory locking."""

from pathlib import Path
import tempfile
import unittest

import runtime_lock


class RuntimeLockTests(unittest.TestCase):
    def test_shared_lock_records_exact_directory_inode(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            build = root / "candle/build"
            build.mkdir(parents=True)
            lock = runtime_lock.acquire_build_lock(root)
            try:
                observed = build.stat()
                self.assertEqual(lock.record["object"], "directory_inode")
                self.assertEqual(lock.record["mode"], "shared")
                self.assertEqual(lock.record["device"], observed.st_dev)
                self.assertEqual(lock.record["inode"], observed.st_ino)
            finally:
                lock.close()

    def test_final_symlink_build_directory_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "candle").mkdir()
            target = root / "target"
            target.mkdir()
            (root / "candle/build").symlink_to(target)
            with self.assertRaises(runtime_lock.RuntimeLockError):
                runtime_lock.acquire_build_lock(root)

    def test_intermediate_symlink_candle_directory_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            target = root / "target"
            (target / "build").mkdir(parents=True)
            (root / "candle").symlink_to(target)
            with self.assertRaises(runtime_lock.RuntimeLockError):
                runtime_lock.acquire_build_lock(root)


if __name__ == "__main__":
    unittest.main()
