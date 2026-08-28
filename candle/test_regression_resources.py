#!/usr/bin/env python3
"""Unit tests for process-tree resource sampling."""

import errno
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import regression


class _FakeFile:
    def __init__(self, result):
        self.result = result

    def read_text(self, encoding):
        del encoding
        if isinstance(self.result, BaseException):
            raise self.result
        return self.result


class _FakeEntry:
    def __init__(self, pid, files):
        self.name = str(pid)
        self.files = files

    def __truediv__(self, name):
        return _FakeFile(self.files[name])


class _FakeProc:
    def __init__(self, entries):
        self.entries = entries

    def iterdir(self):
        return iter(self.entries)


class ProcessTreeSamplerTest(unittest.TestCase):
    def test_explicit_log_directory_is_created_and_used(self):
        with tempfile.TemporaryDirectory() as directory:
            log_dir = Path(directory) / "persistent-logs"
            logfile, log_path = regression._open_test_log(
                "100_target", log_dir)
            try:
                logfile.write("evidence\n")
            finally:
                logfile.close()
            path = Path(log_path)
            self.assertEqual(path.parent, log_dir.resolve())
            self.assertEqual(path.read_text(encoding="utf-8"), "evidence\n")

    def test_vanished_processes_are_an_ordinary_snapshot_race(self):
        vanished = ProcessLookupError(errno.ESRCH, "process vanished")
        entries = [
            _FakeEntry(101, {"stat": vanished}),
            _FakeEntry(102, {
                "stat": "102 (short lived) S 1 0 0",
                "statm": vanished,
            }),
            _FakeEntry(103, {
                "stat": "103 (live worker) S 7 0 0",
                "statm": "100 25 0 0",
            }),
        ]
        fake_proc = _FakeProc(entries)
        with mock.patch.object(regression, "Path", return_value=fake_proc):
            parents, rss = regression.ProcessTreeSampler._process_snapshot()

        page_kib = regression.os.sysconf("SC_PAGE_SIZE") // 1024
        self.assertEqual(parents, {103: 7})
        self.assertEqual(rss, {103: 25 * page_kib})


if __name__ == "__main__":
    unittest.main()
