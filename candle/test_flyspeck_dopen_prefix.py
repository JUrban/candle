#!/usr/bin/env python3

import hashlib
import tempfile
import unittest
from pathlib import Path

import flyspeck_dopen_prefix as subject


class DopenPrefixTests(unittest.TestCase):
    def test_extracts_exact_ordered_prefix(self) -> None:
        source = (
            b"before\n" + subject.PARSER_ACTION + b"\nmiddle\n" +
            subject.DEBUG_ACTION + b"\nafter\n"
        )
        prefix = subject.extract_strictbuild_prefix(source)
        self.assertEqual(prefix, source[:source.index(subject.DEBUG_ACTION) + len(subject.DEBUG_ACTION)] + b"\n")
        self.assertNotIn(b"after", prefix)

    def test_rejects_action_order_drift(self) -> None:
        source = subject.DEBUG_ACTION + b"\n" + subject.PARSER_ACTION
        with self.assertRaisesRegex(subject.ContractError, "order drift"):
            subject.extract_strictbuild_prefix(source)

    def test_rejects_full_driver_in_prefix(self) -> None:
        source = (
            subject.PARSER_ACTION + b"\n#flyspeck_needs \"x\";;\n" +
            subject.DEBUG_ACTION
        )
        with self.assertRaisesRegex(subject.ContractError, "297-entry"):
            subject.extract_strictbuild_prefix(source)

    def test_record_hash_validation_is_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "source.hl"
            path.write_bytes(b"source")
            record = {
                "bytes": 6,
                "sha256": hashlib.sha256(b"source").hexdigest(),
                "md5": hashlib.md5(b"source", usedforsecurity=False).hexdigest(),
            }
            self.assertEqual(subject.validate_record(path, record, "test"), record["md5"])
            record["sha256"] = "0" * 64
            with self.assertRaisesRegex(subject.ContractError, "SHA-256 mismatch"):
                subject.validate_record(path, record, "test")


if __name__ == "__main__":
    unittest.main()
