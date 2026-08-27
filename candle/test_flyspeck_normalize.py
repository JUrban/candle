import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path

import flyspeck_normalize


def digests(data: bytes) -> tuple[str, str]:
    return (
        hashlib.sha256(data).hexdigest(),
        hashlib.md5(data, usedforsecurity=False).hexdigest(),
    )


class FlyspeckNormalizationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.contract_path = Path(__file__).with_name(
            flyspeck_normalize.CONTRACT_NAME
        )
        cls.contract = flyspeck_normalize.load_contract(cls.contract_path)

    def fixture_entry(self) -> tuple[dict, bytes, bytes]:
        source = b"prefix\n    if n == 1 then [] else\nsuffix\n"
        normalized = b"prefix\n    if n = 1 then [] else\nsuffix\n"
        entry = copy.deepcopy(self.contract["entries"][0])
        entry["operations"][0]["line"] = 2
        entry["source_sha256"], entry["source_md5"] = digests(source)
        entry["normalized_sha256"], entry["normalized_md5"] = digests(normalized)
        entry["normalized_bytes"] = len(normalized)
        return entry, source, normalized

    def test_exact_once_normalization(self):
        entry, source, normalized = self.fixture_entry()
        self.assertEqual(
            flyspeck_normalize.normalize_bytes(source, entry), normalized,
        )

    def test_source_drift_fails_closed(self):
        entry, source, _ = self.fixture_entry()
        with self.assertRaisesRegex(ValueError, "source digest mismatch"):
            flyspeck_normalize.normalize_bytes(source + b"drift", entry)

    def test_ambiguous_anchor_fails_closed(self):
        entry, source, _ = self.fixture_entry()
        doubled = source + source
        entry["source_sha256"], entry["source_md5"] = digests(doubled)
        with self.assertRaisesRegex(ValueError, "anchor count is not one"):
            flyspeck_normalize.normalize_bytes(doubled, entry)

    def test_ordered_operations_are_not_commuted(self):
        entry, _, _ = self.fixture_entry()
        source = b"a\nb\n"
        normalized = b"c\nb\n"
        entry["operations"] = [
            {
                "id": "fixture-first",
                "kind": "exact_bytes_replace_once",
                "line": 1,
                "before": "a\n",
                "after": "b\n",
            },
            {
                "id": "fixture-second",
                "kind": "exact_bytes_replace_once",
                "line": 2,
                "before": "b\n",
                "after": "c\n",
            },
        ]
        entry["source_sha256"], entry["source_md5"] = digests(source)
        entry["normalized_sha256"], entry["normalized_md5"] = digests(normalized)
        entry["normalized_bytes"] = len(normalized)
        with self.assertRaisesRegex(ValueError, "anchor count is not one"):
            flyspeck_normalize.normalize_bytes(source, entry)

    def test_source_line_drift_fails_closed(self):
        entry, source, _ = self.fixture_entry()
        entry["operations"][0]["line"] += 1
        with self.assertRaisesRegex(ValueError, "source line mismatch"):
            flyspeck_normalize.normalize_bytes(source, entry)

    def test_output_digest_fails_closed(self):
        entry, source, _ = self.fixture_entry()
        entry["normalized_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "normalized digest mismatch"):
            flyspeck_normalize.normalize_bytes(source, entry)

    def test_contract_is_narrow_and_auditable(self):
        self.assertEqual(self.contract["schema"], 2)
        self.assertEqual(len(self.contract["entries"]), 10)
        entries = {entry["id"]: entry for entry in self.contract["entries"]}
        immediate = entries["PROJECT-POINTER-S3-IMMEDIATE-001"]
        self.assertEqual(immediate["operations"][0]["line"], 1050)
        self.assertEqual(immediate["operations"][0]["before"].count("=="), 1)
        self.assertNotIn("==", immediate["operations"][0]["after"])
        self.assertIn("does not apply to allocated values", immediate["scope_limit"])
        allocated = entries["PROJECT-POINTER-S3-ALLOCATED-LIB-001"]
        self.assertEqual(len(allocated["operations"]), 5)
        self.assertIn("qmap is a selected-graph non-use", allocated["scope_limit"])
        unsuppress = entries["PROJECT-POINTER-S3-UNSUPPRESS-001"]
        self.assertIn("failwith", unsuppress["operations"][0]["after"])
        relabel = entries["PROJECT-POINTER-S3-RELABEL-001"]
        self.assertIn("not (y = x)", relabel["operations"][0]["after"])
        set_make = entries["PROJECT-MODULE-S3-SET-MAKE-001"]
        self.assertEqual(set_make["operations"][0]["line"], 34)
        self.assertIn("type t = string list", set_make["operations"][0]["after"])
        self.assertNotIn("Set.Make", set_make["operations"][0]["after"])
        self.assertIn("only through empty, add, and mem", set_make["semantic_rule"])
        strictbuild = entries["PROJECT-TOPLOOP-S3-USE-FILE-B-001"]
        self.assertIn("dynamic use_file_b is disabled", (
            strictbuild["operations"][0]["after"]
        ))
        self.assertNotIn("Toploop", strictbuild["operations"][0]["after"])
        self.assertIn("#flyspeck_loadt", strictbuild["operations"][1]["after"])
        self.assertIn("dynamic strictbuild needs is disabled", (
            strictbuild["operations"][2]["after"]
        ))
        self.assertIn("#flyspeck_loadt", strictbuild["operations"][3]["after"])
        self.assertIn("dynamic strictbuild reneeds is disabled", (
            strictbuild["operations"][4]["after"]
        ))
        parser_orpattern = entries["PROJECT-PARSER-S3-LET-OR-PATTERN-001"]
        self.assertEqual(
            [operation["line"] for operation in parser_orpattern["operations"]],
            [36, 86],
        )
        self.assertIn("string_of_num n", (
            parser_orpattern["operations"][0]["after"]
        ))
        self.assertIn("match opname with", (
            parser_orpattern["operations"][1]["after"]
        ))
        self.assertNotIn("Varp((\"=\"|\"<=>\")", (
            parser_orpattern["operations"][1]["after"]
        ))
        trailing_semi = entries["PROJECT-PARSER-S3-TRAILING-SEMI-001"]
        self.assertEqual(trailing_semi["operations"][0]["line"], 22)
        self.assertIn('print_string "\\n");;', (
            trailing_semi["operations"][0]["after"]
        ))
        shell_free = entries["PROJECT-FFI-S3-LP-SHELL-ELIMINATION-001"]
        self.assertEqual(
            [operation["line"] for operation in shell_free["operations"]],
            [88, 124],
        )
        self.assertNotIn("Sys.command", "".join(
            operation["after"] for operation in shell_free["operations"]
        ))
        self.assertIn("fails closed", shell_free["scope_limit"])
        static_inventory = entries["PROJECT-FFI-S3-LP-STATIC-INVENTORY-001"]
        self.assertEqual(static_inventory["operations"][0]["line"], 10)
        self.assertIn("candle_flyspeck_lp_certificate_files", (
            static_inventory["operations"][0]["after"]
        ))
        self.assertNotIn("Sys.readdir", (
            static_inventory["operations"][0]["after"]
        ))
        operation_ids = [
            operation["id"]
            for entry in entries.values()
            for operation in entry["operations"]
        ]
        self.assertEqual(len(operation_ids), 20)
        self.assertEqual(len(operation_ids), len(set(operation_ids)))

    def test_materialized_receipt_is_deterministic(self):
        entry, source, normalized = self.fixture_entry()
        contract = copy.deepcopy(self.contract)
        contract["flyspeck_commit"] = "a" * 40
        contract["entries"] = [entry]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source_root = root / "source"
            output_root = root / "output"
            source_path = source_root / entry["path"]
            source_path.parent.mkdir(parents=True)
            source_path.write_bytes(source)
            contract_path = root / "contract.json"
            contract_path.write_text(
                json.dumps(contract, indent=2) + "\n", encoding="utf-8",
            )
            original_git_head = flyspeck_normalize._git_head
            flyspeck_normalize._git_head = lambda _: "a" * 40
            try:
                first = flyspeck_normalize.materialize(
                    contract_path, source_root, output_root,
                )
                second = flyspeck_normalize.materialize(
                    contract_path, source_root, output_root,
                )
            finally:
                flyspeck_normalize._git_head = original_git_head
            self.assertEqual(first, second)
            self.assertEqual((output_root / entry["path"]).read_bytes(), normalized)
            receipt = json.loads(
                (output_root / flyspeck_normalize.RECEIPT_NAME).read_text()
            )
            self.assertEqual(receipt, first)

    def test_materialization_cannot_overwrite_pinned_source(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with self.assertRaisesRegex(ValueError, "output must be separate"):
                flyspeck_normalize.materialize(
                    self.contract_path, root, root,
                )

    def test_materialization_refuses_parent_symlink(self):
        entry, source, _ = self.fixture_entry()
        contract = copy.deepcopy(self.contract)
        contract["flyspeck_commit"] = "a" * 40
        contract["entries"] = [entry]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source_root = root / "source"
            output_root = root / "output"
            source_path = source_root / entry["path"]
            source_path.parent.mkdir(parents=True)
            source_path.write_bytes(source)
            output_root.mkdir()
            first_component = Path(entry["path"]).parts[0]
            (output_root / first_component).symlink_to(
                source_root / first_component, target_is_directory=True,
            )
            contract_path = root / "contract.json"
            contract_path.write_text(
                json.dumps(contract, indent=2) + "\n", encoding="utf-8",
            )
            original_git_head = flyspeck_normalize._git_head
            flyspeck_normalize._git_head = lambda _: "a" * 40
            try:
                with self.assertRaisesRegex(ValueError, "output symlink"):
                    flyspeck_normalize.materialize(
                        contract_path, source_root, output_root,
                    )
            finally:
                flyspeck_normalize._git_head = original_git_head


if __name__ == "__main__":
    unittest.main()
