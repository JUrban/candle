#!/usr/bin/env python3

import copy
import json
import sys
import unittest
from pathlib import Path
from unittest import mock


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FLYSPECK_ROOT = Path("/project/worktrees/flyspeck-v13-source")
sys.path.insert(0, str(HERE))
import flyspeck_all_inventory_sources as subject  # noqa: E402


class AllInventorySourcePreparationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.descriptor_data = (ROOT / subject.DESCRIPTOR_RELATIVE).read_bytes()
        cls.manifest_data = (ROOT / subject.MANIFEST_RELATIVE).read_bytes()
        cls.normalization_data = (ROOT / subject.NORMALIZATION_RELATIVE).read_bytes()
        cls.descriptor = subject.decode_object(
            cls.descriptor_data, "test descriptor",
        )
        cls.manifest = subject.decode_object(cls.manifest_data, "test manifest")
        cls.plan, cls.files = subject.prepare_all_sources(ROOT, FLYSPECK_ROOT)

    def raw_sites(self):
        fields = {"kind", "line", "literal", "expression", "syntax_position"}
        sites = []
        for entry in self.plan["inputs"]:
            for action in entry["recognized_loader_actions"]:
                sites.append({
                    "input_index": entry["index"],
                    "source_key": entry["source_key"],
                    "source_action_index": action["source_action_index"],
                    **{key: value for key, value in action.items() if key in fields},
                })
        return sites

    def test_exact_all_400_source_only_contract(self) -> None:
        self.assertEqual(self.plan["input_count"], 400)
        self.assertEqual(len(self.plan["inputs"]), 400)
        self.assertEqual(len(self.files), 400)
        self.assertEqual(
            self.plan["effective_kind_counts"],
            {"exact-normalized": 18, "exact-original": 382},
        )
        self.assertFalse(self.plan["promotion_allowed"])
        self.assertFalse(self.plan["parser_run"])
        self.assertFalse(self.plan["runtime_execution"])
        self.assertIn("source-only", self.plan["claim"])
        self.assertIn("non-promotable", self.plan["claim"])
        self.assertIn("not a parser run", self.plan["claim"])

    def test_exact_loader_site_and_masking_contract(self) -> None:
        actions = self.plan["loader_actions"]
        self.assertEqual(actions["recognized_site_count"], 727)
        self.assertEqual(actions["masked_whole_line_count"], 721)
        self.assertEqual(actions["embedded_retained_count"], 6)
        self.assertEqual(actions["kind_counts"], subject.EXPECTED_ACTION_KIND_COUNTS)
        self.assertEqual(
            actions["ordered_site_sha256"], subject.EXPECTED_ACTION_SITE_SHA256,
        )
        handling = [
            action["handling"]
            for entry in self.plan["inputs"]
            for action in entry["recognized_loader_actions"]
        ]
        self.assertEqual(
            handling.count("masked-complete-whole-line-before-parser"), 721,
        )
        self.assertEqual(
            handling.count("retained-exactly-in-source-only-input"), 6,
        )
        self.assertTrue(all(
            not action["action_semantics_executed"]
            for entry in self.plan["inputs"]
            for action in entry["recognized_loader_actions"]
        ))
        remaining = [
            call
            for entry in self.plan["inputs"]
            for call in subject.scan_load_calls(
                self.files[entry["prepared_input"]["path"]]
            )
        ]
        self.assertEqual(len(remaining), 6)
        self.assertTrue(all(
            call["syntax_position"] == "embedded-expression"
            for call in remaining
        ))

    def test_prepared_paths_and_hashes_are_exact_ordered_and_unique(self) -> None:
        prepared = self.plan["prepared_inputs"]
        self.assertEqual(prepared["count"], 400)
        self.assertTrue(prepared["paths_unique"])
        self.assertTrue(prepared["sha256_unique"])
        self.assertEqual(
            prepared["ordered_path_sha256"], subject.EXPECTED_ORDERED_PATH_SHA256,
        )
        self.assertEqual(
            prepared["ordered_effective_sha256"],
            subject.EXPECTED_ORDERED_EFFECTIVE_SHA256,
        )
        self.assertEqual(
            prepared["ordered_prepared_sha256"],
            subject.EXPECTED_ORDERED_PREPARED_SHA256,
        )
        paths = [entry["prepared_input"]["path"] for entry in self.plan["inputs"]]
        hashes = [entry["prepared_input"]["sha256"] for entry in self.plan["inputs"]]
        self.assertEqual(paths, [f"inputs/{index:03d}.ml" for index in range(400)])
        self.assertEqual(len(paths), len(set(paths)))
        self.assertEqual(len(hashes), len(set(hashes)))
        self.assertEqual(set(paths), set(self.files))

    def test_original_and_normalized_identities_are_bound(self) -> None:
        normalized = [
            entry for entry in self.plan["inputs"]
            if entry["effective_kind"] == "exact-normalized"
        ]
        original = [
            entry for entry in self.plan["inputs"]
            if entry["effective_kind"] == "exact-original"
        ]
        self.assertEqual((len(original), len(normalized)), (382, 18))
        self.assertTrue(all(entry["normalization"] is None for entry in original))
        self.assertTrue(all(
            entry["normalization"]["contract_sha256"]
            == subject.EXPECTED_AUTHORITIES[
                subject.NORMALIZATION_RELATIVE.as_posix()
            ]["sha256"]
            for entry in normalized
        ))
        self.assertTrue(all(
            entry["effective_input"]["sha256"]
            == entry["normalization"]["normalized_sha256"]
            for entry in normalized
        ))

    def test_non_utf8_collect_geom_is_included_by_one_byte_scan(self) -> None:
        key = "flyspeck:text_formalization/leg/collect_geom.hl"
        self.assertEqual(self.plan["non_utf8_source_keys"], [key])
        entry = next(item for item in self.plan["inputs"] if item["source_key"] == key)
        self.assertEqual(entry["index"], 110)
        self.assertFalse(entry["utf8_decodable"])
        self.assertEqual(entry["lexical_scan_encoding"], "latin-1-one-byte-round-trip")
        source = (FLYSPECK_ROOT / entry["source"]["path"]).read_bytes()
        with self.assertRaises(UnicodeDecodeError):
            source.decode("utf-8")
        self.assertEqual(source.decode("latin-1").encode("latin-1"), source)
        self.assertEqual(len(subject.scan_load_calls(source)), 4)
        self.assertEqual(len(entry["recognized_loader_actions"]), 4)
        self.assertIn(entry["prepared_input"]["path"], self.files)
        self.assertEqual(
            subject.scan_load_calls(self.files[entry["prepared_input"]["path"]]),
            [],
        )

    def test_scanner_matches_reference_semantics_on_hostile_lexical_fixture(self) -> None:
        source = (
            b"let needs x = x;;\n"
            b'(* nested (* loads "ignored.ml";; *) comment *)\n'
            b'let text = "needs \\"ignored.ml\\";;";;\n'
            b'loads "once.ml";;\n'
            b'let f () = needs "retained.ml";;\n'
            b'#use "always.ml";;\n'
            b'let byte = "\x96";;\n'
        )
        self.assertEqual(subject.scan_load_calls(source), [
            {
                "kind": "loads", "line": 4, "literal": "once.ml",
                "syntax_position": "standalone-phrase",
            },
            {
                "kind": "needs", "line": 5, "literal": "retained.ml",
                "syntax_position": "embedded-expression",
            },
            {
                "kind": "#use", "line": 6, "literal": "always.ml",
                "syntax_position": "standalone-phrase",
            },
        ])

    def test_whole_line_mask_preserves_bytes_and_embedded_call(self) -> None:
        source = b'loads "dep.ml";; (* comment *)\nlet f () = needs "x.ml";;\n'
        calls = subject.scan_load_calls(source)
        prepared, actions = subject._mask_effective_source("fixture", source, calls)
        self.assertEqual(len(prepared), len(source))
        self.assertEqual(prepared.count(b"\n"), source.count(b"\n"))
        self.assertEqual(
            prepared.split(b"\n", 1)[0], b" " * len(source.split(b"\n", 1)[0]),
        )
        self.assertIn(b'needs "x.ml"', prepared)
        self.assertEqual(subject.scan_load_calls(prepared), [calls[1]])
        self.assertEqual(
            [action["handling"] for action in actions],
            [
                "masked-complete-whole-line-before-parser",
                "retained-exactly-in-source-only-input",
            ],
        )

    def test_descriptor_drift_fails_before_source_reads(self) -> None:
        altered = self.descriptor_data.replace(b'"schema": 1', b'"schema": 2', 1)
        with mock.patch.object(subject, "_read_source") as read_source:
            with self.assertRaisesRegex(subject.ContractError, "authority drift"):
                subject.prepare_all_sources(
                    ROOT, FLYSPECK_ROOT, descriptor_data=altered,
                )
        read_source.assert_not_called()

    def test_normalization_contract_drift_fails_before_source_reads(self) -> None:
        altered = self.normalization_data.replace(b'"schema": 2', b'"schema": 1', 1)
        with mock.patch.object(subject, "_read_source") as read_source:
            with self.assertRaisesRegex(subject.ContractError, "authority drift"):
                subject.prepare_all_sources(
                    ROOT, FLYSPECK_ROOT, normalization_data=altered,
                )
        read_source.assert_not_called()

    def test_original_source_drift_fails_closed(self) -> None:
        original_read = subject._read_source

        def drift(path, label):
            data = original_read(path, label)
            return data + b"drift" if label == "candle:hol.ml" else data

        with mock.patch.object(subject, "_read_source", side_effect=drift):
            with self.assertRaisesRegex(subject.ContractError, "source identity drift"):
                subject.prepare_all_sources(ROOT, FLYSPECK_ROOT)

    def test_descriptor_count_and_boolean_types_fail_closed(self) -> None:
        altered = copy.deepcopy(self.descriptor)
        altered["selection"]["inventory_source_count"] = True
        with self.assertRaisesRegex(subject.ContractError, "count/type drift"):
            subject._validate_descriptor(altered, self.manifest, self.manifest_data)
        altered = copy.deepcopy(self.descriptor)
        altered["inputs"][0]["index"] = False
        with self.assertRaisesRegex(subject.ContractError, "index/type/order drift"):
            subject._validate_descriptor(altered, self.manifest, self.manifest_data)

    def test_descriptor_duplicate_and_reorder_fail_closed(self) -> None:
        duplicate = copy.deepcopy(self.descriptor)
        duplicate["inputs"][1] = copy.deepcopy(duplicate["inputs"][0])
        duplicate["inputs"][1]["index"] = 1
        with self.assertRaisesRegex(subject.ContractError, "duplicate descriptor source"):
            subject._validate_descriptor(duplicate, self.manifest, self.manifest_data)
        reordered = copy.deepcopy(self.descriptor)
        reordered["inputs"][0], reordered["inputs"][1] = (
            reordered["inputs"][1], reordered["inputs"][0],
        )
        reordered["inputs"][0]["index"] = 0
        reordered["inputs"][1]["index"] = 1
        with self.assertRaisesRegex(subject.ContractError, "ordered source-key digest drift"):
            subject._validate_descriptor(reordered, self.manifest, self.manifest_data)

    def test_manifest_normalization_digest_drift_fails_closed(self) -> None:
        altered = copy.deepcopy(self.manifest)
        altered["source_normalization_contract"]["contract_sha256"] = "0" * 64
        with self.assertRaisesRegex(subject.ContractError, "contract digest drift"):
            subject._normalizations(altered, self.normalization_data)

    def test_action_count_kind_and_order_drift_fail_closed(self) -> None:
        sites = self.raw_sites()
        subject._validate_action_inventory(sites)
        with self.assertRaisesRegex(subject.ContractError, "action count drift"):
            subject._validate_action_inventory(sites[:-1])
        altered = copy.deepcopy(sites)
        altered[0]["kind"] = "needs"
        with self.assertRaisesRegex(subject.ContractError, "kind count drift"):
            subject._validate_action_inventory(altered)
        reordered = copy.deepcopy(sites)
        reordered[0], reordered[1] = reordered[1], reordered[0]
        with self.assertRaisesRegex(subject.ContractError, "site/order drift"):
            subject._validate_action_inventory(reordered)

    def test_masking_line_drift_fails_closed(self) -> None:
        source = b'loads "dep.ml";;\n'
        calls = subject.scan_load_calls(source)
        calls[0]["line"] = True
        with self.assertRaisesRegex(subject.ContractError, "line out of range"):
            subject._mask_effective_source("fixture", source, calls)
        calls = subject.scan_load_calls(source)
        calls[0]["literal"] = "other.ml"
        with self.assertRaisesRegex(subject.ContractError, "literal/line drift"):
            subject._mask_effective_source("fixture", source, calls)
        trailing = b'loads "dep.ml";; let unexpected = 1;;\n'
        with self.assertRaisesRegex(subject.ContractError, "complete line phrase"):
            subject._mask_effective_source(
                "fixture", trailing, subject.scan_load_calls(trailing),
            )

    def test_utf8_omission_and_input_count_drift_fail_closed(self) -> None:
        altered = copy.deepcopy(self.descriptor)
        altered["inputs"] = [
            entry for entry in altered["inputs"]
            if entry["source_key"]
            != "flyspeck:text_formalization/leg/collect_geom.hl"
        ]
        with self.assertRaisesRegex(subject.ContractError, "source count/type drift"):
            subject._validate_descriptor(altered, self.manifest, self.manifest_data)


if __name__ == "__main__":
    unittest.main()
