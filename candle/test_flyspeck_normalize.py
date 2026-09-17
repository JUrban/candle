import copy
import hashlib
import json
import os
import tempfile
import unittest
from unittest import mock
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
        pointer_operation = next(
            operation for operation in entry["operations"]
            if operation["id"] == "PROJECT-POINTER-S3-IMMEDIATE-001-REPLACE"
        )
        entry["operations"] = [copy.deepcopy(pointer_operation)]
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

    def test_exact_span_normalization_and_span_drift(self):
        source = b"prefix\nSTART\ninside\nEND\nsuffix\n"
        normalized = b"prefix\nreplacement\nsuffix\n"
        entry = copy.deepcopy(self.contract["entries"][0])
        span = b"START\ninside\nEND\n"
        entry["operations"] = [{
            "id": "fixture-span",
            "kind": "exact_span_replace_once",
            "line": 2,
            "end_line": 4,
            "start": "START\n",
            "end": "END\n",
            "span_sha256": hashlib.sha256(span).hexdigest(),
            "after": "replacement\n",
        }]
        entry["source_sha256"], entry["source_md5"] = digests(source)
        entry["normalized_sha256"], entry["normalized_md5"] = digests(normalized)
        entry["normalized_bytes"] = len(normalized)
        self.assertEqual(flyspeck_normalize.normalize_bytes(source, entry), normalized)
        entry["operations"][0]["span_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "source span digest mismatch"):
            flyspeck_normalize.normalize_bytes(source, entry)

    def test_exact_ocaml_global_thunk_list_preserves_order_and_fails_closed(self):
        source = (
            b"module M = struct\n\nlet xs = [\n"
            b'(\"a\",0);\n\n(\"b\",1);\n\n(\"c\",2)\n];;\n\nend;;'
        )
        normalized = (
            b"let candle_test_chunks () = [\n(\"c\",2)\n];;\n\n"
            b"let candle_test_chunks () = [\n"
            b'(\"a\",0);\n\n(\"b\",1)\n] @ candle_test_chunks ();;\n\n'
            b"module M = struct\n\n"
            b"let xs = candle_test_chunks ();;\n\nend;;"
        )
        entry = copy.deepcopy(self.contract["entries"][0])
        entry["operations"] = [{
            "id": "fixture-global-thunk-list",
            "kind": "exact_ocaml_global_thunk_list",
            "line": 1,
            "module_prefix": "module M = struct\n\n",
            "module_suffix": "end;;",
            "binding_name": "xs",
            "accumulator_name": "candle_test_chunks",
            "item_separator": ";\n\n",
            "item_prefix": "(\"",
            "entry_count": 3,
            "chunk_size": 2,
            "chunk_count": 2,
        }]
        entry["source_sha256"], entry["source_md5"] = digests(source)
        entry["normalized_sha256"], entry["normalized_md5"] = digests(normalized)
        entry["normalized_bytes"] = len(normalized)
        self.assertEqual(
            flyspeck_normalize.normalize_bytes(source, entry), normalized,
        )
        entry["operations"][0]["entry_count"] = 4
        entry["operations"][0]["chunk_count"] = 2
        with self.assertRaisesRegex(ValueError, "exact list entry count mismatch"):
            flyspeck_normalize.normalize_bytes(source, entry)
        entry["operations"][0]["accumulator_name"] = "Bad.name"
        with self.assertRaisesRegex(ValueError, "invalid exact OCaml global thunk"):
            flyspeck_normalize.load_contract_bytes(json.dumps({
                "schema": 2,
                "flyspeck_commit": "a" * 40,
                "entries": [entry],
            }).encode())

    def test_exact_line_batch_preserves_order_and_fails_closed(self):
        source = b"module M = struct\nemit 1;;\nemit 2;;\nend;;\n"
        normalized = (
            b"module M = struct\nlet _ = emit 1;;\n"
            b"let _ = emit 2;;\nend;;\n"
        )
        entry = copy.deepcopy(self.contract["entries"][0])
        entry["operations"] = [{
            "id": "fixture-exact-lines",
            "kind": "exact_lines_replace_once",
            "line": 2,
            "replacement_count": 2,
            "replacements": [
                {"line": 2, "before": "emit 1;;", "after": "let _ = emit 1;;"},
                {"line": 3, "before": "emit 2;;", "after": "let _ = emit 2;;"},
            ],
        }]
        entry["source_sha256"], entry["source_md5"] = digests(source)
        entry["normalized_sha256"], entry["normalized_md5"] = digests(normalized)
        entry["normalized_bytes"] = len(normalized)
        self.assertEqual(
            flyspeck_normalize.normalize_bytes(source, entry), normalized,
        )
        entry["operations"][0]["replacements"][1]["before"] = "emit 3;;"
        with self.assertRaisesRegex(ValueError, "source line anchor mismatch"):
            flyspeck_normalize.normalize_bytes(source, entry)

        duplicate = copy.deepcopy(entry)
        duplicate["operations"][0]["replacements"][1]["line"] = 2
        with self.assertRaisesRegex(ValueError, "invalid exact line replacement order"):
            flyspeck_normalize.load_contract_bytes(json.dumps({
                "schema": 2,
                "flyspeck_commit": "a" * 40,
                "entries": [duplicate],
            }).encode())

    def test_output_digest_fails_closed(self):
        entry, source, _ = self.fixture_entry()
        entry["normalized_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "normalized digest mismatch"):
            flyspeck_normalize.normalize_bytes(source, entry)

    def test_contract_is_narrow_and_auditable(self):
        self.assertEqual(self.contract["schema"], 2)
        self.assertEqual(len(self.contract["entries"]), 52)
        entries = {entry["id"]: entry for entry in self.contract["entries"]}
        retired_frontend_entries = {
            "PROJECT-ADD-TRIANGLE-S2-STRUCTURE-EFFECTS-001",
            "PROJECT-COLLECT-GEOM-S3-STRUCTURE-EFFECT-001",
            "PROJECT-COLLECT-GEOM2-S3-STRUCTURE-EFFECT-001",
            "PROJECT-DIH2K-S2-STRUCTURE-EFFECT-001",
            "PROJECT-FAN-S2-STRUCTURE-EFFECT-001",
            "PROJECT-GOAL-PRINTER-S3-STRUCTURE-EFFECT-001",
            "PROJECT-GRUTOTI-S2-NATIVE-SET-SCOPE-001",
            "PROJECT-HYPERMAP-ISO-S2-STRUCTURE-EFFECTS-001",
            "PROJECT-HYPERMAP-S2-STRUCTURE-EFFECT-001",
            "PROJECT-INEQUALITIES-S2-GOAL-EFFECT-001",
            "PROJECT-LOCAL-LEMMAS-S2-STRUCTURE-EFFECT-001",
            "PROJECT-LOCAL-LEMMAS1-S2-STRUCTURE-EFFECT-001",
            "PROJECT-LOCALIZATION-S2-STRUCTURE-EFFECT-001",
            "PROJECT-NKEZBFC-S2-GOAL-EFFECT-001",
            "PROJECT-NUM-EXT-NABS-S3-STRUCTURE-EFFECT-001",
            "PROJECT-OXLZLEZ3-S2-STRUCTURE-EFFECT-001",
            "PROJECT-POLYHEDRON-S2-STRUCTURE-EFFECT-001",
            "PROJECT-REAL-EXT-S3-STRUCTURE-EFFECT-001",
            "PROJECT-REFINEMENT-S3-FOR-LOOP-001",
            "PROJECT-SEQ-S2-STRUCTURE-EFFECTS-001",
            "PROJECT-SEQ2-S2-STRUCTURE-EFFECTS-001",
            "PROJECT-SORT-S2-STRUCTURE-EFFECTS-001",
            "PROJECT-SSRBOOL-S2-STRUCTURE-EFFECTS-001",
            "PROJECT-SSRFUN-S2-STRUCTURE-EFFECTS-001",
            "PROJECT-SSRNAT-S2-STRUCTURE-EFFECTS-001",
            "PROJECT-TACTICS-S3-STRUCTURE-EFFECT-001",
            "PROJECT-TAME-LEMMAS-S2-STRUCTURE-EFFECTS-001",
            "PROJECT-TAYLOR-ATN-S3-STRUCTURE-EFFECT-001",
            "PROJECT-TRIG1-S3-STRUCTURE-EFFECT-001",
            "PROJECT-TRIG2-S3-STRUCTURE-EFFECT-001",
            "PROJECT-TSKAJXY2-S2-GOAL-EFFECT-001",
            "PROJECT-VOL1-S2-STRUCTURE-EFFECT-001",
            "PROJECT-WRGCVDR-S2-STRUCTURE-EFFECT-001",
        }
        self.assertTrue(retired_frontend_entries.isdisjoint(entries))
        operation_ids = {
            operation["id"]
            for entry in entries.values()
            for operation in entry["operations"]
        }
        self.assertFalse(any(
            "STRUCTURE-EFFECT" in operation_id
            or "GOAL-EFFECT" in operation_id
            for operation_id in operation_ids
        ))
        self.assertTrue({
            "PROJECT-REFINEMENT-S3-FOR-LOOP-001-LABEL-ALL",
            "PROJECT-INEQ-S3-PRINTF-FLATTEN-LOOPS-001-F4-ITERATION",
            "PROJECT-INEQ-S3-PRINTF-FLATTEN-LOOPS-001-QITNPEA1-ITERATION",
            "PROJECT-MAIN-ESTIMATE-INEQ-S3-PRINTF-LOOP-001-HEX-ITERATION",
        }.isdisjoint(operation_ids))
        for entry_id, expected_line in (
            ("PROJECT-EMNWUUS-S2-TERM-SETIFY-001", 50),
            ("PROJECT-OXLZLEZ2-S2-TERM-SETIFY-001", 117),
            ("PROJECT-SLTSTLO-S2-TERM-SETIFY-001", 27),
        ):
            entry = entries[entry_id]
            self.assertEqual(len(entry["operations"]), 1)
            self.assertEqual(entry["operations"][0]["line"], expected_line)
            self.assertEqual(
                entry["operations"][0]["after"],
                "let vs = setify Term.(<) (flat vss) in",
            )
            self.assertIn("flattened from map frees", entry["semantic_rule"])
            self.assertIn("unique unary setify", entry["scope_limit"])
        ajripqn = entries["PROJECT-AJRIPQN-S2-OPEN-RESOLUTION-001"]
        self.assertEqual(
            [operation["line"] for operation in ajripqn["operations"]],
            [137, 333, 626],
        )
        self.assertEqual(
            ajripqn["operations"][0]["before"],
            "(MATCH_MP_TAC KIUMVTC);",
        )
        self.assertEqual(
            ajripqn["operations"][0]["after"],
            "(MATCH_MP_TAC Pack1.KIUMVTC);",
        )
        marchal3 = entries[
            "PROJECT-MARCHAL3-S2-COMPATIBILITY-004"
        ]
        self.assertEqual(
            [operation["line"] for operation in marchal3["operations"]],
            [5085, 5196, 5325, 40, 43, 3869, 3878, 3887, 3896, 3905, 3914, 4127],
        )
        card_permutation = marchal3["operations"][0]
        self.assertEqual(card_permutation["kind"], "exact_lines_replace_once")
        self.assertEqual(card_permutation["replacement_count"], 2)
        self.assertEqual(
            [replacement["line"] for replacement in card_permutation["replacements"]],
            [5085, 5308],
        )
        self.assertTrue(all(
            replacement["before"] == " (AP_TERM_TAC THEN SET_TAC[]);"
            and replacement["after"] ==
            " (REWRITE_TAC[SET_RULE `{w0,w1,w2,w3:real^3} = "
            "{w3,w0,w1,w2}`]);"
            for replacement in card_permutation["replacements"]
        ))
        selected_members = marchal3["operations"][1]
        self.assertEqual(selected_members["kind"], "exact_lines_replace_once")
        self.assertEqual(selected_members["replacement_count"], 4)
        self.assertEqual(
            [replacement["line"] for replacement in selected_members["replacements"]],
            [5196, 5197, 5422, 5423],
        )
        self.assertTrue(all(
            selected_members["replacements"][index]["before"] ==
            " (UP_ASM_TAC THEN UP_ASM_TAC THEN UP_ASM_TAC THEN "
            "UP_ASM_TAC THEN "
            and selected_members["replacements"][index]["after"] ==
            " (MATCH_MP_TAC FOUR_SELECTED_MEMBERS_EXHAUST THEN "
            "ASM_REWRITE_TAC[]);"
            for index in (0, 2)
        ))
        self.assertTrue(all(
            selected_members["replacements"][index]["before"] ==
            "   UP_ASM_TAC THEN SET_TAC[]);"
            and selected_members["replacements"][index]["after"] == ""
            for index in (1, 3)
        ))
        set_swaps = marchal3["operations"][2]
        self.assertEqual(set_swaps["kind"], "exact_lines_replace_once")
        self.assertEqual(set_swaps["replacement_count"], 2)
        self.assertEqual(
            [replacement["line"] for replacement in set_swaps["replacements"]],
            [5325, 5426],
        )
        self.assertEqual(
            set_swaps["replacements"][0]["before"],
            " (SET_TAC[]);",
        )
        self.assertEqual(
            set_swaps["replacements"][0]["after"],
            " (REWRITE_TAC[SET_RULE `{u,v,a:real^3} = {v,u,a}`]);",
        )
        self.assertEqual(
            set_swaps["replacements"][1]["after"],
            " (REWRITE_TAC[SET_RULE `{u,v,a,b:real^3} = {v,u,a,b}`]);",
        )
        self.assertEqual(
            marchal3["operations"][3]["before"],
            "open Upfzbzm_support_lemmas;;",
        )
        self.assertEqual(
            marchal3["operations"][3]["after"],
            "open Upfzbzm_support_lemmas;;\n\n"
            "let prove_by_refinement = "
            "Prove_by_refinement.prove_by_refinement;;",
        )
        selected_helper = marchal3["operations"][4]
        self.assertEqual(
            selected_helper["before"],
            "let TAKE_TAC = UP_ASM_TAC THEN REPEAT STRIP_TAC;;",
        )
        self.assertIn("let FOUR_SELECTED_MEMBERS_EXHAUST = prove", selected_helper["after"])
        self.assertIn("REPEAT(FIRST_X_ASSUM DISJ_CASES_TAC)", selected_helper["after"])
        self.assertTrue(all(
            "ONCE_REWRITE_TAC[GSYM (ASSUME" in operation["after"]
            and "SUBST1_TAC (ASSUME" in operation["after"]
            and "REWRITE_TAC[INSERT_AC]" in operation["after"]
            for operation in marchal3["operations"][5:11]
        ))
        self.assertEqual(
            marchal3["operations"][-1]["after"],
            "(REWRITE_TAC[MATCH_MP PERMUTES_INVERSE_EQ\n"
            "   (ASSUME `p permutes 0..3`)] THEN ASM_REWRITE_TAC[]);",
        )
        self.assertIn("Native OCaml", marchal3["semantic_rule"])
        self.assertIn("identical three-element set goal", marchal3["semantic_rule"])
        self.assertIn("FOUR_SELECTED_MEMBERS_EXHAUST", marchal3["semantic_rule"])
        self.assertIn("seventeen mechanically enumerated", marchal3["scope_limit"])
        self.assertIn("two identical cardinality", marchal3["scope_limit"])
        self.assertIn("two paired four-selected-member", marchal3["scope_limit"])
        self.assertIn("two context-free set swaps", marchal3["scope_limit"])
        self.assertIn("earlier three-index inverse proof", marchal3["scope_limit"])
        self.assertTrue(all(
            "Pack1.KIUMVTC" in operation["after"]
            for operation in ajripqn["operations"]
        ))
        self.assertIn("native OCaml", ajripqn["semantic_rule"])
        self.assertIn("do not whitelist a basename", ajripqn["scope_limit"])
        ssreflect = entries["PROJECT-TOPLOOP-S3-SSREFLECT-LOOKUP-001"]
        self.assertEqual(
            [operation["line"] for operation in ssreflect["operations"]],
            [721, 60, 69, 115, 622, 889, 904],
        )
        self.assertIn(
            "compose_insts insts2 i",
            ssreflect["operations"][1]["after"],
        )
        self.assertIn(
            "map (inst_goal insts2) gls1",
            ssreflect["operations"][2]["after"],
        )
        self.assertEqual(
            ssreflect["operations"][3]["after"],
            "let f_vars = setify Term.(<) (flat (map frees tms)) in",
        )
        self.assertEqual(
            ssreflect["operations"][4]["after"],
            "\t\t   ((head1 @ tail), th0)",
        )
        self.assertEqual(
            ssreflect["operations"][5]["after"],
            "let cases_table : (string, thm) Hashtbl.t = Hashtbl.create 10;;",
        )
        self.assertEqual(
            ssreflect["operations"][6]["after"],
            "let elim_table : (string, thm) Hashtbl.t = Hashtbl.create 10;;",
        )
        self.assertIn("native OCaml grouping", ssreflect["semantic_rule"])
        self.assertIn("top-level value restriction", ssreflect["semantic_rule"])
        self.assertIn("current HOL Light", ssreflect["semantic_rule"])
        fnjlbxs = entries["PROJECT-FNJLBXS-S2-STRUCTURE-EFFECTS-001"]
        self.assertEqual(len(fnjlbxs["operations"]), 3)
        fnjlbxs_proofs = fnjlbxs["operations"]
        self.assertEqual(
            [operation["id"] for operation in fnjlbxs_proofs],
            [
                "PROJECT-FNJLBXS-S2-REALLIM-ADD-APPLY-001",
                "PROJECT-FNJLBXS-S2-MIN-K-CONTINUOUS-REWRITE-001",
                "PROJECT-FNJLBXS-S2-MIN-K-LIMIT-REWRITE-001",
            ],
        )
        self.assertEqual(
            [operation["line"] for operation in fnjlbxs_proofs],
            [52, 93, 117],
        )
        self.assertTrue(all(
            operation["kind"] == "exact_lines_replace_once" and
            operation["replacement_count"] == 1 and
            len(operation["replacements"]) == 1
            for operation in fnjlbxs_proofs
        ))
        self.assertIn("same REALLIM_ADD theorem", fnjlbxs["semantic_rule"])
        self.assertIn("same named definitions", fnjlbxs["semantic_rule"])
        self.assertIn("three independently minimized", fnjlbxs["scope_limit"])
        pent_hex = entries["PROJECT-PENT-HEX-S2-PRINTF-001"]
        self.assertEqual(
            [operation["line"] for operation in pent_hex["operations"]],
            [2697, 2875, 2908],
        )
        self.assertEqual(
            [operation["kind"] for operation in pent_hex["operations"]],
            ["exact_bytes_replace_once"] * 3,
        )
        self.assertEqual(sum(
            "Printf.sprintf" in operation["before"]
            for operation in pent_hex["operations"]
        ), 3)
        self.assertTrue(all(
            "Printf.sprintf" not in operation["after"]
            and operation["after"].count("string_of_int") == 3
            for operation in pent_hex["operations"]
        ))
        self.assertIn("complete mechanically enumerated", pent_hex["scope_limit"])
        self.assertIn("no pent_hex source or patch", pent_hex["scope_limit"])
        misc_functions = entries[
            "PROJECT-MISC-FUNCTIONS-S2-COMPATIBILITY-001"
        ]
        self.assertEqual(len(misc_functions["operations"]), 1)
        error_fmt = misc_functions["operations"][0]
        self.assertEqual(error_fmt["line"], 17)
        self.assertEqual(error_fmt["kind"], "exact_bytes_replace_once")
        self.assertIn("sprintf str fmt", error_fmt["before"])
        self.assertNotIn("sprintf", error_fmt["after"])
        self.assertIn("error_msg", error_fmt["after"])
        self.assertIn("explicit fail-closed Error", misc_functions["semantic_rule"])
        self.assertIn("no error_fmt caller", misc_functions["scope_limit"])
        self.assertIn("fix-top100", misc_functions["scope_limit"])
        self.assertIn("unchanged test helper", misc_functions["scope_limit"])
        self.assertIn("central for-loop gate", misc_functions["scope_limit"])
        arith_num = entries["PROJECT-ARITH-NUM-S2-VALUE-RESTRICTION-001"]
        self.assertEqual(len(arith_num["operations"]), 1)
        arith_tables = arith_num["operations"][0]
        self.assertEqual(arith_tables["kind"], "exact_lines_replace_once")
        self.assertEqual(arith_tables["replacement_count"], 21)
        self.assertEqual(
            [replacement["line"] for replacement in arith_tables["replacements"]],
            [111, 112, 167, 209, 323, 375, 440, 489, 574, 670, 701,
             744, 775, 961, 972, 1136, 1201, 1250, 1251, 1483, 1492],
        )
        self.assertTrue(all(
            "Hashtbl.create" in replacement["before"]
            and " Hashtbl.t = Hashtbl.create" in replacement["after"]
            for replacement in arith_tables["replacements"]
        ))
        self.assertIn("complete static set of 21", arith_num["semantic_rule"])
        self.assertIn("all 21 and only", arith_num["scope_limit"])
        self.assertIn("fresh cumulative replay", arith_num["scope_limit"])
        arith_cache = entries[
            "PROJECT-ARITH-CACHE-S2-VALUE-RESTRICTION-001"
        ]
        self.assertEqual(len(arith_cache["operations"]), 3)
        cache_tables, cache_clear, cache_print = arith_cache["operations"]
        self.assertEqual(cache_tables["kind"], "exact_bytes_replace_once")
        self.assertEqual(cache_tables["line"], 25)
        self.assertEqual(cache_tables["before"].count("Hashtbl.create"), 6)
        self.assertEqual(cache_tables["after"].count("Hashtbl.t ="), 6)
        self.assertIn("(string, thm * thm) Hashtbl.t", cache_tables["after"])
        self.assertEqual(cache_clear["line"], 49)
        self.assertIn("let clear = Hashtbl.clear", cache_clear["before"])
        self.assertNotIn("let clear", cache_clear["after"])
        self.assertEqual(cache_clear["after"].count("Hashtbl.clear"), 6)
        self.assertEqual(cache_print["line"], 76)
        self.assertEqual(cache_print["before"].count("sprintf"), 10)
        self.assertNotIn("sprintf", cache_print["after"])
        self.assertEqual(cache_print["after"].count("string_of_int"), 19)
        self.assertNotIn("let len = Hashtbl.length", cache_print["after"])
        self.assertEqual(cache_print["after"].count("Hashtbl.length"), 6)
        self.assertIn("complete simultaneous group of six", arith_cache["semantic_rule"])
        self.assertIn("all six and only", arith_cache["scope_limit"])
        self.assertIn("fix-top100", arith_cache["scope_limit"])
        glpk_link = entries[
            "PROJECT-GLPK-LINK-S3-FAIL-CLOSED-PRINTF-001"
        ]
        self.assertEqual(len(glpk_link["operations"]), 1)
        glpk_sprintf = glpk_link["operations"][0]
        self.assertEqual(glpk_sprintf["kind"], "exact_bytes_replace_once")
        self.assertEqual(glpk_sprintf["line"], 33)
        self.assertEqual(glpk_sprintf["before"], "let sprintf = Printf.sprintf;;")
        self.assertIn("let sprintf _ =", glpk_sprintf["after"])
        self.assertIn("non-verification GLPK formatter", glpk_sprintf["after"])
        self.assertIn("fresh polymorphic instantiation", glpk_link["semantic_rule"])
        self.assertIn("not Printf or formatting support", glpk_link["scope_limit"])
        self.assertIn("fresh cumulative replay", glpk_link["scope_limit"])
        immediate = entries["PROJECT-POINTER-S3-IMMEDIATE-001"]
        self.assertEqual(
            [operation["line"] for operation in immediate["operations"]],
            [284, 329, 342, 1050, 299, 852, 1059],
        )
        self.assertEqual(
            immediate["operations"][0]["after"],
            "let var_table : (term, thm) Hashtbl.t = Hashtbl.create 1000;;",
        )
        self.assertTrue(all(
            "Term.compare" in operation["after"]
            for operation in immediate["operations"][1:3]
        ))
        self.assertEqual(immediate["operations"][3]["before"].count("=="), 1)
        self.assertNotIn("==", immediate["operations"][3]["after"])
        self.assertIn("does not apply to allocated values", immediate["scope_limit"])
        allocated = entries["PROJECT-POINTER-S3-ALLOCATED-LIB-001"]
        self.assertEqual(
            [operation["id"] for operation in allocated["operations"]],
            [
                "PROJECT-S3-LIB-REV-VALUE-RESTRICTION-001",
                "PROJECT-S3-LIB-LENGTH-VALUE-RESTRICTION-001",
                "PROJECT-POINTER-S3-LIB-FILTER-001",
                "PROJECT-POINTER-S3-LIB-PARTITION-001",
                "PROJECT-POINTER-S3-LIB-UNIQ-001",
                "PROJECT-S3-LIB-GCD-NUM-API-001",
                "PROJECT-POINTER-S3-LIB-QMAP-001",
                "PROJECT-S3-LIB-MAPF-VALUE-RESTRICTION-001",
                "PROJECT-S3-LIB-FOLDL-VALUE-RESTRICTION-001",
                "PROJECT-S3-LIB-FOLDR-VALUE-RESTRICTION-001",
                "PROJECT-S3-LIB-APPLYD-VALUE-RESTRICTION-001",
                "PROJECT-POINTER-S3-LIB-UNDEFINE-001",
                "PROJECT-S3-LIB-PAIR-VALUE-RESTRICTION-001",
            ],
        )
        self.assertEqual(
            allocated["operations"][0]["id"],
            "PROJECT-S3-LIB-REV-VALUE-RESTRICTION-001",
        )
        self.assertEqual(allocated["operations"][0]["line"], 70)
        self.assertTrue(allocated["operations"][0]["after"].startswith(
            "let rev l =\n",
        ))
        self.assertNotIn(
            "fun l -> rev_append [] l",
            allocated["operations"][0]["after"],
        )
        self.assertTrue(allocated["operations"][11]["after"].startswith(
            "let undefine x t =\n",
        ))
        pair_replacement_path = (
            Path(__file__).with_name("compatibility") / "fixtures" /
            "lib_pair_split_replacement.ml"
        )
        self.assertEqual(
            allocated["operations"][12]["after"],
            pair_replacement_path.read_text().rstrip("\n"),
        )
        self.assertIn("same total list or Patricia-tree functions", (
            allocated["semantic_rule"]
        ))
        self.assertIn("qmap is a selected-graph non-use", allocated["scope_limit"])
        flyspeck_lib = entries[
            "PROJECT-FLYSPECK-LIB-S3-COMPATIBILITY-002"
        ]
        self.assertEqual(
            flyspeck_lib["operations"][0]["before"],
            'needs (String.concat "/" ["general"; if version_ge_4_14 '
            'then "flyspeck_eval_4.14.hl" else "flyspeck_eval.hl"]);;',
        )
        self.assertEqual(
            flyspeck_lib["operations"][0]["after"],
            'needs "general/flyspeck_eval_4.14.hl";;',
        )
        self.assertEqual(
            flyspeck_lib["operations"][1]["before"],
            'Printf.fprintf outs "%s" a',
        )
        self.assertEqual(
            flyspeck_lib["operations"][1]["after"],
            "output_string outs a",
        )
        self.assertIn("same logical relative-path literal", (
            flyspeck_lib["semantic_rule"]
        ))
        self.assertIn("constant %s format", flyspeck_lib["semantic_rule"])
        print_types = entries["PROJECT-PRINT-TYPES-S3-COMPATIBILITY-001"]
        self.assertEqual(
            [operation["line"] for operation in print_types["operations"]],
            [34, 64, 82, 83, 85],
        )
        self.assertIn("failwith", print_types["operations"][0]["after"])
        comparator = "Pair.compare String.compare Type.compare x y < 0"
        self.assertIn(comparator, print_types["operations"][1]["after"])
        self.assertEqual(
            sum(operation["after"].count("setify atom_type_lt")
                for operation in print_types["operations"]),
            4,
        )
        self.assertIn("later numeric comparisons", print_types["scope_limit"])
        hol_pervasives = entries[
            "PROJECT-HOL-PERVASIVES-S3-COMPATIBILITY-001"
        ]
        self.assertEqual(
            [operation["line"] for operation in hol_pervasives["operations"]],
            [21, 48],
        )
        self.assertIn("dynamic Hol_pervasives.needs is disabled", (
            hol_pervasives["operations"][0]["after"]
        ))
        self.assertIn("String.compare x y < 0", (
            hol_pervasives["operations"][1]["after"]
        ))
        self.assertIn("no qualified Hol_pervasives.needs", (
            hol_pervasives["semantic_rule"]
        ))
        relabel = entries["PROJECT-POINTER-S3-RELABEL-001"]
        self.assertEqual(
            [operation["line"] for operation in relabel["operations"]],
            [182, 256, 529],
        )
        self.assertIn("let absname", relabel["operations"][0]["after"])
        self.assertIn("(absname,repname)", relabel["operations"][0]["after"])
        self.assertIn("not (y = x)", relabel["operations"][1]["after"])
        self.assertIn("Hash_term.hash_of_term", relabel["operations"][2]["after"])
        set_make = entries["PROJECT-MODULE-S3-SET-MAKE-001"]
        self.assertEqual(set_make["operations"][0]["line"], 34)
        self.assertIn("type t = string list", set_make["operations"][0]["after"])
        self.assertNotIn("Set.Make", set_make["operations"][0]["after"])
        self.assertIn("only through empty, add, and mem", set_make["semantic_rule"])
        self.assertEqual(len(set_make["operations"]), 3)
        self.assertIn("#flyspeck_loadt", set_make["operations"][1]["after"])
        digest_output = set_make["operations"][2]
        self.assertEqual(digest_output["kind"], "exact_span_replace_once")
        self.assertEqual((digest_output["line"], digest_output["end_line"]),
                         (490, 499))
        self.assertIn("Filename.temp_file", digest_output["start"])
        self.assertNotIn("Filename.temp_file", digest_output["after"])
        self.assertEqual(digest_output["after"].count("failwith"), 2)
        self.assertIn("attempt-local atomic", set_make["scope_limit"])
        update_database = entries["PROJECT-TOPLOOP-S3-UPDATE-DATABASE-001"]
        self.assertEqual(
            [operation["kind"] for operation in update_database["operations"]],
            ["exact_bytes_replace_once", "exact_span_replace_once"],
        )
        self.assertIn("failwith", update_database["operations"][1]["after"])
        self.assertIn("dead-effect elimination", update_database["scope_limit"])
        update_database_310 = entries[
            "PROJECT-TOPLOOP-S3-UPDATE-DATABASE-310-UNSELECTED-001"
        ]
        self.assertEqual(
            [operation["kind"] for operation in
             update_database_310["operations"]],
            ["exact_span_replace_once", "exact_bytes_replace_once"],
        )
        self.assertIn("failwith", update_database_310["operations"][0]["after"])
        self.assertIn("unselected OCaml-3.10", update_database_310["scope_limit"])
        eval_command = entries["PROJECT-TOPLOOP-S3-EVAL-COMMAND-001"]
        self.assertIn("failwith", eval_command["operations"][0]["after"])
        self.assertNotIn("?(silent", eval_command["operations"][0]["after"])
        self.assertIn("no active ~silent label", eval_command["scope_limit"])
        ssreflect = entries["PROJECT-TOPLOOP-S3-SSREFLECT-LOOKUP-001"]
        self.assertIn("use_arg_then2", ssreflect["semantic_rule"])
        self.assertNotIn("Toploop", ssreflect["operations"][0]["after"])
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
        logical_digest_operations = strictbuild["operations"][5:8]
        self.assertEqual(
            [operation["line"] for operation in logical_digest_operations],
            [94, 126, 173],
        )
        self.assertTrue(all(
            "Digest.to_hex (Digest.file s')" in operation["after"]
            for operation in logical_digest_operations
        ))
        self.assertIn("dynamic strictbuild build_and_report is disabled", (
            strictbuild["operations"][8]["after"]
        ))
        self.assertIn("canonical 32-character", strictbuild["semantic_rule"])
        self.assertIn("open_out_gen shim", strictbuild["semantic_rule"])
        sphere = entries["PROJECT-SPHERE-S3-TERM-ORDER-001"]
        self.assertEqual(
            [operation["line"] for operation in sphere["operations"]],
            [33],
        )
        self.assertIn("sort Term.(<) (frees bod)", (
            sphere["operations"][0]["after"]
        ))
        for entry_id, lines in (
            ("PROJECT-HALES-TACTIC-S3-LIST-CONCAT-001",
             [103, 142, 125, 133, 143]),
            ("PROJECT-TRUONG-TACTIC-S3-LIST-CONCAT-001",
             [89, 133, 105, 113, 134]),
        ):
            tactic = entries[entry_id]
            self.assertEqual(
                [operation["line"] for operation in tactic["operations"]],
                lines,
            )
            self.assertTrue(all(
                "List.concat" in operation["after"]
                and "List.flatten" not in operation["after"]
                for operation in tactic["operations"][:2]
            ))
            self.assertEqual(
                sum("setify Term.(<)" in operation["after"]
                    for operation in tactic["operations"]),
                3,
            )
            self.assertIn(
                "Pair.compare String.compare Term.compare",
                tactic["operations"][4]["after"],
            )
        hash_term = entries["PROJECT-HASH-TERM-S3-CHAR-CODE-001"]
        self.assertEqual(hash_term["operations"][0]["line"], 20)
        self.assertEqual(
            hash_term["operations"][0]["after"],
            "Char.code (String.get h 0)",
        )
        self.assertIn(
            'let name = "??_"^(string_of_int n)',
            hash_term["operations"][1]["after"],
        )
        calc_derivative = entries[
            "PROJECT-CALC-DERIVATIVE-S3-TUPLE-CONSTRUCTOR-001"
        ]
        self.assertEqual(calc_derivative["operations"][0]["line"], 1236)
        self.assertIn(
            'let name = "F"^(string_of_int !c)',
            calc_derivative["operations"][0]["after"],
        )
        nonlinear_boundary_entries = {
            "PROJECT-INEQDATA3Q1H-S3-POLYMORPHIC-NTH-001": 5,
            "PROJECT-INEQ-S3-PRINTF-FLATTEN-LOOPS-001": 8,
            "PROJECT-MAIN-ESTIMATE-INEQ-S3-PRINTF-LOOP-001": 1,
            "PROJECT-PARSE-INEQ-S3-CANDLE-COMPATIBILITY-001": 13,
            "PROJECT-OPTIMIZE-S3-PRINTF-001": 4,
            "PROJECT-MERGE-INEQ-S3-CANDLE-COMPATIBILITY-001": 6,
        }
        for entry_id, operation_count in nonlinear_boundary_entries.items():
            self.assertEqual(len(entries[entry_id]["operations"]), operation_count)
        ineq_operations = entries[
            "PROJECT-INEQ-S3-PRINTF-FLATTEN-LOOPS-001"
        ]["operations"]
        ineqdoc = next(
            operation for operation in ineq_operations
            if operation["id"] == "PROJECT-INEQ-S3-INEQDOC-VALUE-RESTRICTION-001"
        )
        self.assertEqual(
            ineqdoc["after"],
            "let ineqdoc = ref ([]:(texmarker * string * string) list);;",
        )
        dart_classes = next(
            operation for operation in ineq_operations
            if operation["id"] == (
                "PROJECT-INEQ-S3-DART-CLASSES-VALUE-RESTRICTION-001"
            )
        )
        self.assertEqual(
            dart_classes["after"], "let dart_classes = ref ([]:thm list);;",
        )
        self.assertEqual(
            entries["PROJECT-INEQDATA3Q1H-S3-POLYMORPHIC-NTH-001"]
            ["operations"][0]["after"],
            "",
        )
        self.assertIn(
            "String.compare left right < 0",
            next(
                operation for operation in entries[
                    "PROJECT-PARSE-INEQ-S3-CANDLE-COMPATIBILITY-001"
                ]["operations"]
                if operation["id"].endswith("STRING-ORDER")
            )["after"],
        )
        autogen = entries[
            "PROJECT-PARSE-INEQ-S3-CANDLE-COMPATIBILITY-001"
        ]["operations"][0]
        self.assertEqual(
            autogen["after"], "let autogen = ref ([]:term list);;",
        )
        parse_ineq_operations = entries[
            "PROJECT-PARSE-INEQ-S3-CANDLE-COMPATIBILITY-001"
        ]["operations"]
        self.assertEqual(
            next(operation for operation in parse_ineq_operations
                 if operation["id"].endswith("DOUBLE-MAXIMUM-001"))["line"],
            337,
        )
        self.assertIn(
            "Cake.Double.(>)",
            next(operation for operation in parse_ineq_operations
                 if operation["id"].endswith("DOUBLE-MAXIMUM-001"))["after"],
        )
        self.assertEqual(
            next(operation for operation in parse_ineq_operations
                 if operation["id"].endswith("COUNTER-UNIT-001"))["after"],
            "      let counter () = \n",
        )
        self.assertNotIn(
            "Match_failure",
            next(operation for operation in parse_ineq_operations
                 if operation["id"].endswith("EXPLICIT-ACS-ARITY-001"))
            ["after"],
        )
        parse_ineq_cfsqp = next(
            operation
            for operation in entries[
                "PROJECT-PARSE-INEQ-S3-CANDLE-COMPATIBILITY-001"
            ]["operations"]
            if operation["id"].endswith("DISABLE-CFSQP-CODE")
        )
        self.assertEqual(parse_ineq_cfsqp["kind"], "exact_span_replace_once")
        self.assertEqual(parse_ineq_cfsqp["line"], 408)
        self.assertEqual(parse_ineq_cfsqp["end_line"], 449)
        self.assertIn(
            "CFSQP code generation is disabled", parse_ineq_cfsqp["after"],
        )
        optimize_tuple = next(
            operation for operation in entries[
                "PROJECT-OPTIMIZE-S3-PRINTF-001"
            ]["operations"]
            if operation["id"] == "PROJECT-OPTIMIZE-S3-TUPLE-CONSTRUCTOR-001"
        )
        self.assertEqual(optimize_tuple["line"], 76)
        self.assertIn('let name = "x"^string_of_int i', optimize_tuple["after"])
        self.assertIn('let name = "a"^string_of_int i', optimize_tuple["after"])
        optimize_preprocess = [
            operation for operation in entries[
                "PROJECT-OPTIMIZE-S3-PRINTF-001"
            ]["operations"]
            if "PREPROCESS" in operation["id"]
        ]
        self.assertEqual(len(optimize_preprocess), 2)
        self.assertIn("let prep_name", optimize_preprocess[0]["after"])
        self.assertIn("let case_name", optimize_preprocess[1]["after"])
        self.assertIn("let case_ineq", optimize_preprocess[1]["after"])
        merge_bounds = next(
            operation for operation in entries[
                "PROJECT-MERGE-INEQ-S3-CANDLE-COMPATIBILITY-001"
            ]["operations"]
            if operation["id"].endswith("BOUNDS-CONCAT")
        )
        self.assertIn(
            "Pair.compare Term.compare (Pair.compare Term.compare Term.compare)",
            merge_bounds["after"],
        )
        merge_operations = entries[
            "PROJECT-MERGE-INEQ-S3-CANDLE-COMPATIBILITY-001"
        ]["operations"]
        self.assertIn(
            "let tsk_record = Ineq.TSKAJXY_DERIVED",
            next(operation for operation in merge_operations
                 if operation["id"].endswith("QUALIFIED-RECORD-001"))["after"],
        )
        self.assertIn(
            'let name = "y" ^ string_of_int i',
            next(operation for operation in merge_operations
                 if operation["id"].endswith("TUPLE-CONSTRUCTOR-001"))["after"],
        )
        float_entry = entries["PROJECT-FLOAT-S3-STRUCTURE-EFFECT-001"]
        self.assertEqual(
            [operation["line"] for operation in float_entry["operations"]],
            [184, 191, 1144, 1155, 1538, 1681],
        )
        self.assertEqual(
            sum("Assert_failure" in operation["after"]
                for operation in float_entry["operations"]),
            4,
        )
        self.assertEqual(
            sum("float_fabs" in operation["after"]
                and "Cake.Double.(>=)" in operation["after"]
                for operation in float_entry["operations"]),
            2,
        )
        misc_entry = entries["PROJECT-MISC-DEFS-S3-STRUCTURE-EFFECT-001"]
        self.assertEqual(
            [operation["line"] for operation in misc_entry["operations"]],
            [365, 367],
        )
        self.assertEqual(
            misc_entry["operations"][0]["after"],
            "SUBGOAL_MP_TAC `?t. t = x+|y'`;",
        )
        self.assertEqual(
            misc_entry["operations"][1]["after"],
            "SPEC_TAC (`x:num`,`a:num`);",
        )
        parser_orpattern = entries["PROJECT-PARSER-S3-LET-OR-PATTERN-001"]
        self.assertEqual(
            [operation["line"] for operation in parser_orpattern["operations"]],
            [36, 86, 106],
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
        self.assertIn("let name = \"GEN%PVAR%\"", (
            parser_orpattern["operations"][2]["after"]
        ))
        self.assertIn("Varp(name,dpty)", (
            parser_orpattern["operations"][2]["after"]
        ))
        tuple_after = parser_orpattern["operations"][2]["after"]
        self.assertLess(tuple_after.index("gcounter := count + 1"),
                        tuple_after.index("let name = \"GEN%PVAR%\""))
        self.assertLess(tuple_after.index("let name = \"GEN%PVAR%\""),
                        tuple_after.index("Varp(name,dpty)"))
        self.assertIn("tuple-valued Varp", parser_orpattern["semantic_rule"])
        debug_compatibility = entries["PROJECT-DEBUG-S3-COMPATIBILITY-001"]
        self.assertEqual(debug_compatibility["operations"][0]["line"], 22)
        self.assertIn('print_string "\\n");;', (
            debug_compatibility["operations"][0]["after"]
        ))
        self.assertEqual(
            [operation["line"] for operation in debug_compatibility["operations"]],
            [22, 107, 115, 110, 113, 126],
        )
        self.assertIn("let _ = false;;", debug_compatibility["operations"][1]["after"])
        self.assertIn("let _ = true;;", debug_compatibility["operations"][2]["after"])
        self.assertIn("Cakeml.unquote := quotexpander_verbose", (
            debug_compatibility["operations"][3]["after"]
        ))
        self.assertIn("Cakeml.unquote := quotexpander", (
            debug_compatibility["operations"][4]["after"]
        ))
        self.assertIn("setify Term.(<) fs", (
            debug_compatibility["operations"][5]["after"]
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
        self.assertNotIn("Gc.stat", static_inventory["operations"][1]["after"])
        self.assertIn("outer runner", static_inventory["operations"][1]["after"])
        self.assertEqual(static_inventory["operations"][2]["line"], 57)
        self.assertIn(
            "candle_flyspeck_record_lp_certificate_consumption file",
            static_inventory["operations"][2]["after"],
        )
        self.assertIn("successful return", static_inventory["scope_limit"])
        self.assertEqual(
            [operation["line"] for operation in static_inventory["operations"][3:]],
            [48, 70],
        )
        self.assertIn(
            "string_of_int !remaining_files",
            static_inventory["operations"][3]["after"],
        )
        section_compare = entries["PROJECT-COMPARE-S3-SECTION-NAME-001"]
        self.assertIn("String.compare", section_compare["operations"][0]["after"])
        lp_compare = entries["PROJECT-COMPARE-S3-LP-COUNT-ORDER-001"]
        self.assertIn("Int.compare", lp_compare["operations"][2]["after"])
        self.assertIn("let addv key xs t", (
            lp_compare["operations"][3]["after"]
        ))
        self.assertEqual(
            lp_compare["operations"][4]["after"].count("= addv "),
            4,
        )
        self.assertIn("let p_int = sprintf", (
            lp_compare["operations"][5]["after"]
        ))
        self.assertEqual(
            lp_compare["operations"][5]["after"].count("p_int\""),
            2,
        )
        self.assertEqual(lp_compare["operations"][6]["after"], (
            "  let feasible r = "
            "(Stdlib.Float.compare r 11.9999 = 1) in "
            "(* relax a bit from 12.0 *)"
        ))
        self.assertEqual(lp_compare["operations"][7]["after"], (
            "    output_string outs j;;  "
        ))
        interval_table = entries[
            "PROJECT-LP-S3-VALUE-RESTRICTION-001-CONSTANT-INTERVALS"
        ]
        self.assertEqual(len(interval_table["operations"]), 1)
        self.assertEqual(interval_table["operations"][0]["line"], 498)
        self.assertEqual(
            interval_table["operations"][0]["after"],
            "let interval_table : (term, thm) Hashtbl.t = Hashtbl.create 10;;",
        )
        self.assertIn("exact type already forced", interval_table["semantic_rule"])
        self.assertIn("action-159", interval_table["scope_limit"])
        fixed_format_entries = {
            "PROJECT-LP-S3-FIXED-FORMAT-GOOD-LIST-001": 98,
            "PROJECT-LP-S3-FIXED-FORMAT-INEQS-001": 308,
            "PROJECT-LP-S3-FIXED-FORMAT-BODY-001": 233,
        }
        for entry_id, line in fixed_format_entries.items():
            self.assertEqual(entries[entry_id]["operations"][0]["line"], line)
            self.assertIn("string_of_int", (
                entries[entry_id]["operations"][0]["after"]
            ))
        exact_lp = entries["PROJECT-S3-LP-EXACT-RESULT-COVERAGE-001"]
        self.assertEqual(exact_lp["operations"][0]["line"], 46)
        exact_lp_after = exact_lp["operations"][0]["after"]
        self.assertIn("duplicate Flyspeck archive id", exact_lp_after)
        self.assertIn("unexpected LP result id", exact_lp_after)
        self.assertIn("duplicate LP result id", exact_lp_after)
        self.assertIn("length ths <> length archive_const_ids", exact_lp_after)
        self.assertNotIn("map (fun (id, th) -> Hashtbl.add", exact_lp_after)
        self.assertEqual(
            [operation["line"] for operation in exact_lp["operations"][1:]],
            [45, 58],
        )
        prove_lp = entries["PROJECT-POINTER-S3-IMMEDIATE-001"]
        self.assertEqual(
            [operation["line"] for operation in prove_lp["operations"][-3:]],
            [299, 852, 1059],
        )
        nonlinear_coverage = entries[
            "PROJECT-NONLINEAR-S3-RECONSTRUCTION-COVERAGE-001"
        ]
        self.assertEqual(
            [operation["line"] for operation in nonlinear_coverage["operations"]],
            [1649, 1693, 1702],
        )
        nonlinear_coverage_after = "".join(
            operation["after"] for operation in nonlinear_coverage["operations"]
        )
        self.assertIn("23242 ||", nonlinear_coverage_after)
        self.assertIn("candle_nonlinear_iarg_leaf_visits", nonlinear_coverage_after)
        self.assertIn("incr candle_nonlinear_iarg_leaf_visits", nonlinear_coverage_after)
        self.assertIn("partition-shape", nonlinear_coverage["scope_limit"])
        nonlinear_digests = entries[
            "PROJECT-NONLINEAR-S3-FINAL-COVERAGE-GATES-001"
        ]
        self.assertEqual(
            [operation["line"] for operation in nonlinear_digests["operations"]],
            [49, 335, 364, 412],
        )
        nonlinear_after = "".join(
            operation["after"] for operation in nonlinear_digests["operations"]
        )
        self.assertIn("1f054717131cf915bd8cc95ab7b645c3", nonlinear_after)
        self.assertIn("e607b9e5e7f4c495236c6546d6889963", nonlinear_after)
        self.assertIn("filter (fun (_,t) -> t = TRUTH) exec_results = []", nonlinear_after)
        self.assertIn("candle_nonlinear_iarg_leaf_visits = 7479", nonlinear_after)
        self.assertEqual(nonlinear_after.count("||\n  failwith"), 4)
        self.assertIn("do not bind definition/proof history", (
            nonlinear_digests["scope_limit"]
        ))
        lp_quads = entries[
            "PROJECT-LP-S3-QUADS-BOUNDED-FRONTEND-001"
        ]
        self.assertEqual(
            lp_quads["path"],
            "formal_lp/hypermap/ineqs/lp_ineqs_quads-compiled.hl",
        )
        self.assertEqual(len(lp_quads["operations"]), 1)
        whole_source = lp_quads["operations"][0]
        self.assertEqual(whole_source["kind"], "exact_span_replace_once")
        self.assertEqual(
            [whole_source["line"], whole_source["end_line"]],
            [1, 270],
        )
        self.assertEqual(
            whole_source["span_sha256"],
            lp_quads["source_sha256"],
        )
        self.assertEqual(
            hashlib.sha256(whole_source["after"].encode()).hexdigest(),
            lp_quads["normalized_sha256"],
        )
        self.assertIn('USE_THEN "fanV"', whole_source["after"])
        self.assertIn(
            "F_FAN_PAIR_EXT_PERMUTES_DART_OF_FAN",
            whole_source["after"],
        )
        self.assertIn("PERMUTES_INVERSE", whole_source["after"])
        self.assertIn("PERMUTES_IN_IMAGE", whole_source["after"])
        invf_helper = whole_source["after"].split(
            "module Candle_lp_ineqs_quads_ineq119_tauVEF_tactics_00",
            1,
        )[0]
        self.assertNotIn("f_fan_pair_ext_in_darts_k", invf_helper)
        self.assertIn(
            "module Candle_lp_ineqs_quads_tactic_support = struct",
            whole_source["after"],
        )
        self.assertIn("module Lp_ineqs_quads = struct", whole_source["after"])
        self.assertIn("complete 85-item flattened trace", (
            lp_quads["scope_limit"]
        ))
        conforming_sequence = entries[
            "PROJECT-CONFORMING-S2-TACTIC-SEQUENCE-001"
        ]["operations"][0]
        self.assertEqual(conforming_sequence["line"], 1424)
        self.assertIn("; THEN", conforming_sequence["before"])
        self.assertNotIn("; THEN", conforming_sequence["after"])
        operation_ids = [
            operation["id"]
            for entry in entries.values()
            for operation in entry["operations"]
        ]
        archive = entries["PROJECT-ARCHIVE-S3-TAME-LIST-THUNKS-001"]
        self.assertEqual(
            archive["operations"][0]["kind"],
            "exact_ocaml_global_thunk_list",
        )
        self.assertEqual(archive["operations"][0]["chunk_count"], 40)
        self.assertIn("lexical shadowing", archive["semantic_rule"])
        lpproc = entries["PROJECT-COMPARE-S3-LP-COUNT-ORDER-001"]
        self.assertEqual(
            [operation["after"] for operation in lpproc["operations"][:2]],
            [
                'needs "../formal_lp/glpk/glpk_link.ml";;',
                'needs "../formal_graph/archive/archive_all.ml";;',
            ],
        )
        self.assertIn("same logical relative-path literals", (
            lpproc["semantic_rule"]
        ))
        self.assertEqual(len(operation_ids), 187)
        self.assertEqual(len(operation_ids), len(set(operation_ids)))

    def test_materialized_receipt_is_deterministic(self):
        entry, source, normalized = self.fixture_entry()
        contract = copy.deepcopy(self.contract)
        contract["flyspeck_commit"] = "a" * 40
        contract["entries"] = [entry]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source_root = root / "source"
            first_output = root / "output-first"
            second_output = root / "output-second"
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
                    contract_path, source_root, first_output,
                )
                second = flyspeck_normalize.materialize(
                    contract_path, source_root, second_output,
                )
            finally:
                flyspeck_normalize._git_head = original_git_head
            self.assertEqual(first, second)
            self.assertEqual(
                (first_output / entry["path"]).read_bytes(), normalized
            )
            receipt = json.loads(
                (
                    first_output / flyspeck_normalize.RECEIPT_NAME
                ).read_text()
            )
            self.assertEqual(receipt, first)
            self.assertEqual(receipt["schema"], 3)
            self.assertEqual(
                receipt["publication"], flyspeck_normalize.PUBLICATION_RECORD,
            )

    def test_cli_refuses_dangling_output_symlink(self):
        entry, source, _ = self.fixture_entry()
        contract = copy.deepcopy(self.contract)
        contract["flyspeck_commit"] = "a" * 40
        contract["entries"] = [entry]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source_root = root / "source"
            source_path = source_root / entry["path"]
            source_path.parent.mkdir(parents=True)
            source_path.write_bytes(source)
            contract_path = root / "contract.json"
            contract_path.write_text(json.dumps(contract), encoding="utf-8")
            output_root = root / "output"
            output_root.symlink_to(root / "dangling", target_is_directory=True)
            arguments = [
                "flyspeck_normalize.py",
                "--flyspeck-root", str(source_root),
                "--contract", str(contract_path),
                "--write", str(output_root),
            ]
            with mock.patch.object(flyspeck_normalize, "_git_head",
                                   return_value="a" * 40), \
                    mock.patch("sys.argv", arguments), \
                    self.assertRaisesRegex(ValueError, "output symlink"):
                flyspeck_normalize.main()
            self.assertTrue(output_root.is_symlink())
            self.assertFalse((root / "dangling").exists())

    def test_publication_race_preserves_colliding_destination(self):
        entry, source, _ = self.fixture_entry()
        contract = copy.deepcopy(self.contract)
        contract["flyspeck_commit"] = "a" * 40
        contract["entries"] = [entry]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source_root = root / "source"
            source_path = source_root / entry["path"]
            source_path.parent.mkdir(parents=True)
            source_path.write_bytes(source)
            contract_path = root / "contract.json"
            contract_path.write_text(json.dumps(contract), encoding="utf-8")
            output_root = root / "output"
            rename_noreplace = flyspeck_normalize._rename_noreplace

            def collide(source_path, destination_path):
                destination_path.mkdir()
                (destination_path / "unrelated").write_text("preserved")
                rename_noreplace(source_path, destination_path)

            with mock.patch.object(flyspeck_normalize, "_git_head",
                                   return_value="a" * 40), \
                    mock.patch.object(flyspeck_normalize, "_rename_noreplace",
                                      side_effect=collide), \
                    self.assertRaises(FileExistsError):
                flyspeck_normalize.materialize(
                    contract_path, source_root, output_root,
                )
            self.assertEqual(
                (output_root / "unrelated").read_text(), "preserved"
            )
            staging = list(root.glob(".output.tmp.*"))
            self.assertEqual(len(staging), 1)
            self.assertFalse(
                (staging[0] / flyspeck_normalize.RECEIPT_NAME).exists()
            )
            self.assertTrue(
                (staging[0] / flyspeck_normalize.PENDING_RECEIPT_NAME).is_file()
            )

    def test_materialization_modes_ignore_permissive_umask(self):
        entry, source, _ = self.fixture_entry()
        contract = copy.deepcopy(self.contract)
        contract["flyspeck_commit"] = "a" * 40
        contract["entries"] = [entry]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source_root = root / "source"
            source_path = source_root / entry["path"]
            source_path.parent.mkdir(parents=True)
            source_path.write_bytes(source)
            contract_path = root / "contract.json"
            contract_path.write_text(json.dumps(contract), encoding="utf-8")
            output_root = root / "output"
            original_umask = os.umask(0)
            try:
                with mock.patch.object(flyspeck_normalize, "_git_head",
                                       return_value="a" * 40):
                    flyspeck_normalize.materialize(
                        contract_path, source_root, output_root,
                    )
            finally:
                os.umask(original_umask)
            self.assertEqual(output_root.stat().st_mode & 0o777, 0o555)
            self.assertEqual(
                (output_root / entry["path"]).stat().st_mode & 0o777, 0o444,
            )
            self.assertEqual(
                (output_root / flyspeck_normalize.RECEIPT_NAME).stat().st_mode
                & 0o777,
                0o444,
            )
            for parent in (output_root / entry["path"]).parents:
                if parent == output_root:
                    break
                self.assertEqual(parent.stat().st_mode & 0o777, 0o555)

    def test_receipt_hashes_the_contract_bytes_that_were_parsed(self):
        entry, source, _ = self.fixture_entry()
        contract = copy.deepcopy(self.contract)
        contract["flyspeck_commit"] = "a" * 40
        contract["entries"] = [entry]
        contract_bytes = json.dumps(contract).encode()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source_root = root / "source"
            source_path = source_root / entry["path"]
            source_path.parent.mkdir(parents=True)
            source_path.write_bytes(source)
            contract_path = root / "contract.json"
            contract_path.write_bytes(contract_bytes)
            original_evaluate = flyspeck_normalize.evaluate_contract

            def evaluate_then_swap(path, source, *, contract_bytes):
                result = original_evaluate(
                    path, source, contract_bytes=contract_bytes,
                )
                path.write_text("{}", encoding="utf-8")
                return result

            with mock.patch.object(flyspeck_normalize, "_git_head",
                                   return_value="a" * 40), \
                    mock.patch.object(flyspeck_normalize, "evaluate_contract",
                                      side_effect=evaluate_then_swap):
                receipt = flyspeck_normalize.materialize(
                    contract_path, source_root, root / "output",
                )
            self.assertEqual(
                receipt["contract_sha256"],
                hashlib.sha256(contract_bytes).hexdigest(),
            )

    def test_materialization_refuses_existing_output_root(self):
        entry, source, _ = self.fixture_entry()
        contract = copy.deepcopy(self.contract)
        contract["flyspeck_commit"] = "a" * 40
        contract["entries"] = [entry]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source_root = root / "source"
            source_path = source_root / entry["path"]
            source_path.parent.mkdir(parents=True)
            source_path.write_bytes(source)
            output_root = root / "output"
            output_root.mkdir()
            (output_root / "unexpected").write_text("must not survive")
            contract_path = root / "contract.json"
            contract_path.write_text(json.dumps(contract), encoding="utf-8")
            original_git_head = flyspeck_normalize._git_head
            flyspeck_normalize._git_head = lambda _: "a" * 40
            try:
                with self.assertRaisesRegex(ValueError, "already exists"):
                    flyspeck_normalize.materialize(
                        contract_path, source_root, output_root,
                    )
            finally:
                flyspeck_normalize._git_head = original_git_head
            self.assertEqual(
                (output_root / "unexpected").read_text(), "must not survive"
            )

    def test_materialization_cannot_overwrite_pinned_source(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            with self.assertRaisesRegex(ValueError, "output must be separate"):
                flyspeck_normalize.materialize(
                    self.contract_path, root, root,
                )

    def test_materialization_refuses_output_symlink(self):
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
            output_root.symlink_to(source_root, target_is_directory=True)
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
