#!/usr/bin/env python3

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FLYSPECK_ROOT = Path("/project/worktrees/flyspeck-v13-source")
sys.path.insert(0, str(HERE))

import flyspeck_nonlinear_verifier_closure as subject


class NonlinearVerifierClosureTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.payload = subject.build_closure(ROOT, FLYSPECK_ROOT)
        cls.published = json.loads(
            (ROOT / subject.OUTPUT).read_text(encoding="utf-8")
        )

    def test_published_closure_is_current(self) -> None:
        self.assertEqual(self.published, self.payload)

    def test_exact_bounded_closure(self) -> None:
        counts = self.payload["counts"]
        self.assertEqual(self.payload["root"], subject.VERIFIER_ROOT.key)
        self.assertEqual(counts["selected_source_nodes"], 90)
        self.assertEqual(counts["selected_by_repository"], {
            "candle": 28,
            "flyspeck": 62,
        })
        self.assertEqual(counts["already_in_direct_manifest"], 34)
        self.assertEqual(counts["identity_extension"], 56)
        self.assertEqual(counts["identity_extension_by_repository"], {
            "candle": 0,
            "flyspeck": 56,
        })
        self.assertEqual(counts["normalized_sources"], 18)
        self.assertEqual(counts["normalization_operations"], 106)

    def test_every_source_action_is_exactly_resolved(self) -> None:
        selected = set(self.payload["source_nodes"])
        for key, node in self.payload["source_nodes"].items():
            self.assertIn(node["repository"], {"candle", "flyspeck"})
            self.assertEqual(len(node["md5"]), 32)
            self.assertEqual(len(node["sha256"]), 64)
            for dependency in node["dependencies"]:
                if dependency["status"] == "runtime-library":
                    self.assertEqual(dependency["kind"], "#load")
                else:
                    self.assertEqual(dependency["status"], "resolved")
                    self.assertIn(dependency["selected"], selected, key)

    def test_extension_has_logical_identity_and_two_hashes(self) -> None:
        direct = set(self.payload["direct_manifest_overlap"])
        extension = self.payload["identity_extension"]
        self.assertEqual(len(extension), 56)
        self.assertTrue(all(item["source_key"] not in direct for item in extension))
        self.assertTrue(all(
            item["source_key"] ==
            f'{item["repository"]}:{item["logical_relative_path"]}'
            for item in extension
        ))

    def test_runtime_compatibility_members_are_accounted_for(self) -> None:
        compatibility = self.payload["compatibility"]
        self.assertEqual(compatibility["unsupported_use_count"], 0)
        self.assertEqual(compatibility["unsupported_uses"], [])
        members = {
            (use["module"], use["member"])
            for use in compatibility["qualified_uses"]
        }
        self.assertTrue({
            ("Array", "to_list"),
            ("Big_int", "eq_big_int"),
            ("Big_int", "mult_big_int"),
            ("Big_int", "sqrt_big_int"),
            ("Format", "std_formatter"),
            ("Stdlib", "abs_float"),
            ("Stdlib", "ignore"),
        } <= members)
        self.assertIn("abs_float", compatibility["toplevel_members"])
        self.assertTrue(any(
            use["source"] == "flyspeck:formal_ineqs/trig/exp_eval.hl" and
            use["identifier"] == "abs_float" and use["line"] == 345
            for use in compatibility["toplevel_uses"]
        ))

    def test_nested_array_grouping_is_lowered_exactly(self) -> None:
        normalized = {
            key: node["normalization"]
            for key, node in self.payload["source_nodes"].items()
            if "normalization" in node
        }
        parser_normalized = {
            key: record for key, record in normalized.items()
            if record["authority"] == "nonlinear-verifier-closure"
        }
        grouping_sources = {
            "flyspeck:formal_ineqs/taylor/m_taylor.hl",
            "flyspeck:formal_ineqs/taylor/m_taylor_arith2.hl",
            "flyspeck:formal_ineqs/verifier/m_verifier.hl",
            "flyspeck:formal_ineqs/verifier/m_verifier_main.hl",
        }
        self.assertTrue(grouping_sources <= set(parser_normalized))
        grouping_kinds = {
            "nested-array-get", "nested-array-set",
            *(kind for kind, _, _ in subject.MAIN_VERIFIER_GROUPING_REPLACEMENTS),
        }
        self.assertEqual(
            sum(
                operation["kind"] in grouping_kinds
                for record in parser_normalized.values()
                for operation in record["operations"]
            ),
            45,
        )
        self.assertEqual(
            sum(
                operation["kind"] == "nested-array-set"
                for record in parser_normalized.values()
                for operation in record["operations"]
            ),
            1,
        )
        self.assertTrue(all(
            record["id"] == subject.SOURCE_NORMALIZATION
            for record in parser_normalized.values()
        ))
        main = parser_normalized[
            "flyspeck:formal_ineqs/verifier/m_verifier_main.hl"
        ]
        self.assertEqual(main["operation_count"], 4)
        self.assertEqual(
            {operation["kind"] for operation in main["operations"]},
            {kind for kind, _, _ in subject.MAIN_VERIFIER_GROUPING_REPLACEMENTS},
        )

    def test_extension_formatting_inventory_is_complete(self) -> None:
        normalized = {
            key: node["normalization"]
            for key, node in self.payload["source_nodes"].items()
            if node.get("normalization", {}).get("authority")
            == "nonlinear-verifier-closure"
        }
        self.assertEqual(
            set(subject.EXTENSION_COMPATIBILITY_REPLACEMENTS),
            {
                key for key, record in normalized.items()
                if any(
                    operation["kind"]
                    not in {"nested-array-get", "nested-array-set"}
                    and operation["kind"] not in {
                        kind for kind, _, _
                        in subject.MAIN_VERIFIER_GROUPING_REPLACEMENTS
                    }
                    for operation in record["operations"]
                )
            },
        )

    def test_arith_float_top_level_table_inventory_is_typed(self) -> None:
        source_key = "flyspeck:formal_ineqs/arith/arith_float.hl"
        node = self.payload["source_nodes"][source_key]
        operations = node["normalization"]["operations"]
        table_operations = {
            operation["kind"]: operation
            for operation in operations
            if operation["kind"].endswith("table-type")
            or operation["kind"].endswith("table-types")
        }
        self.assertEqual(set(table_operations), {
            "arith-float-lo-table-type",
            "arith-float-lo2-table-type",
            "arith-float-hi-table-type",
            "arith-float-cache-table-types",
        })
        self.assertEqual(
            sum(operation["before"].count("Hashtbl.create")
                for operation in table_operations.values()),
            10,
        )
        self.assertEqual(
            sum(operation["after"].count(" Hashtbl.t = Hashtbl.create")
                for operation in table_operations.values()),
            10,
        )

    def test_raw_float_num_exponents_use_explicit_num_order(self) -> None:
        source_key = "flyspeck:formal_ineqs/arith/arith_float.hl"
        operations = self.payload["source_nodes"][source_key][
            "normalization"
        ]["operations"]
        selected = [
            operation for operation in operations
            if operation["kind"] == "arith-float-num-exponent-order"
        ]
        self.assertEqual(len(selected), 1)
        self.assertEqual(selected[0]["before"], "if e1 <= e2 then")
        self.assertEqual(selected[0]["after"], "if le_num e1 e2 then")
        self.assertEqual(selected[0]["replacement_count"], 1)

    def test_direct_normalizations_reuse_canonical_authority(self) -> None:
        normalized = {
            key: node["normalization"]
            for key, node in self.payload["source_nodes"].items()
            if "normalization" in node
        }
        direct = {
            key: record for key, record in normalized.items()
            if record["authority"] == "direct-flyspeck-normalization-contract"
        }
        self.assertEqual(set(direct), {
            "flyspeck:formal_ineqs/arith/arith_cache.hl",
            "flyspeck:formal_ineqs/arith/arith_num.hl",
            "flyspeck:formal_ineqs/misc/misc_functions.hl",
        })
        manifest = json.loads(
            (ROOT / subject.MANIFEST).read_text(encoding="utf-8")
        )
        for key, record in direct.items():
            authority = manifest["source_nodes"][key]["execution_normalization"]
            self.assertEqual(record["id"], authority["id"])
            self.assertEqual(
                record["normalized_sha256"], authority["normalized_sha256"],
            )

    def test_normalization_lanes_fail_closed_on_overlap(self) -> None:
        source = b"let x = a.(i).(j);;\n"
        direct = {
            "flyspeck:test.hl": ({
                "id": "direct-test",
                "semantic_rule": "test",
                "scope_limit": "test",
                "operations": [{"id": "test", "kind": "test"}],
                "normalized_bytes": len(source),
                "normalized_md5": "unused",
                "normalized_sha256": "unused",
            }, source),
        }
        with self.assertRaisesRegex(ValueError, "overlapping"):
            subject._normalization_record(
                "flyspeck:test.hl", source, direct,
            )

    def test_nested_array_lowering_preserves_native_behavior(self) -> None:
        original = b'''let f a =
  let n = 2 and i = 2 in
  let x = a.(n - 1).(i - 2) in
  let _ = a.(n - 2).(i - 1) <- x in
  a.(n - 2).(i - 1);;
let () = Printf.printf "%d\\n" (f [|[|1;2|];[|7;8|]|]);;
'''
        normalized, operations = subject.normalize_nested_array_access(
            original,
        )
        self.assertEqual(len(operations), 3)
        self.assertNotIn(b".(n - 1).(i - 2)", normalized)
        self.assertNotIn(b".(n - 2).(i - 1)", normalized)
        outputs = []
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, source in (("original", original),
                                 ("normalized", normalized)):
                source_path = root / f"{name}.ml"
                executable = root / name
                source_path.write_bytes(source)
                subprocess.run(
                    ["ocamlc", "-o", str(executable), str(source_path)],
                    check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                )
                result = subprocess.run(
                    [str(executable)], check=True,
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                )
                outputs.append(result.stdout)
        self.assertEqual(outputs, [b"7\n", b"7\n"])

    def test_fixed_format_lowering_preserves_native_behavior(self) -> None:
        original = b'''let emit i s b =
  print_endline (Printf.sprintf "i=%d s=%s b=%b" i s b);;
let () =
  emit 0 "" false;
  emit (-17) "alpha beta" true;
  emit min_int "punctuation: []()," false;;
'''
        normalized = b'''let emit i s b =
  print_endline
    ("i=" ^ string_of_int i ^ " s=" ^ s ^ " b=" ^
     (if b then "true" else "false"));;
let () =
  emit 0 "" false;
  emit (-17) "alpha beta" true;
  emit min_int "punctuation: []()," false;;
'''
        outputs = []
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name, source in (("original", original),
                                 ("normalized", normalized)):
                source_path = root / f"{name}.ml"
                executable = root / name
                source_path.write_bytes(source)
                subprocess.run(
                    ["ocamlc", "-o", str(executable), str(source_path)],
                    check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                )
                result = subprocess.run(
                    [str(executable)], check=True,
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                )
                outputs.append(result.stdout)
        self.assertEqual(outputs[0], outputs[1])

    def test_main_verifier_grouping_preserves_native_behavior(self) -> None:
        source = b'''module Informal_verifier = struct
  type verification_funs = {taylor:int; f:int; df:int; ddf:int}
end;;
module Informal_search = struct
  type search_options = {raw_intervals0:bool; max_width:float;
                         max_depth:int; pp:int; mono_depth:int}
end;;
let r1 = {Informal_verifier.taylor=1; Informal_verifier.f=2;
          Informal_verifier.df=3; Informal_verifier.ddf=4};;
let r2 = ({taylor=1; f=2; df=3; ddf=4} :
          Informal_verifier.verification_funs);;
let o1 = {Informal_search.raw_intervals0=true;
          Informal_search.max_width=1e-10; Informal_search.max_depth=200;
          Informal_search.pp=6; Informal_search.mono_depth=0};;
let o2 = ({raw_intervals0=true; max_width=1e-10; max_depth=200;
           pp=6; mono_depth=0} : Informal_search.search_options);;
let a = ref 0 and b = ref 0;;
let flag = true;;
let _ = a := if flag then 7 else 9;;
let _ = b := (if flag then 7 else 9);;
let () = Printf.printf "%b\n"
  (r1 = r2 && o1 = o2 && !a = !b);;
'''
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source_path = root / "grouping.ml"
            executable = root / "grouping"
            source_path.write_bytes(source)
            subprocess.run(
                ["ocamlc", "-o", str(executable), str(source_path)],
                check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            )
            result = subprocess.run(
                [str(executable)], check=True,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            )
        self.assertEqual(result.stdout, b"true\n")


if __name__ == "__main__":
    unittest.main()
