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
        self.assertEqual(counts["normalized_sources"], 4)
        self.assertEqual(counts["normalization_operations"], 45)

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
        self.assertEqual(set(normalized), {
            "flyspeck:formal_ineqs/taylor/m_taylor.hl",
            "flyspeck:formal_ineqs/taylor/m_taylor_arith2.hl",
            "flyspeck:formal_ineqs/verifier/m_verifier.hl",
            "flyspeck:formal_ineqs/verifier/m_verifier_main.hl",
        })
        self.assertEqual(
            sum(record["operation_count"] for record in normalized.values()),
            45,
        )
        self.assertEqual(
            sum(
                operation["kind"] == "nested-array-set"
                for record in normalized.values()
                for operation in record["operations"]
            ),
            1,
        )
        self.assertTrue(all(
            record["id"] == subject.SOURCE_NORMALIZATION
            for record in normalized.values()
        ))
        main = normalized[
            "flyspeck:formal_ineqs/verifier/m_verifier_main.hl"
        ]
        self.assertEqual(main["operation_count"], 4)
        self.assertEqual(
            {operation["kind"] for operation in main["operations"]},
            {kind for kind, _, _ in subject.MAIN_VERIFIER_GROUPING_REPLACEMENTS},
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
