import json
import tempfile
import unittest
from pathlib import Path

import flyspeck_manifest


class SyntaxTests(unittest.TestCase):
    def test_nested_comments_and_build_sequence(self):
        source = '''
          (* ["ignored"] (* needs "ignored.ml";; *) *)
          let build_sequence_full = ["a.ml"; "b.hl";];;
        '''
        self.assertEqual(
            flyspeck_manifest.extract_full_build_sequence(source),
            ["a.ml", "b.hl"],
        )

    def test_literal_dynamic_directive_and_definition_calls(self):
        source = '''
          let needs s = s;;
          needs "a.ml";;
          needs ("b.hl");;
          needs (Filename.concat root "c.hl");;
          #use "d.ml";;
          #load "unix.cma";;
          (* loads "ignored.ml";; *)
        '''
        calls = flyspeck_manifest.scan_load_calls(source)
        self.assertEqual(
            [(call["kind"], call.get("literal")) for call in calls],
            [
                ("needs", "a.ml"),
                ("needs", "b.hl"),
                ("needs", None),
                ("#use", "d.ml"),
                ("#load", "unix.cma"),
            ],
        )

    def test_resolution_precedence_and_path_policy(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            candle = root / "candle"
            flyspeck = root / "flyspeck"
            (candle / "Library").mkdir(parents=True)
            (flyspeck / "text_formalization/Library").mkdir(parents=True)
            (flyspeck / "formal_ineqs").mkdir()
            (flyspeck / "jHOLLight").mkdir()
            (candle / "Library/x.ml").write_text("candle", encoding="utf-8")
            (flyspeck / "text_formalization/Library/x.ml").write_text("flyspeck", encoding="utf-8")
            resolver = flyspeck_manifest.Resolver(candle, flyspeck)
            matches, error = resolver.resolve("Library/x.ml")
            self.assertIsNone(error)
            self.assertEqual(
                [match.key for match in matches],
                ["flyspeck:text_formalization/Library/x.ml", "candle:Library/x.ml"],
            )
            self.assertEqual(resolver.resolve("/tmp/x.ml"), ([], "absolute source dependency"))


class GeneratedManifestTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = Path(__file__).with_name("flyspeck_manifest.json")
        cls.payload = json.loads(path.read_text(encoding="utf-8"))

    def test_manifest_scope_is_explicit(self):
        self.assertEqual(self.payload["schema"], 1)
        self.assertEqual(self.payload["build_mode"], "full")
        self.assertIn("not loader execution evidence", self.payload["claim"])
        self.assertEqual(self.payload["build_sequence_count"], 297)
        self.assertEqual(self.payload["build_sequence_unique_count"], 287)
        self.assertEqual(len(self.payload["build_sequence_roots"]), 297)
        self.assertEqual(self.payload["source_node_count"], 398)
        self.assertGreater(self.payload["source_edge_count"], 300)

    def test_diagnostics_are_promotion_gates(self):
        diagnostics = self.payload["diagnostics"]
        for key in (
            "unresolved_build_roots",
            "cycles",
        ):
            self.assertEqual(diagnostics[key], [])
        for key in (
            "dynamic_dependencies",
            "missing_dependencies",
            "ambiguous_dependencies",
            "forbidden_dependencies",
        ):
            self.assertEqual(diagnostics[key], 0)
        self.assertEqual(diagnostics["reviewed_dynamic_dependencies"], 16)
        self.assertEqual(diagnostics["generated_dependencies"], 1)

    def test_manifest_has_no_absolute_source_identity(self):
        serialized = json.dumps(self.payload)
        self.assertNotIn("/project/", serialized)

    def test_every_node_and_generated_input_is_hashed(self):
        for node in self.payload["source_nodes"].values():
            self.assertRegex(node["sha256"], r"^[0-9a-f]{64}$")
        for generated in self.payload["generated_inputs"]:
            self.assertRegex(generated["sha256"], r"^[0-9a-f]{64}$")

    def test_generated_runtime_dependencies_remain_explicit(self):
        contracts = self.payload["generated_dependency_contracts"]
        self.assertEqual(len(contracts), 2)
        self.assertEqual(
            {contract["status"] for contract in contracts},
            {"generated-missing", "generated-runtime"},
        )
        self.assertEqual(
            {contract["source"] for contract in contracts},
            {
                "candle:hol_lib.ml",
                "flyspeck:text_formalization/general/serialization.hl",
            },
        )

    def test_final_target_is_direct_source_only(self):
        target = self.payload["final_target"]
        self.assertEqual(target["source"], "candle:candle/flyspeck_l2_target.ml")
        source = Path(__file__).with_name("flyspeck_l2_target.ml").read_text(encoding="utf-8")
        for forbidden in ("PFT", "pft", "save_pft", "new_axiom", "mk_thm"):
            self.assertNotIn(forbidden, source)
        self.assertIn("Candle_flyspeck_l2", source)
        self.assertIn("import_tame_classification", source)


if __name__ == "__main__":
    unittest.main()
