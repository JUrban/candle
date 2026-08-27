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

    def test_qualified_runtime_use_scanner_ignores_data_and_comments(self):
        source = '''
          Unix.gettimeofday ();;
          let r = Str.regexp "x";;
          (* Unix.system "ignored";; *)
          let s = "Str.split";;
          let theorem = `Unix.mkdir /\\ Str.string_match`;;
        '''
        self.assertEqual(
            flyspeck_manifest.scan_qualified_module_uses(source, {"Str", "Unix"}),
            [
                {"line": 2, "module": "Unix", "member": "gettimeofday"},
                {"line": 3, "module": "Str", "member": "regexp"},
            ],
        )

    def test_unknown_runtime_library_blocks_promotion(self):
        diagnostics = {
            key: [] for key in flyspeck_manifest.PROMOTION_EMPTY_DIAGNOSTICS
        }
        diagnostics.update({
            key: 0 for key in flyspeck_manifest.PROMOTION_ZERO_DIAGNOSTICS
        })
        diagnostics["unsupported_runtime_libraries"] = [
            {"source": "flyspeck:x.ml", "line": 1, "library": "evil.cma"},
        ]
        self.assertEqual(
            flyspeck_manifest.promotion_blockers(diagnostics),
            ["unsupported_runtime_libraries"],
        )

    def test_opened_module_uses_are_not_lost(self):
        source = '''
          open Str;;
          let split_words = split (regexp " +");;
          let qualified = Str.global_replace;;
          let data = "string_match regexp";;
          (* bounded_split is not used *)
        '''
        opens, uses = flyspeck_manifest.scan_opened_module_uses(
            source, flyspeck_manifest.OPENED_MODULE_EXPORTS,
        )
        self.assertEqual(opens, [{"line": 2, "module": "Str"}])
        self.assertEqual(
            [(use["line"], use["module"], use["member"]) for use in uses],
            [(3, "Str", "split"), (3, "Str", "regexp")],
        )
        self.assertEqual(
            {use["attribution_status"] for use in uses},
            {"lexical-reviewed-not-compiler-proved"},
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
        self.assertEqual(self.payload["source_edge_count"], 417)
        self.assertNotIn("flyspeck:load_flyspeck.ml", self.payload["source_nodes"])
        self.assertEqual(
            self.payload["bootstrap_roots"],
            [
                "candle:hol.ml",
                "flyspeck:text_formalization/build/strictbuild.hl",
            ],
        )

    def test_diagnostics_are_promotion_gates(self):
        diagnostics = self.payload["diagnostics"]
        for key in (
            "unresolved_build_roots",
            "cycles",
            "unsupported_runtime_libraries",
            "unsupported_runtime_members",
            "unsupported_compatibility_members",
        ):
            self.assertEqual(diagnostics[key], [])
        for key in (
            "dynamic_dependencies",
            "missing_dependencies",
            "ambiguous_dependencies",
            "forbidden_dependencies",
        ):
            self.assertEqual(diagnostics[key], 0)
        self.assertEqual(diagnostics["reviewed_dynamic_dependencies"], 15)
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
            {"generated-contract", "generated-runtime"},
        )
        self.assertEqual(
            {contract["source"] for contract in contracts},
            {
                "candle:hol_lib.ml",
                "flyspeck:text_formalization/general/serialization.hl",
            },
        )
        self.assertNotIn("candle:candle/build/insulate.ml", self.payload["source_nodes"])

    def test_final_target_is_direct_source_only(self):
        target = self.payload["final_target"]
        self.assertEqual(target["source"], "candle:candle/flyspeck_l2_target.ml")
        source = Path(__file__).with_name("flyspeck_l2_target.ml").read_text(encoding="utf-8")
        for forbidden in ("PFT", "pft", "save_pft", "new_axiom", "mk_thm"):
            self.assertNotIn(forbidden, source)
        self.assertIn("Candle_flyspeck_l2", source)
        self.assertIn("import_tame_classification", source)

    def test_loader_has_a_fail_closed_build_mode(self):
        loader = self.payload["loader"]
        self.assertEqual(loader["source"], "candle:candle/flyspeck_loader.ml")
        self.assertEqual(loader["required_build_mode"], "full")
        self.assertEqual(
            loader["configuration_bindings"],
            [
                "candle_hollight_root", "candle_flyspeck_root",
                "candle_flyspeck_build_mode",
            ],
        )
        source = Path(__file__).with_name("flyspeck_loader.ml").read_text(encoding="utf-8")
        self.assertIn('candle_flyspeck_build_mode must be full', source)
        self.assertIn('needs "build/strictbuild.hl"', source)
        self.assertIn("Build.build_sequence_full", source)
        self.assertIn('needs "candle/flyspeck_l2_target.ml"', source)
        for forbidden in ("PFT", "pft", "new_axiom", "mk_thm"):
            self.assertNotIn(forbidden, source)

    def test_static_library_contract_is_exact_and_inactive(self):
        contract = self.payload["static_library_contract"]
        self.assertEqual(
            contract["activation_status"],
            "blocked-pending-static-binding-evidence",
        )
        self.assertIn("no-op is forbidden", contract["directive_policy"])
        self.assertEqual(
            contract["library_modules"],
            {"str.cma": "Str", "unix.cma": "Unix"},
        )
        directives = contract["directives"]
        self.assertEqual(len(directives), 5)
        self.assertEqual(
            {directive["library"] for directive in directives},
            {"str.cma", "unix.cma"},
        )
        self.assertEqual(
            {directive["library"]: sum(d["library"] == directive["library"] for d in directives)
             for directive in directives},
            {"str.cma": 3, "unix.cma": 2},
        )
        uses = contract["qualified_uses"]
        self.assertTrue(uses)
        self.assertEqual({use["module"] for use in uses}, {"Str", "Unix"})
        self.assertEqual({use["library"] for use in uses}, {"str.cma", "unix.cma"})
        self.assertEqual(len(uses), 39)
        opened_uses = contract["opened_module_uses"]
        self.assertEqual(len(opened_uses), 3)
        self.assertEqual(
            [(use["line"], use["member"]) for use in opened_uses],
            [(137, "regexp"), (138, "global_replace"), (138, "regexp")],
        )
        self.assertEqual(len(contract["capability_uses"]), 42)
        self.assertIn("not a compiler name-resolution proof", contract["opened_use_attribution"])
        self.assertEqual(
            {use["attribution_status"] for use in opened_uses},
            {"lexical-reviewed-not-compiler-proved"},
        )
        self.assertEqual(
            {(entry["source"], entry["line"], entry["module"])
             for entry in contract["module_opens"]},
            {
                ("flyspeck:formal_lp/glpk/glpk_link.ml", 31, "Str"),
                ("flyspeck:formal_lp/hypermap/computations/"
                 "list_hypermap_computations.hl", 11, "Str"),
            },
        )
        for entry in directives + contract["capability_uses"]:
            self.assertRegex(entry["source"], r"^(candle|flyspeck):")
            self.assertGreater(entry["line"], 0)

    def test_static_binding_evidence_is_partial_and_source_backed(self):
        evidence = self.payload["static_library_contract"]["binding_evidence"]
        self.assertEqual(
            evidence["str.cma"]["status"],
            "partial-pure-source-differential-gate",
        )
        self.assertEqual(
            evidence["unix.cma"]["status"],
            "startup-metadata-only-explicit-fail-otherwise",
        )
        source = Path(__file__).with_name("ocaml.ml").read_text(encoding="utf-8")
        self.assertIn("module Str = struct", source)
        for member in evidence["str.cma"]["members"]:
            self.assertRegex(source, rf"\blet\s+{member}\b")
        self.assertIn("module Unix = struct", source)
        for member in evidence["unix.cma"]["members"]:
            self.assertRegex(source, rf"\blet\s+{member}\b")
        self.assertIn("module Buffer = struct", source)
        for member in ("create", "add_channel", "add_string", "contents", "reset"):
            self.assertRegex(source, rf"\blet(?:\s+rec)?\s+{member}\b")
        self.assertEqual(evidence["unix.cma"]["source"], "candle:candle/ocaml.ml")
        self.assertEqual(
            evidence["unix.cma"]["gate"],
            "candle:candle/test_unix_metadata.sh",
        )
        self.assertEqual(
            evidence["unix.cma"]["deterministic_process_inputs"],
            [
                {
                    "command": "date",
                    "source": "candle:candle/flyspeck_metadata/date.txt",
                    "bytes": 21,
                    "sha256": (
                        "8f2148c336b70d69d770cd80e0f3decc"
                        "5a1c9716fac2fc7961f7a5b2d57701e8"
                    ),
                },
                {
                    "command": "whoami",
                    "source": "candle:candle/flyspeck_metadata/user.txt",
                    "bytes": 16,
                    "sha256": (
                        "ad29b534dd27882add87d6996aa4ccf39"
                        "bf1e5b15ccfd08804636905e8b8d864"
                    ),
                },
            ],
        )

    def test_digest_compatibility_contract_is_exact_and_source_backed(self):
        contract = self.payload["ocaml_compatibility_contract"]
        self.assertEqual(contract["activation_status"], "partial-source-bindings")
        self.assertEqual(
            contract["supported_members"]["Digest"],
            ["compare", "file", "string", "t", "to_hex"],
        )
        self.assertEqual(
            contract["selected_members"]["Digest"],
            ["file", "string", "t", "to_hex"],
        )
        uses = contract["qualified_uses"]
        self.assertEqual(len(uses), 13)
        self.assertEqual(contract["opened_module_uses"], [])
        self.assertEqual(contract["module_opens"], [])
        self.assertEqual(
            {member: sum(use["member"] == member for use in uses)
             for member in {use["member"] for use in uses}},
            {"file": 6, "string": 2, "t": 3, "to_hex": 2},
        )
        evidence = contract["binding_evidence"]["Digest"]
        self.assertEqual(evidence["status"], "pure-source-differential-gate")
        self.assertEqual(evidence["source"], "candle:candle/ocaml.ml")
        self.assertEqual(evidence["gate"], "candle:candle/test_digest_compat.sh")
        self.assertIn("not yet formally linked", evidence["assurance_limit"])
        source = Path(__file__).with_name("ocaml.ml").read_text(encoding="utf-8")
        self.assertIn("module Digest = struct", source)
        for member in contract["supported_members"]["Digest"]:
            if member != "t":
                self.assertRegex(source, rf"\blet(?:\s+rec)?\s+{member}\b")


if __name__ == "__main__":
    unittest.main()
