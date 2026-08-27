import json
import tempfile
import unittest
from pathlib import Path

import flyspeck_manifest
import flyspeck_normalize


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
          if enabled then needs "e.ml";;
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
                ("needs", "e.ml"),
            ],
        )
        self.assertEqual(
            [call["syntax_position"] for call in calls],
            [
                "standalone-phrase", "standalone-phrase",
                "standalone-phrase", "standalone-phrase",
                "standalone-phrase", "embedded-expression",
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

    def test_identifier_scanner_ignores_data_and_comments(self):
        source = '''
          let use_arg_then x = x;;
          update_database ();;
          (* search_thml use_arg_then *)
          let s = "update_database search";;
          let theorem = `search_thml`;;
        '''
        self.assertEqual(
            flyspeck_manifest.scan_identifier_uses(
                source, {"search_thml", "update_database", "use_arg_then"},
            ),
            [
                {"line": 2, "identifier": "use_arg_then"},
                {"line": 3, "identifier": "update_database"},
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
        self.assertEqual(self.payload["source_node_count"], 399)
        self.assertEqual(self.payload["source_edge_count"], 418)
        self.assertNotIn("flyspeck:load_flyspeck.ml", self.payload["source_nodes"])
        self.assertEqual(
            self.payload["bootstrap_roots"],
            [
                "candle:hol.ml",
                "flyspeck:text_formalization/build/strictbuild.hl",
            ],
        )

    def test_build_strata_cover_order_and_dependency_graph(self):
        strata = self.payload["build_strata"]
        self.assertEqual(
            [entry["name"] for entry in strata],
            [
                "base", "arithmetic", "nonlinear_support", "analysis",
                "geometry", "lp_support", "text_formalization",
                "final_assembly",
            ],
        )
        expected_index = 0
        covered = 0
        for entry in strata:
            self.assertEqual(entry["start_index"], expected_index)
            self.assertEqual(
                entry["entry_count"],
                entry["end_index"] - entry["start_index"] + 1,
            )
            self.assertEqual(
                entry["first"],
                self.payload["build_sequence"][entry["start_index"]],
            )
            self.assertEqual(
                entry["last"],
                self.payload["build_sequence"][entry["end_index"]],
            )
            self.assertRegex(entry["ordered_root_sha256"], r"^[0-9a-f]{64}$")
            self.assertGreater(entry["transitive_source_node_count"], 0)
            expected_index = entry["end_index"] + 1
            covered += entry["entry_count"]
        self.assertEqual(covered, self.payload["build_sequence_count"])
        self.assertEqual(expected_index, self.payload["build_sequence_count"])

        memberships = self.payload["source_node_strata"]
        self.assertEqual(set(memberships), set(self.payload["source_nodes"]))
        allowed = {entry["name"] for entry in strata}
        for membership in memberships.values():
            self.assertTrue(membership)
            self.assertLessEqual(set(membership), allowed)
        self.assertIn("base", memberships["candle:hol.ml"])
        self.assertIn(
            "final_assembly",
            memberships["candle:candle/flyspeck_l2_target.ml"],
        )

    def test_static_full_build_program_is_exact_and_fail_closed(self):
        contract = self.payload["static_full_build_contract"]
        self.assertEqual(
            contract["activation_status"],
            "generated-fail-closed-pending-loader-action",
        )
        self.assertEqual(contract["directive"], "#flyspeck_needs")
        self.assertEqual(contract["entry_count"], 297)
        self.assertEqual(contract["unique_target_count"], 287)
        self.assertIn("neutralize_state exactly once", contract["required_loader_action"])
        self.assertIn("already-loaded duplicate", contract["required_loader_action"])
        self.assertIn("evaluator false", contract["failure_policy"])
        self.assertIn("neutralization exception", contract["failure_policy"])
        self.assertIn("fail-closed refinement", contract["assurance_limit"])
        self.assertIn("before strictbuild", contract["preload_authentication"])

        generated = Path(__file__).with_name("flyspeck_full_build.ml")
        self.assertTrue(generated.is_file())
        self.assertEqual(
            flyspeck_manifest._sha256(generated),
            contract["generated_source_sha256"],
        )
        source = generated.read_text(encoding="utf-8")
        directives = [
            line for line in source.splitlines()
            if line.startswith("#flyspeck_needs ")
        ]
        self.assertEqual(len(directives), contract["entry_count"])
        targets = [
            json.loads(line[len("#flyspeck_needs "):-2])
            for line in directives
        ]
        self.assertEqual(targets, self.payload["build_sequence"])
        for index, root in enumerate(self.payload["build_sequence_roots"]):
            node = self.payload["source_nodes"][root["selected"]]
            marker = (
                f"(* {index:03d} selected={root['selected']} "
                f"sha256={node['sha256']}"
            )
            normalization = node.get("execution_normalization")
            if normalization:
                marker += (
                    f" normalization={normalization['id']} "
                    f"normalized_sha256={normalization['normalized_sha256']}"
                )
            marker += " *)"
            self.assertIn(marker, source)

    def test_source_normalizations_are_exact_and_narrow(self):
        contract = self.payload["source_normalization_contract"]
        self.assertEqual(
            contract["activation_status"],
            "ready-pending-compiled-loader-integration",
        )
        self.assertEqual(contract["entry_count"], 4)
        self.assertIn("every anchor must occur once", contract["input_policy"])
        self.assertIn("before parsing", contract["output_policy"])
        self.assertIn("qmap", contract["scope_limit"])
        contract_path = Path(__file__).with_name("flyspeck_normalizations.json")
        self.assertEqual(
            flyspeck_normalize.contract_sha256(contract_path),
            contract["contract_sha256"],
        )
        entries = {entry["id"]: entry for entry in contract["entries"]}
        entry = entries["PROJECT-POINTER-S3-IMMEDIATE-001"]
        self.assertEqual(entry["source_key"], (
            "flyspeck:formal_lp/hypermap/main/prove_flyspeck_lp.hl"
        ))
        self.assertEqual(entry["operations"][0]["line"], 1050)
        node = self.payload["source_nodes"][entry["source_key"]]
        self.assertEqual(node["sha256"], entry["source_sha256"])
        self.assertEqual(node["md5"], entry["source_md5"])
        self.assertEqual(
            node["execution_normalization"]["normalized_sha256"],
            entry["normalized_sha256"],
        )
        normalized_nodes = [
            key for key, value in self.payload["source_nodes"].items()
            if "execution_normalization" in value
        ]
        self.assertEqual(set(normalized_nodes), {
            value["source_key"] for value in entries.values()
        })
        self.assertEqual(
            entries["PROJECT-POINTER-S3-ALLOCATED-LIB-001"]["operation_count"],
            5,
        )
        self.assertIn(
            "failwith",
            entries["PROJECT-POINTER-S3-UNSUPPRESS-001"]["operations"][0]["after"],
        )
        non_use = contract["selected_graph_non_use_bindings"]
        self.assertEqual(non_use["identifiers"], ["qmap", "unsuppress"])
        self.assertEqual(
            [
                (site["identifier"], site["role"])
                for site in non_use["reviewed_occurrences"]
            ],
            [
                ("qmap", "definition"),
                ("qmap", "recursive-body"),
                ("unsuppress", "signature"),
                ("unsuppress", "definition"),
            ],
        )
        self.assertIn("any caller occurrence aborts", non_use["policy"])
        self.assertIn(
            "candle:candle/test_flyspeck_identity_normalization.sh",
            contract["gates"],
        )
        self.assertEqual(
            contract["performance_probe"],
            "candle:candle/flyspeck_identity_benchmark.ml",
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
        self.assertEqual(diagnostics["generated_dependencies"], 2)

    def test_manifest_has_no_absolute_source_identity(self):
        serialized = json.dumps(self.payload)
        self.assertNotIn("/project/", serialized)

    def test_every_node_and_generated_input_is_hashed(self):
        for node in self.payload["source_nodes"].values():
            self.assertRegex(node["md5"], r"^[0-9a-f]{32}$")
            self.assertRegex(node["sha256"], r"^[0-9a-f]{64}$")
        for generated in self.payload["generated_inputs"]:
            self.assertRegex(generated["sha256"], r"^[0-9a-f]{64}$")

    def test_generated_runtime_dependencies_remain_explicit(self):
        contracts = self.payload["generated_dependency_contracts"]
        self.assertEqual(len(contracts), 3)
        self.assertEqual(
            {contract["status"] for contract in contracts},
            {"generated-contract", "generated-runtime"},
        )
        self.assertEqual(
            {contract["source"] for contract in contracts},
            {
                "candle:hol_lib.ml",
                "candle:candle/flyspeck_loader.ml",
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
        self.assertIn('needs "candle/flyspeck_source_digests.ml"', source)
        self.assertIn("candle_flyspeck_verify_sources 398", source)
        self.assertIn(
            self.payload["source_digest_contract"]["generated_source_md5"],
            source,
        )
        self.assertIn(
            self.payload["static_full_build_contract"]["generated_source_md5"],
            source,
        )
        self.assertIn("static full-build program authentication failed", source)
        self.assertIn("Build.build_sequence_full", source)
        self.assertIn('needs "candle/flyspeck_l2_target.ml"', source)
        for forbidden in ("PFT", "pft", "new_axiom", "mk_thm"):
            self.assertNotIn(forbidden, source)

    def test_source_digest_contract_is_complete_and_preflighted(self):
        contract = self.payload["source_digest_contract"]
        self.assertEqual(contract["activation_status"], "preflight-before-strictbuild")
        self.assertEqual(contract["entry_count"], self.payload["source_node_count"] - 1)
        self.assertEqual(
            contract["bootstrap_exclusions"],
            ["candle:candle/flyspeck_loader.ml"],
        )
        self.assertEqual(
            contract["generated_source"],
            "candle:candle/flyspeck_source_digests.ml",
        )
        self.assertRegex(contract["generated_source_sha256"], r"^[0-9a-f]{64}$")
        self.assertRegex(contract["generated_source_md5"], r"^[0-9a-f]{32}$")
        generated = Path(__file__).with_name("flyspeck_source_digests.ml")
        self.assertTrue(generated.is_file())
        self.assertEqual(
            flyspeck_manifest._sha256(generated),
            contract["generated_source_sha256"],
        )
        source = generated.read_text(encoding="utf-8")
        self.assertEqual(source.count('\n  ("'), contract["entry_count"])
        self.assertNotIn(
            '("candle","candle/flyspeck_loader.ml",',
            source,
        )
        integrity = Path(__file__).with_name(
            "flyspeck_source_integrity.ml"
        ).read_text(encoding="utf-8")
        self.assertIn("Digest.file", integrity)
        self.assertIn("source digest mismatch before Flyspeck build", integrity)

    def test_static_library_contract_has_exact_static_selection(self):
        contract = self.payload["static_library_contract"]
        self.assertEqual(
            contract["activation_status"],
            "exact-static-link-selection-active-member-compatibility-partial",
        )
        self.assertIn("complete standalone #load phrase", contract["directive_policy"])
        self.assertIn("not full member compatibility", contract["directive_policy"])
        self.assertEqual(
            contract["activation_source"],
            "cakeml:candle/prover/candle_boot.ml",
        )
        self.assertEqual(
            contract["activation_gate"],
            "candle:candle/test_static_load_directive.sh",
        )
        self.assertEqual(
            contract["member_compatibility_status"],
            "partial-and-fail-closed-as-recorded-per-library",
        )
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
        self.assertEqual(len(uses), 19)
        self.assertEqual(contract["opened_module_uses"], [])
        self.assertEqual(contract["module_opens"], [])
        self.assertEqual(
            {member: sum(use["member"] == member for use in uses)
             for member in {use["member"] for use in uses}},
            {"file": 9, "string": 2, "t": 3, "to_hex": 5},
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

    def test_toplevel_interface_contract_is_exact_and_fail_closed(self):
        contract = self.payload["toplevel_interface_contract"]
        self.assertEqual(contract["activation_status"], "blocked-no-dummy-or-no-op")
        self.assertIn("dummy return", contract["policy"])
        uses = contract["qualified_uses"]
        self.assertEqual(len(uses), 133)
        self.assertEqual(
            {module: sum(use["module"] == module for use in uses)
             for module in {use["module"] for use in uses}},
            {"Format": 106, "Lexing": 5, "Obj": 3, "Toploop": 19},
        )
        self.assertEqual(
            contract["unbound_members"]["Format"],
            ["formatter_of_buffer", "pp_set_margin", "sprintf", "std_formatter"],
        )
        self.assertEqual(contract["unbound_members"]["Lexing"], ["from_string"])
        self.assertEqual(contract["unbound_members"]["Obj"], ["magic"])
        self.assertEqual(
            contract["unbound_members"]["Toploop"],
            [
                "String", "execute_phrase", "getvalue", "parse_toplevel_phrase",
                "parse_use_file", "toplevel_env", "use_file", "use_silently",
            ],
        )
        selection = contract["conditional_source_selection"]
        self.assertEqual(selection["pinned_ocaml_version"], "4.14.1")
        self.assertTrue(selection["selected"].endswith("update_database_400.ml"))
        self.assertTrue(selection["unselected"].endswith("update_database_310.ml"))
        payloads = contract["dynamic_source_payloads"]
        self.assertEqual([payload["line"] for payload in payloads], [60, 134, 186, 193])
        for payload in payloads:
            self.assertIn(payload["source"], self.payload["source_nodes"])
            self.assertGreater(payload["line"], 0)
        consumers = contract["consumer_inventory"]
        self.assertEqual(len(consumers["reviewed_occurrences"]), 20)
        self.assertEqual(
            consumers["identifier_counts"],
            {
                "eval_command": 1,
                "save_all_theorems": 1,
                "search": 2,
                "search_thml": 4,
                "test_id_thm": 1,
                "theorems": 4,
                "update_database": 6,
                "use_arg_then": 1,
            },
        )
        active = consumers["selected_active_site"]
        self.assertTrue(active["source"].endswith("update_database_400.ml"))
        self.assertEqual(active["line"], 338)
        self.assertEqual(active["identifier"], "update_database")
        typed = consumers["typed_theorem_lookup"]
        self.assertEqual(typed["identifier"], "use_arg_then2")
        self.assertEqual(typed["occurrences"], 23810)
        self.assertEqual(typed["source_files"], 22)
        self.assertIn("does not call Toploop", typed["distinction"])
        self.assertIn("not a proof", consumers["assurance_limit"])

    def test_loader_action_contract_preserves_distinct_semantics(self):
        contract = self.payload["loader_action_contract"]
        self.assertEqual(
            contract["activation_status"],
            "blocked-exact-token-actions-not-integrated",
        )
        self.assertEqual(contract["source_site_count"], 434)
        self.assertEqual(contract["generated_static_root_directives"], 297)
        self.assertEqual(
            {
                (entry["kind"], entry["position"]): entry["count"]
                for entry in contract["syntax_position_counts"]
            },
            {
                ("#load", "standalone-phrase"): 5,
                ("#use", "standalone-phrase"): 1,
                ("flyspeck_needs", "embedded-expression"): 4,
                ("flyspeck_needs", "standalone-phrase"): 144,
                ("loads", "standalone-phrase"): 54,
                ("loadt", "embedded-expression"): 3,
                ("loadt", "standalone-phrase"): 3,
                ("needs", "embedded-expression"): 4,
                ("needs", "standalone-phrase"): 215,
                ("reneeds", "embedded-expression"): 1,
            },
        )
        actions = contract["required_actions"]
        self.assertIn("neutralize state exactly once", actions["flyspeck_needs"])
        self.assertIn("do neither", actions["flyspeck_needs"])
        self.assertIn("generated index", actions["#flyspeck_needs"])
        self.assertNotEqual(actions["loads"], actions["needs"])
        self.assertIn("both sides", contract["embedded_expression_policy"])
        self.assertIn("definition or expression", contract["known_current_boot_defect"])


if __name__ == "__main__":
    unittest.main()
