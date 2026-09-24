#!/usr/bin/env python3

import json
from collections import Counter
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
FLYSPECK_ROOT = Path(
    "/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6"
)
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
        self.assertEqual(counts["normalized_sources"], 29)
        self.assertEqual(counts["normalization_operations"], 170)

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

    def test_float_runtime_identifier_surface_is_accounted_for(self) -> None:
        compatibility = self.payload["compatibility"]
        self.assertEqual(
            compatibility["float_runtime_identifier_resolution"],
            subject.FLOAT_RUNTIME_IDENTIFIER_RESOLUTION,
        )
        uses = compatibility["float_runtime_identifier_uses"]
        self.assertEqual(
            compatibility["float_runtime_identifier_use_count"], 94,
        )
        self.assertEqual(
            Counter(use["identifier"] for use in uses),
            Counter({
                "abs_float": 13,
                "atan": 4,
                "float_of_int": 42,
                "float_of_string": 2,
                "floor": 4,
                "infinity": 2,
                "int_of_float": 19,
                "log": 6,
                "nan": 2,
            }),
        )
        self.assertTrue(all(
            use["resolution"] ==
            subject.FLOAT_RUNTIME_IDENTIFIER_RESOLUTION[use["identifier"]]
            for use in uses
        ))
        atan_sites = {
            (use["source"], use["line"])
            for use in uses if use["identifier"] == "atan"
        }
        self.assertEqual(atan_sites, {
            ("flyspeck:formal_ineqs/informal/informal_sin_cos.hl", 58),
            ("flyspeck:formal_ineqs/informal/informal_sin_cos.hl", 62),
            ("flyspeck:formal_ineqs/trig/cos_bounds_eval.hl", 109),
            ("flyspeck:formal_ineqs/trig/cos_bounds_eval.hl", 119),
        })

    def test_binary64_absolute_sites_use_the_authenticated_helper(self) -> None:
        expected = {
            "flyspeck:formal_ineqs/trig/exp_eval.hl": (
                "exp-eval-binary64-absolute",
                "abs_float (float_of_float_tm x_tm)",
                "candle_binary64_abs (float_of_float_tm x_tm)",
                345,
            ),
            "flyspeck:formal_ineqs/informal/informal_exp.hl": (
                "informal-exp-binary64-absolute",
                "Stdlib.abs_float (float_of_ifloat x)",
                "candle_binary64_abs (float_of_ifloat x)",
                133,
            ),
        }
        for source_key, (kind, before, after, line) in expected.items():
            node = self.payload["source_nodes"][source_key]
            operations = [
                operation
                for operation in node["normalization"]["operations"]
                if operation["kind"] == kind
            ]
            self.assertEqual(len(operations), 1, source_key)
            self.assertEqual(operations[0]["before"], before)
            self.assertEqual(operations[0]["after"], after)
            self.assertEqual(operations[0]["line"], line)
            self.assertEqual(operations[0]["replacement_count"], 1)
            self.assertEqual(
                node["normalization"]["id"], subject.SOURCE_NORMALIZATION,
            )

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
        self.assertEqual(main["operation_count"], 5)

        m_taylor = parser_normalized[
            "flyspeck:formal_ineqs/taylor/m_taylor.hl"
        ]
        finite_type = [
            operation for operation in m_taylor["operations"]
            if operation["kind"] == "modern-finite-type-size-theorem"
        ]
        self.assertEqual(len(finite_type), 1)
        component_variable = [
            operation for operation in m_taylor["operations"]
            if operation["kind"] ==
            "taylor-component-variable-tuple-grouping"
        ]
        self.assertEqual(len(component_variable), 1)
        self.assertEqual(component_variable[0]["replacement_count"], 1)
        self.assertIn(
            'let name = "x" ^ string_of_int i in',
            component_variable[0]["after"],
        )
        self.assertIn("mk_var (name,aty)", component_variable[0]["after"])
        verifier = parser_normalized[
            "flyspeck:formal_ineqs/verifier/m_verifier.hl"
        ]
        verifier_variable_grouping = [
            operation for operation in verifier["operations"]
            if operation["kind"] == "verifier-variable-tuple-grouping"
        ]
        self.assertEqual(len(verifier_variable_grouping), 1)
        self.assertEqual(
            verifier_variable_grouping[0]["replacement_count"], 4,
        )
        self.assertIn(
            "let variable_name = name ^ string_of_int i in",
            verifier_variable_grouping[0]["after"],
        )
        self.assertIn(
            "mk_var (variable_name, real_ty)",
            verifier_variable_grouping[0]["after"],
        )
        canonical_modern_source = (
            ROOT / "Formal_ineqs/taylor/m_taylor.hl"
        ).read_text(encoding="utf-8")
        self.assertEqual(
            finite_type[0]["after"],
            "| _ -> HAS_SIZE_DIMINDEX_RULE(mk_finty(Num.num_of_int i)));;",
        )
        self.assertIn(finite_type[0]["after"], canonical_modern_source)
        self.assertEqual(
            {operation["kind"] for operation in main["operations"]},
            {
                *(kind for kind, _, _ in
                  subject.MAIN_VERIFIER_GROUPING_REPLACEMENTS),
                "array-to-list-compatibility",
            },
        )

    def test_array_to_list_uses_are_lowered_to_the_authenticated_helper(
        self,
    ) -> None:
        for source_key, count in (
            subject.ARRAY_TO_LIST_COMPATIBILITY_COUNTS.items()
        ):
            node = self.payload["source_nodes"][source_key]
            operation = next(
                operation
                for operation in node["normalization"]["operations"]
                if operation["kind"] == "array-to-list-compatibility"
            )
            self.assertEqual(operation["before"], "Array.to_list")
            self.assertEqual(operation["after"], "candle_array_to_list")
            self.assertEqual(operation["replacement_count"], count)
            normalized, _ = subject.normalize_source(
                source_key,
                (FLYSPECK_ROOT / node["logical_relative_path"]).read_bytes(),
            )
            self.assertNotIn(b"Array.to_list", normalized)
            self.assertEqual(normalized.count(b"candle_array_to_list"), count)

    def test_qualified_ignore_uses_the_authenticated_discard_helper(
        self,
    ) -> None:
        for source_key, count in subject.IGNORE_COMPATIBILITY_COUNTS.items():
            node = self.payload["source_nodes"][source_key]
            operation = next(
                operation
                for operation in node["normalization"]["operations"]
                if operation["kind"] == "qualified-ignore-compatibility"
            )
            self.assertEqual(operation["before"], "Stdlib.ignore")
            self.assertEqual(operation["after"], "candle_ignore")
            self.assertEqual(operation["replacement_count"], count)
            normalized, _ = subject.normalize_source(
                source_key,
                (FLYSPECK_ROOT / node["logical_relative_path"]).read_bytes(),
            )
            self.assertNotIn(b"Stdlib.ignore", normalized)
            self.assertEqual(normalized.count(b"candle_ignore"), count)

    def test_late_printers_use_the_authenticated_standard_formatter(
        self,
    ) -> None:
        for source_key, count in (
            subject.STD_FORMATTER_COMPATIBILITY_COUNTS.items()
        ):
            node = self.payload["source_nodes"][source_key]
            operation = next(
                operation
                for operation in node["normalization"]["operations"]
                if operation["kind"] == "standard-formatter-compatibility"
            )
            self.assertEqual(operation["before"], "Format.std_formatter")
            self.assertEqual(operation["after"], "candle_std_formatter")
            self.assertEqual(operation["replacement_count"], count)
            normalized, _ = subject.normalize_source(
                source_key,
                (FLYSPECK_ROOT / node["logical_relative_path"]).read_bytes(),
            )
            self.assertNotIn(b"Format.std_formatter", normalized)
            self.assertEqual(normalized.count(b"candle_std_formatter"), count)
        ssreflect = self.payload["source_nodes"][
            "flyspeck:formal_ineqs/lib/ssreflect/ssreflect.hl"
        ]
        self.assertNotIn(
            "standard-formatter-compatibility",
            {operation["kind"] for operation in
             ssreflect["normalization"]["operations"]},
        )

    def test_taylor_arithmetic_variable_tuples_are_grouped_explicitly(
        self,
    ) -> None:
        source_key = "flyspeck:formal_ineqs/taylor/m_taylor_arith.hl"
        node = self.payload["source_nodes"][source_key]
        operations = {
            operation["kind"]: operation
            for operation in node["normalization"]["operations"]
        }
        expected = {
            "taylor-arith-all-variable-tuple-grouping",
            "taylor-arith-build-variable-tuple-grouping",
        }
        self.assertEqual(set(operations), expected)
        for kind in expected:
            self.assertIn(
                'let variable_name = "a" ^ string_of_int i in',
                operations[kind]["after"],
            )
            self.assertEqual(operations[kind]["replacement_count"], 1)
        normalized, _ = subject.normalize_source(
            source_key,
            (FLYSPECK_ROOT / node["logical_relative_path"]).read_bytes(),
        )
        self.assertEqual(normalized.count(b"let variable_name ="), 2)
        self.assertNotIn(b'mk_var ("a"^string_of_int i', normalized)

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

    def test_certificate_integer_successor_is_explicit(self) -> None:
        operations = self.payload["source_nodes"][
            "flyspeck:formal_ineqs/verifier/certificate.hl"
        ]["normalization"]["operations"]
        selected = [
            operation for operation in operations
            if operation["kind"] == "certificate-int-successor"
        ]
        self.assertEqual(len(selected), 1)
        self.assertEqual(selected[0]["before"], "succ c")
        self.assertEqual(selected[0]["after"], "c + 1")
        self.assertEqual(selected[0]["replacement_count"], 1)

    def test_native_division_exceptions_use_cakeml_constructor(self) -> None:
        expected = {
            "flyspeck:formal_ineqs/informal/informal_search.hl":
                ("search-division-exception", 3),
            "flyspeck:formal_ineqs/informal/informal_verifier.hl":
                ("informal-verifier-division-exception", 1),
        }
        for source_key, (kind, count) in expected.items():
            operations = self.payload["source_nodes"][source_key][
                "normalization"
            ]["operations"]
            selected = [
                operation for operation in operations
                if operation["kind"] == kind
            ]
            self.assertEqual(len(selected), 1)
            if source_key.endswith("informal_verifier.hl"):
                self.assertEqual(
                    selected[0]["before"], "| Division_by_zero ->",
                )
                self.assertEqual(selected[0]["after"], "| Div ->")
            else:
                self.assertEqual(selected[0]["before"], "Division_by_zero")
                self.assertEqual(selected[0]["after"], "Div")
            self.assertEqual(selected[0]["replacement_count"], count)

    def test_informal_nat_integer_successors_are_explicit(self) -> None:
        operations = self.payload["source_nodes"][
            "flyspeck:formal_ineqs/informal/informal_nat.hl"
        ]["normalization"]["operations"]
        selected = {
            operation["kind"]: operation
            for operation in operations
            if operation["kind"].startswith("informal-nat-")
        }
        self.assertEqual(set(selected), {
            "informal-nat-normalize-successor",
            "informal-nat-lo-successor",
            "informal-nat-hi-successor",
            "informal-nat-hi-rounded-successor",
        })
        self.assertEqual(
            {operation["before"] for operation in selected.values()},
            {
                "normalize q (succ e)",
                "lo q (succ e)",
                "hi q (succ e)",
                "hi (succ_big_int q) (succ e)",
            },
        )
        self.assertTrue(all(
            operation["replacement_count"] == 1 and
            "succ e" not in operation["after"] and
            "e + 1" in operation["after"]
            for operation in selected.values()
        ))

    def test_certificate_accumulator_append_grouping_is_explicit(self) -> None:
        operations = self.payload["source_nodes"][
            "flyspeck:formal_ineqs/verifier/certificate.hl"
        ]["normalization"]["operations"]
        selected = {
            operation["kind"]: operation
            for operation in operations
            if operation["kind"] in {
                "certificate-left-accumulator-binding",
                "certificate-right-accumulator-binding",
            }
        }
        self.assertEqual(set(selected), {
            "certificate-left-accumulator-binding",
            "certificate-right-accumulator-binding",
        })
        self.assertTrue(all(
            operation["replacement_count"] == 1
            for operation in selected.values()
        ))
        self.assertTrue(all(
            "let acc'' = acc' @" in operation["after"] and
            "false, acc'', Result_glue" in operation["after"]
            for operation in selected.values()
        ))

    def test_certificate_float_subdomain_order_is_explicit(self) -> None:
        operations = self.payload["source_nodes"][
            "flyspeck:formal_ineqs/verifier/certificate.hl"
        ]["normalization"]["operations"]
        selected = [
            operation for operation in operations
            if operation["kind"] == "certificate-float-subdomain-order"
        ]
        self.assertEqual(len(selected), 1)
        self.assertEqual(selected[0]["replacement_count"], 1)
        self.assertIn("(a <= b)", selected[0]["before"])
        self.assertIn("float_ieee_le a b", selected[0]["after"])

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

    def test_float_split_uses_native_ieee_equality(self) -> None:
        expected = {
            "flyspeck:formal_ineqs/arith/more_float.hl": {
                "more-float-ieee-base-order",
                "more-float-ieee-special-equality",
                "more-float-ieee-sign-order",
                "more-float-ieee-unit-order",
                "more-float-ieee-zero-equality",
            },
            "flyspeck:formal_ineqs/informal/informal_float.hl": {
                "informal-float-ieee-base-order",
                "informal-float-ieee-special-equality",
                "informal-float-ieee-sign-order",
                "informal-float-ieee-unit-order",
                "informal-float-ieee-zero-equality",
            },
        }
        for source_key, kinds in expected.items():
            operations = self.payload["source_nodes"][source_key][
                "normalization"
            ]["operations"]
            selected = {
                operation["kind"]: operation
                for operation in operations if operation["kind"] in kinds
            }
            self.assertEqual(set(selected), kinds)
            self.assertTrue(all(
                "float_ieee_" in operation["after"]
                for operation in selected.values()
            ))

    def test_raw_double_branches_use_native_ieee_order(self) -> None:
        expected = {
            "flyspeck:formal_ineqs/informal/informal_atn.hl": {
                "informal-atn-ieee-tail-order",
            },
            "flyspeck:formal_ineqs/informal/informal_exp.hl": {
                "informal-exp-ieee-reduction-order",
                "informal-exp-ieee-tail-order",
            },
            "flyspeck:formal_ineqs/informal/informal_sin_cos.hl": {
                "informal-cos-ieee-reduction-lower-order",
                "informal-cos-ieee-reduction-upper-order",
                "informal-cos-ieee-tail-order",
            },
            "flyspeck:formal_ineqs/trig/atn_eval.hl": {
                "atn-eval-ieee-tail-order",
            },
            "flyspeck:formal_ineqs/trig/cos_bounds_eval.hl": {
                "cos-bounds-eval-ieee-tail-order",
            },
            "flyspeck:formal_ineqs/trig/cos_eval.hl": {
                "cos-eval-ieee-reduction-lower-order",
                "cos-eval-ieee-reduction-upper-order",
            },
            "flyspeck:formal_ineqs/trig/exp_eval.hl": {
                "exp-eval-ieee-reduction-order",
                "exp-eval-ieee-tail-order",
            },
        }
        selected = {}
        for source_key, kinds in expected.items():
            operations = self.payload["source_nodes"][source_key][
                "normalization"
            ]["operations"]
            selected[source_key] = {
                operation["kind"]: operation
                for operation in operations
                if operation["kind"] in kinds
            }
            self.assertEqual(set(selected[source_key]), kinds)
        operations = [
            operation
            for source_operations in selected.values()
            for operation in source_operations.values()
        ]
        self.assertEqual(len(operations), 12)
        self.assertTrue(all(
            operation["replacement_count"] == 1 and
            "float_ieee_" in operation["after"]
            for operation in operations
        ))

    def test_atan_one_table_bounds_use_exact_binary64_literal(self) -> None:
        expected = {
            "flyspeck:formal_ineqs/informal/informal_sin_cos.hl":
                "informal-cos-pi-over-two-literal",
            "flyspeck:formal_ineqs/trig/cos_bounds_eval.hl":
                "cos-bounds-eval-pi-over-two-literal",
        }
        for source_key, kind in expected.items():
            operations = self.payload["source_nodes"][source_key][
                "normalization"
            ]["operations"]
            selected = [
                operation for operation in operations
                if operation["kind"] == kind
            ]
            self.assertEqual(len(selected), 1)
            self.assertEqual(selected[0]["replacement_count"], 2)
            self.assertEqual(selected[0]["before"], "2.0 *. atan 1.0")
            self.assertEqual(selected[0]["after"], "1.5707963267948966")

    def test_all_active_assertions_use_distinct_failure_helper(self) -> None:
        assertion_operations = [
            operation
            for node in self.payload["source_nodes"].values()
            for operation in node.get("normalization", {}).get(
                "operations", []
            )
            if "assert" in operation["kind"]
        ]
        self.assertEqual(len(assertion_operations), 10)
        self.assertEqual(
            sum(operation["replacement_count"]
                for operation in assertion_operations),
            14,
        )
        self.assertTrue(all(
            operation["before"].startswith("assert (") and
            operation["after"].startswith("candle_assert (")
            for operation in assertion_operations
        ))

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

    def test_module_ssreflect_reuses_canonical_operation_objects(self) -> None:
        node = self.payload["source_nodes"][
            subject.SSREFLECT_MODULE_SOURCE_KEY
        ]
        record = node["normalization"]
        self.assertEqual(record["id"], subject.DIRECT_NORMALIZATION_ALIAS)
        self.assertEqual(
            record["authority"],
            "direct-flyspeck-normalization-derived-alias",
        )
        self.assertEqual(
            record["canonical_source_key"],
            subject.SSREFLECT_CANONICAL_SOURCE_KEY,
        )
        self.assertEqual(record["operation_count"], 6)
        self.assertEqual(
            tuple(operation["id"] for operation in record["operations"]),
            subject.SSREFLECT_SHARED_OPERATION_IDS,
        )

        contract = json.loads(
            (ROOT / subject.flyspeck_manifest.SOURCE_NORMALIZATION_CONTRACT)
            .read_text(encoding="utf-8")
        )
        canonical = next(
            entry for entry in contract["entries"]
            if entry["source_key"] == subject.SSREFLECT_CANONICAL_SOURCE_KEY
        )
        canonical_operations = {
            operation["id"]: operation
            for operation in canonical["operations"]
        }
        for operation in record["operations"]:
            authoritative = canonical_operations[operation["id"]]
            self.assertEqual(operation["kind"], authoritative["kind"])
            self.assertEqual(operation["before"], authoritative["before"])
            self.assertEqual(operation["after"], authoritative["after"])
            self.assertEqual(
                operation["canonical_line"], authoritative["line"],
            )

        source = (
            FLYSPECK_ROOT / node["logical_relative_path"]
        ).read_bytes()
        _contract_data, direct = subject.load_direct_normalizations(
            ROOT, FLYSPECK_ROOT,
            json.loads((ROOT / subject.MANIFEST).read_text(encoding="utf-8")),
        )
        normalized, observed = subject.apply_recorded_normalization(
            subject.SSREFLECT_MODULE_SOURCE_KEY, source, node, direct,
        )
        self.assertEqual(observed, record)
        self.assertEqual(len(normalized), record["normalized_bytes"])
        self.assertNotIn(
            canonical_operations[
                subject.SSREFLECT_SHARED_OPERATION_IDS[0]
            ]["before"].encode("utf-8"),
            normalized,
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

    def test_nested_array_get_remains_one_argument_after_composition(self) -> None:
        original = b'''let f a =
  (fun x -> x + 1) a.(1).(0);;
let () = Printf.printf "%d\\n" (f [|[|1|];[|7|]|]);;
'''
        normalized, operations = subject.normalize_nested_array_access(
            original,
        )
        self.assertEqual(len(operations), 1)
        self.assertIn(
            b"(fun x -> x + 1) (Array.get (Array.get a (1)) (0))",
            normalized,
        )
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
                    check=True, stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                )
                result = subprocess.run(
                    [str(executable)], check=True,
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                )
                outputs.append(result.stdout)
        self.assertEqual(outputs, [b"8\n", b"8\n"])

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
