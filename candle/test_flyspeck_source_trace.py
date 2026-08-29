#!/usr/bin/env python3

import copy
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import flyspeck_stratum_runtime as subject


class SourceTraceTests(unittest.TestCase):
    nonce = "a" * 32

    def binding(
        self, index: int, key: str, *, resolved: str | None = None,
        canonical: str | None = None,
    ) -> dict[str, object]:
        resolved = resolved or f"/trace/{index:02d}.ml"
        canonical = canonical or resolved
        payload = {
            "resolved": resolved,
            "canonical": canonical,
            "key": key,
            "basename": Path(canonical).name,
            "source_md5": f"{index + 1:032x}",
            "source_sha256": f"{index + 1:064x}",
            "selected": canonical,
            "selected_sha256": f"{index + 1:064x}",
            "normalization": "-",
        }
        return {"binding_id": subject.canonical_sha256(payload), **payload}

    def contract(self) -> dict[str, object]:
        source = self.binding(1, "flyspeck:a")
        source_alias = self.binding(
            2, "flyspeck:a", resolved="/trace/02-alias.ml",
            canonical="/trace/01.ml",
        )
        for field in (
            "source_md5", "source_sha256", "selected_sha256",
        ):
            source_alias[field] = source[field]
        source_alias["binding_id"] = subject.canonical_sha256({
            field: value for field, value in source_alias.items()
            if field != "binding_id"
        })
        bindings = [
            self.binding(0, "control:runtime-setup"),
            source,
            source_alias,
            self.binding(3, "control:instrumented-prefix"),
            self.binding(4, "control:stratum-check"),
            self.binding(5, "control:postlude"),
        ]
        bindings.sort(key=lambda item: item["resolved"])
        required_keys = sorted({item["key"] for item in bindings})
        return {
            "schema": 1,
            "protocol": subject.SOURCE_TRACE_PROTOCOL,
            "nonce": self.nonce,
            "activation": subject.SOURCE_TRACE_ACTIVATION,
            "binding_count": len(bindings),
            "ordered_binding_sha256": subject.canonical_sha256(bindings),
            "bindings": bindings,
            "required_key_count": len(required_keys),
            "ordered_required_key_sha256":
                subject.canonical_sha256(required_keys),
            "required_keys": required_keys,
            "top_level_control_keys":
                list(subject.SOURCE_TRACE_TOP_LEVEL_CONTROLS),
        }

    def request(
        self, contract: dict[str, object], request_id: int, binding_index: int,
        parent: int | None, kind: str, cache: str,
    ) -> str:
        binding = contract["bindings"][binding_index]
        return "\t".join((
            subject.SOURCE_TRACE_PREFIX, self.nonce, "REQUEST",
            str(request_id), "-" if parent is None else str(parent), kind,
            binding["binding_id"], binding["key"], binding["basename"],
            binding["source_md5"], binding["source_sha256"],
            binding["selected_sha256"], binding["normalization"], cache,
        ))

    def outcome(self, request_id: int, outcome: str) -> str:
        return "\t".join((
            subject.SOURCE_TRACE_PREFIX, self.nonce, "OUTCOME",
            str(request_id), outcome,
        ))

    def valid_lines(self) -> tuple[dict[str, object], list[str]]:
        contract = self.contract()
        lines = [
            self.request(contract, 0, 0, None, "#use", "fresh-cache"),
            self.request(contract, 1, 1, 0, "needs", "fresh-cache"),
            self.outcome(1, "evaluated"),
            self.outcome(0, "evaluated"),
            self.request(contract, 2, 3, None, "#use", "fresh-cache"),
            self.request(contract, 3, 2, 2, "#flyspeck_needs", "prior-cache"),
            self.outcome(3, "cache-skip"),
            self.outcome(2, "evaluated"),
            self.request(contract, 4, 4, None, "#use", "fresh-cache"),
            self.outcome(4, "evaluated"),
            self.request(contract, 5, 5, None, "#use", "fresh-cache"),
            self.request(contract, 6, 2, 5, "loads", "prior-cache"),
            self.outcome(6, "evaluated"),
            self.outcome(5, "evaluated"),
            "\t".join((
                subject.SOURCE_TRACE_PREFIX, self.nonce, "TERMINAL", "7",
            )),
        ]
        return contract, lines

    def test_parser_accepts_nested_cache_skip_and_repeated_load(self) -> None:
        contract, lines = self.valid_lines()
        observed = subject.validate_source_trace("\n".join(lines), contract)
        self.assertEqual(observed["request_count"], 7)
        self.assertEqual(observed["cache_skip_count"], 1)
        self.assertEqual(observed["observed_keys"], contract["required_keys"])
        self.assertEqual(observed["status"], "closed-loader-owned-session")
        forged = copy.deepcopy(observed)
        forged["events"][1]["parent"] = True
        forged["ordered_event_sha256"] = subject.canonical_sha256(
            forged["events"]
        )
        with self.assertRaises(subject.ContractError):
            subject.validate_source_trace_observation(contract, forged)

    def test_parser_rejects_forged_state_machine_and_binding_records(self) -> None:
        contract, valid = self.valid_lines()

        def replace_field(lines: list[str], line: int, field: int, value: str) -> None:
            fields = lines[line].split("\t")
            fields[field] = value
            lines[line] = "\t".join(fields)

        cases = []
        wrong_parent = valid.copy()
        replace_field(wrong_parent, 1, 4, "-")
        cases.append(("parent", wrong_parent))
        wrong_outcome = valid.copy()
        replace_field(wrong_outcome, 2, 4, "cache-skip")
        cases.append(("outcome", wrong_outcome))
        wrong_binding = valid.copy()
        replace_field(wrong_binding, 1, 9, "f" * 32)
        cases.append(("binding", wrong_binding))
        wrong_cache = valid.copy()
        replace_field(wrong_cache, 5, 13, "fresh-cache")
        cases.append(("cache", wrong_cache))
        missing_outcome = valid.copy()
        missing_outcome.pop(2)
        cases.append(("missing outcome", missing_outcome))
        duplicate_terminal = valid + [valid[-1]]
        cases.append(("duplicate terminal", duplicate_terminal))
        failure = valid[:-1] + ["\t".join((
            subject.SOURCE_TRACE_PREFIX, self.nonce, "FAILURE", "read",
        ))]
        cases.append(("failure", failure))
        wrong_top_level = valid.copy()
        wrong_top_level[4] = self.request(
            contract, 2, 4, None, "#use", "fresh-cache",
        )
        wrong_top_level[8] = self.request(
            contract, 4, 3, None, "#use", "fresh-cache",
        )
        cases.append(("top-level order", wrong_top_level))
        wrong_nonce = valid.copy()
        replace_field(wrong_nonce, 0, 1, "b" * 32)
        cases.append(("nonce", wrong_nonce))
        noncanonical_id = valid.copy()
        replace_field(noncanonical_id, 0, 3, "00")
        cases.append(("noncanonical request id", noncanonical_id))

        for label, lines in cases:
            with self.subTest(label=label), self.assertRaises(subject.ContractError):
                subject.validate_source_trace("\n".join(lines), contract)

    def test_contract_rejects_forged_identity_closure_and_types(self) -> None:
        valid = self.contract()
        subject.validate_source_trace_contract(valid)
        cases = []
        forged_id = copy.deepcopy(valid)
        forged_id["bindings"][0]["binding_id"] = "f" * 64
        forged_id["ordered_binding_sha256"] = subject.canonical_sha256(
            forged_id["bindings"]
        )
        cases.append(("binding identity", forged_id))
        inconsistent_alias = copy.deepcopy(valid)
        inconsistent_alias["bindings"][2]["source_sha256"] = "f" * 64
        inconsistent_alias["bindings"][2]["binding_id"] = (
            subject.canonical_sha256({
                field: value
                for field, value in inconsistent_alias["bindings"][2].items()
                if field != "binding_id"
            })
        )
        inconsistent_alias["ordered_binding_sha256"] = subject.canonical_sha256(
            inconsistent_alias["bindings"]
        )
        cases.append(("inconsistent alias identity", inconsistent_alias))
        unbound = copy.deepcopy(valid)
        unbound["required_keys"].append("flyspeck:unbound")
        unbound["required_keys"].sort()
        unbound["required_key_count"] = len(unbound["required_keys"])
        unbound["ordered_required_key_sha256"] = subject.canonical_sha256(
            unbound["required_keys"]
        )
        cases.append(("unbound key", unbound))
        boolean_count = copy.deepcopy(valid)
        boolean_count["binding_count"] = True
        cases.append(("boolean count", boolean_count))
        extra_field = copy.deepcopy(valid)
        extra_field["untrusted"] = True
        cases.append(("extra field", extra_field))
        reordered = copy.deepcopy(valid)
        reordered["bindings"][0], reordered["bindings"][1] = (
            reordered["bindings"][1], reordered["bindings"][0]
        )
        reordered["ordered_binding_sha256"] = subject.canonical_sha256(
            reordered["bindings"]
        )
        cases.append(("binding order", reordered))

        for label, contract in cases:
            with self.subTest(label=label), self.assertRaises(subject.ContractError):
                subject.validate_source_trace_contract(contract)

    def test_contract_materialization_binds_controls_alias_and_normalization(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            candle = root / "candle"
            source = root / "flyspeck/a.ml"
            alias = root / "flyspeck/alias-a.ml"
            normalized = root / "overlay/a.ml"
            program = root / "control/program.ml"
            postlude = root / "control/postlude.ml"
            for path in (
                candle / subject.SETUP_RELATIVE,
                candle / subject.SOURCE_DIGEST_RELATIVE,
                candle / "candle/build/insulate.ml",
                candle / subject.CHECK_RELATIVE,
                candle / subject.FINGERPRINT_RELATIVE,
                source, alias, normalized, program, postlude,
            ):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(f"(* {path.name} *)\n", encoding="utf-8")
            source_record = subject.hash_file(source)
            normalized_record = subject.hash_file(normalized)
            prepared = {
                "candle_runtime_root": candle,
                "source_runtime": [{
                    "key": "flyspeck:a", "absolute": str(source),
                    **source_record,
                }],
                "source_alias_runtime": [{
                    "source_key": "flyspeck:a", "alias": str(alias),
                    "canonical": str(source),
                }],
                "normalized_runtime": [{
                    "source_key": "flyspeck:a", "original": str(source),
                    "output": str(normalized),
                    "normalization_id": "TEST-NORMALIZATION-001",
                    **normalized_record,
                }],
            }
            closure = {
                "records": [
                    {"key": "flyspeck:a",
                     "classification": "expected-nested-source"},
                    {"key": "candle:candle/flyspeck_source_digests.ml",
                     "classification": "generated-executed-control"},
                    {"key": "candle:candle/build/insulate.ml",
                     "classification": "generated-executed-control"},
                    {"key": "candle:candle/flyspeck_full_build.ml",
                     "classification": "derivation-only-input"},
                ],
            }
            contract = subject.build_source_trace_contract(
                prepared, closure, program, postlude, ["A.theorem"], self.nonce,
            )
            subject.validate_source_trace_contract(contract)
            self.assertEqual(contract["binding_count"], 9)
            self.assertNotIn(
                "candle:candle/flyspeck_full_build.ml",
                contract["required_keys"],
            )
            source_bindings = [
                item for item in contract["bindings"]
                if item["key"] == "flyspeck:a"
            ]
            self.assertEqual(len(source_bindings), 2)
            self.assertEqual(
                {item["selected"] for item in source_bindings},
                {str(normalized)},
            )
            self.assertEqual(
                {item["normalization"] for item in source_bindings},
                {"TEST-NORMALIZATION-001"},
            )

            config_prepared = {
                **prepared,
                "flyspeck_root": root / "flyspeck",
                "overlay_root": root / "overlay",
                "generated_root": root / "generated",
                "boundary": {"boundary_id": "00-test-through-001"},
                "actions": [],
                "attempt_nonce": self.nonce,
                "source_trace_contract": contract,
                "generated_runtime": [],
                "lp_certificate_runtime": [],
                "process_runtime": [],
            }
            config = root / "control/runtime-config.ml"
            subject.write_config(
                config, candle, config_prepared, program,
                subject.hash_file(program)["md5"],
            )
            rendered = config.read_text(encoding="utf-8")
            self.assertEqual(rendered.count("Cakeml.configureSourceTrace"), 1)
            self.assertEqual(rendered.count("TEST-NORMALIZATION-001"), 2)
            self.assertLess(
                rendered.index("Cakeml.configureSourceTrace"),
                rendered.index("candle_flyspeck_stratum_source_aliases"),
            )


if __name__ == "__main__":
    unittest.main()
