#!/usr/bin/env python3

import copy
import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import flyspeck_stratum_runtime as subject


class SourceTraceTests(unittest.TestCase):
    nonce = "a" * 32

    def loader_tree(self, root: Path) -> tuple[
        dict[str, object], dict[str, dict[str, object]], dict[str, object],
        dict[str, object], Path, Path,
    ]:
        candle = root / "candle"
        flyspeck = root / "flyspeck"
        files = {
            candle / subject.SETUP_RELATIVE: (
                b'#use "hol.ml";;\n'
                b'let candle_flyspeck_stratum_add_load_path path = ();;\n'
                b'List.iter candle_flyspeck_stratum_add_load_path [];;\n'
            ),
            candle / "hol.ml": b"(* authenticated HOL entry *)\n",
            flyspeck / "text_formalization/general/a.hl": b"(* action *)\n",
            candle / subject.SOURCE_DIGEST_RELATIVE: b"(* digests *)\n",
            candle / "candle/build/insulate.ml": b"(* insulate *)\n",
            candle / subject.CHECK_RELATIVE: b"(* check *)\n",
            root / "control/instrumented-prefix.ml": b"(* prefix *)\n",
            root / "control/postlude.ml": b"(* postlude *)\n",
        }
        for path, content in files.items():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
        (flyspeck / "jHOLLight").mkdir()
        (flyspeck / "formal_ineqs").mkdir()
        source_by_key = {}
        for repository, relative in (
            ("candle", "hol.ml"),
            ("flyspeck", "text_formalization/general/a.hl"),
        ):
            source_root = candle if repository == "candle" else flyspeck
            path = source_root / relative
            key = f"{repository}:{relative}"
            source_by_key[key] = {
                "key": key, "repository": repository, "path": relative,
                **subject.hash_file(path),
            }
        linked_dependency = {
            "generation": {
                "generator": "candle/insulate.py",
                "recipe": "build-instructions.sh",
                "runtime_input": "candle/build/types.txt",
            },
            "kind": "loads",
            "line": 23,
            "literal": "candle/build/insulate.ml",
            "status": "generated-contract",
            "syntax_position": "standalone-phrase",
        }
        insulate = candle / "candle/build/insulate.ml"
        source_by_key["candle:candle/build/insulate.ml"] = {
            "key": "candle:candle/build/insulate.ml",
            "repository": "candle",
            "path": "candle/build/insulate.ml",
            "artifact_role": "linked-runtime-control",
            **subject.hash_file(insulate),
        }
        manifest = {
            "load_path_order": list(subject.SOURCE_ALIAS_LOAD_PATH_ORDER),
            "build_sequence_roots": [{
                "index": 0, "target": "general/a.hl", "status": "resolved",
                "selected": "flyspeck:text_formalization/general/a.hl",
            }],
            "source_nodes": {
                "candle:hol_lib.ml": {
                    "dependencies": [linked_dependency],
                },
            },
            "generated_dependency_contracts": [{
                **linked_dependency, "source": "candle:hol_lib.ml",
            }],
        }
        source_loader_runtime = subject.derive_source_loader_runtime(
            manifest, source_by_key, candle, flyspeck,
        )
        prepared = {
            "candle_runtime_root": candle,
            "flyspeck_root": flyspeck,
            "source_runtime": [
                {**record, "absolute": str(
                    (candle if record["repository"] == "candle" else flyspeck) /
                    record["path"]
                )}
                for record in source_by_key.values()
            ],
            "source_alias_runtime": [],
            "source_loader_runtime": source_loader_runtime,
            "normalized_runtime": [],
        }
        closure = {
            "records": [
                {"key": "candle:hol.ml",
                 "classification": "expected-nested-source"},
                {"key": "flyspeck:text_formalization/general/a.hl",
                 "classification": "observed-outer-source"},
                {"key": "candle:candle/flyspeck_source_digests.ml",
                 "classification": "generated-executed-control"},
                {"key": "candle:candle/build/insulate.ml",
                 "classification": "generated-executed-control"},
            ],
        }
        return (
            manifest, source_by_key, prepared, closure,
            root / "control/instrumented-prefix.ml",
            root / "control/postlude.ml",
        )

    def binding(
        self, index: int, key: str, *, resolved: str | None = None,
        canonical: str | None = None,
    ) -> dict[str, object]:
        resolved = resolved or f"/trace/{index:02d}.ml"
        canonical = canonical or resolved
        source_repository, _ = key.split(":", 1)
        if source_repository == "control":
            source_repository = "attempt-control"
        source_relative = Path(canonical).name
        logical_identity = {
            "schema": 1,
            "artifact_role": (
                "manifest-source" if key.startswith("flyspeck:")
                else "attempt-control"
            ),
            "source_key": key,
            "source_repository": source_repository,
            "source_relative_path": source_relative,
            "request_repository": source_repository,
            "request_relative_path": Path(resolved).name,
            "request_contexts": ["test-loader-context"],
            "source_md5": f"{index + 1:032x}",
            "source_sha256": f"{index + 1:064x}",
            "selected_repository": source_repository,
            "selected_relative_path": source_relative,
            "selected_sha256": f"{index + 1:064x}",
            "normalization": "-",
        }
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
            "logical_identity": logical_identity,
        }
        return {
            "binding_id": subject.canonical_sha256(logical_identity), **payload,
        }

    def refresh_binding(self, binding: dict[str, object]) -> None:
        logical = binding["logical_identity"]
        for field in (
            "source_md5", "source_sha256", "selected_sha256", "normalization",
        ):
            logical[field] = binding[field]
        binding["binding_id"] = subject.canonical_sha256(logical)

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
        source_alias["logical_identity"] = copy.deepcopy(
            source["logical_identity"]
        )
        source_alias["logical_identity"]["request_relative_path"] = (
            Path(source_alias["resolved"]).name
        )
        self.refresh_binding(source_alias)
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
            "schema": 2,
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
        forged = copy.deepcopy(observed)
        forged["events"][0]["cache_before"] = []
        forged["ordered_event_sha256"] = subject.canonical_sha256(
            forged["events"]
        )
        with self.assertRaises(subject.ContractError):
            subject.validate_source_trace_observation(contract, forged)
        forged = copy.deepcopy(observed)
        forged["events"][0]["id"] = 0.0
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
        self.refresh_binding(inconsistent_alias["bindings"][2])
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
        float_schema = copy.deepcopy(valid)
        float_schema["schema"] = 1.0
        cases.append(("float schema", float_schema))
        float_count = copy.deepcopy(valid)
        float_count["binding_count"] = float(float_count["binding_count"])
        cases.append(("float count", float_count))
        integer_nonce = copy.deepcopy(valid)
        integer_nonce["nonce"] = int("1" * 32)
        cases.append(("integer nonce", integer_nonce))
        malformed_key = copy.deepcopy(valid)
        malformed_key["required_keys"][0] = []
        malformed_key["ordered_required_key_sha256"] = subject.canonical_sha256(
            malformed_key["required_keys"]
        )
        cases.append(("malformed required key", malformed_key))
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
        duplicate_canonical = copy.deepcopy(valid)
        duplicate_canonical["bindings"][2]["key"] = "flyspeck:b"
        duplicate_canonical["bindings"][2]["logical_identity"]["source_key"] = (
            "flyspeck:b"
        )
        self.refresh_binding(duplicate_canonical["bindings"][2])
        duplicate_canonical["required_keys"].append("flyspeck:b")
        duplicate_canonical["required_keys"].sort()
        duplicate_canonical["required_key_count"] = len(
            duplicate_canonical["required_keys"]
        )
        duplicate_canonical["ordered_required_key_sha256"] = (
            subject.canonical_sha256(duplicate_canonical["required_keys"])
        )
        duplicate_canonical["ordered_binding_sha256"] = subject.canonical_sha256(
            duplicate_canonical["bindings"]
        )
        cases.append(("canonical path has two keys", duplicate_canonical))

        for label, contract in cases:
            with self.subTest(label=label), self.assertRaises(subject.ContractError):
                subject.validate_source_trace_contract(contract)

    def test_contract_materialization_binds_controls_alias_and_normalization(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            candle = root / "candle"
            source = root / "flyspeck/a.ml"
            alias = root / "flyspeck/nested/../a.ml"
            normalized = root / "overlay/a.ml"
            program = root / "control/instrumented-prefix.ml"
            postlude = root / "control/postlude.ml"
            for path in (
                candle / subject.SETUP_RELATIVE,
                candle / subject.SOURCE_DIGEST_RELATIVE,
                candle / "candle/build/insulate.ml",
                candle / subject.CHECK_RELATIVE,
                candle / subject.FINGERPRINT_RELATIVE,
                source, normalized, program, postlude,
            ):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(f"(* {path.name} *)\n", encoding="utf-8")
            (root / "flyspeck/nested").mkdir()
            source_record = subject.hash_file(source)
            normalized_record = subject.hash_file(normalized)
            prepared = {
                "candle_runtime_root": candle,
                "flyspeck_root": root / "flyspeck",
                "source_runtime": [{
                    "key": "flyspeck:a", "absolute": str(source),
                    "repository": "flyspeck", "path": "a.ml",
                    **source_record,
                }],
                "source_alias_runtime": [{
                    "source_key": "flyspeck:a", "alias": str(alias),
                    "canonical": str(source),
                    "alias_repository": "flyspeck",
                    "alias_relative": "nested/../a.ml",
                    "canonical_repository": "flyspeck",
                    "canonical_relative": "a.ml",
                }],
                "source_loader_runtime": [
                    {
                        "source_key": "flyspeck:a",
                        "request_repository": "flyspeck",
                        "request_relative": "a.ml",
                        "canonical_repository": "flyspeck",
                        "canonical_relative": "a.ml",
                        "search_contexts": ["test-flyspeck-root"],
                    },
                    {
                        "source_key": "flyspeck:a",
                        "request_repository": "flyspeck",
                        "request_relative": "nested/../a.ml",
                        "canonical_repository": "flyspeck",
                        "canonical_relative": "a.ml",
                        "search_contexts": ["test-flyspeck-alias-root"],
                    },
                    {
                        "source_key": "candle:candle/build/insulate.ml",
                        "request_repository": "candle",
                        "request_relative": "candle/build/insulate.ml",
                        "canonical_repository": "candle",
                        "canonical_relative": "candle/build/insulate.ml",
                        "artifact_role": "linked-runtime-control",
                        "source_md5": subject.hash_file(
                            candle / "candle/build/insulate.ml"
                        )["md5"],
                        "source_sha256": subject.hash_file(
                            candle / "candle/build/insulate.ml"
                        )["sha256"],
                        "search_contexts": [
                            "manifest-generated-loader-contract"
                        ],
                    },
                ],
                "normalized_runtime": [{
                    "source_key": "flyspeck:a", "original": str(source),
                    "output": str(normalized),
                    "relative": "a.ml",
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

    def test_loader_logical_authority_survives_absolute_root_relocation(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            left = self.loader_tree(base / "left")
            right = self.loader_tree(base / "relocated/right")
            left_contract = subject.build_source_trace_contract(
                left[2], left[3], left[4], left[5], [], self.nonce,
            )
            right_contract = subject.build_source_trace_contract(
                right[2], right[3], right[4], right[5], [], self.nonce,
            )
            left_logical = sorted(
                (binding["binding_id"], binding["logical_identity"])
                for binding in left_contract["bindings"]
            )
            right_logical = sorted(
                (binding["binding_id"], binding["logical_identity"])
                for binding in right_contract["bindings"]
            )
            self.assertEqual(left_logical, right_logical)
            hol = next(
                binding for binding in left_contract["bindings"]
                if binding["key"] == "candle:hol.ml"
            )
            self.assertEqual(hol["resolved"], "hol.ml")
            self.assertEqual(
                hol["logical_identity"]["request_contexts"],
                ["setup-pre-load-path-candle-dot"],
            )
            insulate = next(
                binding for binding in left_contract["bindings"]
                if binding["key"] == "candle:candle/build/insulate.ml"
            )
            self.assertEqual(insulate["resolved"], "candle/build/insulate.ml")
            self.assertEqual(
                insulate["logical_identity"], {
                    "schema": 1,
                    "artifact_role": "linked-runtime-control",
                    "source_key": "candle:candle/build/insulate.ml",
                    "source_repository": "candle",
                    "source_relative_path": "candle/build/insulate.ml",
                    "request_repository": "candle",
                    "request_relative_path": "candle/build/insulate.ml",
                    "request_contexts": [
                        "manifest-generated-loader-contract"
                    ],
                    "source_md5": insulate["source_md5"],
                    "source_sha256": insulate["source_sha256"],
                    "selected_repository": "candle",
                    "selected_relative_path": "candle/build/insulate.ml",
                    "selected_sha256": insulate["selected_sha256"],
                    "normalization": "-",
                },
            )
            self.assertNotEqual(
                left_contract["ordered_binding_sha256"],
                right_contract["ordered_binding_sha256"],
            )

    def test_linked_runtime_source_authority_is_complete_and_fail_closed(self) -> None:
        dependency = {
            "generation": {
                "generator": "candle/insulate.py",
                "recipe": "build-instructions.sh",
                "runtime_input": "candle/build/types.txt",
            },
            "kind": "loads",
            "line": 23,
            "literal": "candle/build/insulate.ml",
            "status": "generated-contract",
            "syntax_position": "standalone-phrase",
        }

        def fixture(root: Path) -> tuple[dict[str, object], dict[str, object], Path]:
            path = root / "candle/build/insulate.ml"
            path.parent.mkdir(parents=True)
            path.write_bytes(b"(* exact linked runtime source *)\n")
            output = subject.hash_file(path)
            manifest = {
                "generated_dependency_contracts": [{
                    **dependency, "source": "candle:hol_lib.ml",
                }],
                "source_nodes": {
                    "candle:hol_lib.ml": {"dependencies": [dependency]},
                },
            }
            linked = {
                "outputs": {
                    "insulate.ml": {
                        field: output[field] for field in ("bytes", "sha256")
                    },
                },
            }
            return manifest, linked, path

        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)
            valid_manifest, valid_linked, valid_path = fixture(base / "valid")
            observed = subject.derive_linked_runtime_sources(
                valid_manifest, valid_linked, base / "valid",
            )
            self.assertEqual(list(observed), [
                "candle:candle/build/insulate.ml"
            ])
            self.assertEqual(observed[
                "candle:candle/build/insulate.ml"
            ]["artifact_role"], "linked-runtime-control")

            changed_manifest, changed_linked, changed_path = fixture(base / "changed")
            changed_path.write_bytes(b"changed bytes")
            with self.assertRaisesRegex(subject.ContractError, "mismatch"):
                subject.derive_linked_runtime_sources(
                    changed_manifest, changed_linked, base / "changed",
                )

            symlink_manifest, symlink_linked, symlink_path = fixture(base / "symlink")
            replacement = symlink_path.with_name("replacement.ml")
            replacement.write_bytes(symlink_path.read_bytes())
            symlink_path.unlink()
            symlink_path.symlink_to(replacement.name)
            with self.assertRaisesRegex(subject.ContractError, "missing ordinary"):
                subject.derive_linked_runtime_sources(
                    symlink_manifest, symlink_linked, base / "symlink",
                )

            hardlink_manifest, hardlink_linked, hardlink_path = fixture(base / "hardlink")
            replacement = hardlink_path.with_name("replacement.ml")
            hardlink_path.rename(replacement)
            os.link(replacement, hardlink_path)
            with self.assertRaisesRegex(subject.ContractError, "unique ordinary"):
                subject.derive_linked_runtime_sources(
                    hardlink_manifest, hardlink_linked, base / "hardlink",
                )

            substituted_manifest, substituted_linked, _ = fixture(base / "substituted")
            substituted_manifest["generated_dependency_contracts"][0]["literal"] = (
                "candle/build/substitute.ml"
            )
            with self.assertRaisesRegex(subject.ContractError, "parent dependency"):
                subject.derive_linked_runtime_sources(
                    substituted_manifest, substituted_linked,
                    base / "substituted",
                )

            missing_manifest, missing_linked, _ = fixture(base / "missing")
            missing_linked["outputs"] = {}
            with self.assertRaisesRegex(subject.ContractError, "lacks an exact linked output"):
                subject.derive_linked_runtime_sources(
                    missing_manifest, missing_linked, base / "missing",
                )

    def test_loader_context_rejects_substitution_bytes_links_and_basename_alias(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            base = Path(temporary)

            changed = self.loader_tree(base / "changed")
            (base / "changed/candle/hol.ml").write_bytes(b"changed")
            with self.assertRaisesRegex(subject.ContractError, "mismatch"):
                subject.derive_source_loader_runtime(
                    changed[0], changed[1], base / "changed/candle",
                    base / "changed/flyspeck",
                )

            substituted = self.loader_tree(base / "substituted")
            setup = base / "substituted/candle" / subject.SETUP_RELATIVE
            setup.write_bytes(
                setup.read_bytes().replace(b'"hol.ml"', b'"nested/hol.ml"')
            )
            with self.assertRaisesRegex(subject.ContractError, "undeclared source"):
                subject.derive_source_loader_runtime(
                    substituted[0], substituted[1], base / "substituted/candle",
                    base / "substituted/flyspeck",
                )

            symlinked = self.loader_tree(base / "symlinked")
            hol = base / "symlinked/candle/hol.ml"
            replacement = base / "symlinked/candle/replacement.ml"
            replacement.write_bytes(hol.read_bytes())
            hol.unlink()
            hol.symlink_to(replacement.name)
            with self.assertRaisesRegex(subject.ContractError, "unique ordinary"):
                subject.derive_source_loader_runtime(
                    symlinked[0], symlinked[1], base / "symlinked/candle",
                    base / "symlinked/flyspeck",
                )

            hardlinked = self.loader_tree(base / "hardlinked")
            hol = base / "hardlinked/candle/hol.ml"
            replacement = base / "hardlinked/candle/replacement.ml"
            replacement.write_bytes(hol.read_bytes())
            hol.unlink()
            os.link(replacement, hol)
            with self.assertRaisesRegex(subject.ContractError, "unique ordinary"):
                subject.derive_source_loader_runtime(
                    hardlinked[0], hardlinked[1], base / "hardlinked/candle",
                    base / "hardlinked/flyspeck",
                )

            collision = self.loader_tree(base / "collision")
            flyspeck_hol = base / "collision/flyspeck/hol.ml"
            flyspeck_hol.write_bytes(b"untrusted same basename")
            observed = subject.derive_source_loader_runtime(
                collision[0], collision[1], base / "collision/candle",
                base / "collision/flyspeck",
            )
            startup = next(
                item for item in observed
                if "setup-pre-load-path-candle-dot"
                in item["search_contexts"]
            )
            self.assertEqual(startup["source_key"], "candle:hol.ml")


if __name__ == "__main__":
    unittest.main()
