#!/usr/bin/env python3
"""Static, single-core tests for the Great 100 inventory contract."""

import json
import re
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import top100_manifest
import reference_fingerprints as reference


class Top100ManifestTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads(
            top100_manifest.MANIFEST.read_text(encoding="utf-8")
        )

    def test_generated_manifest_is_current(self):
        self.assertEqual(self.manifest, top100_manifest.build_manifest())

    def test_actual_suite_shape_is_explicit(self):
        self.assertEqual(self.manifest["target_count"], 65)
        self.assertEqual(self.manifest["covered_source_count"], 66)
        self.assertEqual(
            self.manifest["inventory_contract"]["theorem_request_count"], 97)
        self.assertEqual(
            self.manifest["excluded_100_sources"],
            [{
                "path": "100/sqrt.ml",
                "reason": "absent_from_upstream_GREAT_100_THEOREMS",
                "approval_status": "unreviewed",
                "flyspeck_dependency_impact": "unassessed",
            }],
        )

    def test_no_hidden_skips(self):
        self.assertTrue(all(target["skip"] is None
                            for target in self.manifest["targets"]))
        self.assertTrue(all(target["expected_status"] == "pass"
                            for target in self.manifest["targets"]))

    def test_missing_s1_evidence_is_not_misreported_as_success(self):
        for target in self.manifest["targets"]:
            request = target["fingerprint_request"]
            self.assertTrue(request["theorems"])
            self.assertIsNone(request["expected_identities"])
            self.assertIn(target["fingerprints"]["status"],
                          {"missing", "not_reached"})
            self.assertIsNone(target["fingerprints"]["theorems"])
            self.assertIsNone(target["fingerprints"]["assumptions"])
            self.assertIsNone(target["fingerprints"]["post_state"])
        approval = self.manifest["identity_approval"]
        self.assertEqual(approval["approval_status"], "unapproved")
        self.assertFalse(approval["promotion_allowed"])

    def test_all_named_results_resolve_and_manual_review_is_explicit(self):
        manual = {}
        for target in self.manifest["targets"]:
            request = target["fingerprint_request"]
            for theorem in request["theorems"]:
                declaration = theorem["resolved_declaration"]
                self.assertIn(declaration["path"], target["load_files"])
                self.assertGreater(declaration["line"], 0)
            if request["mapping_status"] == "manual_review":
                self.assertTrue(request["review_note"])
                manual[target["name"]] = request["review_note"]
            else:
                self.assertEqual(request["mapping_status"], "audited")
                self.assertIsNone(request["review_note"])
        self.assertEqual(set(manual), set(top100_manifest.MANUAL_REVIEW_MAPPINGS))

    def test_observed_failure_links_to_minimized_ledger_entry(self):
        targets = {target["name"]: target for target in self.manifest["targets"]}
        observation = targets["100/bertrand-primerecip"]["baseline_observation"]
        self.assertEqual(observation["status"], "fail")
        self.assertEqual(
            observation["ledger_id"], "CANDLE-OCAML-FLOAT-LITERAL-001")
        ledger = json.loads(
            (top100_manifest.ROOT / "candle" / "compatibility" / "ledger.json")
            .read_text(encoding="utf-8")
        )
        self.assertIn(observation["ledger_id"],
                      {entry["id"] for entry in ledger["entries"]})

    def test_module_scoped_theorem_request_is_qualified(self):
        target = next(target for target in self.manifest["targets"]
                      if target["name"] == "100/e_is_transcendental")
        theorem = target["fingerprint_request"]["theorems"][0]
        self.assertEqual(theorem["name"], "Finale.TRANSCENDENTAL_E")
        self.assertEqual(theorem["resolved_declaration"]["line"], 2903)
        self.assertIn(
            {"path": "100/e_is_transcendental.ml", "line": 2910},
            theorem["qualified_references"])

    def test_piseries_mapping_is_source_designated(self):
        target = next(target for target in self.manifest["targets"]
                      if target["name"] == "100/piseries")
        request = target["fingerprint_request"]
        self.assertEqual(request["mapping_status"], "audited")
        self.assertIn("most famous special case", request["mapping_basis"])
        self.assertEqual(
            request["theorems"], [{
                "name": "EULER_HARMONIC_SUM",
                "resolved_declaration": {
                    "path": "100/piseries.ml", "line": 2699},
                "shadowed_declarations": [],
            }])
        source = (top100_manifest.ROOT / "100/piseries.ml").read_text()
        self.assertRegex(
            source,
            r"Isolate the most famous special case[\s\S]*?"
            r"let EULER_HARMONIC_SUM = mk_harmonic 2;;")

    def test_quartic_final_rebinding_preserves_theorem_statement(self):
        target = next(target for target in self.manifest["targets"]
                      if target["name"] == "100/quartic")
        request = target["fingerprint_request"]
        self.assertEqual(request["mapping_status"], "audited")
        self.assertIn("changes only the proof", request["mapping_basis"])
        theorem = request["theorems"][0]
        self.assertEqual(
            theorem["resolved_declaration"],
            {"path": "100/quartic.ml", "line": 186})
        self.assertEqual(
            theorem["shadowed_declarations"],
            [{"path": "100/quartic.ml", "line": 140},
             {"path": "100/quartic.ml", "line": 163}])
        source = (top100_manifest.ROOT / "100/quartic.ml").read_text()
        statements = re.findall(
            r"let QUARTIC_CASES = prove\n \(`(.*?)`,\n", source, re.DOTALL)
        self.assertEqual(len(statements), 3)
        self.assertNotEqual(statements[0], statements[1])
        self.assertEqual(statements[1], statements[2])

    def test_cantor_and_fourier_boundaries_are_conservatively_audited(self):
        targets = {target["name"]: target for target in self.manifest["targets"]}
        cantor = targets["100/cantor"]["fingerprint_request"]
        self.assertEqual(cantor["mapping_status"], "audited")
        self.assertIsNone(cantor["review_note"])
        self.assertIn("post-load environment", cantor["mapping_basis"])
        self.assertEqual(
            [item["line"] for item in cantor["theorems"][0][
                "shadowed_declarations"]], [25])
        self.assertEqual(
            cantor["theorems"][0]["resolved_declaration"]["line"], 62)

        fourier = targets["100/fourier"]["fingerprint_request"]
        self.assertEqual(fourier["mapping_status"], "audited")
        self.assertIsNone(fourier["review_note"])
        self.assertIn("all four", fourier["mapping_basis"])
        self.assertEqual(
            [item["name"] for item in fourier["theorems"]],
            ["FOURIER_SERIES_L2", "FOURIER_DINI_TEST",
             "FOURIER_JORDAN_BOUNDED_VARIATION",
             "FOURIER_FEJER_CESARO_SUMMABLE_SIMPLE"])

    def test_reference_candidate_cannot_enter_expected_identities(self):
        candidate = {
            "schema": "candle-s1-reference-candidate-v1",
            "artifact_kind": "reference_identity_candidate",
            "approval_status": "candidate_unapproved",
            "promotion_allowed": False,
            "candidate_identities": {"status": "observed_uncompared"},
        }
        with self.assertRaisesRegex(ValueError, "malformed expected"):
            top100_manifest._validate_expected_identity_object(
                "100/gcd", ["EGCD"], candidate)

        approved_shape = {
            "approval_sha256": "5" * 64,
            "serializer_sha256": "0" * 64,
            "theorems": [{
                "name": "EGCD",
                "theorem_sha256": "1" * 64,
                "hypotheses_sha256":
                    top100_manifest.EMPTY_HYPOTHESES_SHA256,
                "conclusion_sha256": "3" * 64,
                "global_axioms_sha256": "4" * 64,
                "hypothesis_count": 0,
                "global_axiom_count": 3,
            }],
            "post_state": {
                "kernel_state_sha256": "6" * 64,
                "type_constants_sha256": "7" * 64,
                "type_constant_count": 1,
                "term_constants_sha256": "8" * 64,
                "term_constant_count": 2,
                "definitions_sha256": "9" * 64,
                "definition_count": 3,
                "global_axioms_sha256": "4" * 64,
                "global_axiom_count": 3,
            },
        }
        self.assertIs(
            top100_manifest._validate_expected_identity_object(
                "100/gcd", ["EGCD"], approved_shape),
            approved_shape)
        nonclosed = json.loads(json.dumps(approved_shape))
        nonclosed["theorems"][0]["hypothesis_count"] = 1
        with self.assertRaisesRegex(ValueError, "theorem is not closed"):
            top100_manifest._validate_expected_identity_object(
                "100/gcd", ["EGCD"], nonclosed)

    def test_unapproved_artifact_is_exact_and_cannot_carry_identities(self):
        targets = top100_manifest.build_manifest()["targets"]
        original = json.loads(
            top100_manifest.IDENTITY_APPROVAL.read_text(encoding="utf-8"))
        original["targets"] = [{"self_approved": True}]
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "approval.json"
            path.write_text(json.dumps(original), encoding="utf-8")
            with mock.patch.object(top100_manifest, "IDENTITY_APPROVAL", path):
                with self.assertRaisesRegex(ValueError, "promotable data"):
                    top100_manifest._load_identity_approval(targets)

    def test_duplicate_approval_json_key_fails_closed(self):
        targets = top100_manifest.build_manifest()["targets"]
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "approval.json"
            path.write_text('{"schema":"a","schema":"b"}', encoding="utf-8")
            with mock.patch.object(top100_manifest, "IDENTITY_APPROVAL", path):
                with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                    top100_manifest._load_identity_approval(targets)

    def test_approved_artifact_requires_two_retained_independent_runs(self):
        targets = top100_manifest.build_manifest()["targets"]
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "candle/evidence").mkdir(parents=True)
            serializer = root / "candle/fingerprint.ml"
            serializer.write_bytes(top100_manifest.ROOT.joinpath(
                "candle/fingerprint.ml").read_bytes())
            serializer_sha256 = top100_manifest._sha256(serializer)
            collector = root / "candle/reference_fingerprints.py"
            collector.write_bytes(Path(reference.__file__).read_bytes())
            source_contract_payload = json.loads(
                top100_manifest.REFERENCE_SOURCE_CONTRACT.read_text(
                    encoding="utf-8"))
            reference_source_contract = \
                root / "candle/reference_source_contracts.json"
            reference_source_contract.write_text(
                json.dumps(source_contract_payload, indent=2) + "\n",
                encoding="utf-8")
            source_contract = root / "candle/evidence/source-contract.json"
            source_contract.write_bytes(reference_source_contract.read_bytes())

            def record(relative, content):
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(content)
                return {
                    "path": relative,
                    "bytes": len(content),
                    "sha256": top100_manifest.hashlib.sha256(content).hexdigest(),
                }

            collection_deadlines = {
                "collection_wall_seconds": 21600,
                "target_wall_seconds": 21660,
                "validation_wall_seconds": 900,
            }
            collection_rows = {1: [], 2: []}
            approved_targets = []
            for target_index, target in enumerate(targets):
                axioms = f"axioms:{target_index}".encode()
                theorem_serializations = {
                    theorem["name"]: {
                        "theorem": f"theorem:{target_index}:{theorem['name']}".encode(),
                        "hypotheses": b"4:list1:0",
                        "conclusion":
                            f"conclusion:{target_index}:{theorem['name']}".encode(),
                    }
                    for theorem in target["fingerprint_request"]["theorems"]
                }
                state_serializations = {
                    "kernel": f"state:{target_index}".encode(),
                    "types": f"types:{target_index}".encode(),
                    "constants": f"constants:{target_index}".encode(),
                    "definitions": f"definitions:{target_index}".encode(),
                }
                expected = {
                    "serializer_sha256": serializer_sha256,
                    "theorems": [{
                        "name": theorem["name"],
                        "theorem_sha256": top100_manifest.hashlib.sha256(
                            theorem_serializations[theorem["name"]][
                                "theorem"]).hexdigest(),
                        "hypotheses_sha256": top100_manifest.hashlib.sha256(
                            theorem_serializations[theorem["name"]][
                                "hypotheses"]).hexdigest(),
                        "conclusion_sha256": top100_manifest.hashlib.sha256(
                            theorem_serializations[theorem["name"]][
                                "conclusion"]).hexdigest(),
                        "global_axioms_sha256":
                            top100_manifest.hashlib.sha256(axioms).hexdigest(),
                        "hypothesis_count": 0,
                        "global_axiom_count": 3,
                    } for theorem in target["fingerprint_request"]["theorems"]],
                    "post_state": {
                        "kernel_state_sha256": top100_manifest.hashlib.sha256(
                            state_serializations["kernel"]).hexdigest(),
                        "type_constants_sha256": top100_manifest.hashlib.sha256(
                            state_serializations["types"]).hexdigest(),
                        "type_constant_count": 10,
                        "term_constants_sha256": top100_manifest.hashlib.sha256(
                            state_serializations["constants"]).hexdigest(),
                        "term_constant_count": 20,
                        "definitions_sha256": top100_manifest.hashlib.sha256(
                            state_serializations["definitions"]).hexdigest(),
                        "definition_count": 30,
                        "global_axioms_sha256":
                            top100_manifest.hashlib.sha256(axioms).hexdigest(),
                        "global_axiom_count": 3,
                    },
                }
                identity_sha256 = top100_manifest._canonical_sha256(expected)
                runs = []
                for run_index in range(2):
                    sweep = run_index + 1
                    nonce = ("9" if run_index == 0 else "b") * 64
                    collection_prefix = (
                        f"sweep-{sweep}/target-{target_index + 1:03d}/"
                        "attempt-0001")
                    prefix = f"candle/evidence/collection/{collection_prefix}"
                    request_source = reference._request_source(
                        target, serializer, nonce)
                    package_root = Path("/reference-tools/pari")
                    def route(argument, resolved):
                        return {
                            "argument_path": argument,
                            "argument_parent": {
                                "path": str(Path(argument).parent),
                                "kind": "directory", "mode": 0o755,
                                "resolved_path": str(Path(argument).parent),
                            },
                            "argument": {
                                "path": argument, "kind": "file", "mode": 0o755,
                                "resolved_path": resolved,
                            },
                            "resolved_executable": {
                                "path": resolved, "sha256": "a" * 64,
                                "mode": 0o755,
                            },
                        }
                    external_environment = {
                        "HOME": "/reference",
                        "PATH": str(package_root / "usr/bin"),
                        "LC_ALL": "C",
                        "GPRC": str(package_root / "candle-gprc"),
                        "GP_DATA_DIR": str(package_root / "candle-data"),
                    }
                    probe_source = reference.PARI_GP_PROBE_SOURCE
                    probe_stdout = "1\n[3, 1; 5, 1]\n"
                    external_runtime = {
                        "policy": "single_private_path_gp_with_pinned_shell_v1",
                        "command_shell": route("/bin/sh", "/usr/bin/dash"),
                        "pari_gp": route(
                            str(package_root / "usr/bin/gp"),
                            str(package_root / "usr/bin/gp-2.15"),
                        ),
                        "pari_gp_version": {
                            "stdout": "2.15.4\n",
                            "sha256": top100_manifest.hashlib.sha256(
                                b"2.15.4\n").hexdigest(),
                        },
                        "package_archive": {
                            "path": "/reference-tools/pari.deb",
                            "sha256": "b" * 64,
                        },
                        "package_tree": {
                            "root": str(package_root), "root_mode": 0o755,
                            "entry_count": 5, "inventory_sha256": "c" * 64,
                            "inventory_policy":
                                "relative_path_kind_mode_link_target_and_content_v1",
                        },
                        "configuration": {
                            "path": str(package_root / "candle-gprc"),
                            "sha256": "d" * 64,
                        },
                        "data_tree": {
                            "root": str(package_root / "candle-data"),
                            "root_mode": 0o555, "entry_count": 0,
                            "inventory_sha256": "e" * 64,
                            "inventory_policy":
                                "relative_path_kind_mode_link_target_and_content_v1",
                        },
                        "dynamic_libraries": [{
                            "path": "/usr/lib/libc.so.6", "sha256": "f" * 64,
                        }],
                        "probe": {
                            "shell_argv": ["/bin/sh", "-c", probe_source],
                            "environment": external_environment,
                            "return_code": 0, "stdout": probe_stdout,
                            "stdout_sha256": top100_manifest.hashlib.sha256(
                                probe_stdout.encode()).hexdigest(),
                            "stderr": "",
                            "stderr_sha256": top100_manifest.hashlib.sha256(
                                b"").hexdigest(),
                        },
                    }
                    def file_pin(path, fill):
                        return {"path": path, "sha256": fill * 64}
                    def tree_pin(root_path, fill):
                        return {
                            "root": root_path, "root_mode": 0o755,
                            "entry_count": 1,
                            "inventory_sha256": fill * 64,
                            "inventory_policy":
                                "relative_path_kind_mode_link_target_and_content_v1",
                        }
                    runtime_tree = tree_pin("/reference/stublibs", "1")
                    ocaml_tree = tree_pin("/reference/ocaml", "2")
                    plan = {
                        "schema": reference.PLAN_SCHEMA,
                        "status": "planned_not_executed",
                        "session_nonce": nonce,
                        "fresh_process_contract": {
                            "required": True,
                            "preloaded_checkpoint_allowed": False,
                            "working_directory": "/reference",
                            "environment_policy":
                                "sanitized_allowlist_no_inherited_overrides",
                            "runtime_argv": [
                                "/reference/ocaml-hol", "-init",
                                "/reference/hol.ml", "-I", "/reference",
                                "-noprompt",
                            ],
                            "runtime_environment": {
                                **external_environment,
                                "HOLLIGHT_DIR": "/reference",
                                "HOLLIGHT_USE_MODULE": "0",
                                "OCAMLRUNPARAM": "l=2000000000",
                                "CAML_LD_LIBRARY_PATH": "/reference/stublibs",
                                "OCAML_TOPLEVEL_PATH": "/reference/ocaml",
                                "OCAMLFIND_CONF": "/reference/ocamlfind.conf",
                            },
                        },
                        "reference": {
                            "root": "/reference",
                            "git_head": source_contract_payload[
                                "exact_source_reference_commit"],
                            "git_status": [],
                            "runtime_executable":
                                file_pin("/reference/ocaml-hol", "3"),
                            "runtime_interpreter": file_pin("/bin/sh", "4"),
                            "runtime_stublib": file_pin(
                                "/reference/stublibs/dllzarith.so", "5"),
                            "runtime_library_tree": runtime_tree,
                            "runtime_stub_files": [
                                file_pin(
                                    "/reference/stublibs/dllunix.so", "6"),
                                file_pin(
                                    "/reference/stublibs/dllzarith.so", "5"),
                            ],
                            "dynamic_libraries": [
                                file_pin("/usr/lib/libc.so.6", "7")],
                            "ocamlc": {
                                **file_pin("/reference/bin/ocamlc", "8"),
                                "version": "4.14.1",
                                "stdlib_directory": "/reference/ocaml",
                            },
                            "findlib": {
                                "executable": file_pin(
                                    "/reference/bin/ocamlfind", "9"),
                                "version": "1.9.6",
                                "configuration": file_pin(
                                    "/reference/ocamlfind.conf", "a"),
                                "package_roots": [ocaml_tree],
                            },
                            "hol_ml": file_pin("/reference/hol.ml", "b"),
                            "generated_boot_files": [
                                file_pin("/reference/hol_loader.cmo", "c"),
                                file_pin("/reference/pa_j.cmo", "d"),
                                file_pin(
                                    "/reference/load_camlp5_topfind.ml", "e"),
                            ],
                            "ocaml_library_tree": ocaml_tree,
                            "external_runtime": external_runtime,
                        },
                        "input": {
                            "collector": {
                                "path": str(collector.resolve()),
                                "sha256": top100_manifest._sha256(collector),
                            },
                            "collector_repository": {
                                "root": str(root),
                                "git_head": "8" * 40,
                                "git_status": [],
                                "collector_relative_path":
                                    "candle/reference_fingerprints.py",
                                "collector_at_head_sha256":
                                    top100_manifest._sha256(collector),
                                "collector_matches_head": True,
                                "support_relative_path":
                                    "candle/reference_protocol.py",
                                "support_at_head_sha256": "1" * 64,
                                "support_matches_head": True,
                            },
                            "manifest": {
                                "path": "/manifest", "sha256": "0" * 64},
                            "manifest_schema_version": 1,
                            "target": target["name"],
                            "load_files": [{
                                "relative_path": relative,
                                "path": f"/reference/{relative}",
                                "sha256": target["load_file_sha256"][relative],
                                "source_role": "selected-manifest-source",
                            } for relative in target["load_files"]],
                            "theorem_names": [
                                theorem["name"] for theorem in
                                target["fingerprint_request"]["theorems"]],
                            "mapping_status": "audited",
                            "serializer": {
                                "path": str(serializer.resolve()),
                                "sha256": serializer_sha256,
                            },
                            "source_mode": "manifest-exact",
                            "source_contract": {
                                "path": str(source_contract.resolve()),
                                "sha256": top100_manifest._sha256(source_contract),
                                **{
                                    key: source_contract_payload[key] for key in (
                                        "historical_upstream_commit",
                                        "exact_source_reference_commit",
                                        "compatibility_deltas")
                                },
                            },
                        },
                        "request": {
                            "source": request_source,
                            "sha256": top100_manifest.hashlib.sha256(
                                request_source.encode()).hexdigest(),
                        },
                    }
                    wire_records = []
                    for theorem in target["fingerprint_request"]["theorems"]:
                        serialized = theorem_serializations[theorem["name"]]
                        wire_records.append("\t".join([
                            reference.regression.FINGERPRINT_MARKER,
                            theorem["name"].encode("ascii").hex(),
                            serialized["theorem"].hex(),
                            serialized["hypotheses"].hex(),
                            serialized["conclusion"].hex(), axioms.hex(),
                            "0", "3",
                        ]))
                    wire_records.append("\t".join([
                        reference.regression.STATE_FINGERPRINT_MARKER,
                        state_serializations["kernel"].hex(),
                        state_serializations["types"].hex(),
                        state_serializations["constants"].hex(),
                        state_serializations["definitions"].hex(), axioms.hex(),
                        "10", "20", "30", "3",
                    ]))
                    transcript = "\n".join([
                        f"{reference.SESSION_MARKER}\t{nonce}",
                        *wire_records,
                        f"{reference.COMPLETE_MARKER}\t{nonce}", "",
                    ])
                    candidate = reference.candidate_from_transcript(
                        plan, transcript)
                    candidate_source = (
                        json.dumps(candidate, indent=2) + "\n").encode()
                    plan_source = (json.dumps(plan, indent=2) + "\n").encode()
                    artifacts = {
                        "candidate": record(
                            f"{prefix}-candidate.json", candidate_source),
                        "plan": record(f"{prefix}-plan.json", plan_source),
                        "request": record(
                            f"{prefix}-request.ml", request_source.encode()),
                        "transcript": record(
                            f"{prefix}-transcript.log", transcript.encode()),
                    }
                    artifacts["source_contract"] = {
                        "path": "candle/evidence/source-contract.json",
                        "bytes": source_contract.stat().st_size,
                        "sha256": top100_manifest._sha256(source_contract),
                    }
                    collected_artifacts = {
                        artifact_name: {
                            "path": artifact["path"].removeprefix(
                                "candle/evidence/collection/"),
                            "bytes": artifact["bytes"],
                            "sha256": artifact["sha256"],
                        }
                        for artifact_name, artifact in artifacts.items()
                        if artifact_name in {
                            "candidate", "plan", "request", "transcript"}
                    }
                    output_records = {}
                    for field, filename, content in (
                            ("collector_stdout", "collect.stdout", b"collect\n"),
                            ("collector_stderr", "collect.stderr", b""),
                            ("validator_stdout", "validate.stdout", b"validate\n"),
                            ("validator_stderr", "validate.stderr", b"")):
                        value = record(f"{prefix}/{filename}", content)
                        output_records[field] = {
                            **value,
                            "path": value["path"].removeprefix(
                                "candle/evidence/collection/"),
                        }
                        artifacts[field] = value
                    success = {
                        "schema": 1,
                        "kind": "candle-reference-attempt-success",
                        "sweep": sweep, "target_index": target_index + 1,
                        "target": target["name"], "session_nonce": nonce,
                        "artifacts": collected_artifacts,
                        **output_records,
                        "deadlines": collection_deadlines,
                        "approval_status": "candidate_unapproved",
                        "promotion_allowed": False,
                    }
                    success_source = (
                        json.dumps(success, indent=2, sort_keys=True) + "\n").encode()
                    success_record = record(
                        f"{prefix}/success.json", success_source)
                    artifacts["controller_success"] = success_record
                    runs.append({
                        "artifacts": artifacts,
                        "reference_git_head":
                            source_contract_payload["exact_source_reference_commit"],
                        "session_nonce": nonce,
                        "identity_sha256": identity_sha256,
                        "sweep": sweep,
                    })
                    collection_success_path = f"{collection_prefix}/success.json"
                    collection_rows[sweep].append({
                        "index": target_index + 1, "name": target["name"],
                        "state": "complete", "attempt_count": 1,
                        "success": {
                            "attempt": "attempt-0001",
                            "receipt_path": collection_success_path,
                            "receipt": {
                                **success_record,
                                "path": collection_success_path,
                            },
                            "session_nonce": nonce,
                            "artifacts": collected_artifacts,
                        },
                        "attempts": [{"attempt": "attempt-0001",
                                      "state": "complete"}],
                    })
                approved_targets.append({
                    "name": target["name"], "reference_runs": runs,
                    "expected_identity": expected,
                })
            collection_contract = {
                "schema": 2,
                "kind": "candle-great100-two-sweep-reference-collection",
                "approval_status": "candidate_collection_only_unapproved",
                "promotion_allowed": False,
                "sweep_count": 2, "target_count": 65,
                "total_target_runs": 130, "source_mode": "manifest-exact",
                "project": {"root": "/project", "git_head": "7" * 40,
                            "controller": {"fixture": True}},
                "candle": {
                    "root": str(root), "git_head": "8" * 40,
                    "collector": {
                        "path": "candle/reference_fingerprints.py",
                        "sha256": top100_manifest._sha256(collector)},
                    "protocol": {"path": "candle/reference_protocol.py",
                                 "sha256": "1" * 64},
                    "manifest": {"path": "candle/top100_manifest.json",
                                 "sha256": "0" * 64},
                    "serializer": {"path": "candle/fingerprint.ml",
                                   "sha256": serializer_sha256},
                    "source_contract": {
                        "path": "candle/reference_source_contracts.json",
                        "sha256": top100_manifest._sha256(source_contract)},
                },
                "reference": {
                    "root": "/reference",
                    "git_head": source_contract_payload[
                        "exact_source_reference_commit"],
                    "source_policy": {
                        key: source_contract_payload[key] for key in (
                            "historical_upstream_commit",
                            "exact_source_reference_commit",
                            "compatibility_deltas")},
                },
                "runtime": {},
                "external_runtime": {
                    "policy": external_runtime["policy"],
                    "command_shell": {"argument_path": "/bin/sh",
                                      "path": "/usr/bin/dash",
                                      "sha256": "a" * 64},
                    "pari_gp": {
                        "argument_path": str(package_root / "usr/bin/gp"),
                        "path": str(package_root / "usr/bin/gp-2.15"),
                        "sha256": "a" * 64},
                    "package_archive": {
                        "argument_path": "/reference-tools/pari.deb",
                        **external_runtime["package_archive"]},
                    "package_tree": external_runtime["package_tree"],
                    "configuration": {
                        "argument_path": str(package_root / "candle-gprc"),
                        **external_runtime["configuration"]},
                    "data_tree": external_runtime["data_tree"],
                    "runtime_environment": {
                        key: external_environment[key]
                        for key in ("PATH", "GPRC", "GP_DATA_DIR")},
                },
                "deadlines": collection_deadlines,
                "inventory": {
                    "target_count": 65, "source_count": 66,
                    "request_count": 97,
                    "targets": [{"name": target["name"]} for target in targets],
                },
                "controller": {"path": "/controller", "sha256": "2" * 64},
            }
            contract_source = (
                json.dumps(collection_contract, indent=2, sort_keys=True) +
                "\n").encode()
            contract_record = record(
                "candle/evidence/collection/collection-contract.json",
                contract_source)
            collection_receipt = {
                "schema": 1,
                "kind": "candle-great100-two-sweep-reference-receipt",
                "contract_sha256": top100_manifest._canonical_sha256(
                    collection_contract),
                "contract": {**contract_record,
                             "path": "collection-contract.json"},
                "sweep_count": 2, "target_count": 65,
                "total_target_runs": 130, "completed_target_runs": 130,
                "pending_target_runs": 0, "failure_attempt_count": 0,
                "failures": [], "publication_interruptions": [],
                "outcome": "complete", "closed": True,
                "approval_status": "candidates_unapproved",
                "promotion_allowed": False,
                "sweeps": [{
                    "sweep": sweep, "target_count": 65,
                    "completed_count": 65, "pending_count": 0,
                    "targets": collection_rows[sweep],
                } for sweep in (1, 2)],
            }
            receipt_source = (
                json.dumps(collection_receipt, indent=2, sort_keys=True) +
                "\n").encode()
            receipt_record = record(
                "candle/evidence/collection/receipt.json", receipt_source)
            _, inventory_sha256 = top100_manifest._inventory_contract(targets)
            approval = {
                "schema": "candle-s1-identity-approval-v2",
                "artifact_kind":
                    "independently-reviewed-ocaml-reference-identities",
                "approval_status": "approved", "promotion_allowed": True,
                "inventory_contract_sha256": inventory_sha256,
                "serializer_sha256": serializer_sha256,
                "reference_policy": {
                    key: source_contract_payload[key] for key in (
                        "historical_upstream_commit",
                        "exact_source_reference_commit",
                        "compatibility_deltas")
                },
                "review": {
                    "reviewer": "independent-reviewer",
                    "approved_utc": "2026-08-29T00:00:00+00:00",
                    "review_commit": "f" * 40,
                    "decision":
                        "two-reference-runs-identical-and-source-deltas-reviewed",
                },
                "collection_evidence": {
                    "contract": contract_record,
                    "receipt": receipt_record,
                },
                "targets": approved_targets,
            }
            approval_path = root / "candle/top100_identity_approval.json"
            approval_path.write_text(
                json.dumps(approval, indent=2) + "\n", encoding="utf-8")
            with (mock.patch.object(top100_manifest, "ROOT", root),
                  mock.patch.object(
                      top100_manifest, "IDENTITY_APPROVAL", approval_path),
                  mock.patch.object(top100_manifest,
                                    "REFERENCE_SOURCE_CONTRACT",
                                    reference_source_contract)):
                loaded, artifact_sha256, expected, _ = \
                    top100_manifest._load_identity_approval(targets)
                self.assertTrue(loaded["promotion_allowed"])
                self.assertEqual(len(expected), 65)
                self.assertEqual(
                    expected[targets[0]["name"]]["approval_sha256"],
                    artifact_sha256)
                approval["reference_policy"][
                    "exact_source_reference_commit"] = \
                    "6ce6fc15ed6a399902757a294bc59c954ebbbd85"
                approval_path.write_text(
                    json.dumps(approval, indent=2) + "\n", encoding="utf-8")
                with self.assertRaisesRegex(
                        ValueError, "reference commits are not pinned"):
                    top100_manifest._load_identity_approval(targets)
                approval["reference_policy"][
                    "exact_source_reference_commit"] = \
                    top100_manifest.EXACT_SOURCE_REFERENCE_COMMIT
                approval_path.write_text(
                    json.dumps(approval, indent=2) + "\n", encoding="utf-8")
                first_artifacts = approved_targets[0]["reference_runs"][0][
                    "artifacts"]
                for artifact_name, replacement in (
                        ("candidate", b"arbitrary candidate text\n"),
                        ("plan", b"arbitrary plan text\n"),
                        ("request", b"arbitrary request text\n"),
                        ("transcript", b"arbitrary transcript text\n")):
                    record_value = first_artifacts[artifact_name]
                    artifact_path = root / record_value["path"]
                    original_source = artifact_path.read_bytes()
                    artifact_path.write_bytes(replacement)
                    record_value["bytes"] = len(replacement)
                    record_value["sha256"] = top100_manifest.hashlib.sha256(
                        replacement).hexdigest()
                    approval_path.write_text(
                        json.dumps(approval, indent=2) + "\n", encoding="utf-8")
                    with self.assertRaisesRegex(
                            ValueError, "replay|malformed"):
                        top100_manifest._load_identity_approval(targets)
                    artifact_path.write_bytes(original_source)
                    record_value["bytes"] = len(original_source)
                    record_value["sha256"] = top100_manifest.hashlib.sha256(
                        original_source).hexdigest()
                    approval_path.write_text(
                        json.dumps(approval, indent=2) + "\n", encoding="utf-8")
                plan_record = first_artifacts["plan"]
                plan_path = root / plan_record["path"]
                original_plan_source = plan_path.read_bytes()
                original_plan = json.loads(original_plan_source)
                plan_mutations = []
                changed_target = json.loads(json.dumps(original_plan))
                changed_target["input"]["target"] = "100/wrong-target"
                plan_mutations.append((changed_target, "target contract"))
                changed_head = json.loads(json.dumps(original_plan))
                changed_head["reference"]["git_head"] = "1" * 40
                plan_mutations.append((changed_head, "reference head"))
                changed_nonce = json.loads(json.dumps(original_plan))
                changed_nonce["session_nonce"] = "2" * 64
                plan_mutations.append((changed_nonce, "plan session"))
                changed_contract = json.loads(json.dumps(original_plan))
                changed_contract["input"]["source_contract"][
                    "compatibility_deltas"][0]["reason"] = "unreviewed rewrite"
                plan_mutations.append((changed_contract, "source contract"))
                changed_external = json.loads(json.dumps(original_plan))
                changed_external["reference"]["external_runtime"] = {}
                plan_mutations.append((changed_external, "external-runtime"))
                changed_environment = json.loads(json.dumps(original_plan))
                changed_environment["fresh_process_contract"][
                    "runtime_environment"]["LD_PRELOAD"] = "/tmp/evil.so"
                plan_mutations.append((changed_environment, "external-runtime"))
                changed_runtime = json.loads(json.dumps(original_plan))
                changed_runtime["reference"]["runtime_executable"] = {}
                plan_mutations.append((changed_runtime, "external-runtime"))
                for changed_plan, diagnostic in plan_mutations:
                    changed_source = (
                        json.dumps(changed_plan, indent=2) + "\n").encode()
                    plan_path.write_bytes(changed_source)
                    plan_record["bytes"] = len(changed_source)
                    plan_record["sha256"] = top100_manifest.hashlib.sha256(
                        changed_source).hexdigest()
                    approval_path.write_text(
                        json.dumps(approval, indent=2) + "\n", encoding="utf-8")
                    with self.assertRaisesRegex(ValueError, diagnostic):
                        top100_manifest._load_identity_approval(targets)
                plan_path.write_bytes(original_plan_source)
                plan_record["bytes"] = len(original_plan_source)
                plan_record["sha256"] = top100_manifest.hashlib.sha256(
                    original_plan_source).hexdigest()
                approval_path.write_text(
                    json.dumps(approval, indent=2) + "\n", encoding="utf-8")
                theorem_identity = approved_targets[0]["expected_identity"][
                    "theorems"][0]
                original_theorem_sha256 = theorem_identity["theorem_sha256"]
                theorem_identity["theorem_sha256"] = "f" * 64
                approval_path.write_text(
                    json.dumps(approval, indent=2) + "\n", encoding="utf-8")
                with self.assertRaisesRegex(
                        ValueError, "replay identity projection"):
                    top100_manifest._load_identity_approval(targets)
                theorem_identity["theorem_sha256"] = original_theorem_sha256
                approval_path.write_text(
                    json.dumps(approval, indent=2) + "\n", encoding="utf-8")
                changed = root / approved_targets[0]["reference_runs"][0][
                    "artifacts"]["transcript"]["path"]
                alias = changed.with_name(changed.name + "-hardlink")
                alias.hardlink_to(changed)
                with self.assertRaisesRegex(ValueError, "ordinary transcript"):
                    top100_manifest._load_identity_approval(targets)
                alias.unlink()
                changed.write_bytes(changed.read_bytes() + b"mutation")
                with self.assertRaisesRegex(ValueError, "changed transcript"):
                    top100_manifest._load_identity_approval(targets)


if __name__ == "__main__":
    unittest.main()
