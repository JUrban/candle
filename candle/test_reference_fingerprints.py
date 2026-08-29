#!/usr/bin/env python3
"""Lightweight tests for fail-closed HOL Light reference collection."""

import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import reference_fingerprints as reference
import regression


NONCE = "ab" * 32


class ReferenceFingerprintTest(unittest.TestCase):
    @staticmethod
    def _state_record(axioms=b"axioms"):
        return "\t".join([
            regression.STATE_FINGERPRINT_MARKER,
            b"state".hex(), b"types".hex(), b"constants".hex(),
            b"definitions".hex(), axioms.hex(), "1", "2", "3", "3",
        ])

    def setUp(self):
        collector_sha256 = reference._sha256(Path(reference.__file__))
        self.collector_patch = mock.patch.object(
            reference, "_collector_repository_pin", return_value={
                "root": str(reference.ROOT),
                "git_head": "3" * 40,
                "git_status": [],
                "collector_relative_path": "candle/reference_fingerprints.py",
                "collector_at_head_sha256": collector_sha256,
                "collector_matches_head": True,
            })
        self.collector_patch.start()

    def tearDown(self):
        self.collector_patch.stop()

    def _fake_reference(self, directory, matching_source=True):
        root = Path(directory)
        (root / "100").mkdir()
        source = (reference.ROOT / "100/gcd.ml").read_bytes()
        if not matching_source:
            source += b"\n(* changed reference *)\n"
        (root / "100/gcd.ml").write_bytes(source)
        (root / "hol.ml").write_text("(* pinned fake hol root *)\n")
        (root / "hol_loader.cmo").write_text("pinned loader\n")
        (root / "pa_j.cmo").write_text("pinned parser\n")
        (root / "load_camlp5_topfind.ml").write_text("pinned topfind loader\n")
        runtime = root / "ocaml-hol"
        runtime_stublib = root / "stublibs/dllzarith.so"
        runtime_stublib.parent.mkdir()
        ocaml_library = root / "ocaml-library"
        ocaml_library.mkdir()
        (ocaml_library / "topfind").write_text("pinned topfind\n")
        (ocaml_library / "stublibs").mkdir()
        (ocaml_library / "stublibs/dllunix.so").write_text(
            "pinned system stub\n")
        findlib_config = root / "ocamlfind.conf"
        findlib_config.write_text(f'path="{ocaml_library}"\n')
        ocamlc = root / "ocamlc"
        ocamlfind = root / "ocamlfind"
        record = "\t".join([
            regression.FINGERPRINT_MARKER,
            b"EGCD".hex(), b"theorem".hex(),
            regression.EMPTY_HYPOTHESES_WIRE.hex(),
            b"conclusion".hex(), b"axioms".hex(), "0", "3",
        ])
        runtime.write_text(
            "#!/bin/sh\n"
            "cat >/dev/null\n"
            f"printf '%s\\n' '{reference.SESSION_MARKER}\t{NONCE}'\n"
            f"printf '%s\\n' '{record}'\n"
            f"printf '%s\\n' '{self._state_record()}'\n"
            f"printf '%s\\n' '{reference.COMPLETE_MARKER}\t{NONCE}'\n")
        runtime_stublib.write_text("pinned runtime stub\n")
        ocamlc.write_text(
            "#!/bin/sh\n"
            f"if [ \"$1\" = -where ]; then printf '%s\\n' '{ocaml_library}'; "
            "else printf '4.14.1\\n'; fi\n")
        ocamlfind.write_text(
            "#!/bin/sh\n"
            "if [ \"$1\" = query ]; then printf '1.9.6\\n'; "
            f"elif [ \"$2\" = conf ]; then printf '%s\\n' '{findlib_config}'; "
            f"elif [ \"$2\" = path ]; then printf '%s\\n' '{ocaml_library}'; "
            "else exit 2; fi\n")
        for executable in (runtime, ocamlc, ocamlfind):
            executable.chmod(0o755)
        subprocess.run(["git", "init", "-q", str(root)], check=True)
        subprocess.run(
            ["git", "-C", str(root), "config", "user.email", "test@example"],
            check=True)
        subprocess.run(
            ["git", "-C", str(root), "config", "user.name", "test"],
            check=True)
        subprocess.run(
            ["git", "-C", str(root), "add", "."], check=True)
        subprocess.run(
            ["git", "-C", str(root), "commit", "-qm", "fixture"],
            check=True)
        return root, runtime, runtime_stublib, ocamlc, ocamlfind

    def test_plan_pins_clean_tree_order_and_exact_request(self):
        with tempfile.TemporaryDirectory() as directory:
            root, runtime, runtime_stublib, ocamlc, ocamlfind = self._fake_reference(
                directory)
            plan = reference.build_plan(
                "100/gcd", root, runtime, runtime_stublib, ocamlc,
                ocamlfind, NONCE)
        self.assertEqual(plan["status"], "planned_not_executed")
        self.assertTrue(plan["fresh_process_contract"]["required"])
        self.assertFalse(
            plan["fresh_process_contract"]["preloaded_checkpoint_allowed"])
        self.assertEqual(
            plan["fresh_process_contract"]["runtime_argv"][-1], "-noprompt")
        self.assertEqual(
            [item["relative_path"] for item in plan["input"]["load_files"]],
            ["100/gcd.ml"])
        self.assertEqual(plan["input"]["theorem_names"], ["EGCD"])
        self.assertEqual(plan["input"]["source_mode"], "manifest-exact")
        self.assertEqual(
            len(plan["input"]["source_contract"]["compatibility_deltas"]), 3)
        source = plan["request"]["source"]
        self.assertLess(source.index("candle/fingerprint.ml"),
                        source.index('loadt "100/gcd.ml"'))
        self.assertLess(source.index('loadt "100/gcd.ml"'),
                        source.index('candle_s1_emit_fingerprint "EGCD" EGCD'))
        self.assertIn(reference.SESSION_MARKER + "\\t" + NONCE, source)
        self.assertEqual(
            plan["request"]["sha256"],
            hashlib.sha256(source.encode()).hexdigest())
        self.assertEqual(
            plan["reference"]["runtime_interpreter"]["path"],
            str(Path("/bin/sh").resolve()))
        self.assertEqual(
            plan["reference"]["generated_boot_files"][0]["path"],
            str(root / "hol_loader.cmo"))
        self.assertEqual(
            plan["reference"]["ocaml_library_tree"]["entry_count"], 3)
        self.assertEqual(
            [Path(item["path"]).name
             for item in plan["reference"]["runtime_stub_files"]],
            ["dllunix.so", "dllzarith.so"])
        self.assertEqual(
            plan["fresh_process_contract"]["runtime_environment"]
                ["OCAMLFIND_CONF"],
            str(root / "ocamlfind.conf"))
        self.assertEqual(
            plan["reference"]["findlib"]["package_roots"][0]
                ["inventory_sha256"],
            plan["reference"]["ocaml_library_tree"]["inventory_sha256"])

    def test_plan_rejects_source_mismatch_and_manual_mapping(self):
        with tempfile.TemporaryDirectory() as directory:
            root, runtime, runtime_stublib, ocamlc, ocamlfind = self._fake_reference(
                directory, matching_source=False)
            with self.assertRaisesRegex(
                    reference.CollectionError, "differs from manifest"):
                reference.build_plan(
                    "100/gcd", root, runtime, runtime_stublib, ocamlc,
                    ocamlfind, NONCE)
        manual_target = {
            "fingerprint_request": {
                "mapping_status": "manual_review",
                "expected_identities": None,
            },
        }
        with mock.patch.object(
                reference, "_target_from_manifest",
                return_value=({}, manual_target)):
            with self.assertRaisesRegex(
                    reference.CollectionError, "manual-review"):
                reference.build_plan(
                    "manual-fixture", "/missing", "/missing", "/missing",
                    "/missing", "/missing", NONCE)

    def test_historical_mode_requires_exact_historical_head(self):
        with tempfile.TemporaryDirectory() as directory:
            root, runtime, runtime_stublib, ocamlc, ocamlfind = \
                self._fake_reference(directory)
            with self.assertRaisesRegex(
                    reference.CollectionError, "exact upstream HEAD"):
                reference.build_plan(
                    "100/gcd", root, runtime, runtime_stublib, ocamlc,
                    ocamlfind, NONCE, source_mode="historical-original")

    def test_exact_three_delta_contract_matches_both_git_sides(self):
        contract = reference._load_source_contract()
        self.assertEqual(len(contract["compatibility_deltas"]), 3)
        for delta in contract["compatibility_deltas"]:
            historical = subprocess.check_output([
                "/usr/bin/git", "-C", str(reference.ROOT), "show",
                f"{contract['historical_upstream_commit']}:{delta['path']}",
            ])
            self.assertEqual(
                hashlib.sha256(historical).hexdigest(),
                delta["historical_sha256"])
            self.assertEqual(
                reference._sha256(reference.ROOT / delta["path"]),
                delta["selected_sha256"])
            selected = subprocess.check_output([
                "/usr/bin/git", "-C", str(reference.ROOT), "show",
                f"{contract['exact_source_reference_commit']}:{delta['path']}",
            ])
            self.assertEqual(
                hashlib.sha256(selected).hexdigest(), delta["selected_sha256"])
        changed = subprocess.check_output([
            "/usr/bin/git", "-C", str(reference.ROOT), "diff", "--name-only",
            contract["historical_upstream_commit"],
            contract["exact_source_reference_commit"], "--", "100/*.ml",
        ], text=True).splitlines()
        self.assertEqual(set(changed), {
            delta["path"] for delta in contract["compatibility_deltas"]})

    def test_transcript_produces_only_an_unapproved_candidate(self):
        plan = {
            "schema": reference.PLAN_SCHEMA,
            "session_nonce": NONCE,
            "fresh_process_contract": {"required": True},
            "reference": {"git_head": "1" * 40},
            "input": {
                "target": "100/gcd", "theorem_names": ["EGCD"],
                "mapping_status": "audited"},
            "request": {"sha256": "2" * 64},
        }
        fields = [
            regression.FINGERPRINT_MARKER,
            b"EGCD".hex(), b"theorem".hex(),
            regression.EMPTY_HYPOTHESES_WIRE.hex(),
            b"conclusion".hex(), b"axioms".hex(), "0", "3",
        ]
        transcript = "\n".join([
            f"{reference.SESSION_MARKER}\t{NONCE}",
            "\t".join(fields),
            self._state_record(),
            f"{reference.COMPLETE_MARKER}\t{NONCE}",
            "",
        ])
        candidate = reference.candidate_from_transcript(plan, transcript)
        reference.validate_candidate(candidate)
        self.assertEqual(candidate["approval_status"], "candidate_unapproved")
        self.assertFalse(candidate["promotion_allowed"])
        self.assertEqual(
            candidate["candidate_identities"]["status"],
            "observed_uncompared")
        self.assertNotIn("expected_identities", candidate)
        with self.assertRaisesRegex(
                regression.LoadFailure, "malformed expected"):
            regression._match_expected_identities(
                [], {}, candidate, reference._sha256(reference.SERIALIZER),
                "audited")

    def test_collect_spawns_process_rechecks_pins_and_writes_candidate(self):
        with tempfile.TemporaryDirectory() as directory:
            root, runtime, runtime_stublib, ocamlc, ocamlfind = \
                self._fake_reference(directory)
            plan = reference.build_plan(
                "100/gcd", root, runtime, runtime_stublib, ocamlc,
                ocamlfind, NONCE)
            transcript = root.parent / "transcript.log"
            candidate_path = root.parent / "candidate.json"
            reference.collect(plan, transcript, candidate_path, 10)
            candidate = json.loads(candidate_path.read_text())
            reference.validate_candidate(
                candidate, plan, plan["request"]["source"],
                transcript.read_text())
            self.assertIn(reference.COMPLETE_MARKER, transcript.read_text())
            self.assertEqual(
                candidate["plan_pins"]["reference"]["git_head"],
                plan["reference"]["git_head"])

    def test_candidate_validation_and_markers_fail_closed(self):
        with self.assertRaisesRegex(
                reference.CollectionError, "session markers"):
            reference.candidate_from_transcript({
                "schema": reference.PLAN_SCHEMA,
                "session_nonce": NONCE,
                "input": {"theorem_names": [], "mapping_status": "audited"},
            }, "")
        candidate = {
            "schema": reference.CANDIDATE_SCHEMA,
            "artifact_kind": "reference_identity_candidate",
            "approval_status": "candidate_unapproved",
            "promotion_allowed": True,
            "warning": "x", "plan_pins": {}, "session_nonce": NONCE,
            "process_exit_code": 0,
            "artifact_hashes": {
                "plan_sha256": "0" * 64,
                "request_sha256": "0" * 64,
                "transcript_sha256": "0" * 64,
            },
            "candidate_identities": {"status": "observed_uncompared"},
        }
        with self.assertRaisesRegex(reference.CollectionError, "fail-closed"):
            reference.validate_candidate(candidate)
        extra = copy.deepcopy(candidate)
        extra["promotion_allowed"] = False
        extra["expected_identities"] = {}
        with self.assertRaisesRegex(reference.CollectionError, "fields"):
            reference.validate_candidate(extra)

    def test_fingerprint_outside_nonce_markers_fails_closed(self):
        plan = {
            "schema": reference.PLAN_SCHEMA,
            "session_nonce": NONCE,
            "fresh_process_contract": {"required": True},
            "reference": {"git_head": "1" * 40},
            "input": {
                "target": "100/gcd", "theorem_names": ["EGCD"],
                "mapping_status": "audited"},
            "request": {"sha256": "2" * 64},
        }
        record = "\t".join([
            regression.FINGERPRINT_MARKER,
            b"EGCD".hex(), b"theorem".hex(),
            regression.EMPTY_HYPOTHESES_WIRE.hex(),
            b"conclusion".hex(), b"axioms".hex(), "0", "3",
        ])
        transcript = "\n".join([
            record,
            f"{reference.SESSION_MARKER}\t{NONCE}",
            self._state_record(),
            f"{reference.COMPLETE_MARKER}\t{NONCE}",
            "",
        ])
        with self.assertRaisesRegex(
                reference.CollectionError, "outside reference session"):
            reference.candidate_from_transcript(plan, transcript)

        state_outside = "\n".join([
            self._state_record(),
            f"{reference.SESSION_MARKER}\t{NONCE}", record,
            f"{reference.COMPLETE_MARKER}\t{NONCE}", "",
        ])
        with self.assertRaisesRegex(
                reference.CollectionError, "outside reference session"):
            reference.candidate_from_transcript(plan, state_outside)

    def test_linked_artifact_validation_rejects_tampering(self):
        plan = {
            "schema": reference.PLAN_SCHEMA,
            "session_nonce": NONCE,
            "fresh_process_contract": {"required": True},
            "reference": {"git_head": "1" * 40},
            "input": {
                "target": "100/gcd", "theorem_names": ["EGCD"],
                "mapping_status": "audited"},
            "request": {"source": "pinned request\n"},
        }
        plan["request"]["sha256"] = hashlib.sha256(
            plan["request"]["source"].encode()).hexdigest()
        record = "\t".join([
            regression.FINGERPRINT_MARKER,
            b"EGCD".hex(), b"theorem".hex(),
            regression.EMPTY_HYPOTHESES_WIRE.hex(),
            b"conclusion".hex(), b"axioms".hex(), "0", "3",
        ])
        transcript = "\n".join([
            f"{reference.SESSION_MARKER}\t{NONCE}", record,
            self._state_record(),
            f"{reference.COMPLETE_MARKER}\t{NONCE}", "",
        ])
        candidate = reference.candidate_from_transcript(plan, transcript)
        with self.assertRaisesRegex(
                reference.CollectionError, "transcript artifact hash mismatch"):
            reference.validate_candidate(
                candidate, plan, plan["request"]["source"], transcript + "x")


if __name__ == "__main__":
    unittest.main()
