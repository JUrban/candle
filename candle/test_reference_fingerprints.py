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
    def _fake_reference(self, directory, matching_source=True):
        root = Path(directory)
        (root / "100").mkdir()
        source = (reference.ROOT / "100/gcd.ml").read_bytes()
        if not matching_source:
            source += b"\n(* changed reference *)\n"
        (root / "100/gcd.ml").write_bytes(source)
        (root / "hol.ml").write_text("(* pinned fake hol root *)\n")
        launcher = root / "hol.sh"
        runtime = root / "ocaml-hol"
        ocamlc = root / "ocamlc"
        record = "\t".join([
            regression.FINGERPRINT_MARKER,
            b"EGCD".hex(), b"theorem".hex(), b"hypotheses".hex(),
            b"conclusion".hex(), b"axioms".hex(), "0", "3",
        ])
        launcher.write_text(
            "#!/bin/sh\n"
            "cat >/dev/null\n"
            f"printf '%s\\n' '{reference.SESSION_MARKER}\t{NONCE}'\n"
            f"printf '%s\\n' '{record}'\n"
            f"printf '%s\\n' '{reference.COMPLETE_MARKER}\t{NONCE}'\n")
        runtime.write_text("#!/bin/sh\nexit 99\n")
        ocamlc.write_text("#!/bin/sh\nprintf '4.14.1\\n'\n")
        for executable in (launcher, runtime, ocamlc):
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
        return root, launcher, runtime, ocamlc

    def test_plan_pins_clean_tree_order_and_exact_request(self):
        with tempfile.TemporaryDirectory() as directory:
            root, launcher, runtime, ocamlc = self._fake_reference(directory)
            plan = reference.build_plan(
                "100/gcd", root, launcher, runtime, ocamlc, NONCE)
        self.assertEqual(plan["status"], "planned_not_executed")
        self.assertTrue(plan["fresh_process_contract"]["required"])
        self.assertFalse(
            plan["fresh_process_contract"]["preloaded_checkpoint_allowed"])
        self.assertEqual(
            [item["relative_path"] for item in plan["input"]["load_files"]],
            ["100/gcd.ml"])
        self.assertEqual(plan["input"]["theorem_names"], ["EGCD"])
        source = plan["request"]["source"]
        self.assertLess(source.index("candle/fingerprint.ml"),
                        source.index('loadt "100/gcd.ml"'))
        self.assertLess(source.index('loadt "100/gcd.ml"'),
                        source.index('candle_s1_emit_fingerprint "EGCD" EGCD'))
        self.assertIn(reference.SESSION_MARKER + "\\t" + NONCE, source)
        self.assertEqual(
            plan["request"]["sha256"],
            hashlib.sha256(source.encode()).hexdigest())

    def test_plan_rejects_source_mismatch_and_manual_mapping(self):
        with tempfile.TemporaryDirectory() as directory:
            root, launcher, runtime, ocamlc = self._fake_reference(
                directory, matching_source=False)
            with self.assertRaisesRegex(
                    reference.CollectionError, "differs from manifest"):
                reference.build_plan(
                    "100/gcd", root, launcher, runtime, ocamlc, NONCE)
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
                    "/missing", NONCE)

    def test_transcript_produces_only_an_unapproved_candidate(self):
        plan = {
            "schema": "candle-s1-reference-plan-v1",
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
            b"EGCD".hex(), b"theorem".hex(), b"hypotheses".hex(),
            b"conclusion".hex(), b"axioms".hex(), "0", "3",
        ]
        transcript = "\n".join([
            f"{reference.SESSION_MARKER}\t{NONCE}",
            "\t".join(fields),
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
                [], candidate, reference._sha256(reference.SERIALIZER),
                "audited")

    def test_collect_spawns_process_rechecks_pins_and_writes_candidate(self):
        with tempfile.TemporaryDirectory() as directory:
            root, launcher, runtime, ocamlc = self._fake_reference(directory)
            plan = reference.build_plan(
                "100/gcd", root, launcher, runtime, ocamlc, NONCE)
            transcript = root.parent / "transcript.log"
            candidate_path = root.parent / "candidate.json"
            reference.collect(plan, transcript, candidate_path, 10)
            candidate = json.loads(candidate_path.read_text())
            reference.validate_candidate(candidate)
            self.assertIn(reference.COMPLETE_MARKER, transcript.read_text())
            self.assertEqual(
                candidate["plan_pins"]["reference"]["git_head"],
                plan["reference"]["git_head"])

    def test_candidate_validation_and_markers_fail_closed(self):
        with self.assertRaisesRegex(
                reference.CollectionError, "session markers"):
            reference.candidate_from_transcript({
                "schema": "candle-s1-reference-plan-v1",
                "session_nonce": NONCE,
                "input": {"theorem_names": [], "mapping_status": "audited"},
            }, "")
        candidate = {
            "schema": reference.CANDIDATE_SCHEMA,
            "artifact_kind": "reference_identity_candidate",
            "approval_status": "candidate_unapproved",
            "promotion_allowed": True,
            "warning": "x", "plan_pins": {}, "session_nonce": NONCE,
            "process_exit_code": 0, "transcript_sha256": "0" * 64,
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
            "schema": "candle-s1-reference-plan-v1",
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
            b"EGCD".hex(), b"theorem".hex(), b"hypotheses".hex(),
            b"conclusion".hex(), b"axioms".hex(), "0", "3",
        ])
        transcript = "\n".join([
            record,
            f"{reference.SESSION_MARKER}\t{NONCE}",
            f"{reference.COMPLETE_MARKER}\t{NONCE}",
            "",
        ])
        with self.assertRaisesRegex(
                reference.CollectionError, "outside reference session"):
            reference.candidate_from_transcript(plan, transcript)


if __name__ == "__main__":
    unittest.main()
