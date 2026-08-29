#!/usr/bin/env python3
"""Lightweight tests for fail-closed HOL Light reference collection."""

import copy
import fcntl
import hashlib
import json
import os
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
        real_git = reference._git
        self.git_patch = mock.patch.object(
            reference, "_git",
            side_effect=lambda root, *args:
                reference.EXACT_SOURCE_REFERENCE_COMMIT
                if args == ("rev-parse", "HEAD") else real_git(root, *args))
        self.git_patch.start()
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
        self.git_patch.stop()

    def _fake_reference(self, directory, matching_source=True):
        container = Path(directory)
        root = container / "reference"
        root.mkdir()
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
        gp_root = container / "pari-gp"
        gp_bin = gp_root / "usr/bin"
        gp_bin.mkdir(parents=True)
        gp_executable = gp_bin / "gp-2.15"
        gp_executable.write_text(
            "#!/bin/sh\n"
            "if [ \"$1\" = --version-short ]; then "
            "printf '2.15.4\\n'; exit 0; fi\n"
            "while IFS= read -r ignored; do :; done\n"
            "printf '[3, 1; 5, 1]\\n'\n")
        gp_executable.chmod(0o755)
        (gp_bin / "gp").symlink_to("gp-2.15")
        (gp_root / "candle-gprc").write_text(
            "\\\\ deterministic empty test configuration\n")
        (gp_root / "candle-gprc").chmod(0o444)
        (gp_root / "candle-data").mkdir()
        (gp_root / "candle-data").chmod(0o555)
        (container / "pari-gp.deb").write_text("pinned package archive\n")
        (container / "pari-gp.deb").chmod(0o444)
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

    def _build_plan(self, target, root, runtime, runtime_stublib, ocamlc,
                    ocamlfind, nonce=NONCE, source_mode="manifest-exact"):
        root = Path(root)
        return reference.build_plan(
            target, root, runtime, runtime_stublib, ocamlc, ocamlfind,
            root.parent / "pari-gp", root.parent / "pari-gp.deb",
            Path("/bin/sh"),
            nonce, source_mode)

    def test_plan_pins_clean_tree_order_and_exact_request(self):
        with tempfile.TemporaryDirectory() as directory:
            root, runtime, runtime_stublib, ocamlc, ocamlfind = self._fake_reference(
                directory)
            plan = self._build_plan(
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
        external = plan["reference"]["external_runtime"]
        self.assertEqual(
            external["policy"],
            "single_private_path_gp_with_pinned_shell_v1")
        self.assertEqual(external["pari_gp_version"]["stdout"], "2.15.4\n")
        self.assertIn("[3, 1; 5, 1]", external["probe"]["stdout"])
        self.assertEqual(
            plan["fresh_process_contract"]["runtime_environment"]["PATH"],
            str(root.parent / "pari-gp/usr/bin"))
        self.assertEqual(
            plan["fresh_process_contract"]["runtime_environment"]["GPRC"],
            str(root.parent / "pari-gp/candle-gprc"))

    def test_external_gp_bytes_are_rechecked_after_planning(self):
        with tempfile.TemporaryDirectory() as directory:
            root, runtime, runtime_stublib, ocamlc, ocamlfind = \
                self._fake_reference(directory)
            plan = self._build_plan(
                "100/gcd", root, runtime, runtime_stublib, ocamlc,
                ocamlfind, NONCE)
            gp = root.parent / "pari-gp/usr/bin/gp-2.15"
            gp.write_bytes(gp.read_bytes() + b"\n# changed after plan\n")
            with self.assertRaisesRegex(
                    reference.CollectionError, "inputs differ"):
                reference._require_current_plan_pins(plan)

    def test_plan_rejects_source_mismatch_and_manual_mapping(self):
        with tempfile.TemporaryDirectory() as directory:
            root, runtime, runtime_stublib, ocamlc, ocamlfind = self._fake_reference(
                directory, matching_source=False)
            with self.assertRaisesRegex(
                    reference.CollectionError, "differs from manifest"):
                self._build_plan(
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
                self._build_plan(
                    "manual-fixture", "/missing", "/missing", "/missing",
                    "/missing", "/missing", NONCE)

    def test_historical_mode_requires_exact_historical_head(self):
        with tempfile.TemporaryDirectory() as directory:
            root, runtime, runtime_stublib, ocamlc, ocamlfind = \
                self._fake_reference(directory)
            with self.assertRaisesRegex(
                    reference.CollectionError, "exact upstream HEAD"):
                self._build_plan(
                    "100/gcd", root, runtime, runtime_stublib, ocamlc,
                    ocamlfind, NONCE, source_mode="historical-original")

    def test_manifest_exact_mode_rejects_reduced_candle_fork_head(self):
        with tempfile.TemporaryDirectory() as directory:
            root, runtime, runtime_stublib, ocamlc, ocamlfind = \
                self._fake_reference(directory)
            with mock.patch.object(
                    reference, "_git",
                    side_effect=lambda _root, *args:
                        "6ce6fc15ed6a399902757a294bc59c954ebbbd85"
                        if args == ("rev-parse", "HEAD") else ""):
                with self.assertRaisesRegex(
                        reference.CollectionError, "exact reference HEAD"):
                    self._build_plan(
                        "100/gcd", root, runtime, runtime_stublib, ocamlc,
                        ocamlfind, NONCE)

    def test_controller_lock_descriptor_is_checked_and_inheritable(self):
        with tempfile.TemporaryDirectory() as directory:
            lock_path = Path(directory) / "controller.lock"
            lock_path.write_text("lock\n")
            descriptor = os.open(lock_path, os.O_RDONLY)
            try:
                fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
                with mock.patch.dict(os.environ, {
                        reference.CONTROLLER_LOCK_FD_ENV: str(descriptor)}):
                    self.assertEqual(
                        reference._controller_lock_pass_fds(), (descriptor,))
                    completed = subprocess.run(
                        ["/bin/sh", "-c",
                         f"test -f /proc/self/fd/{descriptor}"],
                        pass_fds=reference._controller_lock_pass_fds(),
                        check=False)
                    self.assertEqual(completed.returncode, 0)
            finally:
                os.close(descriptor)
        with mock.patch.dict(os.environ, {
                reference.CONTROLLER_LOCK_FD_ENV: "not-a-descriptor"}):
            with self.assertRaisesRegex(
                    reference.CollectionError, "malformed inherited"):
                reference._controller_lock_pass_fds()

    def test_collector_starts_with_isolated_stdlib_only_python(self):
        completed = subprocess.run(
            ["/usr/bin/python3", "-I", "-S", str(Path(reference.__file__)),
             "--help"],
            env={"PATH": "/usr/bin:/bin", "LC_ALL": "C", "LANG": "C"},
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            check=False)
        self.assertEqual(completed.returncode, 0, completed.stderr)
        self.assertIn("{plan,collect,validate}", completed.stdout)

    def test_isolated_protocol_loader_rejects_changed_sibling(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            collector = root / "reference_fingerprints.py"
            protocol = root / "reference_protocol.py"
            collector.write_bytes(Path(reference.__file__).read_bytes())
            protocol.write_bytes(
                Path(reference.regression.__file__).read_bytes() + b"\n# changed\n")
            completed = subprocess.run(
                ["/usr/bin/python3", "-I", "-S", str(collector), "--help"],
                env={"PATH": "/usr/bin:/bin", "LC_ALL": "C", "LANG": "C"},
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                check=False)
        self.assertNotEqual(completed.returncode, 0)
        self.assertIn("differs from collector pin", completed.stderr)

    def test_runner_and_reference_protocol_share_wire_behavior(self):
        theorem_names = ["EGCD", "Module.RESULT"]
        self.assertEqual(
            regression._fingerprint_request_source(theorem_names),
            reference.regression._fingerprint_request_source(theorem_names))
        self.assertEqual(
            regression.FINGERPRINT_MARKER,
            reference.regression.FINGERPRINT_MARKER)
        self.assertEqual(
            regression.STATE_FINGERPRINT_MARKER,
            reference.regression.STATE_FINGERPRINT_MARKER)
        self.assertEqual(
            regression.EMPTY_HYPOTHESES_WIRE,
            reference.regression.EMPTY_HYPOTHESES_WIRE)

    def test_exact_three_delta_contract_matches_both_git_sides(self):
        contract = reference._load_source_contract()
        self.assertEqual(
            contract["exact_source_reference_commit"],
            reference.EXACT_SOURCE_REFERENCE_COMMIT)
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
        parents = subprocess.check_output([
            "/usr/bin/git", "-C", str(reference.ROOT), "rev-list",
            "--parents", "-n1", contract["exact_source_reference_commit"],
        ], text=True).split()
        self.assertEqual(parents, [
            contract["exact_source_reference_commit"],
            contract["historical_upstream_commit"],
        ])
        changed = subprocess.check_output([
            "/usr/bin/git", "-C", str(reference.ROOT), "diff-tree",
            "--no-commit-id", "--name-only", "-r",
            contract["exact_source_reference_commit"],
        ], text=True).splitlines()
        self.assertEqual(set(changed), {
            delta["path"] for delta in contract["compatibility_deltas"]})

    def test_rejected_candle_fork_reference_contract_fails(self):
        contract = json.loads(reference.SOURCE_CONTRACT.read_text())
        contract["exact_source_reference_commit"] = \
            "6ce6fc15ed6a399902757a294bc59c954ebbbd85"
        with tempfile.TemporaryDirectory() as directory:
            source_contract = Path(directory) / "source-contract.json"
            source_contract.write_text(json.dumps(contract) + "\n")
            with mock.patch.object(
                    reference, "SOURCE_CONTRACT", source_contract):
                with self.assertRaisesRegex(
                        reference.CollectionError, "unsupported exact"):
                    reference._load_source_contract()

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
            plan = self._build_plan(
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
