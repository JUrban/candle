#!/usr/bin/env python3

import copy
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from contextlib import contextmanager
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cakeml_bootstrap_transition as subject


GIT_ENV = {
    "LC_ALL": "C",
    "PATH": "/usr/bin:/bin",
    "GIT_CONFIG_NOSYSTEM": "1",
    "GIT_CONFIG_GLOBAL": "/dev/null",
}


def git(root: Path, *arguments: str) -> str:
    return subprocess.run(
        ["/usr/bin/git", "-C", str(root), *arguments],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        env=GIT_ENV,
    ).stdout.strip()


def commit(root: Path, message: str) -> str:
    git(root, "add", ".")
    git(
        root, "-c", "user.name=Transition Test", "-c",
        "user.email=transition@example.invalid", "commit", "-qm", message,
    )
    return git(root, "rev-parse", "HEAD")


class TransitionFixture:
    def __init__(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name).resolve()
        self.source = self.root / "source"
        self.final = self.root / "final"
        self.cakeml = self.root / "cakeml"
        self.evidence = self.root / "evidence"
        self.evidence.mkdir()
        self.source.mkdir()
        self.cakeml.mkdir()
        git(self.source, "init", "-q")
        git(self.cakeml, "init", "-q")
        (self.cakeml / "pinned-input").write_text(
            "CakeML input closure\n", encoding="utf-8",
        )
        self.cakeml_head = commit(self.cakeml, "CakeML")
        manifest = {
            "dopen_corpus_contract": {
                "verified_cakeml_integration": {
                    "commit": self.cakeml_head,
                    "proof_hol4_commit": "a" * 40,
                },
            },
        }
        contents = {
            "build-local-cakeml-bootstrap.sh": b"#!/bin/bash -p\nbootstrap\n",
            "candle/cakeml_artifact_provenance.py": b"provenance controller\n",
            "candle/flyspeck_manifest.json": (
                json.dumps(manifest, sort_keys=True) + "\n"
            ).encode(),
            "candle/cake.S.patch": b"authenticated patch\n",
            "candle/insulate.py": b"link generator input\n",
        }
        for relative, value in contents.items():
            path = self.source / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(value)
        os.chmod(self.source / "build-local-cakeml-bootstrap.sh", 0o755)
        self.source_head = commit(self.source, "bootstrap source")
        subprocess.run(
            ["/usr/bin/git", "clone", "-q", str(self.source), str(self.final)],
            check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=GIT_ENV,
        )
        (self.final / "destination-only").write_text(
            "transition implementation is outside bootstrap input closure\n",
            encoding="utf-8",
        )
        self.final_head = commit(self.final, "later final Candle")
        self.receipt = self.evidence / "bootstrap-provenance.json"
        self.receipt.write_text("{}\n", encoding="utf-8")
        self.transition = self.evidence / "bootstrap-transition.json"

    def close(self) -> None:
        self.temporary.cleanup()

    def bootstrap(self) -> dict:
        pins = subject.provenance.expected_pins(self.source)
        return {
            "candle_root": str(self.source),
            "candle_commit": self.source_head,
            "cakeml_root": str(self.cakeml),
            "cakeml_commit": self.cakeml_head,
            **pins,
        }

    @contextmanager
    def authenticated_receipt(self):
        expected = self.bootstrap()

        def validate(candle_root, cakeml_root, record_path):
            self.assert_path(candle_root, self.source)
            self.assert_path(cakeml_root, self.cakeml)
            self.assert_path(record_path, self.receipt)
            return copy.deepcopy(expected)

        with mock.patch.object(
            subject, "validate_canonical_bootstrap_receipt",
            side_effect=validate,
        ):
            yield

    @staticmethod
    def assert_path(observed, expected) -> None:
        if Path(observed).resolve() != Path(expected).resolve():
            raise subject.provenance.ProvenanceError(
                "bootstrap receipt source Candle authority mismatch",
            )

    def arguments(self) -> tuple:
        return (
            self.source, self.source_head, self.final, self.final_head,
            self.cakeml, self.receipt,
        )


class CakeMLBootstrapTransitionTests(unittest.TestCase):
    def make_fixture(self) -> TransitionFixture:
        fixture = TransitionFixture()
        self.addCleanup(fixture.close)
        return fixture

    def test_isolated_cli_loads_exact_sibling_source(self) -> None:
        script = Path(subject.__file__).resolve()
        completed = subprocess.run(
            ["/usr/bin/python3", "-I", "-S", str(script), "--help"],
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            env={"LC_ALL": "C", "PATH": "/usr/bin:/bin"},
        )
        self.assertEqual(completed.returncode, 0, completed.stdout)
        self.assertIn("record-transition", completed.stdout)

    def test_schema7_is_diagnostic_and_schema6_promotion_gate_stays_closed(self) -> None:
        regression_source = (
            Path(subject.__file__).resolve().with_name("regression.py")
        ).read_text(encoding="utf-8")
        self.assertIn('linked_payload.get("schema") != 6', regression_source)
        self.assertEqual(subject.TRANSITION_LINKED_SCHEMA, 7)

    def test_exact_loader_ignores_adjacent_bytecode_cache(self) -> None:
        path = Path(subject.provenance.__file__)
        cache = path.parent / "__pycache__"
        cache.mkdir(exist_ok=True)
        injected = cache / "cakeml_artifact_provenance.cpython-312.pyc"
        prior = injected.read_bytes() if injected.exists() else None
        try:
            injected.write_bytes(b"untrusted adjacent bytecode")
            module = subject._load_exact_local_source(
                "_transition_bytecode_regression", path,
            )
            self.assertEqual(
                module.__candle_source_bytes__, path.read_bytes(),
            )
        finally:
            if prior is None:
                injected.unlink(missing_ok=True)
                try:
                    cache.rmdir()
                except OSError:
                    pass
            else:
                injected.write_bytes(prior)

    def test_canonical_validator_runs_exact_source_controller_directly(self) -> None:
        fixture = self.make_fixture()
        completed = subprocess.CompletedProcess(
            [], 0, b"bootstrap provenance PASS\n", b"",
        )
        with mock.patch.object(
            subject.subprocess, "run", return_value=completed,
        ) as run:
            self.assertEqual(
                subject.validate_canonical_bootstrap_receipt(
                    fixture.source, fixture.cakeml, fixture.receipt,
                ),
                {},
            )
        argv = run.call_args.args[0]
        self.assertEqual(argv[:3], ["/usr/bin/python3", "-I", "-S"])
        self.assertEqual(
            argv[3],
            str(fixture.source / "candle/cakeml_artifact_provenance.py"),
        )
        self.assertIn("check-bootstrap", argv)

    def test_transition_reconstructs_byte_identical_closure(self) -> None:
        fixture = self.make_fixture()
        with fixture.authenticated_receipt():
            record = subject.record_transition(
                *fixture.arguments(), fixture.transition,
            )
            observed, bootstrap = subject.validate_transition_record(
                *fixture.arguments(), fixture.transition,
            )
        self.assertEqual(observed, record)
        self.assertEqual(bootstrap["candle_commit"], fixture.source_head)
        self.assertEqual(record["comparison"], "byte_for_byte_equal")
        self.assertEqual(
            record["source_candle"]["closure"],
            record["final_candle"]["closure"],
        )
        self.assertEqual(fixture.transition.stat().st_mode & 0o777, 0o444)

    def test_retained_transition_reconstructs_source_commit_without_worktree(self) -> None:
        fixture = self.make_fixture()
        with fixture.authenticated_receipt():
            transition = subject.transition_derivation(*fixture.arguments())
        bootstrap = fixture.bootstrap()
        bootstrap["source_bootstrap_record"] = subject.provenance.file_record(
            fixture.receipt,
        )
        controller_sources = {}
        for relative in (
            "build-local-cakeml-bootstrap.sh",
            "candle/cakeml_artifact_provenance.py",
        ):
            identity = {
                field: transition["source_candle"]["closure"]["inputs"][relative][field]
                for field in ("bytes", "sha256")
            }
            controller_sources[relative] = {
                "repository_path": relative,
                "path": str(fixture.source / relative),
                **identity,
                "commit_blob": identity,
            }
        preflight = {
            "controller_sources": controller_sources,
            "python_controller": {
                "source": controller_sources[
                    "candle/cakeml_artifact_provenance.py"
                ],
            },
        }
        bootstrap["python_controller"] = preflight["python_controller"]
        subject.validate_retained_transition(
            transition, bootstrap, preflight, fixture.final, fixture.final_head,
        )

        forged = copy.deepcopy(transition)
        for side in ("source_candle", "final_candle"):
            closure = forged[side]["closure"]
            closure["inputs"]["candle/insulate.py"]["sha256"] = "f" * 64
            canonical = json.dumps(
                closure["inputs"], sort_keys=True, separators=(",", ":"),
                ensure_ascii=True,
            ).encode()
            closure["sha256"] = hashlib.sha256(canonical).hexdigest()
        with self.assertRaisesRegex(
            subject.provenance.ProvenanceError, "source closure differs from Git",
        ):
            subject.validate_retained_transition(
                forged, bootstrap, preflight, fixture.final, fixture.final_head,
            )

        omitted = copy.deepcopy(transition)
        del omitted["comparison"]
        with self.assertRaisesRegex(
            subject.provenance.ProvenanceError,
            "malformed retained bootstrap transition",
        ):
            subject.validate_retained_transition(
                omitted, bootstrap, preflight, fixture.final, fixture.final_head,
            )

        rebound = copy.deepcopy(transition)
        rebound_bootstrap = copy.deepcopy(bootstrap)
        rebound["source_candle"]["root"] = str(fixture.final)
        rebound["source_candle"]["head"] = fixture.final_head
        rebound_bootstrap["candle_root"] = str(fixture.final)
        rebound_bootstrap["candle_commit"] = fixture.final_head
        with self.assertRaisesRegex(
            subject.provenance.ProvenanceError, "authorities are not distinct",
        ):
            subject.validate_retained_transition(
                rebound, rebound_bootstrap, preflight,
                fixture.final, fixture.final_head,
            )

        forged_preflight = copy.deepcopy(preflight)
        forged_bootstrap = copy.deepcopy(bootstrap)
        forged_source = forged_preflight["controller_sources"][
            "candle/cakeml_artifact_provenance.py"
        ]
        forged_source["sha256"] = "e" * 64
        forged_source["commit_blob"]["sha256"] = "e" * 64
        forged_preflight["python_controller"]["source"] = forged_source
        forged_bootstrap["python_controller"] = forged_preflight[
            "python_controller"
        ]
        with self.assertRaisesRegex(
            subject.provenance.ProvenanceError,
            "controller differs from source Git",
        ):
            subject.validate_retained_transition(
                transition, forged_bootstrap, forged_preflight,
                fixture.final, fixture.final_head,
            )

    def test_schema7_linked_record_rejects_omitted_or_wrong_controller(self) -> None:
        fixture = self.make_fixture()
        build = fixture.final / "candle/build"
        build.mkdir(parents=True)
        record_path = build / subject.provenance.LINKED_RECORD_RELATIVE.name
        pins = subject.provenance.expected_pins(fixture.final)
        base = {
            "schema": subject.TRANSITION_LINKED_SCHEMA,
            "kind": subject.TRANSITION_LINKED_KIND,
            "promotion_status":
                "diagnostic-only-requires-final-head-canonical-bootstrap",
            "transition_mode":
                "byte-identical-canonical-bootstrap-rebinding-v1",
            "transition_record": {},
            "transition_controller": {"wrong": {}},
            "candle_commit": fixture.final_head,
            **pins,
            "bootstrap_record": {}, "bootstrap_preflight": {},
            "bootstrap_log": {}, "cake_patch": {},
            "cake_patch_derivation": {}, "native_link_derivation": {},
            "outputs": {}, "runtime_elf_closure": {},
            "version_output_sha256": "0" * 64,
        }
        omitted = copy.deepcopy(base)
        del omitted["transition_record"]
        record_path.write_text(json.dumps(omitted), encoding="utf-8")
        with self.assertRaisesRegex(
            subject.provenance.ProvenanceError,
            "malformed transition-linked provenance",
        ):
            subject.validate_linked_transition_record(fixture.final)

        record_path.write_text(json.dumps(base), encoding="utf-8")
        with mock.patch.object(
            subject, "validate_git_checkout", return_value=fixture.final,
        ), mock.patch.object(
            subject.provenance, "expected_pins", return_value=pins,
        ), mock.patch.object(
            subject, "transition_controller_closure",
            return_value={"expected": {}},
        ), self.assertRaisesRegex(
            subject.provenance.ProvenanceError, "controller closure mismatch",
        ):
            subject.validate_linked_transition_record(fixture.final)

    def test_schema6_dispatch_rejects_transition_downgrade(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            (root / "candle/build").mkdir(parents=True)
            record_path = root / subject.provenance.LINKED_RECORD_RELATIVE
            record_path.write_text(
                json.dumps({"schema": subject.provenance.LINKED_PROVENANCE_SCHEMA}),
                encoding="utf-8",
            )
            linked = {
                "schema": subject.provenance.LINKED_PROVENANCE_SCHEMA,
                "candle_commit": "f" * 40,
            }
            retained = {
                "candle_root": "/different/bootstrap/root",
                "candle_commit": "e" * 40,
            }
            with mock.patch.object(
                subject.provenance, "validate_linked_record", return_value=linked,
            ), mock.patch.object(
                subject.provenance, "validate_build_directory",
                return_value=root / "candle/build",
            ), mock.patch.object(
                subject.provenance, "expected_pins", return_value={},
            ), mock.patch.object(
                subject.provenance, "validate_linked_bootstrap_copy",
                return_value=retained,
            ), self.assertRaisesRegex(
                subject.provenance.ProvenanceError,
                "not an exact-root bootstrap link",
            ):
                subject.validate_linked_record(root)

    def test_changed_bootstrap_inputs_reject(self) -> None:
        for relative in subject.TRANSITION_CANDLE_INPUTS:
            with self.subTest(relative=relative):
                fixture = TransitionFixture()
                try:
                    path = fixture.final / relative
                    path.write_bytes(path.read_bytes() + b"changed\n")
                    if relative.endswith(".sh"):
                        os.chmod(path, 0o755)
                    fixture.final_head = commit(
                        fixture.final, f"change {relative}",
                    )
                    with fixture.authenticated_receipt(), self.assertRaisesRegex(
                        subject.provenance.ProvenanceError,
                        "input closure is not byte-identical",
                    ):
                        subject.transition_derivation(*fixture.arguments())
                finally:
                    fixture.close()

    def test_source_and_final_root_or_head_mismatch_reject(self) -> None:
        fixture = self.make_fixture()
        with fixture.authenticated_receipt():
            record = subject.record_transition(
                *fixture.arguments(), fixture.transition,
            )
            wrong_head = "0" * 40
            with self.assertRaisesRegex(
                subject.provenance.ProvenanceError, "revision mismatch",
            ):
                subject.validate_transition_record(
                    fixture.source, wrong_head, fixture.final, fixture.final_head,
                    fixture.cakeml, fixture.receipt, fixture.transition,
                )
            with self.assertRaisesRegex(
                subject.provenance.ProvenanceError, "revision mismatch",
            ):
                subject.validate_transition_record(
                    fixture.source, fixture.source_head, fixture.final, wrong_head,
                    fixture.cakeml, fixture.receipt, fixture.transition,
                )
            with self.assertRaisesRegex(
                subject.provenance.ProvenanceError,
                "source Candle authority mismatch",
            ):
                rebound = fixture.root / "rebound"
                subprocess.run(
                    ["/usr/bin/git", "clone", "-q", str(fixture.source),
                     str(rebound)],
                    check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    env=GIT_ENV,
                )
                subject.validate_transition_record(
                    rebound, fixture.source_head,
                    fixture.final, fixture.final_head,
                    fixture.cakeml, fixture.receipt, fixture.transition,
                )
        self.assertEqual(record["source_candle"]["root"], str(fixture.source))

    def test_final_root_rebinding_rejects_against_explicit_authority(self) -> None:
        fixture = self.make_fixture()
        with fixture.authenticated_receipt():
            subject.record_transition(*fixture.arguments(), fixture.transition)
            rebound = fixture.root / "rebound-final"
            subprocess.run(
                ["/usr/bin/git", "clone", "-q", str(fixture.final), str(rebound)],
                check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                env=GIT_ENV,
            )
            with self.assertRaisesRegex(
                subject.provenance.ProvenanceError, "live reconstruction",
            ):
                subject.validate_transition_record(
                    fixture.source, fixture.source_head,
                    rebound, fixture.final_head,
                    fixture.cakeml, fixture.receipt, fixture.transition,
                )

    def test_dirty_git_rejects(self) -> None:
        for checkout_name in ("source", "final"):
            with self.subTest(checkout=checkout_name):
                fixture = TransitionFixture()
                try:
                    checkout = getattr(fixture, checkout_name)
                    (checkout / "untracked-injection").write_text(
                        "dirty\n", encoding="utf-8",
                    )
                    with fixture.authenticated_receipt(), self.assertRaisesRegex(
                        subject.provenance.ProvenanceError,
                        "worktree is not clean",
                    ):
                        subject.transition_derivation(*fixture.arguments())
                finally:
                    fixture.close()

    def test_grafts_replacements_and_hidden_index_flags_reject(self) -> None:
        cases = ("graft", "replace", "assume", "skip")
        for case in cases:
            with self.subTest(case=case):
                fixture = TransitionFixture()
                try:
                    if case == "graft":
                        info = fixture.final / ".git/info"
                        info.mkdir(exist_ok=True)
                        (info / "grafts").write_text(
                            f"{fixture.final_head} {fixture.source_head}\n",
                            encoding="utf-8",
                        )
                        message = "grafts file"
                    elif case == "replace":
                        git(
                            fixture.final, "update-ref",
                            f"refs/replace/{fixture.final_head}",
                            fixture.source_head,
                        )
                        message = "replacement objects"
                    elif case == "assume":
                        git(
                            fixture.final, "update-index", "--assume-unchanged",
                            "candle/insulate.py",
                        )
                        message = "assume-unchanged or skip-worktree"
                    else:
                        git(
                            fixture.final, "update-index", "--skip-worktree",
                            "candle/insulate.py",
                        )
                        message = "assume-unchanged or skip-worktree"
                    with fixture.authenticated_receipt(), self.assertRaisesRegex(
                        subject.provenance.ProvenanceError, message,
                    ):
                        subject.transition_derivation(*fixture.arguments())
                finally:
                    fixture.close()

    def test_malformed_and_fully_rehashed_transition_records_reject(self) -> None:
        fixture = self.make_fixture()
        with fixture.authenticated_receipt():
            original = subject.record_transition(
                *fixture.arguments(), fixture.transition,
            )
            os.chmod(fixture.transition, 0o644)
            malformed = copy.deepcopy(original)
            malformed["unexpected"] = "self-asserted"
            fixture.transition.write_text(
                json.dumps(malformed, sort_keys=True) + "\n", encoding="utf-8",
            )
            with self.assertRaisesRegex(
                subject.provenance.ProvenanceError, "live reconstruction",
            ):
                subject.validate_transition_record(
                    *fixture.arguments(), fixture.transition,
                )

            forged = copy.deepcopy(original)
            target = forged["final_candle"]["closure"]
            target["inputs"]["candle/insulate.py"]["sha256"] = "f" * 64
            canonical = json.dumps(
                target["inputs"], sort_keys=True, separators=(",", ":"),
                ensure_ascii=True,
            ).encode()
            target["sha256"] = hashlib.sha256(canonical).hexdigest()
            fixture.transition.write_text(
                json.dumps(forged, sort_keys=True) + "\n", encoding="utf-8",
            )
            with self.assertRaisesRegex(
                subject.provenance.ProvenanceError, "live reconstruction",
            ):
                subject.validate_transition_record(
                    *fixture.arguments(), fixture.transition,
                )

    def test_transition_record_root_rebinding_rejects_even_if_rehashed(self) -> None:
        fixture = self.make_fixture()
        with fixture.authenticated_receipt():
            record = subject.record_transition(
                *fixture.arguments(), fixture.transition,
            )
            rebound = fixture.root / "rebound"
            subprocess.run(
                ["/usr/bin/git", "clone", "-q", str(fixture.source), str(rebound)],
                check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                env=GIT_ENV,
            )
            forged = copy.deepcopy(record)
            forged["source_candle"]["root"] = str(rebound)
            os.chmod(fixture.transition, 0o644)
            fixture.transition.write_text(
                json.dumps(forged, sort_keys=True) + "\n", encoding="utf-8",
            )
            with self.assertRaisesRegex(
                subject.provenance.ProvenanceError, "live reconstruction",
            ):
                subject.validate_transition_record(
                    *fixture.arguments(), fixture.transition,
                )

    def test_transition_record_inside_authenticated_git_metadata_rejects(self) -> None:
        fixture = self.make_fixture()
        hidden_record = fixture.final / ".git/bootstrap-transition.json"
        with fixture.authenticated_receipt():
            record = subject.transition_derivation(*fixture.arguments())
            hidden_record.write_text(
                json.dumps(record, sort_keys=True) + "\n", encoding="utf-8",
            )
            with self.assertRaisesRegex(
                subject.provenance.ProvenanceError,
                "outside authenticated worktrees",
            ):
                subject.validate_transition_record(
                    *fixture.arguments(), hidden_record,
                )


if __name__ == "__main__":
    unittest.main()
