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
            subject.provenance, "validate_bootstrap_record",
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
