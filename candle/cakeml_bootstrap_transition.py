#!/usr/bin/env python3
"""Authenticate a canonical CakeML bootstrap receipt across Candle revisions.

This controller does not reinterpret or weaken the canonical bootstrap receipt.
It first validates that receipt with ``validate_bootstrap_record`` at the exact
source Candle checkout recorded by the bootstrap.  A transition is admissible
only when a separately supplied destination checkout is clean, descends from
the source revision, and has the same complete Candle-side bootstrap/link input
closure byte for byte.

The transition record is diagnostic proof, not an authority or a signature.
Every consumer reconstructs it from the explicit source/destination roots and
heads, the original receipt, and the live clean Git worktrees.  Consequently a
rewritten or fully rehashed JSON record cannot redirect the authority roots.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
from pathlib import Path
from typing import Any

import cakeml_artifact_provenance as provenance


TRANSITION_SCHEMA = 1
TRANSITION_KIND = "candle-cakeml-bootstrap-byte-identical-transition"
TRANSITION_POLICY = "reconstruct_exact_candle_bootstrap_input_closure_v1"

# build-local-cakeml.sh is deliberately not in this equality closure: it is the
# destination-side consumer being extended with transition support, not an
# input to the already completed canonical bootstrap.  Its exact bytes (and
# those of this controller) are nevertheless authenticated by the clean final
# Candle commit recorded in the transition and the linked provenance record.
TRANSITION_CANDLE_INPUTS = {
    "build-local-cakeml-bootstrap.sh": "100755",
    "candle/cakeml_artifact_provenance.py": "100644",
    "candle/flyspeck_manifest.json": "100644",
    "candle/cake.S.patch": "100644",
    "candle/insulate.py": "100644",
}

TRANSITION_TRUST_BOUNDARY = {
    "policy": "diagnostic_reconstructed_transition_not_signature_v1",
    "bound_by_content": [
        "the original schema-5 bootstrap receipt, preflight, transcript, "
        "outputs, CakeML/HOL4 closure, and source Candle checkout through the "
        "unchanged canonical validate_bootstrap_record",
        "clean exact source and final Candle roots/commits, with replacement "
        "objects, grafts, and hidden index flags rejected",
        "byte-identical committed and live manifest, canonical bootstrap "
        "launcher, provenance controller, assembly patch, and insulate input",
        "the exact CakeML root and revision already bound by the bootstrap",
    ],
    "trusted_not_independently_authenticated": [
        "kernel, filesystem, process, and Git executable semantics",
        "absence of hostile same-UID mutation between guarded observations",
        "the semantic adequacy of the enumerated Candle-side closure; the "
        "CakeML/HOL4 and host portions retain the bootstrap receipt's stated "
        "trust boundary",
        "this transition JSON is proof data rather than a signature; callers "
        "must supply the expected roots and heads and reconstruct it live",
    ],
}


def require_commit(value: str, label: str) -> str:
    provenance.require(
        isinstance(value, str) and re.fullmatch(r"[0-9a-f]{40}", value) is not None,
        f"malformed {label}",
    )
    return value


def ordinary_directory(path: Path, label: str) -> Path:
    try:
        metadata = path.lstat()
    except OSError as error:
        raise provenance.ProvenanceError(f"missing {label}: {path}") from error
    provenance.require(
        stat.S_ISDIR(metadata.st_mode) and not path.is_symlink(),
        f"{label} is not an ordinary directory: {path}",
    )
    return path


def git_bytes(root: Path, *arguments: str) -> bytes:
    try:
        completed = subprocess.run(
            provenance.git_command(root, *arguments),
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            env=provenance.git_environment(),
            timeout=120,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise provenance.ProvenanceError(
            f"Git command failed for transition checkout: {root}",
        ) from error
    provenance.require(
        completed.returncode == 0 and completed.stderr == b"",
        f"Git command failed for transition checkout {root}: {arguments!r}",
    )
    return completed.stdout


def git_common_directory(root: Path, label: str) -> Path:
    dot_git = root / ".git"
    try:
        metadata = dot_git.lstat()
    except OSError as error:
        raise provenance.ProvenanceError(
            f"{label} has no readable .git metadata",
        ) from error
    if stat.S_ISDIR(metadata.st_mode) and not dot_git.is_symlink():
        git_directory = ordinary_directory(dot_git, f"{label} Git directory")
    else:
        provenance.require(
            stat.S_ISREG(metadata.st_mode) and not dot_git.is_symlink(),
            f"{label} has unsupported .git metadata",
        )
        value, _ = provenance.captured_ordinary_file(dot_git)
        try:
            line = value.decode("utf-8", errors="strict")
        except UnicodeDecodeError as error:
            raise provenance.ProvenanceError(
                f"{label} has malformed .git metadata",
            ) from error
        provenance.require(
            line.startswith("gitdir: ") and line.endswith("\n") and
            line.count("\n") == 1,
            f"{label} has malformed .git metadata",
        )
        git_path = Path(line[len("gitdir: "):-1])
        if not git_path.is_absolute():
            git_path = root / git_path
        git_directory = ordinary_directory(
            git_path.resolve(strict=True), f"{label} Git directory",
        )
    common_file = git_directory / "commondir"
    if not os.path.lexists(common_file):
        return git_directory
    common_bytes, _ = provenance.captured_ordinary_file(common_file)
    try:
        common_value = common_bytes.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise provenance.ProvenanceError(
            f"{label} has malformed Git common-directory metadata",
        ) from error
    provenance.require(
        common_value.endswith("\n") and common_value.count("\n") == 1,
        f"{label} has malformed Git common-directory metadata",
    )
    common_path = Path(common_value[:-1])
    if not common_path.is_absolute():
        common_path = git_directory / common_path
    return ordinary_directory(
        common_path.resolve(strict=True), f"{label} Git common directory",
    )


def validate_git_checkout(root: Path, expected_head: str, label: str) -> Path:
    root = ordinary_directory(root.resolve(strict=True), label)
    expected_head = require_commit(expected_head, f"{label} head")
    common = git_common_directory(root, label)
    provenance.require(
        not os.path.lexists(common / "info/grafts"),
        f"{label} has a Git grafts file",
    )
    top = git_bytes(root, "rev-parse", "--show-toplevel").decode().strip()
    provenance.require(Path(top) == root, f"{label} is not the exact Git top level")
    head = git_bytes(root, "rev-parse", "--verify", "HEAD^{commit}").decode().strip()
    provenance.require(head == expected_head, f"{label} revision mismatch")
    provenance.require(
        git_bytes(root, "status", "--porcelain=v1", "-z", "--untracked-files=all")
        == b"",
        f"{label} worktree is not clean",
    )
    provenance.require(
        git_bytes(root, "for-each-ref", "--format=%(refname)", "refs/replace")
        == b"",
        f"{label} has Git replacement objects",
    )
    for record in git_bytes(root, "ls-files", "-v", "-z").split(b"\0"):
        if record:
            provenance.require(
                record.startswith(b"H "),
                f"{label} has assume-unchanged or skip-worktree index flags",
            )
    return root


def committed_input_record(
    root: Path,
    head: str,
    relative: str,
    expected_mode: str,
    label: str,
) -> dict[str, Any]:
    stage = git_bytes(root, "ls-files", "--stage", "--", relative)
    try:
        fields = stage.decode("utf-8", errors="strict").strip().split()
    except UnicodeDecodeError as error:
        raise provenance.ProvenanceError(
            f"malformed {label} index entry: {relative}",
        ) from error
    provenance.require(
        len(fields) == 4 and fields[0] == expected_mode and fields[2] == "0" and
        fields[3] == relative,
        f"{label} input is not one exact stage-0 {expected_mode} file: {relative}",
    )
    live, identity = provenance.captured_ordinary_file(root / relative)
    committed = git_bytes(root, "cat-file", "blob", f"{head}:{relative}")
    provenance.require(
        live == committed,
        f"{label} live input differs from its commit: {relative}",
    )
    return {"path": relative, "mode": expected_mode, **identity}


def candle_input_closure(root: Path, head: str, label: str) -> dict[str, Any]:
    inputs = {
        relative: committed_input_record(root, head, relative, mode, label)
        for relative, mode in TRANSITION_CANDLE_INPUTS.items()
    }
    canonical = json.dumps(
        inputs, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
    ).encode()
    return {
        "policy": "exact_committed_live_files_v1",
        "inputs": inputs,
        "sha256": hashlib.sha256(canonical).hexdigest(),
    }


def transition_derivation(
    source_candle_root: Path,
    source_candle_head: str,
    final_candle_root: Path,
    final_candle_head: str,
    cakeml_root: Path,
    bootstrap_record_path: Path,
) -> dict[str, Any]:
    source_candle_head = require_commit(source_candle_head, "source Candle head")
    final_candle_head = require_commit(final_candle_head, "final Candle head")
    source_candle_root = validate_git_checkout(
        source_candle_root, source_candle_head, "source Candle checkout",
    )
    final_candle_root = validate_git_checkout(
        final_candle_root, final_candle_head, "final Candle checkout",
    )
    provenance.require(
        source_candle_root != final_candle_root,
        "bootstrap transition requires distinct source and final Candle roots",
    )
    provenance.require(
        source_candle_head != final_candle_head,
        "bootstrap transition requires distinct source and final Candle heads",
    )
    ancestry = git_bytes(
        final_candle_root, "merge-base", "--is-ancestor",
        source_candle_head, final_candle_head,
    )
    provenance.require(
        ancestry == b"",
        "final Candle head does not descend from the bootstrap source head",
    )

    cakeml_root = ordinary_directory(
        cakeml_root.resolve(strict=True), "CakeML checkout",
    )
    bootstrap_record_path = bootstrap_record_path.resolve(strict=True)
    provenance.require(
        not any(bootstrap_record_path.is_relative_to(root) for root in (
            source_candle_root, final_candle_root, cakeml_root,
        )),
        "bootstrap receipt must be outside transition worktrees",
    )
    bootstrap = provenance.validate_bootstrap_record(
        source_candle_root, cakeml_root, bootstrap_record_path,
    )
    provenance.require(
        bootstrap.get("candle_root") == str(source_candle_root) and
        bootstrap.get("candle_commit") == source_candle_head,
        "bootstrap receipt source Candle authority mismatch",
    )
    cakeml_head = require_commit(
        bootstrap.get("cakeml_commit"), "bootstrap CakeML head",
    )
    validate_git_checkout(cakeml_root, cakeml_head, "CakeML checkout")

    source_closure = candle_input_closure(
        source_candle_root, source_candle_head, "source Candle checkout",
    )
    final_closure = candle_input_closure(
        final_candle_root, final_candle_head, "final Candle checkout",
    )
    provenance.require(
        source_closure == final_closure,
        "bootstrap-relevant Candle input closure is not byte-identical",
    )
    source_pins = provenance.expected_pins(source_candle_root)
    final_pins = provenance.expected_pins(final_candle_root)
    provenance.require(
        source_pins == final_pins and
        all(bootstrap.get(field) == expected for field, expected in source_pins.items()),
        "source/final/bootstrap manifest pins differ",
    )
    _, bootstrap_identity = provenance.captured_ordinary_file(
        bootstrap_record_path,
    )
    return {
        "schema": TRANSITION_SCHEMA,
        "kind": TRANSITION_KIND,
        "policy": TRANSITION_POLICY,
        "source_candle": {
            "root": str(source_candle_root),
            "head": source_candle_head,
            "closure": source_closure,
        },
        "final_candle": {
            "root": str(final_candle_root),
            "head": final_candle_head,
            "closure": final_closure,
        },
        "cakeml": {"root": str(cakeml_root), "head": cakeml_head},
        "bootstrap_record": {
            "path": str(bootstrap_record_path), **bootstrap_identity,
        },
        "comparison": "byte_for_byte_equal",
        "trusted_boundary": TRANSITION_TRUST_BOUNDARY,
    }


def record_transition(
    source_candle_root: Path,
    source_candle_head: str,
    final_candle_root: Path,
    final_candle_head: str,
    cakeml_root: Path,
    bootstrap_record_path: Path,
    output_path: Path,
) -> dict[str, Any]:
    record = transition_derivation(
        source_candle_root, source_candle_head,
        final_candle_root, final_candle_head,
        cakeml_root, bootstrap_record_path,
    )
    output_path = provenance.resolve_new_output(
        output_path, "bootstrap transition record",
    )
    authenticated_roots = tuple(Path(record[key]["root"]) for key in (
        "source_candle", "final_candle", "cakeml",
    ))
    provenance.require(
        not any(output_path.is_relative_to(root) for root in authenticated_roots),
        "bootstrap transition record must be outside authenticated worktrees",
    )

    def revalidate() -> None:
        provenance.require(
            transition_derivation(
                source_candle_root, source_candle_head,
                final_candle_root, final_candle_head,
                cakeml_root, bootstrap_record_path,
            ) == record,
            "bootstrap transition inputs changed during publication",
        )

    provenance.write_new_json(
        output_path, record, before_publish=revalidate, after_publish=revalidate,
    )
    return record


def validate_transition_record(
    source_candle_root: Path,
    source_candle_head: str,
    final_candle_root: Path,
    final_candle_head: str,
    cakeml_root: Path,
    bootstrap_record_path: Path,
    transition_record_path: Path,
) -> tuple[dict[str, Any], dict[str, Any]]:
    expected = transition_derivation(
        source_candle_root, source_candle_head,
        final_candle_root, final_candle_head,
        cakeml_root, bootstrap_record_path,
    )
    transition_record_path = transition_record_path.resolve(strict=True)
    authenticated_roots = tuple(Path(expected[key]["root"]) for key in (
        "source_candle", "final_candle", "cakeml",
    ))
    provenance.require(
        not any(transition_record_path.is_relative_to(root)
                for root in authenticated_roots),
        "bootstrap transition record must be outside authenticated worktrees",
    )
    transition, _ = provenance.load_captured_object(transition_record_path)
    provenance.require(
        transition == expected,
        "bootstrap transition record differs from live reconstruction",
    )
    # Do not reuse a bootstrap object parsed from the transition.  Re-run the
    # canonical validator and return that exact result to the linking phase.
    bootstrap = provenance.validate_bootstrap_record(
        Path(expected["source_candle"]["root"]),
        Path(expected["cakeml"]["root"]),
        Path(expected["bootstrap_record"]["path"]),
    )
    return transition, bootstrap


def record_linked_transition(
    source_candle_root: Path,
    source_candle_head: str,
    final_candle_root: Path,
    final_candle_head: str,
    cakeml_root: Path,
    bootstrap_record_path: Path,
    transition_record_path: Path,
    output_path: Path,
) -> dict[str, Any]:
    """Create the ordinary schema-6 linked record after a valid transition."""
    transition, bootstrap = validate_transition_record(
        source_candle_root, source_candle_head,
        final_candle_root, final_candle_head,
        cakeml_root, bootstrap_record_path, transition_record_path,
    )
    final_candle_root = Path(transition["final_candle"]["root"])
    cakeml_root = Path(transition["cakeml"]["root"])
    build_dir = provenance.validate_build_directory(final_candle_root)
    inputs = bootstrap["inputs"]
    for name in ("config_enc_str.txt", "candle_boot.ml", "basis_ffi.c", "Makefile"):
        provenance.validate_file_record(
            build_dir / name, inputs[name], f"copied {name}",
        )
    cake_commit, hol_commit, version_output = provenance.version_details(
        build_dir / "cake",
    )
    provenance.require(
        cake_commit == bootstrap["cakeml_commit"],
        "linked compiler CakeML revision mismatch",
    )
    provenance.require(
        hol_commit == bootstrap["hol4_commit"],
        "linked compiler HOL4 revision mismatch",
    )
    provenance.materialize_linked_bootstrap(
        build_dir, bootstrap_record_path.resolve(), bootstrap,
    )
    patch_derivation = provenance.cake_patch_derivation(
        build_dir, inputs["cake.S"], final_candle_root / "candle/cake.S.patch",
    )
    link_derivation = provenance.native_link_derivation(build_dir)
    record = {
        "schema": provenance.LINKED_PROVENANCE_SCHEMA,
        "kind": "candle-linked-pinned-cakeml",
        "candle_commit": final_candle_head,
        "cakeml_commit": cake_commit,
        "hol4_commit": hol_commit,
        "manifest_sha256": bootstrap["manifest_sha256"],
        "bootstrap_record": provenance.file_record(
            build_dir / provenance.LINKED_BOOTSTRAP_RECORD,
        ),
        "bootstrap_preflight": provenance.file_record(
            build_dir / provenance.LINKED_BOOTSTRAP_PREFLIGHT,
        ),
        "bootstrap_log": provenance.file_record(
            build_dir / provenance.LINKED_BOOTSTRAP_LOG,
        ),
        "cake_patch": provenance.file_record(
            final_candle_root / "candle/cake.S.patch",
        ),
        "cake_patch_derivation": patch_derivation,
        "native_link_derivation": link_derivation,
        "outputs": {
            name: provenance.file_record(build_dir / name)
            for name in provenance.LINKED_OUTPUTS
        },
        "runtime_elf_closure": provenance.elf_dynamic_closure(build_dir / "cake"),
        "version_output_sha256": hashlib.sha256(version_output.encode()).hexdigest(),
    }
    provenance.validate_candle_elf_policy(record["runtime_elf_closure"])
    provenance.require(
        output_path.parent.resolve() == build_dir.resolve() and
        output_path.name == provenance.LINKED_RECORD_RELATIVE.name and
        not output_path.is_symlink(),
        "linked provenance destination must be the ordinary Candle build record",
    )
    output_path.write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8",
    )
    return record


def add_transition_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--source-candle-root", type=Path, required=True)
    parser.add_argument("--source-candle-head", required=True)
    parser.add_argument("--final-candle-root", type=Path, required=True)
    parser.add_argument("--final-candle-head", required=True)
    parser.add_argument("--cakeml-root", type=Path, required=True)
    parser.add_argument("--bootstrap-record", type=Path, required=True)


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    record_parser = subparsers.add_parser("record-transition")
    add_transition_arguments(record_parser)
    record_parser.add_argument("--write", type=Path, required=True)
    check_parser = subparsers.add_parser("check-transition")
    add_transition_arguments(check_parser)
    check_parser.add_argument("--record", type=Path, required=True)
    linked_parser = subparsers.add_parser("record-linked-transition")
    add_transition_arguments(linked_parser)
    linked_parser.add_argument("--transition-record", type=Path, required=True)
    linked_parser.add_argument("--write", type=Path, required=True)
    arguments = parser.parse_args()
    common = (
        arguments.source_candle_root, arguments.source_candle_head,
        arguments.final_candle_root, arguments.final_candle_head,
        arguments.cakeml_root, arguments.bootstrap_record,
    )
    if arguments.command == "record-transition":
        record_transition(*common, arguments.write)
        print(f"bootstrap transition provenance recorded: {arguments.write}")
    elif arguments.command == "check-transition":
        validate_transition_record(*common, arguments.record)
        print("bootstrap transition provenance PASS")
    else:
        record_linked_transition(
            *common, arguments.transition_record, arguments.write,
        )
        print(f"linked CakeML provenance recorded: {arguments.write}")


if __name__ == "__main__":
    main()
