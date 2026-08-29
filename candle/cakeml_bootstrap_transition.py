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
import sys
import types
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent


def _load_exact_local_source(name: str, path: Path):
    """Execute one stable sibling source image without import/bytecode lookup."""
    try:
        descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    except OSError as error:
        raise RuntimeError(f"could not open exact local source: {path}") from error
    try:
        before = os.fstat(descriptor)
        chunks = []
        while block := os.read(descriptor, 1024 * 1024):
            chunks.append(block)
        after = os.fstat(descriptor)
        named = path.stat(follow_symlinks=False)
    finally:
        os.close(descriptor)
    source = b"".join(chunks)
    if (not stat.S_ISREG(before.st_mode) or
            (before.st_dev, before.st_ino, before.st_size,
             before.st_mtime_ns, before.st_ctime_ns) !=
            (after.st_dev, after.st_ino, after.st_size,
             after.st_mtime_ns, after.st_ctime_ns) or
            (named.st_dev, named.st_ino) != (after.st_dev, after.st_ino) or
            len(source) != before.st_size):
        raise RuntimeError(f"local source changed while loading: {path}")
    source_sha256 = hashlib.sha256(source).hexdigest()
    existing = sys.modules.get(name)
    if existing is not None:
        if (getattr(existing, "__candle_source_sha256__", None) !=
                source_sha256 or
                Path(getattr(existing, "__file__", "")).resolve() != path):
            raise RuntimeError(f"untrusted preloaded local module: {name}")
        return existing
    module = types.ModuleType(name)
    module.__file__ = str(path)
    module.__package__ = ""
    module.__candle_source_sha256__ = source_sha256
    module.__candle_source_bytes__ = source
    sys.modules[name] = module
    try:
        exec(
            compile(source, str(path), "exec", dont_inherit=True),
            module.__dict__,
        )
    except BaseException:
        sys.modules.pop(name, None)
        raise
    return module


provenance = _load_exact_local_source(
    "_candle_bootstrap_transition_provenance",
    HERE / "cakeml_artifact_provenance.py",
)


TRANSITION_SCHEMA = 1
TRANSITION_KIND = "candle-cakeml-bootstrap-byte-identical-transition"
TRANSITION_POLICY = "reconstruct_exact_candle_bootstrap_input_closure_v1"
TRANSITION_LINKED_SCHEMA = 7
TRANSITION_LINKED_KIND = "candle-linked-pinned-cakeml-transition"
LINKED_TRANSITION_RECORD = "bootstrap-transition.json"

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
TRANSITION_LINK_CONTROLLER_INPUTS = {
    "build-local-cakeml.sh": "100755",
    "candle/cakeml_bootstrap_transition.py": "100644",
}
TRANSITION_LINKED_OUTPUTS = (
    *provenance.LINKED_OUTPUTS,
    LINKED_TRANSITION_RECORD,
)

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


def committed_tree_input_closure(
    repository_root: Path,
    head: str,
    label: str,
) -> dict[str, Any]:
    """Reconstruct the closure at an ancestor without its old worktree."""
    inputs: dict[str, dict[str, Any]] = {}
    for relative, expected_mode in TRANSITION_CANDLE_INPUTS.items():
        entry = git_bytes(
            repository_root, "ls-tree", "-z", head, "--", relative,
        )
        provenance.require(
            entry.endswith(b"\0") and entry.count(b"\0") == 1,
            f"{label} has no exact committed input: {relative}",
        )
        metadata, path_bytes = entry[:-1].split(b"\t", 1)
        fields = metadata.decode("ascii", errors="strict").split()
        path = path_bytes.decode("utf-8", errors="strict")
        provenance.require(
            len(fields) == 3 and fields[0] == expected_mode and
            fields[1] == "blob" and
            re.fullmatch(r"[0-9a-f]{40}", fields[2]) is not None and
            path == relative,
            f"{label} committed input mode/path mismatch: {relative}",
        )
        value = git_bytes(repository_root, "cat-file", "blob", fields[2])
        inputs[relative] = {
            "path": relative,
            "mode": expected_mode,
            **provenance.bytes_record(value),
        }
    canonical = json.dumps(
        inputs, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
    ).encode()
    return {
        "policy": "exact_committed_live_files_v1",
        "inputs": inputs,
        "sha256": hashlib.sha256(canonical).hexdigest(),
    }


def validate_canonical_bootstrap_receipt(
    source_candle_root: Path,
    cakeml_root: Path,
    bootstrap_record_path: Path,
) -> dict[str, Any]:
    """Run the exact source controller because its process identity is causal."""
    controller = source_candle_root / "candle/cakeml_artifact_provenance.py"
    before_identity = provenance.ordinary_file_identity(bootstrap_record_path)
    receipt_bytes, receipt_record = provenance.captured_ordinary_file(
        bootstrap_record_path,
    )
    completed = subprocess.run(
        [
            "/usr/bin/python3", "-I", "-S", str(controller),
            "check-bootstrap",
            "--candle-root", str(source_candle_root),
            "--cakeml-root", str(cakeml_root),
            "--record", str(bootstrap_record_path),
        ],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        env={"LC_ALL": "C", "PATH": "/usr/bin:/bin"},
        timeout=3600,
    )
    provenance.require(
        completed.returncode == 0 and
        completed.stdout == b"bootstrap provenance PASS\n" and
        completed.stderr == b"",
        "canonical source bootstrap validator did not report exact PASS",
    )
    provenance.require(
        provenance.ordinary_file_identity(bootstrap_record_path) == before_identity,
        "bootstrap receipt changed across canonical validation",
    )
    try:
        bootstrap = json.loads(receipt_bytes.decode("utf-8", errors="strict"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise provenance.ProvenanceError(
            "malformed canonically validated bootstrap receipt",
        ) from error
    provenance.require(
        isinstance(bootstrap, dict) and
        provenance.bytes_record(receipt_bytes) == receipt_record,
        "malformed canonically validated bootstrap receipt",
    )
    return bootstrap


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
    bootstrap = validate_canonical_bootstrap_receipt(
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
    bootstrap = validate_canonical_bootstrap_receipt(
        Path(expected["source_candle"]["root"]),
        Path(expected["cakeml"]["root"]),
        Path(expected["bootstrap_record"]["path"]),
    )
    return transition, bootstrap


def materialize_transition_record(
    build_dir: Path,
    source_path: Path,
    transition: dict[str, Any],
) -> dict[str, Any]:
    source_path = source_path.resolve(strict=True)
    source_bytes, source_identity = provenance.captured_ordinary_file(source_path)
    destination = build_dir / LINKED_TRANSITION_RECORD
    provenance.require(
        not destination.is_symlink(),
        "refusing symlink destination for linked bootstrap transition",
    )
    destination.write_bytes(source_bytes)
    provenance.validate_file_record(
        destination, source_identity, "materialized bootstrap transition",
    )
    retained, _ = provenance.load_captured_object(destination)
    provenance.require(
        retained == transition,
        "materialized bootstrap transition differs from validated record",
    )
    return source_identity


def transition_controller_closure(
    final_candle_root: Path,
    final_candle_head: str,
) -> dict[str, Any]:
    return {
        relative: committed_input_record(
            final_candle_root, final_candle_head, relative, mode,
            "final transition-link controller",
        )
        for relative, mode in TRANSITION_LINK_CONTROLLER_INPUTS.items()
    }


def validate_retained_transition(
    transition: dict[str, Any],
    bootstrap: dict[str, Any],
    preflight: dict[str, Any],
    final_candle_root: Path,
    final_candle_head: str,
) -> None:
    provenance.require(
        isinstance(transition, dict) and set(transition) == {
            "schema", "kind", "policy", "source_candle", "final_candle",
            "cakeml", "bootstrap_record", "comparison", "trusted_boundary",
        },
        "malformed retained bootstrap transition",
    )
    provenance.require(
        transition.get("schema") == TRANSITION_SCHEMA and
        transition.get("kind") == TRANSITION_KIND and
        transition.get("policy") == TRANSITION_POLICY and
        transition.get("comparison") == "byte_for_byte_equal" and
        transition.get("trusted_boundary") == TRANSITION_TRUST_BOUNDARY,
        "retained bootstrap transition policy mismatch",
    )
    source = transition.get("source_candle")
    final = transition.get("final_candle")
    cakeml = transition.get("cakeml")
    receipt = transition.get("bootstrap_record")
    provenance.require(
        isinstance(source, dict) and set(source) == {"root", "head", "closure"} and
        isinstance(final, dict) and set(final) == {"root", "head", "closure"} and
        isinstance(cakeml, dict) and set(cakeml) == {"root", "head"} and
        isinstance(receipt, dict) and set(receipt) == {
            "path", "bytes", "sha256",
        },
        "malformed retained bootstrap transition authority",
    )
    provenance.require(
        source["root"] == bootstrap.get("candle_root") and
        source["head"] == bootstrap.get("candle_commit") and
        cakeml["root"] == bootstrap.get("cakeml_root") and
        cakeml["head"] == bootstrap.get("cakeml_commit") and
        final["root"] == str(final_candle_root) and
        final["head"] == final_candle_head,
        "retained bootstrap transition root/head mismatch",
    )
    provenance.require(
        source["root"] != str(final_candle_root) and
        source["head"] != final_candle_head,
        "retained bootstrap transition authorities are not distinct",
    )
    source_head = require_commit(
        source["head"], "retained bootstrap source Candle head",
    )
    try:
        ancestry = subprocess.run(
            provenance.git_command(
                final_candle_root, "merge-base", "--is-ancestor",
                source_head, final_candle_head,
            ),
            check=False, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=provenance.git_environment(), timeout=120,
        )
    except (OSError, subprocess.SubprocessError) as error:
        raise provenance.ProvenanceError(
            "could not reconstruct retained transition ancestry",
        ) from error
    provenance.require(
        ancestry.returncode == 0 and ancestry.stdout == b"" and
        ancestry.stderr == b"",
        "retained bootstrap source is not an ancestor of final Candle head",
    )
    provenance.require(
        {field: receipt[field] for field in ("bytes", "sha256")} ==
        bootstrap.get("source_bootstrap_record"),
        "retained transition bootstrap receipt identity mismatch",
    )
    provenance.require(
        isinstance(receipt["path"], str) and Path(receipt["path"]).is_absolute(),
        "malformed retained transition bootstrap receipt path",
    )
    for name, closure in (("source", source["closure"]),
                          ("final", final["closure"])):
        provenance.require(
            isinstance(closure, dict) and set(closure) == {
                "policy", "inputs", "sha256",
            } and closure.get("policy") == "exact_committed_live_files_v1" and
            isinstance(closure.get("inputs"), dict) and
            set(closure["inputs"]) == set(TRANSITION_CANDLE_INPUTS),
            f"malformed retained {name} transition closure",
        )
        for relative, mode in TRANSITION_CANDLE_INPUTS.items():
            item = closure["inputs"][relative]
            provenance.require(
                isinstance(item, dict) and set(item) == {
                    "path", "mode", "bytes", "sha256",
                } and item.get("path") == relative and
                item.get("mode") == mode and
                isinstance(item.get("bytes"), int) and item["bytes"] >= 0 and
                isinstance(item.get("sha256"), str) and
                re.fullmatch(r"[0-9a-f]{64}", item["sha256"]) is not None,
                f"malformed retained {name} transition input: {relative}",
            )
        canonical = json.dumps(
            closure["inputs"], sort_keys=True, separators=(",", ":"),
            ensure_ascii=True,
        ).encode()
        provenance.require(
            hashlib.sha256(canonical).hexdigest() == closure["sha256"],
            f"retained {name} transition closure digest mismatch",
        )
    provenance.require(
        source["closure"] == final["closure"],
        "retained bootstrap transition closures differ",
    )
    observed_source = committed_tree_input_closure(
        final_candle_root, source_head, "retained source Candle commit",
    )
    provenance.require(
        observed_source == source["closure"],
        "retained bootstrap transition source closure differs from Git",
    )
    controller_sources = preflight.get("controller_sources")
    provenance.require(
        isinstance(controller_sources, dict),
        "retained bootstrap preflight lacks controller sources",
    )
    for relative in (
        "build-local-cakeml-bootstrap.sh",
        "candle/cakeml_artifact_provenance.py",
    ):
        controller = controller_sources.get(relative)
        closure_input = source["closure"]["inputs"][relative]
        provenance.require(
            isinstance(controller, dict) and
            controller.get("repository_path") == relative and
            {field: controller.get(field) for field in ("bytes", "sha256")} ==
            {field: closure_input[field] for field in ("bytes", "sha256")} and
            controller.get("commit_blob") == {
                field: closure_input[field] for field in ("bytes", "sha256")
            },
            f"retained bootstrap controller differs from source Git: {relative}",
        )
    python_controller = preflight.get("python_controller")
    provenance.require(
        isinstance(python_controller, dict) and
        python_controller.get("source") ==
        controller_sources["candle/cakeml_artifact_provenance.py"] and
        bootstrap.get("python_controller") == python_controller,
        "retained bootstrap Python controller/source binding mismatch",
    )
    observed_final = candle_input_closure(
        final_candle_root, final_candle_head, "retained final Candle checkout",
    )
    provenance.require(
        observed_final == final["closure"],
        "retained bootstrap transition final closure changed",
    )


def validate_linked_transition_record(candle_root: Path) -> dict[str, Any]:
    candle_root = candle_root.resolve(strict=True)
    record_path = candle_root / provenance.LINKED_RECORD_RELATIVE
    record = provenance.load_object(record_path)
    provenance.require(
        set(record) == {
            "schema", "kind", "promotion_status", "transition_mode",
            "transition_record",
            "transition_controller", "candle_commit", "cakeml_commit",
            "hol4_commit", "manifest_sha256", "bootstrap_record",
            "bootstrap_preflight", "bootstrap_log", "cake_patch",
            "cake_patch_derivation", "native_link_derivation", "outputs",
            "runtime_elf_closure", "version_output_sha256",
        },
        "malformed transition-linked provenance record",
    )
    provenance.require(
        record.get("schema") == TRANSITION_LINKED_SCHEMA and
        record.get("kind") == TRANSITION_LINKED_KIND and
        record.get("promotion_status") ==
        "diagnostic-only-requires-final-head-canonical-bootstrap" and
        record.get("transition_mode") ==
        "byte-identical-canonical-bootstrap-rebinding-v1",
        "unsupported transition-linked provenance record",
    )
    candle_head = require_commit(
        record.get("candle_commit"), "transition-linked Candle head",
    )
    validate_git_checkout(candle_root, candle_head, "Candle checkout")
    pins = provenance.expected_pins(candle_root)
    for field, expected in pins.items():
        provenance.require(
            record.get(field) == expected,
            f"transition-linked {field} mismatch",
        )
    controller = record.get("transition_controller")
    provenance.require(
        isinstance(controller, dict) and
        set(controller) == set(TRANSITION_LINK_CONTROLLER_INPUTS) and
        controller == transition_controller_closure(candle_root, candle_head),
        "transition-linked controller closure mismatch",
    )
    build_dir = provenance.validate_build_directory(candle_root)
    outputs = record.get("outputs")
    provenance.require(
        isinstance(outputs, dict) and set(outputs) == set(TRANSITION_LINKED_OUTPUTS),
        "transition-linked output set mismatch",
    )
    for name in TRANSITION_LINKED_OUTPUTS:
        provenance.validate_file_record(
            build_dir / name, outputs[name], f"transition-linked {name}",
        )
    provenance.validate_file_record(
        candle_root / "candle/cake.S.patch", record.get("cake_patch", {}),
        "CakeML assembly patch",
    )
    bootstrap = provenance.validate_linked_bootstrap_copy(
        build_dir, record, pins,
    )
    transition_record = record.get("transition_record")
    provenance.require(
        isinstance(transition_record, dict) and
        set(transition_record) == {"bytes", "sha256"} and
        transition_record == outputs[LINKED_TRANSITION_RECORD],
        "transition-linked transition identity mismatch",
    )
    transition_path = build_dir / LINKED_TRANSITION_RECORD
    provenance.validate_file_record(
        transition_path, transition_record, "linked bootstrap transition copy",
    )
    retained_transition = provenance.load_object(transition_path)
    retained_preflight = provenance.load_object(
        build_dir / provenance.LINKED_BOOTSTRAP_PREFLIGHT,
    )
    validate_retained_transition(
        retained_transition, bootstrap, retained_preflight,
        candle_root, candle_head,
    )
    observed_derivation = provenance.cake_patch_derivation(
        build_dir, bootstrap["inputs"]["cake.S"],
        candle_root / "candle/cake.S.patch",
    )
    provenance.require(
        observed_derivation == record.get("cake_patch_derivation"),
        "CakeML assembly patch derivation mismatch",
    )
    provenance.validate_native_link_derivation(
        build_dir, record.get("native_link_derivation"),
    )
    provenance.validate_root_runtime_aliases(candle_root, outputs)
    provenance.validate_elf_dynamic_closure(
        build_dir / "cake", record.get("runtime_elf_closure", {}),
    )
    provenance.validate_candle_elf_policy(record["runtime_elf_closure"])
    cake_commit, hol_commit, version_output = provenance.version_details(
        build_dir / "cake",
    )
    provenance.require(
        cake_commit == pins["cakeml_commit"], "runtime CakeML revision mismatch",
    )
    provenance.require(
        hol_commit == pins["hol4_commit"], "runtime HOL4 revision mismatch",
    )
    provenance.require(
        hashlib.sha256(version_output.encode()).hexdigest() ==
        record.get("version_output_sha256"),
        "runtime version output mismatch",
    )
    return record


def validate_linked_record(candle_root: Path) -> dict[str, Any]:
    record = provenance.load_object(
        candle_root.resolve() / provenance.LINKED_RECORD_RELATIVE,
    )
    schema = record.get("schema")
    if schema == provenance.LINKED_PROVENANCE_SCHEMA:
        linked = provenance.validate_linked_record(candle_root)
        root = candle_root.resolve(strict=True)
        bootstrap = provenance.validate_linked_bootstrap_copy(
            provenance.validate_build_directory(root),
            linked, provenance.expected_pins(root),
        )
        provenance.require(
            bootstrap.get("candle_root") == str(root) and
            bootstrap.get("candle_commit") == linked.get("candle_commit"),
            "schema-6 linked record is not an exact-root bootstrap link",
        )
        return linked
    if schema == TRANSITION_LINKED_SCHEMA:
        return validate_linked_transition_record(candle_root)
    raise provenance.ProvenanceError("unsupported linked provenance schema")


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
    """Create a durable schema-7 linked record after a valid transition."""
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
    materialize_transition_record(
        build_dir, transition_record_path, transition,
    )
    patch_derivation = provenance.cake_patch_derivation(
        build_dir, inputs["cake.S"], final_candle_root / "candle/cake.S.patch",
    )
    link_derivation = provenance.native_link_derivation(build_dir)
    controller_closure = transition_controller_closure(
        final_candle_root, final_candle_head,
    )
    record = {
        "schema": TRANSITION_LINKED_SCHEMA,
        "kind": TRANSITION_LINKED_KIND,
        "promotion_status":
            "diagnostic-only-requires-final-head-canonical-bootstrap",
        "transition_mode": "byte-identical-canonical-bootstrap-rebinding-v1",
        "transition_record": provenance.file_record(
            build_dir / LINKED_TRANSITION_RECORD,
        ),
        "transition_controller": controller_closure,
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
            for name in TRANSITION_LINKED_OUTPUTS
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
    check_linked_parser = subparsers.add_parser("check-linked")
    check_linked_parser.add_argument("--candle-root", type=Path, required=True)
    arguments = parser.parse_args()
    if arguments.command == "check-linked":
        validate_linked_record(arguments.candle_root)
        print("linked CakeML provenance PASS")
        return
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
