#!/usr/bin/env python3
"""Fail-closed provenance records for the pinned local CakeML handoff."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path
from typing import Any


BOOTSTRAP_INPUTS = (
    "cake.S",
    "config_enc_str.txt",
    "candle_boot.ml",
    "basis_ffi.c",
    "Makefile",
)
LINKED_OUTPUTS = (
    "cake.S",
    "cake",
    "config_enc_str.txt",
    "candle_boot.ml",
    "basis_ffi.c",
    "Makefile",
    "types.txt",
    "insulate.ml",
)
BOOTSTRAP_RELATIVE = Path("compiler/bootstrap/compilation/x64/64")
MANIFEST_RELATIVE = Path("candle/flyspeck_manifest.json")
LINKED_RECORD_RELATIVE = Path("candle/build/cakeml-build-provenance.json")


class ProvenanceError(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ProvenanceError(message)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while block := source.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def file_record(path: Path) -> dict[str, Any]:
    require(path.is_file(), f"missing provenance input: {path}")
    return {"bytes": path.stat().st_size, "sha256": sha256_file(path)}


def validate_file_record(path: Path, record: dict[str, Any], label: str) -> None:
    require(set(record) == {"bytes", "sha256"}, f"malformed {label} record")
    observed = file_record(path)
    require(observed == record, f"{label} provenance mismatch: {path}")


def load_object(path: Path) -> dict[str, Any]:
    require(path.is_file() and not path.is_symlink(), f"missing ordinary provenance record: {path}")
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"expected provenance JSON object: {path}")
    return value


def git_output(root: Path, *arguments: str) -> str:
    return subprocess.run(
        ["git", "-C", str(root), *arguments], check=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
    ).stdout.strip()


def validate_git(root: Path, expected_head: str, label: str) -> None:
    require(git_output(root, "rev-parse", "HEAD") == expected_head,
            f"{label} revision mismatch")
    require(not git_output(root, "status", "--porcelain", "--untracked-files=all"),
            f"{label} worktree is not clean")


def expected_pins(candle_root: Path) -> dict[str, str]:
    manifest_path = candle_root / MANIFEST_RELATIVE
    manifest = load_object(manifest_path)
    integration = manifest["dopen_corpus_contract"]["verified_cakeml_integration"]
    return {
        "cakeml_commit": integration["commit"],
        "hol4_commit": integration["proof_hol4_commit"],
        "manifest_sha256": sha256_file(manifest_path),
    }


def version_details(executable: Path) -> tuple[str, str, str]:
    require(executable.is_file(), f"missing linked CakeML executable: {executable}")
    output = subprocess.run(
        [str(executable), "--version"], check=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
    ).stdout
    cake_lines = [line.removeprefix("CakeML:").strip()
                  for line in output.splitlines() if line.startswith("CakeML:")]
    hol_lines = [line.removeprefix("HOL4:").strip()
                 for line in output.splitlines() if line.startswith("HOL4:")]
    require(len(cake_lines) == 1 and len(hol_lines) == 1,
            "linked compiler version identity missing or ambiguous")
    return cake_lines[0], hol_lines[0], output


def record_bootstrap(
    candle_root: Path,
    cakeml_root: Path,
    hol_root: Path,
    log_path: Path,
    output_path: Path,
) -> dict[str, Any]:
    candle_root = candle_root.resolve()
    cakeml_root = cakeml_root.resolve()
    hol_root = hol_root.resolve()
    log_path = log_path.resolve()
    output_path = output_path.resolve()
    pins = expected_pins(candle_root)
    validate_git(cakeml_root, pins["cakeml_commit"], "CakeML")
    validate_git(hol_root, pins["hol4_commit"], "HOL4")
    require(log_path.is_file() and not log_path.is_symlink(),
            "bootstrap log must be an ordinary file")
    log = log_path.read_text(encoding="utf-8", errors="replace")
    require("Exit status: 0" in log, "bootstrap log has no successful exit status")
    require("Holmake: [" in log and "cake.S" in log,
            "bootstrap log lacks the x64 cake.S target evidence")
    bootstrap_dir = cakeml_root / BOOTSTRAP_RELATIVE
    inputs = {name: file_record(bootstrap_dir / name) for name in BOOTSTRAP_INPUTS}
    record = {
        "schema": 1,
        "kind": "verified-cakeml-x64-64-bootstrap",
        **pins,
        "cakeml_root": str(cakeml_root),
        "hol4_root": str(hol_root),
        "build_command": (
            f"env HOLDIR={hol_root} {hol_root}/bin/Holmake -j1 cake.S"
        ),
        "bootstrap_log": {
            "path": str(log_path),
            **file_record(log_path),
        },
        "inputs": inputs,
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8",
    )
    return record


def validate_bootstrap_record(
    candle_root: Path,
    cakeml_root: Path,
    record_path: Path,
) -> dict[str, Any]:
    candle_root = candle_root.resolve()
    cakeml_root = cakeml_root.resolve()
    record_path = record_path.resolve()
    record = load_object(record_path)
    require(record.get("schema") == 1, "unsupported bootstrap provenance schema")
    require(record.get("kind") == "verified-cakeml-x64-64-bootstrap",
            "wrong bootstrap provenance kind")
    pins = expected_pins(candle_root)
    for field, expected in pins.items():
        require(record.get(field) == expected, f"bootstrap {field} mismatch")
    require(record.get("cakeml_root") == str(cakeml_root),
            "bootstrap CakeML root mismatch")
    hol_root = Path(record.get("hol4_root", "")).resolve()
    validate_git(cakeml_root, pins["cakeml_commit"], "CakeML")
    validate_git(hol_root, pins["hol4_commit"], "HOL4")
    log_record = record.get("bootstrap_log")
    require(isinstance(log_record, dict) and "path" in log_record,
            "malformed bootstrap log record")
    log_path = Path(log_record["path"])
    validate_file_record(
        log_path, {key: log_record[key] for key in ("bytes", "sha256")},
        "bootstrap log",
    )
    log = log_path.read_text(encoding="utf-8", errors="replace")
    require("Exit status: 0" in log, "bootstrap log no longer records success")
    inputs = record.get("inputs")
    require(isinstance(inputs, dict) and set(inputs) == set(BOOTSTRAP_INPUTS),
            "bootstrap input set mismatch")
    bootstrap_dir = cakeml_root / BOOTSTRAP_RELATIVE
    for name in BOOTSTRAP_INPUTS:
        validate_file_record(bootstrap_dir / name, inputs[name], f"bootstrap {name}")
    return record


def record_linked(
    candle_root: Path,
    cakeml_root: Path,
    bootstrap_record_path: Path,
    output_path: Path,
) -> dict[str, Any]:
    candle_root = candle_root.resolve()
    bootstrap_record_path = bootstrap_record_path.resolve()
    bootstrap = validate_bootstrap_record(
        candle_root, cakeml_root, bootstrap_record_path,
    )
    candle_head = git_output(candle_root, "rev-parse", "HEAD")
    validate_git(candle_root, candle_head, "Candle")
    build_dir = candle_root / "candle/build"
    inputs = bootstrap["inputs"]
    for name in ("config_enc_str.txt", "candle_boot.ml", "basis_ffi.c", "Makefile"):
        validate_file_record(build_dir / name, inputs[name], f"copied {name}")
    cake_commit, hol_commit, version_output = version_details(build_dir / "cake")
    require(cake_commit == bootstrap["cakeml_commit"],
            "linked compiler CakeML revision mismatch")
    require(hol_commit == bootstrap["hol4_commit"],
            "linked compiler HOL4 revision mismatch")
    record = {
        "schema": 1,
        "kind": "candle-linked-pinned-cakeml",
        "candle_commit": candle_head,
        "cakeml_commit": cake_commit,
        "hol4_commit": hol_commit,
        "manifest_sha256": bootstrap["manifest_sha256"],
        "bootstrap_record": file_record(bootstrap_record_path),
        "bootstrap_record_path": str(bootstrap_record_path),
        "cake_patch": file_record(candle_root / "candle/cake.S.patch"),
        "outputs": {name: file_record(build_dir / name) for name in LINKED_OUTPUTS},
        "version_output_sha256": hashlib.sha256(version_output.encode()).hexdigest(),
    }
    output_path = output_path.resolve()
    output_path.write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8",
    )
    return record


def validate_linked_record(candle_root: Path) -> dict[str, Any]:
    candle_root = candle_root.resolve()
    record_path = candle_root / LINKED_RECORD_RELATIVE
    record = load_object(record_path)
    require(record.get("schema") == 1, "unsupported linked provenance schema")
    require(record.get("kind") == "candle-linked-pinned-cakeml",
            "wrong linked provenance kind")
    candle_head = record.get("candle_commit")
    require(isinstance(candle_head, str) and len(candle_head) == 40,
            "linked Candle revision missing")
    validate_git(candle_root, candle_head, "Candle")
    pins = expected_pins(candle_root)
    for field, expected in pins.items():
        require(record.get(field) == expected, f"linked {field} mismatch")
    bootstrap_path = Path(record.get("bootstrap_record_path", ""))
    validate_file_record(
        bootstrap_path, record.get("bootstrap_record", {}), "bootstrap record",
    )
    validate_file_record(
        candle_root / "candle/cake.S.patch", record.get("cake_patch", {}),
        "CakeML assembly patch",
    )
    outputs = record.get("outputs")
    require(isinstance(outputs, dict) and set(outputs) == set(LINKED_OUTPUTS),
            "linked output set mismatch")
    build_dir = candle_root / "candle/build"
    for name in LINKED_OUTPUTS:
        validate_file_record(build_dir / name, outputs[name], f"linked {name}")
    cake_commit, hol_commit, version_output = version_details(build_dir / "cake")
    require(cake_commit == pins["cakeml_commit"], "runtime CakeML revision mismatch")
    require(hol_commit == pins["hol4_commit"], "runtime HOL4 revision mismatch")
    require(hashlib.sha256(version_output.encode()).hexdigest()
            == record.get("version_output_sha256"),
            "runtime version output mismatch")
    return record


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)

    record_parser = subparsers.add_parser("record-bootstrap")
    record_parser.add_argument("--candle-root", type=Path, required=True)
    record_parser.add_argument("--cakeml-root", type=Path, required=True)
    record_parser.add_argument("--hol-root", type=Path, required=True)
    record_parser.add_argument("--bootstrap-log", type=Path, required=True)
    record_parser.add_argument("--write", type=Path, required=True)

    check_parser = subparsers.add_parser("check-bootstrap")
    check_parser.add_argument("--candle-root", type=Path, required=True)
    check_parser.add_argument("--cakeml-root", type=Path, required=True)
    check_parser.add_argument("--record", type=Path, required=True)

    linked_parser = subparsers.add_parser("record-linked")
    linked_parser.add_argument("--candle-root", type=Path, required=True)
    linked_parser.add_argument("--cakeml-root", type=Path, required=True)
    linked_parser.add_argument("--bootstrap-record", type=Path, required=True)
    linked_parser.add_argument("--write", type=Path, required=True)

    runtime_parser = subparsers.add_parser("check-linked")
    runtime_parser.add_argument("--candle-root", type=Path, required=True)

    arguments = parser.parse_args()
    if arguments.command == "record-bootstrap":
        record_bootstrap(
            arguments.candle_root, arguments.cakeml_root, arguments.hol_root,
            arguments.bootstrap_log, arguments.write,
        )
        print(f"bootstrap provenance recorded: {arguments.write}")
    elif arguments.command == "check-bootstrap":
        validate_bootstrap_record(
            arguments.candle_root, arguments.cakeml_root, arguments.record,
        )
        print("bootstrap provenance PASS")
    elif arguments.command == "record-linked":
        record_linked(
            arguments.candle_root, arguments.cakeml_root,
            arguments.bootstrap_record, arguments.write,
        )
        print(f"linked CakeML provenance recorded: {arguments.write}")
    else:
        validate_linked_record(arguments.candle_root)
        print("linked CakeML provenance PASS")


if __name__ == "__main__":
    main()
