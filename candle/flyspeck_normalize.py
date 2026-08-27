#!/usr/bin/env python3
"""Validate or materialize exact, hash-bound Flyspeck source normalizations.

The pinned upstream tree remains the authenticated input.  A release loader may
evaluate the normalized bytes only after checking both the input and output
digests recorded here.  Nothing in this module performs a heuristic rewrite.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
from pathlib import Path
from typing import Any


CONTRACT_NAME = "flyspeck_normalizations.json"
RECEIPT_NAME = "flyspeck_normalization_receipt.json"


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _md5(data: bytes) -> str:
    return hashlib.md5(data, usedforsecurity=False).hexdigest()


def contract_sha256(contract_path: Path) -> str:
    return _sha256(contract_path.read_bytes())


def load_contract(contract_path: Path) -> dict[str, Any]:
    contract = json.loads(contract_path.read_text(encoding="utf-8"))
    if contract.get("schema") != 1:
        raise ValueError("unsupported Flyspeck normalization schema")
    entries = contract.get("entries")
    if not isinstance(entries, list) or not entries:
        raise ValueError("normalization contract must contain entries")
    ids: set[str] = set()
    paths: set[str] = set()
    for entry in entries:
        entry_id = entry.get("id")
        path = entry.get("path")
        if not isinstance(entry_id, str) or not entry_id or entry_id in ids:
            raise ValueError("normalization ids must be nonempty and unique")
        if not isinstance(path, str) or not path or path in paths:
            raise ValueError("normalization paths must be nonempty and unique")
        relative = Path(path)
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"unsafe normalization path: {path}")
        source_key = entry.get("source_key")
        if source_key != f"flyspeck:{relative.as_posix()}":
            raise ValueError(f"source key/path mismatch for {entry_id}")
        operation = entry.get("operation")
        if not isinstance(operation, dict) or operation.get("kind") != "exact_bytes_replace_once":
            raise ValueError(f"unsupported normalization operation for {entry_id}")
        before = operation.get("before")
        after = operation.get("after")
        if not isinstance(before, str) or not before or not isinstance(after, str):
            raise ValueError(f"invalid exact replacement for {entry_id}")
        for field, length in (
            ("source_sha256", 64), ("source_md5", 32),
            ("normalized_sha256", 64), ("normalized_md5", 32),
        ):
            value = entry.get(field)
            if not isinstance(value, str) or len(value) != length or any(
                char not in "0123456789abcdef" for char in value
            ):
                raise ValueError(f"invalid {field} for {entry_id}")
        ids.add(entry_id)
        paths.add(path)
    return contract


def normalize_bytes(source: bytes, entry: dict[str, Any]) -> bytes:
    entry_id = str(entry["id"])
    if _sha256(source) != entry["source_sha256"] or _md5(source) != entry["source_md5"]:
        raise ValueError(f"source digest mismatch for normalization {entry_id}")
    operation = entry["operation"]
    before = str(operation["before"]).encode("utf-8")
    after = str(operation["after"]).encode("utf-8")
    if source.count(before) != 1:
        raise ValueError(f"exact replacement anchor count is not one for {entry_id}")
    normalized = source.replace(before, after, 1)
    if len(normalized) != entry["normalized_bytes"]:
        raise ValueError(f"normalized byte count mismatch for {entry_id}")
    if (
        _sha256(normalized) != entry["normalized_sha256"]
        or _md5(normalized) != entry["normalized_md5"]
    ):
        raise ValueError(f"normalized digest mismatch for {entry_id}")
    return normalized


def _git_head(root: Path) -> str:
    return subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=root, check=True,
        stdout=subprocess.PIPE, text=True,
    ).stdout.strip()


def evaluate_contract(
    contract_path: Path, source_root: Path,
) -> tuple[dict[str, Any], list[tuple[dict[str, Any], bytes]]]:
    contract = load_contract(contract_path)
    observed_commit = _git_head(source_root)
    if observed_commit != contract["flyspeck_commit"]:
        raise ValueError(
            "Flyspeck normalization commit mismatch: "
            f"expected {contract['flyspeck_commit']}, got {observed_commit}"
        )
    outputs: list[tuple[dict[str, Any], bytes]] = []
    for entry in contract["entries"]:
        source = (source_root / entry["path"]).read_bytes()
        outputs.append((entry, normalize_bytes(source, entry)))
    return contract, outputs


def materialize(
    contract_path: Path, source_root: Path, output_root: Path,
) -> dict[str, Any]:
    source_root = source_root.resolve()
    output_root = output_root.resolve()
    if (
        source_root == output_root
        or output_root.is_relative_to(source_root)
        or source_root.is_relative_to(output_root)
    ):
        raise ValueError(
            "normalization output must be separate from and must not contain "
            "the pinned source root"
        )
    contract, outputs = evaluate_contract(contract_path, source_root)
    output_root.mkdir(parents=True, exist_ok=True)
    rendered_entries: list[dict[str, Any]] = []
    for entry, normalized in outputs:
        destination = output_root / entry["path"]
        destination.parent.mkdir(parents=True, exist_ok=True)
        temporary = destination.with_name(destination.name + ".tmp")
        if destination.is_symlink() or temporary.is_symlink():
            raise ValueError(f"refusing normalization output symlink: {destination}")
        temporary.write_bytes(normalized)
        os.replace(temporary, destination)
        rendered_entries.append({
            "id": entry["id"],
            "path": entry["path"],
            "normalized_bytes": len(normalized),
            "normalized_sha256": _sha256(normalized),
            "normalized_md5": _md5(normalized),
        })
    receipt = {
        "schema": 1,
        "contract_sha256": contract_sha256(contract_path),
        "flyspeck_commit": contract["flyspeck_commit"],
        "entries": rendered_entries,
    }
    receipt_path = output_root / RECEIPT_NAME
    temporary_receipt = receipt_path.with_name(receipt_path.name + ".tmp")
    temporary_receipt.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8",
    )
    os.replace(temporary_receipt, receipt_path)
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--flyspeck-root", type=Path, required=True)
    parser.add_argument(
        "--contract", type=Path,
        default=Path(__file__).with_name(CONTRACT_NAME),
    )
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--check", action="store_true")
    action.add_argument("--write", type=Path, metavar="OUTPUT_ROOT")
    arguments = parser.parse_args()
    if arguments.check:
        contract, outputs = evaluate_contract(
            arguments.contract.resolve(), arguments.flyspeck_root.resolve(),
        )
        print(
            f"normalization contract ok: {len(outputs)} entries, "
            f"Flyspeck {contract['flyspeck_commit']}"
        )
    else:
        receipt = materialize(
            arguments.contract.resolve(), arguments.flyspeck_root.resolve(),
            arguments.write.resolve(),
        )
        print(
            f"normalization overlay written: {len(receipt['entries'])} entries, "
            f"contract {receipt['contract_sha256']}"
        )


if __name__ == "__main__":
    main()
