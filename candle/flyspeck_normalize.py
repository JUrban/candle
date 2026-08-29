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
import shutil
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
    if contract.get("schema") != 2:
        raise ValueError("unsupported Flyspeck normalization schema")
    entries = contract.get("entries")
    if not isinstance(entries, list) or not entries:
        raise ValueError("normalization contract must contain entries")
    ids: set[str] = set()
    operation_ids: set[str] = set()
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
        operations = entry.get("operations")
        if not isinstance(operations, list) or not operations:
            raise ValueError(f"normalization operations must be nonempty for {entry_id}")
        for operation in operations:
            operation_id = operation.get("id") if isinstance(operation, dict) else None
            if (
                not isinstance(operation_id, str)
                or not operation_id
                or operation_id in operation_ids
            ):
                raise ValueError("normalization operation ids must be nonempty and unique")
            kind = operation.get("kind")
            after = operation.get("after")
            line = operation.get("line")
            if not isinstance(line, int) or line < 1:
                raise ValueError(f"invalid source line for {operation_id}")
            if kind == "exact_bytes_replace_once":
                before = operation.get("before")
                if (
                    not isinstance(before, str)
                    or not before
                    or not isinstance(after, str)
                    or before == after
                ):
                    raise ValueError(f"invalid exact replacement for {operation_id}")
            elif kind == "exact_span_replace_once":
                start = operation.get("start")
                end = operation.get("end")
                end_line = operation.get("end_line")
                span_sha256 = operation.get("span_sha256")
                if (
                    not isinstance(start, str)
                    or not start
                    or not isinstance(end, str)
                    or not end
                    or not isinstance(after, str)
                    or not isinstance(end_line, int)
                    or end_line < line
                    or not isinstance(span_sha256, str)
                    or len(span_sha256) != 64
                    or any(char not in "0123456789abcdef" for char in span_sha256)
                ):
                    raise ValueError(f"invalid exact span replacement for {operation_id}")
            else:
                raise ValueError(f"unsupported normalization operation for {entry_id}")
            operation_ids.add(operation_id)
        for field, length in (
            ("source_sha256", 64), ("source_md5", 32),
            ("normalized_sha256", 64), ("normalized_md5", 32),
        ):
            value = entry.get(field)
            if not isinstance(value, str) or len(value) != length or any(
                char not in "0123456789abcdef" for char in value
            ):
                raise ValueError(f"invalid {field} for {entry_id}")
        if not isinstance(entry.get("normalized_bytes"), int) or entry["normalized_bytes"] < 0:
            raise ValueError(f"invalid normalized_bytes for {entry_id}")
        for field in ("semantic_rule", "scope_limit"):
            if not isinstance(entry.get(field), str) or not entry[field]:
                raise ValueError(f"invalid {field} for {entry_id}")
        ids.add(entry_id)
        paths.add(path)
    return contract


def normalize_bytes(source: bytes, entry: dict[str, Any]) -> bytes:
    entry_id = str(entry["id"])
    if _sha256(source) != entry["source_sha256"] or _md5(source) != entry["source_md5"]:
        raise ValueError(f"source digest mismatch for normalization {entry_id}")
    def operation_bounds(data: bytes, operation: dict[str, Any], phase: str) -> tuple[int, int]:
        operation_id = str(operation["id"])
        if operation["kind"] == "exact_bytes_replace_once":
            before = str(operation["before"]).encode("utf-8")
            if data.count(before) != 1:
                raise ValueError(
                    f"{phase} source anchor count is not one for " + operation_id
                )
            start_offset = data.index(before)
            return start_offset, start_offset + len(before)
        start_anchor = str(operation["start"]).encode("utf-8")
        end_anchor = str(operation["end"]).encode("utf-8")
        if data.count(start_anchor) != 1 or data.count(end_anchor) != 1:
            raise ValueError(
                f"{phase} source span anchor count is not one for " + operation_id
            )
        start_offset = data.index(start_anchor)
        end_offset = data.index(end_anchor) + len(end_anchor)
        if start_offset >= end_offset:
            raise ValueError(
                f"{phase} source span anchors are reversed for " + operation_id
            )
        return start_offset, end_offset

    for operation in entry["operations"]:
        operation_id = str(operation["id"])
        start_offset, end_offset = operation_bounds(source, operation, "original")
        observed_line = source.count(b"\n", 0, start_offset) + 1
        if observed_line != operation["line"]:
            raise ValueError(
                f"source line mismatch for {operation_id}: "
                f"expected {operation['line']}, got {observed_line}"
            )
        if operation["kind"] == "exact_span_replace_once":
            observed_end_line = source.count(b"\n", 0, end_offset - 1) + 1
            if observed_end_line != operation["end_line"]:
                raise ValueError(
                    f"source end line mismatch for {operation_id}: "
                    f"expected {operation['end_line']}, got {observed_end_line}"
                )
            if _sha256(source[start_offset:end_offset]) != operation["span_sha256"]:
                raise ValueError(f"source span digest mismatch for {operation_id}")
    normalized = source
    for operation in entry["operations"]:
        operation_id = str(operation["id"])
        after = str(operation["after"]).encode("utf-8")
        start_offset, end_offset = operation_bounds(normalized, operation, "exact")
        if operation["kind"] == "exact_span_replace_once" and (
            _sha256(normalized[start_offset:end_offset]) != operation["span_sha256"]
        ):
            raise ValueError(f"exact replacement span digest mismatch for {operation_id}")
        normalized = normalized[:start_offset] + after + normalized[end_offset:]
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


def _prepare_destination(output_root: Path, relative: Path) -> Path:
    parent = output_root
    for part in relative.parent.parts:
        parent = parent / part
        if parent.is_symlink():
            raise ValueError(f"refusing normalization output symlink: {parent}")
        if parent.exists():
            if not parent.is_dir():
                raise ValueError(
                    f"normalization output parent is not a directory: {parent}"
                )
        else:
            parent.mkdir()
    return parent / relative.name


def materialize(
    contract_path: Path, source_root: Path, output_root: Path,
) -> dict[str, Any]:
    source_root = source_root.resolve()
    if output_root.is_symlink():
        raise ValueError(f"refusing normalization output symlink: {output_root}")
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
    if output_root.exists():
        raise ValueError(f"normalization output root already exists: {output_root}")
    if not output_root.parent.is_dir():
        raise ValueError(
            f"normalization output parent does not exist: {output_root.parent}"
        )
    temporary_root = output_root.with_name(
        f"{output_root.name}.tmp.{os.getpid()}"
    )
    if temporary_root.exists() or temporary_root.is_symlink():
        raise ValueError(
            f"normalization temporary output already exists: {temporary_root}"
        )
    temporary_root.mkdir()
    rendered_entries: list[dict[str, Any]] = []
    try:
        for entry, normalized in outputs:
            destination = _prepare_destination(
                temporary_root, Path(entry["path"])
            )
            temporary = destination.with_name(destination.name + ".tmp")
            if destination.is_symlink() or temporary.is_symlink():
                raise ValueError(
                    f"refusing normalization output symlink: {destination}"
                )
            temporary.write_bytes(normalized)
            os.replace(temporary, destination)
            rendered_entries.append({
                "id": entry["id"],
                "path": entry["path"],
                "operation_ids": [
                    operation["id"] for operation in entry["operations"]
                ],
                "normalized_bytes": len(normalized),
                "normalized_sha256": _sha256(normalized),
                "normalized_md5": _md5(normalized),
            })
        receipt = {
            "schema": 2,
            "contract_sha256": contract_sha256(contract_path),
            "flyspeck_commit": contract["flyspeck_commit"],
            "entries": rendered_entries,
        }
        receipt_path = temporary_root / RECEIPT_NAME
        temporary_receipt = receipt_path.with_name(receipt_path.name + ".tmp")
        temporary_receipt.write_text(
            json.dumps(receipt, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        os.replace(temporary_receipt, receipt_path)
        os.rename(temporary_root, output_root)
    except BaseException:
        shutil.rmtree(temporary_root)
        raise
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
