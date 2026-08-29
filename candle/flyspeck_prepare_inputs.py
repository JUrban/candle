#!/usr/bin/env python3
"""Authenticate and materialize host-prepared Flyspeck runtime inputs.

The selected Flyspeck build contains one compressed LP certificate.  The
compiled prover must consume and verify the certificate bytes, but it need not
run a host shell, tar, or rm.  This tool turns the pinned archive into a
separate, hash-addressed generated-input tree before Candle starts.
"""

from __future__ import annotations

import argparse
import ctypes
import errno
import hashlib
import json
import os
import stat
import subprocess
import tarfile
import tempfile
from pathlib import Path
from typing import Any, BinaryIO


CONTRACT_NAME = "flyspeck_lp_archive_contract.json"
RECEIPT_NAME = "flyspeck_lp_archive_receipt.json"
PENDING_RECEIPT_NAME = f".{RECEIPT_NAME}.pending"
CHUNK_BYTES = 1024 * 1024
ROOT_MODE = 0o555
DIRECTORY_MODE = 0o555
PREPARED_FILE_MODE = 0o644
RECEIPT_MODE = 0o444
PUBLICATION_RECORD = {
    "policy": "fresh-root-renameat2-noreplace",
    "failed_staging": "retained",
    "concurrent_same_uid_mutation": "trusted",
    "modes": {
        "root": "0555",
        "directories": "0555",
        "prepared_files": "0644",
        "receipt": "0444",
    },
}
AT_FDCWD = -100
RENAME_NOREPLACE = 1


def _sha256_file(path: Path) -> tuple[int, str]:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as source:
        while block := source.read(CHUNK_BYTES):
            digest.update(block)
            size += len(block)
    return size, digest.hexdigest()


def _git_head(root: Path) -> str:
    return subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=root, check=True,
        stdout=subprocess.PIPE, text=True,
    ).stdout.strip()


def _safe_relative(value: object, label: str) -> Path:
    if not isinstance(value, str) or not value:
        raise ValueError(f"invalid {label}")
    path = Path(value)
    if path.is_absolute() or ".." in path.parts:
        raise ValueError(f"unsafe {label}: {value}")
    return path


def load_contract_bytes(contract_bytes: bytes) -> dict[str, Any]:
    contract = json.loads(contract_bytes.decode("utf-8"))
    if contract.get("schema") != 1:
        raise ValueError("unsupported LP archive contract schema")
    commit = contract.get("flyspeck_commit")
    if not isinstance(commit, str) or len(commit) != 40:
        raise ValueError("invalid Flyspeck commit")
    archive = contract.get("archive")
    if not isinstance(archive, dict) or archive.get("format") != "tar.gz":
        raise ValueError("invalid LP archive record")
    _safe_relative(archive.get("path"), "archive path")
    members = contract.get("members")
    if not isinstance(members, list) or len(members) != 1:
        raise ValueError("LP archive contract must name exactly one member")
    member = members[0]
    if not isinstance(member, dict) or member.get("kind") != "regular-file":
        raise ValueError("LP archive member must be a regular file")
    _safe_relative(member.get("archive_name"), "archive member name")
    _safe_relative(member.get("output_path"), "generated output path")
    for record, label in ((archive, "archive"), (member, "member")):
        size = record.get("bytes")
        digest = record.get("sha256")
        if not isinstance(size, int) or size < 0:
            raise ValueError(f"invalid {label} byte count")
        if (
            not isinstance(digest, str) or len(digest) != 64
            or any(char not in "0123456789abcdef" for char in digest)
        ):
            raise ValueError(f"invalid {label} SHA-256")
    if member.get("mode") != 0o644:
        raise ValueError("generated LP certificate mode must be 0644")
    policy = contract.get("policy")
    expected_policy = {
        "archive_member_set": "exact",
        "links": "forbidden",
        "absolute_or_parent_paths": "forbidden",
        "output_root": "new separate generated-input tree",
        "overwrite": "forbidden; atomic no-replace publication after validation",
        "runtime_shell_or_extraction": "forbidden",
    }
    if policy != expected_policy:
        raise ValueError("LP archive policy mismatch")
    return contract


def load_contract(path: Path) -> dict[str, Any]:
    return load_contract_bytes(path.read_bytes())


def _validate_source(contract: dict[str, Any], source_root: Path) -> Path:
    observed_commit = _git_head(source_root)
    if observed_commit != contract["flyspeck_commit"]:
        raise ValueError(
            "Flyspeck commit mismatch: "
            f"expected {contract['flyspeck_commit']}, got {observed_commit}"
        )
    archive = contract["archive"]
    archive_path = source_root / _safe_relative(archive["path"], "archive path")
    size, digest = _sha256_file(archive_path)
    if size != archive["bytes"] or digest != archive["sha256"]:
        raise ValueError("LP archive digest or byte count mismatch")
    return archive_path


def _validated_member(
    contract: dict[str, Any], archive_path: Path,
) -> tuple[tarfile.TarFile, tarfile.TarInfo, BinaryIO]:
    archive = tarfile.open(archive_path, mode="r:gz")
    try:
        members = archive.getmembers()
        expected = contract["members"][0]
        if len(members) != 1 or members[0].name != expected["archive_name"]:
            raise ValueError("LP archive member set mismatch")
        member = members[0]
        _safe_relative(member.name, "observed archive member name")
        if not member.isreg() or member.issym() or member.islnk():
            raise ValueError("LP archive member is not an ordinary file")
        if member.size != expected["bytes"] or member.mode != expected["mode"]:
            raise ValueError("LP archive member metadata mismatch")
        stream = archive.extractfile(member)
        if stream is None:
            raise ValueError("LP archive member has no byte stream")
        return archive, member, stream
    except Exception:
        archive.close()
        raise


def _copy_and_hash(source: BinaryIO, destination: BinaryIO | None) -> tuple[int, str]:
    digest = hashlib.sha256()
    size = 0
    while block := source.read(CHUNK_BYTES):
        digest.update(block)
        size += len(block)
        if destination is not None:
            destination.write(block)
    return size, digest.hexdigest()


def _prepare_destination(output_root: Path, relative: Path) -> Path:
    parent = output_root
    for part in relative.parent.parts:
        parent /= part
        if parent.is_symlink():
            raise ValueError(f"refusing generated-input parent symlink: {parent}")
        if parent.exists():
            if not parent.is_dir():
                raise ValueError(f"generated-input parent is not a directory: {parent}")
        else:
            parent.mkdir(mode=0o700)
    destination = parent / relative.name
    if destination.is_symlink():
        raise ValueError(f"refusing generated-input symlink: {destination}")
    return destination


def _rename_noreplace(source: Path, destination: Path) -> None:
    libc = ctypes.CDLL(None, use_errno=True)
    try:
        renameat2 = libc.renameat2
    except AttributeError as error:
        raise OSError(
            errno.ENOSYS, "renameat2 is required for fresh-root publication"
        ) from error
    renameat2.argtypes = [
        ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p,
        ctypes.c_uint,
    ]
    renameat2.restype = ctypes.c_int
    if renameat2(
        AT_FDCWD, os.fsencode(source), AT_FDCWD, os.fsencode(destination),
        RENAME_NOREPLACE,
    ) != 0:
        error_number = ctypes.get_errno()
        if error_number == errno.EEXIST:
            raise FileExistsError(
                error_number, os.strerror(error_number), destination,
            )
        raise OSError(error_number, os.strerror(error_number), destination)


def evaluate(contract_path: Path, source_root: Path) -> dict[str, Any]:
    contract = load_contract(contract_path)
    archive_path = _validate_source(contract, source_root.resolve())
    archive, _, source = _validated_member(contract, archive_path)
    try:
        size, digest = _copy_and_hash(source, None)
    finally:
        source.close()
        archive.close()
    expected = contract["members"][0]
    if size != expected["bytes"] or digest != expected["sha256"]:
        raise ValueError("LP certificate digest or byte count mismatch")
    return contract


def materialize(
    contract_path: Path, source_root: Path, output_root: Path,
) -> dict[str, Any]:
    source_root = source_root.resolve()
    if output_root.is_symlink():
        raise ValueError(f"refusing generated output symlink: {output_root}")
    output_root = output_root.resolve()
    if (
        source_root == output_root
        or output_root.is_relative_to(source_root)
        or source_root.is_relative_to(output_root)
    ):
        raise ValueError("generated output must be separate from pinned source")
    contract_bytes = contract_path.read_bytes()
    contract = load_contract_bytes(contract_bytes)
    archive_path = _validate_source(contract, source_root)
    expected = contract["members"][0]
    if output_root.exists():
        raise ValueError(f"generated output root already exists: {output_root}")
    if not output_root.parent.is_dir():
        raise ValueError(
            f"generated output parent does not exist: {output_root.parent}"
        )
    temporary_root = Path(tempfile.mkdtemp(
        prefix=f".{output_root.name}.tmp.", dir=output_root.parent,
    ))
    staging_identity = os.stat(temporary_root, follow_symlinks=False)
    if not stat.S_ISDIR(staging_identity.st_mode):
        raise ValueError(
            f"generated staging root is not a directory: {temporary_root}"
        )
    try:
        destination = _prepare_destination(
            temporary_root,
            _safe_relative(expected["output_path"], "generated output path"),
        )
        temporary = destination.with_name(
            destination.name + f".tmp.{os.getpid()}"
        )
        if temporary.exists() or temporary.is_symlink():
            raise ValueError(f"refusing existing temporary output: {temporary}")
        archive, _, source = _validated_member(contract, archive_path)
        try:
            with temporary.open("xb") as output:
                size, digest = _copy_and_hash(source, output)
                output.flush()
                os.fsync(output.fileno())
            if size != expected["bytes"] or digest != expected["sha256"]:
                raise ValueError("LP certificate digest or byte count mismatch")
            if expected["mode"] != PREPARED_FILE_MODE:
                raise ValueError("unexpected prepared-file mode")
            os.chmod(temporary, PREPARED_FILE_MODE)
            os.replace(temporary, destination)
        finally:
            source.close()
            archive.close()
        receipt = {
            "schema": 2,
            "contract_sha256": hashlib.sha256(contract_bytes).hexdigest(),
            "flyspeck_commit": contract["flyspeck_commit"],
            "archive_sha256": contract["archive"]["sha256"],
            "publication": PUBLICATION_RECORD,
            "outputs": [{
                "path": expected["output_path"],
                "bytes": size,
                "sha256": digest,
                "mode": expected["mode"],
            }],
        }
        pending_receipt = temporary_root / PENDING_RECEIPT_NAME
        receipt_temp = pending_receipt.with_name(
            pending_receipt.name + f".tmp.{os.getpid()}"
        )
        receipt_temp.write_text(
            json.dumps(receipt, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        os.chmod(receipt_temp, RECEIPT_MODE)
        os.replace(receipt_temp, pending_receipt)
        for current, directory_names, _ in os.walk(
            temporary_root, topdown=False, followlinks=False,
        ):
            for directory_name in directory_names:
                directory = Path(current) / directory_name
                observed = os.stat(directory, follow_symlinks=False)
                if not stat.S_ISDIR(observed.st_mode):
                    raise ValueError(
                        f"generated staging entry is not a directory: {directory}"
                    )
                os.chmod(directory, DIRECTORY_MODE)
        observed_staging = os.stat(temporary_root, follow_symlinks=False)
        if (
            not stat.S_ISDIR(observed_staging.st_mode)
            or (observed_staging.st_dev, observed_staging.st_ino)
            != (staging_identity.st_dev, staging_identity.st_ino)
        ):
            raise ValueError(
                f"generated staging identity changed: {temporary_root}"
            )
        _rename_noreplace(temporary_root, output_root)
        os.replace(
            output_root / PENDING_RECEIPT_NAME,
            output_root / RECEIPT_NAME,
        )
        os.chmod(output_root, ROOT_MODE)
    except BaseException as error:
        # Retain failed staging rather than risk deleting a pathname exchanged
        # by another same-UID process.  Retries use a new final output root.
        error.add_note(f"failed generated-input staging retained: {temporary_root}")
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
        contract = evaluate(arguments.contract.resolve(), arguments.flyspeck_root)
        member = contract["members"][0]
        print(
            "LP archive contract ok: "
            f"{member['bytes']} bytes, {member['sha256']}"
        )
    else:
        receipt = materialize(
            arguments.contract.resolve(), arguments.flyspeck_root, arguments.write,
        )
        print(
            "LP generated input written: "
            f"{receipt['outputs'][0]['bytes']} bytes, "
            f"{receipt['outputs'][0]['sha256']}"
        )


if __name__ == "__main__":
    main()
