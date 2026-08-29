#!/usr/bin/env python3
"""Generate and validate the pinned direct-Flyspeck decimal-float corpus.

This is a host-side compatibility gate.  It authenticates every selected
source byte before scanning it, reproduces the exact decimal-float inventory,
and pins OCaml 4.14.1 IEEE-754 observations.  It does not execute Candle and is
not theorem, S2, or S3 evidence.
"""

from __future__ import annotations

import argparse
import bisect
import collections
import ctypes
import errno
import hashlib
import json
import locale
import os
from pathlib import Path
import re
import stat
import struct
import subprocess
import tempfile
from typing import Any


SCHEMA_VERSION = 1
LEDGER_ID = "CANDLE-OCAML-FLOAT-LITERAL-001"
EXPECTED_OCAML_VERSION = "4.14.1"
EXPECTED_CANDLE_BASE = "5358f96fd52191a321893db8db25810efaafbbbb"
EXPECTED_MANIFEST_SHA256 = (
    "1521484e31ae03404d5395dfa4c3496e6cc9f3f213f2017422709fc86b7838d1"
)
EXPECTED_FLYSPECK_COMMIT = "1ce0353008eba83d3c76ae9a25c3c242e4802d53"
EXPECTED_NORMALIZATION_CONTRACT_SHA256 = (
    "ac925270aa6a8605a8f70ab170ff965c3e4a4d6410623e3d3a6d51976ff1da08"
)
EXPECTED_NORMALIZATION_RECEIPT_SHA256 = (
    "852ccd8b086377ebdb7654d1709c6a1916a865f693da12aa749bcfb30a0c71c4"
)
EXPECTED_SOURCE_NODES = 400
EXPECTED_NORMALIZED_FILES = 18
EXPECTED_CODE_OCCURRENCES = 15_775
EXPECTED_UNIQUE_SPELLINGS = 1_741
EXPECTED_FLOAT_FILES = 9
EXPECTED_UNIQUE_SPELLING_SHA256 = (
    "174fe9827e0e52fbe7e4d2f5303a56996321070921bd0d0cecbca790bf04caa2"
)
EXPECTED_RAW_CONTEXT_COUNTS = {
    "code": 15_775,
    "comment": 5_408,
    "quotation": 38_654,
    "string": 4_103,
}
EXPECTED_INVALID_SUFFIX_COUNTS = {"comment": 18, "string": 3_404}

MANIFEST_RELATIVE = Path("candle/flyspeck_manifest.json")
NORMALIZATION_CONTRACT_RELATIVE = Path("candle/flyspeck_normalizations.json")
NORMALIZATION_RECEIPT = Path("flyspeck_normalization_receipt.json")
NORMALIZATION_PUBLICATION = {
    "policy": "fresh-root-renameat2-noreplace",
    "failed_staging": "retained",
    "concurrent_same_uid_mutation": "trusted",
    "modes": {
        "root": "0555", "directories": "0555",
        "normalized_files": "0444", "receipt": "0444",
    },
}
ARTIFACT_RELATIVE = Path("candle/compatibility/flyspeck_float_corpus.json")

# CakeML's proved lexer accepts
# [0-9][0-9_]*("."[0-9_]*)?([eE][+-]?[0-9_]+)? and requires either
# the point or exponent component.  The prefix guard prevents a numeric
# substring of an identifier from being counted as a token start.
DECIMAL_FLOAT_RE = re.compile(
    rb"(?<![A-Za-z0-9_'])"
    rb"[0-9][0-9_]*"
    rb"(?:(?:\.[0-9_]*)(?:[eE][+-]?[0-9][0-9_]*)?"
    rb"|(?:[eE][+-]?[0-9][0-9_]*))"
)
HEX_FLOAT_RE = re.compile(
    rb"(?<![A-Za-z0-9_'])0[xX][0-9A-Fa-f_]+"
    rb"(?:\.[0-9A-Fa-f_]*)?[pP][+-]?[0-9][0-9_]*"
)
INVALID_SUFFIX = frozenset(
    b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz_"
)
CONTEXTS = ("code", "comment", "quotation", "string")


class CorpusError(ValueError):
    """An authenticated input or corpus invariant did not match."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise CorpusError(message)


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def file_record(path: Path) -> dict[str, Any]:
    require(path.is_file() and not path.is_symlink(),
            f"missing ordinary input file: {path}")
    sha256 = hashlib.sha256()
    md5 = hashlib.md5(usedforsecurity=False)
    size = 0
    with path.open("rb") as source:
        while block := source.read(1024 * 1024):
            size += len(block)
            sha256.update(block)
            md5.update(block)
    return {"bytes": size, "md5": md5.hexdigest(),
            "sha256": sha256.hexdigest()}


def sha256_file(path: Path) -> str:
    return file_record(path)["sha256"]


def load_object(path: Path, label: str) -> dict[str, Any]:
    require(path.is_file() and not path.is_symlink(),
            f"missing ordinary {label}: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise CorpusError(f"cannot read {label} {path}: {error}") from error
    require(isinstance(value, dict), f"expected JSON object for {label}")
    return value


def validate_record(path: Path, expected: dict[str, Any], label: str) -> None:
    observed = file_record(path)
    projection = {field: observed[field] for field in expected}
    require(projection == expected,
            f"{label} byte identity mismatch: {path}")


def validate_materialized_tree(
    root: Path, expected_files: dict[str, int], label: str,
) -> None:
    require(root.is_dir() and not root.is_symlink(),
            f"missing ordinary {label} root: {root}")
    expected_paths = {Path(relative) for relative in expected_files}
    expected_directories = {Path(".")}
    for relative in expected_paths:
        expected_directories.update(
            parent for parent in relative.parents if parent != Path(".")
        )
    observed_files: set[Path] = set()
    observed_directories: set[Path] = {Path(".")}
    root_status = os.stat(root, follow_symlinks=False)
    require(stat.S_ISDIR(root_status.st_mode), f"non-directory {label} root")
    require(stat.S_IMODE(root_status.st_mode) == 0o555,
            f"{label} root mode mismatch")
    for current, directory_names, file_names in os.walk(
        root, topdown=True, followlinks=False,
    ):
        current_path = Path(current)
        for name in directory_names:
            path = current_path / name
            observed = os.stat(path, follow_symlinks=False)
            require(stat.S_ISDIR(observed.st_mode),
                    f"non-directory or symlink in {label}: {path}")
            require(stat.S_IMODE(observed.st_mode) == 0o555,
                    f"{label} directory mode mismatch: {path}")
            observed_directories.add(path.relative_to(root))
        for name in file_names:
            path = current_path / name
            observed = os.stat(path, follow_symlinks=False)
            require(stat.S_ISREG(observed.st_mode),
                    f"non-regular or symlink in {label}: {path}")
            relative = path.relative_to(root)
            observed_files.add(relative)
            require(relative in expected_paths,
                    f"unexpected file in {label}: {relative}")
            require(
                stat.S_IMODE(observed.st_mode) == expected_files[str(relative)],
                f"{label} file mode mismatch: {relative}",
            )
    require(observed_directories == expected_directories,
            f"{label} directory set mismatch")
    require(observed_files == expected_paths, f"{label} file set mismatch")


def git_output(root: Path, *arguments: str) -> str:
    try:
        return subprocess.run(
            ["/usr/bin/git", "-C", str(root), *arguments], check=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            env={"LC_ALL": "C", "PATH": "/usr/bin:/bin"},
        ).stdout.strip()
    except subprocess.CalledProcessError as error:
        raise CorpusError(
            f"git validation failed for {root}: {error.stderr.strip()}"
        ) from error


def validate_roots(candle_root: Path, flyspeck_root: Path) -> None:
    require(candle_root.is_dir(), f"missing Candle root: {candle_root}")
    require(flyspeck_root.is_dir(), f"missing Flyspeck root: {flyspeck_root}")
    ancestor = subprocess.run(
        ["/usr/bin/git", "-C", str(candle_root), "merge-base", "--is-ancestor",
         EXPECTED_CANDLE_BASE, "HEAD"], check=False,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        env={"LC_ALL": "C", "PATH": "/usr/bin:/bin"},
    )
    require(ancestor.returncode == 0,
            "Candle worktree does not descend from the pinned corpus base")
    require(git_output(flyspeck_root, "rev-parse", "HEAD") ==
            EXPECTED_FLYSPECK_COMMIT, "Flyspeck revision mismatch")
    require(not git_output(
        flyspeck_root, "status", "--porcelain", "--untracked-files=all"
    ), "Flyspeck worktree is not clean")


def _safe_relative(value: Any, label: str) -> Path:
    require(isinstance(value, str) and value, f"missing {label} path")
    path = Path(value)
    require(not path.is_absolute() and ".." not in path.parts,
            f"unsafe {label} path: {value}")
    return path


def validate_inputs(
    candle_root: Path,
    flyspeck_root: Path,
    overlay_root: Path,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    """Authenticate the manifest, all original nodes, and all overlay bytes."""
    require(not overlay_root.is_symlink(),
            "normalization overlay root is a symlink")
    candle_root = candle_root.resolve()
    flyspeck_root = flyspeck_root.resolve()
    overlay_root = overlay_root.resolve()
    validate_roots(candle_root, flyspeck_root)
    require(overlay_root.is_dir(), f"missing normalization overlay: {overlay_root}")

    manifest_path = candle_root / MANIFEST_RELATIVE
    require(sha256_file(manifest_path) == EXPECTED_MANIFEST_SHA256,
            "Flyspeck manifest digest mismatch")
    manifest = load_object(manifest_path, "Flyspeck manifest")
    require(manifest.get("source_node_count") == EXPECTED_SOURCE_NODES,
            "manifest source-node count mismatch")
    nodes = manifest.get("source_nodes")
    require(isinstance(nodes, dict) and len(nodes) == EXPECTED_SOURCE_NODES,
            "manifest source-node table mismatch")
    require(manifest.get("repositories", {}).get("flyspeck", {}).get("commit") ==
            EXPECTED_FLYSPECK_COMMIT, "manifest Flyspeck pin mismatch")

    normalization = manifest.get("source_normalization_contract")
    require(isinstance(normalization, dict),
            "missing source normalization contract")
    require(normalization.get("contract_sha256") ==
            EXPECTED_NORMALIZATION_CONTRACT_SHA256,
            "manifest normalization contract mismatch")
    require(normalization.get("entry_count") == EXPECTED_NORMALIZED_FILES,
            "manifest normalization count mismatch")
    contract_path = candle_root / NORMALIZATION_CONTRACT_RELATIVE
    require(sha256_file(contract_path) ==
            EXPECTED_NORMALIZATION_CONTRACT_SHA256,
            "normalization contract byte digest mismatch")

    receipt_path = overlay_root / NORMALIZATION_RECEIPT
    normalization_files = {
        entry["path"]: 0o444 for entry in normalization["entries"]
    }
    normalization_files[str(NORMALIZATION_RECEIPT)] = 0o444
    validate_materialized_tree(
        overlay_root, normalization_files, "normalization overlay",
    )
    require(sha256_file(receipt_path) ==
            EXPECTED_NORMALIZATION_RECEIPT_SHA256,
            "normalization receipt digest mismatch")
    receipt = load_object(receipt_path, "normalization receipt")
    require(receipt.get("schema") == 3,
            "unsupported normalization receipt schema")
    require(receipt.get("publication") == NORMALIZATION_PUBLICATION,
            "normalization publication contract mismatch")
    require(receipt.get("flyspeck_commit") == EXPECTED_FLYSPECK_COMMIT,
            "normalization receipt Flyspeck pin mismatch")
    require(receipt.get("contract_sha256") ==
            EXPECTED_NORMALIZATION_CONTRACT_SHA256,
            "normalization receipt contract mismatch")
    contract_entries = normalization.get("entries")
    receipt_entries = receipt.get("entries")
    require(isinstance(contract_entries, list) and
            len(contract_entries) == EXPECTED_NORMALIZED_FILES,
            "normalization contract entry table mismatch")
    require(isinstance(receipt_entries, list) and
            len(receipt_entries) == EXPECTED_NORMALIZED_FILES,
            "normalization receipt entry table mismatch")
    contract_by_path = {entry["path"]: entry for entry in contract_entries}
    receipt_by_path = {entry["path"]: entry for entry in receipt_entries}
    require(len(contract_by_path) == EXPECTED_NORMALIZED_FILES and
            len(receipt_by_path) == EXPECTED_NORMALIZED_FILES,
            "duplicate normalization path")
    require(contract_by_path.keys() == receipt_by_path.keys(),
            "normalization receipt path set mismatch")

    for relative, record in sorted(contract_by_path.items()):
        observed = receipt_by_path[relative]
        for field in ("id", "normalized_bytes", "normalized_md5",
                      "normalized_sha256"):
            require(observed.get(field) == record.get(field),
                    f"normalization receipt {field} mismatch: {relative}")
        output_path = overlay_root / _safe_relative(relative, "overlay")
        validate_record(output_path, {
            "bytes": record["normalized_bytes"],
            "md5": record["normalized_md5"],
            "sha256": record["normalized_sha256"],
        }, f"normalized source {relative}")

    runtime_sources = []
    for key, node in sorted(nodes.items()):
        require(isinstance(node, dict), f"malformed source node: {key}")
        repository = node.get("repository")
        require(repository in ("candle", "flyspeck"),
                f"unknown source repository: {key}")
        relative = _safe_relative(node.get("path"), f"source node {key}")
        original_root = candle_root if repository == "candle" else flyspeck_root
        original_path = original_root / relative
        validate_record(original_path, {
            "bytes": node["bytes"], "md5": node["md5"],
            "sha256": node["sha256"],
        }, f"original source node {key}")

        execution = node.get("execution_normalization")
        if execution is None:
            runtime_path = original_path
            runtime_sha256 = node["sha256"]
        else:
            require(isinstance(execution, dict),
                    f"malformed execution normalization: {key}")
            contract = contract_by_path.get(relative.as_posix())
            require(contract is not None and contract.get("source_key") == key,
                    f"missing normalization contract for source node: {key}")
            for field in ("id", "kind", "normalized_bytes",
                          "normalized_md5", "normalized_sha256",
                          "operation_count"):
                require(execution.get(field) == contract.get(field),
                        f"source normalization {field} mismatch: {key}")
            runtime_path = overlay_root / relative
            runtime_sha256 = execution["normalized_sha256"]
        runtime_sources.append({
            "key": key,
            "path": relative.as_posix(),
            "repository": repository,
            "original_sha256": node["sha256"],
            "runtime_path": runtime_path,
            "runtime_sha256": runtime_sha256,
            "normalized": execution is not None,
        })

    require(sum(item["normalized"] for item in runtime_sources) ==
            EXPECTED_NORMALIZED_FILES,
            "selected runtime normalization count mismatch")
    return manifest, runtime_sources


def _excluded_ranges(data: bytes) -> list[tuple[int, int, str]]:
    """Return sorted comment/string/HOL-quotation byte ranges."""
    ranges: list[tuple[int, int, str]] = []
    index = 0
    while index < len(data):
        if data.startswith(b"(*", index):
            start = index
            depth = 1
            index += 2
            while index < len(data) and depth:
                if data.startswith(b"(*", index):
                    depth += 1
                    index += 2
                elif data.startswith(b"*)", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            require(depth == 0, "unterminated nested comment")
            ranges.append((start, index, "comment"))
            continue
        if data[index:index + 1] == b'"':
            start = index
            index += 1
            while index < len(data):
                if data[index:index + 1] == b"\\":
                    index += 2
                elif data[index:index + 1] == b'"':
                    index += 1
                    break
                else:
                    index += 1
            require(index <= len(data) and data[index - 1:index] == b'"',
                    "unterminated string")
            ranges.append((start, index, "string"))
            continue
        if data[index:index + 1] == b"`":
            start = index
            index += 1
            end = data.find(b"`", index)
            require(end >= 0, "unterminated HOL quotation")
            index = end + 1
            ranges.append((start, index, "quotation"))
            continue
        index += 1
    return ranges


def _context_at(
    offset: int,
    ranges: list[tuple[int, int, str]],
    starts: list[int],
) -> str:
    index = bisect.bisect_right(starts, offset) - 1
    if index >= 0 and offset < ranges[index][1]:
        return ranges[index][2]
    return "code"


def scan_source(key: str, data: bytes) -> dict[str, Any]:
    ranges = _excluded_ranges(data)
    starts = [item[0] for item in ranges]
    newlines = [-1] + [match.start() for match in re.finditer(rb"\n", data)]
    raw_counts: collections.Counter[str] = collections.Counter()
    invalid_counts: collections.Counter[str] = collections.Counter()
    sites = []
    for match in DECIMAL_FLOAT_RE.finditer(data):
        context = _context_at(match.start(), ranges, starts)
        raw_counts[context] += 1
        suffix = data[match.end():match.end() + 1]
        if suffix and suffix[0] in INVALID_SUFFIX:
            invalid_counts[context] += 1
            continue
        if context != "code":
            continue
        line_index = bisect.bisect_left(newlines, match.start())
        sites.append({
            "source": key,
            "line": line_index,
            "column": match.start() - newlines[line_index - 1],
            "literal": match.group().decode("ascii"),
        })
    hex_counts: collections.Counter[str] = collections.Counter()
    for match in HEX_FLOAT_RE.finditer(data):
        hex_counts[_context_at(match.start(), ranges, starts)] += 1
    return {
        "sites": sites,
        "raw_context_counts": dict(raw_counts),
        "invalid_suffix_context_counts": dict(invalid_counts),
        "hex_context_counts": dict(hex_counts),
    }


def _sum_counts(
    target: collections.Counter[str], value: dict[str, int]
) -> None:
    for key, count in value.items():
        target[key] += count


def scan_corpus(
    manifest: dict[str, Any],
    runtime_sources: list[dict[str, Any]],
) -> dict[str, Any]:
    strata = [record["name"] for record in manifest["build_strata"]]
    stratum_rank = {name: index for index, name in enumerate(strata)}
    raw_counts: collections.Counter[str] = collections.Counter()
    invalid_counts: collections.Counter[str] = collections.Counter()
    hex_counts: collections.Counter[str] = collections.Counter()
    sites = []
    file_records = []
    for source in runtime_sources:
        observed = file_record(source["runtime_path"])
        require(observed["sha256"] == source["runtime_sha256"],
                f"runtime source changed after preflight: {source['key']}")
        result = scan_source(source["key"], source["runtime_path"].read_bytes())
        _sum_counts(raw_counts, result["raw_context_counts"])
        _sum_counts(invalid_counts, result["invalid_suffix_context_counts"])
        _sum_counts(hex_counts, result["hex_context_counts"])
        source_strata = manifest["source_node_strata"].get(source["key"])
        require(isinstance(source_strata, list) and source_strata,
                f"missing source stratum: {source['key']}")
        earliest = min(source_strata, key=stratum_rank.__getitem__)
        for site in result["sites"]:
            site["earliest_stratum"] = earliest
        sites.extend(result["sites"])
        if result["sites"]:
            file_records.append({
                "source": source["key"],
                "path": source["path"],
                "earliest_stratum": earliest,
                "occurrence_count": len(result["sites"]),
                "unique_spelling_count": len({
                    site["literal"] for site in result["sites"]
                }),
                "original_sha256": source["original_sha256"],
                "runtime_sha256": source["runtime_sha256"],
                "normalized": source["normalized"],
            })

    sites.sort(key=lambda site: (
        site["source"], site["line"], site["column"], site["literal"]
    ))
    literals = collections.Counter(site["literal"] for site in sites)
    unique = sorted(literals)
    require(len(sites) == EXPECTED_CODE_OCCURRENCES,
            "decimal-float occurrence count mismatch")
    require(len(unique) == EXPECTED_UNIQUE_SPELLINGS,
            "decimal-float unique-spelling count mismatch")
    require(len(file_records) == EXPECTED_FLOAT_FILES,
            "decimal-float source-file count mismatch")
    require(dict(sorted(raw_counts.items())) == EXPECTED_RAW_CONTEXT_COUNTS,
            "raw decimal context counts mismatch")
    require(dict(sorted(invalid_counts.items())) ==
            EXPECTED_INVALID_SUFFIX_COUNTS,
            "invalid decimal suffix counts mismatch")
    require(not hex_counts, "hexadecimal float candidate entered pinned graph")
    require(canonical_sha256(unique) == EXPECTED_UNIQUE_SPELLING_SHA256,
            "unique decimal spelling digest mismatch")

    source_sets: dict[str, set[str]] = collections.defaultdict(set)
    for site in sites:
        source_sets[site["literal"]].add(site["source"])
    form_counts: collections.Counter[str] = collections.Counter()
    unique_form_counts: collections.Counter[str] = collections.Counter()
    stratum_counts: collections.Counter[str] = collections.Counter()
    for site in sites:
        literal = site["literal"]
        form = ("exponent" if "e" in literal.lower() else
                "trailing_point" if literal.endswith(".") else
                "fractional_decimal")
        form_counts[form] += 1
        stratum_counts[site["earliest_stratum"]] += 1
    for literal in unique:
        form = ("exponent" if "e" in literal.lower() else
                "trailing_point" if literal.endswith(".") else
                "fractional_decimal")
        unique_form_counts[form] += 1
    return {
        "sites": sites,
        "literals": literals,
        "unique": unique,
        "source_sets": source_sets,
        "files": sorted(file_records, key=lambda record: record["source"]),
        "raw_context_counts": dict(sorted(raw_counts.items())),
        "invalid_suffix_context_counts": dict(sorted(invalid_counts.items())),
        "hex_context_counts": dict(sorted(hex_counts.items())),
        "form_occurrence_counts": dict(sorted(form_counts.items())),
        "form_unique_counts": dict(sorted(unique_form_counts.items())),
        "earliest_stratum_counts": dict(sorted(
            stratum_counts.items(), key=lambda item: stratum_rank[item[0]]
        )),
    }


def _fixed_environment() -> dict[str, str]:
    return {"LC_ALL": "C", "PATH": "/usr/bin:/bin"}


def ocaml_words(literals: list[str], ocamlc: str) -> list[str]:
    version = subprocess.run(
        [ocamlc, "-version"], check=False, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True, env=_fixed_environment(),
    )
    require(version.returncode == 0,
            f"cannot execute OCaml compiler: {version.stderr.strip()}")
    require(version.stdout.strip() == EXPECTED_OCAML_VERSION,
            f"OCaml reference version mismatch: {version.stdout.strip()}")
    with tempfile.TemporaryDirectory(prefix="candle-flyspeck-floats-") as tmp:
        root = Path(tmp)
        source = root / "oracle.ml"
        executable = root / "oracle"
        lines = [
            f'Printf.printf "{index}=%Lu\\n" '
            f'(Int64.bits_of_float ({literal}));;'
            for index, literal in enumerate(literals)
        ]
        source.write_text("\n".join(lines) + "\n", encoding="ascii")
        compiled = subprocess.run(
            [ocamlc, "-o", str(executable), str(source)], check=False,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            env=_fixed_environment(),
        )
        require(compiled.returncode == 0,
                "OCaml rejected corpus float source: " + compiled.stderr)
        executed = subprocess.run(
            [str(executable)], check=False, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, text=True, env=_fixed_environment(),
        )
        require(executed.returncode == 0,
                "OCaml corpus float oracle failed: " + executed.stderr)
    observed: dict[int, str] = {}
    for line in executed.stdout.splitlines():
        match = re.fullmatch(r"([0-9]+)=([0-9]+)", line)
        require(match is not None, f"malformed OCaml oracle output: {line}")
        index = int(match.group(1))
        require(index not in observed, f"duplicate OCaml oracle index: {index}")
        observed[index] = match.group(2)
    require(list(sorted(observed)) == list(range(len(literals))),
            "OCaml oracle output index set mismatch")
    return [observed[index] for index in range(len(literals))]


def strtod_words(literals: list[str]) -> tuple[list[str], list[str]]:
    """Return host-strtod words and literals for which libc sets ERANGE."""
    try:
        locale.setlocale(locale.LC_NUMERIC, "C")
    except locale.Error as error:
        raise CorpusError("cannot select C numeric locale") from error
    libc = ctypes.CDLL(None, use_errno=True)
    libc.strtod.argtypes = [ctypes.c_char_p, ctypes.POINTER(ctypes.c_char_p)]
    libc.strtod.restype = ctypes.c_double
    words = []
    erange_literals = []
    for literal in literals:
        encoded = literal.replace("_", "").encode("ascii")
        remainder = ctypes.c_char_p()
        ctypes.set_errno(0)
        value = libc.strtod(encoded, ctypes.byref(remainder))
        observed_errno = ctypes.get_errno()
        require(remainder.value in (None, b""),
                f"strtod left trailing input: {literal}")
        if observed_errno == errno.ERANGE:
            erange_literals.append(literal)
        else:
            require(observed_errno == 0,
                    f"strtod errno {observed_errno}: {literal}")
        words.append(str(struct.unpack("=Q", struct.pack("=d", value))[0]))
    return words, erange_literals


def make_artifact(
    manifest: dict[str, Any],
    scan: dict[str, Any],
    ocamlc: str,
) -> dict[str, Any]:
    words = ocaml_words(scan["unique"], ocamlc)
    host_words, erange_literals = strtod_words(scan["unique"])
    require(not erange_literals,
            "pinned corpus contains a host-strtod ERANGE literal")
    mismatches = [literal for literal, ocaml, host in zip(
        scan["unique"], words, host_words
    ) if ocaml != host]
    require(not mismatches,
            "OCaml 4.14.1 and host strtod bit mismatch: " +
            ", ".join(mismatches[:5]))
    spellings = []
    for literal, word in zip(scan["unique"], words):
        spellings.append({
            "literal": literal,
            "occurrence_count": scan["literals"][literal],
            "source_count": len(scan["source_sets"][literal]),
            "sources": sorted(scan["source_sets"][literal]),
            "ocaml_word64_decimal": word,
        })
    return {
        "schema_version": SCHEMA_VERSION,
        "ledger_id": LEDGER_ID,
        "claim": (
            "authenticated static direct-corpus inventory and OCaml 4.14.1 "
            "reference observations; not compiled Candle, theorem, S2, or S3 "
            "execution evidence"
        ),
        "provenance": {
            "candle_base_commit": EXPECTED_CANDLE_BASE,
            "manifest_sha256": EXPECTED_MANIFEST_SHA256,
            "flyspeck_commit": EXPECTED_FLYSPECK_COMMIT,
            "source_node_count": len(manifest["source_nodes"]),
            "normalization_contract_sha256":
                EXPECTED_NORMALIZATION_CONTRACT_SHA256,
            "normalization_receipt_sha256":
                EXPECTED_NORMALIZATION_RECEIPT_SHA256,
            "normalized_file_count": EXPECTED_NORMALIZED_FILES,
        },
        "scanner": {
            "float_grammar": (
                "[0-9][0-9_]*(\".\"[0-9_]*)?"
                "([eE][+-]?[0-9_]+)? with point or exponent required"
            ),
            "excluded_contexts": ["nested comments", "strings",
                                  "HOL backtick quotations"],
            "invalid_suffix": "immediate ASCII alphabetic character or _",
            "site_record_schema": ["source", "line", "column", "literal",
                                   "earliest_stratum"],
        },
        "inventory": {
            "occurrence_count": len(scan["sites"]),
            "unique_spelling_count": len(scan["unique"]),
            "source_file_count": len(scan["files"]),
            "site_record_sha256": canonical_sha256(scan["sites"]),
            "unique_spelling_sha256": canonical_sha256(scan["unique"]),
            "raw_context_counts": scan["raw_context_counts"],
            "invalid_suffix_context_counts":
                scan["invalid_suffix_context_counts"],
            "hex_float_context_counts": scan["hex_context_counts"],
            "form_occurrence_counts": scan["form_occurrence_counts"],
            "form_unique_counts": scan["form_unique_counts"],
            "earliest_stratum_counts": scan["earliest_stratum_counts"],
            "files": scan["files"],
        },
        "reference": {
            "implementation": "OCaml",
            "version": EXPECTED_OCAML_VERSION,
            "observation": "Int64.bits_of_float as unsigned decimal Word64",
            "host_strtod_erange_count": len(erange_literals),
            "host_strtod_word_mismatch_count": len(mismatches),
            "assurance_limit": (
                "host strtod comparison exercises the Candle FFI primitive's "
                "conversion operation but is not linked compiled-Candle evidence"
            ),
        },
        "spellings": spellings,
    }


def validate_artifact_shape(payload: dict[str, Any]) -> None:
    require(payload.get("schema_version") == SCHEMA_VERSION,
            "unsupported float-corpus artifact schema")
    require(payload.get("ledger_id") == LEDGER_ID,
            "wrong float-corpus ledger id")
    require("not compiled Candle" in payload.get("claim", ""),
            "float-corpus claim boundary drift")
    inventory = payload.get("inventory")
    require(isinstance(inventory, dict), "missing float-corpus inventory")
    require(inventory.get("occurrence_count") == EXPECTED_CODE_OCCURRENCES,
            "artifact occurrence count mismatch")
    require(inventory.get("unique_spelling_count") ==
            EXPECTED_UNIQUE_SPELLINGS,
            "artifact unique-spelling count mismatch")
    require(inventory.get("source_file_count") == EXPECTED_FLOAT_FILES,
            "artifact source-file count mismatch")
    require(inventory.get("unique_spelling_sha256") ==
            EXPECTED_UNIQUE_SPELLING_SHA256,
            "artifact unique-spelling digest mismatch")
    spellings = payload.get("spellings")
    require(isinstance(spellings, list) and
            len(spellings) == EXPECTED_UNIQUE_SPELLINGS,
            "artifact spelling table mismatch")
    literals = [record.get("literal") for record in spellings]
    require(literals == sorted(set(literals)),
            "artifact spelling table is not sorted and unique")
    require(canonical_sha256(literals) == EXPECTED_UNIQUE_SPELLING_SHA256,
            "artifact spelling table digest mismatch")
    require(sum(record.get("occurrence_count", 0) for record in spellings) ==
            EXPECTED_CODE_OCCURRENCES,
            "artifact spelling occurrence sum mismatch")
    for record in spellings:
        require(re.fullmatch(r"[0-9]+", record.get(
            "ocaml_word64_decimal", "")) is not None,
            f"malformed OCaml word: {record.get('literal')}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candle-root", required=True, type=Path)
    parser.add_argument("--flyspeck-root", required=True, type=Path)
    parser.add_argument("--overlay-root", required=True, type=Path)
    parser.add_argument("--ocamlc", default="/usr/bin/ocamlc")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    parser.add_argument("--artifact", type=Path)
    arguments = parser.parse_args()

    candle_root = arguments.candle_root.resolve()
    artifact_path = (arguments.artifact.resolve() if arguments.artifact else
                     candle_root / ARTIFACT_RELATIVE)
    manifest, runtime_sources = validate_inputs(
        candle_root, arguments.flyspeck_root, arguments.overlay_root
    )
    scan = scan_corpus(manifest, runtime_sources)
    generated = make_artifact(manifest, scan, arguments.ocamlc)
    validate_artifact_shape(generated)
    rendered = json_bytes(generated)
    if arguments.write:
        artifact_path.write_bytes(rendered)
        print(f"wrote {artifact_path}")
    else:
        require(artifact_path.is_file() and not artifact_path.is_symlink(),
                f"missing ordinary float-corpus artifact: {artifact_path}")
        require(artifact_path.read_bytes() == rendered,
                "float-corpus artifact differs from authenticated regeneration")
        print(
            "Flyspeck decimal-float corpus PASS: "
            f"{len(scan['sites'])} occurrences, {len(scan['unique'])} exact "
            f"spellings, OCaml {EXPECTED_OCAML_VERSION} and host strtod "
            "bit-identical without ERANGE"
        )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except CorpusError as error:
        raise SystemExit(f"float corpus gate failed: {error}") from error
