#!/usr/bin/env python3
"""Derive the exact all-inventory parser inputs without running a parser.

This module is deliberately source-only.  It authenticates the committed
all-inventory descriptor, manifest, normalization contract, and source bytes;
applies only the hash-bound normalizations; independently rediscovers loader
syntax; and masks complete standalone loader lines.  It does not materialize
files, invoke a runtime, parse OCaml, or provide promotable evidence.
"""

from __future__ import annotations

import hashlib
import json
import re
import stat
from collections import Counter
from pathlib import Path
from typing import Any

import flyspeck_normalize


DESCRIPTOR_RELATIVE = Path("candle/flyspeck_parser_diagnostic_all_inventory.json")
MANIFEST_RELATIVE = Path("candle/flyspeck_manifest.json")
NORMALIZATION_RELATIVE = Path("candle/flyspeck_normalizations.json")

EXPECTED_AUTHORITIES = {
    DESCRIPTOR_RELATIVE.as_posix(): {
        "bytes": 206558,
        "sha256": "f407e98f5cdcab161c49fbc50c0a655a32806e6b90d8522ecd39363fe799e9a6",
    },
    MANIFEST_RELATIVE.as_posix(): {
        "bytes": 820818,
        "sha256": "0e2798eb9b643c0d602768de0a2c159f482904d1fe2acbdca9acd3d0ceb8bb70",
    },
    NORMALIZATION_RELATIVE.as_posix(): {
        "bytes": 48256,
        "sha256": "491ca5a204e15fde5454faf63a42343f5cf4a281e03b8b212c937013b992de7e",
    },
}
EXPECTED_SOURCE_COUNT = 400
EXPECTED_ORIGINAL_COUNT = 382
EXPECTED_NORMALIZED_COUNT = 18
EXPECTED_ACTION_COUNT = 727
EXPECTED_MASKED_COUNT = 721
EXPECTED_EMBEDDED_COUNT = 6
EXPECTED_NON_UTF8_KEYS = (
    "flyspeck:text_formalization/leg/collect_geom.hl",
)
EXPECTED_ACTION_KIND_COUNTS = {
    "#flyspeck_loadt": 4,
    "#flyspeck_needs": 297,
    "#load": 5,
    "#use": 1,
    "flyspeck_needs": 147,
    "loads": 54,
    "loadt": 1,
    "needs": 217,
    "reneeds": 1,
}
EXPECTED_ACTION_SITE_SHA256 = (
    "7334dba65e01244e1568a223f804aed1a7d4dd04d75275b88f15d1fa73b5c894"
)
EXPECTED_ORDERED_PATH_SHA256 = (
    "019b8eef7c4792314e7cbc9239d142c0e3252692426727a5589bd6e8103115fd"
)
EXPECTED_ORDERED_EFFECTIVE_SHA256 = (
    "cc94f3aa549b131c34e1d9561ad1972615ec96f17eb9cf64669719b133428555"
)
EXPECTED_ORDERED_PREPARED_SHA256 = (
    "f7a8827ff3c8b8185e99c46cc5606a4666d862d61c98d8b36bb02c6a86931acd"
)
CLAIM = (
    "source-only all-400 effective-input preparation; categorically "
    "non-promotable and not a parser run, runtime execution, inference, "
    "theorem, S1, S2, S3, or release evidence"
)

LOAD_NAMES = (
    "needs", "loads", "loadt", "flyspeck_needs", "rflyspeck_needs",
    "reneeds",
)
LOAD_RE = re.compile(r"\b(" + "|".join(LOAD_NAMES) + r")\b")
DIRECTIVE_RE = re.compile(r"#\s*(flyspeck_loadt|flyspeck_needs|use|load)\b")
DEFINITION_PREFIX_RE = re.compile(r"(?:\blet|\band)\s+(?:rec\s+)?$")
HEX32 = re.compile(r"^[0-9a-f]{32}$")
HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")


class ContractError(ValueError):
    """An authenticated source-preparation invariant did not match."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ContractError(message)


def _is_int(value: Any) -> bool:
    return type(value) is int


def _pairs_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ContractError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def decode_object(data: bytes, label: str) -> dict[str, Any]:
    try:
        value = json.loads(
            data.decode("utf-8"), object_pairs_hook=_pairs_object,
            parse_constant=lambda token: (_ for _ in ()).throw(
                ContractError(f"invalid JSON constant in {label}: {token}")
            ),
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ContractError(f"cannot decode {label}: {error}") from error
    require(isinstance(value, dict), f"{label} is not an object")
    return value


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def _md5(data: bytes) -> str:
    return hashlib.md5(data, usedforsecurity=False).hexdigest()


def bytes_record(data: bytes, path: str | None = None) -> dict[str, Any]:
    record: dict[str, Any] = {
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }
    if path is not None:
        record["path"] = path
    return record


def _authority(data: bytes, relative: Path) -> dict[str, Any]:
    record = bytes_record(data, relative.as_posix())
    require(
        {key: record[key] for key in ("bytes", "sha256")}
        == EXPECTED_AUTHORITIES[relative.as_posix()],
        f"committed authority drift: {relative.as_posix()}",
    )
    return record


def _safe_relative(value: Any, label: str) -> Path:
    require(isinstance(value, str) and value, f"invalid {label}")
    relative = Path(value)
    require(
        not relative.is_absolute()
        and ".." not in relative.parts
        and relative.as_posix() == value,
        f"unsafe {label}: {value}",
    )
    return relative


def _identity(record: dict[str, Any], label: str) -> None:
    require(_is_int(record.get("bytes")) and record["bytes"] >= 0,
            f"invalid byte count: {label}")
    require(isinstance(record.get("md5"), str) and HEX32.fullmatch(record["md5"]),
            f"invalid MD5: {label}")
    require(isinstance(record.get("sha256"), str) and HEX64.fullmatch(record["sha256"]),
            f"invalid SHA-256: {label}")


def _validate_descriptor(
    descriptor: dict[str, Any], manifest: dict[str, Any], manifest_data: bytes,
) -> list[dict[str, Any]]:
    require(descriptor.get("schema") == 1, "unsupported all-inventory schema")
    require(
        descriptor.get("kind") == "candle-flyspeck-parser-diagnostic-all-inventory",
        "all-inventory kind drift",
    )
    require(
        descriptor.get("manifest")
        == bytes_record(manifest_data, MANIFEST_RELATIVE.as_posix()),
        "descriptor/manifest identity drift",
    )
    nodes = manifest.get("source_nodes")
    require(isinstance(nodes, dict), "manifest source_nodes is not an object")
    require(
        _is_int(manifest.get("source_node_count"))
        and manifest["source_node_count"] == len(nodes) == EXPECTED_SOURCE_COUNT,
        "manifest source count/type drift",
    )
    inputs = descriptor.get("inputs")
    require(
        isinstance(inputs, list) and len(inputs) == EXPECTED_SOURCE_COUNT,
        "descriptor source count/type drift",
    )
    selection = descriptor.get("selection")
    require(isinstance(selection, dict), "descriptor selection is not an object")
    for field, expected in (
        ("inventory_source_count", 400),
        ("discovered_source_count", 392),
        ("explicit_remainder_source_count", 8),
        ("manifest_source_count", 400),
    ):
        require(
            _is_int(selection.get(field)) and selection[field] == expected,
            f"descriptor selection count/type drift: {field}",
        )
    keys: list[str] = []
    for index, entry in enumerate(inputs):
        require(isinstance(entry, dict), f"descriptor input is not an object: {index}")
        require(
            set(entry) == {
                "index", "source_key", "repository", "path", "bytes", "md5",
                "sha256", "discovery",
            },
            f"descriptor input shape drift: {index}",
        )
        require(_is_int(entry.get("index")) and entry["index"] == index,
                f"descriptor index/type/order drift: {index}")
        key = entry.get("source_key")
        require(isinstance(key, str) and key in nodes,
                f"unknown descriptor source: {key}")
        require(key not in keys, f"duplicate descriptor source: {key}")
        node = nodes[key]
        require(isinstance(node, dict), f"manifest node is not an object: {key}")
        for field in ("repository", "path", "bytes", "md5", "sha256"):
            require(entry.get(field) == node.get(field),
                    f"descriptor/node identity drift: {key}:{field}")
        require(entry["repository"] in {"candle", "flyspeck"},
                f"unknown source repository: {key}")
        _safe_relative(entry["path"], f"source path for {key}")
        _identity(entry, f"descriptor input {key}")
        require(isinstance(entry["discovery"], dict),
                f"descriptor discovery is not an object: {key}")
        keys.append(key)
    require(set(keys) == set(nodes), "descriptor is not an exact manifest partition")
    key_digest = canonical_sha256(keys)
    require(selection.get("ordered_source_key_sha256") == key_digest,
            "descriptor ordered source-key digest drift")
    return inputs


def _normalizations(
    manifest: dict[str, Any], contract_data: bytes,
) -> tuple[dict[str, Any], dict[str, dict[str, Any]]]:
    try:
        contract = flyspeck_normalize.load_contract_bytes(contract_data)
    except (KeyError, TypeError, ValueError) as error:
        raise ContractError(f"invalid normalization contract: {error}") from error
    require(
        isinstance(contract.get("flyspeck_commit"), str)
        and HEX40.fullmatch(contract["flyspeck_commit"]),
        "normalization Flyspeck commit drift",
    )
    repositories = manifest.get("repositories")
    require(isinstance(repositories, dict), "manifest repositories is not an object")
    flyspeck = repositories.get("flyspeck")
    require(
        isinstance(flyspeck, dict)
        and flyspeck.get("commit") == contract["flyspeck_commit"],
        "manifest/normalization Flyspeck commit drift",
    )
    manifest_contract = manifest.get("source_normalization_contract")
    require(isinstance(manifest_contract, dict),
            "manifest normalization contract is not an object")
    require(
        manifest_contract.get("contract_source")
        == f"candle:{NORMALIZATION_RELATIVE.as_posix()}",
        "manifest normalization contract path drift",
    )
    require(
        manifest_contract.get("contract_sha256")
        == hashlib.sha256(contract_data).hexdigest(),
        "manifest normalization contract digest drift",
    )
    entries = contract.get("entries")
    require(
        isinstance(entries, list)
        and _is_int(manifest_contract.get("entry_count"))
        and manifest_contract["entry_count"] == len(entries) == EXPECTED_NORMALIZED_COUNT,
        "normalization entry count/type drift",
    )
    by_key: dict[str, dict[str, Any]] = {}
    for entry in entries:
        key = entry.get("source_key")
        require(isinstance(key, str) and key not in by_key,
                f"duplicate normalization source: {key}")
        by_key[key] = entry
    nodes = manifest["source_nodes"]
    normalized_nodes = {
        key for key, node in nodes.items() if "execution_normalization" in node
    }
    require(set(by_key) == normalized_nodes,
            "normalization/manifest source partition drift")
    return contract, by_key


def strip_ocaml_comments(source: str) -> str:
    """Manifest-scanner-compatible nested-comment masking."""
    result = list(source)
    index = 0
    depth = 0
    in_string = False
    in_quote = False
    escaped = False
    while index < len(source):
        if depth:
            if source.startswith("(*", index):
                result[index] = result[index + 1] = " "
                depth += 1
                index += 2
            elif source.startswith("*)", index):
                result[index] = result[index + 1] = " "
                depth -= 1
                index += 2
            else:
                if source[index] != "\n":
                    result[index] = " "
                index += 1
        elif in_string:
            if escaped:
                escaped = False
            elif source[index] == "\\":
                escaped = True
            elif source[index] == '"':
                in_string = False
            index += 1
        elif in_quote:
            if source[index] == "`":
                in_quote = False
            index += 1
        elif source.startswith("(*", index):
            result[index] = result[index + 1] = " "
            depth = 1
            index += 2
        else:
            if source[index] == '"':
                in_string = True
            elif source[index] == "`":
                in_quote = True
            index += 1
    if depth:
        raise ContractError("unterminated OCaml comment")
    if in_string:
        raise ContractError("unterminated OCaml string")
    if in_quote:
        raise ContractError("unterminated HOL quotation")
    return "".join(result)


def _string_at(source: str, index: int) -> tuple[str, int] | None:
    if index >= len(source) or source[index] != '"':
        return None
    index += 1
    value: list[str] = []
    while index < len(source):
        char = source[index]
        if char == '"':
            return "".join(value), index + 1
        if char != "\\":
            value.append(char)
            index += 1
            continue
        index += 1
        if index >= len(source):
            raise ContractError("unterminated string escape")
        escaped = source[index]
        replacements = {"n": "\n", "r": "\r", "t": "\t", "\\": "\\", '"': '"'}
        if escaped in replacements:
            value.append(replacements[escaped])
            index += 1
        elif (
            escaped.isdigit() and index + 2 < len(source)
            and source[index:index + 3].isdigit()
        ):
            value.append(chr(int(source[index:index + 3], 10)))
            index += 3
        else:
            value.append(escaped)
            index += 1
    raise ContractError("unterminated OCaml string")


def _skip_space(source: str, index: int) -> int:
    while index < len(source) and source[index].isspace():
        index += 1
    return index


def _code_mask(source: str) -> str:
    result = list(source)
    in_string = False
    in_quote = False
    escaped = False
    for index, char in enumerate(source):
        if in_string:
            if char != "\n":
                result[index] = " "
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
        elif in_quote:
            if char != "\n":
                result[index] = " "
            if char == "`":
                in_quote = False
        elif char == '"':
            result[index] = " "
            in_string = True
        elif char == "`":
            result[index] = " "
            in_quote = True
    return "".join(result)


def _call_argument(clean: str, index: int) -> tuple[str | None, int]:
    index = _skip_space(clean, index)
    parentheses = 0
    while index < len(clean) and clean[index] == "(":
        parentheses += 1
        index = _skip_space(clean, index + 1)
    parsed = _string_at(clean, index)
    if parsed is None:
        return None, index
    value, end = parsed
    end = _skip_space(clean, end)
    for _ in range(parentheses):
        if end >= len(clean) or clean[end] != ")":
            return None, index
        end = _skip_space(clean, end + 1)
    return value, end


def scan_load_calls(source: bytes) -> list[dict[str, Any]]:
    """Scan one-byte source text without requiring or losing UTF-8 bytes."""
    text = source.decode("latin-1")
    require(text.encode("latin-1") == source, "Latin-1 scan did not round-trip bytes")
    clean = strip_ocaml_comments(text)
    mask = _code_mask(clean)
    directive_matches = list(DIRECTIVE_RE.finditer(mask))
    matches: list[tuple[re.Match[str], str]] = [
        (match, match.group(1)) for match in LOAD_RE.finditer(mask)
        if not any(
            directive.start() <= match.start() < directive.end()
            for directive in directive_matches
        )
    ]
    matches.extend((match, f"#{match.group(1)}") for match in directive_matches)
    calls: list[dict[str, Any]] = []
    for match, kind in sorted(matches, key=lambda item: item[0].start()):
        prefix = clean[max(0, match.start() - 24):match.start()]
        if DEFINITION_PREFIX_RE.search(prefix):
            continue
        previous_phrase_end = mask.rfind(";;", 0, match.start())
        phrase_prefix = mask[previous_phrase_end + 2:match.start()]
        position = (
            "standalone-phrase" if phrase_prefix.strip() == ""
            else "embedded-expression"
        )
        literal, _end = _call_argument(clean, match.end())
        line = clean.count("\n", 0, match.start()) + 1
        if literal is not None:
            call = {
                "kind": kind, "line": line, "literal": literal,
                "syntax_position": position,
            }
        else:
            expression_end = clean.find(";;", match.end())
            if expression_end < 0:
                expression_end = clean.find("\n", match.end())
            if expression_end < 0:
                expression_end = min(len(clean), match.end() + 160)
            expression = " ".join(clean[match.start():expression_end].split())[:160]
            call = {
                "kind": kind, "line": line, "expression": expression,
                "syntax_position": position,
            }
        calls.append(call)
    return calls


def _lf_lines(data: bytes) -> list[bytes]:
    parts = data.split(b"\n")
    lines = [part + b"\n" for part in parts[:-1]]
    if parts[-1]:
        lines.append(parts[-1])
    return lines


def _mask_effective_source(
    source_key: str, effective: bytes, calls: list[dict[str, Any]],
) -> tuple[bytes, list[dict[str, Any]]]:
    lines = _lf_lines(effective)
    clean_bytes = strip_ocaml_comments(
        effective.decode("latin-1")
    ).encode("latin-1")
    clean_lines = _lf_lines(clean_bytes)
    require(len(clean_lines) == len(lines),
            f"comment masking changed line count: {source_key}")
    masked_lines: set[int] = set()
    embedded_lines: set[int] = set()
    actions: list[dict[str, Any]] = []
    for index, call in enumerate(calls):
        position = call["syntax_position"]
        record: dict[str, Any] = {
            "source_action_index": index,
            **call,
            "action_semantics_executed": False,
        }
        if position == "embedded-expression":
            embedded_lines.add(call["line"])
            record["handling"] = "retained-exactly-in-source-only-input"
            actions.append(record)
            continue
        require(position == "standalone-phrase",
                f"unknown loader syntax position: {source_key}")
        line_number = call.get("line")
        require(
            _is_int(line_number) and 1 <= line_number <= len(lines),
            f"loader line out of range: {source_key}",
        )
        require(line_number not in masked_lines,
                f"multiple standalone loader calls on one line: {source_key}:{line_number}")
        original = lines[line_number - 1]
        ending = b""
        content = original
        if content.endswith(b"\r\n"):
            content, ending = content[:-2], b"\r\n"
        elif content.endswith(b"\n"):
            content, ending = content[:-1], b"\n"
        stripped = content.lstrip(b" \t")
        token = call["kind"].encode("ascii")
        require(
            stripped.startswith(token)
            and len(stripped) > len(token)
            and stripped[len(token):len(token) + 1] in b" \t",
            f"loader token/line drift: {source_key}:{line_number}",
        )
        clean_line = clean_lines[line_number - 1].decode("latin-1")
        code_line = _code_mask(clean_line)
        phrase_end = code_line.find(";;")
        require(
            phrase_end >= 0 and code_line[phrase_end + 2:].strip() == "",
            f"loader is not the complete line phrase: {source_key}:{line_number}",
        )
        literal = call.get("literal")
        if isinstance(literal, str):
            encoded = json.dumps(literal, ensure_ascii=False).encode("latin-1")
            require(encoded in stripped,
                    f"loader literal/line drift: {source_key}:{line_number}")
        masked = b" " * len(content) + ending
        require(len(masked) == len(original),
                f"masked loader line size drift: {source_key}:{line_number}")
        lines[line_number - 1] = masked
        masked_lines.add(line_number)
        record["handling"] = "masked-complete-whole-line-before-parser"
        record["original_line"] = bytes_record(original)
        record["masked_line"] = bytes_record(masked)
        actions.append(record)
    prepared = b"".join(lines)
    require(len(prepared) == len(effective), f"prepared size drift: {source_key}")
    require(not masked_lines.intersection(embedded_lines),
            f"masked line also contains an embedded loader call: {source_key}")
    expected_remaining = [
        call for call in calls if call["syntax_position"] == "embedded-expression"
    ]
    require(scan_load_calls(prepared) == expected_remaining,
            f"prepared loader rescan drift: {source_key}")
    return prepared, actions


def _validate_action_inventory(sites: list[dict[str, Any]]) -> None:
    require(len(sites) == EXPECTED_ACTION_COUNT, "effective loader action count drift")
    positions = Counter(site.get("syntax_position") for site in sites)
    require(
        positions == Counter({
            "standalone-phrase": EXPECTED_MASKED_COUNT,
            "embedded-expression": EXPECTED_EMBEDDED_COUNT,
        }),
        "effective loader syntax-position count drift",
    )
    kinds = Counter(site.get("kind") for site in sites)
    require(kinds == Counter(EXPECTED_ACTION_KIND_COUNTS),
            "effective loader kind count drift")
    require(canonical_sha256(sites) == EXPECTED_ACTION_SITE_SHA256,
            "effective loader action site/order drift")


def _read_source(path: Path, label: str) -> bytes:
    try:
        observed = path.lstat()
    except OSError as error:
        raise ContractError(f"cannot read {label}: {path}: {error}") from error
    require(stat.S_ISREG(observed.st_mode), f"source is not an ordinary file: {label}")
    return path.read_bytes()


def prepare_all_sources(
    candle_root: Path,
    flyspeck_root: Path,
    *,
    descriptor_data: bytes | None = None,
    manifest_data: bytes | None = None,
    normalization_data: bytes | None = None,
) -> tuple[dict[str, Any], dict[str, bytes]]:
    """Return an authenticated source-only plan and all 400 prepared bytes."""
    candle_root = Path(candle_root)
    flyspeck_root = Path(flyspeck_root)
    descriptor_data = (
        (candle_root / DESCRIPTOR_RELATIVE).read_bytes()
        if descriptor_data is None else descriptor_data
    )
    manifest_data = (
        (candle_root / MANIFEST_RELATIVE).read_bytes()
        if manifest_data is None else manifest_data
    )
    normalization_data = (
        (candle_root / NORMALIZATION_RELATIVE).read_bytes()
        if normalization_data is None else normalization_data
    )
    authorities = {
        "descriptor": _authority(descriptor_data, DESCRIPTOR_RELATIVE),
        "manifest": _authority(manifest_data, MANIFEST_RELATIVE),
        "normalization_contract": _authority(
            normalization_data, NORMALIZATION_RELATIVE,
        ),
    }
    descriptor = decode_object(descriptor_data, "all-inventory descriptor")
    manifest = decode_object(manifest_data, "Flyspeck manifest")
    inputs = _validate_descriptor(descriptor, manifest, manifest_data)
    contract, normalizations = _normalizations(manifest, normalization_data)

    files: dict[str, bytes] = {}
    records: list[dict[str, Any]] = []
    sites: list[dict[str, Any]] = []
    effective_hashes: list[str] = []
    prepared_hashes: list[str] = []
    prepared_paths: list[str] = []
    kind_counts: Counter[str] = Counter()
    non_utf8_keys: list[str] = []
    for index, selected in enumerate(inputs):
        key = selected["source_key"]
        node = manifest["source_nodes"][key]
        root = candle_root if node["repository"] == "candle" else flyspeck_root
        source_path = root / _safe_relative(node["path"], f"source path for {key}")
        source = _read_source(source_path, key)
        _identity(node, f"manifest node {key}")
        require(
            len(source) == node["bytes"]
            and _md5(source) == node["md5"]
            and hashlib.sha256(source).hexdigest() == node["sha256"],
            f"original source identity drift: {key}",
        )
        try:
            source.decode("utf-8")
            utf8_decodable = True
        except UnicodeDecodeError:
            utf8_decodable = False
            non_utf8_keys.append(key)

        normalization = normalizations.get(key)
        if normalization is None:
            effective = source
            effective_kind = "exact-original"
            normalization_record = None
        else:
            try:
                effective = flyspeck_normalize.normalize_bytes(source, normalization)
            except (KeyError, TypeError, ValueError) as error:
                raise ContractError(f"normalization failed for {key}: {error}") from error
            execution = node.get("execution_normalization")
            require(isinstance(execution, dict),
                    f"missing manifest execution normalization: {key}")
            expected_execution = {
                "id": normalization["id"],
                "kind": "exact_bytes_replace_sequence",
                "operation_count": len(normalization["operations"]),
                "normalized_bytes": normalization["normalized_bytes"],
                "normalized_md5": normalization["normalized_md5"],
                "normalized_sha256": normalization["normalized_sha256"],
            }
            require(execution == expected_execution,
                    f"manifest normalization identity drift: {key}")
            effective_kind = "exact-normalized"
            normalization_record = {
                **expected_execution,
                "contract_sha256": authorities["normalization_contract"]["sha256"],
                "source_sha256": normalization["source_sha256"],
                "source_md5": normalization["source_md5"],
            }
        calls = scan_load_calls(effective)
        prepared, actions = _mask_effective_source(key, effective, calls)
        relative = f"inputs/{index:03d}.ml"
        require(relative not in files, f"duplicate prepared path: {relative}")
        files[relative] = prepared
        effective_record = {
            "bytes": len(effective),
            "md5": _md5(effective),
            "sha256": hashlib.sha256(effective).hexdigest(),
        }
        prepared_record = bytes_record(prepared, relative)
        effective_hashes.append(effective_record["sha256"])
        prepared_hashes.append(prepared_record["sha256"])
        prepared_paths.append(relative)
        kind_counts[effective_kind] += 1
        source_sites = [
            {
                "input_index": index,
                "source_key": key,
                "source_action_index": action_index,
                **call,
            }
            for action_index, call in enumerate(calls)
        ]
        sites.extend(source_sites)
        records.append({
            "index": index,
            "source_key": key,
            "repository": node["repository"],
            "source": {
                "path": node["path"], "bytes": node["bytes"],
                "md5": node["md5"], "sha256": node["sha256"],
            },
            "effective_kind": effective_kind,
            "normalization": normalization_record,
            "effective_input": effective_record,
            "lexical_scan_encoding": "latin-1-one-byte-round-trip",
            "utf8_decodable": utf8_decodable,
            "recognized_loader_actions": actions,
            "recognized_loader_action_count": len(actions),
            "prepared_input": prepared_record,
            "parser_or_runtime_invoked": False,
        })

    require(kind_counts == Counter({
        "exact-original": EXPECTED_ORIGINAL_COUNT,
        "exact-normalized": EXPECTED_NORMALIZED_COUNT,
    }), "effective source kind count drift")
    require(tuple(non_utf8_keys) == EXPECTED_NON_UTF8_KEYS,
            "non-UTF8 source inclusion drift")
    require(len(files) == len(records) == EXPECTED_SOURCE_COUNT,
            "prepared source count drift")
    require(len(set(prepared_paths)) == EXPECTED_SOURCE_COUNT,
            "prepared paths are not unique")
    require(len(set(prepared_hashes)) == EXPECTED_SOURCE_COUNT,
            "prepared hashes are not unique")
    require(canonical_sha256(prepared_paths) == EXPECTED_ORDERED_PATH_SHA256,
            "ordered prepared path drift")
    require(canonical_sha256(effective_hashes) == EXPECTED_ORDERED_EFFECTIVE_SHA256,
            "ordered effective hash drift")
    require(canonical_sha256(prepared_hashes) == EXPECTED_ORDERED_PREPARED_SHA256,
            "ordered prepared hash drift")
    _validate_action_inventory(sites)

    plan = {
        "schema": 1,
        "kind": "candle-flyspeck-all-inventory-source-preparation",
        "claim": CLAIM,
        "promotion_allowed": False,
        "parser_run": False,
        "runtime_execution": False,
        "authorities": authorities,
        "flyspeck_commit": contract["flyspeck_commit"],
        "input_count": len(records),
        "effective_kind_counts": dict(sorted(kind_counts.items())),
        "non_utf8_source_keys": non_utf8_keys,
        "loader_actions": {
            "recognized_site_count": len(sites),
            "masked_whole_line_count": EXPECTED_MASKED_COUNT,
            "embedded_retained_count": EXPECTED_EMBEDDED_COUNT,
            "kind_counts": dict(sorted(Counter(site["kind"] for site in sites).items())),
            "ordered_site_sha256": canonical_sha256(sites),
            "semantics_executed": False,
        },
        "prepared_inputs": {
            "count": len(files),
            "paths_unique": True,
            "sha256_unique": True,
            "ordered_path_sha256": canonical_sha256(prepared_paths),
            "ordered_effective_sha256": canonical_sha256(effective_hashes),
            "ordered_prepared_sha256": canonical_sha256(prepared_hashes),
        },
        "inputs": records,
    }
    return plan, files
