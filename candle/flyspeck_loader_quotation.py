#!/usr/bin/env python3
"""Model Candle's loader-side HOL quotation expansion for parser diagnostics.

The dedicated ``caml_parser$run`` entry point accepts parser input, whereas
ordinary Candle source loading first tokenizes a source phrase and expands
backtick quotations through ``Cakeml.unquote``.  A corpus parser diagnostic
must therefore submit the post-expansion bytes, not raw HOL Light source.

This module implements only that lexical transformation.  It does not load a
source, split phrases, infer, evaluate, or invoke a parser.
"""

from __future__ import annotations

import hashlib
from collections import Counter
from typing import Any


PINNED_CAKEML_COMMIT = "8a8926906ec97204eeec961496d191103cda3229"
CANDLE_BOOT_RELATIVE = "candle/prover/candle_boot.ml"
CANDLE_BOOT_SHA256 = (
    "2ddb376fd956a5eccccf8912ef5d8a452244c1ac69bb0f01718e53497916c763"
)
SYSTEM_RELATIVE = "system.ml"
SYSTEM_SHA256 = (
    "d1466e572b93a9d8fcb3cc906c079ca3efb23775c1b4143c341862d03dc3e882"
)
TRANSFORMATION_ID = "candle-loader-hol-quotation-expansion-v1"


class QuotationError(ValueError):
    """The source is outside the closed loader-quotation model."""


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _escape_string(data: bytes) -> bytes:
    """Exact byte analogue of ``candle_boot.ml``'s ``string_escaped``."""
    output = bytearray()
    for byte in data:
        if byte == 0x5C:
            output.extend(b"\\\\")
        elif byte == 0x08:
            output.extend(b"\\b")
        elif byte == 0x09:
            output.extend(b"\\t")
        elif byte == 0x0A:
            output.extend(b"\\n")
        elif byte == 0x22:
            output.extend(b'\\"')
        else:
            output.append(byte)
    return bytes(output)


def expand_body(body: bytes) -> tuple[bytes, str]:
    """Apply the exact ``system.ml`` ``quotexpander`` cases to one body."""
    if not body:
        raise QuotationError("empty HOL quotation")
    if body.startswith(b":"):
        return b'parse_type "' + _escape_string(body[1:]) + b'"', "type"
    if body.startswith(b";"):
        return b'parse_qproof "' + _escape_string(body) + b'"', "qproof"
    if body.endswith(b":"):
        return b'"' + _escape_string(body[:-1]) + b'"', "string"
    return b'parse_term "' + _escape_string(body) + b'"', "term"


def _skip_comment(source: bytes, index: int) -> int:
    start = index
    index += 2
    depth = 1
    while index < len(source):
        if source[index:index + 2] == b"(*":
            depth += 1
            index += 2
        elif source[index:index + 2] == b"*)":
            depth -= 1
            index += 2
            if depth == 0:
                return index
        else:
            index += 1
    raise QuotationError(f"unterminated OCaml comment at byte {start}")


def _skip_escaped(source: bytes, index: int, delimiter: int, label: str) -> int:
    start = index - 1
    while index < len(source):
        byte = source[index]
        index += 1
        if byte == 0x5C:
            if index < len(source):
                index += 1
        elif byte == delimiter:
            return index
    raise QuotationError(f"unterminated {label} at byte {start}")


def _is_name_byte(byte: int) -> bool:
    return (
        0x41 <= byte <= 0x5A or 0x61 <= byte <= 0x7A
        or 0x30 <= byte <= 0x39 or byte in (0x5F, 0x27)
    )


def _skip_char_or_type_variable(source: bytes, index: int) -> int:
    """Mirror the quote-relevant cases of ``scan_charlit_or_tyvar``."""
    index += 1
    if index >= len(source):
        return index
    byte = source[index]
    if byte == 0x5C:
        return _skip_escaped(source, index + 1, 0x27, "character literal")
    if byte in (0x20, 0x09, 0x0A, 0x0D):
        return index
    index += 1
    if index < len(source) and source[index] == 0x27:
        return index + 1
    while index < len(source) and _is_name_byte(source[index]):
        index += 1
    return index


def expand_source(source: bytes) -> tuple[bytes, dict[str, Any]]:
    """Expand every loader-visible quotation and return exact audit metadata."""
    output = bytearray()
    index = 0
    copied_from = 0
    kind_counts: Counter[str] = Counter()
    while index < len(source):
        if source[index:index + 2] == b"(*":
            index = _skip_comment(source, index)
            continue
        byte = source[index]
        if byte == 0x22:
            index = _skip_escaped(source, index + 1, 0x22, "OCaml string")
            continue
        if byte == 0x27:
            index = _skip_char_or_type_variable(source, index)
            continue
        if byte != 0x60:
            index += 1
            continue

        closing = source.find(b"`", index + 1)
        if closing < 0:
            raise QuotationError(f"unterminated HOL quotation at byte {index}")
        body = source[index + 1:closing]
        expanded, kind = expand_body(body)
        output.extend(source[copied_from:index])
        output.extend(b"(" + expanded + b")")
        copied_from = closing + 1
        index = closing + 1
        kind_counts[kind] += 1
    output.extend(source[copied_from:])
    expanded_source = bytes(output)
    counts = {
        kind: kind_counts.get(kind, 0)
        for kind in ("term", "type", "qproof", "string")
    }
    return expanded_source, {
        "transformation": TRANSFORMATION_ID,
        "input_bytes": len(source),
        "input_sha256": _sha256(source),
        "output_bytes": len(expanded_source),
        "output_sha256": _sha256(expanded_source),
        "quotation_count": sum(counts.values()),
        "kind_counts": counts,
    }


def contract() -> dict[str, Any]:
    """Return immutable source anchors for the modeled runtime operation."""
    return {
        "schema": 1,
        "kind": "candle-loader-hol-quotation-preparation-contract",
        "transformation": TRANSFORMATION_ID,
        "claim": (
            "host-side exact-byte model of loader-visible T_quote expansion; "
            "no loading, phrase splitting, parsing, inference, or evaluation"
        ),
        "cakeml_loader": {
            "commit": PINNED_CAKEML_COMMIT,
            "path": CANDLE_BOOT_RELATIVE,
            "sha256": CANDLE_BOOT_SHA256,
            "functions": ["Lexer.scan", "Lexer.string_of_token", "Cakeml.unquote"],
        },
        "candle_quotexpander": {
            "path": SYSTEM_RELATIVE,
            "sha256": SYSTEM_SHA256,
            "function": "quotexpander",
        },
        "replacement": "T_quote body becomes (quotexpander body)",
        "empty_quotation": "fail-closed",
    }
