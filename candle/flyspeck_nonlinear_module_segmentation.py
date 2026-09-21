#!/usr/bin/env python3
"""Segment the large Taylor module into bounded, interface-preserving phrases.

The original generated source places 3,693 lines in one OCaml module phrase.
Candle's verified frontend accepts that phrase, but its parser cost is too high
for practical nonlinear-verifier development.  This DEVELOPMENT / NON-RELEASE
normalization turns the body into a chain of modules.  Every later chunk opens
the original dependency namespaces and includes the preceding chunk; the
public ``Taylor_interval`` module includes the final chunk.

No HOL term, tactic, theorem value, or public Taylor module member is changed.
The extra print expressions are discarded progress observations only.
"""

from __future__ import annotations

import hashlib
from typing import Any


SOURCE_KEY = (
    "flyspeck:formal_ineqs/taylor/theory/taylor_interval-compiled.hl"
)
INPUT_SHA256 = (
    "998d6e16c3cff9dfeee58de64525d3c549c12b09b6836c656b974a6cd17af624"
)
NORMALIZATION_ID = "candle-nonlinear-taylor-module-segmentation-v1"
MARKER_PREFIX = "CANDLE_NONLINEAR_TAYLOR_SEGMENT"
MODULE_PREFIX = "Candle_taylor_interval_chunk_"

MODULE_ANCHOR = b"(* Module Taylor_interval*)\nmodule Taylor_interval = struct\n"
CLOSE_ANCHOR = b"(* Close the module *)\nend;;\n"
DEPENDENCY_OPENS = (
    b"open Ssreflect;;\n"
    b"open Ssrfun;;\n"
    b"open Ssrbool;;\n"
    b"open Ssrnat;;\n"
    b"open Interval_arith;;\n"
    b"open Matan;;\n"
)

# These are exact top-level structure-item boundaries in the authenticated
# generated module.  The first, second, third, fifth, and sixth anchors remain
# at the end of their preceding chunks.  The fourth begins the next chunk so
# its descriptive comment stays adjacent to the section it names.
SPLIT_ANCHORS = (
    (b'Sections.end_section "MoreDerivativeArith";;\n', "after"),
    (b'Sections.end_section "NthDerivatives";;\n', "after"),
    (b'Sections.end_section "MoreLinearApproximation";;\n', "after"),
    (b"(* Section SecondDerivativeCompose *)\n", "before"),
    (b'Sections.end_section "SecondDerivativeCompose";;\n', "after"),
    (b'Sections.end_section "SecondDerivativeBound";;\n', "after"),
)


def _identity(data: bytes) -> dict[str, Any]:
    return {
        "bytes": len(data),
        "md5": hashlib.md5(data, usedforsecurity=False).hexdigest(),
        "sha256": hashlib.sha256(data).hexdigest(),
    }


def _split_body(body: bytes) -> list[bytes]:
    chunks: list[bytes] = []
    offset = 0
    for anchor, side in SPLIT_ANCHORS:
        if body.count(anchor) != 1:
            raise ValueError(
                "Taylor module segmentation anchor is absent or duplicated"
            )
        position = body.index(anchor)
        boundary = position + (len(anchor) if side == "after" else 0)
        if boundary <= offset:
            raise ValueError("Taylor module segmentation anchors are out of order")
        chunks.append(body[offset:boundary])
        offset = boundary
    chunks.append(body[offset:])
    if any(not chunk.strip() for chunk in chunks):
        raise ValueError("Taylor module segmentation produced an empty chunk")
    if b"".join(chunks) != body:
        raise ValueError("Taylor module segmentation body reconstruction failed")
    return chunks


def _marker(index: int, event: str) -> bytes:
    return (
        f'let _ = print_endline "{MARKER_PREFIX} index={index} event={event}";;\n'
    ).encode("ascii")


def _module_name(index: int) -> str:
    return f"{MODULE_PREFIX}{index:03d}"


def _render_chunk(index: int, chunk: bytes) -> bytes:
    name = _module_name(index)
    header = _marker(index, "begin") + f"module {name} = struct\n".encode("ascii")
    if index:
        previous = _module_name(index - 1)
        header += DEPENDENCY_OPENS + f"include {previous};;\n".encode("ascii")
    return header + chunk + b"\nend;;\n" + _marker(index, "end")


def segment_records(records: list[dict[str, Any]]) -> dict[str, Any]:
    """Segment the one exact Taylor source and update its closure identity."""

    matches = [record for record in records if record["source_key"] == SOURCE_KEY]
    if len(matches) != 1:
        raise ValueError("Taylor module segmentation source is absent or duplicated")
    record = matches[0]
    data = record["normalized_bytes"]
    if hashlib.sha256(data).hexdigest() != INPUT_SHA256:
        raise ValueError("Taylor module segmentation source identity drift")
    if data.count(MODULE_ANCHOR) != 1 or data.count(CLOSE_ANCHOR) != 1:
        raise ValueError("Taylor module segmentation outer anchor drift")
    prefix, remainder = data.split(MODULE_ANCHOR, 1)
    body, suffix = remainder.split(CLOSE_ANCHOR, 1)
    if suffix:
        raise ValueError("Taylor module segmentation unexpected trailing bytes")
    if MODULE_PREFIX.encode("ascii") in body:
        raise ValueError("Taylor module segmentation internal name collision")

    chunks = _split_body(body)
    rendered = b"".join(
        _render_chunk(index, chunk) for index, chunk in enumerate(chunks)
    )
    final_name = _module_name(len(chunks) - 1)
    public_wrapper = (
        b"(* Public interface preserved from the authenticated source. *)\n"
        b"module Taylor_interval = struct\n"
        + f"include {final_name};;\n".encode("ascii")
        + b"end;;\n"
    )
    segmented = prefix + rendered + public_wrapper
    identity = _identity(segmented)
    chunk_records = [
        {
            "index": index,
            "module": _module_name(index),
            **_identity(chunk),
        }
        for index, chunk in enumerate(chunks)
    ]

    prior = record["normalization"]
    record["normalized_bytes"] = segmented
    record["normalization"] = {
        "authority": "development-only-nonlinear-module-segmentation",
        "id": NORMALIZATION_ID,
        "semantic_rule": (
            "partition the exact authenticated Taylor module body only at fixed "
            "top-level structure-item boundaries; every later internal module "
            "reopens the original dependencies and includes its exact predecessor; "
            "the public Taylor_interval module includes the final chunk"
        ),
        "input_normalization": prior,
        "chunk_count": len(chunks),
        "normalized_bytes": identity["bytes"],
        "normalized_md5": identity["md5"],
        "normalized_sha256": identity["sha256"],
    }
    return {
        "normalization_id": NORMALIZATION_ID,
        "source_key": SOURCE_KEY,
        "input_sha256": INPUT_SHA256,
        "marker_prefix": MARKER_PREFIX,
        "chunk_count": len(chunks),
        "chunks": chunk_records,
        "marker_count": 2 * len(chunks),
        "public_module": "Taylor_interval",
        "public_include": final_name,
        "normalized_bytes": identity["bytes"],
        "normalized_md5": identity["md5"],
        "normalized_sha256": identity["sha256"],
    }
