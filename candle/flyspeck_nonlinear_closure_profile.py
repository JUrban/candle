#!/usr/bin/env python3
"""Authenticate and instrument the large Taylor closure for localization.

The markers are DEVELOPMENT / NON-RELEASE observations.  They discard unit,
do not construct a theorem, and leave the public module interface unchanged.
"""

from __future__ import annotations

import hashlib
import re
from typing import Any


SOURCE_KEY = (
    "flyspeck:formal_ineqs/taylor/theory/taylor_interval-compiled.hl"
)
INPUT_SHA256 = (
    "998d6e16c3cff9dfeee58de64525d3c549c12b09b6836c656b974a6cd17af624"
)
NORMALIZATION_ID = "candle-nonlinear-taylor-closure-profile-v1"
MARKER_PREFIX = "CANDLE_NONLINEAR_TAYLOR"
SECTION_RE = re.compile(
    rb'^Sections\.(begin_section|end_section) "([A-Za-z0-9_]+)";;$',
    flags=re.MULTILINE,
)


def _marker(text: str) -> bytes:
    return (
        f'let _ = print_endline "{MARKER_PREFIX} {text}";;\n'
    ).encode("ascii")


def instrument_records(records: list[dict[str, Any]]) -> dict[str, Any]:
    """Instrument the one exact Taylor source and update its identity."""

    matches = [record for record in records if record["source_key"] == SOURCE_KEY]
    if len(matches) != 1:
        raise ValueError("Taylor closure profile source is absent or duplicated")
    record = matches[0]
    data = record["normalized_bytes"]
    if hashlib.sha256(data).hexdigest() != INPUT_SHA256:
        raise ValueError("Taylor closure profile normalized source identity drift")

    module_anchor = b"(* Module Taylor_interval*)\nmodule Taylor_interval = struct\n"
    if data.count(module_anchor) != 1:
        raise ValueError("Taylor closure profile module anchor drift")
    data = data.replace(
        module_anchor,
        _marker("stage=module-frontend event=begin")
        + module_anchor
        + _marker("stage=module-execution event=begin"),
        1,
    )

    section_events: list[dict[str, str]] = []

    def instrument_section(match: re.Match[bytes]) -> bytes:
        operation = match.group(1).decode("ascii")
        section = match.group(2).decode("ascii")
        event = "begin" if operation == "begin_section" else "end"
        section_events.append({"section": section, "event": event})
        return (
            _marker(f"stage=section section={section} event={event}")
            + match.group(0)
        )

    data, section_count = SECTION_RE.subn(instrument_section, data)
    if section_count != 28:
        raise ValueError(
            f"Taylor closure section inventory drift: expected 28, got {section_count}"
        )

    close_anchor = b"(* Close the module *)\nend;;\n"
    if data.count(close_anchor) != 1:
        raise ValueError("Taylor closure profile close anchor drift")
    data = data.replace(
        close_anchor,
        _marker("stage=module-execution event=end")
        + close_anchor
        + _marker("stage=module-frontend event=end"),
        1,
    )

    prior = record["normalization"]
    identity = {
        "bytes": len(data),
        "md5": hashlib.md5(data, usedforsecurity=False).hexdigest(),
        "sha256": hashlib.sha256(data).hexdigest(),
    }
    record["normalized_bytes"] = data
    record["normalization"] = {
        "authority": "development-only-nonlinear-closure-profile",
        "id": NORMALIZATION_ID,
        "semantic_rule": (
            "insert discarded print markers immediately before the exact Taylor "
            "module phrase, at module-body execution, and around every authenticated "
            "section boundary; markers do not construct or authorize a theorem"
        ),
        "input_normalization": prior,
        "operation_count": section_count + 4,
        "normalized_bytes": identity["bytes"],
        "normalized_md5": identity["md5"],
        "normalized_sha256": identity["sha256"],
    }
    return {
        "normalization_id": NORMALIZATION_ID,
        "source_key": SOURCE_KEY,
        "input_sha256": INPUT_SHA256,
        "section_events": section_events,
        "operation_count": section_count + 4,
        "normalized_bytes": identity["bytes"],
        "normalized_md5": identity["md5"],
        "normalized_sha256": identity["sha256"],
    }
