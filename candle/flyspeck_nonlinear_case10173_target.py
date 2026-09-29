#!/usr/bin/env python3
"""Pin the left-half sibling of the current action-296 NL target.

The retained native result identifies the target and historical performance;
it is never imported as proof evidence.  Candle must reconstruct and prove the
ordinary ``ineqm`` theorem from the authenticated current Flyspeck sources.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
from pathlib import Path
from typing import Any

import flyspeck_nonlinear_action296_leaf_target as action296
import flyspeck_nonlinear_first_leaf_target as common


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = Path("candle/flyspeck_nonlinear_case10173_target.json")
CASE_ID = "prep-8657368829"
GLOBAL_CASE = 10173
LOCAL_CASE = 1
FORMAL_LEAF_COUNT = 3305
FORMAL_GLUE_COUNT = 3304


def build_target(flyspeck_root: Path) -> dict[str, Any]:
    """Authenticate case 10173 while retaining the shared source closure."""

    flyspeck_root = flyspeck_root.resolve()
    payload = copy.deepcopy(action296.build_target(flyspeck_root))
    stdout_path = flyspeck_root / action296.AZURE_STDOUT
    stdout = stdout_path.read_text(encoding="utf-8")
    label = f"{GLOBAL_CASE},({CASE_ID},{LOCAL_CASE})"
    theorem_match = re.search(
        rf"Theorem  {re.escape(label)}: \|- (?P<theorem>.*?)\n"
        rf"Time  {re.escape(label)}: (?P<seconds>[0-9.]+)\n"
        rf"Hash  {re.escape(label)}: (?P<digest>[0-9a-f]{{32}})",
        stdout,
        flags=re.DOTALL,
    )
    if theorem_match is None:
        raise ValueError("retained case-10173 theorem record is absent")

    oracle_stats = common._native_certificate_stats(
        stdout, GLOBAL_CASE, label,
    )
    if oracle_stats != {
        "formal_leaf_count": FORMAL_LEAF_COUNT,
        "formal_raw_leaf_count": 0,
        "formal_mono_count": 0,
        "formal_glue_count": FORMAL_GLUE_COUNT,
        "formal_convex_glue_count": 0,
        "formal_pass_mono_count": 0,
    }:
        raise ValueError("retained case-10173 certificate shape has drifted")

    theorem = theorem_match.group("theorem")
    if (
        not theorem.startswith("ineqm [x1; x2; x3; x4; x5; x6]")
        or "frac_left 0 #0.5000" not in theorem
        or "dihatn_x x1 x2 x3 x4 x5 x6 * -- &1 <" not in theorem
        or "#1.277" not in theorem
    ):
        raise ValueError("retained case-10173 theorem has unexpected interface")

    payload["kind"] = "candle-flyspeck-nonlinear-sibling-target"
    payload["claim"] = (
        "authenticated case-10173 target/native oracle only; no Candle "
        "proof, S2, S3, qualification, promotion, or release credit"
    )
    payload["target"].update(
        {
            "global_case": GLOBAL_CASE,
            "local_case": LOCAL_CASE,
            "legacy_ineqm_text": theorem,
            "legacy_ineqm_text_sha256": hashlib.sha256(
                theorem.encode("utf-8")
            ).hexdigest(),
        }
    )
    payload["target"]["first_tree_action"]["side"] = "left"
    payload["native_oracle"] = {
        "precision": 6,
        "epsilon": "1e-10",
        "total_seconds": float(theorem_match.group("seconds")),
        "legacy_theorem_digest": theorem_match.group("digest"),
        **oracle_stats,
    }
    return payload


def _render(payload: dict[str, Any]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--flyspeck-root", type=Path, required=True)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--write", action="store_true")
    action.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    rendered = _render(build_target(arguments.flyspeck_root))
    output = ROOT / OUTPUT
    if arguments.write:
        output.write_text(rendered, encoding="utf-8")
    elif not output.is_file() or output.read_text(encoding="utf-8") != rendered:
        raise SystemExit("stale case-10173 nonlinear target: run with --write")


if __name__ == "__main__":
    main()
