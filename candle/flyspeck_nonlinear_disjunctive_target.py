#!/usr/bin/env python3
"""Pin a small member of a substantial disjunctive nonlinear family.

The retained native results select and characterize the benchmark only.  They
are never imported as proof evidence: Candle must construct a kernel theorem
from the authenticated Flyspeck source expression, box, and certificate data.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from decimal import Decimal
from pathlib import Path
from typing import Any

import flyspeck_nonlinear_first_leaf_target as common


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = Path("candle/flyspeck_nonlinear_disjunctive_target.json")
CASE_ID = "prep-8293089898"
GLOBAL_CASE = 16479
LOCAL_CASE = 149
FORMAL_LEAF_COUNT = 788
FORMAL_GLUE_COUNT = 787
FAMILY_SIZE = 333
FAMILY_FIRST_GLOBAL = 16330
FAMILY_STDOUTS = tuple(
    Path(f"azure/results/urban/out/1/{start}/2/{start + 49}/stdout")
    for start in range(16300, 16700, 50)
)
AZURE_STDOUT = Path("azure/results/urban/out/1/16450/2/16499/stdout")
AZURE_INEQS = Path("azure/ineqs.txt")
AZURE_HASHES = Path("azure/results/hashes.txt")

EXPECTED_THEOREM_SHA256 = (
    "3ff2311b5b67933f5b0dc6c1abe5efd942b7131819851c21ceba4e2775d788de"
)
EXPECTED_TREE_SHA256 = (
    "a7483c8dd800c39cb9d1e9204ec4d7b13f6acb5c7458990a7297f0733a0d6670"
)
EXPECTED_PREP_SHA256 = (
    "ecf90259343115a67722be88c25b0d228453aa5bee5f7fd6876ee7931c846196"
)
EXPECTED_NATIVE_DIGEST = "0b95a6345d43bd6aa35e3892f2c38bf9"
EXPECTED_NATIVE_SECONDS = Decimal("561.614339")
EXPECTED_FAMILY_LEAVES = 2787684
EXPECTED_FAMILY_SECONDS = Decimal("2153899.320383")

EXPECTED_EVIDENCE_SHA256 = {
    "azure/results/urban/out/1/16300/2/16349/stdout":
        "6b780e536f7e98ea1fc1dec058aeb15dbaf2ca19330605404fc443ce0398fc1c",
    "azure/results/urban/out/1/16350/2/16399/stdout":
        "f46a3dec7e4fa2e83318323139f63f474e6aac43249911b1f6d4b1a58e68bcc5",
    "azure/results/urban/out/1/16400/2/16449/stdout":
        "6abfd4de5edb930f2d7775f3cb307fced411d09bf42ffa2834cdf86ad6c6f149",
    "azure/results/urban/out/1/16450/2/16499/stdout":
        "ddcb782e9e22c9df9630b1d3a156888f0bb1d94e9a74c89850dc47acae1dcca1",
    "azure/results/urban/out/1/16500/2/16549/stdout":
        "7db34fa2089db8e5868b304f4dcce0525fcf1af3b95613fbf7fb637acc97c517",
    "azure/results/urban/out/1/16550/2/16599/stdout":
        "6d91cb688ee891ebf969230cc74450fb5edfe018c3341e5da608f9568a529928",
    "azure/results/urban/out/1/16600/2/16649/stdout":
        "d430684ec37d4b198ff6d04e70ca86819f57ad365737db3139eb09b8d57c7ef8",
    "azure/results/urban/out/1/16650/2/16699/stdout":
        "35c52f845ce87ceebc4c3c44aca8bf4e7340186372716abc1860f13be85035b3",
    "azure/ineqs.txt":
        "69e6cba72f3fdf1c90da2823fbfcd7adc8602f59e004f037434047aeb9879f4d",
    "azure/results/hashes.txt":
        "7bfd9f07d2d0f64fb7ffaefbbaeea7410910447bac03cfedd235ad851c0f336c",
    "text_formalization/nonlinear/break_case_log.hl":
        "2b3c74156a5ee9a6b3b5b6905ff28a7fb21e7c50052ad37887b90b9ed3d5e499",
    "text_formalization/nonlinear/prep.hl":
        "3ccef1bf65b13ca02e7ab1f409ebb49c979862ed5ea6ff1d57ed1e4e4761723d",
    "azure/main_verifier.hl":
        "f8c18b2699325c0aeba9d853c8ffa2958346016af887133bf23d082adaa2f3dc",
    "text_formalization/general/prove_by_refinement.hl":
        "3101d7b115e9437e94bcfe7ae8156cfc065ac4422d463a91d690d41acca04cdb",
    "azure/flyspeck-nat/definitions.hl":
        "f5c34e49f0114e038949ed0dc1d9a9f5d5f50103420a1272c3231d8b436bbac4",
    "azure/flyspeck-nat/break_case.hl":
        "7df2af9a8b24923a9c7761c4a3ac3496be39f4c161bef480fe0089db24f7d0bd",
}


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _verified_identity(root: Path, relative: Path) -> dict[str, Any]:
    identity = common._identity(root, relative)
    expected = EXPECTED_EVIDENCE_SHA256[relative.as_posix()]
    if identity["sha256"] != expected:
        raise ValueError(f"disjunctive target evidence drifted: {relative}")
    return identity


def _source_call(source: str, prefix: str) -> str:
    """Extract one balanced top-level call ending in ``;;``."""

    if source.count(prefix) != 1:
        raise ValueError(f"source call is absent or ambiguous: {prefix}")
    start = source.index(prefix)
    depth = 0
    saw_open = False
    in_string = False
    escaped = False
    for offset in range(start, len(source)):
        char = source[offset]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            continue
        if char == '"':
            in_string = True
        elif char == "(":
            depth += 1
            saw_open = True
        elif char == ")":
            depth -= 1
            if depth < 0:
                raise ValueError("unbalanced source call")
            if saw_open and depth == 0:
                end = offset + 1
                while end < len(source) and source[end] in " \t":
                    end += 1
                if source.startswith(";;", end):
                    return source[start:end + 2]
    raise ValueError("unterminated source call")


def _prep_block(prep: str) -> str:
    anchor = f'idv= "{CASE_ID}";'
    if prep.count(anchor) != 1:
        raise ValueError("disjunctive inequality definition is ambiguous")
    anchor_offset = prep.index(anchor)
    start = prep.rfind("add_inequality", 0, anchor_offset)
    end = prep.find("};;", anchor_offset)
    if start < 0 or end < 0:
        raise ValueError("disjunctive inequality definition is incomplete")
    block = prep[start:end + 3]
    if block.count("idv=") != 1:
        raise ValueError("disjunctive inequality block crossed a definition")
    return block


def _family_records(root: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    label_pattern = re.compile(
        rf"^Verifying: ([0-9]+):  "
        rf"([0-9]+,\({re.escape(CASE_ID)},([0-9]+)\))$",
        flags=re.MULTILINE,
    )
    for relative in FAMILY_STDOUTS:
        stdout = (root / relative).read_text(encoding="utf-8")
        for global_text, label, local_text in label_pattern.findall(stdout):
            global_case = int(global_text)
            local_case = int(local_text)
            stats = common._native_certificate_stats(
                stdout, global_case, label,
            )
            result = re.search(
                rf"^Time  {re.escape(label)}: (?P<seconds>[0-9.]+)\n"
                rf"^Hash  {re.escape(label)}: (?P<digest>[0-9a-f]{{32}})$",
                stdout,
                flags=re.MULTILINE,
            )
            if result is None:
                raise ValueError(f"native family result is absent: {label}")
            rows.append(
                {
                    "global_case": global_case,
                    "local_case": local_case,
                    "label": label,
                    "seconds": Decimal(result.group("seconds")),
                    "digest": result.group("digest"),
                    **stats,
                }
            )
    return rows


def _remove_whitespace(text: str) -> str:
    return re.sub(r"\s+", "", text)


def build_target(flyspeck_root: Path) -> dict[str, Any]:
    flyspeck_root = flyspeck_root.resolve()
    closure_data = (ROOT / common.CLOSURE).read_bytes()
    closure = json.loads(closure_data)
    expected_head = closure["repositories"]["flyspeck"]["commit"]
    observed_head = common._git_head(flyspeck_root)
    if observed_head != expected_head:
        raise ValueError("disjunctive target Flyspeck head differs from closure")

    evidence: dict[str, Any] = {}
    for index, relative in enumerate(FAMILY_STDOUTS):
        evidence[f"family_stdout_{index}"] = _verified_identity(
            flyspeck_root, relative,
        )
    for name, relative in (
        ("azure_ineqs", AZURE_INEQS),
        ("azure_hashes", AZURE_HASHES),
        ("break_case_log", common.BREAK_LOG),
        ("prep", common.PREP),
        ("main_verifier", common.MAIN_VERIFIER),
        ("prove_by_refinement", common.PROVE_BY_REFINEMENT),
        ("compiled_definitions", common.COMPILED_DEFINITIONS),
        ("compiled_break_case", common.COMPILED_BREAK_CASE),
    ):
        evidence[name] = _verified_identity(flyspeck_root, relative)

    rows = _family_records(flyspeck_root)
    expected_locals = list(range(FAMILY_SIZE))
    observed_locals = sorted(row["local_case"] for row in rows)
    if observed_locals != expected_locals:
        raise ValueError("retained disjunctive family membership has drifted")
    if any(
        row["global_case"] != FAMILY_FIRST_GLOBAL + row["local_case"]
        for row in rows
    ):
        raise ValueError("retained disjunctive family numbering has drifted")
    if any(
        row["formal_raw_leaf_count"] != 0
        or row["formal_mono_count"] != 0
        or row["formal_convex_glue_count"] != 0
        or row["formal_pass_mono_count"] != 0
        or row["formal_glue_count"] != row["formal_leaf_count"] - 1
        for row in rows
    ):
        raise ValueError("retained disjunctive certificate shape has drifted")
    total_leaves = sum(row["formal_leaf_count"] for row in rows)
    total_seconds = sum((row["seconds"] for row in rows), Decimal(0))
    if (
        total_leaves != EXPECTED_FAMILY_LEAVES
        or total_seconds != EXPECTED_FAMILY_SECONDS
    ):
        raise ValueError("retained disjunctive family aggregate has drifted")

    selected = next(
        row for row in rows
        if row["global_case"] == GLOBAL_CASE
        and row["local_case"] == LOCAL_CASE
    )
    minimum = min(
        rows,
        key=lambda row: (
            row["formal_leaf_count"], row["seconds"], row["local_case"],
        ),
    )
    if selected is not minimum:
        raise ValueError("selected disjunctive minimum has drifted")
    if (
        selected["formal_leaf_count"] != FORMAL_LEAF_COUNT
        or selected["formal_glue_count"] != FORMAL_GLUE_COUNT
        or selected["seconds"] != EXPECTED_NATIVE_SECONDS
        or selected["digest"] != EXPECTED_NATIVE_DIGEST
    ):
        raise ValueError("selected disjunctive native result has drifted")

    if AZURE_STDOUT not in FAMILY_STDOUTS:
        raise AssertionError("selected stdout is outside the family evidence")
    selected_stdout = (flyspeck_root / AZURE_STDOUT).read_text(
        encoding="utf-8",
    )
    label = selected["label"]
    theorem_match = re.search(
        rf"Theorem  {re.escape(label)}: \|- (?P<theorem>.*?)\n"
        rf"Time  {re.escape(label)}: (?P<seconds>[0-9.]+)\n"
        rf"Hash  {re.escape(label)}: (?P<digest>[0-9a-f]{{32}})",
        selected_stdout,
        flags=re.DOTALL,
    )
    if theorem_match is None:
        raise ValueError("selected disjunctive theorem record is absent")
    theorem = theorem_match.group("theorem")
    if (
        _sha256_text(theorem) != EXPECTED_THEOREM_SHA256
        or not theorem.startswith("ineqm [x1; x2; x3; x4; x5; x6]")
        or "frac_right 5 #0.5000" not in theorem
        or "x1_delta_x x1 x2 x3 x4 x5 x6 * &4" not in theorem
        or "delta4_squared_x x1 x2 x3 x4 x5 x6 * --#0.833" not in theorem
        or "rhazimatn_x x1 x2 x3 x4 x5 x6 * -- &1" not in theorem
        or "rhazim2atn_x x1 x2 x3 x4 x5 x6 * -- &1" not in theorem
        or "rhazim3atn_x x1 x2 x3 x4 x5 x6 * -- &1" not in theorem
        or "unit6 x1 x2 x3 x4 x5 x6 * const1 * pi" not in theorem
    ):
        raise ValueError("selected disjunctive theorem interface has drifted")

    inventory = (flyspeck_root / AZURE_INEQS).read_text(encoding="utf-8")
    inventory_prefix = f"{GLOBAL_CASE}: {label}: "
    inventory_lines = [
        line for line in inventory.splitlines()
        if line.startswith(inventory_prefix)
    ]
    if len(inventory_lines) != 1:
        raise ValueError("selected disjunctive inventory record is ambiguous")
    if _remove_whitespace(
        inventory_lines[0][len(inventory_prefix):]
    ) != _remove_whitespace(theorem):
        raise ValueError("stdout theorem differs from the master inventory")

    hashes = (flyspeck_root / AZURE_HASHES).read_text(encoding="utf-8")
    hash_line = f"({CASE_ID},{LOCAL_CASE}): {EXPECTED_NATIVE_DIGEST}"
    if hashes.splitlines().count(hash_line) != 1:
        raise ValueError("selected disjunctive digest inventory has drifted")

    break_log = (flyspeck_root / common.BREAK_LOG).read_text(
        encoding="utf-8",
    )
    tree = _source_call(break_log, f'add_case ("{CASE_ID}",')
    if (
        _sha256_text(tree) != EXPECTED_TREE_SHA256
        or not tree.startswith(
            f'add_case ("{CASE_ID}",\n Iarg_bisect (4,',
        )
    ):
        raise ValueError("disjunctive family tree has drifted")

    prep = (flyspeck_root / common.PREP).read_text(encoding="utf-8")
    definition = _prep_block(prep)
    if (
        _sha256_text(definition) != EXPECTED_PREP_SHA256
        or "x1_delta_x x1 x2 x3 x4 x5 x6 * &4" not in definition
        or "delta4_squared_x x1 x2 x3 x4 x5 x6 * -- #0.833" not in definition
        or "rhazim_x x1 x2 x3 x4 x5 x6 * -- &1" not in definition
        or "rhazim2_x x1 x2 x3 x4 x5 x6 * -- &1" not in definition
        or "rhazim3_x x1 x2 x3 x4 x5 x6 * -- &1" not in definition
    ):
        raise ValueError("disjunctive source inequality has drifted")

    verifier = (flyspeck_root / common.MAIN_VERIFIER).read_text(
        encoding="utf-8",
    )
    if (
        "verify_flyspeck_ineq 6 ineq" not in verifier
        or "{default_params with eps = 1e-10}" not in verifier
    ):
        raise ValueError("historical verifier parameter contract has drifted")

    definitions = (flyspeck_root / common.COMPILED_DEFINITIONS).read_text(
        encoding="utf-8",
    )
    break_case = (flyspeck_root / common.COMPILED_BREAK_CASE).read_text(
        encoding="utf-8",
    )
    if (
        '("rhazimatn_x",rhazimatn_x)' not in definitions
        or '("rhazim2atn_x",rhazim2atn_x)' not in definitions
        or '("rhazim3atn_x",rhazim3atn_x)' not in definitions
        or "let rec ineqm_conv =" not in break_case
    ):
        raise ValueError("disjunctive reconstruction support has drifted")

    return {
        "schema": 1,
        "kind": "candle-flyspeck-nonlinear-disjunctive-target",
        "status": "development-non-release",
        "claim": (
            "authenticated disjunctive target/native oracle only; no Candle "
            "proof, S2, S3, qualification, promotion, or release credit"
        ),
        "flyspeck_commit": observed_head,
        "closure": {
            "path": common.CLOSURE.as_posix(),
            "bytes": len(closure_data),
            "sha256": hashlib.sha256(closure_data).hexdigest(),
        },
        "evidence_files": evidence,
        "family": {
            "id": CASE_ID,
            "member_count": len(rows),
            "global_case_first": FAMILY_FIRST_GLOBAL,
            "global_case_last": FAMILY_FIRST_GLOBAL + FAMILY_SIZE - 1,
            "formal_leaf_count": total_leaves,
            "formal_glue_count": sum(
                row["formal_glue_count"] for row in rows
            ),
            "historical_total_seconds": str(total_seconds),
            "historical_total_processor_hours": str(total_seconds / 3600),
            "ordinary_only": True,
            "source_definition": {
                "bytes": len(definition.encode("utf-8")),
                "sha256": _sha256_text(definition),
            },
            "archive_tree": {
                "bytes": len(tree.encode("utf-8")),
                "sha256": _sha256_text(tree),
                "top_action": {
                    "kind": "Iarg_bisect",
                    "coordinate": 4,
                },
            },
        },
        "target": {
            "id": CASE_ID,
            "global_case": GLOBAL_CASE,
            "local_case": LOCAL_CASE,
            "selection": "minimum formal leaf count in retained family",
            "legacy_box_path": [
                {"kind": "frac", "side": "right", "coordinate": 5,
                 "decimal": "0.5000"},
                {"kind": "bisect", "side": "right", "coordinate": 3},
                {"kind": "bisect", "side": "right", "coordinate": 2},
                {"kind": "bisect", "side": "left", "coordinate": 1},
                {"kind": "bisect", "side": "right", "coordinate": 0},
                {"kind": "bisect", "side": "left", "coordinate": 4},
                {"kind": "bisect", "side": "right", "coordinate": 4},
            ],
            "legacy_ineqm_text": theorem,
            "legacy_ineqm_text_sha256": _sha256_text(theorem),
        },
        "native_oracle": {
            "precision": 6,
            "epsilon": "1e-10",
            "total_seconds": float(selected["seconds"]),
            "legacy_theorem_digest": selected["digest"],
            **{
                key: value for key, value in selected.items()
                if key.startswith("formal_")
            },
        },
    }


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
        raise SystemExit(
            "stale disjunctive nonlinear target: run with --write"
        )


if __name__ == "__main__":
    main()
