#!/usr/bin/env python3
"""Build and validate the machine-readable Candle Great 100 inventory.

The upstream suite name is historical: ``GREAT_100_THEOREMS`` currently has
65 execution targets.  This script keeps that exact target list, its direct
literal ``needs`` dependencies, and the still-missing S1 evidence visible in
one deterministic artifact.
"""

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = Path(__file__).with_suffix(".json")
AUDITED_BASE_COMMIT = "5b1888b9a0c1da7ca0ef2e80526b726f2e27df9d"
NEEDS_RE = re.compile(r'^\s*needs\s*"([^"]+)"\s*;;', re.MULTILINE)

# holtest.mk uses one synthetic target for an ordered two-file session.
SPECIAL_LOAD_FILES = {
    "100/bertrand-primerecip": ["100/bertrand.ml", "100/primerecip.ml"],
}

# Observations are evidence, not acceptance-policy exceptions.  Keep expected
# status "pass" and link failures to a minimized compatibility-ledger entry.
BASELINE_OBSERVATIONS = {
    "100/bertrand-primerecip": {
        "status": "fail",
        "phase": "parse",
        "compatibility_category": "OCaml float-literal syntax",
        "ledger_id": "CANDLE-OCAML-FLOAT-LITERAL-001",
        "diagnostic": "Expected to be at EOF; Parsing failed at let num_of_float",
        "first_source_location": "100/bertrand.ml:18",
        "wall_seconds": 212.6,
        "peak_rss_kib": None,
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "compatibility_paths_match_audited_base": True,
        },
    },
}


def _great_100_targets(text):
    """Return the tokens assigned to GREAT_100_THEOREMS in Make syntax."""
    lines = iter(text.splitlines())
    for line in lines:
        match = re.match(r"^GREAT_100_THEOREMS\s*:=\s*(.*)$", line)
        if match:
            break
    else:
        raise ValueError("GREAT_100_THEOREMS is absent from holtest.mk")

    targets = []
    fragment = match.group(1)
    while True:
        continued = fragment.rstrip().endswith("\\")
        if continued:
            fragment = fragment.rstrip()[:-1]
        targets.extend(fragment.split())
        if not continued:
            break
        try:
            fragment = next(lines)
        except StopIteration as exc:
            raise ValueError("unterminated GREAT_100_THEOREMS assignment") from exc
    return targets


def _sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _direct_needs(load_files):
    dependencies = []
    for load_file in load_files:
        source = (ROOT / load_file).read_text(encoding="utf-8")
        for dependency in NEEDS_RE.findall(source):
            if dependency not in dependencies:
                dependencies.append(dependency)
    return dependencies


def build_manifest():
    names = _great_100_targets((ROOT / "holtest.mk").read_text(encoding="utf-8"))
    targets = []
    covered_sources = set()
    for name in names:
        load_files = SPECIAL_LOAD_FILES.get(name, [f"{name}.ml"])
        missing = [path for path in load_files if not (ROOT / path).is_file()]
        if missing:
            raise ValueError(f"{name}: missing load files: {', '.join(missing)}")
        covered_sources.update(load_files)
        observation = BASELINE_OBSERVATIONS.get(name)
        fingerprint_status = "not_reached" if observation else "missing"
        targets.append({
            "name": name,
            "load_files": load_files,
            "load_file_sha256": {
                path: _sha256(ROOT / path) for path in load_files
            },
            "direct_needs": _direct_needs(load_files),
            "expected_status": "pass",
            "skip": None,
            "fingerprints": {
                "status": fingerprint_status,
                "theorems": None,
                "assumptions": None,
            },
            "baseline_observation": observation,
        })

    all_sources = {
        path.relative_to(ROOT).as_posix() for path in (ROOT / "100").glob("*.ml")
    }
    exclusions = [{
        "path": path,
        "reason": "absent_from_upstream_GREAT_100_THEOREMS",
        "approval_status": "unreviewed",
        "flyspeck_dependency_impact": "unassessed",
    } for path in sorted(all_sources - covered_sources)]

    return {
        "schema_version": 1,
        "suite": "HOL Light Great 100",
        "suite_semantics": (
            "The historical Great 100 suite has 65 clean-process execution "
            "targets over 66 source files; the name does not imply 100 runner entries."
        ),
        "audited_tree_base": AUDITED_BASE_COMMIT,
        "inventory_source": {
            "path": "holtest.mk",
            "variable": "GREAT_100_THEOREMS",
        },
        "dependency_scan": "direct literal needs \"path\";; calls in load_files",
        "execution_contract": {
            "baseline": "hol.ml",
            "isolation": "fresh Candle process per target",
            "cache_policy": "no theorem-state reuse between targets",
        },
        "target_count": len(targets),
        "covered_source_count": len(covered_sources),
        "targets": targets,
        "excluded_100_sources": exclusions,
    }


def _render(payload):
    return json.dumps(payload, indent=2, ensure_ascii=False) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--write", action="store_true", help="regenerate the manifest")
    action.add_argument("--check", action="store_true", help="verify the committed manifest")
    args = parser.parse_args()

    expected = _render(build_manifest())
    if args.write:
        MANIFEST.write_text(expected, encoding="utf-8")
        print(f"wrote {MANIFEST}")
        return 0

    try:
        actual = MANIFEST.read_text(encoding="utf-8")
    except FileNotFoundError:
        print(f"missing manifest: {MANIFEST}", file=sys.stderr)
        return 1
    if actual != expected:
        print(
            f"stale manifest: run {Path(__file__).name} --write",
            file=sys.stderr,
        )
        return 1
    payload = json.loads(actual)
    print(
        f"manifest ok: {payload['target_count']} targets, "
        f"{payload['covered_source_count']} source files, "
        f"{len(payload['excluded_100_sources'])} exclusion(s)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
