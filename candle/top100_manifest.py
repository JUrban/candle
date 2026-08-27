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
LET_BINDING_RE = re.compile(
    r"^[ \t]*let[ \t]+([A-Za-z][A-Za-z0-9_']*)[ \t]*=", re.MULTILINE)

# holtest.mk uses one synthetic target for an ordered two-file session.
SPECIAL_LOAD_FILES = {
    "100/bertrand-primerecip": ["100/bertrand.ml", "100/primerecip.ml"],
}

# Named results requested after each clean load.  This is a source audit, not
# an expected fingerprint table: until a pinned reference run supplies exact
# identities, the manifest continues to report fingerprints as missing.  A
# few broad or repeatedly shadowed source files have an explicit manual-review
# note rather than pretending that their proposed result set is final.
TARGET_THEOREMS = {
    "100/arithmetic_geometric_mean": ["AGM", "AGM_ROOT"],
    "100/arithmetic": ["ARITHMETIC_PROGRESSION"],
    "100/ballot": ["BALLOT"],
    "100/bernoulli": ["SUM_OF_POWERS"],
    "100/bertrand-primerecip": ["BERTRAND", "PRIMERECIP_DIVERGES"],
    "100/birthday": ["BIRTHDAY_THM", "BIRTHDAY_THM_EXPLICIT"],
    "100/buffon": ["BUFFON_GENERAL", "BUFFON_SHORT", "BUFFON_LONG"],
    "100/cantor": ["CANTOR"],
    "100/cayley_hamilton": ["CAYLEY_HAMILTON"],
    "100/ceva": ["CEVA"],
    "100/circle": ["AREA_CBALL", "AREA_BALL"],
    "100/chords": ["SEGMENT_CHORDS"],
    "100/combinations": [
        "NUMBER_OF_COMBINATIONS", "NUMBER_OF_COMBINATIONS_EXPLICIT"],
    "100/constructible": ["DOUBLE_THE_CUBE", "TRISECT_60_DEGREES"],
    "100/cosine": ["LAW_OF_COSINES"],
    "100/cubedissection": ["ONLY_TRIVIAL_CUBE_DISSECTION"],
    "100/cubic": ["CUBIC"],
    "100/derangements": ["THE_DERANGEMENTS_FORMULA"],
    "100/desargues": ["DESARGUES_DIRECT"],
    "100/descartes": ["DESCARTES_RULE_OF_SIGNS"],
    "100/dirichlet": ["DIRICHLET"],
    "100/div3": ["DIVISIBILITY_BY_3"],
    "100/divharmonic": ["HARMONIC_DIVERGES"],
    "100/e_is_transcendental": ["Finale.TRANSCENDENTAL_E"],
    "100/euler": ["EULER_PARTITION_THEOREM"],
    "100/feuerbach": ["FEUERBACH"],
    "100/fourier": [
        "FOURIER_SERIES_L2",
        "FOURIER_DINI_TEST",
        "FOURIER_JORDAN_BOUNDED_VARIATION",
        "FOURIER_FEJER_CESARO_SUMMABLE_SIMPLE",
    ],
    "100/four_squares": ["SUM_OF_TWO_SQUARES", "LAGRANGE_NUM"],
    "100/friendship": ["FRIENDSHIP"],
    "100/fta": ["FTA"],
    "100/gcd": ["EGCD"],
    "100/green": ["GREEN_THEOREM_CURL"],
    "100/heron": ["HERON"],
    "100/isoperimetric": ["ISOPERIMETRIC_THEOREM"],
    "100/inclusion_exclusion": [
        "INCLUSION_EXCLUSION_USUAL", "INCLUSION_EXCLUSION_MOBIUS"],
    "100/independence": [
        "TARSKI_AXIOM_1_NONEUCLIDEAN",
        "TARSKI_AXIOM_2_NONEUCLIDEAN",
        "TARSKI_AXIOM_3_NONEUCLIDEAN",
        "TARSKI_AXIOM_4_NONEUCLIDEAN",
        "TARSKI_AXIOM_5_NONEUCLIDEAN",
        "TARSKI_AXIOM_6_NONEUCLIDEAN",
        "TARSKI_AXIOM_7_NONEUCLIDEAN",
        "TARSKI_AXIOM_8_NONEUCLIDEAN",
        "TARSKI_AXIOM_9_NONEUCLIDEAN",
        "NOT_TARSKI_AXIOM_10_NONEUCLIDEAN",
        "TARSKI_AXIOM_11_NONEUCLIDEAN",
    ],
    "100/isosceles": [
        "ISOSCELES_TRIANGLE_THEOREM", "ISOSCELES_TRIANGLE_CONVERSE"],
    "100/konigsberg": ["KOENIGSBERG"],
    "100/lagrange": ["GROUP_LAGRANGE"],
    "100/leibniz": ["LEIBNIZ_PI"],
    "100/lhopital": ["LHOPITAL"],
    "100/liouville": ["TRANSCENDENTAL_LIOUVILLE"],
    "100/minkowski": ["MINKOWSKI"],
    "100/morley": ["MORLEY"],
    "100/pascal": ["PASCAL"],
    "100/perfect": ["PERFECT_EUCLID", "PERFECT_EULER"],
    "100/pick": ["PICK"],
    "100/piseries": ["EULER_HARMONIC_SUM"],
    "100/platonic": ["PLATONIC_SOLIDS"],
    "100/pnt": ["PNT"],
    "100/polyhedron": ["EULER_RELATION"],
    "100/ptolemy": ["PTOLEMY"],
    "100/pythagoras": ["PYTHAGORAS"],
    "100/quartic": ["QUARTIC_CASES"],
    "100/ramsey": ["RAMSEY"],
    "100/ratcountable": ["COUNTABLE_RATIONALS", "DENUMERABLE_RATIONALS"],
    "100/realsuncountable": ["UNCOUNTABLE_REALS"],
    "100/reciprocity": ["RECIPROCITY_LEGENDRE"],
    "100/stirling": ["STIRLING"],
    "100/subsequence": ["ERDOS_SZEKERES"],
    "100/thales": ["THALES"],
    "100/transcendence": [
        "e_is_irrational",
        "e_is_transcendental",
        "pi_is_transcendental",
        "transcendental_if_exp_nonzero_algebraic",
        "zero_sum_algebraic_exp_algebraic",
    ],
    "100/triangular": ["TRIANGLE_FINITE_SUM", "TRIANGLE_CONVERGES'"],
    "100/two_squares": ["SUM_OF_TWO_SQUARES"],
    "100/wilson": ["WILSON", "WILSON_EQ"],
}

MANUAL_REVIEW_MAPPINGS = {
    "100/cantor": (
        "CANTOR is rebound to a different formulation; the request resolves "
        "to the last declaration, but the acceptance formulation needs review"
    ),
    "100/fourier": (
        "the broad source contains L2, Dini, Jordan, and Fejer results; the "
        "four proposed named results need an approved Great-100 boundary"
    ),
    "100/piseries": (
        "EULER_HARMONIC_SUM is the apparent named pi-series result, but the "
        "file also exposes substantial tan/cot series results"
    ),
    "100/quartic": (
        "QUARTIC_CASES is rebound three times; the request resolves to the "
        "last automatic proof, pending acceptance review"
    ),
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
    "100/ceva": {
        "status": "fail",
        "phase": "dependency_load",
        "compatibility_category": "missing numeric helper",
        "diagnostic": "undefined value round_num while loading Examples/sos.ml",
        "first_source_location": "Examples/sos.ml",
        "wall_seconds": 1428.4,
        "peak_rss_kib": None,
        "anchor_candidate": "218c7c9",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/constructible": {
        "status": "fail",
        "phase": "parse",
        "compatibility_category": "OCaml multiline string literal",
        "diagnostic": "LEXER ERROR; Parsing failed inside the multiline define_type string",
        "first_source_location": "100/constructible.ml:115",
        "log_active_seconds_approx": 3730.4,
        "peak_rss_kib": None,
        "upstream_remedy": {
            "repository": "CakeML/cakeml",
            "commit": "c26aa71d2b1007d43cecd1ef7f843530b32ad4fc",
            "status": "present_in_audited_source_base; compiled Candle rebuild required",
        },
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/cubedissection": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 3794.6,
        "observed_process_rss_kib": 6413644,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/cubic": {
        "status": "fail",
        "phase": "dependency_elaboration",
        "compatibility_category": "polymorphic comparison",
        "ledger_id": "CANDLE-OCAML-POLYMORPHIC-COMPARISON-001",
        "diagnostic": (
            "SEMIRING_NORMALIZERS_CONV comparator inferred as term -> term -> bool "
            "where int -> int -> bool was expected"
        ),
        "first_source_location": "Complex/complexnumbers.ml:720",
        "log_active_seconds_approx": 192.0,
        "peak_rss_kib": None,
        "anchor_candidate": "5c44565",
        "isolated_source_validation": {
            "source_normalization_commit": "75d4062",
            "status": "pass",
            "fingerprint_status": "observed_uncompared",
            "artifact": "candle/compatibility/cubic_target_observation.json",
        },
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/desargues": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 1379.9,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/descartes": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 4108.9,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/dirichlet": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 3759.4,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/div3": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 169.0,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/divharmonic": {
        "status": "pass",
        "evidence_scope": (
            "load_only; theorem and assumption fingerprints remain missing"
        ),
        "log_active_seconds_approx": 193.8,
        "peak_rss_kib": None,
        "timeout_policy": "1800-second inactivity deadline; no total wall deadline",
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
        },
    },
    "100/e_is_transcendental": {
        "status": "fail",
        "phase": "parse",
        "compatibility_category": "trailing semicolon in argument expression",
        "ledger_id": "CANDLE-OCAML-TRAILING-SEMICOLON-001",
        "diagnostic": (
            "Expected to be at EOF; parsing rejects the enclosing "
            "Pm_eqn4_rhs module phrase"
        ),
        "diagnostic_pointer": "100/e_is_transcendental.ml:921",
        "first_incompatible_source_location": "100/e_is_transcendental.ml:995",
        "log_active_seconds_approx": 246.7,
        "peak_rss_kib": None,
        "anchor_candidate": "badbd63",
        "isolated_source_validation": {
            "source_normalization_commit": "6ce6fc1",
            "status": "pass",
            "fingerprint_status": "observed_uncompared",
            "fingerprint_value_path": "Finale.TRANSCENDENTAL_E",
            "artifact": (
                "candle/compatibility/"
                "e_is_transcendental_target_observation.json"
            ),
        },
        "evidence": {
            "runner_git_head": "110a18d485557ae877d0cb47bb9172e6558ddf61",
            "candle_executable_sha256": (
                "d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3"
            ),
            "resource_sampling": "incomplete_after_procfs_sampler_race",
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


def _theorem_request(target, load_files):
    """Resolve every requested OCaml binding in target load order."""
    requested_names = TARGET_THEOREMS.get(target)
    if not requested_names:
        raise ValueError(f"{target}: no named theorem request")

    declarations = {}
    for path in load_files:
        source = (ROOT / path).read_text(encoding="utf-8")
        for match in LET_BINDING_RE.finditer(source):
            name = match.group(1)
            declarations.setdefault(name, []).append({
                "path": path,
                "line": source.count("\n", 0, match.start()) + 1,
            })

    theorems = []
    for name in requested_names:
        declaration_name = name.rsplit(".", 1)[-1]
        occurrences = declarations.get(declaration_name, [])
        if not occurrences:
            raise ValueError(
                f"{target}: requested theorem binding is absent: {name}")
        theorem = {
            "name": name,
            "resolved_declaration": occurrences[-1],
            "shadowed_declarations": occurrences[:-1],
        }
        if "." in name:
            references = []
            reference_re = re.compile(rf"(?<![A-Za-z0-9_']){re.escape(name)}"
                                      rf"(?![A-Za-z0-9_'])")
            for path in load_files:
                source = (ROOT / path).read_text(encoding="utf-8")
                references.extend({
                    "path": path,
                    "line": source.count("\n", 0, match.start()) + 1,
                } for match in reference_re.finditer(source))
            if not references:
                raise ValueError(
                    f"{target}: qualified theorem is never referenced: {name}")
            theorem["qualified_references"] = references
        theorems.append(theorem)

    review_note = MANUAL_REVIEW_MAPPINGS.get(target)
    return {
        "mapping_status": "manual_review" if review_note else "audited",
        "mapping_basis": "named result declarations in ordered load files",
        "review_note": review_note,
        "theorems": theorems,
        "identity_contract": {
            "theorem": "canonical structural theorem serialization",
            "hypotheses": "canonical sorted structural term serializations",
            "assumptions": "canonical sorted global HOL axiom serializations",
        },
        "expected_identities": None,
    }


def build_manifest():
    names = _great_100_targets((ROOT / "holtest.mk").read_text(encoding="utf-8"))
    unknown_mapping_targets = set(TARGET_THEOREMS) - set(names)
    if unknown_mapping_targets:
        raise ValueError(
            "named theorem requests are not Great 100 targets: "
            + ", ".join(sorted(unknown_mapping_targets)))
    targets = []
    covered_sources = set()
    for name in names:
        load_files = SPECIAL_LOAD_FILES.get(name, [f"{name}.ml"])
        missing = [path for path in load_files if not (ROOT / path).is_file()]
        if missing:
            raise ValueError(f"{name}: missing load files: {', '.join(missing)}")
        covered_sources.update(load_files)
        observation = BASELINE_OBSERVATIONS.get(name)
        fingerprint_status = (
            "not_reached"
            if observation and observation["status"] != "pass"
            else "missing"
        )
        targets.append({
            "name": name,
            "load_files": load_files,
            "load_file_sha256": {
                path: _sha256(ROOT / path) for path in load_files
            },
            "direct_needs": _direct_needs(load_files),
            "expected_status": "pass",
            "skip": None,
            "fingerprint_request": _theorem_request(name, load_files),
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
            "recorded_live_baseline_timeout_policy": {
                "boot_inactivity_timeout_seconds": 30,
                "load_inactivity_timeout_seconds": 1800,
                "inactivity_resets_on": (
                    "each recognized Loading, val, or Finished progress event"
                ),
                "total_wall_timeout_seconds": None,
                "wall_policy": "unbounded",
                "note": (
                    "The live runner left boot at pexpect's 30-second default. "
                    "Its --timeout 1800 applied to every subsequent expect "
                    "wait, so progress reset the load inactivity clock and no "
                    "total per-target deadline applied."
                ),
            },
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
