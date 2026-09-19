#!/usr/bin/env python3
"""Generate the authenticated source closure for Flyspeck's formal verifier.

This is a bounded development authority for the reflective nonlinear lane.  It
does not enlarge the direct 400-source release manifest.  Instead, it records
the exact additional logical source identities that a future manifest revision
must admit before ``M_verifier_main.verify_ineq`` can be exercised in Candle.
Dependency recognition and lookup deliberately reuse the direct manifest's
scanner and lexical resolver rather than introducing a second interpretation
of HOL Light loading syntax.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path
from typing import Any

import flyspeck_manifest
import flyspeck_normalize


SCHEMA = 1
ROOT = Path(__file__).resolve().parents[1]
MANIFEST = Path("candle/flyspeck_manifest.json")
OUTPUT = Path("candle/flyspeck_nonlinear_verifier_closure.json")
VERIFIER_ROOT = flyspeck_manifest.SourceRef(
    "flyspeck", "formal_ineqs/verifier/m_verifier_main.hl",
)
SOURCE_NORMALIZATION = "candle-flyspeck-parser-compatibility-v1"
NESTED_ARRAY_NORMALIZATION = SOURCE_NORMALIZATION
NORMALIZATION_SEMANTIC_RULE = (
    "make native OCaml grouping explicit: chained array accesses use "
    "Array.get/Array.set with parenthesized indices; module-qualified record "
    "labels use the same unqualified labels under an explicit original record "
    "type; and a ref assignment's conditional RHS is parenthesized"
)
NORMALIZATION_SCOPE_LIMIT = (
    "This bounded parser normalization is confined to the authenticated "
    "formal-verifier closure and only makes native OCaml grouping explicit. "
    "It changes no theorem statement, hypothesis, proof step, proof intent, "
    "runtime primitive, or axiom. Existing direct-Flyspeck execution "
    "normalizations remain authoritative and are applied from the shared "
    "versioned normalization contract."
)
NESTED_ARRAY_SET_RE = re.compile(
    rb"\b([A-Za-z_][A-Za-z0-9_']*)\.\(([^()\r\n]+)\)\.\(([^()\r\n]+)\)"
    rb"\s*<-\s*([^;\r\n]+?)\s+in\b"
)
NESTED_ARRAY_GET_RE = re.compile(
    rb"\b([A-Za-z_][A-Za-z0-9_']*)\.\(([^()\r\n]+)\)\.\(([^()\r\n]+)\)"
)


def _digest(path: Path, algorithm: str) -> str:
    digest = hashlib.new(algorithm)
    with path.open("rb") as source:
        while block := source.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def _git_head(root: Path) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "HEAD"],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    return result.stdout.strip()


def normalize_nested_array_access(
    source: bytes,
) -> tuple[bytes, list[dict[str, Any]]]:
    """Lower chained OCaml array syntax to the equivalent central API.

    Candle accepts individual array indexing and update expressions, but its
    frontend does not group chained ``a.(i).(j)`` occurrences faithfully in
    the larger formal-verifier modules.  Array.get/Array.set make the native
    OCaml grouping explicit without changing evaluation order or values.
    """

    operations: list[dict[str, Any]] = []

    def replace_set(match: re.Match[bytes]) -> bytes:
        before = match.group(0)
        after = (
            b"Array.set (Array.get " + match.group(1) + b" ("
            + match.group(2) + b")) (" + match.group(3) + b") "
            + match.group(4) + b" in"
        )
        operations.append({
            "kind": "nested-array-set",
            "line": source.count(b"\n", 0, match.start()) + 1,
            "before": before.decode("ascii"),
            "after": after.decode("ascii"),
        })
        return after

    normalized = NESTED_ARRAY_SET_RE.sub(replace_set, source)

    def replace_get(match: re.Match[bytes]) -> bytes:
        before = match.group(0)
        after = (
            b"Array.get (Array.get " + match.group(1) + b" ("
            + match.group(2) + b")) (" + match.group(3) + b")"
        )
        operations.append({
            "kind": "nested-array-get",
            "line": normalized.count(b"\n", 0, match.start()) + 1,
            "before": before.decode("ascii"),
            "after": after.decode("ascii"),
        })
        return after

    normalized = NESTED_ARRAY_GET_RE.sub(replace_get, normalized)
    if (
        NESTED_ARRAY_SET_RE.search(normalized) is not None
        or NESTED_ARRAY_GET_RE.search(normalized) is not None
    ):
        raise ValueError("nested array normalization left an unmatched access")
    operations.sort(key=lambda operation: (
        int(operation["line"]),
        str(operation["kind"]),
        str(operation["before"]),
    ))
    return normalized, operations


MAIN_VERIFIER_GROUPING_REPLACEMENTS = (
    (
        "typed-informal-verification-record",
        b'''      {
\tInformal_verifier.taylor = eval_ti;
\tInformal_verifier.f = eval0_informal;
\tInformal_verifier.df = dummy_df;
\tInformal_verifier.ddf = dummy_ddf
      };;''',
        b'''      ({
\ttaylor = eval_ti;
\tf = eval0_informal;
\tdf = dummy_df;
\tddf = dummy_ddf
      } : Informal_verifier.verification_funs);;''',
    ),
    (
        "parenthesized-assignment-conditional",
        b'''\tval_ref := if lo_flag then (lhs, snd !val_ref) else (fst !val_ref, rhs) in''',
        b'''\tval_ref := (if lo_flag then (lhs, snd !val_ref) else (fst !val_ref, rhs)) in''',
    ),
    (
        "typed-informal-search-record-adaptive",
        b'''      let opt0 = {
\tInformal_search.raw_intervals0 = !params.raw_intervals0;
\tInformal_search.max_width = 1e-10;
\tInformal_search.max_depth = 200;
\tInformal_search.pp = pp;
\tInformal_search.mono_depth = if !params.allow_derivatives then 200 else 0;
      } in''',
        b'''      let opt0 = ({
\traw_intervals0 = !params.raw_intervals0;
\tmax_width = 1e-10;
\tmax_depth = 200;
\tpp = pp;
\tmono_depth = if !params.allow_derivatives then 200 else 0;
      } : Informal_search.search_options) in''',
    ),
    (
        "typed-informal-search-record-fixed",
        b'''      let opt0 = {
\tInformal_search.raw_intervals0 = !params.raw_intervals0;
\tInformal_search.max_width = 1e-10;
\tInformal_search.max_depth = 200;
\tInformal_search.pp = pp;
\tInformal_search.mono_depth = 0;
      } in''',
        b'''      let opt0 = ({
\traw_intervals0 = !params.raw_intervals0;
\tmax_width = 1e-10;
\tmax_depth = 200;
\tpp = pp;
\tmono_depth = 0;
      } : Informal_search.search_options) in''',
    ),
)


def normalize_source(
    source_key: str,
    source: bytes,
) -> tuple[bytes, list[dict[str, Any]]]:
    """Apply the complete bounded frontend compatibility normalization."""

    normalized, operations = normalize_nested_array_access(source)
    if source_key != (
        "flyspeck:formal_ineqs/verifier/m_verifier_main.hl"
    ):
        return normalized, operations
    for kind, before, after in MAIN_VERIFIER_GROUPING_REPLACEMENTS:
        if normalized.count(before) != 1:
            raise ValueError(f"main verifier grouping anchor drift: {kind}")
        offset = normalized.index(before)
        operations.append({
            "kind": kind,
            "line": normalized.count(b"\n", 0, offset) + 1,
            "before": before.decode("ascii"),
            "after": after.decode("ascii"),
        })
        normalized = normalized.replace(before, after, 1)
    operations.sort(key=lambda operation: (
        int(operation["line"]),
        str(operation["kind"]),
        str(operation["before"]),
    ))
    return normalized, operations


def _normalization_record(
    source_key: str,
    source: bytes,
    direct_normalizations: dict[str, tuple[dict[str, Any], bytes]],
) -> tuple[bytes, dict[str, Any] | None]:
    """Apply one authoritative normalization lane, rejecting overlap.

    Sources already covered by the direct Flyspeck normalization contract use
    those exact recorded bytes.  The nonlinear parser compatibility pass is
    then checked against the resulting bytes.  Supporting an overlap would
    require an explicit composed contract; silently composing two authorities
    here would make the output identity depend on an unreviewed order.
    """

    direct = direct_normalizations.get(source_key)
    base = source if direct is None else direct[1]
    normalized, operations = normalize_source(source_key, base)
    if direct is not None and operations:
        raise ValueError(
            f"overlapping direct/parser normalizations: {source_key}"
        )
    if direct is not None:
        entry, expected = direct
        if normalized != expected:
            raise ValueError(f"direct normalization output drift: {source_key}")
        return normalized, {
            "id": entry["id"],
            "authority": "direct-flyspeck-normalization-contract",
            "semantic_rule": entry["semantic_rule"],
            "scope_limit": entry["scope_limit"],
            "operation_count": len(entry["operations"]),
            "operations": entry["operations"],
            "normalized_bytes": entry["normalized_bytes"],
            "normalized_md5": entry["normalized_md5"],
            "normalized_sha256": entry["normalized_sha256"],
        }
    if not operations:
        return source, None
    return normalized, {
        "id": SOURCE_NORMALIZATION,
        "authority": "nonlinear-verifier-closure",
        "semantic_rule": NORMALIZATION_SEMANTIC_RULE,
        "scope_limit": NORMALIZATION_SCOPE_LIMIT,
        "operation_count": len(operations),
        "operations": operations,
        "normalized_bytes": len(normalized),
        "normalized_md5": hashlib.md5(
            normalized, usedforsecurity=False,
        ).hexdigest(),
        "normalized_sha256": hashlib.sha256(normalized).hexdigest(),
    }


def load_direct_normalizations(
    candle_root: Path,
    flyspeck_root: Path,
    manifest: dict[str, Any],
) -> tuple[bytes, dict[str, tuple[dict[str, Any], bytes]]]:
    """Load the direct lane's canonical, versioned normalization authority."""

    contract_path = candle_root / flyspeck_manifest.SOURCE_NORMALIZATION_CONTRACT
    contract_data = contract_path.read_bytes()
    authority = manifest.get("source_normalization_contract", {})
    if (
        authority.get("contract_source")
        != "candle:" + flyspeck_manifest.SOURCE_NORMALIZATION_CONTRACT
        or authority.get("contract_sha256")
        != hashlib.sha256(contract_data).hexdigest()
    ):
        raise ValueError("direct normalization authority identity drift")
    _contract, outputs = flyspeck_normalize.evaluate_contract(
        contract_path, flyspeck_root,
    )
    result: dict[str, tuple[dict[str, Any], bytes]] = {}
    for entry, normalized in outputs:
        source_key = str(entry["source_key"])
        node = manifest.get("source_nodes", {}).get(source_key)
        recorded = None if not isinstance(node, dict) else node.get(
            "execution_normalization"
        )
        expected = {
            "id": entry["id"],
            "kind": "exact_bytes_replace_sequence",
            "operation_count": len(entry["operations"]),
            "normalized_bytes": len(normalized),
            "normalized_sha256": entry["normalized_sha256"],
            "normalized_md5": entry["normalized_md5"],
        }
        if recorded != expected:
            raise ValueError(
                f"direct manifest normalization summary drift: {source_key}"
            )
        result[source_key] = (entry, normalized)
    return contract_data, result


def apply_recorded_normalization(
    source_key: str,
    source: bytes,
    node: dict[str, Any],
    direct_normalizations: dict[str, tuple[dict[str, Any], bytes]],
) -> tuple[bytes, dict[str, Any] | None]:
    """Reproduce and validate a closure node's normalization contract."""

    normalized, observed = _normalization_record(
        source_key, source, direct_normalizations,
    )
    record = node.get("normalization")
    if observed is None:
        if record is not None:
            raise ValueError(f"spurious source normalization: {source_key}")
        return source, None
    if not isinstance(record, dict):
        raise ValueError(f"missing source normalization: {source_key}")
    if record != observed:
        raise ValueError(f"source normalization contract drift: {source_key}")
    return normalized, record


def _load_direct_manifest(candle_root: Path) -> tuple[bytes, dict[str, Any]]:
    data = (candle_root / MANIFEST).read_bytes()
    manifest = json.loads(data)
    if manifest.get("schema") != 1:
        raise ValueError("unsupported direct Flyspeck manifest schema")
    nodes = manifest.get("source_nodes")
    if not isinstance(nodes, dict):
        raise ValueError("direct Flyspeck manifest has no source-node map")
    return data, manifest


def build_closure(candle_root: Path, flyspeck_root: Path) -> dict[str, Any]:
    candle_root = candle_root.resolve()
    flyspeck_root = flyspeck_root.resolve()
    manifest_data, manifest = _load_direct_manifest(candle_root)
    normalization_contract_data, direct_normalizations = (
        load_direct_normalizations(candle_root, flyspeck_root, manifest)
    )
    expected_flyspeck_head = manifest["repositories"]["flyspeck"]["commit"]
    observed_flyspeck_head = _git_head(flyspeck_root)
    if observed_flyspeck_head != expected_flyspeck_head:
        raise ValueError(
            "formal-verifier Flyspeck head differs from the direct manifest"
        )

    resolver = flyspeck_manifest.Resolver(candle_root, flyspeck_root)
    pending = [VERIFIER_ROOT]
    discovery_order: list[str] = []
    nodes: dict[str, dict[str, Any]] = {}
    compatibility_uses: list[dict[str, Any]] = []
    toplevel_compatibility_uses: list[dict[str, Any]] = []
    compatibility_modules = (
        set(flyspeck_manifest.OCAML_COMPATIBILITY_SUPPORTED_MEMBERS)
        | set(flyspeck_manifest.STATIC_RUNTIME_LIBRARIES.values())
        | set(flyspeck_manifest.TOPLEVEL_INTERFACE_MODULES)
    )
    while pending:
        source_ref = pending.pop(0)
        if source_ref.key in nodes:
            continue
        source_path = resolver.path(source_ref)
        if not source_path.is_file() or source_path.is_symlink():
            raise ValueError(
                f"formal-verifier source is not an ordinary file: {source_ref.key}"
            )
        source_data = source_path.read_bytes()
        text = source_data.decode("utf-8", errors="surrogateescape")
        for use in flyspeck_manifest.scan_qualified_module_uses(
            text, compatibility_modules,
        ):
            compatibility_uses.append({"source": source_ref.key, **use})
        if source_ref.repository == "flyspeck":
            for use in flyspeck_manifest.scan_identifier_uses(
                text,
                flyspeck_manifest.OCAML_TOPLEVEL_COMPATIBILITY_MEMBERS,
            ):
                toplevel_compatibility_uses.append({
                    "source": source_ref.key, **use,
                })
        dependencies: list[dict[str, Any]] = []
        selected_keys: list[str] = []
        for call in flyspeck_manifest.scan_load_calls(text):
            kind = str(call["kind"])
            line = int(call["line"])
            literal = call.get("literal")
            if kind == "#load":
                if not isinstance(literal, str):
                    raise ValueError(
                        f"dynamic #load in formal-verifier closure: "
                        f"{source_ref.key}:{line}"
                    )
                dependencies.append({
                    "kind": kind,
                    "line": line,
                    "literal": literal,
                    "status": "runtime-library",
                    "syntax_position": call["syntax_position"],
                })
                continue
            if not isinstance(literal, str):
                raise ValueError(
                    f"dynamic source dependency in formal-verifier closure: "
                    f"{source_ref.key}:{line}"
                )
            matches, error = resolver.resolve(literal)
            if error is not None:
                raise ValueError(
                    f"forbidden formal-verifier dependency: "
                    f"{source_ref.key}:{line}: {error}"
                )
            if len(matches) != 1:
                raise ValueError(
                    f"formal-verifier dependency is not uniquely resolved: "
                    f"{source_ref.key}:{line}: {literal}: "
                    f"{[match.key for match in matches]}"
                )
            selected = matches[0]
            dependencies.append({
                "kind": kind,
                "line": line,
                "literal": literal,
                "selected": selected.key,
                "status": "resolved",
                "syntax_position": call["syntax_position"],
                "lookup": resolver.selected_lookup(literal, selected),
            })
            selected_keys.append(selected.key)
            pending.append(selected)

        discovery_order.append(source_ref.key)
        normalized_data, normalization = _normalization_record(
            source_ref.key, source_data, direct_normalizations,
        )
        node = {
            "repository": source_ref.repository,
            "logical_relative_path": source_ref.path,
            "bytes": len(source_data),
            "md5": _digest(source_path, "md5"),
            "sha256": _digest(source_path, "sha256"),
            "dependencies": dependencies,
            "selected_dependencies": sorted(set(selected_keys)),
        }
        if normalization is not None:
            node["normalization"] = normalization
        nodes[source_ref.key] = node

    direct_nodes = set(manifest["source_nodes"])
    selected_nodes = set(nodes)
    extension_nodes = sorted(selected_nodes - direct_nodes)
    overlap_nodes = sorted(selected_nodes & direct_nodes)
    repository_counts = {
        repository: sum(
            node["repository"] == repository for node in nodes.values()
        )
        for repository in ("candle", "flyspeck")
    }
    extension_repository_counts = {
        repository: sum(
            nodes[key]["repository"] == repository for key in extension_nodes
        )
        for repository in ("candle", "flyspeck")
    }
    identity_extension = [
        {
            "source_key": key,
            "repository": nodes[key]["repository"],
            "logical_relative_path": nodes[key]["logical_relative_path"],
            "md5": nodes[key]["md5"],
            "sha256": nodes[key]["sha256"],
        }
        for key in extension_nodes
    ]
    supported_members = {
        **flyspeck_manifest.OCAML_COMPATIBILITY_SUPPORTED_MEMBERS,
        **{
            module: flyspeck_manifest.STATIC_RUNTIME_MEMBERS[module]
            for _library, module
            in flyspeck_manifest.STATIC_RUNTIME_LIBRARIES.items()
        },
        **flyspeck_manifest.TOPLEVEL_INTERFACE_SOURCE_MEMBERS,
    }
    sorted_compatibility_uses = sorted(
        compatibility_uses,
        key=lambda use: (
            str(use["source"]), int(use["line"]),
            str(use["module"]), str(use["member"]),
        ),
    )
    unsupported_compatibility_uses = [
        use for use in sorted_compatibility_uses
        if str(use["member"]) not in supported_members[str(use["module"])]
    ]
    sorted_toplevel_compatibility_uses = sorted(
        toplevel_compatibility_uses,
        key=lambda use: (
            str(use["source"]), int(use["line"]), str(use["identifier"]),
        ),
    )
    return {
        "schema": SCHEMA,
        "kind": "candle-flyspeck-nonlinear-verifier-source-closure",
        "status": "development-non-release",
        "claim": (
            "exact recursive literal source closure for "
            "M_verifier_main.verify_ineq; not direct-run or release evidence"
        ),
        "root": VERIFIER_ROOT.key,
        "repositories": {
            "candle": {"identity": "closure-owning-tree"},
            "flyspeck": {"commit": observed_flyspeck_head},
        },
        "direct_manifest": {
            "path": MANIFEST.as_posix(),
            "schema": manifest["schema"],
            "sha256": hashlib.sha256(manifest_data).hexdigest(),
            "source_node_count": len(direct_nodes),
        },
        "source_normalization_contract": {
            "path": flyspeck_manifest.SOURCE_NORMALIZATION_CONTRACT,
            "schema": 2,
            "sha256": hashlib.sha256(
                normalization_contract_data,
            ).hexdigest(),
        },
        "counts": {
            "selected_source_nodes": len(selected_nodes),
            "selected_source_edges": sum(
                len(node["selected_dependencies"]) for node in nodes.values()
            ),
            "selected_by_repository": repository_counts,
            "already_in_direct_manifest": len(overlap_nodes),
            "identity_extension": len(extension_nodes),
            "identity_extension_by_repository": extension_repository_counts,
            "normalized_sources": sum(
                "normalization" in node for node in nodes.values()
            ),
            "normalization_operations": sum(
                node.get("normalization", {}).get("operation_count", 0)
                for node in nodes.values()
            ),
        },
        "discovery_order": discovery_order,
        "direct_manifest_overlap": overlap_nodes,
        "identity_extension": identity_extension,
        "compatibility": {
            "qualified_use_count": len(sorted_compatibility_uses),
            "qualified_member_count": len({
                (str(use["module"]), str(use["member"]))
                for use in sorted_compatibility_uses
            }),
            "unsupported_use_count": len(unsupported_compatibility_uses),
            "unsupported_uses": unsupported_compatibility_uses,
            "qualified_uses": sorted_compatibility_uses,
            "toplevel_use_count": len(sorted_toplevel_compatibility_uses),
            "toplevel_members": sorted(
                flyspeck_manifest.OCAML_TOPLEVEL_COMPATIBILITY_MEMBERS
            ),
            "toplevel_uses": sorted_toplevel_compatibility_uses,
        },
        "source_nodes": {key: nodes[key] for key in sorted(nodes)},
        "integration_policy": {
            "source_authority": (
                "repository identity + logical relative path + exact hashes"
            ),
            "runtime_requirement": (
                "all extension identities must be authenticated before any new "
                "source is parsed or evaluated"
            ),
            "forbidden_shortcuts": [
                "basename-only authorization",
                "absolute-path-only identity",
                "unmanifested #use",
                "changed bytes under an approved path",
                "partial-state reuse after a failed source load",
            ],
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
    rendered = _render(build_closure(ROOT, arguments.flyspeck_root))
    output = ROOT / OUTPUT
    if arguments.write:
        output.write_text(rendered, encoding="utf-8")
    elif not output.is_file() or output.read_text(encoding="utf-8") != rendered:
        raise SystemExit(
            f"stale nonlinear verifier closure: run {Path(__file__).name} --write"
        )


if __name__ == "__main__":
    main()
