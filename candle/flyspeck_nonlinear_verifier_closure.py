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
import subprocess
from pathlib import Path
from typing import Any

import flyspeck_manifest


SCHEMA = 1
ROOT = Path(__file__).resolve().parents[1]
MANIFEST = Path("candle/flyspeck_manifest.json")
OUTPUT = Path("candle/flyspeck_nonlinear_verifier_closure.json")
VERIFIER_ROOT = flyspeck_manifest.SourceRef(
    "flyspeck", "formal_ineqs/verifier/m_verifier_main.hl",
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
        text = source_path.read_text(
            encoding="utf-8", errors="surrogateescape",
        )
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
        nodes[source_ref.key] = {
            "repository": source_ref.repository,
            "logical_relative_path": source_ref.path,
            "bytes": source_path.stat().st_size,
            "md5": _digest(source_path, "md5"),
            "sha256": _digest(source_path, "sha256"),
            "dependencies": dependencies,
            "selected_dependencies": sorted(set(selected_keys)),
        }

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
        "counts": {
            "selected_source_nodes": len(selected_nodes),
            "selected_source_edges": sum(
                len(node["selected_dependencies"]) for node in nodes.values()
            ),
            "selected_by_repository": repository_counts,
            "already_in_direct_manifest": len(overlap_nodes),
            "identity_extension": len(extension_nodes),
            "identity_extension_by_repository": extension_repository_counts,
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
