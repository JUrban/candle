#!/usr/bin/env python3
"""Generate the pinned direct-source Flyspeck dependency inventory.

This is a conservative OCaml/HOL Light source scanner, not the eventual
verified loader.  It extracts the authoritative full build sequence, follows
literal source-loading calls under the recorded load-path order, and makes
every non-literal, missing, ambiguous, or forbidden dependency explicit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path


SCHEMA = 1
LOAD_NAMES = ("needs", "loads", "loadt", "flyspeck_needs", "rflyspeck_needs", "reneeds")
LOAD_RE = re.compile(r"\b(" + "|".join(LOAD_NAMES) + r")\b")
DIRECTIVE_RE = re.compile(r"#\s*(use|load)\b")
BUILD_SEQUENCE_RE = re.compile(r"\blet\s+build_sequence_full\s*=\s*\[")
DEFINITION_PREFIX_RE = re.compile(r"(?:\blet|\band)\s+(?:rec\s+)?$")
GENERATED_INPUT_GLOBS = (
    "formal_lp/glpk/binary/easy*",
    "formal_lp/glpk/binary/hard*",
)
NAMED_INPUTS = (
    ("lp-archive", "formal_graph/archive/archive_all.ml"),
    ("nonlinear-preparation", "text_formalization/nonlinear/prep.hl"),
    ("nonlinear-case-log", "text_formalization/nonlinear/break_case_log.hl"),
)
KNOWN_GENERATED_DEPENDENCIES = {
    "candle/build/insulate.ml": {
        "generator": "candle/insulate.py",
        "runtime_input": "candle/build/types.txt",
        "recipe": "build-instructions.sh",
    },
}
MANUAL_DYNAMIC_REVIEWS = {
    ("candle:candle/flyspeck_loader.ml", 36, "flyspeck_needs"): {
        "status": "root-driver",
        "reason": "maps the separately extracted authoritative full build sequence",
    },
    ("flyspeck:formal_lp/glpk/lpproc.ml", 53, "needs"): {
        "status": "resolved-dynamic",
        "targets": ["../formal_lp/glpk/glpk_link.ml"],
        "reason": "glpk_dir is pinned Flyspeck repository path",
    },
    ("flyspeck:formal_lp/glpk/lpproc.ml", 54, "needs"): {
        "status": "resolved-dynamic",
        "targets": ["../formal_graph/archive/archive_all.ml"],
        "reason": "project_root_dir is pinned Flyspeck repository path",
    },
    ("flyspeck:load_flyspeck.ml", 12, "needs"): {
        "status": "resolved-dynamic",
        "targets": ["build/strictbuild.hl"],
        "reason": "flyspeck_dir is the manifest text_formalization root",
    },
    ("flyspeck:load_flyspeck.ml", 18, "flyspeck_needs"): {
        "status": "root-driver",
        "reason": "seq0 is a prefix of the separately extracted authoritative build sequence",
    },
    ("flyspeck:text_formalization/build/strictbuild.hl", 103, "loadt"): {
        "status": "resolved-dynamic",
        "targets": ["general/parser_verbose.hl"],
        "reason": "flyspeckpath prefixes the pinned text_formalization root",
    },
    ("flyspeck:text_formalization/build/strictbuild.hl", 104, "loadt"): {
        "status": "resolved-dynamic",
        "targets": ["general/debug.hl"],
        "reason": "flyspeckpath prefixes the pinned text_formalization root",
    },
    ("flyspeck:text_formalization/build/strictbuild.hl", 139, "loadt"): {
        "status": "loader-definition",
        "reason": "implementation of the literal needs wrapper; not an invocation",
    },
    ("flyspeck:text_formalization/build/strictbuild.hl", 167, "loadt"): {
        "status": "resolved-dynamic",
        "targets": ["general/state_manager.hl"],
        "reason": "flyspeckpath prefixes the pinned text_formalization root",
    },
    ("flyspeck:text_formalization/build/strictbuild.hl", 168, "loadt"): {
        "status": "loader-definition",
        "reason": "definition of reneeds; call targets are reviewed at invocations",
    },
    ("flyspeck:text_formalization/build/strictbuild.hl", 169, "reneeds"): {
        "status": "function-alias",
        "reason": "rflyspeck_needs aliases reneeds without invoking it",
    },
    ("flyspeck:text_formalization/build/strictbuild.hl", 246, "flyspeck_needs"): {
        "status": "root-driver",
        "reason": "maps the separately extracted main build sequence",
    },
    ("flyspeck:text_formalization/build/strictbuild.hl", 253, "flyspeck_needs"): {
        "status": "root-driver",
        "reason": "do_build argument is constrained by the loader build-mode manifest",
    },
    ("flyspeck:text_formalization/build/strictbuild.hl", 276, "flyspeck_needs"): {
        "status": "root-driver",
        "reason": "maps a loader-selected build list; no independent source target",
    },
    ("flyspeck:text_formalization/general/flyspeck_lib.hl", 15, "needs"): {
        "status": "resolved-dynamic",
        "targets": ["general/flyspeck_eval_4.14.hl"],
        "reason": "v1.3 pins the OCaml 4.14.1 compatibility branch",
    },
    ("flyspeck:text_formalization/general/hol_pervasives.hl", 25, "loadt"): {
        "status": "loader-definition",
        "reason": "implementation of Hol_pervasives.needs; not an invocation",
    },
    ("flyspeck:text_formalization/general/serialization.hl", 499, "needs"): {
        "status": "generated-runtime",
        "reason": "digest_file is a temporary theorem-digest module written by save_all",
        "open_gate": "versioned generated-input/checkpoint schema and atomic lifecycle",
    },
}


@dataclass(frozen=True)
class SourceRef:
    repository: str
    path: str

    @property
    def key(self) -> str:
        return f"{self.repository}:{self.path}"


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def _git_head(root: Path) -> str:
    return subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=root,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    ).stdout.strip()


def _require_git_clean(root: Path) -> None:
    status = subprocess.run(
        ["git", "status", "--porcelain"],
        cwd=root,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    ).stdout
    if status:
        raise ValueError(f"source repository is dirty: {root}")


def strip_ocaml_comments(source: str) -> str:
    """Replace nested OCaml comments with spaces while preserving locations."""
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
        raise ValueError("unterminated OCaml comment")
    if in_string:
        raise ValueError("unterminated OCaml string")
    if in_quote:
        raise ValueError("unterminated HOL quotation")
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
            raise ValueError("unterminated string escape")
        escaped = source[index]
        replacements = {"n": "\n", "r": "\r", "t": "\t", "\\": "\\", '"': '"'}
        if escaped in replacements:
            value.append(replacements[escaped])
            index += 1
        elif escaped.isdigit() and index + 2 < len(source) and source[index:index + 3].isdigit():
            value.append(chr(int(source[index:index + 3], 10)))
            index += 3
        else:
            value.append(escaped)
            index += 1
    raise ValueError("unterminated OCaml string")


def _skip_space(source: str, index: int) -> int:
    while index < len(source) and source[index].isspace():
        index += 1
    return index


def _code_mask(source: str) -> str:
    """Mask string and HOL-quotation bodies so names inside data do not match."""
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


def extract_full_build_sequence(source: str) -> list[str]:
    clean = strip_ocaml_comments(source)
    match = BUILD_SEQUENCE_RE.search(clean)
    if not match:
        raise ValueError("build_sequence_full list not found")
    index = match.end()
    result: list[str] = []
    while index < len(clean):
        index = _skip_space(clean, index)
        if clean.startswith(";;", index):
            index += 2
            continue
        if clean[index] == "]":
            return result
        parsed = _string_at(clean, index)
        if parsed is None:
            raise ValueError(
                f"non-literal build_sequence_full entry at line {clean.count(chr(10), 0, index) + 1}"
            )
        value, index = parsed
        result.append(value)
        index = _skip_space(clean, index)
        if index < len(clean) and clean[index] == ";":
            index += 1
    raise ValueError("unterminated build_sequence_full list")


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


def scan_load_calls(source: str) -> list[dict[str, object]]:
    clean = strip_ocaml_comments(source)
    mask = _code_mask(clean)
    matches: list[tuple[re.Match[str], str]] = [
        (match, match.group(1)) for match in LOAD_RE.finditer(mask)
    ]
    matches.extend((match, f"#{match.group(1)}") for match in DIRECTIVE_RE.finditer(mask))
    calls: list[dict[str, object]] = []
    for match, kind in sorted(matches, key=lambda item: item[0].start()):
        prefix = clean[max(0, match.start() - 24):match.start()]
        if DEFINITION_PREFIX_RE.search(prefix):
            continue
        literal, end = _call_argument(clean, match.end())
        line = clean.count("\n", 0, match.start()) + 1
        if literal is not None:
            calls.append({"kind": kind, "line": line, "literal": literal})
        else:
            expression_end = clean.find(";;", match.end())
            if expression_end < 0:
                expression_end = clean.find("\n", match.end())
            if expression_end < 0:
                expression_end = min(len(clean), match.end() + 160)
            expression = " ".join(clean[match.start():expression_end].split())[:160]
            calls.append({"kind": kind, "line": line, "expression": expression})
    return calls


class Resolver:
    def __init__(self, candle_root: Path, flyspeck_root: Path):
        self.candle_root = candle_root.resolve()
        self.flyspeck_root = flyspeck_root.resolve()
        self.search_roots = (
            self.flyspeck_root / "text_formalization",
            self.flyspeck_root / "formal_ineqs",
            self.flyspeck_root / "jHOLLight",
            self.candle_root,
        )

    def path(self, ref: SourceRef) -> Path:
        root = self.candle_root if ref.repository == "candle" else self.flyspeck_root
        return root / ref.path

    def ref(self, path: Path) -> SourceRef:
        resolved = path.resolve()
        try:
            return SourceRef("candle", resolved.relative_to(self.candle_root).as_posix())
        except ValueError:
            return SourceRef("flyspeck", resolved.relative_to(self.flyspeck_root).as_posix())

    def resolve(self, target: str) -> tuple[list[SourceRef], str | None]:
        if os.path.isabs(target):
            return [], "absolute source dependency"
        matches: list[SourceRef] = []
        for root in self.search_roots:
            candidate = (root / target).resolve()
            if not candidate.is_file():
                continue
            if not (candidate.is_relative_to(self.candle_root) or candidate.is_relative_to(self.flyspeck_root)):
                return [], "source dependency escapes pinned repositories"
            ref = self.ref(candidate)
            if ref not in matches:
                matches.append(ref)
        return matches, None


def _cycles(edges: dict[str, list[str]]) -> list[list[str]]:
    found: list[list[str]] = []
    active: list[str] = []
    active_set: set[str] = set()
    done: set[str] = set()

    def visit(node: str) -> None:
        if node in done:
            return
        if node in active_set:
            start = active.index(node)
            cycle = active[start:] + [node]
            if cycle not in found:
                found.append(cycle)
            return
        active.append(node)
        active_set.add(node)
        for child in edges.get(node, []):
            visit(child)
        active.pop()
        active_set.remove(node)
        done.add(node)

    for node in sorted(edges):
        visit(node)
    return found


def build_manifest(candle_root: Path, flyspeck_root: Path) -> dict[str, object]:
    _require_git_clean(flyspeck_root)
    resolver = Resolver(candle_root, flyspeck_root)
    build_file = flyspeck_root / "text_formalization/build/build.hl"
    sequence = extract_full_build_sequence(build_file.read_text(encoding="utf-8"))

    bootstrap = [
        SourceRef("candle", "hol.ml"),
        SourceRef("flyspeck", "load_flyspeck.ml"),
        SourceRef("flyspeck", "text_formalization/build/strictbuild.hl"),
        SourceRef("flyspeck", "text_formalization/build/build.hl"),
    ]
    loader_source = SourceRef("candle", "candle/flyspeck_loader.ml")
    final_target = SourceRef("candle", "candle/flyspeck_l2_target.ml")
    roots = list(bootstrap)
    build_roots: list[dict[str, object]] = []
    unresolved_roots: list[dict[str, object]] = []
    for index, target in enumerate(sequence):
        matches, error = resolver.resolve(target)
        if error or not matches:
            root_entry = {"index": index, "target": target, "status": error or "missing"}
            build_roots.append(root_entry)
            unresolved_roots.append(root_entry)
        else:
            roots.append(matches[0])
            root_entry = {
                "index": index,
                "target": target,
                "status": "resolved" if len(matches) == 1 else "ambiguous",
                "selected": matches[0].key,
            }
            build_roots.append(root_entry)
            if len(matches) > 1:
                root_entry["matches"] = [match.key for match in matches]
                unresolved_roots.append(root_entry)
    roots.append(loader_source)

    pending = list(dict.fromkeys(roots))
    nodes: dict[str, dict[str, object]] = {}
    edges: dict[str, list[str]] = {}
    while pending:
        ref = pending.pop(0)
        if ref.key in nodes:
            continue
        path = resolver.path(ref)
        text = path.read_text(encoding="utf-8", errors="surrogateescape")
        dependencies: list[dict[str, object]] = []
        edge_targets: list[str] = []
        try:
            calls = scan_load_calls(text)
        except ValueError as error:
            raise ValueError(f"{ref.key}: {error}") from error
        for call in calls:
            dependency = dict(call)
            literal = call.get("literal")
            if not isinstance(literal, str):
                review = MANUAL_DYNAMIC_REVIEWS.get((ref.key, int(call["line"]), str(call["kind"])))
                if review is None:
                    dependency["status"] = "dynamic"
                else:
                    dependency.update(review)
                    selected_targets: list[str] = []
                    for target in review.get("targets", []):
                        matches, error = resolver.resolve(str(target))
                        if error or not matches:
                            raise ValueError(
                                f"reviewed dynamic dependency no longer resolves: {ref.key}:{call['line']} {target}"
                            )
                        selected_targets.append(matches[0].key)
                        edge_targets.append(matches[0].key)
                        pending.append(matches[0])
                    if selected_targets:
                        dependency["selected_targets"] = selected_targets
            elif call["kind"] == "#load":
                dependency["status"] = "runtime-library"
            else:
                matches, error = resolver.resolve(literal)
                if error:
                    dependency.update(status="forbidden", error=error)
                elif not matches:
                    generated = KNOWN_GENERATED_DEPENDENCIES.get(literal)
                    if generated is None:
                        dependency["status"] = "missing"
                    else:
                        dependency.update(status="generated-missing", generation=generated)
                else:
                    selected = matches[0]
                    dependency.update(
                        status="resolved" if len(matches) == 1 else "ambiguous",
                        selected=selected.key,
                        matches=[match.key for match in matches],
                    )
                    edge_targets.append(selected.key)
                    pending.append(selected)
            dependencies.append(dependency)
        edges[ref.key] = sorted(set(edge_targets))
        nodes[ref.key] = {
            "repository": ref.repository,
            "path": ref.path,
            "bytes": path.stat().st_size,
            "sha256": _sha256(path),
            "dependencies": dependencies,
        }

    generated_inputs: list[dict[str, object]] = []
    generated_paths: set[Path] = set()
    for pattern in GENERATED_INPUT_GLOBS:
        generated_paths.update(flyspeck_root.glob(pattern))
    for path in sorted(generated_paths):
        generated_inputs.append({
            "class": "lp-certificate",
            "path": path.relative_to(flyspeck_root).as_posix(),
            "bytes": path.stat().st_size,
            "sha256": _sha256(path),
        })
    for input_class, relative in NAMED_INPUTS:
        path = flyspeck_root / relative
        generated_inputs.append({
            "class": input_class,
            "path": relative,
            "bytes": path.stat().st_size,
            "sha256": _sha256(path),
        })

    diagnostics = {
        "unresolved_build_roots": unresolved_roots,
        "dynamic_dependencies": sum(
            1 for node in nodes.values() for dep in node["dependencies"] if dep["status"] == "dynamic"
        ),
        "reviewed_dynamic_dependencies": sum(
            1
            for node in nodes.values()
            for dep in node["dependencies"]
            if dep["status"] in {
                "resolved-dynamic", "root-driver", "loader-definition",
                "function-alias", "generated-runtime",
            }
        ),
        "missing_dependencies": sum(
            1 for node in nodes.values() for dep in node["dependencies"] if dep["status"] == "missing"
        ),
        "generated_dependencies": sum(
            1
            for node in nodes.values()
            for dep in node["dependencies"]
            if dep["status"] == "generated-missing"
        ),
        "ambiguous_dependencies": sum(
            1 for node in nodes.values() for dep in node["dependencies"] if dep["status"] == "ambiguous"
        ),
        "forbidden_dependencies": sum(
            1 for node in nodes.values() for dep in node["dependencies"] if dep["status"] == "forbidden"
        ),
        "cycles": _cycles(edges),
    }
    sequence_positions: dict[str, list[int]] = {}
    for index, target in enumerate(sequence):
        sequence_positions.setdefault(target, []).append(index)
    duplicates = {
        target: positions
        for target, positions in sorted(sequence_positions.items())
        if len(positions) > 1
    }
    generated_dependency_contracts = []
    for source_key, node in sorted(nodes.items()):
        for dependency in node["dependencies"]:
            if dependency["status"] not in {"generated-missing", "generated-runtime"}:
                continue
            generated_dependency_contracts.append({
                "source": source_key,
                **dependency,
            })
    return {
        "schema": SCHEMA,
        "claim": "G6 source inventory only; not loader execution evidence",
        "build_mode": "full",
        "repositories": {
            "candle": {
                "identity": "manifest-owning-tree",
                "note": "pinned externally to avoid a self-referential commit hash",
            },
            "flyspeck": {"commit": _git_head(flyspeck_root)},
        },
        "load_path_order": [
            "flyspeck:text_formalization",
            "flyspeck:formal_ineqs",
            "flyspeck:jHOLLight",
            "candle:.",
        ],
        "build_sequence_source": {
            "path": "flyspeck:text_formalization/build/build.hl",
            "sha256": _sha256(build_file),
        },
        "build_sequence_count": len(sequence),
        "build_sequence_unique_count": len(sequence_positions),
        "build_sequence_duplicates": duplicates,
        "build_sequence": sequence,
        "build_sequence_roots": build_roots,
        "bootstrap_roots": [ref.key for ref in bootstrap],
        "loader": {
            "source": loader_source.key,
            "required_build_mode": "full",
            "configuration_bindings": [
                "candle_flyspeck_root", "candle_flyspeck_build_mode",
            ],
            "success_marker": "CANDLE_FLYSPECK_DIRECT_FULL_OK",
        },
        "final_target": {
            "source": final_target.key,
            "name": "Candle_flyspeck_l2.tame_imp_kepler_conjecture",
            "statement": "import_tame_classification ==> the_kepler_conjecture",
            "imported_premises": ["import_tame_classification"],
        },
        "source_node_count": len(nodes),
        "source_edge_count": sum(len(targets) for targets in edges.values()),
        "source_nodes": {key: nodes[key] for key in sorted(nodes)},
        "generated_inputs": generated_inputs,
        "generated_dependency_contracts": generated_dependency_contracts,
        "diagnostics": diagnostics,
    }


def _render(payload: dict[str, object]) -> str:
    return json.dumps(payload, indent=2, sort_keys=True) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--flyspeck-root", type=Path, required=True)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--write", action="store_true")
    action.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    candle_root = Path(__file__).resolve().parents[1]
    manifest_path = candle_root / "candle/flyspeck_manifest.json"
    rendered = _render(build_manifest(candle_root, arguments.flyspeck_root.resolve()))
    if arguments.write:
        manifest_path.write_text(rendered, encoding="utf-8")
    elif not manifest_path.is_file() or manifest_path.read_text(encoding="utf-8") != rendered:
        raise SystemExit(f"stale manifest: run {Path(__file__).name} --write")
    payload = json.loads(rendered)
    print(
        f"manifest ok: {payload['build_sequence_count']} roots, "
        f"{payload['source_node_count']} source nodes, "
        f"{len(payload['generated_inputs'])} generated inputs"
    )


if __name__ == "__main__":
    main()
