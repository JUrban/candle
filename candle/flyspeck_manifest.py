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
SOURCE_DIGEST_PROGRAM = "candle/flyspeck_source_digests.ml"
SOURCE_DIGEST_EXCLUSIONS = {"candle:candle/flyspeck_loader.ml"}
LOAD_NAMES = ("needs", "loads", "loadt", "flyspeck_needs", "rflyspeck_needs", "reneeds")
LOAD_RE = re.compile(r"\b(" + "|".join(LOAD_NAMES) + r")\b")
DIRECTIVE_RE = re.compile(r"#\s*(use|load)\b")
BUILD_SEQUENCE_RE = re.compile(r"\blet\s+build_sequence_full\s*=\s*\[")
DEFINITION_PREFIX_RE = re.compile(r"(?:\blet|\band)\s+(?:rec\s+)?$")
STATIC_RUNTIME_LIBRARIES = {
    "str.cma": "Str",
    "unix.cma": "Unix",
}
STATIC_RUNTIME_MEMBERS = {
    "Str": {
        "first_chars", "global_replace", "regexp", "split", "string_match",
    },
    "Unix": {
        "close_process", "close_process_in", "gettimeofday", "mkdir",
        "open_process", "open_process_in",
    },
}
OCAML_COMPATIBILITY_SUPPORTED_MEMBERS = {
    "Digest": {"compare", "file", "string", "t", "to_hex"},
}
TOPLEVEL_INTERFACE_MODULES = {"Format", "Lexing", "Obj", "Toploop"}
TOPLEVEL_INTERFACE_SOURCE_MEMBERS = {
    "Format": {
        "close_box", "formatter", "open_box", "open_hbox", "open_hvbox",
        "open_vbox", "pp_close_box", "pp_get_max_boxes", "pp_open_box",
        "pp_open_hbox", "pp_open_hvbox", "pp_open_vbox", "pp_print_as",
        "pp_print_break", "pp_print_newline", "pp_print_space",
        "pp_print_string", "pp_set_max_boxes", "print_break", "print_flush",
        "print_newline", "print_space", "print_string", "set_margin",
        "set_max_boxes",
    },
    "Lexing": set(),
    "Obj": set(),
    "Toploop": set(),
}
# These are source-program constructors passed to [exec] in the pinned 4.x
# update-database branch.  Ordinary qualified-use scanning intentionally masks
# strings, so the dynamic program boundary needs a separate explicit contract.
DYNAMIC_TOPLEVEL_PAYLOADS = (
    {
        "source": "flyspeck:text_formalization/general/update_database_400.ml",
        "line": 60,
        "purpose": "declare version-dependent type_expr family",
    },
    {
        "source": "flyspeck:text_formalization/general/update_database_400.ml",
        "line": 134,
        "purpose": "declare version-dependent env_t record",
    },
    {
        "source": "flyspeck:text_formalization/general/update_database_400.ml",
        "line": 186,
        "purpose": "evaluate a theorem identifier into buf__",
    },
    {
        "source": "flyspeck:text_formalization/general/update_database_400.ml",
        "line": 193,
        "purpose": "declare update_database with top-level environment enumeration",
    },
)
# Operational checkpoint strata for the authoritative full sequence.  These
# names are intentionally contiguous load-order partitions, not claims that a
# source file has dependencies in only one mathematical area.  Transitive
# source nodes below record every stratum from which they are reachable.
BUILD_STRATA = (
    {
        "name": "base",
        "start": 0,
        "end": 29,
        "first": "general/hol_pervasives.hl",
        "last": "general/vukhacky_tactics.hl",
    },
    {
        "name": "arithmetic",
        "start": 30,
        "end": 37,
        "first": "trigonometry/trig1.hl",
        "last": "trigonometry/HVIHVEC.hl",
    },
    {
        "name": "nonlinear_support",
        "start": 38,
        "end": 49,
        "first": "nonlinear/calc_derivative.hl",
        "last": "nonlinear/merge_ineq.hl",
    },
    {
        "name": "analysis",
        "start": 50,
        "end": 60,
        "first": "volume/vol1.hl",
        "last": "fan/polyhedron.hl",
    },
    {
        "name": "geometry",
        "start": 61,
        "end": 151,
        "first": "packing/pack1.hl",
        "last": "local/lp_details.hl",
    },
    {
        "name": "lp_support",
        "start": 152,
        "end": 184,
        "first": "../formal_lp/hypermap/arith_link.hl",
        "last": "tame/linear_programming_results.hl",
    },
    {
        "name": "text_formalization",
        "start": 185,
        "end": 290,
        "first": "local/ZITHLQN.hl",
        "last": "packing/flyspeck_devol.hl",
    },
    {
        "name": "final_assembly",
        "start": 291,
        "end": 296,
        "first": "general/kepler_spec.hl",
        "last": "nonlinear/mk_all_ineq.hl",
    },
)
# Complete OCaml Str names that can be conservatively attributed after
# [open Str].  Qualified use scanning does not need this list because it
# records every member following [Str.].  There is no reachable [open Unix].
OPENED_MODULE_EXPORTS = {
    "Str": {
        "bounded_full_split", "bounded_split", "bounded_split_delim",
        "first_chars", "full_split", "global_replace", "global_substitute",
        "group_beginning", "group_end", "last_chars", "match_beginning",
        "match_end", "matched_group", "matched_string", "quote", "regexp",
        "regexp_case_fold", "regexp_string", "regexp_string_case_fold",
        "replace_first", "search_backward", "search_forward", "split",
        "split_delim", "string_after", "string_before", "string_match",
        "string_partial_match", "substitute_first",
    },
    "Unix": STATIC_RUNTIME_MEMBERS["Unix"],
}
PROMOTION_EMPTY_DIAGNOSTICS = (
    "unresolved_build_roots",
    "cycles",
    "unsupported_runtime_libraries",
    "unsupported_runtime_members",
    "unsupported_compatibility_members",
)
PROMOTION_ZERO_DIAGNOSTICS = (
    "dynamic_dependencies",
    "missing_dependencies",
    "ambiguous_dependencies",
    "forbidden_dependencies",
)
GENERATED_INPUT_GLOBS = (
    "formal_lp/glpk/binary/easy*",
    "formal_lp/glpk/binary/hard*",
)
NAMED_INPUTS = (
    ("lp-archive", "formal_graph/archive/archive_all.ml"),
    ("nonlinear-preparation", "text_formalization/nonlinear/prep.hl"),
    ("nonlinear-case-log", "text_formalization/nonlinear/break_case_log.hl"),
)
DETERMINISTIC_PROCESS_INPUTS = (
    ("date", "candle/flyspeck_metadata/date.txt"),
    ("whoami", "candle/flyspeck_metadata/user.txt"),
)
KNOWN_GENERATED_DEPENDENCIES = {
    "candle/build/insulate.ml": {
        "generator": "candle/insulate.py",
        "runtime_input": "candle/build/types.txt",
        "recipe": "build-instructions.sh",
    },
    SOURCE_DIGEST_PROGRAM: {
        "generator": "candle/flyspeck_manifest.py",
        "runtime_input": "candle/flyspeck_manifest.json",
        "recipe": "flyspeck_manifest.py --write",
    },
}
MANUAL_DYNAMIC_REVIEWS = {
    ("candle:candle/flyspeck_loader.ml", 82, "flyspeck_needs"): {
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


def _md5(path: Path) -> str:
    digest = hashlib.md5(usedforsecurity=False)
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


def scan_qualified_module_uses(source: str, modules: set[str]) -> list[dict[str, object]]:
    """Inventory qualified module members in executable OCaml source regions."""
    if not modules:
        return []
    clean = strip_ocaml_comments(source)
    mask = _code_mask(clean)
    qualified = re.compile(
        r"\b(" + "|".join(re.escape(module) for module in sorted(modules))
        + r")\.([A-Za-z_][A-Za-z0-9_']*)\b"
    )
    return [
        {
            "line": clean.count("\n", 0, match.start()) + 1,
            "module": match.group(1),
            "member": match.group(2),
        }
        for match in qualified.finditer(mask)
    ]


def scan_opened_module_uses(
    source: str, module_exports: dict[str, set[str]],
) -> tuple[list[dict[str, object]], list[dict[str, object]]]:
    """Conservatively attribute known unqualified names after module opens."""
    clean = strip_ocaml_comments(source)
    mask = _code_mask(clean)
    module_pattern = "|".join(re.escape(module) for module in sorted(module_exports))
    open_re = re.compile(r"\bopen\s+(" + module_pattern + r")\b")
    opens = [
        {
            "line": clean.count("\n", 0, match.start()) + 1,
            "module": match.group(1),
            "offset": match.start(),
        }
        for match in open_re.finditer(mask)
    ]
    uses: list[dict[str, object]] = []
    for module in sorted(module_exports):
        module_opens = [entry for entry in opens if entry["module"] == module]
        if not module_opens:
            continue
        first_open = min(int(entry["offset"]) for entry in module_opens)
        members = module_exports[module]
        if not members:
            continue
        member_re = re.compile(
            r"\b(" + "|".join(re.escape(member) for member in sorted(members))
            + r")\b"
        )
        for match in member_re.finditer(mask, first_open):
            prefix = mask[:match.start()].rstrip()
            if prefix.endswith("."):
                continue
            uses.append({
                "line": clean.count("\n", 0, match.start()) + 1,
                "module": module,
                "member": match.group(1),
                "qualification": "opened-module",
                "attribution_status": "lexical-reviewed-not-compiler-proved",
                "open_lines": [int(entry["line"]) for entry in module_opens],
            })
    return (
        [{key: value for key, value in entry.items() if key != "offset"} for entry in opens],
        uses,
    )


def promotion_blockers(diagnostics: dict[str, object]) -> list[str]:
    blockers = [
        key for key in PROMOTION_EMPTY_DIAGNOSTICS if diagnostics.get(key) != []
    ]
    blockers.extend(
        key for key in PROMOTION_ZERO_DIAGNOSTICS if diagnostics.get(key) != 0
    )
    return blockers


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


def _build_strata_contract(
    sequence: list[str],
    build_roots: list[dict[str, object]],
    nodes: dict[str, dict[str, object]],
    edges: dict[str, list[str]],
    bootstrap: list[SourceRef],
    loader_source: SourceRef,
) -> tuple[list[dict[str, object]], dict[str, list[str]]]:
    expected_index = 0
    stratum_for_index: dict[int, str] = {}
    contract: list[dict[str, object]] = []
    names = [str(spec["name"]) for spec in BUILD_STRATA]
    for spec in BUILD_STRATA:
        start = int(spec["start"])
        end = int(spec["end"])
        name = str(spec["name"])
        if start != expected_index or end < start:
            raise ValueError(f"non-contiguous build stratum {name}: {start}..{end}")
        if end >= len(sequence):
            raise ValueError(f"build stratum {name} exceeds full sequence")
        if sequence[start] != spec["first"] or sequence[end] != spec["last"]:
            raise ValueError(f"build stratum boundary drifted: {name}")
        rows: list[dict[str, object]] = []
        for index in range(start, end + 1):
            root = build_roots[index]
            selected = root.get("selected")
            if not isinstance(selected, str) or selected not in nodes:
                raise ValueError(f"unresolved stratum root: {name}:{index}")
            rows.append({
                "index": index,
                "target": sequence[index],
                "selected": selected,
                "sha256": nodes[selected]["sha256"],
            })
            stratum_for_index[index] = name
        encoded = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
        contract.append({
            "name": name,
            "start_index": start,
            "end_index": end,
            "entry_count": len(rows),
            "first": sequence[start],
            "last": sequence[end],
            "ordered_root_sha256": hashlib.sha256(encoded).hexdigest(),
        })
        expected_index = end + 1
    if expected_index != len(sequence) or len(stratum_for_index) != len(sequence):
        raise ValueError("build strata do not cover the authoritative full sequence")

    memberships: dict[str, set[str]] = {key: set() for key in nodes}

    def mark_reachable(root: str, name: str) -> None:
        pending = [root]
        seen: set[str] = set()
        while pending:
            node = pending.pop()
            if node in seen:
                continue
            if node not in nodes:
                raise ValueError(f"stratum edge leaves selected graph: {node}")
            seen.add(node)
            memberships[node].add(name)
            pending.extend(edges.get(node, []))

    for root in bootstrap:
        mark_reachable(root.key, "base")
    for index, root in enumerate(build_roots):
        mark_reachable(str(root["selected"]), stratum_for_index[index])
    mark_reachable(loader_source.key, "final_assembly")

    missing = sorted(key for key, membership in memberships.items() if not membership)
    if missing:
        raise ValueError(f"source nodes lack a build stratum: {missing}")
    order = {name: index for index, name in enumerate(names)}
    rendered_memberships = {
        key: sorted(membership, key=order.__getitem__)
        for key, membership in memberships.items()
    }
    for entry in contract:
        name = str(entry["name"])
        entry["transitive_source_node_count"] = sum(
            name in membership for membership in rendered_memberships.values()
        )
    return contract, rendered_memberships


def _render_source_digest_program(nodes: dict[str, dict[str, object]]) -> str:
    lines = [
        "(* Generated by candle/flyspeck_manifest.py; do not edit. *)",
        "let candle_flyspeck_source_digests = [",
    ]
    for key in sorted(nodes):
        if key in SOURCE_DIGEST_EXCLUSIONS:
            continue
        node = nodes[key]
        repository = json.dumps(str(node["repository"]))
        path = json.dumps(str(node["path"]))
        digest = json.dumps(str(node["md5"]))
        lines.append(f"  ({repository},{path},{digest});")
    lines.extend([
        "];;",
        "",
    ])
    return "\n".join(lines)


def build_manifest(candle_root: Path, flyspeck_root: Path) -> dict[str, object]:
    _require_git_clean(flyspeck_root)
    resolver = Resolver(candle_root, flyspeck_root)
    build_file = flyspeck_root / "text_formalization/build/build.hl"
    sequence = extract_full_build_sequence(build_file.read_text(encoding="utf-8"))

    bootstrap = [
        SourceRef("candle", "hol.ml"),
        SourceRef("flyspeck", "text_formalization/build/strictbuild.hl"),
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
    static_library_directives: list[dict[str, object]] = []
    qualified_runtime_uses: list[dict[str, object]] = []
    opened_runtime_uses: list[dict[str, object]] = []
    runtime_module_opens: list[dict[str, object]] = []
    qualified_compatibility_uses: list[dict[str, object]] = []
    opened_compatibility_uses: list[dict[str, object]] = []
    compatibility_module_opens: list[dict[str, object]] = []
    toplevel_interface_uses: list[dict[str, object]] = []
    runtime_modules = set(STATIC_RUNTIME_LIBRARIES.values())
    compatibility_modules = set(OCAML_COMPATIBILITY_SUPPORTED_MEMBERS)
    all_opened_exports = {
        **OPENED_MODULE_EXPORTS,
        **OCAML_COMPATIBILITY_SUPPORTED_MEMBERS,
    }
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
        for use in scan_qualified_module_uses(
            text,
            runtime_modules | compatibility_modules | TOPLEVEL_INTERFACE_MODULES,
        ):
            if use["module"] in TOPLEVEL_INTERFACE_MODULES:
                toplevel_interface_uses.append({"source": ref.key, **use})
            else:
                target = (
                    qualified_runtime_uses
                    if use["module"] in runtime_modules
                    else qualified_compatibility_uses
                )
                target.append({"source": ref.key, **use})
        opens, opened_uses = scan_opened_module_uses(text, all_opened_exports)
        for entry in opens:
            target = (
                runtime_module_opens
                if entry["module"] in runtime_modules
                else compatibility_module_opens
            )
            target.append({"source": ref.key, **entry})
        for entry in opened_uses:
            target = (
                opened_runtime_uses
                if entry["module"] in runtime_modules
                else opened_compatibility_uses
            )
            target.append({"source": ref.key, **entry})
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
                static_library_directives.append({
                    "source": ref.key,
                    "line": call["line"],
                    "library": literal,
                })
            elif literal in KNOWN_GENERATED_DEPENDENCIES:
                dependency.update(
                    status="generated-contract",
                    generation=KNOWN_GENERATED_DEPENDENCIES[literal],
                )
            else:
                matches, error = resolver.resolve(literal)
                if error:
                    dependency.update(status="forbidden", error=error)
                elif not matches:
                    dependency["status"] = "missing"
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
            "md5": _md5(path),
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

    unsupported_runtime_libraries = [
        directive
        for directive in static_library_directives
        if directive["library"] not in STATIC_RUNTIME_LIBRARIES
    ]
    def add_runtime_library(use: dict[str, object]) -> dict[str, object]:
        return {
            **use,
            "library": next(
                library
                for library, module in STATIC_RUNTIME_LIBRARIES.items()
                if module == use["module"]
            ),
        }

    qualified_runtime_contract_uses = [
        add_runtime_library(use) for use in qualified_runtime_uses
    ]
    opened_runtime_contract_uses = [
        add_runtime_library(use) for use in opened_runtime_uses
    ]
    all_runtime_uses = qualified_runtime_contract_uses + opened_runtime_contract_uses
    unsupported_runtime_members = [
        use
        for use in all_runtime_uses
        if use["member"] not in STATIC_RUNTIME_MEMBERS[str(use["module"])]
    ]
    all_compatibility_uses = qualified_compatibility_uses + opened_compatibility_uses
    unsupported_compatibility_members = [
        use
        for use in all_compatibility_uses
        if use["member"] not in OCAML_COMPATIBILITY_SUPPORTED_MEMBERS[str(use["module"])]
    ]
    toplevel_selected_members = {
        module: sorted({
            str(use["member"])
            for use in toplevel_interface_uses
            if use["module"] == module
        })
        for module in sorted(TOPLEVEL_INTERFACE_MODULES)
    }
    toplevel_unbound_members = {
        module: sorted(
            set(toplevel_selected_members[module])
            - TOPLEVEL_INTERFACE_SOURCE_MEMBERS[module]
        )
        for module in sorted(TOPLEVEL_INTERFACE_MODULES)
    }
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
            if dep["status"] == "generated-contract"
        ),
        "ambiguous_dependencies": sum(
            1 for node in nodes.values() for dep in node["dependencies"] if dep["status"] == "ambiguous"
        ),
        "forbidden_dependencies": sum(
            1 for node in nodes.values() for dep in node["dependencies"] if dep["status"] == "forbidden"
        ),
        "unsupported_runtime_libraries": unsupported_runtime_libraries,
        "unsupported_runtime_members": unsupported_runtime_members,
        "unsupported_compatibility_members": unsupported_compatibility_members,
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
            if dependency["status"] not in {"generated-contract", "generated-runtime"}:
                continue
            generated_dependency_contracts.append({
                "source": source_key,
                **dependency,
            })
    deterministic_process_inputs = []
    for command, relative in DETERMINISTIC_PROCESS_INPUTS:
        path = candle_root / relative
        deterministic_process_inputs.append({
            "command": command,
            "source": f"candle:{relative}",
            "bytes": path.stat().st_size,
            "sha256": _sha256(path),
        })
    for payload in DYNAMIC_TOPLEVEL_PAYLOADS:
        source_key = str(payload["source"])
        if source_key not in nodes:
            raise ValueError(f"dynamic top-level payload source not selected: {source_key}")
        source_lines = resolver.path(
            SourceRef(*source_key.split(":", 1))
        ).read_text(encoding="utf-8", errors="surrogateescape").splitlines()
        line_number = int(payload["line"])
        if line_number < 1 or line_number > len(source_lines):
            raise ValueError(
                f"dynamic top-level payload line out of range: {source_key}:{line_number}"
            )
        if "exec" not in source_lines[line_number - 1]:
            raise ValueError(
                f"dynamic top-level payload site drifted: {source_key}:{line_number}"
            )
    build_strata, source_node_strata = _build_strata_contract(
        sequence, build_roots, nodes, edges, bootstrap, loader_source,
    )
    source_digest_program = _render_source_digest_program(nodes)
    source_digest_program_bytes = source_digest_program.encode()
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
        "build_strata_policy": (
            "contiguous operational checkpoint partitions in authoritative load "
            "order; labels do not imply mathematical dependency isolation"
        ),
        "build_strata": build_strata,
        "bootstrap_roots": [ref.key for ref in bootstrap],
        "loader": {
            "source": loader_source.key,
            "required_build_mode": "full",
            "configuration_bindings": [
                "candle_hollight_root", "candle_flyspeck_root",
                "candle_flyspeck_build_mode",
            ],
            "success_marker": "CANDLE_FLYSPECK_DIRECT_FULL_OK",
        },
        "source_digest_contract": {
            "activation_status": "preflight-before-strictbuild",
            "algorithm": "MD5 for OCaml Digest.file compatibility",
            "outer_integrity": "manifest and generated program pinned by SHA-256",
            "generated_source": f"candle:{SOURCE_DIGEST_PROGRAM}",
            "generated_source_sha256": hashlib.sha256(
                source_digest_program_bytes
            ).hexdigest(),
            "generated_source_md5": hashlib.md5(
                source_digest_program_bytes, usedforsecurity=False
            ).hexdigest(),
            "entry_count": len(nodes) - len(SOURCE_DIGEST_EXCLUSIONS),
            "coverage": "all selected source nodes except the executing loader",
            "bootstrap_exclusions": sorted(SOURCE_DIGEST_EXCLUSIONS),
            "preload_authentication": (
                "loader checks generated_source_md5 before executing the program"
            ),
            "execution_limit": (
                "preflight detects on-disk corruption before strictbuild; hol.ml "
                "and the loader have already begun execution, and the loader is "
                "authenticated only by the outer release lock"
            ),
            "gate": "candle:candle/test_flyspeck_source_digests.sh",
        },
        "static_library_contract": {
            "scope": "reachable direct-source full-build graph only",
            "activation_status": "blocked-pending-static-binding-evidence",
            "directive_policy": (
                "recognize only the listed libraries; reject every other #load; "
                "directive erasure or no-op is forbidden until all listed module "
                "members have semantically adequate static Candle bindings"
            ),
            "library_modules": STATIC_RUNTIME_LIBRARIES,
            "library_members": {
                library: sorted(STATIC_RUNTIME_MEMBERS[module])
                for library, module in STATIC_RUNTIME_LIBRARIES.items()
            },
            "binding_evidence": {
                "str.cma": {
                    "status": "partial-pure-source-differential-gate",
                    "source": "candle:candle/ocaml.ml",
                    "members": sorted(STATIC_RUNTIME_MEMBERS["Str"]),
                    "oracle": "OCaml 4.14.1 Str",
                    "gate": "candle:candle/test_str_compat.sh",
                    "open_limit": (
                        "escaped grouping, alternation, back-references, and "
                        "empty-match global replacement fail explicitly"
                    ),
                },
                "unix.cma": {
                    "status": "startup-metadata-only-explicit-fail-otherwise",
                    "members": sorted(STATIC_RUNTIME_MEMBERS["Unix"]),
                    "source": "candle:candle/ocaml.ml",
                    "deterministic_process_inputs": deterministic_process_inputs,
                    "gate": "candle:candle/test_unix_metadata.sh",
                },
            },
            "opened_use_attribution": (
                "conservative lexical candidates after a source open; exact "
                "sites reviewed for shadowing, not a compiler name-resolution proof"
            ),
            "directives": sorted(
                static_library_directives,
                key=lambda entry: (str(entry["source"]), int(entry["line"])),
            ),
            "qualified_uses": sorted(
                qualified_runtime_contract_uses,
                key=lambda entry: (
                    str(entry["source"]), int(entry["line"]),
                    str(entry["module"]), str(entry["member"]),
                ),
            ),
            "module_opens": sorted(
                runtime_module_opens,
                key=lambda entry: (str(entry["source"]), int(entry["line"])),
            ),
            "opened_module_uses": sorted(
                opened_runtime_contract_uses,
                key=lambda entry: (
                    str(entry["source"]), int(entry["line"]),
                    str(entry["module"]), str(entry["member"]),
                ),
            ),
            "capability_uses": sorted(
                all_runtime_uses,
                key=lambda entry: (
                    str(entry["source"]), int(entry["line"]),
                    str(entry["module"]), str(entry["member"]),
                ),
            ),
        },
        "ocaml_compatibility_contract": {
            "scope": "reachable direct-source full-build graph only",
            "activation_status": "partial-source-bindings",
            "supported_members": {
                module: sorted(members)
                for module, members in OCAML_COMPATIBILITY_SUPPORTED_MEMBERS.items()
            },
            "selected_members": {
                module: sorted({
                    str(use["member"])
                    for use in all_compatibility_uses
                    if use["module"] == module
                })
                for module in OCAML_COMPATIBILITY_SUPPORTED_MEMBERS
            },
            "binding_evidence": {
                "Digest": {
                    "status": "pure-source-differential-gate",
                    "source": "candle:candle/ocaml.ml",
                    "oracle": "OCaml 4.14.1 Digest",
                    "gate": "candle:candle/test_digest_compat.sh",
                    "assurance_limit": (
                        "differentially tested but not yet formally linked to "
                        "CakeML's existing verified md5Theory/md5Prog"
                    ),
                },
            },
            "opened_use_attribution": (
                "conservative lexical candidates after a source open; exact "
                "sites require review and are not compiler name-resolution proof"
            ),
            "qualified_uses": sorted(
                qualified_compatibility_uses,
                key=lambda entry: (
                    str(entry["source"]), int(entry["line"]),
                    str(entry["module"]), str(entry["member"]),
                ),
            ),
            "module_opens": sorted(
                compatibility_module_opens,
                key=lambda entry: (str(entry["source"]), int(entry["line"])),
            ),
            "opened_module_uses": sorted(
                opened_compatibility_uses,
                key=lambda entry: (
                    str(entry["source"]), int(entry["line"]),
                    str(entry["module"]), str(entry["member"]),
                ),
            ),
            "capability_uses": sorted(
                all_compatibility_uses,
                key=lambda entry: (
                    str(entry["source"]), int(entry["line"]),
                    str(entry["module"]), str(entry["member"]),
                ),
            ),
        },
        "toplevel_interface_contract": {
            "scope": "reachable direct-source full-build graph only",
            "activation_status": "blocked-no-dummy-or-no-op",
            "policy": (
                "Toploop and dynamically evaluated source are correctness-relevant; "
                "a dummy return, silent skip, unchecked Obj.magic, or successful "
                "no-op use_file is forbidden"
            ),
            "qualified_uses": sorted(
                toplevel_interface_uses,
                key=lambda entry: (
                    str(entry["source"]), int(entry["line"]),
                    str(entry["module"]), str(entry["member"]),
                ),
            ),
            "selected_members": toplevel_selected_members,
            "current_source_members": {
                module: sorted(members)
                for module, members in sorted(
                    TOPLEVEL_INTERFACE_SOURCE_MEMBERS.items()
                )
            },
            "unbound_members": toplevel_unbound_members,
            "conditional_source_selection": {
                "source": "flyspeck:text_formalization/general/serialization.hl",
                "selector": "ocaml_version() matches Str.regexp \"Ocaml 4.\"",
                "pinned_ocaml_version": "4.14.1",
                "selected": (
                    "flyspeck:text_formalization/general/update_database_400.ml"
                ),
                "unselected": (
                    "flyspeck:text_formalization/general/update_database_310.ml"
                ),
                "graph_limit": (
                    "the conservative dependency graph contains both literal "
                    "branches; only the selected branch is an execution claim"
                ),
            },
            "dynamic_source_payloads": list(DYNAMIC_TOPLEVEL_PAYLOADS),
            "dynamic_payload_policy": (
                "string bodies are masked by ordinary capability scanning and "
                "therefore require an explicit typed registry transformation or "
                "verified dynamic-evaluation contract before activation"
            ),
        },
        "final_target": {
            "source": final_target.key,
            "name": "Candle_flyspeck_l2.tame_imp_kepler_conjecture",
            "statement": "import_tame_classification ==> the_kepler_conjecture",
            "imported_premises": ["import_tame_classification"],
        },
        "source_node_count": len(nodes),
        "source_edge_count": sum(len(targets) for targets in edges.values()),
        "source_node_strata": {
            key: source_node_strata[key] for key in sorted(source_node_strata)
        },
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
    source_digest_path = candle_root / SOURCE_DIGEST_PROGRAM
    payload = build_manifest(candle_root, arguments.flyspeck_root.resolve())
    rendered = _render(payload)
    source_digest_rendered = _render_source_digest_program(payload["source_nodes"])
    source_digest_sha256 = hashlib.sha256(source_digest_rendered.encode()).hexdigest()
    if source_digest_sha256 != payload["source_digest_contract"]["generated_source_sha256"]:
        raise SystemExit("internal source digest program hash mismatch")
    if arguments.write:
        source_digest_path.write_text(source_digest_rendered, encoding="utf-8")
        manifest_path.write_text(rendered, encoding="utf-8")
    elif (
        not manifest_path.is_file()
        or manifest_path.read_text(encoding="utf-8") != rendered
        or not source_digest_path.is_file()
        or source_digest_path.read_text(encoding="utf-8") != source_digest_rendered
    ):
        raise SystemExit(
            f"stale manifest or source digest program: run {Path(__file__).name} --write"
        )
    blockers = promotion_blockers(payload["diagnostics"])
    if blockers:
        raise SystemExit("manifest promotion blocked by: " + ", ".join(blockers))
    print(
        f"manifest ok: {payload['build_sequence_count']} roots, "
        f"{payload['source_node_count']} source nodes, "
        f"{len(payload['generated_inputs'])} generated inputs"
    )


if __name__ == "__main__":
    main()
