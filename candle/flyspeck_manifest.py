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

import flyspeck_normalize
import flyspeck_prepare_inputs


SCHEMA = 1
SOURCE_DIGEST_PROGRAM = "candle/flyspeck_source_digests.ml"
FULL_BUILD_PROGRAM = "candle/flyspeck_full_build.ml"
SOURCE_NORMALIZATION_CONTRACT = "candle/flyspeck_normalizations.json"
LP_ARCHIVE_CONTRACT = "candle/flyspeck_lp_archive_contract.json"
SOURCE_DIGEST_EXCLUSIONS = {"candle:candle/flyspeck_loader.ml"}
LOAD_NAMES = ("needs", "loads", "loadt", "flyspeck_needs", "rflyspeck_needs", "reneeds")
LOAD_RE = re.compile(r"\b(" + "|".join(LOAD_NAMES) + r")\b")
DIRECTIVE_RE = re.compile(r"#\s*(flyspeck_loadt|flyspeck_needs|use|load)\b")
MODULE_PATH = r"[A-Z][A-Za-z0-9_']*(?:\s*\.\s*[A-Z][A-Za-z0-9_']*)*"
OPEN_DECLARATION_RE = re.compile(
    r"\bopen(?P<override>!)?\s+(?P<path>" + MODULE_PATH + r")\b"
)
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
# Small, correctness-relevant Flyspeck identifiers around the compiler
# top-level boundary.  Unlike qualified-module scanning, this inventory is
# deliberately restricted to Flyspeck source: names such as [search] also
# occur in unrelated Candle implementations.  Every occurrence is reviewed
# below so source drift cannot silently turn a definition-only helper into an
# active consumer.
TOPLEVEL_CONSUMER_IDENTIFIERS = {
    "eval_command", "save_all_theorems", "search", "search_thml",
    "test_id_thm", "theorems", "update_database", "use_arg_then",
}
TYPED_THEOREM_LOOKUP_IDENTIFIER = "use_arg_then2"
TOPLEVEL_CONSUMER_SITE_REVIEWS = (
    # Common selected sources whose Toploop-backed bindings have no other
    # lexical reference in the selected graph.
    ("flyspeck:jHOLLight/caml/ssreflect.hl", 721, "test_id_thm", "definition", "common"),
    ("flyspeck:jHOLLight/caml/ssreflect.hl", 733, "use_arg_then", "definition", "common"),
    ("flyspeck:text_formalization/general/flyspeck_eval_4.14.hl", 13, "eval_command", "definition", "common"),
    ("flyspeck:text_formalization/general/serialization.hl", 519, "save_all_theorems", "definition", "common"),
    ("flyspeck:text_formalization/general/serialization.hl", 520, "update_database", "deferred-body", "common"),
    ("flyspeck:text_formalization/general/serialization.hl", 521, "theorems", "deferred-body", "common"),
    # Conservative graph member selected only by the OCaml 3.x branch.
    ("flyspeck:text_formalization/general/update_database_310.ml", 177, "update_database", "definition", "unselected-3.x"),
    ("flyspeck:text_formalization/general/update_database_310.ml", 209, "theorems", "deferred-body", "unselected-3.x"),
    ("flyspeck:text_formalization/general/update_database_310.ml", 255, "search_thml", "definition", "unselected-3.x"),
    ("flyspeck:text_formalization/general/update_database_310.ml", 300, "update_database", "deferred-body", "unselected-3.x"),
    ("flyspeck:text_formalization/general/update_database_310.ml", 307, "search", "definition", "unselected-3.x"),
    ("flyspeck:text_formalization/general/update_database_310.ml", 307, "search_thml", "deferred-body", "unselected-3.x"),
    ("flyspeck:text_formalization/general/update_database_310.ml", 307, "theorems", "deferred-body", "unselected-3.x"),
    ("flyspeck:text_formalization/general/update_database_310.ml", 313, "update_database", "top-level-call", "unselected-3.x"),
    # Pinned OCaml 4.14.1 execution branch.  The final call is active while
    # the search helper's call and database read are deferred in its body.
    ("flyspeck:text_formalization/general/update_database_400.ml", 280, "search_thml", "definition", "selected-4.x"),
    ("flyspeck:text_formalization/general/update_database_400.ml", 325, "update_database", "deferred-body", "selected-4.x"),
    ("flyspeck:text_formalization/general/update_database_400.ml", 332, "search", "definition", "selected-4.x"),
    ("flyspeck:text_formalization/general/update_database_400.ml", 332, "search_thml", "deferred-body", "selected-4.x"),
    ("flyspeck:text_formalization/general/update_database_400.ml", 332, "theorems", "deferred-body", "selected-4.x"),
    ("flyspeck:text_formalization/general/update_database_400.ml", 338, "update_database", "top-level-call", "selected-4.x"),
)
NORMALIZATION_NONUSE_IDENTIFIERS = {"qmap", "unsuppress", "use_file_b"}
NORMALIZATION_NONUSE_SITE_REVIEWS = (
    ("flyspeck:text_formalization/build/strictbuild.hl", 86, "use_file_b", "definition"),
    ("flyspeck:text_formalization/build/strictbuild.hl", 97, "use_file_b", "deferred-body"),
    ("flyspeck:text_formalization/general/lib.hl", 474, "qmap", "definition"),
    ("flyspeck:text_formalization/general/lib.hl", 476, "qmap", "recursive-body"),
    ("flyspeck:text_formalization/general/print_types.hl", 21, "unsuppress", "signature"),
    ("flyspeck:text_formalization/general/print_types.hl", 34, "unsuppress", "definition"),
)
# The selected graph loads the historical GLPK generator modules because their
# pure parsers and data types are shared with verification.  Their shell/process
# helpers are ordinary function bodies, however, and the proof route has no
# external lexical caller.  Freeze the complete internal call chain so a future
# source change cannot silently make the fail-closed process bindings active.
PROCESS_ROUTE_MODULES = {"Glpk_link", "Lpproc"}
PROCESS_ROUTE_IDENTIFIERS_BY_SOURCE = {
    "flyspeck:formal_lp/glpk/glpk_link.ml": {
        "cpx_branch", "display_ampl", "display_lp", "get_dumpvar", "solve",
        "solve_branch_f", "solve_dual_f", "strip_archive",
    },
    "flyspeck:formal_lp/glpk/lpproc.ml": {
        "allpass", "echo", "execute", "filter_feas", "filter_feas_f",
        "make_model", "onepass", "solve", "solve_branch_verbose", "solve_f",
    },
}
PROCESS_ROUTE_SITE_REVIEWS = (
    ("flyspeck:formal_lp/glpk/glpk_link.ml", 140, "strip_archive", "definition-entrypoint"),
    ("flyspeck:formal_lp/glpk/glpk_link.ml", 189, "display_ampl", "definition-entrypoint"),
    ("flyspeck:formal_lp/glpk/glpk_link.ml", 199, "solve", "definition-shared-helper"),
    ("flyspeck:formal_lp/glpk/glpk_link.ml", 214, "solve_branch_f", "definition-branch-adapter"),
    ("flyspeck:formal_lp/glpk/glpk_link.ml", 216, "solve", "deferred-call"),
    ("flyspeck:formal_lp/glpk/glpk_link.ml", 218, "solve_dual_f", "definition-entrypoint"),
    ("flyspeck:formal_lp/glpk/glpk_link.ml", 220, "solve", "deferred-call"),
    ("flyspeck:formal_lp/glpk/glpk_link.ml", 222, "display_lp", "definition-entrypoint"),
    ("flyspeck:formal_lp/glpk/glpk_link.ml", 230, "cpx_branch", "definition-entrypoint"),
    ("flyspeck:formal_lp/glpk/glpk_link.ml", 241, "get_dumpvar", "definition-entrypoint"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 78, "make_model", "definition-terminal"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 346, "solve_branch_verbose", "definition-chain"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 360, "solve_f", "definition-chain"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 361, "solve_branch_verbose", "deferred-call"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 365, "solve", "definition-chain"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 365, "solve_f", "deferred-call"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 376, "filter_feas_f", "definition-chain"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 377, "solve_f", "deferred-call"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 379, "filter_feas", "definition-chain"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 379, "filter_feas_f", "deferred-call"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 433, "echo", "definition-terminal"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 435, "onepass", "definition-chain"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 437, "echo", "deferred-call"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 438, "filter_feas", "deferred-call"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 440, "allpass", "definition-chain"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 442, "allpass", "recursive-call"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 442, "onepass", "deferred-call"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 493, "execute", "definition-route-root"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 494, "make_model", "deferred-call"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 498, "filter_feas", "deferred-call"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 498, "solve", "deferred-call"),
    ("flyspeck:formal_lp/glpk/lpproc.ml", 500, "allpass", "deferred-call"),
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
    ("candle:candle/flyspeck_loader.ml", 89, "flyspeck_needs"): {
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
    directive_matches = list(DIRECTIVE_RE.finditer(mask))
    matches: list[tuple[re.Match[str], str]] = [
        (match, match.group(1)) for match in LOAD_RE.finditer(mask)
        if not any(
            directive.start() <= match.start() < directive.end()
            for directive in directive_matches
        )
    ]
    matches.extend(
        (match, f"#{match.group(1)}") for match in directive_matches
    )
    calls: list[dict[str, object]] = []
    for match, kind in sorted(matches, key=lambda item: item[0].start()):
        prefix = clean[max(0, match.start() - 24):match.start()]
        if DEFINITION_PREFIX_RE.search(prefix):
            continue
        previous_phrase_end = mask.rfind(";;", 0, match.start())
        phrase_prefix = mask[previous_phrase_end + 2:match.start()]
        syntax_position = (
            "standalone-phrase"
            if phrase_prefix.strip() == ""
            else "embedded-expression"
        )
        literal, end = _call_argument(clean, match.end())
        line = clean.count("\n", 0, match.start()) + 1
        if literal is not None:
            calls.append({
                "kind": kind,
                "line": line,
                "literal": literal,
                "syntax_position": syntax_position,
            })
        else:
            expression_end = clean.find(";;", match.end())
            if expression_end < 0:
                expression_end = clean.find("\n", match.end())
            if expression_end < 0:
                expression_end = min(len(clean), match.end() + 160)
            expression = " ".join(clean[match.start():expression_end].split())[:160]
            calls.append({
                "kind": kind,
                "line": line,
                "expression": expression,
                "syntax_position": syntax_position,
            })
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


def scan_identifier_uses(source: str, identifiers: set[str]) -> list[dict[str, object]]:
    """Inventory exact identifiers outside comments, strings, and HOL quotes."""
    if not identifiers:
        return []
    clean = strip_ocaml_comments(source)
    mask = _code_mask(clean)
    identifier_re = re.compile(
        r"\b(" + "|".join(re.escape(name) for name in sorted(identifiers))
        + r")\b"
    )
    return [
        {
            "line": clean.count("\n", 0, match.start()) + 1,
            "identifier": match.group(1),
        }
        for match in identifier_re.finditer(mask)
    ]


def scan_open_declarations(source: str) -> list[dict[str, object]]:
    """Inventory declaration opens, excluding local [let open M in]."""
    clean = strip_ocaml_comments(source)
    mask = _code_mask(clean)
    declarations: list[dict[str, object]] = []
    for match in OPEN_DECLARATION_RE.finditer(mask):
        prefix = mask[:match.start()].rstrip()
        if re.search(r"\blet$", prefix):
            continue
        path = re.sub(r"\s*\.\s*", ".", match.group("path"))
        declarations.append({
            "line": clean.count("\n", 0, match.start()) + 1,
            "module_path": path,
            "path_form": "dotted" if "." in path else "simple",
            "override_warning_suppression": bool(match.group("override")),
        })
    return declarations


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


def _render_full_build_program(
    sequence: list[str],
    build_roots: list[dict[str, object]],
    nodes: dict[str, dict[str, object]],
    build_strata: list[dict[str, object]],
) -> str:
    """Render the exact manifest-owned full-build root driver.

    The directive is deliberately not ordinary OCaml and is not treated as
    [needs].  Its future Candle loader action is a single atomic contract:
    resolve the manifest-selected source, evaluate it at this point, and call
    State_manager.neutralize_state only after a newly loaded source succeeds.
    An already-loaded duplicate performs neither action.  Until that exact
    action is implemented, the directive remains a fail-closed parser token.
    """
    if len(sequence) != len(build_roots):
        raise ValueError("full-build program root count mismatch")
    stratum_for_index: dict[int, str] = {}
    for stratum in build_strata:
        name = str(stratum["name"])
        for index in range(int(stratum["start_index"]), int(stratum["end_index"]) + 1):
            if index in stratum_for_index:
                raise ValueError(f"full-build program stratum overlap at {index}")
            stratum_for_index[index] = name
    if set(stratum_for_index) != set(range(len(sequence))):
        raise ValueError("full-build program strata do not cover every root")

    lines = [
        "(* Generated by candle/flyspeck_manifest.py; do not edit.",
        "   #flyspeck_needs is fail-closed until Candle implements the exact",
        "   manifest-rooted load-and-neutralize action recorded in",
        "   candle/flyspeck_manifest.json. *)",
    ]
    previous_stratum: str | None = None
    for index, (target, root) in enumerate(zip(sequence, build_roots, strict=True)):
        if root.get("status") != "resolved":
            raise ValueError(f"cannot render unresolved full-build root {index}")
        selected = str(root["selected"])
        if selected not in nodes:
            raise ValueError(f"full-build root leaves selected graph: {selected}")
        stratum = stratum_for_index[index]
        if stratum != previous_stratum:
            lines.extend(["", f"(* stratum: {stratum} *)"])
            previous_stratum = stratum
        marker = (
            f"(* {index:03d} selected={selected} "
            f"sha256={nodes[selected]['sha256']}"
        )
        normalization = nodes[selected].get("execution_normalization")
        if isinstance(normalization, dict):
            marker += (
                f" normalization={normalization['id']} "
                f"normalized_sha256={normalization['normalized_sha256']}"
            )
        lines.append(marker + " *)")
        lines.append(f"#flyspeck_needs {json.dumps(target)};;")
    lines.append("")
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
    declaration_opens: list[dict[str, object]] = []
    toplevel_interface_uses: list[dict[str, object]] = []
    toplevel_consumer_uses: list[dict[str, object]] = []
    normalization_nonuse_uses: list[dict[str, object]] = []
    process_route_uses: list[dict[str, object]] = []
    process_route_qualified_uses: list[dict[str, object]] = []
    typed_theorem_lookup_counts: dict[str, int] = {}
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
            runtime_modules | compatibility_modules | TOPLEVEL_INTERFACE_MODULES
            | PROCESS_ROUTE_MODULES,
        ):
            if use["module"] in PROCESS_ROUTE_MODULES:
                process_route_qualified_uses.append({"source": ref.key, **use})
            elif use["module"] in TOPLEVEL_INTERFACE_MODULES:
                toplevel_interface_uses.append({"source": ref.key, **use})
            else:
                target = (
                    qualified_runtime_uses
                    if use["module"] in runtime_modules
                    else qualified_compatibility_uses
                )
                target.append({"source": ref.key, **use})
        if ref.repository == "flyspeck":
            for use in scan_identifier_uses(text, TOPLEVEL_CONSUMER_IDENTIFIERS):
                toplevel_consumer_uses.append({"source": ref.key, **use})
            for use in scan_identifier_uses(text, NORMALIZATION_NONUSE_IDENTIFIERS):
                normalization_nonuse_uses.append({"source": ref.key, **use})
            process_identifiers = PROCESS_ROUTE_IDENTIFIERS_BY_SOURCE.get(ref.key)
            if process_identifiers is not None:
                for use in scan_identifier_uses(text, process_identifiers):
                    process_route_uses.append({"source": ref.key, **use})
            typed_count = len(scan_identifier_uses(
                text, {TYPED_THEOREM_LOOKUP_IDENTIFIER},
            ))
            if typed_count:
                typed_theorem_lookup_counts[ref.key] = typed_count
        for declaration in scan_open_declarations(text):
            declaration_opens.append({"source": ref.key, **declaration})
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

    normalization_path = candle_root / SOURCE_NORMALIZATION_CONTRACT
    normalization_contract, normalization_outputs = (
        flyspeck_normalize.evaluate_contract(
            normalization_path, flyspeck_root,
        )
    )
    normalization_entries: list[dict[str, object]] = []
    for entry, normalized in normalization_outputs:
        source_key = str(entry["source_key"])
        if source_key not in nodes:
            raise ValueError(
                f"normalization source is outside selected graph: {source_key}"
            )
        node = nodes[source_key]
        if (
            node["sha256"] != entry["source_sha256"]
            or node["md5"] != entry["source_md5"]
        ):
            raise ValueError(
                f"normalization/source-node digest mismatch: {source_key}"
            )
        execution_normalization = {
            "id": entry["id"],
            "kind": "exact_bytes_replace_sequence",
            "operation_count": len(entry["operations"]),
            "normalized_bytes": len(normalized),
            "normalized_sha256": entry["normalized_sha256"],
            "normalized_md5": entry["normalized_md5"],
        }
        node["execution_normalization"] = execution_normalization
        normalization_entries.append({
            "id": entry["id"],
            "source_key": source_key,
            "path": entry["path"],
            "source_sha256": entry["source_sha256"],
            "source_md5": entry["source_md5"],
            **execution_normalization,
            "operations": entry["operations"],
            "semantic_rule": entry["semantic_rule"],
            "scope_limit": entry["scope_limit"],
        })

    lp_archive_contract_path = candle_root / LP_ARCHIVE_CONTRACT
    lp_archive_contract = flyspeck_prepare_inputs.evaluate(
        lp_archive_contract_path, flyspeck_root,
    )
    lp_archive_member = lp_archive_contract["members"][0]

    generated_inputs: list[dict[str, object]] = []
    generated_paths: set[Path] = set()
    for pattern in GENERATED_INPUT_GLOBS:
        generated_paths.update(flyspeck_root.glob(pattern))
    for path in sorted(generated_paths):
        relative = path.relative_to(flyspeck_root).as_posix()
        generated_inputs.append({
            "class": (
                "lp-certificate-archive"
                if relative == lp_archive_contract["archive"]["path"]
                else "lp-certificate"
            ),
            "path": relative,
            "bytes": path.stat().st_size,
            "sha256": _sha256(path),
        })
    generated_inputs.append({
        "class": "lp-certificate-prepared",
        "path": lp_archive_member["output_path"],
        "bytes": lp_archive_member["bytes"],
        "sha256": lp_archive_member["sha256"],
        "derived_from": lp_archive_contract["archive"]["path"],
        "derivation_contract_sha256": hashlib.sha256(
            lp_archive_contract_path.read_bytes()
        ).hexdigest(),
    })
    for input_class, relative in NAMED_INPUTS:
        path = flyspeck_root / relative
        generated_inputs.append({
            "class": input_class,
            "path": relative,
            "bytes": path.stat().st_size,
            "sha256": _sha256(path),
        })
    lp_runtime_certificate_basenames = sorted(
        Path(str(item["path"])).name
        for item in generated_inputs
        if item["class"] in {"lp-certificate", "lp-certificate-prepared"}
    )
    if (
        len(lp_runtime_certificate_basenames) != 39
        or len(set(lp_runtime_certificate_basenames)) != 39
        or any(name.endswith(".gz") for name in lp_runtime_certificate_basenames)
    ):
        raise ValueError("prepared LP runtime certificate inventory mismatch")

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
    observed_consumer_sites = {
        (str(use["source"]), int(use["line"]), str(use["identifier"]))
        for use in toplevel_consumer_uses
    }
    reviewed_consumer_sites = {
        (source, line, identifier)
        for source, line, identifier, _role, _branch
        in TOPLEVEL_CONSUMER_SITE_REVIEWS
    }
    if len(observed_consumer_sites) != len(toplevel_consumer_uses):
        raise ValueError("duplicate reviewed top-level consumer site")
    if observed_consumer_sites != reviewed_consumer_sites:
        missing = sorted(reviewed_consumer_sites - observed_consumer_sites)
        unreviewed = sorted(observed_consumer_sites - reviewed_consumer_sites)
        raise ValueError(
            "top-level consumer sites drifted: "
            f"missing={missing}; unreviewed={unreviewed}"
        )
    consumer_reviews = {
        (source, line, identifier): {"role": role, "branch": branch}
        for source, line, identifier, role, branch
        in TOPLEVEL_CONSUMER_SITE_REVIEWS
    }
    reviewed_consumer_uses = [
        {
            **use,
            **consumer_reviews[
                (str(use["source"]), int(use["line"]), str(use["identifier"]))
            ],
        }
        for use in toplevel_consumer_uses
    ]
    consumer_identifier_counts = {
        identifier: sum(
            use["identifier"] == identifier for use in toplevel_consumer_uses
        )
        for identifier in sorted(TOPLEVEL_CONSUMER_IDENTIFIERS)
    }
    observed_normalization_nonuse_sites = {
        (str(use["source"]), int(use["line"]), str(use["identifier"]))
        for use in normalization_nonuse_uses
    }
    reviewed_normalization_nonuse_sites = {
        (source, line, identifier)
        for source, line, identifier, _role
        in NORMALIZATION_NONUSE_SITE_REVIEWS
    }
    if len(observed_normalization_nonuse_sites) != len(normalization_nonuse_uses):
        raise ValueError("duplicate normalization non-use site")
    if observed_normalization_nonuse_sites != reviewed_normalization_nonuse_sites:
        missing = sorted(
            reviewed_normalization_nonuse_sites - observed_normalization_nonuse_sites
        )
        unreviewed = sorted(
            observed_normalization_nonuse_sites - reviewed_normalization_nonuse_sites
        )
        raise ValueError(
            "normalization non-use sites drifted: "
            f"missing={missing}; unreviewed={unreviewed}"
        )
    normalization_nonuse_roles = {
        (source, line, identifier): role
        for source, line, identifier, role in NORMALIZATION_NONUSE_SITE_REVIEWS
    }
    reviewed_normalization_nonuse_uses = [
        {
            **use,
            "role": normalization_nonuse_roles[
                (str(use["source"]), int(use["line"]), str(use["identifier"]))
            ],
        }
        for use in normalization_nonuse_uses
    ]
    observed_process_route_sites = {
        (str(use["source"]), int(use["line"]), str(use["identifier"]))
        for use in process_route_uses
    }
    reviewed_process_route_sites = {
        (source, line, identifier)
        for source, line, identifier, _role in PROCESS_ROUTE_SITE_REVIEWS
    }
    if len(observed_process_route_sites) != len(process_route_uses):
        raise ValueError("duplicate reviewed process-route site")
    if observed_process_route_sites != reviewed_process_route_sites:
        missing = sorted(reviewed_process_route_sites - observed_process_route_sites)
        unreviewed = sorted(observed_process_route_sites - reviewed_process_route_sites)
        raise ValueError(
            "process-route sites drifted: "
            f"missing={missing}; unreviewed={unreviewed}"
        )
    if process_route_qualified_uses:
        raise ValueError(
            "selected graph gained an external qualified GLPK process-route use: "
            f"{process_route_qualified_uses}"
        )
    process_route_roles = {
        (source, line, identifier): role
        for source, line, identifier, role in PROCESS_ROUTE_SITE_REVIEWS
    }
    reviewed_process_route_uses = [
        {
            **use,
            "role": process_route_roles[
                (str(use["source"]), int(use["line"]), str(use["identifier"]))
            ],
        }
        for use in process_route_uses
    ]
    process_route_module_opens = [
        entry for entry in declaration_opens
        if entry["module_path"] in PROCESS_ROUTE_MODULES
    ]
    expected_process_route_module_opens = [
        {
            "source": "flyspeck:formal_lp/glpk/lpproc.ml",
            "line": 58,
            "module_path": "Glpk_link",
            "path_form": "simple",
            "override_warning_suppression": False,
        },
    ]
    if process_route_module_opens != expected_process_route_module_opens:
        raise ValueError(
            "selected GLPK process-route module opens drifted: "
            f"expected={expected_process_route_module_opens}; "
            f"observed={process_route_module_opens}"
        )
    typed_theorem_lookup_occurrences = sum(typed_theorem_lookup_counts.values())
    dependency_kind_status_counts: dict[tuple[str, str], int] = {}
    dependency_position_counts: dict[tuple[str, str], int] = {}
    for node in nodes.values():
        for dependency in node["dependencies"]:
            key = (str(dependency["kind"]), str(dependency["status"]))
            dependency_kind_status_counts[key] = (
                dependency_kind_status_counts.get(key, 0) + 1
            )
            position_key = (
                str(dependency["kind"]), str(dependency["syntax_position"]),
            )
            dependency_position_counts[position_key] = (
                dependency_position_counts.get(position_key, 0) + 1
            )
    loader_action_site_count = sum(dependency_kind_status_counts.values())
    build_strata, source_node_strata = _build_strata_contract(
        sequence, build_roots, nodes, edges, bootstrap, loader_source,
    )
    sorted_declaration_opens = sorted(
        declaration_opens,
        key=lambda entry: (
            str(entry["source"]), int(entry["line"]),
            str(entry["module_path"]),
        ),
    )
    declaration_open_site_bytes = json.dumps(
        sorted_declaration_opens,
        sort_keys=True,
        separators=(",", ":"),
    ).encode()
    declaration_open_strata: list[dict[str, object]] = []
    for stratum in BUILD_STRATA:
        name = str(stratum["name"])
        sites = [
            entry for entry in sorted_declaration_opens
            if source_node_strata[str(entry["source"])][0] == name
        ]
        declaration_open_strata.append({
            "name": name,
            "occurrence_count": len(sites),
            "source_file_count": len({str(entry["source"]) for entry in sites}),
            "module_path_count": len({str(entry["module_path"]) for entry in sites}),
        })
    full_build_program = _render_full_build_program(
        sequence, build_roots, nodes, build_strata,
    )
    full_build_program_bytes = full_build_program.encode()
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
        "static_full_build_contract": {
            "activation_status": "exact-action-and-overlay-active-pending-full-run",
            "generated_source": f"candle:{FULL_BUILD_PROGRAM}",
            "generated_source_sha256": hashlib.sha256(
                full_build_program_bytes
            ).hexdigest(),
            "generated_source_md5": hashlib.md5(
                full_build_program_bytes, usedforsecurity=False
            ).hexdigest(),
            "directive": "#flyspeck_needs",
            "entry_count": len(sequence),
            "unique_target_count": len(sequence_positions),
            "ordered_target_sha256": hashlib.sha256(
                json.dumps(sequence, separators=(",", ":")).encode()
            ).hexdigest(),
            "source_selection_binding": (
                "every generated entry records its manifest-selected source key "
                "and SHA-256 beside the authoritative target literal; a normalized "
                "entry additionally records its exact normalization id and output hash"
            ),
            "preload_authentication": (
                "the direct loader checks generated_source_md5 before strictbuild; "
                "the outer release manifest pins generated_source_sha256"
            ),
            "required_loader_action": (
                "at the directive position authenticate and resolve only the "
                "manifest-selected source; an already-loaded duplicate performs "
                "neither evaluation nor neutralization; otherwise evaluate it "
                "exactly once, require a true result, then call "
                "State_manager.neutralize_state exactly once; record action "
                "success only after both steps return normally"
            ),
            "failure_policy": (
                "unknown, malformed, reordered, unresolved, hash-mismatched, or "
                "unsupported dynamic loads abort; evaluator false or any "
                "evaluation exception aborts the one-shot process before "
                "neutralization, later targets, or a success marker; any "
                "neutralization exception likewise aborts before action success; "
                "the directive must not be erased or implemented as a successful "
                "no-op"
            ),
            "assurance_limit": (
                "exact for accepted and already-loaded observations and an "
                "intentional fail-closed refinement of pinned failure behavior; "
                "the release does not preserve post-failure state, diagnostics, "
                "neutralization after evaluator false, or swallowed Failure from "
                "neutralization"
            ),
            "open_gate": (
                "a complete selected run, dynamic non-use observations, and exact "
                "semantic fingerprints remain open"
            ),
        },
        "source_normalization_contract": {
            "activation_status": "exact-overlay-selection-active-pending-full-run",
            "runtime_selection_source": (
                "cakeml:candle/prover/candle_boot.ml@1b17732f and "
                "candle:candle/flyspeck_loader.ml"
            ),
            "runtime_selection_policy": (
                "after the original-source preflight, authenticate each normalized "
                "MD5 and install one exact original-path to output-path mapping; "
                "never add the overlay directory to load_path"
            ),
            "contract_source": f"candle:{SOURCE_NORMALIZATION_CONTRACT}",
            "contract_sha256": flyspeck_normalize.contract_sha256(
                normalization_path
            ),
            "flyspeck_commit": normalization_contract["flyspeck_commit"],
            "entry_count": len(normalization_entries),
            "entries": normalization_entries,
            "selected_graph_non_use_bindings": {
                "identifiers": sorted(NORMALIZATION_NONUSE_IDENTIFIERS),
                "reviewed_occurrences": sorted(
                    reviewed_normalization_nonuse_uses,
                    key=lambda entry: (
                        str(entry["source"]), int(entry["line"]),
                        str(entry["identifier"]),
                    ),
                ),
                "policy": (
                    "only the exact reviewed signature, definition, recursive-body, "
                    "and deferred-body occurrences are allowed; any occurrence drift "
                    "aborts regeneration"
                ),
            },
            "input_policy": (
                "authenticate the pinned original source before applying an exact "
                "ordered replacement sequence whose byte or span anchors must occur "
                "once; authenticate every removed span independently"
            ),
            "output_policy": (
                "authenticate the normalized byte count, MD5, and SHA-256 before "
                "parsing or evaluating the result"
            ),
            "failure_policy": (
                "commit, path, input digest, original anchor count/line, operation "
                "order, output size, or output digest drift aborts; heuristic and "
                "blanket rewrites are forbidden"
            ),
            "scope_limit": (
                "the rules are site-specific; qmap, unsuppress, and strictbuild's "
                "use_file_b are selected-static-route non-use refinements that fail "
                "closed on any call; the LP rules require the exact prepared-input "
                "contract and static 39-file inventory; the Serialization.St rule "
                "implements only the exact selected empty/add/mem observations; "
                "dynamic eval_command, obsolete ssreflect lookup, and future theorem-"
                "database updates fail closed after the one unobserved initial cache "
                "mutation is eliminated; "
                "compiled, fingerprint, and "
                "performance gates remain open"
            ),
            "reference_implementation": {
                "repository": "https://github.com/ocaml/ocaml.git",
                "tag": "4.14.1",
                "commit": "99cb5d93fc30f1a6f3e69f5aa5d2063994d33a93",
                "sources": [
                    "stdlib/stdlib.ml:69-77",
                    "lambda/translprim.ml:165",
                    "lambda/translprim.ml:475-482",
                    "lambda/translprim.ml:543-547",
                    "runtime/caml/mlvalues.h:75-80",
                ],
            },
            "gates": [
                "candle:candle/test_flyspeck_normalize.py",
                "candle:candle/test_check_flyspeck_normalized_identity.py",
                "candle:candle/test_flyspeck_identity_normalization.sh",
                "candle:candle/test_flyspeck_immediate_normalization.sh",
                "candle:candle/test_flyspeck_needs_directive.sh",
                "candle:candle/test_flyspeck_parser_orpattern_normalization.sh",
                "candle:candle/test_flyspeck_set_make_normalization.sh",
                "candle:candle/test_flyspeck_toplevel_normalization.sh",
            ],
            "performance_probe": (
                "candle:candle/flyspeck_identity_benchmark.ml"
            ),
        },
        "bootstrap_roots": [ref.key for ref in bootstrap],
        "loader": {
            "source": loader_source.key,
            "required_build_mode": "full",
            "configuration_bindings": [
                "candle_hollight_root", "candle_flyspeck_root",
                "candle_flyspeck_overlay_root", "candle_flyspeck_generated_root",
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
            "activation_status": (
                "exact-static-link-selection-active-member-compatibility-partial"
            ),
            "directive_policy": (
                "accept only a complete standalone #load phrase for a listed "
                "library and select its fixed statically linked module; reject "
                "every other #load; selection is not full member compatibility"
            ),
            "activation_source": "cakeml:candle/prover/candle_boot.ml",
            "activation_gate": "candle:candle/test_static_load_directive.sh",
            "member_compatibility_status": (
                "partial-and-fail-closed-as-recorded-per-library"
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
                    "status": (
                        "startup-metadata-and-zero-telemetry-explicit-fail-otherwise"
                    ),
                    "members": sorted(STATIC_RUNTIME_MEMBERS["Unix"]),
                    "source": "candle:candle/ocaml.ml",
                    "deterministic_process_inputs": deterministic_process_inputs,
                    "telemetry_policy": (
                        "gettimeofday returns deterministic Float.zero; exact "
                        "selected consumers use elapsed values only for reports, "
                        "and the external release runner owns wall/RSS telemetry"
                    ),
                    "telemetry_uses": [
                        entry for entry in sorted(
                            qualified_runtime_contract_uses,
                            key=lambda item: (
                                str(item["source"]), int(item["line"]),
                                str(item["module"]), str(item["member"]),
                            ),
                        )
                        if entry["module"] == "Unix"
                        and entry["member"] == "gettimeofday"
                    ],
                    "process_filesystem_route": {
                        "status": (
                            "selected-proof-route-static-nonuse-with-"
                            "fail-closed-bindings-pending-complete-run"
                        ),
                        "lp_mkdir_disposition": {
                            "source": (
                                "flyspeck:formal_lp/hypermap/main/"
                                "lp_certificate.hl"
                            ),
                            "original_line": 108,
                            "normalization": (
                                "PROJECT-FFI-S3-LP-SHELL-ELIMINATION-001"
                            ),
                            "effect": (
                                "the authenticated ordinary-certificate overlay "
                                "removes mkdir, chdir, command, readdir, tar, and rm"
                            ),
                        },
                        "glpk_generator_chain": {
                            "reviewed_occurrences": sorted(
                                reviewed_process_route_uses,
                                key=lambda entry: (
                                    str(entry["source"]), int(entry["line"]),
                                    str(entry["identifier"]),
                                ),
                            ),
                            "reviewed_occurrence_count": len(
                                reviewed_process_route_uses
                            ),
                            "external_qualified_uses": (
                                process_route_qualified_uses
                            ),
                            "module_opens": process_route_module_opens,
                            "route_root": "Lpproc.execute",
                            "definition_only_entrypoints": [
                                "Glpk_link.cpx_branch",
                                "Glpk_link.display_ampl",
                                "Glpk_link.display_lp",
                                "Glpk_link.get_dumpvar",
                                "Glpk_link.solve_dual_f",
                                "Glpk_link.strip_archive",
                                "Lpproc.execute",
                            ],
                            "policy": (
                                "load the shared pure definitions, but keep Sys.chdir, "
                                "Sys.command, Unix.open_process, Unix.close_process, "
                                "and Unix.mkdir fail-closed; any unexpected invocation "
                                "must abort the one-shot S3 run"
                            ),
                            "assurance_limit": (
                                "the exact lexical chain and absence of selected "
                                "external callers are necessary non-use evidence, not "
                                "proof against reflection or external input; a complete "
                                "compiled run and final theorem fingerprints remain "
                                "mandatory"
                            ),
                        },
                    },
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
            "activation_status": (
                "partial-exact-static-normalizations-active-pending-full-run"
            ),
            "policy": (
                "Toploop and dynamically evaluated source are correctness-relevant; "
                "a dummy return, silent skip, unchecked Obj.magic, or successful "
                "no-op implementation is forbidden. Exact selected-route "
                "dead-effect elimination and fail-closed non-use bindings require "
                "complete-run and final-fingerprint confirmation"
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
                "therefore cannot be implemented by a dummy evaluator. The selected "
                "update_database_400 payload block is removed by an exact hash-bound "
                "dead-effect normalization; any future observation requires an "
                "explicit typed registry or verified dynamic-evaluation contract"
            ),
            "selected_execution_disposition": {
                "serialization_branch_action": (
                    "PROJECT-MODULE-S3-SET-MAKE-001"
                ),
                "update_database_dead_effect": (
                    "PROJECT-TOPLOOP-S3-UPDATE-DATABASE-001"
                ),
                "definition_only_fail_closed": [
                    "PROJECT-TOPLOOP-S3-EVAL-COMMAND-001",
                    "PROJECT-TOPLOOP-S3-SSREFLECT-LOOKUP-001",
                    "PROJECT-TOPLOOP-S3-USE-FILE-B-001",
                ],
                "unselected_original_source": (
                    "flyspeck:text_formalization/general/update_database_310.ml"
                ),
                "acceptance_gate": (
                    "complete compiled selected run with exact theorem, assumption, "
                    "and target fingerprints"
                ),
            },
            "consumer_inventory": {
                "scope": (
                    "exact identifiers in reachable Flyspeck source, outside "
                    "comments, strings, and HOL quotations"
                ),
                "reviewed_occurrences": sorted(
                    reviewed_consumer_uses,
                    key=lambda entry: (
                        str(entry["source"]), int(entry["line"]),
                        str(entry["identifier"]),
                    ),
                ),
                "identifier_counts": consumer_identifier_counts,
                "selected_active_site": {
                    "source": (
                        "flyspeck:text_formalization/general/"
                        "update_database_400.ml"
                    ),
                    "line": 338,
                    "identifier": "update_database",
                    "effect": (
                        "load-time compiler-environment enumeration and theorem "
                        "database replacement"
                    ),
                    "execution_disposition": (
                        "exact selected-route dead-effect elimination; update_database "
                        "remains fail-closed for every deferred caller"
                    ),
                },
                "definition_only_selected_graph": [
                    "eval_command", "save_all_theorems", "test_id_thm",
                    "use_arg_then",
                ],
                "typed_theorem_lookup": {
                    "identifier": TYPED_THEOREM_LOOKUP_IDENTIFIER,
                    "occurrences": typed_theorem_lookup_occurrences,
                    "source_files": len(typed_theorem_lookup_counts),
                    "by_source": [
                        {"source": source, "occurrences": count}
                        for source, count in sorted(
                            typed_theorem_lookup_counts.items()
                        )
                    ],
                    "distinction": (
                        "use_arg_then2 receives an explicit theorem fallback and "
                        "does not call Toploop; it must not be conflated with the "
                        "definition-only use_arg_then"
                    ),
                },
                "assurance_limit": (
                    "lexical non-use is necessary evidence for a narrow "
                    "normalization, not a proof against reflection, constructed "
                    "names, or an external caller; compiled reference and final "
                    "fingerprint gates remain mandatory"
                ),
            },
        },
        "lp_archive_preparation_contract": {
            "activation_status": "materializer-ready-pending-direct-runtime-leaf",
            "contract_source": f"candle:{LP_ARCHIVE_CONTRACT}",
            "contract_sha256": hashlib.sha256(
                lp_archive_contract_path.read_bytes()
            ).hexdigest(),
            "flyspeck_commit": lp_archive_contract["flyspeck_commit"],
            "archive": lp_archive_contract["archive"],
            "members": lp_archive_contract["members"],
            "policy": lp_archive_contract["policy"],
            "runtime_certificate_basenames": lp_runtime_certificate_basenames,
            "runtime_certificate_basenames_sha256": hashlib.sha256(
                json.dumps(
                    lp_runtime_certificate_basenames,
                    separators=(",", ":"),
                ).encode()
            ).hexdigest(),
            "runtime_contract": (
                "the compiled S3 route receives the prepared ordinary file and "
                "must not invoke a shell, tar, rm, or runtime archive extraction"
            ),
            "evidence_boundary": (
                "preparation authenticates bytes and container shape; the HOL-side "
                "LP verifier remains responsible for certificate validity"
            ),
        },
        "loader_action_contract": {
            "scope": "all loading syntax in the reachable direct-source graph",
            "activation_status": "partial-exact-static-actions-active",
            "static_action_source": "cakeml:candle/prover/candle_boot.ml@1b17732f",
            "static_action_gate": "candle:candle/test_flyspeck_needs_directive.sh",
            "source_site_count": loader_action_site_count,
            "site_counts": [
                {"kind": kind, "status": status, "count": count}
                for (kind, status), count
                in sorted(dependency_kind_status_counts.items())
            ],
            "syntax_position_counts": [
                {"kind": kind, "position": position, "count": count}
                for (kind, position), count
                in sorted(dependency_position_counts.items())
            ],
            "generated_static_root_directives": len(sequence),
            "recognition_policy": (
                "a source directive is recognized only when it is the complete "
                "standalone top-level phrase and has its exact literal grammar; "
                "an identifier in a definition, conditional, function body, "
                "argument, or other expression is ordinary source syntax"
            ),
            "embedded_expression_policy": (
                "embedded loading calls require ordinary verified evaluation or "
                "an exact hash-bound normalization that preserves the pinned "
                "branch and call semantics; the boot scanner must not execute "
                "both sides of a conditional"
            ),
            "required_actions": {
                "#load": (
                    "activate only an exact allowlisted static library; unknown, "
                    "inactive, or malformed directives abort"
                ),
                "#use": "evaluate the literal source even if previously loaded",
                "loads": "evaluate the literal source even if previously loaded",
                "needs": "evaluate once and skip an already-loaded source",
                "loadt": "evaluate even if previously loaded",
                "flyspeck_needs": (
                    "if new, evaluate in place, require success, neutralize state "
                    "exactly once, and record success only after both return; if "
                    "already loaded, do neither; any failure aborts the one-shot "
                    "process"
                ),
                "#flyspeck_needs": (
                    "enforce the generated index, stratum, selected source key, "
                    "source hash, and root order, then apply the accepted-run-exact, "
                    "fail-closed flyspeck_needs refinement"
                ),
                "#flyspeck_loadt": (
                    "authenticate the exact source identity, evaluate on every "
                    "occurrence, commit that logical identity after success even "
                    "when repeated, and never neutralize state"
                ),
                "reneeds": "evaluate even if previously loaded, without neutralization",
            },
            "ordinary_directive_boundary_status": (
                "compiled exact phrase-start recognition is active for ordinary "
                "needs, loads, and #use as well as #load, #flyspeck_needs, and "
                "#flyspeck_loadt; needs/loads identifiers inside definitions, "
                "conditionals, and function bodies remain ordinary source syntax"
            ),
            "forbidden_shortcuts": [
                "blanket directive erasure",
                "successful no-op source load",
                "neutralization before or after failed evaluation",
                "neutralization for a duplicate skip",
                "treating loads/loadt/reneeds as duplicate-skipping needs",
            ],
        },
        "final_target": {
            "source": final_target.key,
            "name": "Candle_flyspeck_l2.tame_imp_kepler_conjecture",
            "statement": "import_tame_classification ==> the_kepler_conjecture",
            "imported_premises": ["import_tame_classification"],
        },
        "source_node_count": len(nodes),
        "source_edge_count": sum(len(targets) for targets in edges.values()),
        "dopen_corpus_contract": {
            "scope": "declaration opens in the reachable direct-source full-build graph",
            "activation_status": (
                "verified-source-stack-integration-pending-compiler-rebuild-and-corpus-run"
            ),
            "verified_cakeml_integration": {
                "branch": "codex/flyspeck-v13-integration",
                "commit": "936219bbc3021fa20418d62e85155f2d0092b9f9",
                "dopen_proof_target": "compiler/inference/tests/dopenTestsTheory.uo",
                "dopen_proof_theories": 39,
                "ocaml_parser_target": "compiler/parsing/ocaml/camlTestsTheory.uo",
                "proof_hol4_commit": "a390cbabd3a4521bab4ee20281e3e42933a8a3ae",
                "soundness_targets": [
                    "semantics/proofs/namespacePropsTheory.uo",
                    "semantics/proofs/weakeningTheory.uo",
                    "semantics/proofs/typeSoundTheory.uo",
                    "translator/evaluate_decTheory.uo",
                    "candle/prover/permsTheory.uo",
                ],
                "soundness_repairs": [
                    "d4ed3e6d5b811dd2457f46d494b30bc67b706fdf",
                    "a336d8493b1ffc81b3a93348c4326d6200cf2d78",
                    "ed49b28052c79abf612642921bff808c16f2332b",
                    "fec48e7d76b7d3b132ef2d420279a5f0655c76f7",
                    "936219bbc3021fa20418d62e85155f2d0092b9f9",
                ],
            },
            "required_gate": (
                "rebuild the x64-64 compiler from the pinned verified integration, "
                "then require a real corpus-derived open-dependent compiled Candle "
                "slice to match pinned OCaml/HOL Light reference fingerprints"
            ),
            "exclusions": (
                "local let-open and parenthesized local-open expressions are separate "
                "frontend forms and are not Dopen declarations"
            ),
            "occurrence_count": len(sorted_declaration_opens),
            "source_file_count": len({
                str(entry["source"]) for entry in sorted_declaration_opens
            }),
            "module_path_count": len({
                str(entry["module_path"]) for entry in sorted_declaration_opens
            }),
            "path_form_counts": {
                form: sum(
                    entry["path_form"] == form
                    for entry in sorted_declaration_opens
                )
                for form in ("simple", "dotted")
            },
            "override_warning_suppression_count": sum(
                bool(entry["override_warning_suppression"])
                for entry in sorted_declaration_opens
            ),
            "site_digest_format": (
                "SHA-256 of canonical compact sorted JSON records with source, line, "
                "module_path, path_form, and override_warning_suppression"
            ),
            "site_sha256": hashlib.sha256(declaration_open_site_bytes).hexdigest(),
            "earliest_stratum_counts": declaration_open_strata,
        },
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
    full_build_path = candle_root / FULL_BUILD_PROGRAM
    payload = build_manifest(candle_root, arguments.flyspeck_root.resolve())
    rendered = _render(payload)
    source_digest_rendered = _render_source_digest_program(payload["source_nodes"])
    full_build_rendered = _render_full_build_program(
        payload["build_sequence"],
        payload["build_sequence_roots"],
        payload["source_nodes"],
        payload["build_strata"],
    )
    source_digest_sha256 = hashlib.sha256(source_digest_rendered.encode()).hexdigest()
    if source_digest_sha256 != payload["source_digest_contract"]["generated_source_sha256"]:
        raise SystemExit("internal source digest program hash mismatch")
    full_build_sha256 = hashlib.sha256(full_build_rendered.encode()).hexdigest()
    if full_build_sha256 != payload["static_full_build_contract"]["generated_source_sha256"]:
        raise SystemExit("internal static full-build program hash mismatch")
    if arguments.write:
        source_digest_path.write_text(source_digest_rendered, encoding="utf-8")
        full_build_path.write_text(full_build_rendered, encoding="utf-8")
        manifest_path.write_text(rendered, encoding="utf-8")
    elif (
        not manifest_path.is_file()
        or manifest_path.read_text(encoding="utf-8") != rendered
        or not source_digest_path.is_file()
        or source_digest_path.read_text(encoding="utf-8") != source_digest_rendered
        or not full_build_path.is_file()
        or full_build_path.read_text(encoding="utf-8") != full_build_rendered
    ):
        raise SystemExit(
            f"stale manifest or generated program: run {Path(__file__).name} --write"
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
