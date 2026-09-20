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
SOURCE_NORMALIZATION = "candle-flyspeck-nonlinear-closure-compatibility-v7"
NESTED_ARRAY_NORMALIZATION = SOURCE_NORMALIZATION
NORMALIZATION_SEMANTIC_RULE = (
    "make native OCaml grouping explicit: chained array accesses use "
    "Array.get/Array.set with parenthesized indices; module-qualified record "
    "labels use the same unqualified labels under an explicit original record "
    "type; and a ref assignment's conditional RHS is parenthesized. The "
    "complete remaining top-level Hashtbl.create inventory states the exact "
    "key and value types already forced by its uses. The "
    "closed verifier extension's fixed %d/%s/%b diagnostic formats use exact "
    "literal concatenation and primitive conversions; optional file logging "
    "fails closed if invoked because Candle has no channel-backed formatter. "
    "The private raw-float comparator orders the two Num-valued numeral "
    "exponents with Num.le_num instead of unavailable OCaml polymorphic <=; "
    "native canonical nonnegative integer Num values have the same structural "
    "and numeric order, including across the Int/Big_int boundary. The two "
    "float-splitting implementations route their zero, infinity, and NaN "
    "tests through float_ieee_equal, preserving OCaml float equality despite "
    "CakeML generic equality's representation semantics; their adjacent "
    "native float orderings use typed IEEE helpers instead of Candle's "
    "integer-only unqualified operators. The twelve active raw-double "
    "threshold and angle-reduction comparisons use the same typed IEEE "
    "helpers. All 14 "
    "active native assert sites call one condition-preserving helper that "
    "raises the existing distinct Assert_failure on false"
)
NORMALIZATION_SCOPE_LIMIT = (
    "This bounded parser normalization is confined to the authenticated "
    "formal-verifier closure and only makes native OCaml grouping explicit. "
    "It changes no theorem statement, hypothesis, proof step, proof intent, "
    "runtime primitive, or axiom. Existing direct-Flyspeck execution "
    "normalizations remain authoritative and are applied from the shared "
    "versioned normalization contract. Hash-table annotations change no "
    "allocation, operation, contents, or exceptions. Diagnostic-only "
    "substitutions preserve "
    "the fixed rendered bytes except the unused elapsed-time suffix, which "
    "fails closed; optional float logging is disabled only while its controlling "
    "flag remains false and any invocation fails closed. The Num ordering "
    "rewrite is confined to the two nonnegative numeral hashes passed to the "
    "private compare_floats_raw helper; it does not authorize general "
    "polymorphic comparison or change a theorem statement or inference. The "
    "float equality rewrites are confined to the identical split/fix tests in "
    "more_float and informal_float; they preserve signed-zero equality, NaN "
    "inequality, infinity equality, and every finite nonzero comparison. The "
    "typed ordering rewrites cover exactly the three adjacent split branches "
    "in each implementation plus twelve raw-double threshold and angle "
    "branches in seven authenticated sources; they preserve native "
    "false-on-NaN behavior. The "
    "assert rewrites preserve condition evaluation, success value, and failure "
    "constructor; only the run-local native source position is replaced by a "
    "stable logical source label with zero line/column fields."
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


def _replacement(
    kind: str,
    before: bytes,
    after: bytes,
    count: int = 1,
) -> tuple[str, bytes, bytes, int]:
    return kind, before, after, count


EXTENSION_COMPATIBILITY_REPLACEMENTS = {
    "flyspeck:formal_ineqs/arith/float_pow.hl": (
        _replacement(
            "float-pow-assert-gt2",
            b'assert (n > 2)',
            b'candle_assert (n > 2) "formal_ineqs/arith/float_pow.hl"',
            2,
        ),
        _replacement(
            "float-pow-assert-gt1",
            b'assert (n > 1)',
            b'candle_assert (n > 1) "formal_ineqs/arith/float_pow.hl"',
        ),
    ),
    "flyspeck:formal_ineqs/arith/more_float.hl": (
        _replacement(
            "more-float-ieee-special-equality",
            b'if t = 0.0 || t = infinity || t = nan then',
            b'if float_ieee_equal t 0.0 || float_ieee_equal t infinity || '
            b'float_ieee_equal t nan then',
        ),
        _replacement(
            "more-float-ieee-zero-equality",
            b'if f = 0.0 then',
            b'if float_ieee_equal f 0.0 then',
        ),
        _replacement(
            "more-float-ieee-unit-order",
            b'else if t < 1.0 then',
            b'else if float_ieee_lt t 1.0 then',
        ),
        _replacement(
            "more-float-ieee-base-order",
            b'else if t >= b then',
            b'else if float_ieee_ge t b then',
        ),
        _replacement(
            "more-float-ieee-sign-order",
            b'if f < 0.0 then',
            b'if float_ieee_lt f 0.0 then',
        ),
    ),
    "flyspeck:formal_ineqs/arith/arith_float.hl": (
        _replacement(
            "arith-float-lo-table-type",
            b'let lo_thm_table = Hashtbl.create Arith_num.arith_base;;',
            b'let lo_thm_table : (term, thm) Hashtbl.t = '
            b'Hashtbl.create Arith_num.arith_base;;',
        ),
        _replacement(
            "arith-float-lo2-table-type",
            b'let lo_thm2_table = Hashtbl.create Arith_num.arith_base;;',
            b'let lo_thm2_table : (term, thm) Hashtbl.t = '
            b'Hashtbl.create Arith_num.arith_base;;',
        ),
        _replacement(
            "arith-float-hi-table-type",
            b'let hi_thm_table = Hashtbl.create Arith_num.arith_base;;',
            b'let hi_thm_table : (term, thm) Hashtbl.t = '
            b'Hashtbl.create Arith_num.arith_base;;',
        ),
        _replacement(
            "arith-float-cache-table-types",
            b'''let mul_table = Hashtbl.create cache_size and\r
    div_table = Hashtbl.create cache_size and\r
    add_table = Hashtbl.create cache_size and\r
    sub_table = Hashtbl.create cache_size and\r
    sqrt_table = Hashtbl.create cache_size and\r
    le_table = Hashtbl.create cache_size and\r
    max_table = Hashtbl.create cache_size;;''',
            b'''let mul_table : (string, thm) Hashtbl.t = Hashtbl.create cache_size and\r
    div_table : (string, thm) Hashtbl.t = Hashtbl.create cache_size and\r
    add_table : (string, thm) Hashtbl.t = Hashtbl.create cache_size and\r
    sub_table : (string, thm) Hashtbl.t = Hashtbl.create cache_size and\r
    sqrt_table : (string, thm) Hashtbl.t = Hashtbl.create cache_size and\r
    le_table : (string, thm) Hashtbl.t = Hashtbl.create cache_size and\r
    max_table : (string, thm) Hashtbl.t = Hashtbl.create cache_size;;''',
        ),
        _replacement(
            "arith-float-num-exponent-order",
            b'if e1 <= e2 then',
            b'if le_num e1 e2 then',
        ),
        _replacement(
            "arith-float-stat-cmp1",
            b'sprintf "lt0 = %d\\ngt0 = %d\\nlt = %d\\n" !lt0_c !gt0_c !lt_c',
            b'"lt0 = " ^ string_of_int !lt0_c ^ "\\ngt0 = " ^ '
            b'string_of_int !gt0_c ^ "\\nlt = " ^ string_of_int !lt_c ^ "\\n"',
        ),
        _replacement(
            "arith-float-stat-cmp2",
            b'sprintf "le0 = %d\\nge0 = %d\\n" !le0_c !ge0_c',
            b'"le0 = " ^ string_of_int !le0_c ^ "\\nge0 = " ^ '
            b'string_of_int !ge0_c ^ "\\n"',
        ),
        _replacement(
            "arith-float-stat-cmp3",
            b'sprintf "min = %d\\nmin_max = %d\\n" !min_c !min_max_c',
            b'"min = " ^ string_of_int !min_c ^ "\\nmin_max = " ^ '
            b'string_of_int !min_max_c ^ "\\n"',
        ),
        _replacement(
            "arith-float-stat-le",
            b'sprintf "le = %d (le_hash = %d)\\n" !le_c (len le_table)',
            b'"le = " ^ string_of_int !le_c ^ " (le_hash = " ^ '
            b'string_of_int (len le_table) ^ ")\\n"',
        ),
        _replacement(
            "arith-float-stat-max",
            b'sprintf "max = %d (max_hash = %d)\\n" !max_c (len max_table)',
            b'"max = " ^ string_of_int !max_c ^ " (max_hash = " ^ '
            b'string_of_int (len max_table) ^ ")\\n"',
        ),
        _replacement(
            "arith-float-stat-mul",
            b'sprintf "mul_lo = %d, mul_hi = %d (mul_hash = %d)\\n" !mul_lo_c !mul_hi_c (len mul_table)',
            b'"mul_lo = " ^ string_of_int !mul_lo_c ^ ", mul_hi = " ^ '
            b'string_of_int !mul_hi_c ^ " (mul_hash = " ^ '
            b'string_of_int (len mul_table) ^ ")\\n"',
        ),
        _replacement(
            "arith-float-stat-div",
            b'sprintf "div_lo = %d, div_hi = %d (div_hash = %d)\\n" !div_lo_c !div_hi_c (len div_table)',
            b'"div_lo = " ^ string_of_int !div_lo_c ^ ", div_hi = " ^ '
            b'string_of_int !div_hi_c ^ " (div_hash = " ^ '
            b'string_of_int (len div_table) ^ ")\\n"',
        ),
        _replacement(
            "arith-float-stat-add",
            b'sprintf "add_lo = %d, add_hi = %d (add_hash = %d)\\n" !add_lo_c !add_hi_c (len add_table)',
            b'"add_lo = " ^ string_of_int !add_lo_c ^ ", add_hi = " ^ '
            b'string_of_int !add_hi_c ^ " (add_hash = " ^ '
            b'string_of_int (len add_table) ^ ")\\n"',
        ),
        _replacement(
            "arith-float-stat-sub",
            b'sprintf "sub_lo = %d, sub_hi = %d (sub_hash = %d)\\n" !sub_lo_c !sub_hi_c (len sub_table)',
            b'"sub_lo = " ^ string_of_int !sub_lo_c ^ ", sub_hi = " ^ '
            b'string_of_int !sub_hi_c ^ " (sub_hash = " ^ '
            b'string_of_int (len sub_table) ^ ")\\n"',
        ),
        _replacement(
            "arith-float-stat-sqrt",
            b'sprintf "sqrt_lo = %d, sqrt_hi = %d (sqrt_hash = %d)\\n" !sqrt_lo_c !sqrt_hi_c (len sqrt_table)',
            b'"sqrt_lo = " ^ string_of_int !sqrt_lo_c ^ ", sqrt_hi = " ^ '
            b'string_of_int !sqrt_hi_c ^ " (sqrt_hash = " ^ '
            b'string_of_int (len sqrt_table) ^ ")\\n"',
        ),
    ),
    "flyspeck:formal_ineqs/informal/informal_float.hl": (
        _replacement(
            "informal-float-ieee-special-equality",
            b'if t = 0.0 || t = infinity || t = nan then',
            b'if float_ieee_equal t 0.0 || float_ieee_equal t infinity || '
            b'float_ieee_equal t nan then',
        ),
        _replacement(
            "informal-float-ieee-zero-equality",
            b'if f = 0.0 then',
            b'if float_ieee_equal f 0.0 then',
        ),
        _replacement(
            "informal-float-ieee-unit-order",
            b'else if t < 1.0 then',
            b'else if float_ieee_lt t 1.0 then',
        ),
        _replacement(
            "informal-float-ieee-base-order",
            b'else if t >= b then',
            b'else if float_ieee_ge t b then',
        ),
        _replacement(
            "informal-float-ieee-sign-order",
            b'if f < 0.0 then',
            b'if float_ieee_lt f 0.0 then',
        ),
        _replacement(
            "informal-float-assert-nonnegative",
            b'assert (n >= 0)',
            b'candle_assert (n >= 0) "formal_ineqs/informal/informal_float.hl"',
            2,
        ),
        _replacement(
            "informal-float-assert-gt2",
            b'assert (n > 2)',
            b'candle_assert (n > 2) "formal_ineqs/informal/informal_float.hl"',
            2,
        ),
        _replacement(
            "informal-float-plain",
            b'Printf.sprintf "%s%s" s_str n_str',
            b's_str ^ n_str',
        ),
        _replacement(
            "informal-float-scaled",
            b'Printf.sprintf "%s%s*%d^%d" s_str n_str arith_base k',
            b's_str ^ n_str ^ "*" ^ string_of_int arith_base ^ "^" ^ '
            b'string_of_int k',
        ),
    ),
    "flyspeck:formal_ineqs/informal/informal_atn.hl": (
        _replacement(
            "informal-atn-ieee-tail-order",
            b'if r <= t then i else try_i (i + 1)',
            b'if float_ieee_le r t then i else try_i (i + 1)',
        ),
        _replacement(
            "informal-atn-assert-x1-sign",
            b'assert (sign_float x1 = false)',
            b'candle_assert (sign_float x1 = false) '
            b'"formal_ineqs/informal/informal_atn.hl"',
        ),
        _replacement(
            "informal-atn-assert-lo-sign",
            b'assert (sign_float lo = false)',
            b'candle_assert (sign_float lo = false) '
            b'"formal_ineqs/informal/informal_atn.hl"',
        ),
        _replacement(
            "informal-atn-assert-t-sign",
            b'assert (sign_float t = false)',
            b'candle_assert (sign_float t = false) '
            b'"formal_ineqs/informal/informal_atn.hl"',
            2,
        ),
    ),
    "flyspeck:formal_ineqs/informal/informal_exp.hl": (
        _replacement(
            "informal-exp-ieee-tail-order",
            b'if r <= t then i else try_i (i + 1)',
            b'if float_ieee_le r t then i else try_i (i + 1)',
        ),
        _replacement(
            "informal-exp-ieee-reduction-order",
            b'if f <= exp_max_x then',
            b'if float_ieee_le f exp_max_x then',
        ),
    ),
    "flyspeck:formal_ineqs/informal/informal_interval.hl": (
        _replacement(
            "informal-interval-assert-gt1",
            b'assert (n > 1)',
            b'candle_assert (n > 1) '
            b'"formal_ineqs/informal/informal_interval.hl"',
        ),
    ),
    "flyspeck:formal_ineqs/informal/informal_search.hl": (
        _replacement(
            "search-progress",
            b'Printf.sprintf "%d " !last_report',
            b'string_of_int !last_report ^ " "',
        ),
        _replacement(
            "search-depth-error",
            b'Printf.sprintf "depth (%d) > max_depth (%d)" depth opt.max_depth',
            b'"depth (" ^ string_of_int depth ^ ") > max_depth (" ^ '
            b'string_of_int opt.max_depth ^ ")"',
        ),
    ),
    "flyspeck:formal_ineqs/informal/informal_sin_cos.hl": (
        _replacement(
            "informal-cos-ieee-tail-order",
            b'if r <= t then i else try_i (i + 1)',
            b'if float_ieee_le r t then i else try_i (i + 1)',
        ),
        _replacement(
            "informal-cos-ieee-reduction-lower-order",
            b'if y < -.f_pi then k0 + 1',
            b'if float_ieee_lt y (-.f_pi) then k0 + 1',
        ),
        _replacement(
            "informal-cos-ieee-reduction-upper-order",
            b'else if y > f_pi then k0 - 1',
            b'else if float_ieee_gt y f_pi then k0 - 1',
        ),
        _replacement(
            "informal-sin-cos-assert-negative",
            b'assert (i < 0)',
            b'candle_assert (i < 0) '
            b'"formal_ineqs/informal/informal_sin_cos.hl"',
        ),
        _replacement(
            "informal-sin-cos-assert-nonnegative",
            b'assert (i >= 0)',
            b'candle_assert (i >= 0) '
            b'"formal_ineqs/informal/informal_sin_cos.hl"',
        ),
        _replacement(
            "informal-cos-constant-warning",
            b'Printf.sprintf "cos_interval: reduction failed"',
            b'"cos_interval: reduction failed"',
        ),
    ),
    "flyspeck:formal_ineqs/informal/informal_verifier.hl": (
        _replacement(
            "informal-testing-precision",
            b'sprintf "Testing p = %d (other: %d)" p (length ps)',
            b'"Testing p = " ^ string_of_int p ^ " (other: " ^ '
            b'string_of_int (length ps) ^ ")"',
        ),
        _replacement(
            "informal-precision-failure",
            b'sprintf "Failure at p = %d: %s" p msg',
            b'"Failure at p = " ^ string_of_int p ^ ": " ^ msg',
        ),
        _replacement(
            "informal-division-failure",
            b'sprintf "Failure at p = %d: Division_by_zero" p',
            b'"Failure at p = " ^ string_of_int p ^ ": Division_by_zero"',
        ),
        _replacement(
            "informal-selected-precision",
            b'sprintf "p = %d" p',
            b'"p = " ^ string_of_int p',
        ),
        _replacement(
            "informal-mono-status",
            b'sprintf "%s%d (%b)" (if m.decr_flag then "-" else "") \n\t\t       m.variable m.df0_flag',
            b'(if m.decr_flag then "-" else "") ^ string_of_int m.variable ^\n'
            b'                       " (" ^ (if m.df0_flag then "true" else "false") ^ ")"',
        ),
        _replacement(
            "informal-mono-report",
            b'sprintf "Mono: [%s]" (String.concat ";" mono_strs)',
            b'"Mono: [" ^ String.concat ";" mono_strs ^ "]"',
        ),
        _replacement(
            "informal-pass-progress",
            b'sprintf "Verifying: %d/%d (f0_flag = %b)" !k r_size f0_flag',
            b'"Verifying: " ^ string_of_int !k ^ "/" ^ string_of_int r_size ^ '
            b'" (f0_flag = " ^ (if f0_flag then "true" else "false") ^ ")"',
        ),
        _replacement(
            "informal-percent-progress",
            b'sprintf "%d " r',
            b'string_of_int r ^ " "',
        ),
        _replacement(
            "informal-reference-progress",
            b'sprintf "Ref: %d" i',
            b'"Ref: " ^ string_of_int i',
        ),
        _replacement(
            "informal-list-progress",
            b'sprintf "List: %d/%d" !k size',
            b'"List: " ^ string_of_int !k ^ "/" ^ string_of_int size',
        ),
    ),
    "flyspeck:formal_ineqs/misc/report.hl": (
        _replacement(
            "report-time-fail-closed",
            b'let time_string () =   Printf.sprintf "time(%.0f)" (Sys.time());;',
            b'let time_string () =\n  failwith "Candle Flyspeck: timed diagnostic formatting is unavailable";;',
        ),
        _replacement(
            "report-error-count",
            b'Printf.sprintf "(errors %d)" (get_error_count())',
            b'"(errors " ^ string_of_int (get_error_count()) ^ ")"',
        ),
        _replacement(
            "report-error-message",
            b'Printf.sprintf "error(%d) --\\n%s" ec s',
            b'"error(" ^ string_of_int ec ^ ") --\\n" ^ s',
        ),
    ),
    "flyspeck:formal_ineqs/taylor/m_taylor.hl": (
        _replacement(
            "taylor-vector-size-error",
            b'sprintf "Wrong vector size; expected size: %d" n',
            b'"Wrong vector size; expected size: " ^ string_of_int n',
            3,
        ),
    ),
    "flyspeck:formal_ineqs/tests/log.hl": (
        _replacement(
            "optional-channel-logging-fail-closed",
            b'''let open_log, close_log, close_all_logs, append_to_log, log_fmt =
  (* [name, (channel, formatter)] *)
  let logs = ref [] in
  let log_for_name name =''' + b" \n" + b'''    try
      Some (assoc name !logs)
    with Failure _ ->
      None
  in
  let add_log name (c, fmt) =
    logs := (name, (c, fmt)) :: !logs
  in
  let delete_log name =
    logs := filter (fun (n, _) -> n <> name) !logs
  in
  let close_log name =
    match log_for_name name with
      | None -> ()
      | Some (c, _) ->
	  close_out c;
	  delete_log name
  in
  let close_all_logs () =
    let names = map fst !logs in
    let _ = map close_log names in
      ()
  in
  let open_log name =
    match log_for_name name with
      | Some _ -> ()
      | None ->
	  let _ = get_dir "log" in
	  let log_name = Filename.concat "log" (Filename.basename name ^ ".log") in
	  let c = open_out log_name in
	  let fmt = formatter_of_out_channel c in
	    add_log name (c, fmt)
  in
  let append_to_log name str =
    match log_for_name name with
      | None -> ()
      | Some (_, fmt) ->
	pp_print_string fmt str;
	pp_print_newline fmt ()
  in
  let log_fmt name =
    match log_for_name name with
      | None -> None
      | Some (_, fmt) -> Some fmt
  in
  open_log,
  close_log,
  close_all_logs,
  append_to_log,
  log_fmt;;''',
            b'''let candle_disabled_log () =
  failwith "Candle Flyspeck: optional float logging is unavailable";;

let open_log name = let _ = name in candle_disabled_log ();;
let close_log name = let _ = name in candle_disabled_log ();;
let close_all_logs () = candle_disabled_log ();;
let append_to_log name str =
  let _ = name in let _ = str in candle_disabled_log ();;
let log_fmt name = let _ = name in candle_disabled_log ();;''',
        ),
    ),
    "flyspeck:formal_ineqs/trig/atn_eval.hl": (
        _replacement(
            "atn-eval-ieee-tail-order",
            b'if r <= t then i else try_i (i + 1)',
            b'if float_ieee_le r t then i else try_i (i + 1)',
        ),
    ),
    "flyspeck:formal_ineqs/trig/cos_bounds_eval.hl": (
        _replacement(
            "cos-bounds-eval-ieee-tail-order",
            b'if r <= t then i else try_i (i + 1)',
            b'if float_ieee_le r t then i else try_i (i + 1)',
        ),
    ),
    "flyspeck:formal_ineqs/trig/cos_eval.hl": (
        _replacement(
            "cos-eval-ieee-reduction-lower-order",
            b'if y < -.f_pi then k0 + 1',
            b'if float_ieee_lt y (-.f_pi) then k0 + 1',
        ),
        _replacement(
            "cos-eval-ieee-reduction-upper-order",
            b'else if y > f_pi then k0 - 1',
            b'else if float_ieee_gt y f_pi then k0 - 1',
        ),
        _replacement(
            "cos-interval-warning",
            b'Printf.sprintf "float_interval_cos: reduction failed (%s, %s)"\n\t\t\t   (string_of_term a_tm) (string_of_term b_tm)',
            b'"float_interval_cos: reduction failed (" ^ string_of_term a_tm ^\n'
            b'                                   ", " ^ string_of_term b_tm ^ ")"',
        ),
        _replacement(
            "cos-reduction-warning",
            b'Printf.sprintf "cos_reduction: reduction failed (%s, %s)"\n\t\t\t (string_of_term a_tm) (string_of_term b_tm)',
            b'"cos_reduction: reduction failed (" ^ string_of_term a_tm ^\n'
            b'                                 ", " ^ string_of_term b_tm ^ ")"',
            2,
        ),
    ),
    "flyspeck:formal_ineqs/trig/exp_eval.hl": (
        _replacement(
            "exp-eval-ieee-tail-order",
            b'if r <= t then i else try_i (i + 1)',
            b'if float_ieee_le r t then i else try_i (i + 1)',
        ),
        _replacement(
            "exp-eval-ieee-reduction-order",
            b'if f <= exp_max_x then',
            b'if float_ieee_le f exp_max_x then',
        ),
    ),
    "flyspeck:formal_ineqs/trig/poly_eval.hl": (
        _replacement(
            "poly-high-coefficient-error",
            b'Printf.sprintf "eval_high_poly_f_pos_pos: non-positive coefficient: %s, %s" \n\t\t  (string_of_term c.c_tm) \n\t\t  (string_of_term c.bounds_tm)',
            b'"eval_high_poly_f_pos_pos: non-positive coefficient: " ^\n'
            b'                  string_of_term c.c_tm ^ ", " ^\n'
            b'                  string_of_term c.bounds_tm',
        ),
        _replacement(
            "poly-low-coefficient-error",
            b'Printf.sprintf "eval_low_poly_f_pos_pos: non-positive coefficient: %s, %s" \n\t\t  (string_of_term c.c_tm) \n\t\t  (string_of_term c.bounds_tm)',
            b'"eval_low_poly_f_pos_pos: non-positive coefficient: " ^\n'
            b'                  string_of_term c.c_tm ^ ", " ^\n'
            b'                  string_of_term c.bounds_tm',
        ),
    ),
    "flyspeck:formal_ineqs/verifier/certificate.hl": (
        _replacement(
            "certificate-stats",
            b'sprintf "pass = %d (pass_raw = %d)\\nmono = %d\\nglue = %d (glue_convex = %d)\\npass_mono = %d"\n'
            b'    stats.pass stats.pass_raw stats.mono stats.glue stats.glue_convex stats.pass_mono',
            b'"pass = " ^ string_of_int stats.pass ^ " (pass_raw = " ^\n'
            b'    string_of_int stats.pass_raw ^ ")\\nmono = " ^ string_of_int stats.mono ^\n'
            b'    "\\nglue = " ^ string_of_int stats.glue ^ " (glue_convex = " ^\n'
            b'    string_of_int stats.glue_convex ^ ")\\npass_mono = " ^\n'
            b'    string_of_int stats.pass_mono',
        ),
        _replacement(
            "certificate-precision-stats",
            b'sprintf "p = %d: %d\\n" p c',
            b'"p = " ^ string_of_int p ^ ": " ^ string_of_int c ^ "\\n"',
        ),
        _replacement(
            "certificate-domain-string",
            b'sprintf "[%s], [%s]" (String.concat "; " s1) (String.concat "; " s2)',
            b'"[" ^ String.concat "; " s1 ^ "], [" ^ String.concat "; " s2 ^ "]"',
        ),
        _replacement(
            "certificate-path-string",
            b'sprintf "%s(%d)" s j',
            b's ^ "(" ^ string_of_int j ^ ")"',
        ),
    ),
    "flyspeck:formal_ineqs/verifier/m_verifier.hl": (
        _replacement(
            "verifier-variable-name",
            b'sprintf "%s%d" name i',
            b'name ^ string_of_int i',
            4,
        ),
        _replacement(
            "verifier-mono-failure",
            b'sprintf "m_mono_pass_gen: j = %d, th = %s" j (string_of_thm le_th0)',
            b'"m_mono_pass_gen: j = " ^ string_of_int j ^ ", th = " ^ '
            b'string_of_thm le_th0',
        ),
        _replacement(
            "verifier-df0-report",
            b'sprintf "df0_flags = %b" df0_flags',
            b'"df0_flags = " ^ (if df0_flags then "true" else "false")',
            3,
        ),
        _replacement(
            "verifier-mono-status",
            b'sprintf "%s%d (%b)" (if m.decr_flag then "-" else "") \n\t\t\t  m.variable m.df0_flag',
            b'(if m.decr_flag then "-" else "") ^ string_of_int m.variable ^\n'
            b'                               " (" ^ (if m.df0_flag then "true" else "false") ^ ")"',
            3,
        ),
        _replacement(
            "verifier-mono-report",
            b'sprintf "Mono: [%s]" (String.concat ";" mono_strs)',
            b'"Mono: [" ^ String.concat ";" mono_strs ^ "]"',
            3,
        ),
        _replacement(
            "verifier-pass-progress",
            b'sprintf "Verifying: %d/%d (f0_flag = %b)" !k r_size f0_flag',
            b'"Verifying: " ^ string_of_int !k ^ "/" ^ string_of_int r_size ^ '
            b'" (f0_flag = " ^ (if f0_flag then "true" else "false") ^ ")"',
            4,
        ),
        _replacement(
            "verifier-percent-progress",
            b'sprintf "%d " r',
            b'string_of_int r ^ " "',
            4,
        ),
        _replacement(
            "verifier-glue-progress",
            b'sprintf "GlueConvex: %d" (i + 1)',
            b'"GlueConvex: " ^ string_of_int (i + 1)',
            3,
        ),
        _replacement(
            "verifier-reference-progress",
            b'sprintf "Ref: %d" i',
            b'"Ref: " ^ string_of_int i',
            4,
        ),
        _replacement(
            "verifier-list-progress",
            b'sprintf "List: %d/%d" !k size',
            b'"List: " ^ string_of_int !k ^ "/" ^ string_of_int size',
            2,
        ),
    ),
    "flyspeck:formal_ineqs/verifier/m_verifier_build.hl": (
        _replacement(
            "derivative-count-progress",
            b'sprintf "Computing partial derivatives (%d)..." n',
            b'"Computing partial derivatives (" ^ string_of_int n ^ ")..."',
        ),
        _replacement(
            "derivative-index-progress",
            b'sprintf " %d" i',
            b'" " ^ string_of_int i',
        ),
        _replacement(
            "second-derivative-index-progress",
            b'sprintf " %d,%d" j i',
            b'" " ^ string_of_int j ^ "," ^ string_of_int i',
        ),
    ),
}


def normalize_source(
    source_key: str,
    source: bytes,
) -> tuple[bytes, list[dict[str, Any]]]:
    """Apply the complete bounded frontend compatibility normalization."""

    normalized, operations = normalize_nested_array_access(source)
    if source_key == "flyspeck:formal_ineqs/verifier/m_verifier_main.hl":
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
    for kind, before, after, count in (
        EXTENSION_COMPATIBILITY_REPLACEMENTS.get(source_key, ())
    ):
        if normalized.count(before) != count:
            raise ValueError(
                f"extension compatibility anchor drift: {source_key}: "
                f"{kind}: expected {count}, observed {normalized.count(before)}"
            )
        offset = normalized.index(before)
        operations.append({
            "kind": kind,
            "line": normalized.count(b"\n", 0, offset) + 1,
            "replacement_count": count,
            "before": before.decode("ascii"),
            "after": after.decode("ascii"),
        })
        normalized = normalized.replace(before, after)
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
