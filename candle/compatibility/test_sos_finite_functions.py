#!/usr/bin/env python3
"""Differential gate for SOS-style finite-function comparator adaptation."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
CASES = HERE / "sos_finite_func_cases.json"


def load_cases():
    payload = json.loads(CASES.read_text(encoding="utf-8"))
    if payload.get("schema_version") != 1:
        raise ValueError("unsupported finite-function case schema")
    if payload.get("ledger_id") != "CANDLE-HOLLIGHT-SOS-FINITE-FUNC-001":
        raise ValueError("unexpected finite-function compatibility entry")
    ids = [case["id"] for case in payload["cases"]]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate finite-function case id")
    return payload


def oracle_source(candle):
    empty_int = "undefined Int.compare" if candle else "undefined"
    empty_pair = (
        "undefined (Pair.compare Int.compare Int.compare)"
        if candle else "undefined")
    point_int = ("((1 |=> 1) Int.compare)" if candle else "(1 |=> 1)")
    point_int2 = ("((2 |=> 1) Int.compare)" if candle else "(2 |=> 1)")
    nested_cmp = (
        "(_func_compare (Pair.compare Int.compare Int.compare))"
        if candle else "")
    empty_nested = f"undefined {nested_cmp}" if candle else "undefined"
    empty_term = "undefined Term.compare" if candle else "undefined"
    term_func_cmp = (
        "(_func_compare (Pair.compare Term.compare Int.compare))"
        if candle else "")
    empty_term_outer = (
        f"undefined {term_func_cmp}" if candle else "undefined")
    int_graph = "graph candle_f4 Int.compare" if candle else "graph candle_f4"
    pair_graph = "graph candle_p2 Int.compare" if candle else "graph candle_p2"
    combine_graph = "graph candle_sum Int.compare" if candle else "graph candle_sum"

    return f'''let candle_func_check id ok =
  if ok then print_endline ("CANDLE_FUNC_CASE=" ^ id ^ "=PASS")
  else failwith ("finite function mismatch: " ^ id)
;;
let candle_f0 : (int,int) func = {empty_int};;
let candle_f1 = (3 |-> 30) candle_f0;;
let candle_f2 = (1 |-> 10) candle_f1;;
let candle_f3 = (2 |-> 20) candle_f2;;
let candle_f4 = (2 |-> 22) candle_f3;;
candle_func_check "integer_update_graph"
  ({int_graph} = [(1,10);(2,22);(3,30)] &&
   tryapplyd candle_f4 2 99 = 22 && tryapplyd candle_f4 4 99 = 99);;
let candle_p0 : ((int*int),int) func = {empty_pair};;
let candle_p1 = ((2,1) |-> 21) candle_p0;;
let candle_p2 = ((1,2) |-> 12) candle_p1;;
candle_func_check "pair_update_graph"
  ({pair_graph} = [((1,2),12);((2,1),21)] && apply candle_p2 (2,1) = 21);;
let candle_g0 : (int,int) func = {empty_int};;
let candle_g1 = (1 |-> (-10)) ((2 |-> 8) candle_g0);;
let candle_sum = combine (+) (fun x -> x = 0) candle_f4 candle_g1;;
candle_func_check "combine_zero_elision"
  ({combine_graph} = [(2,30);(3,30)]);;
let candle_m1 : (int,int) func = {point_int};;
let candle_m1_again : (int,int) func = {point_int};;
let candle_m2 : (int,int) func = {point_int2};;
let candle_outer0 : ((int,int) func,int) func = {empty_nested};;
let candle_outer = (candle_m2 |-> 22) ((candle_m1 |-> 11) candle_outer0);;
candle_func_check "nested_function_keys"
  (candle_m1 = candle_m1_again && candle_m1 <> candle_m2 &&
   apply candle_outer candle_m1 = 11 && apply candle_outer candle_m2 = 22);;
let candle_tx = mk_var("candle_x",mk_type("real",[]));;
let candle_tm0 : (term,int) func = {empty_term};;
let candle_tm = (candle_tx |-> 2) candle_tm0;;
let candle_term_outer0 : ((term,int) func,num) func = {empty_term_outer};;
let candle_term_outer = (candle_tm |-> num 7) candle_term_outer0;;
candle_func_check "term_monomial_key"
  (apply candle_term_outer candle_tm =/ num 7);;
let candle_mapped = mapf (fun x -> x + 1) candle_f4;;
candle_func_check "map_and_fold"
  (tryapplyd candle_mapped 2 0 = 23 &&
   foldl (fun a k v -> a + k + v) 0 candle_f4 = 68);;
let candle_sos_finite_function_differential_passed = true;;
'''


def expected_lines(payload):
    return {f'CANDLE_FUNC_CASE={case["id"]}=PASS'
            for case in payload["cases"]}


def check_source(candle_root):
    lib_source = (candle_root / "lib.ml").read_text(encoding="utf-8")
    sos_source = (candle_root / "Examples" / "sos.ml").read_text(
        encoding="utf-8")
    required = {
        "lib.ml": ["let _func_compare cmp", "List.compare cmp f g"],
        "Examples/sos.ml": [
            "let _inundefined : (int,num) func = undefined Int.compare",
            "let _iinundefined : (int*int,num) func =",
            "let _tiundefined : (term,int) func = undefined Term.compare",
            "let _monomial_compare m1 m2 =",
            "(graph p Num.compare)",
        ],
    }
    sources = {"lib.ml": lib_source, "Examples/sos.ml": sos_source}
    for name, snippets in required.items():
        for snippet in snippets:
            if snippet not in sources[name]:
                raise AssertionError(f"{name} omits selected adaptation: {snippet}")


def check_reference(payload, reference_root, timeout):
    ocaml = reference_root / "_opam" / "bin" / "ocaml"
    version_result = subprocess.run(
        [str(ocaml), "-version"], check=True, text=True,
        stdout=subprocess.PIPE)
    version = version_result.stdout.strip().rsplit(" ", 1)[-1]
    if version != "4.14.1":
        raise RuntimeError(f"reference must be OCaml 4.14.1, got {version}")
    with tempfile.TemporaryDirectory(prefix="candle-func-reference-") as tmp:
        source = Path(tmp) / "oracle.ml"
        source.write_text(oracle_source(False), encoding="utf-8")
        environment = os.environ.copy()
        environment["HOLLIGHT_DIR"] = str(reference_root)
        stublib_dir = reference_root / "_opam" / "lib" / "stublibs"
        old_stublibs = environment.get("CAML_LD_LIBRARY_PATH", "")
        environment["CAML_LD_LIBRARY_PATH"] = (
            str(stublib_dir) + ((":" + old_stublibs) if old_stublibs else ""))
        result = subprocess.run(
            [str(reference_root / "ocaml-hol"), "-init",
             str(reference_root / "hol.ml")],
            cwd=reference_root, check=False, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            env=environment, timeout=timeout,
            input=f'#use "{source}";;\n')
    if result.returncode != 0:
        raise AssertionError("HOL Light finite-function oracle failed:\n" +
                             result.stdout[-12000:])
    observed = {line for line in result.stdout.splitlines()
                if line.startswith("CANDLE_FUNC_CASE=")}
    if observed != expected_lines(payload):
        raise AssertionError(
            f"HOL Light oracle mismatch: expected={expected_lines(payload)!r} "
            f"observed={observed!r}\n{result.stdout[-12000:]}")
    print(f"OCaml {version} HOL Light: {len(observed)} finite-function cases PASS")


def check_candle(payload, candle_root, timeout):
    import pexpect

    transcript_file = tempfile.NamedTemporaryFile(
        mode="w+", encoding="utf-8", prefix="candle-func-", suffix=".log",
        delete=False)
    transcript_path = Path(transcript_file.name)
    process = None
    passed = False
    try:
        with tempfile.TemporaryDirectory(prefix="candle-func-source-") as tmp:
            source = Path(tmp) / "oracle.ml"
            source.write_text(oracle_source(True), encoding="utf-8")
            process = pexpect.spawn(
                str(candle_root / "candle.sh"), cwd=str(candle_root),
                encoding="utf-8", env=os.environ.copy(),
                logfile=transcript_file)
            try:
                boot = process.expect(
                    [r"\n# ", r"\n(ERROR: .+)", r"\n(EXCEPTION: .+)",
                     pexpect.TIMEOUT, pexpect.EOF], timeout=timeout)
                if boot != 0:
                    raise AssertionError("Candle boot did not reach its prompt")
                process.sendline('#use "hol.ml";;')
                hol_load = process.expect(
                    [r"\n# ", r"\n(ERROR: .+)", r"\n(Parsing failed)",
                     r"\n(EXCEPTION: .+)", pexpect.TIMEOUT, pexpect.EOF],
                    timeout=timeout)
                if hol_load != 0:
                    raise AssertionError("Candle hol.ml load failed")
                process.sendline(f'#use "{source}";;')
                result = process.expect(
                    [r"\nval candle_sos_finite_function_differential_passed = true",
                     r"\n(ERROR: .+)", r"\n(Parsing failed)",
                     r"\n(EXCEPTION: .+)", pexpect.TIMEOUT, pexpect.EOF],
                    timeout=timeout)
                if result != 0:
                    raise AssertionError("Candle finite-function source failed")
                transcript = process.before
            except Exception as error:
                transcript_file.flush()
                raise AssertionError(
                    f"Candle finite-function oracle failed: {error}\n"
                    f"transcript: {transcript_path}") from error
            finally:
                if process is not None:
                    process.close(force=True)
        passed = True
    finally:
        transcript_file.close()
        if passed:
            transcript_path.unlink()
    for line in expected_lines(payload):
        if line not in transcript:
            raise AssertionError(f"Candle finite-function oracle omitted {line}")
    print(f"Candle: {len(expected_lines(payload))} finite-function cases PASS")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference-root", type=Path)
    parser.add_argument("--candle-root", type=Path)
    parser.add_argument("--timeout", type=int, default=900)
    args = parser.parse_args()
    payload = load_cases()
    if args.reference_root is None:
        print("OCaml HOL Light: NOT RUN (pass --reference-root)")
    else:
        check_reference(payload, args.reference_root.resolve(), args.timeout)
    if args.candle_root is None:
        print("Candle: NOT RUN (pass --candle-root)")
    else:
        candle_root = args.candle_root.resolve()
        check_source(candle_root)
        check_candle(payload, candle_root, args.timeout)


if __name__ == "__main__":
    main()
