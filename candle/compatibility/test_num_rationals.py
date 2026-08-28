#!/usr/bin/env python3
"""Differential oracle for Candle's selected HOL Light Num operations."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
CASES = HERE / "num_rational_cases.json"


def load_cases():
    payload = json.loads(CASES.read_text(encoding="utf-8"))
    if payload.get("schema_version") != 1:
        raise ValueError("unsupported Num case schema")
    if payload.get("ledger_id") != "CANDLE-OCAML-NUM-ROUNDING-001":
        raise ValueError("unexpected Num compatibility entry")
    ids = [case["id"] for key in ("cases", "exception_cases", "excluded_cases")
           for case in payload[key]]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate Num case id")
    return payload


def oracle_source(payload):
    lines = [
        "let candle_num_check id expected actual =",
        "  if Num.string_of_num actual = expected then",
        "    print_endline (\"CANDLE_NUM_CASE=\" ^ id ^ \"=\" ^ expected)",
        "  else failwith (\"Num mismatch: \" ^ id)",
        ";;",
    ]
    for case in payload["cases"]:
        lines.append(
            f'candle_num_check "{case["id"]}" "{case["expected"]}" '
            f'({case["expression"]});;')
    for case in payload["exception_cases"]:
        lines.append(
            f'if (try ignore ({case["expression"]}); false '
            f'with Failure _ -> true) then '
            f'print_endline "CANDLE_NUM_EXCEPTION={case["id"]}=Failure" '
            f'else failwith "missing Num exception: {case["id"]}";;')
    lines.append("let candle_num_rational_differential_passed = true;;")
    return "\n".join(lines) + "\n"


def expected_lines(payload):
    return {
        *(f'CANDLE_NUM_CASE={case["id"]}={case["expected"]}'
          for case in payload["cases"]),
        *(f'CANDLE_NUM_EXCEPTION={case["id"]}={case["exception"]}'
          for case in payload["exception_cases"]),
    }


def check_reference(payload, ocaml, zarith_dir, stublib_dir):
    version_output = subprocess.run(
        [ocaml, "-version"], check=True, text=True,
        stdout=subprocess.PIPE).stdout.strip()
    version = version_output.rsplit(" ", 1)[-1]
    if version != "4.14.1":
        raise RuntimeError(f"reference must be OCaml 4.14.1, got {version}")
    with tempfile.TemporaryDirectory(prefix="candle-num-reference-") as tmp:
        source = Path(tmp) / "oracle.ml"
        source.write_text(
            f'#use "{ROOT / "bignum_zarith.ml"}";;\n' +
            oracle_source(payload), encoding="utf-8")
        command = [ocaml, "-I", str(zarith_dir), "zarith.cma", str(source)]
        reference_env = os.environ.copy()
        if stublib_dir.is_dir():
            old_stublibs = reference_env.get("CAML_LD_LIBRARY_PATH", "")
            reference_env["CAML_LD_LIBRARY_PATH"] = (
                str(stublib_dir) + ((":" + old_stublibs) if old_stublibs else ""))
        result = subprocess.run(
            command, cwd=ROOT, check=False, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=reference_env)
    if result.returncode != 0:
        raise AssertionError("OCaml Num oracle failed:\n" + result.stderr)
    observed = {line for line in result.stdout.splitlines()
                if line.startswith("CANDLE_NUM_")}
    if observed != expected_lines(payload):
        raise AssertionError(
            f"OCaml Num oracle mismatch: expected={expected_lines(payload)!r} "
            f"observed={observed!r}")
    print(f"OCaml {version}: {len(observed)} Num cases PASS")


def check_candle(payload, candle_root, timeout):
    import pexpect

    root = candle_root.resolve()
    transcript_file = tempfile.NamedTemporaryFile(
        mode="w+", encoding="utf-8", prefix="candle-num-", suffix=".log",
        delete=False)
    transcript_path = Path(transcript_file.name)
    passed = False
    process = None
    try:
        with tempfile.TemporaryDirectory(prefix="candle-num-source-") as tmp:
            source = Path(tmp) / "oracle.ml"
            source.write_text(oracle_source(payload), encoding="utf-8")
            process = pexpect.spawn(
                str(root / "candle.sh"), cwd=str(root), encoding="utf-8",
                env=os.environ.copy(), logfile=transcript_file)
            try:
                boot = process.expect([
                    r"\n# ", r"\n(ERROR: .+)", r"\n(EXCEPTION: .+)",
                    pexpect.TIMEOUT, pexpect.EOF], timeout=timeout)
                if boot != 0:
                    detail = (process.match.group(1) if boot in (1, 2) else
                              "timeout" if boot == 3 else "unexpected EOF")
                    raise AssertionError(f"Candle boot failed: {detail}")
                process.send('#use "hol.ml";;\n'
                             'let candle_hol_load_complete = '
                             '(check_axioms (); true);;\n')
                hol_load = process.expect([
                    r"\n- Finished loading (?:\S*/)?hol\.ml",
                    r"\n(ERROR: .+)", r"\n(Parsing failed)",
                    r"\n(EXCEPTION: .+)", pexpect.TIMEOUT, pexpect.EOF],
                    timeout=timeout)
                if hol_load != 0:
                    detail = (process.match.group(1)
                              if hol_load in (1, 2, 3) else
                              "timeout" if hol_load == 4 else "unexpected EOF")
                    raise AssertionError(
                        f"Candle hol.ml EOF witness failed: {detail}")
                hol_marker = process.expect([
                    r"\nval candle_hol_load_complete = true",
                    r"\n(ERROR: .+)", r"\n(Parsing failed)",
                    r"\n(EXCEPTION: .+)", pexpect.TIMEOUT, pexpect.EOF],
                    timeout=timeout)
                if hol_marker != 0:
                    detail = (process.match.group(1)
                              if hol_marker in (1, 2, 3) else
                              "timeout" if hol_marker == 4 else
                              "unexpected EOF")
                    raise AssertionError(
                        f"Candle hol.ml completion marker failed: {detail}")
                prompt = process.expect([
                    r"\n# ", r"\n(ERROR: .+)", r"\n(EXCEPTION: .+)",
                    pexpect.TIMEOUT, pexpect.EOF], timeout=timeout)
                if prompt != 0:
                    detail = (process.match.group(1)
                              if prompt in (1, 2) else
                              "timeout" if prompt == 3 else
                              "unexpected EOF")
                    raise AssertionError(
                        f"Candle prompt after hol.ml failed: {detail}")
                process.sendline(f'#use "{source}";;')
                result = process.expect([
                    r"\nval candle_num_rational_differential_passed = true",
                    r"\n(ERROR: .+)", r"\n(Parsing failed)",
                    r"\n(EXCEPTION: .+)", pexpect.TIMEOUT, pexpect.EOF],
                    timeout=timeout)
                if result != 0:
                    detail = (process.match.group(1) if result in (1, 2, 3) else
                              "timeout" if result == 4 else "unexpected EOF")
                    raise AssertionError(f"Candle Num source failed: {detail}")
                transcript = process.before
            except Exception as error:
                transcript_file.flush()
                raise AssertionError(
                    f"Candle Num oracle failed: {error}\n"
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
            raise AssertionError(f"Candle Num oracle omitted {line}")
    print(f"Candle: {len(expected_lines(payload))} Num cases PASS")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ocaml", default="ocaml")
    parser.add_argument("--zarith-dir", type=Path, default=Path("+zarith"))
    parser.add_argument("--stublib-dir", type=Path)
    parser.add_argument("--candle-root", type=Path)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    payload = load_cases()
    stublib_dir = (args.stublib_dir if args.stublib_dir is not None else
                   args.zarith_dir.parent / "stublibs")
    check_reference(payload, args.ocaml, args.zarith_dir, stublib_dir)
    if args.candle_root is None:
        print("Candle: NOT RUN (pass --candle-root for the differential gate)")
    else:
        check_candle(payload, args.candle_root, args.timeout)


if __name__ == "__main__":
    main()
