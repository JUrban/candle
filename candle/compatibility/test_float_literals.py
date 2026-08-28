#!/usr/bin/env python3
"""Differential oracle for CANDLE-OCAML-FLOAT-LITERAL-001.

The default reference-only mode pins parsing and IEEE-754 values under OCaml
4.14.1. Once a Candle executable containing the CakeML parser change exists,
``--candle-root`` checks the same values and rejection cases in one fresh
Candle session. The optional check is deliberately not an automatic skip: a
reported pass always says whether only OCaml or both implementations ran.
"""

import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
CASES_PATH = HERE / "float_literal_cases.json"
EXPECTED_OCAML_VERSION = "4.14.1"


def _load_cases():
    payload = json.loads(CASES_PATH.read_text(encoding="utf-8"))
    if payload.get("schema_version") != 1:
        raise ValueError(f"unsupported float case schema: {CASES_PATH}")
    if payload.get("ledger_id") != "CANDLE-OCAML-FLOAT-LITERAL-001":
        raise ValueError(f"unexpected compatibility entry: {CASES_PATH}")
    return payload


def _run(command, **kwargs):
    return subprocess.run(command, check=False, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          **kwargs)


def check_ocaml(payload, ocamlc):
    version = _run([ocamlc, "-version"])
    if version.returncode != 0:
        raise RuntimeError(f"cannot run {ocamlc}: {version.stderr.strip()}")
    actual_version = version.stdout.strip()
    if actual_version != EXPECTED_OCAML_VERSION:
        raise RuntimeError(
            f"reference must be OCaml {EXPECTED_OCAML_VERSION}, got "
            f"{actual_version}")

    with tempfile.TemporaryDirectory(prefix="candle-float-ocaml-") as tmp:
        tmp_path = Path(tmp)
        positive_source = tmp_path / "positive.ml"
        positive_program = [
            "let print_bits id value =",
            "  Printf.printf \"%s=%Lu\\n\" id (Int64.bits_of_float value)",
            ";;",
        ]
        for case in payload["positive_cases"]:
            positive_program.append(
                f'print_bits "{case["id"]}" ({case["literal"]});;')
        positive_source.write_text("\n".join(positive_program) + "\n",
                                   encoding="utf-8")
        executable = tmp_path / "positive"
        compiled = _run([ocamlc, "-o", str(executable),
                         str(positive_source)])
        if compiled.returncode != 0:
            raise AssertionError(
                "OCaml rejected a positive float case:\n" + compiled.stderr)
        observed = _run([str(executable)])
        if observed.returncode != 0:
            raise AssertionError(
                "OCaml float oracle did not run:\n" + observed.stderr)
        actual_bits = dict(line.split("=", 1)
                           for line in observed.stdout.splitlines())
        expected_bits = {
            case["id"]: case["expected_word64_decimal"]
            for case in payload["positive_cases"]
        }
        if actual_bits != expected_bits:
            raise AssertionError(
                f"OCaml float bits differ:\nexpected={expected_bits}\n"
                f"actual={actual_bits}")

        for case in payload["negative_cases"]:
            negative_source = tmp_path / f'negative-{case["id"]}.ml'
            negative_source.write_text(
                f'let candle_invalid_float = {case["literal"]};;\n',
                encoding="utf-8")
            parsed = _run([ocamlc, "-stop-after", "parsing", "-c",
                           str(negative_source)])
            if parsed.returncode == 0:
                raise AssertionError(
                    f'OCaml accepted negative case {case["id"]}: '
                    f'{case["literal"]}')

    print(f"OCaml {actual_version}: "
          f'{len(payload["positive_cases"])} positive values and '
          f'{len(payload["negative_cases"])} negative parses PASS')


def _candle_positive_source(payload):
    lines = []
    for case in payload["positive_cases"]:
        binding = f'candle_float_{case["id"]}'
        expected = case["expected_word64_decimal"]
        lines.extend([
            f'let {binding} = {case["literal"]};;',
            (f'let () = if Cake.Word64.toInt (Cake.Double.toWord {binding}) '
             f'= {expected} then () else failwith '
             f'"float bits: {case["id"]}";;'),
        ])
    lines.append("let candle_float_differential_passed = true;;")
    return "\n".join(lines) + "\n"


def _expect_prompt(process, timeout):
    import pexpect

    index = process.expect([
        r"\n# ",
        r"\n(ERROR: .+)",
        r"\n(EXCEPTION: .+)",
        pexpect.TIMEOUT,
        pexpect.EOF,
    ], timeout=timeout)
    if index != 0:
        detail = (process.match.group(1) if index in (1, 2)
                  else "timeout" if index == 3 else "unexpected EOF")
        raise AssertionError(f"Candle did not reach its prompt: {detail}")


def check_candle(payload, candle_root, timeout):
    try:
        import pexpect
    except ImportError as error:
        raise RuntimeError("Candle differential mode requires pexpect") from error

    root = candle_root.resolve()
    launcher = root / "candle.sh"
    if not launcher.is_file():
        raise RuntimeError(f"Candle launcher not found: {launcher}")

    transcript = tempfile.NamedTemporaryFile(
        mode="w+", encoding="utf-8", prefix="candle-float-", suffix=".log",
        delete=False)
    transcript_path = Path(transcript.name)
    process = None
    passed = False
    try:
        process = pexpect.spawn(
            str(launcher), encoding="utf-8", logfile=transcript,
            cwd=str(root), env=os.environ.copy())
        _expect_prompt(process, timeout)
        process.sendline('#use "candle/build/insulate.ml";;')
        _expect_prompt(process, timeout)
        with tempfile.TemporaryDirectory(prefix="candle-float-source-") as tmp:
            source = Path(tmp) / "positive.ml"
            source.write_text(_candle_positive_source(payload),
                              encoding="utf-8")
            process.sendline(f'#use "{source}";;')
            index = process.expect([
                r"\nval candle_float_differential_passed = true",
                r"\n(ERROR: .+)",
                r"\n(Parsing failed)",
                r"\n(EXCEPTION: .+)",
                pexpect.TIMEOUT,
                pexpect.EOF,
            ], timeout=timeout)
            if index != 0:
                detail = (process.match.group(1) if index in (1, 2, 3)
                          else "timeout" if index == 4 else "unexpected EOF")
                raise AssertionError(
                    f"Candle positive float differential failed: {detail}")
            _expect_prompt(process, timeout)

            for case in payload["negative_cases"]:
                process.sendline(
                    f'let candle_invalid_float = {case["literal"]};;')
                index = process.expect([
                    r"\nParsing failed",
                    r"\nval candle_invalid_float =",
                    r"\n(ERROR: .+)",
                    r"\n(EXCEPTION: .+)",
                    pexpect.TIMEOUT,
                    pexpect.EOF,
                ], timeout=timeout)
                if index != 0:
                    detail = ("accepted" if index == 1 else
                              process.match.group(1) if index in (2, 3) else
                              "timeout" if index == 4 else "unexpected EOF")
                    raise AssertionError(
                        f'Candle negative case {case["id"]} did not produce '
                        f'a parse failure: {detail}')
                _expect_prompt(process, timeout)
        passed = True
    except Exception as error:
        transcript.flush()
        raise AssertionError(
            f"{error}\nCandle transcript: {transcript_path}") from error
    finally:
        if process is not None:
            process.close(force=True)
        transcript.close()
        if passed:
            transcript_path.unlink()

    print(f"Candle: {len(payload['positive_cases'])} positive values and "
          f"{len(payload['negative_cases'])} negative parses PASS")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ocamlc", default="ocamlc")
    parser.add_argument(
        "--candle-root", type=Path,
        help="also test a built Candle tree containing candle.sh")
    parser.add_argument(
        "--timeout", type=int, default=600,
        help="seconds allowed for each Candle boot/load interaction")
    args = parser.parse_args()

    payload = _load_cases()
    check_ocaml(payload, args.ocamlc)
    if args.candle_root is None:
        print("Candle: NOT RUN (pass --candle-root after rebuilding the parser)")
    else:
        check_candle(payload, args.candle_root, args.timeout)


if __name__ == "__main__":
    main()
