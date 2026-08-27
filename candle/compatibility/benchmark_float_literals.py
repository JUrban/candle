#!/usr/bin/env python3
"""Measure compiled-Candle load cost at the decimal-float trust boundary.

The historical parser support was removed because every literal performed a
runtime ``Double.fromString`` call.  This benchmark therefore times complete
``#use`` interactions, after boot, for equally sized list expressions:

* integer literals (parser/evaluator control),
* explicit ``Option.valOf (Double.fromString ...)`` calls, and
* OCaml decimal source literals.

A baseline Candle is expected to reject the source-literal scenario.  Pass
``--require-literals`` for the rebuilt acceptance run.  These measurements are
diagnostic performance evidence, not proof or IEEE-value evidence.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import tempfile
import time

import pexpect


SCENARIO_EXPRESSIONS = {
    "integer_control": "2",
    "explicit_from_string": (
        'Option.valOf (Double.fromString "2.")'),
    "source_literal": "2.",
}


def _source(scenario, terms):
    expression = SCENARIO_EXPRESSIONS[scenario]
    elements = "; ".join([expression] * terms)
    return f"let candle_float_benchmark = [{elements}];;\n"


def _sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _one_load(candle_root, source, timeout, env):
    process = pexpect.spawn(
        str(candle_root / "candle.sh"), encoding="utf-8",
        cwd=str(candle_root), env=env)
    try:
        boot = process.expect([
            r"\n# ", r"\n(ERROR: .+)", r"\n(EXCEPTION: .+)",
            pexpect.TIMEOUT, pexpect.EOF,
        ], timeout=timeout)
        if boot != 0:
            return {
                "outcome": "boot_error",
                "detail": (process.match.group(1) if boot in (1, 2)
                           else "timeout" if boot == 3 else "unexpected EOF"),
            }

        started = time.perf_counter()
        process.sendline(f'#use "{source}";;')
        terminal = process.expect([
            r"\n\- Finished loading \S+",
            r"\n(Parsing failed)",
            r"\n(ERROR: .+)",
            r"\n(EXCEPTION: .+)",
            pexpect.TIMEOUT,
            pexpect.EOF,
        ], timeout=timeout)
        elapsed = time.perf_counter() - started
        if terminal == 0:
            return {"outcome": "pass", "elapsed_seconds": elapsed}
        if terminal == 1:
            return {"outcome": "reject", "elapsed_seconds": elapsed,
                    "detail": process.match.group(1)}
        return {
            "outcome": "load_error",
            "elapsed_seconds": elapsed,
            "detail": (process.match.group(1) if terminal in (2, 3)
                       else "timeout" if terminal == 4 else "unexpected EOF"),
        }
    finally:
        process.close(force=True)


def _aggregate(runs):
    outcomes = [run["outcome"] for run in runs]
    elapsed = [run["elapsed_seconds"] for run in runs
               if "elapsed_seconds" in run]
    result = {
        "outcome": outcomes[0] if len(set(outcomes)) == 1 else "mixed",
        "runs": runs,
    }
    if elapsed:
        result.update({
            "median_seconds": statistics.median(elapsed),
            "minimum_seconds": min(elapsed),
            "maximum_seconds": max(elapsed),
        })
    return result


def benchmark(candle_root, terms, repetitions, timeout):
    launcher = candle_root / "candle.sh"
    executable = candle_root / "candle" / "build" / "cake"
    if not launcher.is_file() or not executable.is_file():
        raise FileNotFoundError(
            f"built Candle launcher/executable absent under {candle_root}")

    env = {**os.environ, "CML_HEAP_SIZE": "6000"}
    results = {}
    with tempfile.TemporaryDirectory(prefix="candle-float-benchmark-") as tmp:
        tmp_path = Path(tmp)
        for scenario in SCENARIO_EXPRESSIONS:
            source = tmp_path / f"{scenario}.ml"
            source.write_text(_source(scenario, terms), encoding="utf-8")
            runs = [
                _one_load(candle_root, source, timeout, env)
                for _ in range(repetitions)
            ]
            results[scenario] = _aggregate(runs)

    git_head = subprocess.check_output(
        ["git", "-C", str(candle_root), "rev-parse", "HEAD"],
        text=True).strip()
    return {
        "schema_version": 1,
        "benchmark": "CANDLE-OCAML-FLOAT-LITERAL-001 load-time v1",
        "measurement_scope": "post-boot #use through Finished loading",
        "terms_per_source": terms,
        "repetitions": repetitions,
        "candle_root": str(candle_root),
        "candle_git_head": git_head,
        "candle_executable_sha256": _sha256(executable),
        "scenarios": results,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candle-root", required=True, type=Path)
    parser.add_argument("--terms", type=int, default=100)
    parser.add_argument("--repetitions", type=int, default=3)
    parser.add_argument("--timeout", type=float, default=600)
    parser.add_argument("--require-literals", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.terms <= 0 or args.repetitions <= 0 or args.timeout <= 0:
        parser.error("terms, repetitions, and timeout must be positive")

    payload = benchmark(
        args.candle_root.resolve(), args.terms, args.repetitions, args.timeout)
    rendered = json.dumps(payload, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
        print(f"wrote {args.output}")
    else:
        print(rendered, end="")

    scenarios = payload["scenarios"]
    controls_pass = all(
        scenarios[name]["outcome"] == "pass"
        for name in ("integer_control", "explicit_from_string"))
    literals_accepted = scenarios["source_literal"]["outcome"] == "pass"
    if not controls_pass or (args.require_literals and not literals_accepted):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
