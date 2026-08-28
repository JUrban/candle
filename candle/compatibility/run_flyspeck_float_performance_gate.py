#!/usr/bin/env python3
"""Run provenance-bound, performance-only Flyspeck float workloads.

Each measurement uses a fresh authenticated ``candle.sh`` process, loads
``hol.ml`` through its exact EOF marker, and requires ``check_axioms ()``
before the measured source.  Wall time is measured only around the measured
``#use``.  RSS is sampled only during that interval, but is total resident
memory and therefore includes the retained full-HOL state.

This gate supplies parser/runtime performance observations.  It is not a
theorem fingerprint gate and never establishes S2 or S3.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
import threading
import time
from types import ModuleType
from typing import Any

import pexpect

import generate_flyspeck_float_performance as inputs


CLAIM = "performance observation only; not semantic, S2, or S3 evidence"


class GateError(RuntimeError):
    """The performance workload or one of its provenance checks failed."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise GateError(message)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while block := source.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def _load_provenance_module(candle_root: Path) -> ModuleType:
    path = candle_root / "candle/cakeml_artifact_provenance.py"
    require(path.is_file() and not path.is_symlink(),
            f"missing ordinary artifact provenance checker: {path}")
    spec = importlib.util.spec_from_file_location(
        "_candle_float_performance_provenance", path,
    )
    require(spec is not None and spec.loader is not None,
            "could not load artifact provenance checker")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class ProcessTreeSampler:
    """Sample Linux RSS for one process and its descendants."""

    def __init__(self, root_pid: int, interval: float = 0.05):
        self.root_pid = root_pid
        self.interval = interval
        self.peak_process_rss_kib = 0
        self.peak_tree_rss_kib = 0
        self._stop = threading.Event()
        self._thread = threading.Thread(target=self._run, daemon=True)

    @staticmethod
    def _snapshot() -> tuple[dict[int, int], dict[int, int]]:
        parents: dict[int, int] = {}
        rss: dict[int, int] = {}
        page_kib = os.sysconf("SC_PAGE_SIZE") // 1024
        for entry in Path("/proc").iterdir():
            if not entry.name.isdigit():
                continue
            try:
                pid = int(entry.name)
                stat = (entry / "stat").read_text(encoding="utf-8")
                fields = stat[stat.rfind(")") + 2:].split()
                parents[pid] = int(fields[1])
                statm = (entry / "statm").read_text(
                    encoding="utf-8",
                ).split()
                rss[pid] = int(statm[1]) * page_kib
            except (FileNotFoundError, ProcessLookupError, PermissionError,
                    ValueError, IndexError):
                continue
        return parents, rss

    @classmethod
    def tree_rss(cls, root_pid: int) -> tuple[int, int]:
        parents, rss = cls._snapshot()
        tree = {root_pid}
        changed = True
        while changed:
            changed = False
            for pid, parent in parents.items():
                if parent in tree and pid not in tree:
                    tree.add(pid)
                    changed = True
        values = [rss[pid] for pid in tree if pid in rss]
        if not values:
            return 0, 0
        return max(values), sum(values)

    def _sample(self) -> None:
        process_rss, tree_rss = self.tree_rss(self.root_pid)
        self.peak_process_rss_kib = max(
            self.peak_process_rss_kib, process_rss,
        )
        self.peak_tree_rss_kib = max(self.peak_tree_rss_kib, tree_rss)

    def _run(self) -> None:
        self._sample()
        while not self._stop.wait(self.interval):
            self._sample()

    def start(self) -> None:
        self._thread.start()

    def stop(self) -> None:
        self._stop.set()
        self._thread.join()
        self._sample()


class CandleSession:
    """A fresh authenticated Candle process with fail-closed load matching."""

    def __init__(
        self,
        candle_root: Path,
        environment: dict[str, str],
        transcript_path: Path,
        inactivity_timeout: float,
    ):
        self.root = candle_root
        self.inactivity_timeout = inactivity_timeout
        self.transcript = transcript_path.open("w", encoding="utf-8")
        self.process = None
        try:
            self.process = pexpect.spawn(
                str(candle_root / "candle.sh"), cwd=str(candle_root),
                encoding="utf-8", logfile=self.transcript, env=environment,
            )
            self._expect_prompt(600.0, "initial Candle boot")
        except Exception:
            if self.process is not None:
                self.process.close(force=True)
            self.transcript.close()
            raise

    def close(self) -> None:
        self.process.close(force=True)
        self.transcript.close()

    def _expect_until(
        self,
        success_pattern: str,
        wall_timeout: float,
        label: str,
    ) -> None:
        deadline = time.monotonic() + wall_timeout
        while True:
            remaining = deadline - time.monotonic()
            require(remaining > 0, f"{label}: wall timeout")
            timeout = min(self.inactivity_timeout, remaining)
            index = self.process.expect([
                success_pattern,
                r"(?:^|\n)(ERROR: .+)",
                r"(?:^|\n)(Parsing failed)",
                r"(?:^|\n)(EXCEPTION: .+)",
                r"(?:^|\n)[^\n]*\n",
                pexpect.TIMEOUT,
                pexpect.EOF,
            ], timeout=timeout)
            if index == 0:
                return
            if index in (1, 2, 3):
                raise GateError(f"{label}: {self.process.match.group(1)}")
            if index == 4:
                continue
            if index == 5:
                raise GateError(f"{label}: inactivity timeout")
            raise GateError(f"{label}: unexpected process EOF")

    def _expect_prompt(self, wall_timeout: float, label: str) -> None:
        self._expect_until(r"(?:^|\n)# ", wall_timeout, label)

    @staticmethod
    def _finished_pattern(path: Path) -> str:
        return (r"(?:^|\n)- Finished loading (?:\S*/)?" +
                re.escape(path.name) + r"(?:\r)?\n")

    def load(
        self,
        path: Path,
        wall_timeout: float,
        marker: str | None = None,
    ) -> float:
        require(path.is_file(), f"missing load source: {path}")
        self.process.sendline(f"#use {json.dumps(str(path))};;")
        started = time.perf_counter()
        marker_seen = marker is None
        finished = False
        deadline = time.monotonic() + wall_timeout
        marker_pattern = (r"(?:^|\n)val " + re.escape(marker) +
                          r" = true(?:: bool)?(?:\r)?\n"
                          if marker else r"(?!)")
        finished_pattern = self._finished_pattern(path)
        while not finished:
            remaining = deadline - time.monotonic()
            require(remaining > 0, f"loading {path.name}: wall timeout")
            timeout = min(self.inactivity_timeout, remaining)
            index = self.process.expect([
                marker_pattern,
                finished_pattern,
                r"(?:^|\n)(ERROR: .+)",
                r"(?:^|\n)(Parsing failed)",
                r"(?:^|\n)(EXCEPTION: .+)",
                r"(?:^|\n)[^\n]*\n",
                pexpect.TIMEOUT,
                pexpect.EOF,
            ], timeout=timeout)
            if index == 0:
                marker_seen = True
            elif index == 1:
                finished = True
            elif index in (2, 3, 4):
                raise GateError(
                    f"loading {path.name}: {self.process.match.group(1)}")
            elif index == 5:
                continue
            elif index == 6:
                raise GateError(f"loading {path.name}: inactivity timeout")
            else:
                raise GateError(f"loading {path.name}: unexpected process EOF")
        elapsed = time.perf_counter() - started
        require(marker_seen, f"loading {path.name}: success marker missing")
        self._expect_prompt(
            min(wall_timeout, 300.0), f"prompt after loading {path.name}",
        )
        return elapsed

    def evaluate_true(
        self,
        source: str,
        binding: str,
        wall_timeout: float = 300.0,
    ) -> None:
        self.process.sendline(source)
        pattern = (r"(?:^|\n)val " + re.escape(binding) +
                   r" = true(?:: bool)?(?:\r)?\n")
        self._expect_until(pattern, wall_timeout, f"evaluating {binding}")
        self._expect_prompt(wall_timeout, f"prompt after {binding}")

    def full_hol_preflight(self, wall_timeout: float) -> float:
        elapsed = self.load(self.root / "hol.ml", wall_timeout)
        self.evaluate_true(
            "let candle_float_performance_hol_preflight = "
            "(check_axioms (); true);;",
            "candle_float_performance_hol_preflight",
            wall_timeout=min(wall_timeout, 600.0),
        )
        return elapsed

    def axioms_postflight(self, wall_timeout: float) -> None:
        self.evaluate_true(
            "let candle_float_performance_axioms_postflight = "
            "(check_axioms (); true);;",
            "candle_float_performance_axioms_postflight",
            wall_timeout=min(wall_timeout, 600.0),
        )


def _measure_load(
    session: CandleSession,
    path: Path,
    wall_timeout: float,
    marker: str | None = None,
) -> dict[str, Any]:
    before_process, before_tree = ProcessTreeSampler.tree_rss(
        session.process.pid,
    )
    sampler = ProcessTreeSampler(session.process.pid)
    sampler.start()
    try:
        elapsed = session.load(path, wall_timeout, marker=marker)
    finally:
        sampler.stop()
    after_process, after_tree = ProcessTreeSampler.tree_rss(
        session.process.pid,
    )
    return {
        "elapsed_seconds": elapsed,
        "rss_scope": (
            "total process/tree RSS sampled from immediately before measured "
            "#use through source EOF and prompt; includes full-HOL baseline"
        ),
        "rss_before_process_kib": before_process,
        "rss_before_tree_kib": before_tree,
        "peak_process_rss_kib": sampler.peak_process_rss_kib,
        "peak_tree_rss_kib": sampler.peak_tree_rss_kib,
        "rss_after_process_kib": after_process,
        "rss_after_tree_kib": after_tree,
    }


def _run_one(
    name: str,
    candle_root: Path,
    flyspeck_root: Path,
    generated_dir: Path,
    log_dir: Path,
    environment: dict[str, str],
    inactivity_timeout: float,
    hol_wall_timeout: float,
    scenario_wall_timeout: float,
) -> dict[str, Any]:
    transcript_path = log_dir / f"{name}.log"
    session = CandleSession(
        candle_root, environment, transcript_path, inactivity_timeout,
    )
    try:
        hol_elapsed = session.full_hol_preflight(hol_wall_timeout)
        if name == "break_case_log":
            type_path = flyspeck_root / "text_formalization/nonlinear/break_case_type.hl"
            setup_elapsed = session.load(type_path, scenario_wall_timeout)
            measured = _measure_load(
                session,
                flyspeck_root / inputs.SOURCE_PATH,
                scenario_wall_timeout,
            )
            session.evaluate_true(
                "let candle_float_performance_break_case_count_ok = "
                "List.length (!Break_case_log.break_data) = 463;;",
                "candle_float_performance_break_case_count_ok",
            )
            measured["setup_seconds"] = setup_elapsed
            measured["measurement_scope"] = (
                "post-full-HOL exact pinned break_case_log #use through EOF"
            )
        else:
            source = generated_dir / f"candle_float_{name}_loop.ml"
            marker = f"candle_float_perf_{name}_passed"
            measured = _measure_load(
                session, source, scenario_wall_timeout, marker=marker,
            )
            measured["measurement_scope"] = (
                f"post-full-HOL generated {name} loop #use through EOF"
            )
        session.axioms_postflight(scenario_wall_timeout)
        measured.update({
            "outcome": "pass",
            "hol_preflight_elapsed_seconds": hol_elapsed,
            "hol_eof_witness": True,
            "check_axioms_preflight": True,
            "check_axioms_postflight": True,
        })
    finally:
        session.close()
    measured["transcript"] = {
        "path": str(transcript_path),
        "bytes": transcript_path.stat().st_size,
        "sha256": sha256_file(transcript_path),
    }
    return measured


def threshold_failures(
    scenarios: dict[str, dict[str, Any]],
    max_break_case_seconds: float | None,
    max_call_time_seconds: float | None,
    max_call_to_hoisted_ratio: float | None,
) -> list[str]:
    failures = []
    break_elapsed = scenarios["break_case_log"]["elapsed_seconds"]
    call_elapsed = scenarios["call_time"]["elapsed_seconds"]
    hoisted_elapsed = scenarios["hoisted"]["elapsed_seconds"]
    if (max_break_case_seconds is not None and
            break_elapsed > max_break_case_seconds):
        failures.append("break_case_log elapsed threshold exceeded")
    if (max_call_time_seconds is not None and
            call_elapsed > max_call_time_seconds):
        failures.append("call_time elapsed threshold exceeded")
    if max_call_to_hoisted_ratio is not None:
        require(hoisted_elapsed > 0, "hoisted elapsed time is not positive")
        if call_elapsed / hoisted_elapsed > max_call_to_hoisted_ratio:
            failures.append("call_time/hoisted ratio threshold exceeded")
    return failures


def _create_evidence_layout(
    evidence_dir: Path,
    candle_root: Path,
    flyspeck_root: Path,
) -> tuple[Path, Path, Path]:
    require(not evidence_dir.is_relative_to(candle_root),
            "evidence directory cannot be inside the Candle source tree")
    require(not evidence_dir.is_relative_to(flyspeck_root),
            "evidence directory cannot be inside the Flyspeck source tree")
    require(not evidence_dir.exists(),
            f"refusing to overwrite evidence directory: {evidence_dir}")
    evidence_dir.mkdir(parents=True)
    generated_dir = evidence_dir / "generated"
    transcript_dir = evidence_dir / "transcripts"
    transcript_dir.mkdir()
    return generated_dir, transcript_dir, evidence_dir / "report.json"


def _write_json(path: Path, value: dict[str, Any]) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8",
    )


def _verify_generated_inputs(
    generated_dir: Path,
    receipt: dict[str, Any],
) -> None:
    persisted_path = generated_dir / "flyspeck_float_performance_inputs.json"
    require(json.loads(persisted_path.read_text(encoding="utf-8")) == receipt,
            "generated input receipt changed during the run")
    for name, expected in receipt["outputs"].items():
        require(inputs.file_record(generated_dir / name) == expected,
                f"generated performance input changed during the run: {name}")


def run(arguments: argparse.Namespace) -> dict[str, Any]:
    candle_root = arguments.candle_root.resolve()
    flyspeck_root = arguments.flyspeck_root.resolve()
    evidence_dir = arguments.evidence_dir.resolve()

    provenance = _load_provenance_module(candle_root)
    try:
        linked = provenance.validate_linked_record(candle_root)
        runtime_environment = provenance.runtime_environment({
            "CML_HEAP_SIZE": str(arguments.heap_mb),
        })
    except Exception as error:  # provenance package owns its exception type
        raise GateError(f"linked Candle provenance failed: {error}") from error
    launcher = candle_root / "candle.sh"
    require(launcher.is_file() and os.access(launcher, os.X_OK),
            f"authenticated Candle launcher is unavailable: {launcher}")
    generated_dir, transcript_dir, output_path = _create_evidence_layout(
        evidence_dir, candle_root, flyspeck_root,
    )
    linked_record_path = (
        candle_root / "candle/build/cakeml-build-provenance.json"
    )
    linked_archive_path = evidence_dir / "linked-provenance.json"
    linked_archive_path.write_bytes(linked_record_path.read_bytes())
    config_path = evidence_dir / "gate-config.json"
    config = {
        "schema": 1,
        "kind": "flyspeck-float-performance-gate-config",
        "claim": CLAIM,
        "candle_root": str(candle_root),
        "flyspeck_root": str(flyspeck_root),
        "evidence_dir": str(evidence_dir),
        "iterations": arguments.iterations,
        "heap_mb": arguments.heap_mb,
        "inactivity_timeout_seconds": arguments.inactivity_timeout,
        "hol_wall_timeout_seconds": arguments.hol_wall_timeout,
        "scenario_wall_timeout_seconds": arguments.scenario_wall_timeout,
        "thresholds": {
            "max_break_case_seconds": arguments.max_break_case_seconds,
            "max_call_time_seconds": arguments.max_call_time_seconds,
            "max_call_to_hoisted_ratio":
                arguments.max_call_to_hoisted_ratio,
        },
        "runtime_environment": runtime_environment,
        "linked_provenance_source": str(linked_record_path),
        "linked_provenance_sha256": sha256_file(linked_record_path),
    }
    _write_json(config_path, config)
    receipt = inputs.materialize(
        candle_root, flyspeck_root, generated_dir, arguments.iterations,
    )
    require(receipt["manifest"]["sha256"] == linked["manifest_sha256"],
            "generated input manifest differs from linked provenance")
    scenarios = {
        name: _run_one(
            name, candle_root, flyspeck_root, generated_dir, transcript_dir,
            runtime_environment, arguments.inactivity_timeout,
            arguments.hol_wall_timeout, arguments.scenario_wall_timeout,
        )
        for name in ("call_time", "hoisted", "break_case_log")
    }

    try:
        linked_postflight = provenance.validate_linked_record(candle_root)
    except Exception as error:  # provenance package owns its exception type
        raise GateError(
            f"linked Candle provenance postflight failed: {error}"
        ) from error
    require(linked_postflight == linked,
            "linked Candle provenance record changed during the run")
    require(linked_archive_path.read_bytes() == linked_record_path.read_bytes(),
            "archived linked provenance differs at postflight")
    validated_postflight = inputs.validate_inputs(candle_root, flyspeck_root)
    validated_postflight.pop("source_text")
    require(validated_postflight == {
        "manifest": receipt["manifest"],
        "flyspeck": receipt["flyspeck"],
    }, "Flyspeck source or manifest changed during the run")
    _verify_generated_inputs(generated_dir, receipt)

    ratio = (scenarios["call_time"]["elapsed_seconds"] /
             scenarios["hoisted"]["elapsed_seconds"])
    failures = threshold_failures(
        scenarios, arguments.max_break_case_seconds,
        arguments.max_call_time_seconds, arguments.max_call_to_hoisted_ratio,
    )
    report = {
        "schema": 1,
        "kind": "flyspeck-float-performance-gate",
        "claim": CLAIM,
        "outcome": "fail" if failures else "pass",
        "candle": {
            "root": str(candle_root),
            "commit": linked["candle_commit"],
            "cakeml_commit": linked["cakeml_commit"],
            "hol4_commit": linked["hol4_commit"],
            "manifest_sha256": linked["manifest_sha256"],
            "launcher_sha256": sha256_file(launcher),
            "executable_sha256": linked["outputs"]["cake"]["sha256"],
            "linked_provenance_sha256": sha256_file(
                linked_record_path),
        },
        "inputs": receipt,
        "scenarios": scenarios,
        "evidence": {
            "directory": str(evidence_dir),
            "gate_config": {
                "path": str(config_path),
                **inputs.file_record(config_path),
            },
            "linked_provenance_archive": {
                "path": str(linked_archive_path),
                **inputs.file_record(linked_archive_path),
            },
            "generated_input_receipt": {
                "path": str(
                    generated_dir / "flyspeck_float_performance_inputs.json"
                ),
                **inputs.file_record(
                    generated_dir / "flyspeck_float_performance_inputs.json"
                ),
            },
            "transcript_directory": str(transcript_dir),
        },
        "postflight": {
            "all_session_check_axioms": True,
            "check_linked_postflight": True,
            "linked_provenance_revalidated": True,
            "linked_provenance_unchanged": True,
            "flyspeck_manifest_source_revalidated": True,
            "generated_inputs_rehashed": True,
        },
        "comparison": {
            "call_time_minus_hoisted_seconds": (
                scenarios["call_time"]["elapsed_seconds"] -
                scenarios["hoisted"]["elapsed_seconds"]),
            "call_time_to_hoisted_elapsed_ratio": ratio,
            "interpretation_limit": (
                "external wall comparison of fresh full-HOL processes; no "
                "claim about optimizer conversion count"
            ),
        },
        "thresholds": {
            "max_break_case_seconds": arguments.max_break_case_seconds,
            "max_call_time_seconds": arguments.max_call_time_seconds,
            "max_call_to_hoisted_ratio": arguments.max_call_to_hoisted_ratio,
            "failures": failures,
        },
    }
    _write_json(output_path, report)
    if failures:
        raise GateError("; ".join(failures) + f"; report: {output_path}")
    return report


def _positive_float(value: str) -> float:
    parsed = float(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be positive")
    return parsed


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candle-root", type=Path, required=True)
    parser.add_argument("--flyspeck-root", type=Path, required=True)
    parser.add_argument("--evidence-dir", type=Path, required=True)
    parser.add_argument("--iterations", type=int, default=inputs.DEFAULT_ITERATIONS)
    parser.add_argument("--heap-mb", type=int, default=6000)
    parser.add_argument("--inactivity-timeout", type=_positive_float, default=300.0)
    parser.add_argument("--hol-wall-timeout", type=_positive_float, default=3600.0)
    parser.add_argument(
        "--scenario-wall-timeout", type=_positive_float, default=1800.0,
    )
    parser.add_argument("--max-break-case-seconds", type=_positive_float)
    parser.add_argument("--max-call-time-seconds", type=_positive_float)
    parser.add_argument("--max-call-to-hoisted-ratio", type=_positive_float)
    arguments = parser.parse_args()
    if arguments.iterations <= 0 or arguments.heap_mb <= 0:
        parser.error("iterations and heap-mb must be positive")
    report = run(arguments)
    print(json.dumps({
        "claim": report["claim"],
        "outcome": report["outcome"],
        "evidence_dir": str(arguments.evidence_dir.resolve()),
        "report": str(arguments.evidence_dir.resolve() / "report.json"),
        "call_time_to_hoisted_elapsed_ratio":
            report["comparison"]["call_time_to_hoisted_elapsed_ratio"],
    }, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (GateError, inputs.InputError) as error:
        print(f"float performance gate failed: {error}", file=sys.stderr)
        raise SystemExit(1) from error
