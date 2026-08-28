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
import datetime as dt
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import shutil
import sys
import threading
import time
from types import ModuleType
from typing import Any

import pexpect

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import generate_flyspeck_float_performance as inputs
import runtime_lock


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
        if root_pid not in rss:
            return 0, 0
        return rss[root_pid], sum(rss[pid] for pid in tree if pid in rss)

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
        except BaseException:
            if self.process is not None:
                self.process.close(force=True)
            self.transcript.close()
            raise

    def abort(self) -> None:
        if self.process.isalive():
            self.process.close(force=True)
        self.transcript.close()

    def finish(self, wall_timeout: float = 300.0) -> None:
        try:
            self.process.sendeof()
            self.process.expect(pexpect.EOF, timeout=wall_timeout)
            self.process.close()
            require(
                self.process.exitstatus == 0 and
                self.process.signalstatus is None,
                "Candle performance session did not exit cleanly",
            )
        finally:
            if self.process.isalive():
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
        started = time.perf_counter()
        self.process.sendline(f"#use {json.dumps(str(path))};;")
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
            "#use through source EOF and prompt; includes full-HOL baseline; "
            "tree sum can double-count shared pages"
        ),
        "rss_sampling_interval_seconds": sampler.interval,
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
    source_paths: dict[str, Path],
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
    succeeded = False
    try:
        hol_elapsed = session.full_hol_preflight(hol_wall_timeout)
        if name == "break_case_log":
            type_path = source_paths["break_case_type"]
            setup_elapsed = session.load(type_path, scenario_wall_timeout)
            measured = _measure_load(
                session,
                source_paths["break_case_log"],
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
        succeeded = True
    finally:
        try:
            if succeeded:
                session.finish()
            else:
                session.abort()
        finally:
            if transcript_path.is_file() and not transcript_path.is_symlink():
                transcript_path.chmod(0o444)
    measured["transcript"] = {
        "path": str(transcript_path.relative_to(log_dir.parent)),
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


def observation_outcome(
    iterations: int,
    failures: list[str],
    max_break_case_seconds: float | None,
    max_call_time_seconds: float | None,
    max_call_to_hoisted_ratio: float | None,
) -> tuple[str, bool]:
    policy_complete = (
        iterations == inputs.DEFAULT_ITERATIONS and
        all(value is not None for value in (
            max_break_case_seconds, max_call_time_seconds,
            max_call_to_hoisted_ratio,
        ))
    )
    if failures:
        return "thresholds_failed", policy_complete
    if policy_complete:
        return "thresholds_satisfied", True
    return "observation_complete", False


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
    temporary = path.with_name(f".{path.name}.tmp.{os.getpid()}")
    require(not temporary.exists(), f"stale JSON temporary file: {temporary}")
    try:
        temporary.write_text(
            json.dumps(
                value, allow_nan=False, indent=2, sort_keys=True,
            ) + "\n",
            encoding="utf-8",
        )
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def _utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def _archive_file(
    source: Path,
    destination: Path,
    evidence_dir: Path,
    expected: dict[str, Any] | None = None,
) -> dict[str, Any]:
    require(
        source.is_file() and not source.is_symlink() and
        not destination.exists() and not destination.is_symlink(),
        f"cannot archive ordinary performance evidence input: {source}",
    )
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, destination)
    observed = inputs.file_record(destination)
    if expected is not None:
        require(observed == expected,
                f"archived performance evidence mismatch: {destination}")
    destination.chmod(0o444)
    return {
        "path": str(destination.relative_to(evidence_dir)),
        **observed,
    }


def _archive_linked_runtime(
    candle_root: Path,
    evidence_dir: Path,
    linked: dict[str, Any],
) -> dict[str, Any]:
    """Retain the mutable local/system inputs behind a linked record."""

    archive_root = evidence_dir / "provenance"
    build_dir = candle_root / "candle/build"
    linked_record_path = build_dir / "cakeml-build-provenance.json"
    archived = {
        "linked_provenance": _archive_file(
            linked_record_path, archive_root / "linked-provenance.json",
            evidence_dir,
        ),
        "bootstrap_provenance": _archive_file(
            build_dir / "bootstrap-provenance.json",
            archive_root / "bootstrap-provenance.json", evidence_dir,
            linked["bootstrap_record"],
        ),
        "bootstrap_log": _archive_file(
            build_dir / "bootstrap.log", archive_root / "bootstrap.log",
            evidence_dir, linked["bootstrap_log"],
        ),
        "runtime_elf_objects": [],
    }
    linked_archive = evidence_dir / archived["linked_provenance"]["path"]
    require(json.loads(linked_archive.read_text(encoding="utf-8")) == linked,
            "archived linked provenance differs from validated record")
    for source_string, expected in sorted(
        linked["runtime_elf_closure"]["files"].items()
    ):
        source = Path(source_string)
        destination = (
            archive_root / "runtime-elf" /
            f"{expected['sha256'][:16]}-{source.name}"
        )
        archived["runtime_elf_objects"].append({
            "source_path": source_string,
            **_archive_file(source, destination, evidence_dir, expected),
        })
    return archived


def _archive_performance_sources(
    candle_root: Path,
    flyspeck_root: Path,
    evidence_dir: Path,
    receipt: dict[str, Any],
    linked: dict[str, Any],
) -> dict[str, Any]:
    manifest_source = candle_root / "candle/flyspeck_manifest.json"
    manifest_record = inputs.file_record(manifest_source)
    require(manifest_record["sha256"] == linked["manifest_sha256"],
            "performance source manifest differs from linked provenance")
    manifest = json.loads(manifest_source.read_text(encoding="utf-8"))
    archive_root = evidence_dir / "sources"
    archived = {
        "manifest": _archive_file(
            manifest_source, archive_root / "flyspeck_manifest.json",
            evidence_dir, manifest_record,
        ),
        "flyspeck": {},
    }
    source_contracts = {
        "break_case_log": {
            "key": inputs.SOURCE_KEY,
            "path": inputs.SOURCE_PATH,
            "expected": {
                field: receipt["flyspeck"][field]
                for field in ("bytes", "sha256")
            },
        },
        "break_case_type": {
            "key": (
                "flyspeck:text_formalization/nonlinear/"
                "break_case_type.hl"
            ),
            "path": Path(
                "text_formalization/nonlinear/break_case_type.hl"
            ),
            "expected": None,
        },
    }
    for label, contract in source_contracts.items():
        node = manifest.get("source_nodes", {}).get(contract["key"])
        require(
            isinstance(node, dict) and node.get("repository") == "flyspeck" and
            node.get("path") == contract["path"].as_posix(),
            f"{label} is absent from the authenticated source graph",
        )
        node_record = {field: node[field] for field in ("bytes", "sha256")}
        if contract["expected"] is not None:
            require(node_record == contract["expected"],
                    f"{label} receipt differs from manifest")
        source = (flyspeck_root / contract["path"]).resolve()
        require(source.is_relative_to(flyspeck_root),
                f"{label} escaped the Flyspeck source root")
        destination = archive_root / "flyspeck" / contract["path"]
        archived["flyspeck"][label] = {
            "source_key": contract["key"],
            "source_path": contract["path"].as_posix(),
            **_archive_file(source, destination, evidence_dir, node_record),
        }
    return archived


def _verify_performance_source_archive(
    evidence_dir: Path,
    archived: dict[str, Any],
    linked: dict[str, Any],
) -> None:
    manifest_record = archived["manifest"]
    require(
        inputs.file_record(evidence_dir / manifest_record["path"]) == {
            field: manifest_record[field] for field in ("bytes", "sha256")
        } and manifest_record["sha256"] == linked["manifest_sha256"],
        "retained Flyspeck manifest changed during performance gate",
    )
    manifest = json.loads(
        (evidence_dir / manifest_record["path"]).read_text(encoding="utf-8")
    )
    for label, record in archived["flyspeck"].items():
        node = manifest["source_nodes"][record["source_key"]]
        expected = {field: node[field] for field in ("bytes", "sha256")}
        require(
            inputs.file_record(evidence_dir / record["path"]) == expected,
            f"retained Flyspeck {label} changed during performance gate",
        )


def _verify_linked_runtime_archive(
    evidence_dir: Path,
    archived: dict[str, Any],
    linked: dict[str, Any],
) -> None:
    for label in ("linked_provenance", "bootstrap_provenance",
                  "bootstrap_log"):
        record = archived[label]
        require(
            inputs.file_record(evidence_dir / record["path"]) == {
                field: record[field] for field in ("bytes", "sha256")
            },
            f"retained {label} changed during performance gate",
        )
    linked_archive = evidence_dir / archived["linked_provenance"]["path"]
    require(json.loads(linked_archive.read_text(encoding="utf-8")) == linked,
            "retained linked provenance semantics changed")
    expected_elf = linked["runtime_elf_closure"]["files"]
    require(
        {record["source_path"] for record in archived["runtime_elf_objects"]}
        == set(expected_elf),
        "retained runtime ELF archive has the wrong object set",
    )
    for record in archived["runtime_elf_objects"]:
        expected = expected_elf[record["source_path"]]
        require(
            inputs.file_record(evidence_dir / record["path"]) == expected,
            f"retained runtime ELF object changed: {record['path']}",
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


def _run_attempt(
    arguments: argparse.Namespace,
    runtime_lock_handle: runtime_lock.BuildLock,
) -> dict[str, Any]:
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
    attempt_path = evidence_dir / "attempt.json"
    attempt = {
        "schema": 1,
        "kind": "flyspeck-float-performance-attempt",
        "claim": CLAIM,
        "state": "running",
        "started_utc": _utc_now(),
        "runtime_environment": runtime_environment,
        "runtime_lock": runtime_lock_handle.record,
        "repositories": {
            "candle": linked["candle_commit"],
            "cakeml": linked["cakeml_commit"],
            "hol4": linked["hol4_commit"],
            "flyspeck": inputs.EXPECTED_FLYSPECK_COMMIT,
        },
        "manifest_sha256": linked["manifest_sha256"],
        "linked_provenance_sha256": sha256_file(
            candle_root / "candle/build/cakeml-build-provenance.json"
        ),
        "parameters": {
            "iterations": arguments.iterations,
            "heap_mb": arguments.heap_mb,
            "inactivity_timeout_seconds": arguments.inactivity_timeout,
            "hol_wall_timeout_seconds": arguments.hol_wall_timeout,
            "scenario_wall_timeout_seconds": arguments.scenario_wall_timeout,
        },
    }
    _write_json(attempt_path, attempt)
    attempt_path.chmod(0o444)
    linked_record_path = (
        candle_root / "candle/build/cakeml-build-provenance.json"
    )
    archived_runtime = _archive_linked_runtime(
        candle_root, evidence_dir, linked,
    )
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
    config_record = inputs.file_record(config_path)
    config_path.chmod(0o444)
    receipt = inputs.materialize(
        candle_root, flyspeck_root, generated_dir, arguments.iterations,
    )
    require(receipt["manifest"]["sha256"] == linked["manifest_sha256"],
            "generated input manifest differs from linked provenance")
    for name in receipt["outputs"]:
        (generated_dir / name).chmod(0o444)
    (generated_dir / "flyspeck_float_performance_inputs.json").chmod(0o444)
    archived_sources = _archive_performance_sources(
        candle_root, flyspeck_root, evidence_dir, receipt, linked,
    )
    source_paths = {
        label: evidence_dir / record["path"]
        for label, record in archived_sources["flyspeck"].items()
    }
    scenarios = {}
    for name in ("call_time", "hoisted", "break_case_log"):
        scenarios[name] = _run_one(
            name, candle_root, source_paths, generated_dir, transcript_dir,
            runtime_environment, arguments.inactivity_timeout,
            arguments.hol_wall_timeout, arguments.scenario_wall_timeout,
        )
        scenario_path = evidence_dir / f"scenario-{name}.json"
        _write_json(scenario_path, scenarios[name])
        scenario_path.chmod(0o444)

    try:
        linked_postflight = provenance.validate_linked_record(candle_root)
    except Exception as error:  # provenance package owns its exception type
        raise GateError(
            f"linked Candle provenance postflight failed: {error}"
        ) from error
    require(linked_postflight == linked,
            "linked Candle provenance record changed during the run")
    _verify_linked_runtime_archive(evidence_dir, archived_runtime, linked)
    _verify_performance_source_archive(
        evidence_dir, archived_sources, linked,
    )
    validated_postflight = inputs.validate_inputs(candle_root, flyspeck_root)
    validated_postflight.pop("source_text")
    require(validated_postflight == {
        "manifest": receipt["manifest"],
        "flyspeck": receipt["flyspeck"],
    }, "Flyspeck source or manifest changed during the run")
    _verify_generated_inputs(generated_dir, receipt)
    require(inputs.file_record(config_path) == config_record,
            "performance gate configuration changed during the run")

    ratio = (scenarios["call_time"]["elapsed_seconds"] /
             scenarios["hoisted"]["elapsed_seconds"])
    failures = threshold_failures(
        scenarios, arguments.max_break_case_seconds,
        arguments.max_call_time_seconds, arguments.max_call_to_hoisted_ratio,
    )
    outcome, supplied_threshold_set_complete = observation_outcome(
        arguments.iterations, failures, arguments.max_break_case_seconds,
        arguments.max_call_time_seconds,
        arguments.max_call_to_hoisted_ratio,
    )
    report = {
        "schema": 1,
        "kind": "flyspeck-float-performance-gate",
        "claim": CLAIM,
        "outcome": outcome,
        "performance_accepted": False,
        "reviewed_acceptance_contract": None,
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
                "path": str(config_path.relative_to(evidence_dir)),
                **config_record,
            },
            "linked_runtime_archive": archived_runtime,
            "performance_source_archive": archived_sources,
            "generated_input_receipt": {
                "path": str(
                    (generated_dir / "flyspeck_float_performance_inputs.json").relative_to(
                        evidence_dir
                    )
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
            "linked_runtime_archive_rehashed": True,
            "performance_source_archive_rehashed": True,
            "flyspeck_manifest_source_revalidated": True,
            "generated_inputs_rehashed": True,
            "gate_configuration_rehashed": True,
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
            "supplied_threshold_set_complete":
                supplied_threshold_set_complete,
            "required_iterations_for_acceptance": inputs.DEFAULT_ITERATIONS,
            "max_break_case_seconds": arguments.max_break_case_seconds,
            "max_call_time_seconds": arguments.max_call_time_seconds,
            "max_call_to_hoisted_ratio": arguments.max_call_to_hoisted_ratio,
            "failures": failures,
        },
    }
    _write_json(output_path, report)
    output_path.chmod(0o444)
    if failures:
        raise GateError("; ".join(failures) + f"; report: {output_path}")
    return report


def _evidence_inventory(evidence_dir: Path) -> dict[str, Any]:
    inventory = {}
    for path in sorted(evidence_dir.rglob("*")):
        if path.is_file() and not path.is_symlink() and path.name != "receipt.json":
            inventory[str(path.relative_to(evidence_dir))] = inputs.file_record(path)
    return inventory


def _failure_postflight(
    arguments: argparse.Namespace,
    evidence_dir: Path,
) -> dict[str, Any]:
    result: dict[str, Any] = {}
    linked_archive = evidence_dir / "provenance/linked-provenance.json"
    if linked_archive.is_file() and not linked_archive.is_symlink():
        try:
            archived = json.loads(linked_archive.read_text(encoding="utf-8"))
            current = _load_provenance_module(
                arguments.candle_root.resolve()
            ).validate_linked_record(arguments.candle_root.resolve())
            result["linked_provenance_valid"] = True
            result["linked_provenance_unchanged"] = current == archived
        except Exception as error:
            result["linked_provenance_valid"] = False
            result["linked_provenance_error"] = str(error)
    try:
        validated = inputs.validate_inputs(
            arguments.candle_root.resolve(), arguments.flyspeck_root.resolve(),
        )
        validated.pop("source_text")
        result["flyspeck_manifest_source_valid"] = True
    except Exception as error:
        result["flyspeck_manifest_source_valid"] = False
        result["flyspeck_manifest_source_error"] = str(error)
    return result


def _completed_scenario_journals(
    evidence_dir: Path,
) -> tuple[dict[str, Any], dict[str, Any]]:
    completed = {}
    errors = {}
    for name in ("call_time", "hoisted", "break_case_log"):
        path = evidence_dir / f"scenario-{name}.json"
        if not path.exists():
            continue
        if not path.is_file() or path.is_symlink():
            errors[name] = {"message": "scenario journal is not ordinary"}
            continue
        record = inputs.file_record(path)
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
            require(isinstance(value, dict), "scenario journal is not an object")
            completed[name] = value
        except Exception as error:
            errors[name] = {
                "message": str(error),
                "record": record,
            }
    return completed, errors


def run(arguments: argparse.Namespace) -> dict[str, Any]:
    evidence_dir = arguments.evidence_dir.resolve()
    runtime_lock_handle = runtime_lock.acquire_build_lock(
        arguments.candle_root.resolve()
    )
    try:
        report = _run_attempt(arguments, runtime_lock_handle)
    except BaseException as error:
        attempt_path = evidence_dir / "attempt.json"
        if attempt_path.is_file() and not attempt_path.is_symlink():
            try:
                attempt = json.loads(attempt_path.read_text(encoding="utf-8"))
                if (attempt.get("schema") == 1 and
                        attempt.get("kind") ==
                        "flyspeck-float-performance-attempt"):
                    receipt_path = evidence_dir / "receipt.json"
                    require(not receipt_path.exists(),
                            "performance receipt already exists")
                    completed_scenarios, scenario_journal_errors = (
                        _completed_scenario_journals(evidence_dir)
                    )
                    try:
                        failure_postflight = _failure_postflight(
                            arguments, evidence_dir,
                        )
                    except BaseException as postflight_error:
                        failure_postflight = {
                            "completed": False,
                            "error": {
                                "type": type(postflight_error).__name__,
                                "message": str(postflight_error),
                            },
                        }
                    receipt = {
                        **attempt,
                        "kind": "flyspeck-float-performance-receipt",
                        "state": "failed",
                        "finished_utc": _utc_now(),
                        "validation_error": {
                            "type": type(error).__name__,
                            "message": str(error),
                        },
                        "completed_scenarios": completed_scenarios,
                        "scenario_journal_errors": scenario_journal_errors,
                        "failure_postflight": failure_postflight,
                        "evidence_inventory": _evidence_inventory(evidence_dir),
                    }
                    _write_json(receipt_path, receipt)
                    receipt_path.chmod(0o444)
            except BaseException as receipt_error:
                if isinstance(error, (KeyboardInterrupt, SystemExit)):
                    raise
                raise GateError(
                    f"{error}; failure receipt construction also failed: "
                    f"{type(receipt_error).__name__}: {receipt_error}; "
                    f"retained evidence: {evidence_dir}"
                ) from error
        if isinstance(error, (KeyboardInterrupt, SystemExit)):
            raise
        suffix = (
            f"; retained evidence: {evidence_dir}"
            if attempt_path.is_file() else ""
        )
        raise GateError(f"{error}{suffix}") from error
    receipt_path = evidence_dir / "receipt.json"
    receipt = {
        "schema": 1,
        "kind": "flyspeck-float-performance-receipt",
        "claim": CLAIM,
        "state": "completed",
        "started_utc": json.loads(
            (evidence_dir / "attempt.json").read_text(encoding="utf-8")
        )["started_utc"],
        "finished_utc": _utc_now(),
        "report": inputs.file_record(evidence_dir / "report.json"),
        "evidence_inventory": _evidence_inventory(evidence_dir),
    }
    _write_json(receipt_path, receipt)
    receipt_path.chmod(0o444)
    return report


def _positive_float(value: str) -> float:
    parsed = float(value)
    if not math.isfinite(parsed) or parsed <= 0:
        raise argparse.ArgumentTypeError("value must be positive and finite")
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
