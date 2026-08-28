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
import importlib
import json
import math
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import types
from typing import Any

HERE = Path(__file__).resolve().parent
RUNNER_SOURCE_BYTES = Path(__file__).read_bytes()


def _load_local_source(name: str, path: Path):
    """Execute exact local source bytes without consulting bytecode caches."""

    source = path.read_bytes()
    source_sha256 = hashlib.sha256(source).hexdigest()
    existing = sys.modules.get(name)
    if existing is not None:
        if (getattr(existing, "__candle_source_sha256__", None) !=
                source_sha256 or
                Path(getattr(existing, "__file__", "")).resolve() != path):
            raise RuntimeError(f"untrusted preloaded local module: {name}")
        return existing
    module = types.ModuleType(name)
    module.__file__ = str(path)
    module.__package__ = ""
    module.__candle_source_sha256__ = source_sha256
    module.__candle_source_bytes__ = source
    sys.modules[name] = module
    try:
        exec(compile(source, str(path), "exec", dont_inherit=True),
             module.__dict__)
    except BaseException:
        sys.modules.pop(name, None)
        raise
    return module


# Private names prevent a preloaded module in an embedding process from
# satisfying the exact-source execution contract.
inputs = _load_local_source(
    "_candle_float_performance_inputs",
    HERE / "generate_flyspeck_float_performance.py",
)
runtime_lock = _load_local_source(
    "_candle_float_performance_runtime_lock",
    HERE.parent / "runtime_lock.py",
)
provenance = _load_local_source(
    "_candle_float_performance_provenance",
    HERE.parent / "cakeml_artifact_provenance.py",
)

# Loaded only after its complete pinned source set has been copied into the
# retained evidence directory.  This deliberately has no ambient import.
pexpect: types.ModuleType | None = None


CLAIM = "performance observation only; not semantic, S2, or S3 evidence"
TRUST_BOUNDARY = {
    "assumes_no_hostile_same_uid_transient_mutation": True,
    "assumes_listed_host_program_boundaries_are_trusted": True,
    "host_program_assumptions": {
        "/bin/bash": "candle.sh privileged shell interpreter",
        "/usr/bin/env": "candle.sh clean-environment launcher",
        "/usr/bin/flock": "candle.sh shared build lock",
        "/usr/bin/git": "controller repository and commit-blob validation",
        "/usr/bin/ldd": "controller ELF dependency discovery",
        "/usr/bin/patch": "linked CakeML patch-derivation replay",
        "/usr/bin/python3": (
            "candle.sh linked-record validator invocation is not separately "
            "execution-bound; the controller's shared resolved Python image "
            "and base ELF closure are archived"
        ),
        "/usr/bin/readelf": "controller ELF dynamic-tag validation",
        "/usr/bin/readlink": "candle.sh path and runtime-alias resolution",
        "/usr/bin/stat": "candle.sh build-lock inode validation",
    },
    "detail": (
        "pre/postflight hashes detect persistent mutation, but do not exclude "
        "a hostile same-UID process that transiently replaces source or runtime "
        "paths and restores them before postflight; listed host-program roles "
        "have the explicit retention and execution-binding limits stated above"
    ),
}

EXPECTED_PYTHON_RUNTIME = {
    "execution_binding": "/proc/self/exe",
    "version": "3.12.3 (main, Jun 19 2026, 12:46:00) [GCC 13.3.0]",
    "executable": {
        "path": "/usr/bin/python3.12",
        "bytes": 8020928,
        "sha256":
            "1643dacd9feaedc58f3cc581e4d22577dfe25c09b10282936186ccf0f2e61118",
    },
    "elf_closure": {
        "policy": "ldd_roles_resolved_absolute_paths_and_content_v2",
        "files": {
            "/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2": {
                "bytes": 236616,
                "sha256":
                    "cd4df4f3c7b83673d61189bf2eaebd33ca4f2853ab9772b8a25e025ef99b1e81",
            },
            "/lib/x86_64-linux-gnu/libc.so.6": {
                "bytes": 2125328,
                "sha256":
                    "8db37cf3f2169f59a0f07ef1fea308c35656668c64c8ff294e1860f4121eb161",
            },
            "/lib/x86_64-linux-gnu/libexpat.so.1.9.1": {
                "bytes": 174336,
                "sha256":
                    "c42ff317838b4b4639e2ea801905f0317177c6df7e31b2f0d0240e3c3ac0cfde",
            },
            "/lib/x86_64-linux-gnu/libm.so.6": {
                "bytes": 952616,
                "sha256":
                    "e9c4b28d340e415b8137480ec442662f981e1399386c5931dae0e886e3639e91",
            },
            "/lib/x86_64-linux-gnu/libz.so.1.3": {
                "bytes": 113000,
                "sha256":
                    "9b64150b28505a33d6bc3ecf709c279f6de97a1c184dbda65d06ee4537f6d286",
            },
        },
        "roles": {
            "ld-linux-x86-64.so.2":
                "/lib/x86_64-linux-gnu/ld-linux-x86-64.so.2",
            "libc.so.6": "/lib/x86_64-linux-gnu/libc.so.6",
            "libexpat.so.1": "/lib/x86_64-linux-gnu/libexpat.so.1.9.1",
            "libm.so.6": "/lib/x86_64-linux-gnu/libm.so.6",
            "libz.so.1": "/lib/x86_64-linux-gnu/libz.so.1.3",
        },
        "virtual_objects": ["linux-vdso.so.1"],
    },
}
EXPECTED_PEXPECT_SOURCES = {
    "pexpect": {
        "path": "/usr/lib/python3/dist-packages/pexpect/__init__.py",
        "bytes": 4089,
        "sha256":
            "4ae418ce9571a73a8bc19d5febca2fe53bdccbc42ffde0f5fcdcae4880e26da5",
    },
    "pexpect.exceptions": {
        "path": "/usr/lib/python3/dist-packages/pexpect/exceptions.py",
        "bytes": 1068,
        "sha256":
            "03d0b53d66c17368fd00abe7bfb5243c26b08454c419899e50b5b4bf06ccbd74",
    },
    "pexpect.expect": {
        "path": "/usr/lib/python3/dist-packages/pexpect/expect.py",
        "bytes": 13827,
        "sha256":
            "28ab419b1d8c61afb20c4ef5e5794751c96829ee677410f7e7d6b83985570fce",
    },
    "pexpect.pty_spawn": {
        "path": "/usr/lib/python3/dist-packages/pexpect/pty_spawn.py",
        "bytes": 37382,
        "sha256":
            "67281262c767549e5a73188d33d80bbcbad3d8056a83026f6c370f693c71bfd1",
    },
    "pexpect.run": {
        "path": "/usr/lib/python3/dist-packages/pexpect/run.py",
        "bytes": 6629,
        "sha256":
            "3e44c0fc818e1f32d52bcf6d548ce92c9ec8da300d379a3b183707e64d4bcbc7",
    },
    "pexpect.spawnbase": {
        "path": "/usr/lib/python3/dist-packages/pexpect/spawnbase.py",
        "bytes": 21685,
        "sha256":
            "493864410db9c22480fbbbaabde2f785b912f059cb1407e4fa25e05f63ad398f",
    },
    "pexpect.utils": {
        "path": "/usr/lib/python3/dist-packages/pexpect/utils.py",
        "bytes": 6019,
        "sha256":
            "d63221cd4ede06f637a5b5b72d9a09842394d8a5aa82dcb91e043a541608a795",
    },
    "ptyprocess": {
        "path": "/usr/lib/python3/dist-packages/ptyprocess/__init__.py",
        "bytes": 138,
        "sha256":
            "b27f96ff59cd453b883a2d9a0841d52f4eb009525c47e2ce65d8295f3c05b935",
    },
    "ptyprocess.ptyprocess": {
        "path": "/usr/lib/python3/dist-packages/ptyprocess/ptyprocess.py",
        "bytes": 31686,
        "sha256":
            "b24dac536236d98ca5d60537163166a562f7078de8d0aa86ddddc223caf436af",
    },
    "ptyprocess.util": {
        "path": "/usr/lib/python3/dist-packages/ptyprocess/util.py",
        "bytes": 2785,
        "sha256":
            "ad001d0d165fa0e88e9fabf2916b61d3023a145280a7b689b4149db7e28159d5",
    },
}
EXPECTED_PYTHON_STARTUP_FLAGS = {
    "debug": 0,
    "inspect": 0,
    "interactive": 0,
    "optimize": 0,
    "dont_write_bytecode": 0,
    "no_user_site": 1,
    "no_site": 1,
    "ignore_environment": 1,
    "verbose": 0,
    "bytes_warning": 0,
    "quiet": 0,
    "hash_randomization": 1,
    "isolated": 1,
    "dev_mode": False,
    "utf8_mode": 0,
    "warn_default_encoding": 0,
    "safe_path": True,
    "int_max_str_digits": 4300,
}
EXPECTED_PYTHON_STARTUP_OPTIONS = {
    "xoptions": {},
    "warnoptions": [],
    "stdio_write_through": {
        "stdin": False,
        "stdout": False,
        "stderr": False,
    },
}


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


def data_record(value: bytes) -> dict[str, Any]:
    return {
        "bytes": len(value),
        "sha256": hashlib.sha256(value).hexdigest(),
    }


def python_startup_flags() -> dict[str, Any]:
    return {
        name: getattr(sys.flags, name)
        for name in EXPECTED_PYTHON_STARTUP_FLAGS
    }


def python_startup_options() -> dict[str, Any]:
    return {
        "xoptions": dict(sys._xoptions),
        "warnoptions": list(sys.warnoptions),
        "stdio_write_through": {
            "stdin": sys.stdin.write_through,
            "stdout": sys.stdout.write_through,
            "stderr": sys.stderr.write_through,
        },
    }


def require_direct_script_startup() -> dict[str, Any]:
    """Require the documented isolated, direct-source Python invocation."""

    source = Path(__file__).resolve()
    argv0 = Path(sys.argv[0]).resolve()
    try:
        compile(RUNNER_SOURCE_BYTES, str(source), "exec", dont_inherit=True)
    except (SyntaxError, UnicodeError, ValueError) as error:
        raise GateError("performance runner startup bytes are not source") from error
    record = {
        "module_name": __name__,
        "spec_is_none": __spec__ is None,
        "cached_is_none": globals().get("__cached__") is None,
        "argv0": str(argv0),
        "source_path": str(source),
    }
    require(record == {
        "module_name": "__main__",
        "spec_is_none": True,
        "cached_is_none": True,
        "argv0": str(source),
        "source_path": str(source),
    }, "performance runner must execute directly from its .py source")
    require(python_startup_flags() == EXPECTED_PYTHON_STARTUP_FLAGS,
            "performance runner Python startup flags mismatch; use python3 -I -S")
    require(python_startup_options() == EXPECTED_PYTHON_STARTUP_OPTIONS,
            "performance runner Python startup options mismatch")
    return record


def validate_python_runtime() -> dict[str, Any]:
    process_executable = Path("/proc/self/exe")
    require(process_executable.is_symlink(),
            "cannot bind the executing Python image through /proc/self/exe")
    executable = process_executable.resolve(strict=True)
    require(Path(sys.executable).resolve(strict=True) == executable,
            "Python executable metadata differs from the running image")
    executable_record = inputs.file_record(executable)
    observed = {
        "execution_binding": "/proc/self/exe",
        "version": sys.version,
        "executable": {
            "path": str(executable),
            **executable_record,
        },
        "elf_closure": provenance.elf_dynamic_closure(executable),
    }
    require(observed == EXPECTED_PYTHON_RUNTIME,
            "performance runner Python runtime identity mismatch")
    return observed


def local_python_modules() -> tuple[types.ModuleType, ...]:
    return inputs, provenance, runtime_lock


def _git_bytes(root: Path, *arguments: str) -> bytes:
    try:
        return subprocess.run(
            provenance.git_command(root, *arguments), check=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=provenance.git_environment(),
        ).stdout
    except subprocess.CalledProcessError as error:
        raise GateError(
            "Git byte check failed: " +
            error.stderr.decode(errors="replace").strip()
        ) from error


def collect_controller_execution(
    candle_root: Path, candle_commit: str,
) -> dict[str, Any]:
    """Bind executed controller sources, Python, and startup to one commit."""

    expected_root = HERE.parent.parent.resolve()
    require(candle_root == expected_root,
            "performance runner must execute from the supplied Candle root")
    direct_startup = require_direct_script_startup()
    sources: dict[str, dict[str, Any]] = {}
    for module in local_python_modules():
        path = Path(module.__file__).resolve()
        source = module.__candle_source_bytes__
        record = data_record(source)
        require(inputs.file_record(path) == record and
                module.__candle_source_sha256__ == record["sha256"],
                f"executed local source identity mismatch: {path.name}")
        sources[path.name] = {
            "source_path": str(path),
            "source_bytes": source,
            "execution_binding": "compiled-from-captured-source-bytes",
            **record,
        }
    runner = Path(__file__).resolve()
    runner_record = data_record(RUNNER_SOURCE_BYTES)
    require(runner == HERE / runner.name and
            inputs.file_record(runner) == runner_record,
            "top-level performance runner changed after startup capture")
    sources[runner.name] = {
        "source_path": str(runner),
        "source_bytes": RUNNER_SOURCE_BYTES,
        "execution_binding": "startup-captured-after-initial-compilation",
        **runner_record,
    }
    require(set(sources) == {
        "cakeml_artifact_provenance.py",
        "generate_flyspeck_float_performance.py",
        "run_flyspeck_float_performance_gate.py",
        "runtime_lock.py",
    }, "unexpected performance controller source set")
    commit_binding = {}
    for label, record in sorted(sources.items()):
        path = Path(record["source_path"])
        relative = path.relative_to(candle_root).as_posix()
        index = provenance.git_output(
            candle_root, "ls-files", "-v", "--", relative,
        )
        require(index == f"H {relative}",
                f"controller source has special index flags: {relative}")
        blob = _git_bytes(
            candle_root, "cat-file", "blob", f"{candle_commit}:{relative}",
        )
        require(blob == record["source_bytes"],
                f"executed controller source differs from commit: {relative}")
        commit_binding[label] = {
            "repository_path": relative,
            "index_tag": "H",
            **data_record(blob),
        }
    return {
        "direct_script_startup": direct_startup,
        "python_startup_flags": python_startup_flags(),
        "python_startup_options": python_startup_options(),
        "initial_top_level_compilation_in_host_trust_boundary": True,
        "local_sources": sources,
        "commit_binding": {
            "candle_commit": candle_commit,
            "sources": commit_binding,
        },
        "python_runtime": validate_python_runtime(),
        "trust_boundary": TRUST_BOUNDARY,
    }


def load_pexpect_from_pinned_sources(snapshot_root: Path):
    """Copy and import only the complete pinned pexpect/ptyprocess sources."""

    prefixes = ("pexpect", "ptyprocess")
    require(not any(
        name == prefix or name.startswith(prefix + ".")
        for name in sys.modules for prefix in prefixes
    ), "pexpect/ptyprocess were loaded before isolated source validation")
    require(not snapshot_root.exists() and not snapshot_root.is_symlink(),
            "pexpect source snapshot must be a new path")
    snapshot_root.mkdir(parents=True)
    for name, expected in sorted(EXPECTED_PEXPECT_SOURCES.items()):
        source = Path(expected["path"])
        observed = inputs.file_record(source)
        require(observed == {
            field: expected[field] for field in ("bytes", "sha256")
        }, f"pexpect source changed before snapshot: {name}")
        parts = name.split(".")
        destination = (
            snapshot_root / parts[0] /
            ("__init__.py" if len(parts) == 1 else f"{parts[-1]}.py")
        )
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(source.read_bytes())
        require(inputs.file_record(destination) == observed,
                f"pexpect source changed during snapshot: {name}")
        destination.chmod(0o444)
    with tempfile.TemporaryDirectory(
        prefix="candle-performance-empty-python-cache-"
    ) as temporary:
        previous_prefix = sys.pycache_prefix
        previous_dont_write = sys.dont_write_bytecode
        sys.pycache_prefix = temporary
        sys.dont_write_bytecode = True
        sys.path.insert(0, str(snapshot_root))
        try:
            module = importlib.import_module("pexpect")
            loaded_names = {
                name for name in sys.modules
                if any(name == prefix or name.startswith(prefix + ".")
                       for prefix in prefixes)
            }
            require(loaded_names == set(EXPECTED_PEXPECT_SOURCES),
                    "unexpected pexpect/ptyprocess module set")
            observed = {}
            cache_root = Path(temporary)
            for name in sorted(loaded_names):
                loaded = sys.modules[name]
                source = Path(loaded.__file__).resolve(strict=True)
                cached = Path(loaded.__cached__).resolve()
                require(cached.is_relative_to(cache_root) and
                        source.is_relative_to(snapshot_root) and
                        source.suffix == ".py",
                        f"Python package did not load from snapshot: {name}")
                observed[name] = {
                    "path": str(source),
                    **inputs.file_record(source),
                }
            require(all(
                {field: observed[name][field]
                 for field in ("bytes", "sha256")} ==
                {field: expected[field]
                 for field in ("bytes", "sha256")}
                for name, expected in EXPECTED_PEXPECT_SOURCES.items()
            ), "pexpect/ptyprocess source identity mismatch")
        finally:
            if sys.path[0] == str(snapshot_root):
                sys.path.pop(0)
            sys.pycache_prefix = previous_prefix
            sys.dont_write_bytecode = previous_dont_write
    return module, observed


class ProcessTreeSampler:
    """Sample Linux RSS for one process and its descendants."""

    def __init__(self, root_pid: int, interval: float = 0.05):
        self.root_pid = root_pid
        self.interval = interval
        self.peak_process_rss_kib = 0
        self.peak_tree_rss_kib = 0
        self.sample_count = 0
        self.sample_times: list[float] = []
        self.started_monotonic: float | None = None
        self.coverage: dict[str, Any] | None = None
        self._error: BaseException | None = None
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
        require(root_pid in rss,
                f"RSS sampler lost root process {root_pid}")
        return rss[root_pid], sum(rss[pid] for pid in tree if pid in rss)

    def _sample(self) -> None:
        process_rss, tree_rss = self.tree_rss(self.root_pid)
        require(process_rss > 0 and tree_rss >= process_rss,
                f"invalid RSS sample for root process {self.root_pid}")
        self.peak_process_rss_kib = max(
            self.peak_process_rss_kib, process_rss,
        )
        self.peak_tree_rss_kib = max(self.peak_tree_rss_kib, tree_rss)
        self.sample_count += 1
        self.sample_times.append(time.monotonic())

    @staticmethod
    def coverage_record(
        interval: float,
        started: float,
        sample_times: list[float],
    ) -> dict[str, Any]:
        require(interval > 0, "RSS sampling interval is not positive")
        require(len(sample_times) >= 2,
                "RSS sampler did not retain initial and final samples")
        points = [started, *sample_times]
        require(all(later >= earlier
                    for earlier, later in zip(points, points[1:])),
                "RSS sample timestamps are not monotonic")
        gaps = [later - earlier
                for earlier, later in zip(points, points[1:])]
        duration = sample_times[-1] - started
        maximum_allowed_gap = max(0.25, interval * 4.0)
        maximum_observed_gap = max(gaps)
        minimum_sample_count = max(
            2, math.ceil(duration / maximum_allowed_gap),
        )
        require(maximum_observed_gap <= maximum_allowed_gap,
                "RSS sampling cadence exceeded maximum allowed gap")
        require(len(sample_times) >= minimum_sample_count,
                "RSS sampling coverage has too few samples for its duration")
        return {
            "window_seconds": duration,
            "maximum_observed_gap_seconds": maximum_observed_gap,
            "maximum_allowed_gap_seconds": maximum_allowed_gap,
            "minimum_required_sample_count": minimum_sample_count,
        }

    def _run(self) -> None:
        try:
            self._sample()
            while not self._stop.wait(self.interval):
                self._sample()
        except BaseException as error:
            self._error = error
            self._stop.set()

    def start(self) -> None:
        self.started_monotonic = time.monotonic()
        self._thread.start()

    def stop(self) -> None:
        self._stop.set()
        self._thread.join()
        if self._error is not None:
            raise GateError(
                "RSS sampler thread failed: "
                f"{type(self._error).__name__}: {self._error}"
            ) from self._error
        self._sample()
        require(self.started_monotonic is not None,
                "RSS sampler has no start boundary")
        self.coverage = self.coverage_record(
            self.interval, self.started_monotonic, self.sample_times,
        )


class CandleSession:
    """A fresh authenticated Candle process with fail-closed load matching."""

    def __init__(
        self,
        candle_root: Path,
        environment: dict[str, str],
        transcript_path: Path,
        inactivity_timeout: float,
    ):
        require(pexpect is not None,
                "pinned pexpect snapshot was not loaded")
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
    require(sampler.coverage is not None,
            "RSS sampler coverage witness is missing")
    return {
        "elapsed_seconds": elapsed,
        "rss_scope": (
            "total process/tree RSS sampled from immediately before measured "
            "#use through source EOF and prompt; includes full-HOL baseline; "
            "tree sum can double-count shared pages"
        ),
        "rss_sampling_interval_seconds": sampler.interval,
        "rss_sample_count": sampler.sample_count,
        "rss_root_present_all_samples": True,
        "rss_sampler_thread_completed": True,
        "rss_sampling_window_seconds": sampler.coverage["window_seconds"],
        "rss_maximum_observed_gap_seconds":
            sampler.coverage["maximum_observed_gap_seconds"],
        "rss_maximum_allowed_gap_seconds":
            sampler.coverage["maximum_allowed_gap_seconds"],
        "rss_minimum_required_sample_count":
            sampler.coverage["minimum_required_sample_count"],
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


def _archive_bytes(
    value: bytes,
    destination: Path,
    evidence_dir: Path,
) -> dict[str, Any]:
    require(not destination.exists() and not destination.is_symlink(),
            f"refusing to replace controller evidence: {destination}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(value)
    observed = inputs.file_record(destination)
    require(observed == data_record(value),
            f"controller evidence changed on write: {destination}")
    destination.chmod(0o444)
    return {
        "path": str(destination.relative_to(evidence_dir)),
        **observed,
    }


def _archive_controller_execution(
    evidence_dir: Path,
    controller: dict[str, Any],
    pexpect_sources: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    archive_root = evidence_dir / "provenance"
    local_sources = []
    commit_sources = controller["commit_binding"]["sources"]
    for label, source in sorted(controller["local_sources"].items()):
        destination = archive_root / "python" / label
        local_sources.append({
            "label": label,
            "source_path": source["source_path"],
            "execution_binding": source["execution_binding"],
            "commit_binding": commit_sources[label],
            **_archive_bytes(
                source["source_bytes"], destination, evidence_dir,
            ),
        })

    python_runtime = controller["python_runtime"]
    executable = python_runtime["executable"]
    executable_archive = _archive_file(
        Path(executable["path"]),
        archive_root / "python-runtime" / Path(executable["path"]).name,
        evidence_dir,
        {field: executable[field] for field in ("bytes", "sha256")},
    )
    elf_objects = []
    for source_string, expected in sorted(
        python_runtime["elf_closure"]["files"].items()
    ):
        source = Path(source_string)
        destination = (
            archive_root / "python-runtime-elf" /
            f"{expected['sha256'][:16]}-{source.name}"
        )
        elf_objects.append({
            "source_path": source_string,
            **_archive_file(
                source, destination, evidence_dir, expected,
            ),
        })

    retained_pexpect = []
    for label, source in sorted(pexpect_sources.items()):
        path = Path(source["path"])
        record = inputs.file_record(path)
        retained_pexpect.append({
            "label": label,
            "source_path": EXPECTED_PEXPECT_SOURCES[label]["path"],
            "execution_binding": "imported-from-retained-source-snapshot",
            "path": str(path.relative_to(evidence_dir)),
            **record,
        })

    return {
        "direct_script_startup": controller["direct_script_startup"],
        "python_startup_flags": controller["python_startup_flags"],
        "python_startup_options": controller["python_startup_options"],
        "initial_top_level_compilation_in_host_trust_boundary":
            controller["initial_top_level_compilation_in_host_trust_boundary"],
        "commit_binding": {
            "candle_commit": controller["commit_binding"]["candle_commit"],
        },
        "local_sources": local_sources,
        "python_runtime": {
            "execution_binding": python_runtime["execution_binding"],
            "version": python_runtime["version"],
            "executable": {
                "source_path": executable["path"],
                **executable_archive,
            },
            "elf_policy": python_runtime["elf_closure"]["policy"],
            "elf_roles": python_runtime["elf_closure"]["roles"],
            "virtual_objects": python_runtime["elf_closure"]["virtual_objects"],
            "elf_objects": elf_objects,
        },
        "pexpect_sources": retained_pexpect,
        "trust_boundary": controller["trust_boundary"],
    }


def _verify_controller_execution(
    candle_root: Path,
    evidence_dir: Path,
    controller: dict[str, Any],
    archived: dict[str, Any],
) -> None:
    observed = collect_controller_execution(
        candle_root, controller["commit_binding"]["candle_commit"],
    )
    require(observed == controller,
            "performance controller execution identity changed")
    for record in archived["local_sources"]:
        require(inputs.file_record(evidence_dir / record["path"]) == {
            field: record[field] for field in ("bytes", "sha256")
        }, f"retained controller source changed: {record['label']}")
    python_runtime = archived["python_runtime"]
    executable = python_runtime["executable"]
    require(inputs.file_record(evidence_dir / executable["path"]) == {
        field: executable[field] for field in ("bytes", "sha256")
    }, "retained Python executable changed")
    for record in python_runtime["elf_objects"]:
        require(inputs.file_record(evidence_dir / record["path"]) == {
            field: record[field] for field in ("bytes", "sha256")
        }, f"retained Python ELF object changed: {record['path']}")
    for record in archived["pexpect_sources"]:
        require(inputs.file_record(evidence_dir / record["path"]) == {
            field: record[field] for field in ("bytes", "sha256")
        }, f"retained pexpect source changed: {record['label']}")


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


def _verify_json_evidence(
    path: Path,
    expected_value: dict[str, Any],
    expected_record: dict[str, Any] | None,
    label: str,
) -> dict[str, Any]:
    require(path.is_file() and not path.is_symlink(),
            f"{label} is not an ordinary file")
    try:
        observed_value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateError(f"cannot reread {label}: {error}") from error
    require(observed_value == expected_value,
            f"{label} semantics changed after persistence")
    observed_record = inputs.file_record(path)
    if expected_record is not None:
        require(observed_record == expected_record,
                f"{label} content hash changed after persistence")
    return observed_record


def _verify_scenario_journals(
    evidence_dir: Path,
    scenarios: dict[str, dict[str, Any]],
    expected_records: dict[str, dict[str, Any]] | None = None,
) -> dict[str, dict[str, Any]]:
    require(set(scenarios) == {"call_time", "hoisted", "break_case_log"},
            "completed scenario set is not exact")
    if expected_records is not None:
        require(set(expected_records) == set(scenarios),
                "scenario-journal evidence set is not exact")
    records = {}
    for name, scenario in sorted(scenarios.items()):
        path = evidence_dir / f"scenario-{name}.json"
        if expected_records is not None:
            require(expected_records[name].get("path") == path.name,
                    f"scenario journal {name} evidence path is not canonical")
        record = _verify_json_evidence(
            path, scenario,
            ({field: expected_records[name][field]
              for field in ("bytes", "sha256")}
             if expected_records is not None else None),
            f"scenario journal {name}",
        )
        records[name] = {
            "path": str(path.relative_to(evidence_dir)),
            **record,
        }
    return records


def _verify_scenario_transcripts(
    evidence_dir: Path,
    scenarios: dict[str, dict[str, Any]],
) -> None:
    require(set(scenarios) == {"call_time", "hoisted", "break_case_log"},
            "completed transcript scenario set is not exact")
    for name, scenario in sorted(scenarios.items()):
        binding = scenario.get("transcript")
        require(isinstance(binding, dict) and
                set(binding) == {"path", "bytes", "sha256"},
                f"scenario {name} transcript binding is malformed")
        expected_path = f"transcripts/{name}.log"
        require(binding["path"] == expected_path,
                f"scenario {name} transcript path is not canonical")
        path = evidence_dir / expected_path
        require(path.is_file() and not path.is_symlink(),
                f"scenario {name} transcript is not an ordinary file")
        require(inputs.file_record(path) == {
            field: binding[field] for field in ("bytes", "sha256")
        }, f"scenario {name} transcript content hash changed")


def _verify_completed_success_evidence(
    evidence_dir: Path,
    report: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Rebind every success journal immediately before receipt creation."""

    report_record = _verify_json_evidence(
        evidence_dir / "report.json", report, None, "persisted report",
    )
    attempt_evidence = report["evidence"]["attempt"]
    require(attempt_evidence.get("path") == "attempt.json",
            "attempt evidence path is not canonical")
    attempt_path = evidence_dir / attempt_evidence["path"]
    require(attempt_path.is_file() and not attempt_path.is_symlink(),
            "attempt record is not an ordinary file")
    try:
        attempt = json.loads(attempt_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise GateError(f"cannot reread attempt record: {error}") from error
    require(isinstance(attempt, dict) and attempt.get("schema") == 1 and
            attempt.get("kind") == "flyspeck-float-performance-attempt" and
            attempt.get("state") == "running",
            "attempt record semantics changed after persistence")
    require(inputs.file_record(attempt_path) == {
        field: attempt_evidence[field] for field in ("bytes", "sha256")
    }, "attempt record content hash changed after persistence")
    _verify_scenario_journals(
        evidence_dir, report["scenarios"],
        report["evidence"]["scenario_journals"],
    )
    _verify_scenario_transcripts(evidence_dir, report["scenarios"])
    return attempt, report_record


def _run_attempt(
    arguments: argparse.Namespace,
    runtime_lock_handle: runtime_lock.BuildLock,
) -> dict[str, Any]:
    global pexpect

    candle_root = arguments.candle_root.resolve()
    flyspeck_root = arguments.flyspeck_root.resolve()
    evidence_dir = arguments.evidence_dir.resolve()

    try:
        linked = provenance.validate_linked_record(candle_root)
        runtime_environment = provenance.runtime_environment({
            "CML_HEAP_SIZE": str(arguments.heap_mb),
        })
    except Exception as error:  # provenance package owns its exception type
        raise GateError(f"linked Candle provenance failed: {error}") from error
    controller = collect_controller_execution(
        candle_root, linked["candle_commit"],
    )
    launcher = candle_root / "candle.sh"
    require(launcher.is_file() and os.access(launcher, os.X_OK),
            f"authenticated Candle launcher is unavailable: {launcher}")
    generated_dir, transcript_dir, output_path = _create_evidence_layout(
        evidence_dir, candle_root, flyspeck_root,
    )
    pexpect, pexpect_sources = load_pexpect_from_pinned_sources(
        evidence_dir / "provenance/python-packages",
    )
    archived_controller = _archive_controller_execution(
        evidence_dir, controller, pexpect_sources,
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
        "controller_execution": archived_controller,
        "trust_boundary": TRUST_BOUNDARY,
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
    attempt_record = inputs.file_record(attempt_path)
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
        "trust_boundary": TRUST_BOUNDARY,
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
    _verify_controller_execution(
        candle_root, evidence_dir, controller, archived_controller,
    )
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
    _verify_json_evidence(
        attempt_path, attempt, attempt_record, "attempt record",
    )
    scenario_journal_records = _verify_scenario_journals(
        evidence_dir, scenarios,
    )

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
        "trust_boundary": TRUST_BOUNDARY,
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
            "attempt": {
                "path": str(attempt_path.relative_to(evidence_dir)),
                **attempt_record,
            },
            "scenario_journals": scenario_journal_records,
            "gate_config": {
                "path": str(config_path.relative_to(evidence_dir)),
                **config_record,
            },
            "linked_runtime_archive": archived_runtime,
            "controller_execution": archived_controller,
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
            "transcript_directory": str(
                transcript_dir.relative_to(evidence_dir)
            ),
        },
        "postflight": {
            "all_session_check_axioms": True,
            "check_linked_postflight": True,
            "linked_provenance_revalidated": True,
            "linked_provenance_unchanged": True,
            "linked_runtime_archive_rehashed": True,
            "controller_execution_revalidated": True,
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
    _verify_json_evidence(
        output_path, report, None, "persisted report",
    )
    if failures:
        raise GateError("; ".join(failures) + f"; report: {output_path}")
    return report


def _evidence_inventory(evidence_dir: Path) -> dict[str, Any]:
    inventory = {}
    for path in sorted(evidence_dir.rglob("*")):
        if path.is_file() and not path.is_symlink() and path.name != "receipt.json":
            inventory[str(path.relative_to(evidence_dir))] = inputs.file_record(path)
    return inventory


def _validate_success_inventory(
    report: dict[str, Any],
    report_record: dict[str, Any],
    inventory: dict[str, dict[str, Any]],
) -> None:
    """Cross-bind receipt inventory to the just-verified success records."""

    require(inventory.get("report.json") == report_record,
            "success inventory report record differs from verified report")
    attempt = report["evidence"]["attempt"]
    require(inventory.get(attempt["path"]) == {
        field: attempt[field] for field in ("bytes", "sha256")
    }, "success inventory attempt record differs from report binding")
    for name, record in sorted(
        report["evidence"]["scenario_journals"].items()
    ):
        require(inventory.get(record["path"]) == {
            field: record[field] for field in ("bytes", "sha256")
        }, f"success inventory scenario {name} differs from report binding")
    for name, scenario in sorted(report["scenarios"].items()):
        transcript = scenario["transcript"]
        require(inventory.get(transcript["path"]) == {
            field: transcript[field] for field in ("bytes", "sha256")
        }, f"success inventory transcript {name} differs from scenario binding")


def _failure_postflight(
    arguments: argparse.Namespace,
    evidence_dir: Path,
) -> dict[str, Any]:
    result: dict[str, Any] = {}
    linked_archive = evidence_dir / "provenance/linked-provenance.json"
    if linked_archive.is_file() and not linked_archive.is_symlink():
        try:
            archived = json.loads(linked_archive.read_text(encoding="utf-8"))
            current = provenance.validate_linked_record(
                arguments.candle_root.resolve()
            )
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
        success_attempt, success_report_record = (
            _verify_completed_success_evidence(evidence_dir, report)
        )
        success_inventory = _evidence_inventory(evidence_dir)
        _validate_success_inventory(
            report, success_report_record, success_inventory,
        )
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
        "started_utc": success_attempt["started_utc"],
        "finished_utc": _utc_now(),
        "report": success_report_record,
        "evidence_inventory": success_inventory,
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
    require_direct_script_startup()
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
