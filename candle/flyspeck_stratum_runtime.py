#!/usr/bin/env python3
"""Run one authenticated cumulative Flyspeck stratum in compiled Candle.

The input is a materialized plan produced by ``flyspeck_stratum_plan.py``.
Every attempt starts a fresh process, reauthenticates the linked CakeML
artifact and all plan inputs, and writes an authenticated read-only runtime
snapshot plus an append-only-by-convention attempt directory.  A
successful receipt proves only that the selected source actions completed. A
schema-5 receipt adds unapproved semantic observations; it does not become
S2/S3 evidence without separate independent approval.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import math
import os
import re
import resource
import secrets
import shutil
import signal
import subprocess
import sys
import types
from pathlib import Path
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


# Private module names prevent an unrelated earlier import in a test harness or
# embedding process from satisfying the exact-source execution contract.
cakeml_artifact_provenance = _load_local_source(
    "_candle_stratum_cakeml_artifact_provenance",
    HERE / "cakeml_artifact_provenance.py",
)
cakeml_bootstrap_transition = _load_local_source(
    "_candle_stratum_cakeml_bootstrap_transition",
    HERE / "cakeml_bootstrap_transition.py",
)
flyspeck_stratum_plan = _load_local_source(
    "_candle_stratum_flyspeck_stratum_plan",
    HERE / "flyspeck_stratum_plan.py",
)
runtime_lock = _load_local_source(
    "_candle_stratum_runtime_lock", HERE / "runtime_lock.py",
)
reference_protocol = _load_local_source(
    "_candle_stratum_reference_protocol", HERE / "reference_protocol.py",
)


MANIFEST_RELATIVE = Path("candle/flyspeck_manifest.json")
SOURCE_DIGEST_RELATIVE = Path("candle/flyspeck_source_digests.ml")
SETUP_RELATIVE = Path("candle/flyspeck_stratum_setup.ml")
CHECK_RELATIVE = Path("candle/flyspeck_stratum_check.ml")
FINGERPRINT_RELATIVE = Path("candle/fingerprint.ml")
L2_TARGET_RELATIVE = Path("candle/flyspeck_l2_target.ml")
LINKED_RECORD_RELATIVE = Path("candle/build/cakeml-build-provenance.json")
NORMALIZATION_RECEIPT = "flyspeck_normalization_receipt.json"
GENERATED_RECEIPT = "flyspeck_lp_archive_receipt.json"
CHUNK_BYTES = 1024 * 1024
GIB = 1024 * 1024 * 1024
ACTION_PREFIX = "CANDLE_FLYSPECK_STRATUM_ACTION_OK"
ACTION_OUTCOMES = ("load", "skip-ledger")
SOURCE_CLOSURE_PREFIX = "CANDLE_FLYSPECK_LOGICAL_SOURCE_V3"
SOURCE_CLOSURE_SUCCESS_MARKER = "CANDLE_FLYSPECK_LOGICAL_SOURCE_CLOSURE_V3_OK"
SOURCE_CLOSURE_POLICY = "manifest-selected-nested-logical-reachability-v3"
SOURCE_CLOSURE_ORDER = "canonical-source-key-lexicographic-v1"
SOURCE_CLOSURE_OBSERVATION = (
    "outer-and-selected-loadt-ledger-observed-other-nested-expected"
)
SOURCE_TRACE_PREFIX = "CANDLE_FLYSPECK_SOURCE_TRACE_V1"
SOURCE_TRACE_PROTOCOL = "candle-loader-owned-source-trace-v1"
SOURCE_TRACE_ACTIVATION = (
    "runtime-config-is-authenticated-pre-trace-enabler; every later source "
    "directive is required in one closed loader-owned session"
)
SOURCE_TRACE_KINDS = (
    "#flyspeck_needs", "#flyspeck_loadt", "#use", "needs", "loads",
)
SOURCE_TRACE_NEED_KINDS = ("#flyspeck_needs", "needs")
SOURCE_TRACE_LOAD_KINDS = ("#flyspeck_loadt", "loads")
SOURCE_TRACE_TOP_LEVEL_CONTROLS = (
    "control:runtime-setup",
    "control:instrumented-prefix",
    "control:stratum-check",
    "control:postlude",
)
DIRECT_EVIDENCE_CLAIM = (
    "compiled cumulative source-action attempt; not S2/S3 without semantic "
    "fingerprints"
)
DIRECT_V5_EVIDENCE_CLAIM = (
    "compiled cumulative source-action and semantic observation attempt; "
    "not S2/S3 without independent approval"
)
DIRECT_ATTEMPT_FIELDS = frozenset({
    "schema", "kind", "claim", "state", "started_utc", "boundary_id",
    "diagnostic_only", "attempt_nonce", "action_count",
    "ordered_expected_action_sha256", "expected_action_events",
    "timeout_seconds", "resource_limits", "fresh_process_replay_from_action_zero",
    "cooperative_build_run_lock_held", "runtime_lock",
    "concurrent_mutation_model", "process_state_checkpoint", "evidence_contract",
    "expected_logical_source_closure", "expected_physical_source_trace",
    "runtime_environment_policy", "runtime_environment", "inputs", "repositories",
})
DIRECT_RECEIPT_ONLY_FIELDS = frozenset({
    "finished_utc", "timed_out", "exit_code", "command", "child_resources",
    "log", "initial_attempt", "action_markers_validated", "action_events",
    "logical_source_closure", "physical_source_trace", "semantic_fingerprints",
    "s2_s3_evidence", "validation_error", "postflight_reauthenticated",
})
DIRECT_V5_ATTEMPT_FIELDS = DIRECT_ATTEMPT_FIELDS | frozenset({
    "semantic_evidence_plan",
})
DIRECT_V5_RECEIPT_ONLY_FIELDS = DIRECT_RECEIPT_ONLY_FIELDS | frozenset({
    "dependency_history", "semantic_coverage",
})
DIRECT_INPUT_FIELDS = frozenset({
    "plan", "host_materialization", "manifest", "linked_provenance",
    "archived_linked_provenance", "archived_bootstrap_provenance",
    "archived_bootstrap_log", "runtime_snapshot", "runtime_executable",
    "controller_execution", "authenticated_prefix", "instrumented_prefix",
    "runtime_config", "stdin", "postlude", "setup", "check",
    "fingerprint_serializer", "l2_target",
})
SOURCE_CLOSURE_CLASSIFICATIONS = (
    "observed-outer-source",
    "observed-nested-source",
    "expected-nested-source",
    "generated-executed-control",
    "derivation-only-input",
)
SOURCE_CLOSURE_HARNESS_KEYS = (
    "candle:candle/flyspeck_source_integrity.ml",
    "candle:candle/flyspeck_full_build.ml",
)
SOURCE_CLOSURE_DERIVATION_KEY = "candle:candle/flyspeck_full_build.ml"
SOURCE_CLOSURE_GENERATED_KEYS = (
    "candle:candle/build/insulate.ml",
    "candle:candle/flyspeck_source_digests.ml",
)
SOURCE_CLOSURE_FINAL_KEY = "candle:candle/flyspeck_l2_target.ml"
SOURCE_CLOSURE_EXCLUDED_LOADER = "candle:candle/flyspeck_loader.ml"
SOURCE_ALIAS_POLICY = (
    "resolve each authenticated lexical alias to its manifest-selected "
    "canonical source before normalization, logical identity lookup, "
    "and physical loader-cache lookup"
)
SOURCE_ALIAS_LOAD_PATH_ORDER = (
    "flyspeck:text_formalization/../jHOLLight/",
    "flyspeck:text_formalization/../formal_ineqs",
    "flyspeck:jHOLLight",
    "flyspeck:formal_ineqs",
    "flyspeck:text_formalization",
    "candle:.",
)
STRICTBUILD_SOURCE_KEY = "flyspeck:text_formalization/build/strictbuild.hl"
STRICTBUILD_SERIALIZATION_OPT_IN_KEY = (
    "flyspeck:text_formalization/build/use_serialization.hl"
)
SERIALIZATION_SOURCE_KEY = "flyspeck:text_formalization/general/serialization.hl"
STRICTBUILD_NORMALIZATION_ID = "PROJECT-TOPLOOP-S3-USE-FILE-B-001"
STRICTBUILD_FAIL_CLOSED_NEEDS_OPERATION = (
    "PROJECT-TOPLOOP-S3-USE-FILE-B-001-NEEDS-FAIL-CLOSED"
)
SERIALIZATION_STATIC_BRANCH_OPERATION = (
    "PROJECT-TOPLOOP-S3-UPDATE-DATABASE-001-STATIC-LOAD"
)
NON_SOURCE_DEPENDENCY_STATUSES = {
    "function-alias", "generated-contract", "generated-runtime",
    "loader-definition", "root-driver", "runtime-library",
}
PREFLIGHT_MARKER = "CANDLE_FLYSPECK_STRATUM_PREFLIGHT_OK"
SUCCESS_MARKER = "CANDLE_FLYSPECK_STRATUM_BOUNDARY_OK"
FINGERPRINT_MARKER = reference_protocol.FINGERPRINT_MARKER
STATE_FINGERPRINT_MARKER = reference_protocol.STATE_FINGERPRINT_MARKER
FINGERPRINT_SUCCESS_MARKER = "CANDLE_FLYSPECK_STRATUM_FINGERPRINTS_OK"
DEPENDENCY_HISTORY_PREFIX = "CANDLE_FLYSPECK_DEPENDENCY_HISTORY_V1"
DEPENDENCY_HISTORY_SUCCESS_MARKER = (
    "CANDLE_FLYSPECK_DEPENDENCY_HISTORY_V1_OK"
)
DEPENDENCY_HISTORY_POLICY = (
    "serialization-full-digest-thm-sorted-dependency-history-v1"
)
SEMANTIC_COVERAGE_POLICY = (
    "authenticated-direct-source-lp-nonlinear-observation-v1"
)
SAFE_VALUE_PATH = re.compile(r"^[A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9_']*)*$")
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
        "policy": "ldd_roles_resolved_absolute_paths_and_content_v3",
        "dynamic_path_tags": {},
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
EXPECTED_CONTROLLER_TOOLS = {
    "git": {
        "invocation_path": "/usr/bin/git",
        "resolved_path": "/usr/bin/git",
        "symlink_target": None,
        "bytes": 4066232,
        "sha256":
            "2a8c18fbf43da9f692d75474c72bea9dfd796c260b0f3dfe456376abc3bbd668",
    },
    "ldd": {
        "invocation_path": "/usr/bin/ldd",
        "resolved_path": "/usr/bin/ldd",
        "symlink_target": None,
        "bytes": 5382,
        "sha256":
            "4f1d37e25f27535e3f02a5b7da63e1ce18d4982445db2c25fc8f985a3d395cc3",
    },
    "patch": {
        "invocation_path": "/usr/bin/patch",
        "resolved_path": "/usr/bin/patch",
        "symlink_target": None,
        "bytes": 186896,
        "sha256":
            "a7ae8b838a75711c06f86a2a8293dcad85a20b564670a120717e704c436e6f3a",
    },
    "readelf": {
        "invocation_path": "/usr/bin/readelf",
        "resolved_path": "/usr/bin/x86_64-linux-gnu-readelf",
        "symlink_target": "x86_64-linux-gnu-readelf",
        "bytes": 789280,
        "sha256":
            "871be389739ecf9924b052c2fde4d2a2068a54e882201b9c34897337a5a0a130",
    },
}


class ContractError(ValueError):
    """An authenticated runtime input or execution invariant did not match."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ContractError(message)


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def exact_json_equal(left: object, right: object) -> bool:
    """Compare JSON values without Python's bool/int/float coercions."""
    if type(left) is not type(right):
        return False
    if isinstance(left, dict):
        return set(left) == set(right) and all(
            exact_json_equal(left[key], right[key]) for key in left
        )
    if isinstance(left, list):
        return len(left) == len(right) and all(
            exact_json_equal(a, b) for a, b in zip(left, right, strict=True)
        )
    return left == right


def exact_absolute_path(value: object) -> bool:
    """Recognize one normalized lexical absolute path without parent hops."""
    if not isinstance(value, str) or not value:
        return False
    path = Path(value)
    return (value.startswith("/") and not value.startswith("//") and
            path.is_absolute() and ".." not in path.parts and
            str(path) == value)


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def atomic_write_json(path: Path, value: Any) -> None:
    temporary = path.with_name(f"{path.name}.tmp.{os.getpid()}")
    temporary.write_bytes(json_bytes(value))
    os.replace(temporary, path)


def hash_file(path: Path) -> dict[str, Any]:
    sha256 = hashlib.sha256()
    md5 = hashlib.md5(usedforsecurity=False)
    size = 0
    with path.open("rb") as source:
        while block := source.read(CHUNK_BYTES):
            size += len(block)
            sha256.update(block)
            md5.update(block)
    return {"bytes": size, "sha256": sha256.hexdigest(), "md5": md5.hexdigest()}


def data_record(value: bytes) -> dict[str, Any]:
    return {
        "bytes": len(value),
        "sha256": hashlib.sha256(value).hexdigest(),
        "md5": hashlib.md5(value, usedforsecurity=False).hexdigest(),
    }


def local_python_modules() -> tuple[types.ModuleType, ...]:
    return (
        cakeml_artifact_provenance,
        cakeml_bootstrap_transition,
        flyspeck_stratum_plan,
        reference_protocol,
        runtime_lock,
    )


def validate_python_runtime() -> dict[str, Any]:
    """Bind the host controller to the pinned executing Python image."""
    cakeml_artifact_provenance.validate_elf_closure_record(
        EXPECTED_PYTHON_RUNTIME["elf_closure"], "pinned Python runtime",
        allowed_dynamic_path_tags={},
    )
    process_executable = Path("/proc/self/exe")
    require(process_executable.is_symlink(),
            "cannot bind the executing Python image through /proc/self/exe")
    executable = process_executable.resolve(strict=True)
    require(Path(sys.executable).resolve(strict=True) == executable,
            "Python executable metadata differs from the running image")
    executable_record = hash_file(executable)
    observed = {
        "execution_binding": "/proc/self/exe",
        "version": sys.version,
        "executable": {
            "path": str(executable),
            "bytes": executable_record["bytes"],
            "sha256": executable_record["sha256"],
        },
        "elf_closure":
            cakeml_artifact_provenance.elf_dynamic_closure(executable),
    }
    require(observed == EXPECTED_PYTHON_RUNTIME,
            "stratum-controller Python runtime identity mismatch")
    return observed


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
    source = Path(__file__).resolve()
    argv0 = Path(sys.argv[0]).resolve()
    require(source.name == "flyspeck_stratum_runtime.py" and
            RUNNER_SOURCE_BYTES.startswith(b"#!/usr/bin/env python3\n"),
            "stratum runner is not a direct Python source file")
    try:
        compile(RUNNER_SOURCE_BYTES, str(source), "exec", dont_inherit=True)
    except (SyntaxError, UnicodeError, ValueError) as error:
        raise ContractError(
            "stratum runner startup bytes are not Python source"
        ) from error
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
    }, "stratum runner must execute directly from its .py source")
    require(python_startup_flags() == EXPECTED_PYTHON_STARTUP_FLAGS,
            "stratum runner Python startup flags mismatch")
    require(python_startup_options() == EXPECTED_PYTHON_STARTUP_OPTIONS,
            "stratum runner Python startup options mismatch")
    return record


def validate_controller_tools() -> dict[str, dict[str, Any]]:
    """Bind the four fixed external programs used by controller validation."""
    observed = {}
    for label, expected in sorted(EXPECTED_CONTROLLER_TOOLS.items()):
        invocation = Path(expected["invocation_path"])
        require(invocation.is_file(),
                f"missing controller host tool: {invocation}")
        if expected["symlink_target"] is None:
            require(not invocation.is_symlink(),
                    f"unexpected controller host-tool symlink: {invocation}")
            symlink_target = None
        else:
            require(invocation.is_symlink(),
                    f"missing controller host-tool symlink: {invocation}")
            symlink_target = os.readlink(invocation)
        resolved = invocation.resolve(strict=True)
        record = hash_file(resolved)
        candidate = {
            "invocation_path": str(invocation),
            "resolved_path": str(resolved),
            "symlink_target": symlink_target,
            "bytes": record["bytes"],
            "sha256": record["sha256"],
        }
        require(candidate == expected,
                f"controller host-tool identity mismatch: {label}")
        observed[label] = {**candidate, "md5": record["md5"]}
    return observed


def collect_controller_execution(candle_root: Path) -> dict[str, Any]:
    """Capture exact executed local sources and the pinned Python runtime."""
    direct_startup = require_direct_script_startup()
    expected_directory = candle_root / "candle"
    sources: dict[str, dict[str, Any]] = {}
    for module in local_python_modules():
        path = Path(module.__file__).resolve()
        label = path.name
        source = module.__candle_source_bytes__
        record = data_record(source)
        require(path == expected_directory / label,
                f"local Python source is outside the exact Candle root: {label}")
        require(module.__candle_source_sha256__ == record["sha256"],
                f"executed local Python source digest mismatch: {label}")
        require(hash_file(path) == record,
                f"executed local Python source changed after compilation: {label}")
        sources[label] = {
            "source_path": str(path),
            "execution_binding": "compiled-from-captured-source-bytes",
            "source_bytes": source,
            **record,
        }
    runner = Path(__file__).resolve()
    runner_record = data_record(RUNNER_SOURCE_BYTES)
    require(runner == expected_directory / runner.name,
            "top-level runner source is outside the exact Candle root")
    require(hash_file(runner) == runner_record,
            "top-level runner source changed after startup capture")
    sources[runner.name] = {
        "source_path": str(runner),
        "execution_binding": "startup-captured-after-initial-compilation",
        "source_bytes": RUNNER_SOURCE_BYTES,
        **runner_record,
    }
    require(set(sources) == {
        "cakeml_artifact_provenance.py",
        "cakeml_bootstrap_transition.py",
        "flyspeck_stratum_plan.py",
        "flyspeck_stratum_runtime.py",
        "reference_protocol.py",
        "runtime_lock.py",
    }, "unexpected local Python controller source set")
    return {
        "source_root": str(expected_directory),
        "direct_script_startup": direct_startup,
        "python_startup_flags": python_startup_flags(),
        "python_startup_options": python_startup_options(),
        "initial_top_level_compilation_in_host_trust_boundary": True,
        "local_sources": sources,
        "python_runtime": validate_python_runtime(),
        "host_tools": validate_controller_tools(),
        "git_environment": cakeml_artifact_provenance.git_environment(),
    }


def validate_controller_execution(
    expected: dict[str, Any], candle_root: Path, candle_commit: str,
) -> None:
    observed = collect_controller_execution(candle_root)
    bind_controller_sources_to_commit(observed, candle_root, candle_commit)
    require(observed == expected,
            "stratum-controller execution identity changed during attempt")


def load_object(path: Path, label: str) -> dict[str, Any]:
    require(path.is_file() and not path.is_symlink(), f"missing ordinary {label}: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ContractError(f"cannot read {label} {path}: {error}") from error
    require(isinstance(value, dict), f"expected JSON object for {label}: {path}")
    return value


def git_output(root: Path, *arguments: str) -> str:
    try:
        return subprocess.run(
            cakeml_artifact_provenance.git_command(root, *arguments), check=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            env=cakeml_artifact_provenance.git_environment(),
        ).stdout.strip()
    except subprocess.CalledProcessError as error:
        raise ContractError(f"git check failed for {root}: {error.stderr.strip()}") from error


def git_bytes(root: Path, *arguments: str) -> bytes:
    try:
        return subprocess.run(
            cakeml_artifact_provenance.git_command(root, *arguments), check=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=cakeml_artifact_provenance.git_environment(),
        ).stdout
    except subprocess.CalledProcessError as error:
        raise ContractError(
            f"git byte check failed for {root}: " +
            error.stderr.decode(errors="replace").strip()
        ) from error


def bind_controller_sources_to_commit(
    controller: dict[str, Any], candle_root: Path, commit: str,
) -> dict[str, Any]:
    """Require captured controller bytes to be exact blobs of the linked commit."""
    records = {}
    for label, source in sorted(controller["local_sources"].items()):
        relative = f"candle/{label}"
        index = git_output(candle_root, "ls-files", "-v", "--", relative)
        require(index == f"H {relative}",
                f"controller source has special or missing index flags: {relative}")
        blob = git_bytes(candle_root, "cat-file", "blob", f"{commit}:{relative}")
        require(blob == source["source_bytes"],
                f"executed controller source differs from linked commit: {relative}")
        records[label] = {
            "repository_path": relative,
            "index_tag": "H",
            **data_record(blob),
        }
    binding = {
        "candle_commit": commit,
        "sources": records,
    }
    controller["commit_binding"] = binding
    return binding


def validate_clean_exact(root: Path, head: str, label: str) -> None:
    require(git_output(root, "rev-parse", "HEAD") == head, f"{label} revision mismatch")
    require(not git_output(root, "status", "--porcelain", "--untracked-files=all"),
            f"{label} root is not clean")


def validate_file(path: Path, record: dict[str, Any], label: str) -> dict[str, Any]:
    require(path.is_file() and not path.is_symlink(), f"missing ordinary {label}: {path}")
    observed = hash_file(path)
    for field in ("bytes", "sha256", "md5"):
        if field in record:
            require(observed[field] == record[field], f"{label} {field} mismatch: {path}")
    return observed


def resolve_source(binding: dict[str, Any], candle_root: Path, flyspeck_root: Path) -> Path:
    repository = binding.get("repository")
    require(repository in ("candle", "flyspeck"), "unknown source repository")
    root = candle_root if repository == "candle" else flyspeck_root
    return root / binding["path"]


def loader_filename_concat(directory: Path | str, filename: str) -> str:
    """Mirror Candle's lexical Filename.concat without normalizing separators."""
    directory_string = str(directory)
    require(isinstance(filename, str) and filename,
            "malformed loader filename")
    return filename if directory_string == "." else directory_string + "/" + filename


def derive_source_alias_contract(
    manifest: dict[str, Any], candle_root: Path, flyspeck_root: Path,
) -> dict[str, Any]:
    """Reconstruct alias provenance from the independently recorded load graph."""
    require(manifest.get("load_path_order") == list(SOURCE_ALIAS_LOAD_PATH_ORDER),
            "source alias load-path order mismatch")
    text_root = loader_filename_concat(flyspeck_root, "text_formalization")
    search_roots = (
        ("flyspeck", "text_formalization/../jHOLLight/",
         loader_filename_concat(text_root, "../jHOLLight/")),
        ("flyspeck", "text_formalization/../formal_ineqs",
         loader_filename_concat(text_root, "../formal_ineqs")),
        ("flyspeck", "jHOLLight",
         loader_filename_concat(flyspeck_root, "jHOLLight")),
        ("flyspeck", "formal_ineqs",
         loader_filename_concat(flyspeck_root, "formal_ineqs")),
        ("flyspeck", "text_formalization", text_root),
        ("candle", "", str(candle_root)),
    )

    def selected_lookup(target: Any, selected: Any) -> dict[str, Any]:
        require(isinstance(target, str) and target and
                not os.path.isabs(target) and isinstance(selected, str),
                "malformed source alias selection")
        for search_root_index, (repository, prefix, root) in enumerate(search_roots):
            lexical = loader_filename_concat(root, target)
            if not os.path.isfile(lexical):
                continue
            resolved = Path(lexical).resolve(strict=True)
            observed_repository = ""
            observed_relative: Path | None = None
            for candidate_repository, candidate_root in (
                ("candle", candle_root), ("flyspeck", flyspeck_root),
            ):
                try:
                    observed_relative = resolved.relative_to(candidate_root)
                    observed_repository = candidate_repository
                    break
                except ValueError:
                    pass
            require(observed_relative is not None,
                    "source alias selection escapes pinned repositories")
            observed = f"{observed_repository}:{observed_relative.as_posix()}"
            require(observed == selected,
                    "source alias first lexical selection mismatch")
            return {
                "target": target,
                "search_root_index": search_root_index,
                "alias_repository": repository,
                "alias_path": (
                    target if not prefix else
                    loader_filename_concat(prefix, target)
                ),
                "selected": selected,
                "canonical_repository": observed_repository,
                "canonical_path": observed_relative.as_posix(),
            }
        raise ContractError(f"source alias target no longer resolves: {target}")

    occurrences: list[dict[str, Any]] = []
    action_roots = manifest.get("build_sequence_roots")
    require(isinstance(action_roots, list),
            "missing source alias build-sequence provenance")
    for action_index, root in enumerate(action_roots):
        require(isinstance(root, dict) and root.get("index") == action_index and
                root.get("status") in {"resolved", "ambiguous"},
                "malformed source alias build-sequence provenance")
        occurrences.append({
            "kind": "build-sequence-root",
            "action_index": action_index,
            "lookup": selected_lookup(root.get("target"), root.get("selected")),
        })

    nodes = manifest.get("source_nodes")
    require(isinstance(nodes, dict) and
            all(isinstance(key, str) and isinstance(node, dict)
                for key, node in nodes.items()),
            "missing source alias graph provenance")
    for parent_source, node in nodes.items():
        dependencies = node.get("dependencies")
        require(isinstance(dependencies, list) and
                all(isinstance(dependency, dict) for dependency in dependencies),
                "malformed source alias graph provenance")
        for dependency in dependencies:
            kind = dependency.get("kind")
            line = dependency.get("line")
            require(isinstance(kind, str) and type(line) is int and line > 0,
                    "malformed source alias dependency provenance")
            selected_targets = dependency.get("selected_targets")
            if selected_targets is not None:
                targets = dependency.get("targets")
                require(dependency.get("status") == "resolved-dynamic" and
                        isinstance(targets, list) and
                        isinstance(selected_targets, list) and targets and
                        len(targets) == len(selected_targets),
                        "malformed reviewed dynamic source alias provenance")
                for target, selected in zip(targets, selected_targets, strict=True):
                    occurrences.append({
                        "kind": "reviewed-dynamic-source-action",
                        "parent_source": parent_source,
                        "line": line,
                        "action_kind": kind,
                        "lookup": selected_lookup(target, selected),
                    })
            elif dependency.get("status") in {"resolved", "ambiguous"}:
                occurrences.append({
                    "kind": "literal-source-action",
                    "parent_source": parent_source,
                    "line": line,
                    "action_kind": kind,
                    "lookup": selected_lookup(
                        dependency.get("literal"), dependency.get("selected"),
                    ),
                })

    grouped: dict[tuple[str, str], dict[str, Any]] = {}
    for occurrence in occurrences:
        lookup = occurrence["lookup"]
        alias_key = (lookup["alias_repository"], lookup["alias_path"])
        canonical_key = (
            lookup["canonical_repository"], lookup["canonical_path"],
        )
        if alias_key == canonical_key:
            continue
        use = {key: value for key, value in occurrence.items() if key != "lookup"}
        prior = grouped.get(alias_key)
        if prior is None:
            grouped[alias_key] = {**lookup, "uses": [use]}
        else:
            require(all(prior[field] == lookup[field] for field in (
                "target", "search_root_index", "selected",
                "canonical_repository", "canonical_path",
            )), "source alias has conflicting derived selections")
            prior["uses"].append(use)
    records = []
    for alias_key in sorted(grouped):
        record = grouped[alias_key]
        uses = sorted(
            record.pop("uses"),
            key=lambda use: json.dumps(use, sort_keys=True, separators=(",", ":")),
        )
        records.append({**record, "occurrence_count": len(uses), "uses": uses})
    return {
        "schema": 1,
        "policy": SOURCE_ALIAS_POLICY,
        "record_count": len(records),
        "occurrence_count": sum(record["occurrence_count"] for record in records),
        "records": records,
    }


def validate_source_alias_contract(
    manifest: dict[str, Any], source_by_key: dict[str, dict[str, Any]],
    candle_root: Path, flyspeck_root: Path,
) -> list[dict[str, str]]:
    """Bind every lexical loader alias to one authenticated canonical source."""
    alias_contract = manifest.get("source_alias_contract")
    expected_contract = derive_source_alias_contract(
        manifest, candle_root, flyspeck_root,
    )
    require(isinstance(alias_contract, dict) and
            canonical_bytes(alias_contract) == canonical_bytes(expected_contract),
            "source alias contract differs from derived provenance closure")
    alias_records = expected_contract["records"]
    source_alias_runtime: list[dict[str, str]] = []
    seen_aliases: set[tuple[str, str]] = set()
    for record in alias_records:
        alias_repository = record.get("alias_repository")
        canonical_repository = record.get("canonical_repository")
        alias_value = record.get("alias_path")
        canonical_value = record.get("canonical_path")
        require(alias_repository in {"candle", "flyspeck"} and
                canonical_repository in {"candle", "flyspeck"} and
                isinstance(alias_value, str) and
                isinstance(canonical_value, str),
                "malformed source alias path binding")
        alias_relative = Path(alias_value)
        canonical_relative = safe_relative(
            canonical_value, "canonical source alias",
        )
        require(not alias_relative.is_absolute() and
                alias_relative.parts and
                all(part not in {"", "."} for part in alias_relative.parts) and
                ".." in alias_relative.parts,
                f"source alias is not an explicit lexical alias: {alias_value}")
        alias_key = (alias_repository, alias_value)
        require(alias_key not in seen_aliases, "duplicate source alias record")
        seen_aliases.add(alias_key)
        selected = record.get("selected")
        require(selected == f"{canonical_repository}:{canonical_value}" and
                selected in source_by_key,
                "source alias canonical selection is unbound")
        alias_root = candle_root if alias_repository == "candle" else flyspeck_root
        canonical_root = (
            candle_root if canonical_repository == "candle" else flyspeck_root
        )
        alias_path = loader_filename_concat(alias_root, alias_value)
        canonical_path = canonical_root / canonical_relative
        require(os.path.isfile(alias_path) and not os.path.islink(alias_path) and
                Path(alias_path).resolve(strict=True) ==
                canonical_path.resolve(strict=True),
                f"source alias no longer selects canonical source: {alias_value}")
        source_alias_runtime.append({
            "source_key": selected,
            "alias_repository": alias_repository,
            "alias_relative": alias_value,
            "canonical_repository": canonical_repository,
            "canonical_relative": canonical_value,
            "alias": alias_path,
            "canonical": str(canonical_path),
        })
    require(len(source_alias_runtime) == expected_contract["record_count"],
            "source alias runtime closure mismatch")
    return source_alias_runtime


def order_lp_certificate_runtime(
    generated_runtime: list[dict[str, Any]],
    expected_basenames: Any,
) -> list[dict[str, Any]]:
    require(
        isinstance(expected_basenames, list)
        and len(expected_basenames) == 39
        and all(isinstance(name, str) and name for name in expected_basenames)
        and len(set(expected_basenames)) == len(expected_basenames),
        "invalid LP certificate basename contract",
    )
    certificate_by_basename: dict[str, dict[str, Any]] = {}
    for item in generated_runtime:
        if item["class"] not in ("lp-certificate", "lp-certificate-prepared"):
            continue
        basename = Path(item["relative"]).name
        require(basename not in certificate_by_basename,
                f"duplicate LP certificate basename: {basename}")
        certificate_by_basename[basename] = item
    require(set(certificate_by_basename) == set(expected_basenames),
            "LP certificate basename set mismatch")
    return [certificate_by_basename[name] for name in expected_basenames]


def validate_plan(
    candle_root: Path,
    linked_record: dict[str, Any],
    plan_root: Path,
    boundary_id: str,
) -> dict[str, Any]:
    """Reauthenticate a host plan and return exact runtime material."""
    require(plan_root.is_dir() and not plan_root.is_symlink(),
            f"missing ordinary stratum plan root: {plan_root}")
    plan_root_status = os.stat(plan_root, follow_symlinks=False)
    require(
        (plan_root_status.st_mode & 0o170000) == 0o040000
        and plan_root_status.st_mode & 0o777
        == flyspeck_stratum_plan.PLAN_ROOT_MODE,
        f"stratum plan root mode mismatch: {plan_root}",
    )
    plan_path = plan_root / "plan.json"
    schedule_path = plan_root / "host-schedule-template.json"
    materialization_path = plan_root / flyspeck_stratum_plan.HOST_MATERIALIZATION
    for path, label in (
        (plan_path, "stratum plan"),
        (schedule_path, "host schedule template"),
        (materialization_path, "host materialization"),
    ):
        observed = os.stat(path, follow_symlinks=False)
        require(
            not path.is_symlink() and (observed.st_mode & 0o170000) == 0o100000,
            f"missing ordinary {label}: {path}",
        )
        require(observed.st_mode & 0o777 == flyspeck_stratum_plan.PLAN_FILE_MODE,
                f"{label} mode mismatch: {path}")
    plan = load_object(plan_path, "stratum plan")
    schedule = load_object(schedule_path, "host schedule template")
    materialization = load_object(materialization_path, "host materialization")
    require(plan.get("schema") == 1, "unsupported stratum plan schema")
    require(plan.get("kind") == "candle-flyspeck-cumulative-stratum-plan",
            "wrong stratum plan kind")
    require("not Candle execution" in plan.get("claim", ""), "stratum plan claim drift")
    plan_hash = hash_file(plan_path)
    require(materialization.get("schema") == 2, "unsupported materialization schema")
    require(materialization.get("plan_sha256") == plan_hash["sha256"],
            "materialization plan digest mismatch")

    roots = materialization.get("host_roots")
    require(isinstance(roots, dict), "missing materialized host roots")
    require(Path(roots.get("candle", "")).resolve() == candle_root,
            "materialized Candle root mismatch")
    flyspeck_root = Path(roots.get("flyspeck", "")).resolve()
    overlay_root = Path(roots.get("normalization_overlay", "")).resolve()
    generated_root = Path(roots.get("generated_inputs", "")).resolve()

    repositories = plan.get("repositories")
    require(isinstance(repositories, dict), "missing plan repository bindings")
    candle_head = repositories.get("candle_materialization_head")
    require(isinstance(candle_head, str), "missing materialized Candle head")
    validate_clean_exact(candle_root, candle_head, "Candle")
    require(candle_head == linked_record.get("candle_commit"),
            "linked executable does not bind the current Candle head")
    validate_clean_exact(flyspeck_root, repositories["flyspeck_commit"], "Flyspeck")

    # Do not trust a self-consistent plan.  Reconstruct its complete semantic
    # projection from the pinned manifest and full driver, revalidate all host
    # roots, then require exact object and prefix equality.
    expected_base = repositories.get("candle_integration_base")
    require(isinstance(expected_base, str), "missing Candle integration base")
    derived_audit = flyspeck_stratum_plan.audit_manifest(candle_root)
    derived_validated = flyspeck_stratum_plan.validate_inputs(
        candle_root, expected_base, flyspeck_root, overlay_root,
        generated_root, derived_audit,
    )
    derived_plan, derived_prefixes = flyspeck_stratum_plan.make_plan(
        expected_base, derived_audit, derived_validated,
    )
    require(plan == derived_plan,
            "stored stratum plan differs from independently reconstructed plan")
    expected_schedule = flyspeck_stratum_plan.make_host_schedule(
        derived_plan, plan_hash["sha256"],
    )
    require(schedule == expected_schedule,
            "stored host schedule differs from independent reconstruction")
    expected_materialization = flyspeck_stratum_plan.make_host_materialization(
        plan_hash["sha256"],
        hash_file(candle_root / "candle/flyspeck_stratum_plan.py")["sha256"],
        candle_root, flyspeck_root, overlay_root, generated_root,
        derived_validated, derived_audit, derived_plan,
    )
    require(materialization == expected_materialization,
            "stored host materialization differs from independent reconstruction")
    expected_plan_files = {
        filename: flyspeck_stratum_plan.PLAN_FILE_MODE
        for filename in derived_prefixes
    }
    expected_plan_files.update({
        "plan.json": flyspeck_stratum_plan.PLAN_FILE_MODE,
        "host-schedule-template.json": flyspeck_stratum_plan.PLAN_FILE_MODE,
        flyspeck_stratum_plan.HOST_MATERIALIZATION:
            flyspeck_stratum_plan.PLAN_FILE_MODE,
    })
    flyspeck_stratum_plan.validate_materialized_tree(
        plan_root, expected_plan_files, "stratum plan",
    )
    for filename, content in derived_prefixes.items():
        relative = Path(filename)
        require(not relative.is_absolute() and ".." not in relative.parts,
                f"unsafe derived prefix path: {filename}")
        path = plan_root / relative
        require(path.is_file() and not path.is_symlink(),
                f"missing ordinary derived prefix: {path}")
        require(path.read_bytes() == content, f"derived prefix bytes mismatch: {filename}")

    manifest_path = candle_root / MANIFEST_RELATIVE
    manifest = load_object(manifest_path, "Flyspeck manifest")
    require(hash_file(manifest_path)["sha256"] == plan.get("manifest_sha256"),
            "runtime manifest digest mismatch")
    require(manifest["repositories"]["flyspeck"]["commit"] == repositories["flyspeck_commit"],
            "runtime manifest Flyspeck pin mismatch")

    source_graph = plan.get("source_graph")
    require(isinstance(source_graph, dict), "missing source graph")
    source_bindings = source_graph.get("bindings")
    require(isinstance(source_bindings, list), "missing source bindings")
    require(source_graph.get("entry_count") == len(source_bindings) == 400,
            "source binding count mismatch")
    require(canonical_sha256(source_bindings) == source_graph.get("ordered_binding_sha256"),
            "source binding order digest mismatch")
    source_by_key: dict[str, dict[str, Any]] = {}
    source_runtime: list[dict[str, Any]] = []
    for binding in source_bindings:
        key = binding.get("key")
        require(isinstance(key, str) and key not in source_by_key, "duplicate source binding")
        source_path = resolve_source(binding, candle_root, flyspeck_root)
        validate_file(source_path, binding,
                      f"source binding {key}")
        source_by_key[key] = binding
        source_runtime.append({**binding, "absolute": str(source_path)})

    source_alias_runtime = validate_source_alias_contract(
        manifest, source_by_key, candle_root, flyspeck_root,
    )

    digest_contract = manifest.get("source_digest_contract")
    require(isinstance(digest_contract, dict), "missing source digest contract")
    require(digest_contract.get("entry_count") == 399, "source digest count drift")
    source_digest_record = validate_file(candle_root / SOURCE_DIGEST_RELATIVE, {
        "sha256": digest_contract["generated_source_sha256"],
        "md5": digest_contract["generated_source_md5"],
    }, "source digest program")
    harness_records = {
        SOURCE_DIGEST_RELATIVE.as_posix(): source_digest_record,
    }
    for relative in (SETUP_RELATIVE, CHECK_RELATIVE, FINGERPRINT_RELATIVE,
                     L2_TARGET_RELATIVE):
        harness_records[relative.as_posix()] = hash_file(candle_root / relative)

    normalization = plan.get("normalization_overlay")
    require(isinstance(normalization, dict), "missing normalization overlay")
    normalization_bindings = normalization.get("bindings")
    require(isinstance(normalization_bindings, list), "missing normalization bindings")
    source_graph = plan.get("source_graph")
    require(isinstance(source_graph, dict), "missing plan source graph")
    source_graph_bindings = source_graph.get("bindings")
    require(isinstance(source_graph_bindings, list),
            "missing plan source graph bindings")
    expected_normalizations = sum(
        isinstance(binding.get("execution_normalization"), dict)
        for binding in source_graph_bindings
    )
    require(expected_normalizations > 0, "empty normalization contract")
    require(
        normalization.get("entry_count") == len(normalization_bindings)
        == expected_normalizations,
            "normalization binding count mismatch")
    require(canonical_sha256(normalization_bindings) == normalization.get("ordered_binding_sha256"),
            "normalization binding order digest mismatch")
    normalized_runtime: list[dict[str, str]] = []
    for binding in normalization_bindings:
        source_key = binding.get("source_key")
        require(source_key in source_by_key, "normalization source key is unbound")
        source = resolve_source(source_by_key[source_key], candle_root, flyspeck_root)
        output = overlay_root / binding["path"]
        validate_file(output, {
            "bytes": binding["normalized_bytes"],
            "sha256": binding["normalized_sha256"],
            "md5": binding["normalized_md5"],
        }, f"normalized source {binding['path']}")
        normalized_runtime.append({
            "source_key": source_key,
            "normalization_id": binding["id"],
            "relative": binding["path"],
            "original_relative": source_by_key[source_key]["path"],
            "original": str(source), "output": str(output),
            "bytes": binding["normalized_bytes"],
            "sha256": binding["normalized_sha256"],
            "md5": binding["normalized_md5"],
        })
    validate_file(overlay_root / NORMALIZATION_RECEIPT, {
        "sha256": normalization["receipt_sha256"],
    }, "normalization receipt")

    generated = plan.get("generated_inputs")
    require(isinstance(generated, dict), "missing generated inputs")
    generated_bindings = generated.get("bindings")
    require(isinstance(generated_bindings, list), "missing generated-input bindings")
    require(generated.get("entry_count") == len(generated_bindings) == 43,
            "generated-input binding count mismatch")
    require(canonical_sha256(generated_bindings) == generated.get("ordered_binding_sha256"),
            "generated-input binding order digest mismatch")
    generated_runtime: list[dict[str, str]] = []
    for binding in generated_bindings:
        root = generated_root if binding["class"] == "lp-certificate-prepared" else flyspeck_root
        source = root / binding["path"]
        observed = validate_file(source, binding, f"generated input {binding['path']}")
        generated_runtime.append({
            "class": binding["class"], "relative": binding["path"],
            "path": str(source), **observed,
        })
    validate_file(generated_root / GENERATED_RECEIPT, {
        "sha256": generated["receipt_sha256"],
    }, "generated-input receipt")
    expected_certificate_basenames = manifest["lp_archive_preparation_contract"][
        "runtime_certificate_basenames"
    ]
    lp_certificate_runtime = order_lp_certificate_runtime(
        generated_runtime, expected_certificate_basenames,
    )
    require(len(lp_certificate_runtime) == 39, "LP certificate runtime count mismatch")

    process_records = manifest["static_library_contract"]["binding_evidence"]["unix.cma"][
        "deterministic_process_inputs"
    ]
    require([entry.get("command") for entry in process_records] == ["date", "whoami"],
            "deterministic process-input order drift")
    process_runtime: list[dict[str, str]] = []
    for record in process_records:
        source_key = record.get("source", "")
        require(source_key.startswith("candle:"), "unexpected process-input root")
        source = candle_root / source_key.removeprefix("candle:")
        observed = validate_file(source, record, f"process input {record['command']}")
        process_runtime.append({
            "relative": source_key.removeprefix("candle:"),
            "path": str(source), **observed,
        })

    actions = plan.get("actions")
    require(isinstance(actions, list), "missing stratum actions")
    require(plan.get("action_count") == len(actions) == 297, "stratum action count mismatch")
    require(canonical_sha256(actions) == plan.get("ordered_action_sha256"),
            "ordered action digest mismatch")
    for index, action in enumerate(actions):
        require(action.get("index") == index, f"action index drift: {index}")
        require(action.get("selected_source") in source_by_key, f"unbound action source: {index}")

    boundaries = plan.get("boundaries")
    require(isinstance(boundaries, list) and len(boundaries) == 8, "boundary set mismatch")
    diagnostics = plan.get("diagnostic_cutpoints")
    require(isinstance(diagnostics, list) and len(diagnostics) == 2,
            "diagnostic cutpoint set mismatch")
    require(all(entry.get("diagnostic_only") is True for entry in diagnostics),
            "diagnostic cutpoint classification mismatch")
    selected = [
        entry for entry in boundaries + diagnostics
        if entry.get("boundary_id") == boundary_id
    ]
    require(len(selected) == 1, f"unknown or duplicate boundary: {boundary_id}")
    boundary = selected[0]
    count = boundary.get("completed_action_count")
    end = boundary.get("stratum_end_index")
    require(isinstance(count, int) and isinstance(end, int) and count == end + 1,
            "selected boundary count mismatch")
    require(canonical_sha256(actions[:count]) == boundary.get("cumulative_action_sha256"),
            "selected cumulative action digest mismatch")
    prefix_record = boundary.get("cumulative_prefix")
    require(isinstance(prefix_record, dict), "missing selected cumulative prefix")
    prefix_path = plan_root / prefix_record["path"]
    validate_file(prefix_path, prefix_record, "selected cumulative prefix")

    action_ledger_delta_keys = derive_action_ledger_delta_keys(manifest, count)
    action_runtime = []
    for action, delta_keys in zip(
        actions[:count], action_ledger_delta_keys, strict=True,
    ):
        source = source_by_key[action["selected_source"]]
        require(delta_keys[0] == action["selected_source"],
                f"action ledger outer source mismatch: {action['index']}")
        ledger_delta = []
        for delta_index, key in enumerate(delta_keys):
            delta_source = source_by_key.get(key)
            require(isinstance(delta_source, dict),
                    f"unbound action ledger source: {action['index']}:{key}")
            ledger_delta.append({
                "key": key,
                "classification": (
                    "observed-outer-source" if delta_index == 0 else
                    "observed-nested-source"
                ),
                "source_sha256": delta_source["sha256"],
                "identity_basename": Path(delta_source["path"]).name,
                "identity_md5": delta_source["md5"],
            })
        action_runtime.append({
            **action,
            "identity_basename": Path(source["path"]).name,
            "identity_md5": source["md5"],
            "logical_source_delta": ledger_delta,
            "logical_source_delta_sha256": canonical_sha256(ledger_delta),
        })
    linked_outputs = linked_record.get("outputs")
    require(isinstance(linked_outputs, dict) and
            isinstance(linked_outputs.get("insulate.ml"), dict),
            "missing linked insulate output")
    insulate_record = validate_file(
        candle_root / "candle/build/insulate.ml",
        linked_outputs["insulate.ml"], "linked insulate generated control",
    )
    logical_source_closure = derive_logical_source_closure(
        manifest, count, boundary_id.startswith("07-"), {
            "candle:candle/build/insulate.ml": insulate_record,
            "candle:candle/flyspeck_source_digests.ml": source_digest_record,
        },
    )

    return {
        "plan": plan,
        "plan_record": plan_hash,
        "materialization_record": hash_file(materialization_path),
        "manifest_record": hash_file(manifest_path),
        "linked_record": hash_file(candle_root / LINKED_RECORD_RELATIVE),
        "candle_head": candle_head,
        "flyspeck_root": flyspeck_root,
        "overlay_root": overlay_root,
        "generated_root": generated_root,
        "prefix_path": prefix_path,
        "prefix_record": prefix_record,
        "harness_records": harness_records,
        "boundary": boundary,
        "diagnostic_only": boundary.get("diagnostic_only") is True,
        "actions": action_runtime,
        "logical_source_closure": logical_source_closure,
        "source_runtime": source_runtime,
        "source_alias_runtime": source_alias_runtime,
        "normalized_runtime": normalized_runtime,
        "generated_runtime": generated_runtime,
        "lp_certificate_runtime": lp_certificate_runtime,
        "process_runtime": process_runtime,
    }


def ocaml_string(value: str) -> str:
    require(all(32 <= ord(char) < 127 for char in value), "unsafe non-ASCII runtime string")
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def instrument_prefix(prefix: bytes, actions: list[dict[str, Any]], nonce: str) -> bytes:
    """Insert one theorem-state-neutral ledger check after every exact action."""
    require(re.fullmatch(r"[0-9a-f]{32}", nonce) is not None,
            "attempt nonce must be 128-bit lowercase hex")
    try:
        lines = prefix.decode("utf-8").splitlines(keepends=True)
    except UnicodeDecodeError as error:
        raise ContractError("cumulative prefix is not UTF-8") from error
    output: list[str] = []
    action_index = 0
    for line in lines:
        output.append(line)
        if line.startswith("#flyspeck_needs "):
            require(action_index < len(actions), "prefix contains too many actions")
            expected = f"#flyspeck_needs {json.dumps(actions[action_index]['target'])};;"
            require(line.rstrip("\r\n") == expected, f"prefix directive drift: {action_index}")
            marker = (
                f"{ACTION_PREFIX} {nonce} {action_index:03d} "
                f"{actions[action_index]['source_sha256']} "
                f"{actions[action_index]['logical_source_delta_sha256']}"
            )
            identity = (
                f"({ocaml_string(actions[action_index]['identity_basename'])},"
                f"{ocaml_string(actions[action_index]['identity_md5'])})"
            )
            output.append(
                "candle_flyspeck_stratum_commit_action "
                f"{action_index} {identity} {ocaml_string(marker)};;\n"
            )
            action_index += 1
    require(action_index == len(actions), "prefix contains too few actions")
    return "".join(output).encode()


def selected_execution_edges(
    manifest: dict[str, Any], nodes: dict[str, Any],
) -> dict[str, Any]:
    """Authenticate normalization-selected edges that differ from raw syntax."""
    normalization_contract = manifest.get("source_normalization_contract")
    require(isinstance(normalization_contract, dict),
            "missing source normalization contract")
    normalization_entries = normalization_contract.get("entries")
    require(isinstance(normalization_entries, list),
            "missing source normalization entries")

    def exact_normalization(source_key: str, entry_id: str) -> dict[str, Any]:
        matches = [
            entry for entry in normalization_entries
            if isinstance(entry, dict) and entry.get("source_key") == source_key
        ]
        require(len(matches) == 1 and matches[0].get("id") == entry_id,
                f"missing selected execution normalization: {source_key}")
        node_normalization = nodes[source_key].get("execution_normalization")
        require(isinstance(node_normalization, dict) and
                node_normalization.get("id") == entry_id and
                node_normalization.get("operation_count") ==
                len(matches[0].get("operations", [])),
                f"source normalization summary mismatch: {source_key}")
        return matches[0]

    strictbuild_normalization = exact_normalization(
        STRICTBUILD_SOURCE_KEY, STRICTBUILD_NORMALIZATION_ID,
    )
    strictbuild_operations = {
        operation.get("id"): operation
        for operation in strictbuild_normalization.get("operations", [])
        if isinstance(operation, dict)
    }
    fail_closed_needs = strictbuild_operations.get(
        STRICTBUILD_FAIL_CLOSED_NEEDS_OPERATION
    )
    require(isinstance(fail_closed_needs, dict) and
            "dynamic strictbuild needs is disabled" in
            str(fail_closed_needs.get("after", "")),
            "strictbuild selected needs branch is not fail closed")

    interface_contract = manifest.get("toplevel_interface_contract")
    require(isinstance(interface_contract, dict),
            "missing selected branch contract")
    branch = interface_contract.get("conditional_source_selection")
    disposition = interface_contract.get("selected_execution_disposition")
    require(isinstance(branch, dict) and isinstance(disposition, dict) and
            branch.get("source") == SERIALIZATION_SOURCE_KEY and
            branch.get("pinned_ocaml_version") == "4.14.1" and
            disposition.get("serialization_branch_action") ==
            "PROJECT-MODULE-S3-SET-MAKE-001",
            "malformed serialization selected branch contract")
    selected = branch.get("selected")
    unselected = branch.get("unselected")
    require(isinstance(selected, str) and isinstance(unselected, str) and
            selected in nodes and unselected in nodes and
            disposition.get("unselected_original_source") == unselected,
            "unbound serialization branch selection")
    serialization_normalization = exact_normalization(
        SERIALIZATION_SOURCE_KEY,
        str(disposition["serialization_branch_action"]),
    )
    branch_operations = [
        operation for operation in serialization_normalization.get("operations", [])
        if isinstance(operation, dict) and
        operation.get("id") == SERIALIZATION_STATIC_BRANCH_OPERATION
    ]
    expected_directive = (
        '#flyspeck_loadt "' +
        selected.split(":", 1)[1].removeprefix("text_formalization/") +
        '";;'
    )
    require(len(branch_operations) == 1 and
            branch_operations[0].get("after") == expected_directive and
            unselected.split(":", 1)[1].removeprefix("text_formalization/")
            not in expected_directive,
            "serialization static branch operation mismatch")
    return {
        "serialization_selected": selected,
        "serialization_unselected": unselected,
        "nested_loadt_by_outer": {SERIALIZATION_SOURCE_KEY: [selected]},
    }


def derive_action_ledger_delta_keys(
    manifest: dict[str, Any], completed_action_count: int,
) -> list[list[str]]:
    """Return exact post-action logical-ledger prefixes in head-first order."""
    nodes = manifest.get("source_nodes")
    action_roots = manifest.get("build_sequence_roots")
    require(isinstance(nodes, dict) and nodes and
            isinstance(action_roots, list) and
            0 <= completed_action_count <= len(action_roots),
            "malformed action-ledger inputs")
    execution = selected_execution_edges(manifest, nodes)
    nested_by_outer = execution["nested_loadt_by_outer"]
    deltas: list[list[str]] = []
    for index, root in enumerate(action_roots[:completed_action_count]):
        require(isinstance(root, dict) and root.get("index") == index and
                root.get("status") == "resolved" and
                isinstance(root.get("selected"), str) and
                root["selected"] in nodes,
                f"malformed selected action root: {index}")
        outer = root["selected"]
        nested = nested_by_outer.get(outer, [])
        require(all(key in nodes for key in nested),
                f"unbound nested action-ledger source: {index}")
        deltas.append([outer, *nested])
    return deltas


def derive_logical_source_closure(
    manifest: dict[str, Any], completed_action_count: int, final_boundary: bool,
    generated_control_records: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    """Derive the exact classified expected closure from authenticated inputs."""
    nodes = manifest.get("source_nodes")
    bootstrap_roots = manifest.get("bootstrap_roots")
    action_roots = manifest.get("build_sequence_roots")
    require(isinstance(nodes, dict) and nodes, "missing manifest source nodes")
    require(isinstance(bootstrap_roots, list) and bootstrap_roots,
            "missing manifest bootstrap roots")
    require(isinstance(action_roots, list), "missing manifest action roots")
    require(0 <= completed_action_count <= len(action_roots),
            "invalid closure action count")

    execution = selected_execution_edges(manifest, nodes)
    selected_serialization_branch = execution["serialization_selected"]
    unselected_serialization_branch = execution["serialization_unselected"]

    generated_dependencies = manifest.get("generated_dependency_contracts")
    require(isinstance(generated_dependencies, list),
            "missing generated dependency contracts")
    insulate_dependencies = [
        entry for entry in generated_dependencies
        if isinstance(entry, dict) and
        entry.get("literal") == "candle/build/insulate.ml"
    ]
    require(len(insulate_dependencies) == 1 and
            insulate_dependencies[0].get("source") == "candle:hol_lib.ml" and
            insulate_dependencies[0].get("kind") == "loads" and
            insulate_dependencies[0].get("line") == 23 and
            insulate_dependencies[0].get("status") == "generated-contract" and
            insulate_dependencies[0].get("generation") == {
                "generator": "candle/insulate.py",
                "recipe": "build-instructions.sh",
                "runtime_input": "candle/build/types.txt",
            }, "malformed insulate generated dependency contract")
    digest_contract = manifest.get("source_digest_contract")
    require(isinstance(digest_contract, dict) and
            digest_contract.get("generated_source") ==
            "candle:candle/flyspeck_source_digests.ml" and
            digest_contract.get("preload_authentication") ==
            "loader checks generated_source_md5 before executing the program",
            "malformed source-digest generated control contract")

    selected: set[str] = set()
    observed_outer_sources: set[str] = set()
    observed_nested_sources: set[str] = set()

    def visit(key: str) -> None:
        require(isinstance(key, str) and key in nodes,
                f"unbound logical source closure key: {key}")
        if key in selected:
            return
        selected.add(key)
        dependencies = nodes[key].get("dependencies")
        require(isinstance(dependencies, list),
                f"missing dependencies for logical source: {key}")
        for dependency in dependencies:
            require(isinstance(dependency, dict),
                    f"malformed dependency for logical source: {key}")
            status = dependency.get("status")
            if status == "resolved":
                target = dependency.get("selected")
                require(isinstance(target, str),
                        f"resolved dependency has no target: {key}")
                targets = [target]
            elif status == "resolved-dynamic":
                targets = dependency.get("selected_targets")
                require(isinstance(targets, list) and targets and
                        all(isinstance(target, str) for target in targets),
                        f"dynamic dependency has no exact targets: {key}")
            else:
                require(status in NON_SOURCE_DEPENDENCY_STATUSES,
                        f"unsupported dependency status in logical closure: {status}")
                targets = []
            for target in targets:
                if (key == STRICTBUILD_SOURCE_KEY and
                        target == STRICTBUILD_SERIALIZATION_OPT_IN_KEY):
                    require(dependency.get("kind") == "needs" and
                            dependency.get("line") == 162 and
                            dependency.get("syntax_position") ==
                            "embedded-expression",
                            "strictbuild serialization opt-in edge drift")
                    continue
                if key == SERIALIZATION_SOURCE_KEY:
                    if target == unselected_serialization_branch:
                        continue
                    if target in (
                        selected_serialization_branch,
                        unselected_serialization_branch,
                    ):
                        require(target == selected_serialization_branch,
                                "unselected serialization branch reached")
                visit(target)

    roots = list(bootstrap_roots)
    action_ledger_deltas = derive_action_ledger_delta_keys(
        manifest, completed_action_count,
    )
    for delta in action_ledger_deltas:
        roots.append(delta[0])
        observed_outer_sources.add(delta[0])
        observed_nested_sources.update(delta[1:])
    for root in roots:
        visit(root)

    # These are selected runtime sources but not graph roots: source-integrity
    # is loaded by setup, while the executed prefix is authenticated material
    # derived from the full-build driver.  Traversing that driver would falsely
    # claim actions beyond a non-final boundary.
    for key in SOURCE_CLOSURE_HARNESS_KEYS:
        require(key in nodes, f"missing logical source harness: {key}")
        selected.add(key)
    if final_boundary:
        require(SOURCE_CLOSURE_FINAL_KEY in nodes,
                "missing final logical source target")
        selected.add(SOURCE_CLOSURE_FINAL_KEY)
    require(SOURCE_CLOSURE_EXCLUDED_LOADER not in selected,
            "non-executing full loader entered logical source closure")
    require(STRICTBUILD_SERIALIZATION_OPT_IN_KEY not in selected and
            unselected_serialization_branch not in selected,
            "unselected conditional source entered logical source closure")

    require(isinstance(generated_control_records, dict) and
            set(generated_control_records) == set(SOURCE_CLOSURE_GENERATED_KEYS),
            "generated executed-control set mismatch")
    source_digest_record = generated_control_records[
        "candle:candle/flyspeck_source_digests.ml"
    ]
    require(source_digest_record.get("sha256") ==
            digest_contract.get("generated_source_sha256") and
            source_digest_record.get("md5") ==
            digest_contract.get("generated_source_md5"),
            "source-digest generated control differs from manifest")
    record_inputs = {
        key: nodes[key] for key in selected
    }
    for key, generated_record in generated_control_records.items():
        require(key not in record_inputs and isinstance(generated_record, dict),
                f"malformed generated executed control: {key}")
        record_inputs[key] = generated_record

    records: list[dict[str, Any]] = []
    for key in sorted(record_inputs):
        node = record_inputs[key]
        if key in SOURCE_CLOSURE_GENERATED_KEYS:
            classification = "generated-executed-control"
        elif key == SOURCE_CLOSURE_DERIVATION_KEY:
            classification = "derivation-only-input"
        elif key in observed_outer_sources:
            classification = "observed-outer-source"
        elif key in observed_nested_sources:
            classification = "observed-nested-source"
        else:
            classification = "expected-nested-source"
        record: dict[str, Any] = {
            "index": len(records),
            "key": key,
            "classification": classification,
            "source_sha256": node.get("sha256"),
            "source_md5": node.get("md5"),
            "execution_normalization": None,
        }
        require(re.fullmatch(r"[0-9a-f]{64}", str(record["source_sha256"])) is not None and
                re.fullmatch(r"[0-9a-f]{32}", str(record["source_md5"])) is not None,
                f"malformed logical source digest: {key}")
        normalization = node.get("execution_normalization")
        if isinstance(normalization, dict):
            normalized = {
                field: normalization.get(field)
                for field in ("id", "normalized_sha256", "normalized_md5")
            }
            require(isinstance(normalized["id"], str) and normalized["id"] and
                    re.fullmatch(r"[0-9a-f]{64}",
                                 str(normalized["normalized_sha256"])) is not None and
                    re.fullmatch(r"[0-9a-f]{32}",
                                 str(normalized["normalized_md5"])) is not None,
                    f"malformed logical source normalization: {key}")
            record["execution_normalization"] = normalized
        records.append(record)
    return {
        "schema": 3,
        "kind": "candle-flyspeck-selected-nested-logical-source-closure",
        "policy": SOURCE_CLOSURE_POLICY,
        "order": SOURCE_CLOSURE_ORDER,
        "completed_action_count": completed_action_count,
        "final_target_selected": final_boundary,
        "record_count": len(records),
        "ordered_record_sha256": canonical_sha256(records),
        "records": records,
        "physical_loader_cache_trace": False,
        "execution_observation": SOURCE_CLOSURE_OBSERVATION,
        "self_certifies_nested_execution": False,
        "s2_s3_evidence": False,
    }


def logical_source_marker(nonce: str, record: dict[str, Any]) -> str:
    normalization = record["execution_normalization"]
    normalized_fields = ("-", "-", "-")
    if normalization is not None:
        normalized_fields = (
            normalization["id"].encode("utf-8").hex(),
            normalization["normalized_sha256"],
            normalization["normalized_md5"],
        )
    return " ".join((
        SOURCE_CLOSURE_PREFIX, nonce, f"{record['index']:03d}",
        record["key"].encode("utf-8").hex(),
        record["classification"].encode("utf-8").hex(),
        record["source_sha256"],
        record["source_md5"], *normalized_fields,
    ))


def logical_source_terminal(
    nonce: str, boundary_id: str, closure: dict[str, Any],
) -> str:
    return (
        f"{SOURCE_CLOSURE_SUCCESS_MARKER} {nonce} {boundary_id} "
        f"{closure['record_count']} {closure['ordered_record_sha256']}"
    )


def fingerprint_requests(boundary_id: str) -> list[str]:
    """Return ordered candidate identities available at an exact boundary."""
    boundary_number = boundary_id.split("-", 1)[0]
    if boundary_number in ("05", "06"):
        return ["Linear_programming_results.linear_programming_results_th"]
    if boundary_number == "07":
        return [
            "Linear_programming_results.linear_programming_results_th",
            "Mk_all_ineq.the_nonlinear_inequalities",
            "The_kepler_conjecture.tame_nonlinear_imp_kepler_conjecture",
            "Candle_flyspeck_l2.tame_imp_kepler_conjecture",
        ]
    return []


def dependency_history_requests(boundary_id: str) -> list[str]:
    """Return identities for which Serialization is available at the boundary."""
    if boundary_id.startswith("07-"):
        return fingerprint_requests(boundary_id)
    return []


def dependency_history_marker_prefix(
    nonce: str, index: int, theorem_name: str,
) -> str:
    return " ".join((
        DEPENDENCY_HISTORY_PREFIX, nonce, str(index),
        theorem_name.encode("utf-8").hex(),
    )) + " "


def dependency_history_terminal(
    nonce: str, boundary_id: str, theorem_names: list[str],
) -> str:
    return " ".join((
        DEPENDENCY_HISTORY_SUCCESS_MARKER, nonce, boundary_id,
        str(len(theorem_names)), canonical_sha256(theorem_names),
    ))


def dependency_history_not_requested(boundary_id: str) -> dict[str, Any]:
    return {
        "schema": 1,
        "kind": "candle-flyspeck-dependency-history-observation",
        "policy": DEPENDENCY_HISTORY_POLICY,
        "status": "not_requested",
        "boundary_id": boundary_id,
        "record_count": 0,
        "ordered_request_sha256": canonical_sha256([]),
        "ordered_record_sha256": canonical_sha256([]),
        "records": [],
        "approved_reference_present": False,
        "dependency_history_is_kernel_trace": False,
        "pft_used": False,
        "s2_s3_evidence": False,
    }


def parse_dependency_history_text(
    log: str, theorem_names: list[str], boundary_id: str, nonce: str,
) -> dict[str, Any]:
    """Parse an exact nonce-bound Serialization.full_digest_thm session."""
    require(re.fullmatch(r"[0-9a-f]{32}", nonce) is not None,
            "dependency-history nonce must be 128-bit lowercase hex")
    namespace_lines = [
        line for line in log.splitlines()
        if line.startswith("CANDLE_FLYSPECK_DEPENDENCY_HISTORY_")
    ]
    if not theorem_names:
        require(not namespace_lines,
                "unexpected dependency-history record at an unrequested boundary")
        return dependency_history_not_requested(boundary_id)
    require(boundary_id.startswith("07-") and
            theorem_names == dependency_history_requests(boundary_id),
            "dependency history is requested only for the exact final boundary")
    records = []
    expected_lines = []
    for index, theorem_name in enumerate(theorem_names):
        require(SAFE_VALUE_PATH.fullmatch(theorem_name) is not None,
                f"unsafe dependency-history theorem value path: {theorem_name}")
        prefix = dependency_history_marker_prefix(nonce, index, theorem_name)
        matches = [
            line for line in namespace_lines if line.startswith(prefix)
        ]
        require(len(matches) == 1,
                f"missing or duplicate dependency-history record: {index}")
        fields = matches[0].split(" ")
        require(len(fields) == 5 and fields[:4] == prefix[:-1].split(" ") and
                re.fullmatch(r"[0-9a-f]{32}", fields[4]) is not None,
                f"malformed dependency-history record: {index}")
        records.append({
            "index": index,
            "name": theorem_name,
            "full_digest_md5": fields[4],
        })
        expected_lines.append(matches[0])
    terminal = dependency_history_terminal(nonce, boundary_id, theorem_names)
    expected_lines.append(terminal)
    require(namespace_lines == expected_lines,
            "dependency-history session is missing, extra, or out of order")
    return {
        "schema": 1,
        "kind": "candle-flyspeck-dependency-history-observation",
        "policy": DEPENDENCY_HISTORY_POLICY,
        "status": "observed_uncompared",
        "boundary_id": boundary_id,
        "record_count": len(records),
        "ordered_request_sha256": canonical_sha256(theorem_names),
        "ordered_record_sha256": canonical_sha256(records),
        "records": records,
        "approved_reference_present": False,
        "dependency_history_is_kernel_trace": False,
        "pft_used": False,
        "s2_s3_evidence": False,
    }


def parse_dependency_history(
    log_path: Path, theorem_names: list[str], boundary_id: str, nonce: str,
) -> dict[str, Any]:
    try:
        log = log_path.read_text(encoding="utf-8", errors="strict")
    except (OSError, UnicodeError) as error:
        raise ContractError(f"cannot read dependency-history log: {error}") from error
    return parse_dependency_history_text(log, theorem_names, boundary_id, nonce)


def validate_dependency_history_observation(
    observation: object, theorem_names: list[str], boundary_id: str, nonce: str,
) -> dict[str, Any]:
    fields = {
        "schema", "kind", "policy", "status", "boundary_id",
        "record_count", "ordered_request_sha256", "ordered_record_sha256",
        "records", "approved_reference_present",
        "dependency_history_is_kernel_trace", "pft_used", "s2_s3_evidence",
    }
    require(isinstance(observation, dict) and set(observation) == fields,
            "malformed dependency-history observation")
    if not theorem_names:
        expected = dependency_history_not_requested(boundary_id)
    else:
        records = observation.get("records")
        require(isinstance(records, list) and len(records) == len(theorem_names),
                "malformed dependency-history observation records")
        synthetic_lines = []
        for index, (record, name) in enumerate(zip(
            records, theorem_names, strict=True,
        )):
            require(isinstance(record, dict) and set(record) == {
                        "index", "name", "full_digest_md5",
                    } and type(record.get("index")) is int and
                    record["index"] == index and record.get("name") == name and
                    isinstance(record.get("full_digest_md5"), str) and
                    re.fullmatch(r"[0-9a-f]{32}", record["full_digest_md5"])
                    is not None,
                    f"malformed dependency-history observation record: {index}")
            synthetic_lines.append(
                dependency_history_marker_prefix(nonce, index, name) +
                record["full_digest_md5"]
            )
        synthetic_lines.append(
            dependency_history_terminal(nonce, boundary_id, theorem_names)
        )
        expected = parse_dependency_history_text(
            "\n".join(synthetic_lines) + "\n",
            theorem_names, boundary_id, nonce,
        )
    require(exact_json_equal(observation, expected),
            "dependency-history observation differs from exact protocol")
    return expected


def build_semantic_evidence_plan(
    boundary_id: str,
    action_count: int,
    logical_source_closure: dict[str, Any],
    physical_source_trace: dict[str, Any],
    lp_certificate_runtime: list[dict[str, Any]],
    authenticated_inputs: dict[str, str],
) -> dict[str, Any]:
    certificate_records = [
        {
            "index": index,
            "class": item["class"],
            "relative": item["relative"],
            "bytes": item["bytes"],
            "sha256": item["sha256"],
            "md5": item["md5"],
        }
        for index, item in enumerate(lp_certificate_runtime)
    ]
    plan = {
        "schema": 1,
        "kind": "candle-flyspeck-direct-semantic-evidence-plan",
        "policy": SEMANTIC_COVERAGE_POLICY,
        "boundary_id": boundary_id,
        "completed_action_count": action_count,
        "logical_source": {
            "record_count": logical_source_closure["record_count"],
            "ordered_record_sha256":
                logical_source_closure["ordered_record_sha256"],
        },
        "physical_source_trace": {
            "required_key_count": physical_source_trace["required_key_count"],
            "ordered_required_key_sha256":
                physical_source_trace["ordered_required_key_sha256"],
        },
        "structural_fingerprint_requests": fingerprint_requests(boundary_id),
        "dependency_history_requests": dependency_history_requests(boundary_id),
        "authenticated_inputs": authenticated_inputs,
        "lp_certificate_inputs": {
            "status": "authenticated-runtime-inputs-not-consumption-traced",
            "record_count": len(certificate_records),
            "ordered_record_sha256": canonical_sha256(certificate_records),
            "records": certificate_records,
        },
        "approval_included": False,
        "pft_used": False,
        "s2_s3_evidence": False,
    }
    return validate_semantic_evidence_plan(
        plan, boundary_id, action_count,
        logical_source_closure, physical_source_trace, authenticated_inputs,
    )


def validate_semantic_evidence_plan(
    plan: object,
    boundary_id: str,
    action_count: int,
    logical_source_closure: dict[str, Any],
    physical_source_trace: dict[str, Any],
    authenticated_inputs: dict[str, str],
) -> dict[str, Any]:
    fields = {
        "schema", "kind", "policy", "boundary_id", "completed_action_count",
        "logical_source", "physical_source_trace",
        "structural_fingerprint_requests", "dependency_history_requests",
        "authenticated_inputs", "lp_certificate_inputs", "approval_included", "pft_used",
        "s2_s3_evidence",
    }
    require(isinstance(plan, dict) and set(plan) == fields and
            type(plan.get("schema")) is int and plan["schema"] == 1 and
            plan.get("kind") ==
            "candle-flyspeck-direct-semantic-evidence-plan" and
            plan.get("policy") == SEMANTIC_COVERAGE_POLICY and
            plan.get("boundary_id") == boundary_id and
            type(plan.get("completed_action_count")) is int and
            plan["completed_action_count"] == action_count and
            plan.get("approval_included") is False and
            plan.get("pft_used") is False and
            plan.get("s2_s3_evidence") is False,
            "malformed direct semantic-evidence plan")
    require(exact_json_equal(plan.get("logical_source"), {
                "record_count": logical_source_closure["record_count"],
                "ordered_record_sha256":
                    logical_source_closure["ordered_record_sha256"],
            }) and
            exact_json_equal(plan.get("physical_source_trace"), {
                "required_key_count":
                    physical_source_trace["required_key_count"],
                "ordered_required_key_sha256":
                    physical_source_trace["ordered_required_key_sha256"],
            }) and
            exact_json_equal(plan.get("structural_fingerprint_requests"),
                             fingerprint_requests(boundary_id)) and
            exact_json_equal(plan.get("dependency_history_requests"),
                             dependency_history_requests(boundary_id)) and
            isinstance(authenticated_inputs, dict) and
            set(authenticated_inputs) == {
                "plan_sha256", "host_materialization_sha256", "manifest_sha256",
            } and all(isinstance(value, str) and
                      re.fullmatch(r"[0-9a-f]{64}", value) is not None
                      for value in authenticated_inputs.values()) and
            exact_json_equal(plan.get("authenticated_inputs"),
                             authenticated_inputs),
            "semantic-evidence plan differs from authenticated runtime boundary")
    certificates = plan.get("lp_certificate_inputs")
    require(isinstance(certificates, dict) and set(certificates) == {
                "status", "record_count", "ordered_record_sha256", "records",
            } and certificates.get("status") ==
            "authenticated-runtime-inputs-not-consumption-traced" and
            type(certificates.get("record_count")) is int and
            certificates["record_count"] == 39 and
            isinstance(certificates.get("records"), list) and
            len(certificates["records"]) == 39 and
            isinstance(certificates.get("ordered_record_sha256"), str) and
            re.fullmatch(r"[0-9a-f]{64}",
                         certificates["ordered_record_sha256"]) is not None and
            certificates["ordered_record_sha256"] ==
            canonical_sha256(certificates["records"]),
            "malformed semantic-evidence LP-certificate input projection")
    relatives = []
    for index, record in enumerate(certificates["records"]):
        require(isinstance(record, dict) and set(record) == {
                    "index", "class", "relative", "bytes", "sha256", "md5",
                } and type(record.get("index")) is int and
                record["index"] == index and
                record.get("class") == "lp-certificate-prepared" and
                isinstance(record.get("relative"), str) and
                bool(record["relative"]) and
                not Path(record["relative"]).is_absolute() and
                ".." not in Path(record["relative"]).parts and
                Path(record["relative"]).as_posix() == record["relative"] and
                type(record.get("bytes")) is int and record["bytes"] > 0 and
                isinstance(record.get("sha256"), str) and
                re.fullmatch(r"[0-9a-f]{64}", record["sha256"]) is not None and
                isinstance(record.get("md5"), str) and
                re.fullmatch(r"[0-9a-f]{32}", record["md5"]) is not None,
                f"malformed semantic-evidence LP-certificate record: {index}")
        relatives.append(record["relative"])
    require(len(relatives) == len(set(relatives)),
            "duplicate semantic-evidence LP-certificate path")
    return plan


def derive_semantic_coverage(
    plan: dict[str, Any],
    logical_source_observation: dict[str, Any],
    physical_source_observation: dict[str, Any],
    structural_fingerprints: dict[str, Any],
    dependency_history: dict[str, Any],
) -> dict[str, Any]:
    structural_names = plan["structural_fingerprint_requests"]
    dependency_names = plan["dependency_history_requests"]
    require(logical_source_observation.get("status") ==
            "expected-closure-emitted-unapproved" and
            logical_source_observation.get("record_count") ==
            plan["logical_source"]["record_count"] and
            logical_source_observation.get("ordered_record_sha256") ==
            plan["logical_source"]["ordered_record_sha256"] and
            physical_source_observation.get("status") ==
            "closed-loader-owned-session" and
            physical_source_observation.get("observed_key_count") ==
            plan["physical_source_trace"]["required_key_count"] and
            physical_source_observation.get("ordered_observed_key_sha256") ==
            plan["physical_source_trace"]["ordered_required_key_sha256"],
            "semantic coverage lacks exact source observations")
    expected_fingerprint_status = (
        "observed_uncompared" if structural_names else "not_requested"
    )
    expected_dependency_status = (
        "observed_uncompared" if dependency_names else "not_requested"
    )
    require(structural_fingerprints.get("status") ==
            expected_fingerprint_status and
            structural_fingerprints.get("approved_reference_present") is False and
            dependency_history.get("status") == expected_dependency_status and
            dependency_history.get("approved_reference_present") is False and
            dependency_history.get("pft_used") is False and
            dependency_history.get("s2_s3_evidence") is False,
            "semantic coverage contains an unexpected observation state")
    fingerprint_records = structural_fingerprints.get("theorems")
    require(isinstance(fingerprint_records, list) and
            [record.get("name") for record in fingerprint_records
             if isinstance(record, dict)] == structural_names,
            "semantic coverage structural identities differ")
    lp_requested = (
        "Linear_programming_results.linear_programming_results_th"
        in structural_names
    )
    final_requested = bool(dependency_names)
    return {
        "schema": 1,
        "kind": "candle-flyspeck-direct-semantic-coverage-observation",
        "policy": SEMANTIC_COVERAGE_POLICY,
        "status": (
            "observed_uncompared" if structural_names else
            "source-observed-semantic-not-requested"
        ),
        "boundary_id": plan["boundary_id"],
        "semantic_evidence_plan_sha256": canonical_sha256(plan),
        "logical_source_observation_sha256":
            canonical_sha256(logical_source_observation),
        "physical_source_observation_sha256":
            canonical_sha256(physical_source_observation),
        "structural_fingerprint_observation_sha256":
            canonical_sha256(structural_fingerprints),
        "dependency_history_observation_sha256":
            canonical_sha256(dependency_history),
        "lp_certificate_input_sha256": plan["lp_certificate_inputs"][
            "ordered_record_sha256"
        ],
        "source": "loader-observed-exact-unapproved",
        "lp": "observed-uncompared" if lp_requested else "not_requested",
        "nonlinear": (
            "observed-uncompared" if final_requested else "not_requested"
        ),
        "final_implication": (
            "observed-uncompared" if final_requested else "not_requested"
        ),
        "lp_certificate_consumption_trace_included": False,
        "dependency_history_is_kernel_trace": False,
        "approved_reference_present": False,
        "approval_sha256": None,
        "pft_used": False,
        "s2_eligible": False,
        "s3_eligible": False,
        "s2_s3_evidence": False,
    }


def write_postlude(
    path: Path,
    candle_root: Path,
    boundary_id: str,
    theorem_names: list[str],
    nonce: str,
    logical_source_closure: dict[str, Any],
    dependency_theorem_names: list[str] | None = None,
) -> None:
    dependency_theorem_names = dependency_theorem_names or []
    lines = ["(* Generated theorem-observation postlude; not an approval record. *)"]
    if boundary_id.startswith("07-"):
        lines.append(f"#use {ocaml_string(str(candle_root / L2_TARGET_RELATIVE))};;")
    for record in logical_source_closure["records"]:
        lines.append(
            f"print_endline {ocaml_string(logical_source_marker(nonce, record))};;"
        )
    lines.append(
        f"print_endline {ocaml_string(logical_source_terminal(nonce, boundary_id, logical_source_closure))};;"
    )
    if theorem_names:
        lines.append(f"#use {ocaml_string(str(candle_root / FINGERPRINT_RELATIVE))};;")
        for name in theorem_names:
            require(SAFE_VALUE_PATH.fullmatch(name) is not None,
                    f"unsafe theorem value path: {name}")
            lines.append(f"candle_s1_emit_fingerprint {ocaml_string(name)} {name};;")
        lines.append("candle_s1_emit_state_fingerprint ();;")
        marker = (
            f"{FINGERPRINT_SUCCESS_MARKER} {nonce} {boundary_id} "
            f"{len(theorem_names)}"
        )
        lines.append(f"print_endline {ocaml_string(marker)};;")
    if dependency_theorem_names:
        require(dependency_theorem_names == dependency_history_requests(boundary_id),
                "postlude dependency-history request differs from final contract")
        for index, name in enumerate(dependency_theorem_names):
            require(SAFE_VALUE_PATH.fullmatch(name) is not None,
                    f"unsafe dependency-history theorem value path: {name}")
            value = f"candle_flyspeck_dependency_history_{index:03d}"
            lines.append(
                f"let {value} = Serialization.full_digest_thm {name};;"
            )
            lines.append(
                "if String.length " + value + " <> 32 then failwith " +
                ocaml_string("malformed Flyspeck dependency-history digest") + ";;"
            )
            lines.append(
                "print_endline (" +
                ocaml_string(dependency_history_marker_prefix(
                    nonce, index, name,
                )) + " ^ " + value + ");;"
            )
        lines.append(
            "print_endline " + ocaml_string(dependency_history_terminal(
                nonce, boundary_id, dependency_theorem_names,
            )) + ";;"
        )
    lines.append(f"Cakeml.requestSourceTraceFinish {ocaml_string(nonce)};;")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def build_source_trace_contract(
    prepared: dict[str, Any],
    logical_source_closure: dict[str, Any],
    program_path: Path,
    postlude_path: Path,
    theorem_names: list[str],
    nonce: str,
) -> dict[str, Any]:
    """Bind every allowed post-config loader path to exact selected bytes."""
    require(re.fullmatch(r"[0-9a-f]{32}", nonce) is not None,
            "source trace nonce must be 128-bit lowercase hex")
    required_source_keys = {
        record["key"] for record in logical_source_closure["records"]
        if record["classification"] != "derivation-only-input"
    }
    source_by_key = {
        item["key"]: item for item in prepared["source_runtime"]
    }
    require(len(source_by_key) == len(prepared["source_runtime"]),
            "duplicate runtime source key while building trace")
    normalization_by_original = {
        item["original"]: item for item in prepared["normalized_runtime"]
    }
    require(len(normalization_by_original) == len(prepared["normalized_runtime"]),
            "duplicate runtime normalization while building trace")
    bindings_by_resolved: dict[str, dict[str, Any]] = {}

    def add_binding(
        resolved: Path | str,
        canonical: Path | str,
        key: str,
        source_record: dict[str, Any],
        selected: Path | str | None = None,
        selected_sha256: str | None = None,
        normalization: str = "-",
    ) -> str:
        resolved_value = str(resolved)
        canonical_value = str(canonical)
        selected_value = (
            str(selected) if selected is not None else canonical_value
        )
        require(all(os.path.isabs(path) and os.path.isfile(path) and
                    not os.path.islink(path)
                    for path in (
                        resolved_value, canonical_value, selected_value,
                    )),
                f"source trace binding is not an ordinary absolute file: {key}")
        record = {
            "resolved": resolved_value,
            "canonical": canonical_value,
            "key": key,
            "basename": Path(canonical_value).name,
            "source_md5": source_record["md5"],
            "source_sha256": source_record["sha256"],
            "selected": selected_value,
            "selected_sha256": (
                selected_sha256 if selected_sha256 is not None
                else source_record["sha256"]
            ),
            "normalization": normalization,
        }
        require(re.fullmatch(r"[0-9a-f]{32}", str(record["source_md5"]))
                is not None and
                re.fullmatch(r"[0-9a-f]{64}", str(record["source_sha256"]))
                is not None and
                re.fullmatch(r"[0-9a-f]{64}", str(record["selected_sha256"]))
                is not None and isinstance(key, str) and key and
                isinstance(normalization, str) and normalization,
                f"malformed source trace digest binding: {key}")
        binding = {"binding_id": canonical_sha256(record), **record}
        prior = bindings_by_resolved.get(record["resolved"])
        if prior is None:
            bindings_by_resolved[record["resolved"]] = binding
        else:
            require(prior == binding,
                    f"conflicting source trace resolved path: {record['resolved']}")
        return key

    for key in sorted(required_source_keys & set(source_by_key)):
        source = source_by_key[key]
        canonical = source["absolute"]
        normalization = normalization_by_original.get(canonical)
        add_binding(
            canonical, canonical, key, source,
            selected=(normalization["output"] if normalization else canonical),
            selected_sha256=(normalization["sha256"] if normalization else None),
            normalization=(normalization["normalization_id"]
                           if normalization else "-"),
        )
    for item in sorted(
        prepared["source_alias_runtime"], key=lambda value: value["alias"],
    ):
        if item["source_key"] not in required_source_keys:
            continue
        source = source_by_key[item["source_key"]]
        normalization = normalization_by_original.get(item["canonical"])
        add_binding(
            item["alias"], item["canonical"], item["source_key"], source,
            selected=(normalization["output"]
                      if normalization else item["canonical"]),
            selected_sha256=(normalization["sha256"] if normalization else None),
            normalization=(normalization["normalization_id"]
                           if normalization else "-"),
        )

    candle_root = Path(prepared["candle_runtime_root"])
    control_specs = (
        ("control:runtime-setup", candle_root / SETUP_RELATIVE),
        ("candle:candle/flyspeck_source_digests.ml",
         candle_root / SOURCE_DIGEST_RELATIVE),
        ("candle:candle/build/insulate.ml",
         candle_root / "candle/build/insulate.ml"),
        ("control:instrumented-prefix", program_path),
        ("control:stratum-check", candle_root / CHECK_RELATIVE),
        ("control:postlude", postlude_path),
    )
    for key, path in control_specs:
        record = hash_file(path)
        add_binding(path, path, key, record)
        required_source_keys.add(key)
    if theorem_names:
        key = "control:fingerprint-serializer"
        path = candle_root / FINGERPRINT_RELATIVE
        add_binding(path, path, key, hash_file(path))
        required_source_keys.add(key)

    missing = sorted(
        key for key in required_source_keys
        if not any(binding["key"] == key
                   for binding in bindings_by_resolved.values())
    )
    require(not missing, f"source trace required keys are unbound: {missing}")
    bindings = sorted(
        bindings_by_resolved.values(), key=lambda value: value["resolved"],
    )
    binding_ids = [binding["binding_id"] for binding in bindings]
    require(len(binding_ids) == len(set(binding_ids)),
            "duplicate source trace binding identity")
    required_keys = sorted(required_source_keys)
    contract = {
        "schema": 1,
        "protocol": SOURCE_TRACE_PROTOCOL,
        "nonce": nonce,
        "activation": SOURCE_TRACE_ACTIVATION,
        "binding_count": len(bindings),
        "ordered_binding_sha256": canonical_sha256(bindings),
        "bindings": bindings,
        "required_key_count": len(required_keys),
        "ordered_required_key_sha256": canonical_sha256(required_keys),
        "required_keys": required_keys,
        "top_level_control_keys": list(SOURCE_TRACE_TOP_LEVEL_CONTROLS),
    }
    return validate_source_trace_contract(contract)


def write_config(
    path: Path,
    candle_root: Path,
    prepared: dict[str, Any],
    execution_program: Path,
    execution_md5: str,
) -> None:
    def string(value: Path | str) -> str:
        return ocaml_string(str(value))

    source_trace_contract = validate_source_trace_contract(
        prepared["source_trace_contract"]
    )
    require(source_trace_contract["nonce"] == prepared["attempt_nonce"],
            "source trace nonce differs from runtime attempt")
    lines = [
        "(* Generated by flyspeck_stratum_runtime.py; do not edit. *)",
        f"let candle_hollight_root = {string(candle_root)};;",
        f"let candle_flyspeck_root = {string(prepared['flyspeck_root'])};;",
        f"let candle_flyspeck_overlay_root = {string(prepared['overlay_root'])};;",
        f"let candle_flyspeck_generated_root = {string(prepared['generated_root'])};;",
        'let candle_flyspeck_build_mode = "stratum-runtime";;',
        f"let candle_flyspeck_stratum_boundary = {string(prepared['boundary']['boundary_id'])};;",
        f"let candle_flyspeck_stratum_action_count = {len(prepared['actions'])};;",
        (
            "let candle_flyspeck_stratum_normalization_count = "
            f"{len(prepared['normalized_runtime'])};;"
        ),
        (
            "let candle_flyspeck_stratum_source_alias_count = "
            f"{len(prepared['source_alias_runtime'])};;"
        ),
        f"let candle_flyspeck_stratum_attempt_nonce = {string(prepared['attempt_nonce'])};;",
        f"let candle_flyspeck_stratum_program = {string(execution_program)};;",
        f"let candle_flyspeck_stratum_program_md5 = {string(execution_md5)};;",
        (
            "let candle_flyspeck_stratum_source_trace_nonce = "
            f"{string(source_trace_contract['nonce'])};;"
        ),
        "let candle_flyspeck_stratum_source_trace_bindings = [",
    ]
    for item in source_trace_contract["bindings"]:
        lines.append(
            "  (" + ",".join(string(item[field]) for field in (
                "binding_id", "resolved", "canonical", "key", "basename",
                "source_md5", "source_sha256", "selected",
                "selected_sha256", "normalization",
            )) + ");"
        )
    lines.extend([
        "];;",
        (
            "if List.length candle_flyspeck_stratum_source_trace_bindings <> "
            f"{source_trace_contract['binding_count']} then "
            "failwith \"incomplete Flyspeck source trace table\";;"
        ),
        (
            "Cakeml.configureSourceTrace "
            "candle_flyspeck_stratum_source_trace_nonce "
            "candle_flyspeck_stratum_source_trace_bindings;;"
        ),
        "let candle_flyspeck_stratum_source_aliases = [",
    ])
    for item in prepared["source_alias_runtime"]:
        lines.append(
            f"  ({string(item['alias'])},{string(item['canonical'])});"
        )
    lines.extend([
        "];;",
        "let candle_flyspeck_stratum_normalized_sources = [",
    ])
    for item in prepared["normalized_runtime"]:
        lines.append(
            f"  ({string(item['original'])},{string(item['output'])},{string(item['md5'])});"
        )
    lines.extend([
        "];;",
        "let candle_flyspeck_stratum_generated_inputs = [",
    ])
    for item in prepared["generated_runtime"]:
        lines.append(f"  ({string(item['path'])},{string(item['md5'])});")
    lines.extend([
        "];;",
        "let candle_flyspeck_lp_certificate_files = [",
    ])
    for item in prepared["lp_certificate_runtime"]:
        lines.append(f"  {string(item['path'])};")
    lines.extend([
        "];;",
        "let candle_flyspeck_stratum_process_inputs = [",
    ])
    for item in prepared["process_runtime"]:
        lines.append(f"  ({string(item['path'])},{string(item['md5'])});")
    lines.extend([
        "];;",
        "let candle_flyspeck_stratum_action_identities = [",
    ])
    for action in prepared["actions"]:
        lines.append(
            f"  ({string(action['identity_basename'])},{string(action['identity_md5'])});"
        )
    lines.extend([
        "];;",
        "let candle_flyspeck_stratum_action_ledger_deltas = [",
    ])
    for action in prepared["actions"]:
        lines.append("  [")
        for record in action["logical_source_delta"]:
            lines.append(
                f"    ({string(record['identity_basename'])},"
                f"{string(record['identity_md5'])});"
            )
        lines.append("  ];")
    lines.extend([
        "];;",
        "",
    ])
    path.write_text("\n".join(lines), encoding="utf-8")


def parse_fingerprints(
    log_path: Path, theorem_names: list[str], serializer: Path,
) -> dict[str, Any]:
    """Parse direct evidence through the exact shared structural-v2 protocol."""
    if not theorem_names:
        log = log_path.read_text(encoding="utf-8", errors="strict")
        require(not any(line.startswith((
            FINGERPRINT_MARKER + "\t", STATE_FINGERPRINT_MARKER + "\t",
        )) for line in log.splitlines()),
                "unexpected fingerprint record at an unrequested boundary")
        return {
            "status": "not_requested",
            "approved_reference_present": False,
            "serializer": None,
            "theorems": [],
            "post_state": None,
        }
    try:
        parsed = reference_protocol._read_fingerprint_records(
            log_path, tuple(theorem_names), "audited",
        )
    except (OSError, UnicodeError, reference_protocol.LoadFailure) as error:
        raise ContractError(str(error)) from error
    serializer_record = {
        "path": FINGERPRINT_RELATIVE.as_posix(),
        "sha256": hash_file(serializer)["sha256"],
    }
    require(parsed["status"] == "observed_uncompared" and
            parsed["expected_identities_present"] is False and
            parsed["approval_sha256"] is None and
            parsed["mapping_status"] == "audited" and
            parsed["serializer"] == serializer_record,
            "shared fingerprint protocol returned an unexpected evidence state")
    return {
        "status": parsed["status"],
        "approved_reference_present": False,
        "serializer": parsed["serializer"],
        "theorems": parsed["theorems"],
        "post_state": parsed["post_state"],
    }


def validate_log(
    log: str,
    actions: list[dict[str, Any]],
    boundary_id: str,
    nonce: str,
    theorem_names: list[str] | None = None,
    dependency_theorem_names: list[str] | None = None,
) -> list[dict[str, Any]]:
    theorem_names = theorem_names or []
    dependency_theorem_names = dependency_theorem_names or []
    lines = log.splitlines()

    def exact_position(marker: str, label: str) -> int:
        positions = [index for index, line in enumerate(lines) if line == marker]
        require(len(positions) == 1, f"missing or duplicate {label} marker")
        return positions[0]

    preflight = f"{PREFLIGHT_MARKER} {nonce}"
    positions = [exact_position(preflight, "stratum preflight")]
    action_events: list[dict[str, Any]] = []
    allowed_action_markers: set[str] = set()
    for index, action in enumerate(actions):
        prefix = (
            f"{ACTION_PREFIX} {nonce} {index:03d} "
            f"{action['source_sha256']} "
            f"{action['logical_source_delta_sha256']} "
        )
        matches = [
            (position, line[len(prefix):])
            for position, line in enumerate(lines)
            if line.startswith(prefix)
        ]
        require(len(matches) == 1,
                f"missing or duplicate action {index} marker")
        position, outcome = matches[0]
        require(outcome in ACTION_OUTCOMES,
                f"unsupported action {index} outcome: {outcome}")
        marker = prefix + outcome
        allowed_action_markers.add(marker)
        action_events.append({
            "index": index,
            "source_sha256": action["source_sha256"],
            "logical_source_delta_sha256":
                action["logical_source_delta_sha256"],
            "outcome": outcome,
        })
        positions.append(position)
    final = f"{SUCCESS_MARKER} {nonce} {boundary_id} {len(actions)}"
    boundary_position = exact_position(final, "boundary success")
    positions.append(boundary_position)
    fingerprint_position: int | None = None
    allowed_control_markers = {preflight, final}
    allowed_control_markers.update(allowed_action_markers)
    if theorem_names:
        fingerprint_final = (
            f"{FINGERPRINT_SUCCESS_MARKER} {nonce} {boundary_id} {len(theorem_names)}"
        )
        allowed_control_markers.add(fingerprint_final)
        fingerprint_position = exact_position(fingerprint_final, "fingerprint success")
        positions.append(fingerprint_position)
    dependency_observation = parse_dependency_history_text(
        log, dependency_theorem_names, boundary_id, nonce,
    )
    dependency_positions = [
        index for index, line in enumerate(lines)
        if line.startswith("CANDLE_FLYSPECK_DEPENDENCY_HISTORY_")
    ]
    if dependency_theorem_names:
        require(fingerprint_position is not None and dependency_positions and
                all(position > fingerprint_position
                    for position in dependency_positions) and
                dependency_observation["record_count"] ==
                len(dependency_theorem_names),
                "dependency-history protocol is outside its fingerprint session")
        positions.extend(dependency_positions)
    require(positions == sorted(positions), "stratum markers are out of order")
    control_namespaces = (
        "CANDLE_FLYSPECK_STRATUM_PREFLIGHT_",
        "CANDLE_FLYSPECK_STRATUM_ACTION_",
        "CANDLE_FLYSPECK_STRATUM_BOUNDARY_",
        "CANDLE_FLYSPECK_STRATUM_FINGERPRINTS_",
    )
    for line in lines:
        if line.startswith(control_namespaces):
            require(line in allowed_control_markers,
                    "unsupported or unexpected stratum control record")
    for index, line in enumerate(lines):
        if not line.startswith(("CANDLE_FINGERPRINT_", "CANDLE_STATE_FINGERPRINT_")):
            continue
        require(theorem_names and
                line.startswith((FINGERPRINT_MARKER + "\t",
                                 STATE_FINGERPRINT_MARKER + "\t")),
                "unsupported or unexpected fingerprint protocol record")
        require(fingerprint_position is not None and
                boundary_position < index < fingerprint_position,
                "fingerprint protocol record is outside its boundary session")
    require(not re.search(r"^(?:ERROR|EXCEPTION):|Parsing failed", log, re.MULTILINE),
            "compiled stratum log contains a top-level error")
    return action_events


def validate_logical_source_closure(
    log: str,
    expected: dict[str, Any],
    boundary_id: str,
    nonce: str,
) -> dict[str, Any]:
    """Require one exact, complete, ordered logical-closure session."""
    require(expected.get("schema") == 3 and
            expected.get("kind") ==
            "candle-flyspeck-selected-nested-logical-source-closure" and
            expected.get("policy") == SOURCE_CLOSURE_POLICY and
            expected.get("order") == SOURCE_CLOSURE_ORDER and
            expected.get("physical_loader_cache_trace") is False and
            expected.get("execution_observation") == SOURCE_CLOSURE_OBSERVATION and
            expected.get("self_certifies_nested_execution") is False and
            expected.get("s2_s3_evidence") is False,
            "unsupported expected logical source closure")
    records = expected.get("records")
    require(isinstance(records, list) and
            expected.get("record_count") == len(records) and
            expected.get("ordered_record_sha256") == canonical_sha256(records),
            "malformed expected logical source closure")
    lines = log.splitlines()

    def exact_position(marker: str, label: str) -> int:
        positions = [index for index, line in enumerate(lines) if line == marker]
        require(len(positions) == 1, f"missing or duplicate {label}")
        return positions[0]

    boundary = (
        f"{SUCCESS_MARKER} {nonce} {boundary_id} "
        f"{expected['completed_action_count']}"
    )
    boundary_position = exact_position(boundary, "boundary success marker")
    expected_markers = [logical_source_marker(nonce, record) for record in records]
    record_positions = [
        exact_position(marker, f"logical source record {index}")
        for index, marker in enumerate(expected_markers)
    ]
    terminal = logical_source_terminal(nonce, boundary_id, expected)
    terminal_position = exact_position(terminal, "logical source closure terminal marker")
    positions = [boundary_position, *record_positions, terminal_position]
    require(positions == sorted(positions),
            "logical source closure records are out of order")
    allowed = {*expected_markers, terminal}
    namespaces = (SOURCE_CLOSURE_PREFIX + " ", SOURCE_CLOSURE_SUCCESS_MARKER + " ")
    for line in lines:
        if line.startswith(namespaces):
            require(line in allowed,
                    "unsupported or unexpected logical source closure record")
    for index, line in enumerate(lines):
        if line.startswith((FINGERPRINT_MARKER + "\t",
                            STATE_FINGERPRINT_MARKER + "\t",
                            FINGERPRINT_SUCCESS_MARKER + " ")):
            require(index > terminal_position,
                    "fingerprint record precedes logical source closure terminal")
    return {
        **expected,
        "status": "expected-closure-emitted-unapproved",
    }


def validate_source_trace_contract(contract: object) -> dict[str, Any]:
    require(isinstance(contract, dict) and set(contract) == {
        "schema", "protocol", "nonce", "activation", "binding_count",
        "ordered_binding_sha256", "bindings", "required_key_count",
        "ordered_required_key_sha256", "required_keys",
        "top_level_control_keys",
    }, "malformed physical source trace contract")
    require(type(contract["schema"]) is int and contract["schema"] == 1 and
            contract["protocol"] == SOURCE_TRACE_PROTOCOL and
            contract["activation"] == SOURCE_TRACE_ACTIVATION and
            isinstance(contract["nonce"], str) and
            re.fullmatch(r"[0-9a-f]{32}", contract["nonce"]) is not None,
            "physical source trace contract identity mismatch")
    bindings = contract["bindings"]
    require(isinstance(bindings, list) and
            type(contract["binding_count"]) is int and
            contract["binding_count"] == len(bindings) and
            contract["ordered_binding_sha256"] == canonical_sha256(bindings),
            "physical source trace binding closure mismatch")
    previous_resolved: str | None = None
    resolved_paths: set[str] = set()
    binding_ids: set[str] = set()
    bound_keys: set[str] = set()
    identity_by_key: dict[str, tuple[str, ...]] = {}
    key_by_canonical: dict[str, str] = {}
    binding_fields = {
        "binding_id", "resolved", "canonical", "key", "basename",
        "source_md5", "source_sha256", "selected", "selected_sha256",
        "normalization",
    }
    for index, binding in enumerate(bindings):
        require(isinstance(binding, dict) and set(binding) == binding_fields,
                f"malformed physical source trace binding: {index}")
        binding_payload = {
            field: binding[field] for field in binding
            if field != "binding_id"
        }
        resolved = binding["resolved"]
        require(isinstance(resolved, str) and Path(resolved).is_absolute() and
                resolved not in resolved_paths and
                (previous_resolved is None or previous_resolved < resolved) and
                isinstance(binding["canonical"], str) and
                Path(binding["canonical"]).is_absolute() and
                isinstance(binding["selected"], str) and
                Path(binding["selected"]).is_absolute() and
                isinstance(binding["key"], str) and binding["key"] and
                not any(character in binding["key"] for character in "\t\n\r") and
                isinstance(binding["basename"], str) and binding["basename"] and
                not any(character in binding["basename"]
                        for character in "\t\n\r") and
                binding["basename"] == Path(binding["canonical"]).name and
                isinstance(binding["source_md5"], str) and
                re.fullmatch(r"[0-9a-f]{32}", binding["source_md5"])
                is not None and
                isinstance(binding["source_sha256"], str) and
                re.fullmatch(r"[0-9a-f]{64}", binding["source_sha256"])
                is not None and
                isinstance(binding["selected_sha256"], str) and
                re.fullmatch(r"[0-9a-f]{64}", binding["selected_sha256"])
                is not None and
                isinstance(binding["normalization"], str) and
                binding["normalization"] and
                not any(character in binding["normalization"]
                        for character in "\t\n\r") and
                isinstance(binding["binding_id"], str) and
                re.fullmatch(r"[0-9a-f]{64}", binding["binding_id"])
                is not None and
                binding["binding_id"] == canonical_sha256(binding_payload) and
                binding["binding_id"] not in binding_ids,
                f"invalid physical source trace binding: {index}")
        previous_resolved = resolved
        resolved_paths.add(resolved)
        binding_ids.add(binding["binding_id"])
        bound_keys.add(binding["key"])
        identity = tuple(binding[field] for field in (
            "canonical", "basename", "source_md5", "source_sha256",
            "selected", "selected_sha256", "normalization",
        ))
        prior_identity = identity_by_key.setdefault(binding["key"], identity)
        require(prior_identity == identity,
                f"inconsistent physical source trace key: {binding['key']}")
        prior_key = key_by_canonical.setdefault(
            binding["canonical"], binding["key"],
        )
        require(prior_key == binding["key"],
                f"physical source trace canonical path has multiple keys: "
                f"{binding['canonical']}")
    required_keys = contract["required_keys"]
    require(isinstance(required_keys, list) and
            all(isinstance(key, str) and key for key in required_keys),
            "malformed physical source trace required keys")
    require(required_keys == sorted(set(required_keys)) and
            type(contract["required_key_count"]) is int and
            contract["required_key_count"] == len(required_keys) and
            contract["ordered_required_key_sha256"] ==
            canonical_sha256(required_keys) and
            set(required_keys) == bound_keys,
            "physical source trace required-key closure mismatch")
    require(contract["top_level_control_keys"] ==
            list(SOURCE_TRACE_TOP_LEVEL_CONTROLS) and
            set(SOURCE_TRACE_TOP_LEVEL_CONTROLS) <= set(required_keys),
            "physical source trace top-level control mismatch")
    return contract


def validate_source_trace_observation(
    contract: dict[str, Any], observation: object,
) -> dict[str, Any]:
    contract = validate_source_trace_contract(contract)
    require(isinstance(observation, dict) and set(observation) == {
        "schema", "protocol", "nonce", "event_count", "ordered_event_sha256",
        "events", "request_count", "cache_skip_count", "observed_key_count",
        "ordered_observed_key_sha256", "observed_keys", "status",
    }, "malformed physical source trace observation")
    require(type(observation["schema"]) is int and
            observation["schema"] == 1 and
            observation["protocol"] == SOURCE_TRACE_PROTOCOL and
            observation["nonce"] == contract["nonce"] and
            observation["status"] == "closed-loader-owned-session",
            "physical source trace observation identity mismatch")
    events = observation["events"]
    require(isinstance(events, list) and
            type(observation["event_count"]) is int and
            observation["event_count"] == len(events) and
            observation["ordered_event_sha256"] == canonical_sha256(events),
            "physical source trace event closure mismatch")
    binding_by_id = {
        binding["binding_id"]: binding for binding in contract["bindings"]
    }
    active: list[tuple[int, str]] = []
    cache: set[str] = set()
    observed_keys: set[str] = set()
    top_level_keys: list[str] = []
    request_count = 0
    cache_skip_count = 0
    terminal_seen = False
    for event_index, event in enumerate(events):
        require(isinstance(event, dict) and not terminal_seen,
                f"malformed physical source trace event: {event_index}")
        event_type = event.get("event")
        if event_type == "request":
            require(set(event) == {
                "event", "id", "parent", "kind", "binding_id", "key",
                "cache_before",
            } and type(event["id"]) is int and
                    event["id"] == request_count and
                    (event["parent"] is None or
                     (type(event["parent"]) is int and
                      event["parent"] >= 0)) and
                    isinstance(event["binding_id"], str) and
                    isinstance(event["key"], str) and
                    isinstance(event["kind"], str) and
                    isinstance(event["cache_before"], str) and
                    event["kind"] in SOURCE_TRACE_KINDS and
                    event["cache_before"] in {"fresh-cache", "prior-cache"},
                    f"malformed physical source trace request: {event_index}")
            parent = active[-1][0] if active else None
            require(event["parent"] == parent,
                    f"physical source trace parent mismatch: {event['id']}")
            binding = binding_by_id.get(event["binding_id"])
            require(isinstance(binding, dict) and
                    event["key"] == binding["key"] and
                    event["key"] in contract["required_keys"],
                    f"physical source trace request is unbound: {event['id']}")
            prior = binding["canonical"] in cache
            require(event["cache_before"] ==
                    ("prior-cache" if prior else "fresh-cache"),
                    f"physical source trace cache-before mismatch: {event['id']}")
            expected_outcome = (
                "cache-skip"
                if event["kind"] in SOURCE_TRACE_NEED_KINDS and prior
                else "evaluated"
            )
            if (event["kind"] in
                    SOURCE_TRACE_NEED_KINDS + SOURCE_TRACE_LOAD_KINDS and
                    not prior):
                cache.add(binding["canonical"])
            if parent is None:
                top_level_keys.append(event["key"])
            observed_keys.add(event["key"])
            active.append((event["id"], expected_outcome))
            request_count += 1
        elif event_type == "outcome":
            require(set(event) == {"event", "id", "outcome"} and active and
                    type(event["id"]) is int and
                    event["id"] == active[-1][0] and
                    event["outcome"] == active[-1][1],
                    f"physical source trace outcome mismatch: {event_index}")
            if event["outcome"] == "cache-skip":
                cache_skip_count += 1
            active.pop()
        elif event_type == "terminal":
            require(set(event) == {"event", "request_count"} and
                    event_index == len(events) - 1 and not active and
                    type(event["request_count"]) is int and
                    event["request_count"] == request_count and
                    event["request_count"] >= 0,
                    "physical source trace terminal mismatch")
            terminal_seen = True
        else:
            raise ContractError(
                f"unknown physical source trace event: {event_index}"
            )
    require(terminal_seen and top_level_keys ==
            contract["top_level_control_keys"],
            "physical source trace did not close exact top-level controls")
    ordered_keys = sorted(observed_keys)
    require(ordered_keys == contract["required_keys"] and
            observation["observed_keys"] == ordered_keys and
            type(observation["observed_key_count"]) is int and
            observation["observed_key_count"] == len(ordered_keys) and
            observation["ordered_observed_key_sha256"] ==
            canonical_sha256(ordered_keys) and
            type(observation["request_count"]) is int and
            observation["request_count"] == request_count and
            type(observation["cache_skip_count"]) is int and
            observation["cache_skip_count"] == cache_skip_count,
            "physical source trace observed closure mismatch")
    return observation


def validate_source_trace(
    log_text: str, contract: dict[str, Any],
) -> dict[str, Any]:
    contract = validate_source_trace_contract(contract)
    records: list[list[str]] = []
    for line in log_text.splitlines():
        if line.startswith(SOURCE_TRACE_PREFIX):
            require(line.startswith(SOURCE_TRACE_PREFIX + "\t"),
                    "malformed physical source trace namespace")
            records.append(line.split("\t"))
    require(records, "missing physical source trace session")
    events: list[dict[str, Any]] = []
    binding_by_id = {
        binding["binding_id"]: binding for binding in contract["bindings"]
    }
    for fields in records:
        require(len(fields) >= 3 and fields[0] == SOURCE_TRACE_PREFIX and
                fields[1] == contract["nonce"],
                "physical source trace nonce or prefix mismatch")
        record_type = fields[2]
        if record_type == "REQUEST":
            require(len(fields) == 14,
                    "malformed physical source trace REQUEST")
            try:
                request_id = int(fields[3])
                parent = None if fields[4] == "-" else int(fields[4])
            except ValueError as error:
                raise ContractError(
                    "non-integer physical source trace request identity"
                ) from error
            require(fields[3] == str(request_id) and request_id >= 0 and
                    (parent is None or
                     (fields[4] == str(parent) and parent >= 0)),
                    "non-canonical physical source trace request identity")
            binding = binding_by_id.get(fields[6])
            require(isinstance(binding, dict) and fields[5] in SOURCE_TRACE_KINDS and
                    fields[7:13] == [
                        binding["key"], binding["basename"],
                        binding["source_md5"], binding["source_sha256"],
                        binding["selected_sha256"], binding["normalization"],
                    ] and fields[13] in {"fresh-cache", "prior-cache"},
                    "physical source trace REQUEST differs from binding")
            events.append({
                "event": "request", "id": request_id, "parent": parent,
                "kind": fields[5], "binding_id": fields[6], "key": fields[7],
                "cache_before": fields[13],
            })
        elif record_type == "OUTCOME":
            require(len(fields) == 5 and fields[4] in {"evaluated", "cache-skip"},
                    "malformed physical source trace OUTCOME")
            try:
                request_id = int(fields[3])
            except ValueError as error:
                raise ContractError(
                    "non-integer physical source trace outcome identity"
                ) from error
            require(fields[3] == str(request_id) and request_id >= 0,
                    "non-canonical physical source trace outcome identity")
            events.append({
                "event": "outcome", "id": request_id, "outcome": fields[4],
            })
        elif record_type == "TERMINAL":
            require(len(fields) == 4,
                    "malformed physical source trace TERMINAL")
            try:
                request_count = int(fields[3])
            except ValueError as error:
                raise ContractError(
                    "non-integer physical source trace terminal count"
                ) from error
            require(fields[3] == str(request_count) and request_count >= 0,
                    "non-canonical physical source trace terminal count")
            events.append({"event": "terminal", "request_count": request_count})
        elif record_type == "FAILURE":
            require(len(fields) == 4 and fields[3],
                    "malformed physical source trace FAILURE")
            raise ContractError(f"physical source trace failed: {fields[3]}")
        else:
            raise ContractError(f"unknown physical source trace record: {record_type}")
    request_events = [event for event in events if event["event"] == "request"]
    observed_keys = sorted({event["key"] for event in request_events})
    observation = {
        "schema": 1,
        "protocol": SOURCE_TRACE_PROTOCOL,
        "nonce": contract["nonce"],
        "event_count": len(events),
        "ordered_event_sha256": canonical_sha256(events),
        "events": events,
        "request_count": len(request_events),
        "cache_skip_count": sum(
            event.get("outcome") == "cache-skip" for event in events
        ),
        "observed_key_count": len(observed_keys),
        "ordered_observed_key_sha256": canonical_sha256(observed_keys),
        "observed_keys": observed_keys,
        "status": "closed-loader-owned-session",
    }
    return validate_source_trace_observation(contract, observation)


def validate_direct_controller_binding(
    controller: object, candle_commit: str,
) -> None:
    """Validate the complete retained controller claim without host lookups."""
    require(isinstance(controller, dict) and set(controller) == {
                "source_root", "direct_script_startup", "commit_binding",
                "python_startup_flags", "python_startup_options",
                "initial_top_level_compilation_in_host_trust_boundary",
                "local_sources", "python_runtime", "host_tools",
                "git_environment",
                "broader_python_standard_library_in_host_trust_boundary",
            }, "malformed direct runtime controller binding")
    source_root_value = controller["source_root"]
    require(exact_absolute_path(source_root_value),
            "malformed direct runtime controller source root")
    source_root = Path(source_root_value)
    direct_source = source_root / "flyspeck_stratum_runtime.py"
    require(exact_json_equal(controller["direct_script_startup"], {
                "module_name": "__main__",
                "spec_is_none": True,
                "cached_is_none": True,
                "argv0": str(direct_source),
                "source_path": str(direct_source),
            }) and exact_json_equal(
                controller["python_startup_flags"],
                EXPECTED_PYTHON_STARTUP_FLAGS,
            ) and exact_json_equal(
                controller["python_startup_options"],
                EXPECTED_PYTHON_STARTUP_OPTIONS,
            ) and
            controller[
                "initial_top_level_compilation_in_host_trust_boundary"
            ] is True and
            controller[
                "broader_python_standard_library_in_host_trust_boundary"
            ] is True,
            "malformed direct runtime controller startup binding")

    def retained_digest(item: object, fields: set[str], label: str) -> dict[str, Any]:
        require(isinstance(item, dict) and set(item) == fields and
                type(item["bytes"]) is int and item["bytes"] >= 0 and
                isinstance(item["sha256"], str) and
                re.fullmatch(r"[0-9a-f]{64}", item["sha256"]) is not None and
                isinstance(item["md5"], str) and
                re.fullmatch(r"[0-9a-f]{32}", item["md5"]) is not None,
                f"malformed direct runtime retained {label}")
        return item

    expected_bindings = {
        "cakeml_artifact_provenance.py":
            "compiled-from-captured-source-bytes",
        "flyspeck_stratum_plan.py": "compiled-from-captured-source-bytes",
        "flyspeck_stratum_runtime.py":
            "startup-captured-after-initial-compilation",
        "reference_protocol.py": "compiled-from-captured-source-bytes",
        "runtime_lock.py": "compiled-from-captured-source-bytes",
    }
    sources = controller["local_sources"]
    require(isinstance(sources, list) and len(sources) == len(expected_bindings) and
            all(isinstance(item, dict) and
                isinstance(item.get("label"), str) for item in sources) and
            {item.get("label") for item in sources} == set(expected_bindings),
            "malformed direct runtime controller source closure")
    source_by_label: dict[str, dict[str, Any]] = {}
    source_fields = {
        "label", "source_path", "execution_binding", "path",
        "bytes", "sha256", "md5",
    }
    for item in sources:
        retained_digest(item, source_fields, "controller source")
        label = item["label"]
        require(item["execution_binding"] == expected_bindings[label] and
                item["source_path"] == str(source_root / label) and
                item["path"] == f"controller/python-source/{label}",
                f"malformed direct runtime controller source: {label}")
        source_by_label[label] = item

    commit_binding = controller["commit_binding"]
    require(isinstance(commit_binding, dict) and set(commit_binding) == {
                "candle_commit", "sources",
            } and commit_binding["candle_commit"] == candle_commit and
            isinstance(commit_binding["sources"], dict) and
            set(commit_binding["sources"]) == set(expected_bindings),
            "malformed direct runtime controller commit binding")
    for label, item in source_by_label.items():
        require(commit_binding["sources"][label] == {
                    "repository_path": f"candle/{label}",
                    "index_tag": "H",
                    "bytes": item["bytes"],
                    "sha256": item["sha256"],
                    "md5": item["md5"],
                }, f"direct runtime controller commit source differs: {label}")

    python_runtime = controller["python_runtime"]
    require(isinstance(python_runtime, dict) and set(python_runtime) == {
                "execution_binding", "version", "executable", "elf_policy",
                "elf_dynamic_path_tags", "elf_roles", "virtual_elf_objects",
                "elf_objects",
            } and python_runtime["execution_binding"] ==
            EXPECTED_PYTHON_RUNTIME["execution_binding"] and
            python_runtime["version"] == EXPECTED_PYTHON_RUNTIME["version"],
            "malformed direct runtime controller Python binding")
    executable = retained_digest(
        python_runtime["executable"], {
            "source_path", "path", "bytes", "sha256", "md5",
        }, "controller Python executable",
    )
    expected_executable = EXPECTED_PYTHON_RUNTIME["executable"]
    require(executable["source_path"] == expected_executable["path"] and
            executable["path"] == "controller/python-runtime/python3.12" and
            all(executable[field] == expected_executable[field]
                for field in ("bytes", "sha256")),
            "direct runtime controller Python executable differs")
    expected_elf = EXPECTED_PYTHON_RUNTIME["elf_closure"]
    require(python_runtime["elf_policy"] == expected_elf["policy"] and
            python_runtime["elf_dynamic_path_tags"] ==
            expected_elf["dynamic_path_tags"] and
            python_runtime["elf_roles"] == expected_elf["roles"] and
            python_runtime["virtual_elf_objects"] ==
            expected_elf["virtual_objects"],
            "direct runtime controller Python ELF metadata differs")
    elf_objects = python_runtime["elf_objects"]
    require(isinstance(elf_objects, list) and
            len(elf_objects) == len(expected_elf["files"]) and
            all(isinstance(item, dict) and
                isinstance(item.get("source_path"), str)
                for item in elf_objects) and
            {item.get("source_path") for item in elf_objects} ==
            set(expected_elf["files"]),
            "malformed direct runtime controller Python ELF closure")
    for item in elf_objects:
        retained_digest(item, {
            "source_path", "path", "bytes", "sha256", "md5",
        }, "controller Python ELF object")
        expected = expected_elf["files"][item["source_path"]]
        source = Path(item["source_path"])
        require(item["path"] == (
                    "controller/python-runtime-elf/" +
                    f"{expected['sha256'][:16]}-{source.name}"
                ) and all(item[field] == expected[field]
                          for field in ("bytes", "sha256")),
                "direct runtime controller Python ELF object differs")

    require(controller["git_environment"] == {
                "LC_ALL": "C", "PATH": "/usr/bin:/bin",
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_CONFIG_GLOBAL": "/dev/null",
                "GIT_TERMINAL_PROMPT": "0",
                "GIT_NO_REPLACE_OBJECTS": "1",
                "GIT_OPTIONAL_LOCKS": "0",
            }, "direct runtime controller Git environment differs")
    host_tools = controller["host_tools"]
    require(isinstance(host_tools, list) and
            len(host_tools) == len(EXPECTED_CONTROLLER_TOOLS) and
            all(isinstance(item, dict) and
                isinstance(item.get("label"), str) for item in host_tools) and
            {item.get("label") for item in host_tools} ==
            set(EXPECTED_CONTROLLER_TOOLS),
            "malformed direct runtime controller host-tool closure")
    for item in host_tools:
        retained_digest(item, {
            "label", "invocation_path", "resolved_path", "symlink_target",
            "path", "bytes", "sha256", "md5",
        }, "controller host tool")
        label = item["label"]
        expected = EXPECTED_CONTROLLER_TOOLS[label]
        require(all(item[field] == expected[field] for field in (
                    "invocation_path", "resolved_path", "symlink_target",
                    "bytes", "sha256",
                )) and item["path"] == (
                    f"controller/host-tools/{label}-" +
                    Path(expected["resolved_path"]).name
                ), f"direct runtime controller host tool differs: {label}")


def _validate_direct_evidence_artifact(
    artifact: dict[str, Any], *, receipt: bool,
    evidence_schema: int,
    log_path: Path | None = None,
    runtime_executable_path: Path | None = None,
) -> None:
    """Validate one exact, disjoint direct-attempt evidence schema."""
    require(evidence_schema in (4, 5), "unsupported direct evidence schema")
    attempt_fields = (
        DIRECT_V5_ATTEMPT_FIELDS
        if evidence_schema == 5 else DIRECT_ATTEMPT_FIELDS
    )
    receipt_only_fields = (
        DIRECT_V5_RECEIPT_ONLY_FIELDS
        if evidence_schema == 5 else DIRECT_RECEIPT_ONLY_FIELDS
    )
    expected_fields = (
        attempt_fields | receipt_only_fields if receipt else attempt_fields
    )
    require(isinstance(artifact, dict) and set(artifact) == expected_fields,
            "malformed direct runtime evidence envelope")
    require(type(artifact["schema"]) is int and
            artifact["schema"] == evidence_schema,
            f"direct runtime evidence requires disjoint schema {evidence_schema}")
    require(artifact.get("kind") == "candle-flyspeck-compiled-stratum-attempt",
            "wrong direct runtime evidence kind")
    expected_claim = (
        DIRECT_V5_EVIDENCE_CLAIM
        if evidence_schema == 5 else DIRECT_EVIDENCE_CLAIM
    )
    require(artifact.get("claim") == expected_claim and
            isinstance(artifact.get("diagnostic_only"), bool) and
            isinstance(artifact.get("started_utc"), str) and
            artifact["started_utc"].endswith("Z"),
            "malformed direct runtime evidence identity")
    try:
        started = dt.datetime.fromisoformat(
            artifact["started_utc"].removesuffix("Z") + "+00:00"
        )
    except ValueError as error:
        raise ContractError("malformed direct runtime start time") from error
    require(started.tzinfo is not None,
            "direct runtime start time lacks timezone")
    require(type(artifact.get("timeout_seconds")) is int and
            artifact["timeout_seconds"] > 0,
            "malformed direct runtime timeout")
    limits = artifact.get("resource_limits")
    require(isinstance(limits, dict) and set(limits) == {
                "cpu_seconds", "address_space_bytes", "output_file_bytes",
            } and all(type(limits[field]) is int and limits[field] > 0
                      for field in limits),
            "malformed direct runtime resource limits")
    require(artifact.get("fresh_process_replay_from_action_zero") is True and
            artifact.get("cooperative_build_run_lock_held") is True and
            artifact.get("concurrent_mutation_model") == (
                "cooperating build/launcher processes serialized; hostile "
                "same-user path mutation is outside this evidence model"
            ) and artifact.get("process_state_checkpoint") is None and
            artifact.get("runtime_environment_policy") == (
                "minimal PATH/LC_ALL=C/CML sizes; reject LD_*, GLIBC_TUNABLES, "
                "BASH_ENV, and ENV"
            ), "malformed direct runtime execution policy")
    lock = artifact.get("runtime_lock")
    require(isinstance(lock, dict) and set(lock) == {
                "path", "object", "mode", "device", "inode",
            } and exact_absolute_path(lock["path"]) and
            lock["object"] == "directory_inode" and lock["mode"] == "shared" and
            type(lock["device"]) is int and lock["device"] >= 0 and
            type(lock["inode"]) is int and lock["inode"] > 0,
            "malformed direct runtime lock binding")
    environment = artifact.get("runtime_environment")
    require(isinstance(environment, dict) and
            set(environment) >= {"LC_ALL", "PATH"} and
            set(environment) <= {
                "LC_ALL", "PATH", "CML_HEAP_SIZE", "CML_STACK_SIZE",
            } and environment["LC_ALL"] == "C" and
            environment["PATH"] == "/usr/bin:/bin" and
            all(isinstance(value, str) for value in environment.values()) and
            all(re.fullmatch(r"[1-9][0-9]*", environment[name]) is not None
                for name in ("CML_HEAP_SIZE", "CML_STACK_SIZE")
                if name in environment),
            "malformed direct runtime environment")
    inputs = artifact.get("inputs")
    require(isinstance(inputs, dict) and set(inputs) == DIRECT_INPUT_FIELDS,
            "malformed direct runtime input closure")

    def digest_record(value: object, label: str, *, path: bool = False) -> None:
        fields = {"bytes", "sha256", "md5"} | ({"path"} if path else set())
        require(isinstance(value, dict) and set(value) == fields and
                type(value["bytes"]) is int and value["bytes"] >= 0 and
                isinstance(value["sha256"], str) and
                re.fullmatch(r"[0-9a-f]{64}", value["sha256"]) is not None and
                isinstance(value["md5"], str) and
                re.fullmatch(r"[0-9a-f]{32}", value["md5"]) is not None and
                (not path or
                 (isinstance(value["path"], str) and bool(value["path"]))),
                f"malformed direct runtime {label} record")

    for label in sorted(DIRECT_INPUT_FIELDS - {
        "controller_execution", "authenticated_prefix", "runtime_executable",
    }):
        digest_record(inputs[label], f"input {label}")
    digest_record(inputs["authenticated_prefix"],
                  "authenticated prefix", path=True)
    prefix_path = inputs["authenticated_prefix"]["path"]
    require(Path(prefix_path) != Path(".") and
            not Path(prefix_path).is_absolute() and
            ".." not in Path(prefix_path).parts and
            Path(prefix_path).as_posix() == prefix_path,
            "unsafe direct runtime authenticated prefix path")
    digest_record(inputs["runtime_executable"],
                  "runtime executable", path=True)
    runtime_executable = inputs["runtime_executable"]["path"]
    require(exact_absolute_path(runtime_executable) and
            Path(runtime_executable).parts[-5:] == (
                "snapshot", "candle", "candle", "build", "cake",
            ), "malformed direct runtime executable binding")
    repositories = artifact.get("repositories")
    require(isinstance(repositories, dict) and set(repositories) == {
                "candle", "flyspeck",
            } and all(isinstance(value, str) and
                      re.fullmatch(r"[0-9a-f]{40}", value) is not None
                      for value in repositories.values()),
            "malformed direct runtime repository binding")
    validate_direct_controller_binding(
        inputs["controller_execution"], repositories["candle"],
    )
    contract = artifact.get("evidence_contract")
    base_contract = {
        "schema", "allowed_action_outcomes",
        "physical_loader_cache_skip_allowed",
        "logical_source_closure_policy", "logical_source_closure_order",
        "selected_loadt_ledger_delta_included",
        "physical_loader_cache_trace_included",
        "physical_source_trace_protocol", "pre_trace_control_exclusion",
        "s2_s3_approval_included",
    }
    v5_contract = {
        "dependency_history_protocol", "dependency_history_policy",
        "semantic_coverage_policy", "dependency_history_is_kernel_trace",
        "semantic_approval_included", "pft_used",
    }
    require(isinstance(contract, dict) and
            set(contract) == base_contract | (
                v5_contract if evidence_schema == 5 else set()
            ) and
            contract.get("schema") ==
            f"candle-flyspeck-direct-runtime-evidence-v{evidence_schema}" and
            contract.get("allowed_action_outcomes") == list(ACTION_OUTCOMES) and
            contract.get("physical_loader_cache_skip_allowed") ==
            "only loader-authenticated needs cache-skip events" and
            contract.get("logical_source_closure_policy") ==
            SOURCE_CLOSURE_POLICY and
            contract.get("logical_source_closure_order") ==
            SOURCE_CLOSURE_ORDER and
            contract.get("selected_loadt_ledger_delta_included") is True and
            contract.get("physical_loader_cache_trace_included") is True and
            contract.get("physical_source_trace_protocol") ==
            SOURCE_TRACE_PROTOCOL and
            contract.get("pre_trace_control_exclusion") ==
            "control:runtime-config" and
            contract.get("s2_s3_approval_included") is False and
            (evidence_schema == 4 or (
                contract.get("dependency_history_protocol") ==
                DEPENDENCY_HISTORY_PREFIX and
                contract.get("dependency_history_policy") ==
                DEPENDENCY_HISTORY_POLICY and
                contract.get("semantic_coverage_policy") ==
                SEMANTIC_COVERAGE_POLICY and
                contract.get("dependency_history_is_kernel_trace") is False and
                contract.get("semantic_approval_included") is False and
                contract.get("pft_used") is False
            )),
            f"malformed direct runtime evidence-v{evidence_schema} contract")
    action_count = artifact.get("action_count")
    require(type(action_count) is int and action_count >= 0,
            "malformed direct runtime action count")
    boundary_id = artifact.get("boundary_id")
    require(isinstance(boundary_id, str) and boundary_id,
            "malformed direct runtime boundary id")
    expected_actions = artifact.get("expected_action_events")
    require(isinstance(expected_actions, list) and
            len(expected_actions) == action_count and
            artifact.get("ordered_expected_action_sha256") ==
            canonical_sha256(expected_actions),
            "malformed authenticated action-event projection")
    for index, action in enumerate(expected_actions):
        require(isinstance(action, dict) and set(action) == {
                    "index", "source_sha256", "logical_source_delta",
                    "logical_source_delta_sha256",
                } and type(action.get("index")) is int and
                action["index"] == index and
                isinstance(action.get("source_sha256"), str) and
                re.fullmatch(r"[0-9a-f]{64}",
                             action["source_sha256"]) is not None,
                f"malformed authenticated action-event projection: {index}")
        delta = action["logical_source_delta"]
        require(isinstance(delta, list) and bool(delta) and
                action["logical_source_delta_sha256"] == canonical_sha256(delta),
                f"malformed authenticated logical-source delta: {index}")
        for delta_index, record in enumerate(delta):
            require(isinstance(record, dict) and set(record) == {
                        "key", "classification", "source_sha256",
                        "identity_basename", "identity_md5",
                    } and isinstance(record.get("key"), str) and
                    bool(record["key"]) and
                    record.get("classification") == (
                        "observed-outer-source" if delta_index == 0 else
                        "observed-nested-source"
                    ) and
                    isinstance(record.get("source_sha256"), str) and
                    re.fullmatch(r"[0-9a-f]{64}",
                                 record["source_sha256"]) is not None and
                    isinstance(record.get("identity_basename"), str) and
                    bool(record["identity_basename"]) and
                    isinstance(record.get("identity_md5"), str) and
                    re.fullmatch(r"[0-9a-f]{32}",
                                 record["identity_md5"]) is not None,
                    f"malformed logical-source delta record: {index}:{delta_index}")
        require(delta[0]["source_sha256"] == action["source_sha256"],
                f"logical-source delta outer digest mismatch: {index}")

    expected = artifact.get("expected_logical_source_closure")
    expected_fields = {
        "schema", "kind", "policy", "order", "completed_action_count",
        "final_target_selected", "record_count", "ordered_record_sha256",
        "records", "physical_loader_cache_trace", "execution_observation",
        "self_certifies_nested_execution", "s2_s3_evidence",
    }
    require(isinstance(expected, dict) and set(expected) == expected_fields and
            type(expected.get("schema")) is int and
            expected["schema"] == 3 and expected.get("kind") ==
            "candle-flyspeck-selected-nested-logical-source-closure" and
            expected.get("policy") == SOURCE_CLOSURE_POLICY and
            expected.get("order") == SOURCE_CLOSURE_ORDER and
            type(expected.get("completed_action_count")) is int and
            expected["completed_action_count"] == action_count and
            expected.get("final_target_selected") is
            boundary_id.startswith("07-") and
            expected.get("physical_loader_cache_trace") is False and
            expected.get("execution_observation") == SOURCE_CLOSURE_OBSERVATION and
            expected.get("self_certifies_nested_execution") is False and
            expected.get("s2_s3_evidence") is False,
            "malformed direct runtime expected closure")
    expected_records = expected.get("records")
    require(isinstance(expected_records, list) and
            type(expected.get("record_count")) is int and
            expected["record_count"] == len(expected_records) and
            isinstance(expected.get("ordered_record_sha256"), str) and
            re.fullmatch(r"[0-9a-f]{64}",
                         expected["ordered_record_sha256"]) is not None and
            expected.get("ordered_record_sha256") ==
            canonical_sha256(expected_records),
            "malformed direct runtime expected closure records")
    previous_key: str | None = None
    for index, record in enumerate(expected_records):
        require(isinstance(record, dict) and set(record) == {
                    "index", "key", "classification", "source_sha256", "source_md5",
                    "execution_normalization",
                } and type(record.get("index")) is int and
                record["index"] == index and
                isinstance(record.get("key"), str) and record["key"] and
                record.get("classification") in SOURCE_CLOSURE_CLASSIFICATIONS and
                (previous_key is None or previous_key < record["key"]) and
                isinstance(record.get("source_sha256"), str) and
                re.fullmatch(r"[0-9a-f]{64}",
                             record["source_sha256"]) is not None and
                isinstance(record.get("source_md5"), str) and
                re.fullmatch(r"[0-9a-f]{32}",
                             record["source_md5"]) is not None,
                f"malformed direct runtime expected closure record: {index}")
        normalization = record.get("execution_normalization")
        require(normalization is None or (
                    isinstance(normalization, dict) and set(normalization) == {
                        "id", "normalized_sha256", "normalized_md5",
                    } and isinstance(normalization.get("id"), str) and
                    bool(normalization["id"]) and
                    isinstance(normalization.get("normalized_sha256"), str) and
                    re.fullmatch(r"[0-9a-f]{64}",
                                 normalization["normalized_sha256"])
                    is not None and
                    isinstance(normalization.get("normalized_md5"), str) and
                    re.fullmatch(r"[0-9a-f]{32}",
                                 normalization["normalized_md5"])
                    is not None
                ), f"malformed closure normalization record: {index}")
        previous_key = record["key"]
    closure_by_key = {record["key"]: record for record in expected_records}
    for action in expected_actions:
        for delta_record in action["logical_source_delta"]:
            closure_record = closure_by_key.get(delta_record["key"])
            require(isinstance(closure_record, dict) and
                    closure_record["classification"] ==
                    delta_record["classification"] and
                    closure_record["source_sha256"] ==
                    delta_record["source_sha256"] and
                    closure_record["source_md5"] ==
                    delta_record["identity_md5"],
                    "action logical-source delta differs from expected closure")
    expected_trace = validate_source_trace_contract(
        artifact.get("expected_physical_source_trace")
    )
    require(expected_trace["nonce"] == artifact.get("attempt_nonce"),
            "physical source trace nonce differs from attempt")
    trace_required_keys = {
        record["key"] for record in expected_records
        if record["classification"] != "derivation-only-input"
    }
    trace_required_keys.update(SOURCE_TRACE_TOP_LEVEL_CONTROLS)
    if fingerprint_requests(boundary_id):
        trace_required_keys.add("control:fingerprint-serializer")
    require(expected_trace["required_keys"] == sorted(trace_required_keys),
            "physical source trace differs from logical source closure")
    trace_bindings_by_key: dict[str, list[dict[str, Any]]] = {}
    for binding in expected_trace["bindings"]:
        trace_bindings_by_key.setdefault(binding["key"], []).append(binding)
    for record in expected_records:
        if record["classification"] == "derivation-only-input":
            continue
        bindings = trace_bindings_by_key.get(record["key"])
        require(isinstance(bindings, list) and bindings,
                f"logical source lacks physical trace binding: {record['key']}")
        normalization = record["execution_normalization"]
        expected_selected_sha256 = (
            record["source_sha256"] if normalization is None else
            normalization["normalized_sha256"]
        )
        expected_normalization = (
            "-" if normalization is None else normalization["id"]
        )
        require(all(
            binding["source_md5"] == record["source_md5"] and
            binding["source_sha256"] == record["source_sha256"] and
            binding["selected_sha256"] == expected_selected_sha256 and
            binding["normalization"] == expected_normalization
            for binding in bindings
        ), f"logical and physical source identities differ: {record['key']}")
    semantic_plan: dict[str, Any] | None = None
    if evidence_schema == 5:
        semantic_plan = validate_semantic_evidence_plan(
            artifact.get("semantic_evidence_plan"), boundary_id, action_count,
            expected, expected_trace, {
                "plan_sha256": inputs["plan"]["sha256"],
                "host_materialization_sha256":
                    inputs["host_materialization"]["sha256"],
                "manifest_sha256": inputs["manifest"]["sha256"],
            },
        )
    if not receipt:
        require(artifact.get("state") == "running",
                "initial direct runtime artifact is not running")
        return
    require(runtime_executable_path is not None and
            str(Path(runtime_executable_path)) == runtime_executable,
            "direct runtime receipt validation requires its executable bytes")
    validate_file(
        Path(runtime_executable_path), inputs["runtime_executable"],
        "direct runtime executable",
    )
    executable_mode = Path(runtime_executable_path).stat().st_mode
    require(executable_mode & 0o111 != 0 and executable_mode & 0o222 == 0,
            "direct runtime executable mode is not immutable executable")
    initial_projection = {field: artifact[field] for field in attempt_fields}
    initial_projection["state"] = "running"
    digest_record(artifact["initial_attempt"], "initial attempt", path=True)
    require(exact_json_equal(artifact["initial_attempt"], {
                "path": "attempt.json",
                **data_record(json_bytes(initial_projection)),
            }), "receipt differs from immutable initial attempt")
    finished_utc = artifact.get("finished_utc")
    require(isinstance(finished_utc, str) and finished_utc.endswith("Z"),
            "malformed direct runtime finish time")
    try:
        finished = dt.datetime.fromisoformat(
            finished_utc.removesuffix("Z") + "+00:00"
        )
    except ValueError as error:
        raise ContractError("malformed direct runtime finish time") from error
    require(finished >= started,
            "direct runtime finish precedes start")
    command = artifact.get("command")
    require(command == [runtime_executable, "--candle"],
            "malformed direct runtime command")
    log_record = artifact.get("log")
    if log_record is not None:
        digest_record(log_record, "log", path=True)
        require(log_record["path"] == "candle.log",
                "wrong direct runtime log path")
    resources = artifact.get("child_resources")
    if resources is not None:
        require(isinstance(resources, dict) and set(resources) == {
                    "user_cpu_seconds", "system_cpu_seconds", "max_rss_kib",
                    "major_page_faults", "minor_page_faults",
                } and
                all(isinstance(resources[field], (int, float)) and
                    not isinstance(resources[field], bool) and
                    math.isfinite(resources[field]) and
                    resources[field] >= 0
                    for field in ("user_cpu_seconds", "system_cpu_seconds")) and
                all(type(resources[field]) is int and resources[field] >= 0
                    for field in (
                        "max_rss_kib", "major_page_faults", "minor_page_faults",
                    )), "malformed direct runtime child resources")
    require(artifact.get("state") in ("completed", "failed"),
            "direct runtime receipt state mismatch")
    require(artifact.get("s2_s3_evidence") is False,
            "direct runtime receipt must remain nonpromotable")
    timed_out = artifact.get("timed_out")
    exit_code = artifact.get("exit_code")
    postflight = artifact.get("postflight_reauthenticated")
    marker_count = artifact.get("action_markers_validated")
    validation_error = artifact.get("validation_error")
    require(isinstance(timed_out, bool) and
            (exit_code is None or type(exit_code) is int) and
            isinstance(postflight, bool) and
            type(marker_count) is int
            and 0 <= marker_count <= action_count,
            "malformed direct runtime receipt state fields")

    events = artifact.get("action_events")
    exact_events = events is not None
    if events is not None:
        require(isinstance(events, list) and len(events) == action_count,
                "receipt action-event count mismatch")
        for index, (event, expected_action) in enumerate(zip(
            events, expected_actions, strict=True,
        )):
            require(isinstance(event, dict) and set(event) == {
                        "index", "source_sha256",
                        "logical_source_delta_sha256", "outcome",
                    } and type(event.get("index")) is int and
                    event["index"] == index and
                    event.get("source_sha256") ==
                    expected_action["source_sha256"] and
                    event.get("logical_source_delta_sha256") ==
                    expected_action["logical_source_delta_sha256"] and
                    event.get("outcome") in ACTION_OUTCOMES,
                    f"receipt action event differs from authenticated action: {index}")

    observed = artifact.get("logical_source_closure")
    exact_closure = observed is not None
    if observed is not None:
        require(isinstance(observed, dict) and
                observed.get("records") is not None and
                observed.get("ordered_record_sha256") ==
                canonical_sha256(observed["records"]) and
                exact_json_equal(observed, {
                    **expected,
                    "status": "expected-closure-emitted-unapproved",
                }),
                "receipt logical source closure differs from authenticated expectation")

    physical_trace = artifact.get("physical_source_trace")
    exact_physical_trace = physical_trace is not None
    if physical_trace is not None:
        validate_source_trace_observation(expected_trace, physical_trace)

    fingerprints = artifact.get("semantic_fingerprints")
    exact_fingerprints = fingerprints is not None
    if fingerprints is not None:
        expected_names = fingerprint_requests(boundary_id)
        if not expected_names:
            require(exact_json_equal(fingerprints, {
                        "status": "not_requested",
                        "approved_reference_present": False,
                        "serializer": None,
                        "theorems": [],
                        "post_state": None,
                    }), "unexpected fingerprint state at unrequested boundary")
        else:
            require(isinstance(fingerprints, dict) and set(fingerprints) == {
                        "status", "approved_reference_present", "serializer",
                        "theorems", "post_state",
                    } and fingerprints.get("status") == "observed_uncompared" and
                    fingerprints.get("approved_reference_present") is False,
                    "malformed requested-boundary fingerprint state")
            serializer = fingerprints.get("serializer")
            inputs = artifact.get("inputs")
            input_serializer = (
                inputs.get("fingerprint_serializer")
                if isinstance(inputs, dict) else None
            )
            require(isinstance(serializer, dict) and set(serializer) == {
                        "path", "sha256",
                    } and serializer.get("path") ==
                    FINGERPRINT_RELATIVE.as_posix() and
                    isinstance(serializer.get("sha256"), str) and
                    isinstance(input_serializer, dict) and
                    serializer.get("sha256") == input_serializer.get("sha256") and
                    re.fullmatch(r"[0-9a-f]{64}",
                                 serializer["sha256"]) is not None,
                    "requested-boundary fingerprint serializer mismatch")
            theorems = fingerprints.get("theorems")
            post_state = fingerprints.get("post_state")
            require(isinstance(theorems, list) and
                    [record.get("name") for record in theorems
                     if isinstance(record, dict)] == expected_names and
                    isinstance(post_state, dict),
                    "requested-boundary fingerprint identity mismatch")
            theorem_fields = {
                "name", "theorem_sha256", "hypotheses_sha256",
                "conclusion_sha256", "global_axioms_sha256",
                "hypothesis_count", "global_axiom_count",
            }
            for record in theorems:
                require(isinstance(record, dict) and
                        set(record) == theorem_fields and
                        isinstance(record.get("name"), str) and
                        type(record.get("hypothesis_count")) is int and
                        record["hypothesis_count"] == 0 and
                        type(record.get("global_axiom_count")) is int and
                        record["global_axiom_count"] == 3 and
                        all(isinstance(record.get(field), str) and
                            re.fullmatch(r"[0-9a-f]{64}", record[field])
                            is not None for field in (
                                "theorem_sha256", "hypotheses_sha256",
                                "conclusion_sha256", "global_axioms_sha256",
                            )), "malformed theorem fingerprint receipt record")
            state_fields = {
                "kernel_state_sha256", "type_constants_sha256",
                "term_constants_sha256", "definitions_sha256",
                "global_axioms_sha256", "type_constant_count",
                "term_constant_count", "definition_count",
                "global_axiom_count",
            }
            require(set(post_state) == state_fields and
                    post_state.get("global_axiom_count") == 3 and
                    all(type(post_state.get(field)) is int and
                        post_state[field] >= 0 for field in (
                            "type_constant_count", "term_constant_count",
                            "definition_count", "global_axiom_count",
                        )) and
                    all(isinstance(post_state.get(field), str) and
                        re.fullmatch(r"[0-9a-f]{64}", post_state[field])
                        is not None
                        for field in (
                            "kernel_state_sha256", "type_constants_sha256",
                            "term_constants_sha256", "definitions_sha256",
                            "global_axioms_sha256",
                        )) and
                    all(record["global_axioms_sha256"] ==
                        post_state["global_axioms_sha256"]
                        for record in theorems),
                    "malformed post-state fingerprint receipt record")

    exact_dependency_history = evidence_schema == 4
    exact_semantic_coverage = evidence_schema == 4
    dependency_history: dict[str, Any] | None = None
    semantic_coverage: dict[str, Any] | None = None
    if evidence_schema == 5:
        dependency_value = artifact.get("dependency_history")
        exact_dependency_history = dependency_value is not None
        if dependency_value is not None:
            dependency_history = validate_dependency_history_observation(
                dependency_value, dependency_history_requests(boundary_id),
                boundary_id, artifact["attempt_nonce"],
            )
        coverage_value = artifact.get("semantic_coverage")
        exact_semantic_coverage = coverage_value is not None
        if coverage_value is not None:
            require(semantic_plan is not None and
                    observed is not None and physical_trace is not None and
                    fingerprints is not None and dependency_history is not None,
                    "semantic coverage lacks its authenticated observations")
            semantic_coverage = derive_semantic_coverage(
                semantic_plan, observed, physical_trace, fingerprints,
                dependency_history,
            )
            require(exact_json_equal(coverage_value, semantic_coverage),
                    "receipt semantic coverage differs from exact observations")

    complete_success = (
        validation_error is None and timed_out is False and
        exit_code == 0 and postflight is True and log_record is not None and
        resources is not None and
        marker_count == action_count and exact_events and
        exact_closure and exact_physical_trace and exact_fingerprints and
        exact_dependency_history and exact_semantic_coverage
    )
    if artifact["state"] == "completed":
        require(complete_success and log_record["bytes"] > 0,
                "completed direct runtime receipt violates success invariants")
    else:
        require(isinstance(validation_error, str) and bool(validation_error) and
                marker_count == 0,
                "failed direct runtime receipt violates failure invariants")
        require(not complete_success,
                "failed direct runtime receipt has complete success evidence")
    if log_record is None:
        require(log_path is None,
                "direct runtime log path supplied without a log record")
        return
    require(log_path is not None,
            "direct runtime receipt validation requires its log bytes")
    bound_log_path = Path(log_path)
    require(bound_log_path.name == "candle.log",
            "direct runtime log filename mismatch")
    validate_file(bound_log_path, log_record, "direct runtime log")
    require(bound_log_path.stat().st_mode & 0o222 == 0,
            "direct runtime log is writable")
    if artifact["state"] != "completed":
        return
    try:
        log_text = bound_log_path.read_text(encoding="utf-8", errors="strict")
    except (OSError, UnicodeError) as error:
        raise ContractError(f"cannot read direct runtime log: {error}") from error
    require(exact_json_equal(
                validate_source_trace(log_text, expected_trace), physical_trace,
            ),
            "receipt physical source trace differs from bound log")
    require(exact_json_equal(validate_log(
                log_text, expected_actions, boundary_id,
                artifact["attempt_nonce"], fingerprint_requests(boundary_id),
                (dependency_history_requests(boundary_id)
                 if evidence_schema == 5 else []),
            ), events),
            "receipt action events differ from bound log")
    require(exact_json_equal(validate_logical_source_closure(
                log_text, expected, boundary_id, artifact["attempt_nonce"],
            ), observed),
            "receipt logical source closure differs from bound log")
    theorem_names = fingerprint_requests(boundary_id)
    if theorem_names:
        try:
            parsed = reference_protocol._read_fingerprint_records(
                bound_log_path, tuple(theorem_names), "audited",
            )
        except (OSError, UnicodeError, reference_protocol.LoadFailure) as error:
            raise ContractError(str(error)) from error
        require(parsed["status"] == "observed_uncompared" and
                parsed["expected_identities_present"] is False and
                parsed["approval_sha256"] is None and
                parsed["mapping_status"] == "audited",
                "bound log fingerprint protocol returned an unexpected state")
        log_fingerprints = {
            "status": parsed["status"],
            "approved_reference_present": False,
            "serializer": parsed["serializer"],
            "theorems": parsed["theorems"],
            "post_state": parsed["post_state"],
        }
    else:
        log_fingerprints = parse_fingerprints(
            bound_log_path, [], Path("unused-for-unrequested-boundary"),
        )
    require(exact_json_equal(log_fingerprints, fingerprints),
            "receipt fingerprints differ from bound log")
    if evidence_schema == 5:
        log_dependency_history = parse_dependency_history_text(
            log_text, dependency_history_requests(boundary_id), boundary_id,
            artifact["attempt_nonce"],
        )
        require(exact_json_equal(log_dependency_history, dependency_history),
                "receipt dependency history differs from bound log")


def validate_direct_evidence_v4_artifact(
    artifact: dict[str, Any], *, receipt: bool,
    log_path: Path | None = None,
    runtime_executable_path: Path | None = None,
) -> None:
    """Validate the permanently nonpromotable direct evidence-v4 schema."""
    _validate_direct_evidence_artifact(
        artifact, receipt=receipt, evidence_schema=4, log_path=log_path,
        runtime_executable_path=runtime_executable_path,
    )


def validate_direct_evidence_v5_artifact(
    artifact: dict[str, Any], *, receipt: bool,
    log_path: Path | None = None,
    runtime_executable_path: Path | None = None,
) -> None:
    """Validate direct evidence-v5 observations without granting approval."""
    _validate_direct_evidence_artifact(
        artifact, receipt=receipt, evidence_schema=5, log_path=log_path,
        runtime_executable_path=runtime_executable_path,
    )


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def safe_relative(value: str, label: str) -> Path:
    relative = Path(value)
    require(not relative.is_absolute() and ".." not in relative.parts,
            f"unsafe {label} path: {value}")
    return relative


def snapshot_copy(
    source: Path,
    root: Path,
    relative_value: str,
    expected: dict[str, Any],
) -> dict[str, Any]:
    relative = safe_relative(relative_value, "snapshot")
    require(source.is_file() and not source.is_symlink(),
            f"snapshot source is not an ordinary file: {source}")
    destination = root / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        require(destination.is_file() and not destination.is_symlink(),
                f"snapshot destination collision: {destination}")
        require(hash_file(destination) == hash_file(source),
                f"non-identical snapshot destination collision: {destination}")
    else:
        shutil.copyfile(source, destination)
    destination.chmod(0o444)
    observed = {"path": relative.as_posix(), **hash_file(destination)}
    for field in ("bytes", "sha256", "md5"):
        if field in expected:
            require(observed[field] == expected[field],
                    f"snapshot {field} mismatch: {destination}")
    return observed


def snapshot_bytes(
    source: bytes,
    root: Path,
    relative_value: str,
    expected: dict[str, Any],
) -> dict[str, Any]:
    """Archive immutable bytes that were already used for Python compilation."""
    relative = safe_relative(relative_value, "snapshot")
    destination = root / relative
    require(not destination.exists() and not destination.is_symlink(),
            f"snapshot byte destination collision: {destination}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_bytes(source)
    destination.chmod(0o444)
    observed = {"path": relative.as_posix(), **hash_file(destination)}
    for field in ("bytes", "sha256", "md5"):
        if field in expected:
            require(observed[field] == expected[field],
                    f"snapshot byte {field} mismatch: {destination}")
    return observed


def create_runtime_snapshot(
    output_root: Path,
    candle_root: Path,
    prepared: dict[str, Any],
    linked: dict[str, Any],
    controller_execution: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Copy every runtime-consumed byte into one disjoint read-only tree."""
    snapshot_root = output_root / "snapshot"
    candle_snapshot = snapshot_root / "candle"
    flyspeck_snapshot = snapshot_root / "flyspeck"
    overlay_snapshot = snapshot_root / "overlay"
    generated_snapshot = snapshot_root / "generated"
    controller_snapshot = snapshot_root / "controller"
    records_by_path: dict[str, dict[str, Any]] = {}

    def add_record(prefix: str, classification: str,
                   record: dict[str, Any]) -> None:
        snapshot_relative = safe_relative(
            (Path(prefix) / record["path"]).as_posix(), "snapshot record",
        ).as_posix()
        candidate = {
            "path": snapshot_relative,
            "bytes": record["bytes"],
            "sha256": record["sha256"],
            "md5": record["md5"],
            "classes": [classification],
        }
        previous = records_by_path.get(snapshot_relative)
        if previous is None:
            records_by_path[snapshot_relative] = candidate
        else:
            require(
                all(previous[field] == candidate[field]
                    for field in ("bytes", "sha256", "md5")),
                f"non-identical snapshot record collision: {snapshot_relative}",
            )
            if classification not in previous["classes"]:
                previous["classes"].append(classification)

    source_runtime = []
    for binding in prepared["source_runtime"]:
        destination_root = candle_snapshot if binding["repository"] == "candle" else flyspeck_snapshot
        record = snapshot_copy(
            Path(binding["absolute"]), destination_root, binding["path"], binding,
        )
        add_record(binding["repository"], f"source:{binding['repository']}", record)
        source_runtime.append({
            **binding,
            "absolute": str(destination_root / binding["path"]),
        })

    source_alias_runtime = []
    for item in prepared["source_alias_runtime"]:
        alias_root = (
            candle_snapshot
            if item["alias_repository"] == "candle" else flyspeck_snapshot
        )
        canonical_root = (
            candle_snapshot
            if item["canonical_repository"] == "candle" else flyspeck_snapshot
        )
        alias = loader_filename_concat(alias_root, item["alias_relative"])
        canonical = canonical_root / safe_relative(
            item["canonical_relative"], "snapshot canonical source alias",
        )
        require(os.path.isfile(alias) and not os.path.islink(alias) and
                Path(alias).resolve(strict=True) == canonical.resolve(strict=True),
                f"snapshot source alias differs from canonical source: {alias}")
        source_alias_runtime.append({
            **item, "alias": alias, "canonical": str(canonical),
        })

    for relative in (SOURCE_DIGEST_RELATIVE, SETUP_RELATIVE, CHECK_RELATIVE,
                     FINGERPRINT_RELATIVE, L2_TARGET_RELATIVE):
        record = snapshot_copy(
            candle_root / relative, candle_snapshot, relative.as_posix(),
            prepared["harness_records"][relative.as_posix()],
        )
        add_record("candle", "runtime-harness", record)

    linked_outputs = linked.get("outputs")
    require(isinstance(linked_outputs, dict), "missing linked output records")
    for name, expected in sorted(linked_outputs.items()):
        source = candle_root / "candle/build" / name
        validate_file(source, expected, f"linked snapshot input {name}")
        record = snapshot_copy(
            source, candle_snapshot, f"candle/build/{name}", expected,
        )
        add_record("candle", "linked-runtime", record)
    # The executable reads these two files relative to its process cwd.
    for name in ("config_enc_str.txt", "candle_boot.ml"):
        record = snapshot_copy(
            candle_root / "candle/build" / name, candle_snapshot, name,
            linked_outputs[name],
        )
        add_record("candle", "linked-root-input", record)
    cake_snapshot = candle_snapshot / "candle/build/cake"
    cake_snapshot.chmod(0o555)

    linked_record_snapshot = candle_snapshot / LINKED_RECORD_RELATIVE
    record = snapshot_copy(
        candle_root / LINKED_RECORD_RELATIVE, candle_snapshot,
        LINKED_RECORD_RELATIVE.as_posix(), prepared["linked_record"],
    )
    add_record("candle", "linked-provenance-record", record)

    bootstrap_record_snapshot = (
        candle_snapshot / "candle/build/bootstrap-provenance.json"
    )
    bootstrap_log_snapshot = candle_snapshot / "candle/build/bootstrap.log"
    bootstrap = load_object(bootstrap_record_snapshot, "linked bootstrap record")
    bootstrap_log = bootstrap.get("bootstrap_log")
    require(isinstance(bootstrap_log, dict) and
            set(bootstrap_log) == {"path", "bytes", "sha256"},
            "malformed linked bootstrap log record")
    require(bootstrap_log.get("path") == "bootstrap.log",
            "linked bootstrap log path is not relocation-safe")
    bootstrap_log_record = {
        field: bootstrap_log[field] for field in ("bytes", "sha256")
    }
    validate_file(
        bootstrap_log_snapshot, bootstrap_log_record,
        "linked bootstrap log snapshot",
    )

    closure = linked.get("runtime_elf_closure")
    require(isinstance(closure, dict), "missing linked ELF closure")
    closure_files = closure.get("files")
    require(isinstance(closure_files, dict), "missing linked ELF closure files")
    for path_string, expected in sorted(closure_files.items()):
        source = Path(path_string)
        relative = f"{expected['sha256'][:16]}-{source.name}"
        record = snapshot_copy(
            source, snapshot_root / "runtime-elf", relative, expected,
        )
        add_record("runtime-elf", "archived-runtime-elf", record)

    normalized_runtime = []
    for item in prepared["normalized_runtime"]:
        output_record = snapshot_copy(
            Path(item["output"]), overlay_snapshot, item["relative"], item,
        )
        add_record("overlay", "normalized", output_record)
        normalized_runtime.append({
            **item,
            "original": str(flyspeck_snapshot / item["original_relative"]),
            "output": str(overlay_snapshot / item["relative"]),
        })

    generated_runtime = []
    for item in prepared["generated_runtime"]:
        destination_root = (
            generated_snapshot
            if item["class"] == "lp-certificate-prepared"
            else flyspeck_snapshot
        )
        record = snapshot_copy(
            Path(item["path"]), destination_root, item["relative"], item,
        )
        prefix = "generated" if item["class"] == "lp-certificate-prepared" else "flyspeck"
        add_record(prefix, f"generated:{item['class']}", record)
        generated_runtime.append({
            **item, "path": str(destination_root / item["relative"]),
        })
    generated_by_relative = {item["relative"]: item for item in generated_runtime}
    lp_certificate_runtime = [
        generated_by_relative[item["relative"]]
        for item in prepared["lp_certificate_runtime"]
    ]

    process_runtime = []
    for item in prepared["process_runtime"]:
        record = snapshot_copy(
            Path(item["path"]), candle_snapshot, item["relative"], item,
        )
        add_record("candle", "process-input", record)
        process_runtime.append({
            **item, "path": str(candle_snapshot / item["relative"]),
        })

    prefix_relative = safe_relative(
        prepared["prefix_record"]["path"], "selected cumulative prefix",
    )
    prefix_snapshot = snapshot_root / "plan"
    prefix_copy_record = snapshot_copy(
        prepared["prefix_path"], prefix_snapshot, prefix_relative.as_posix(),
        prepared["prefix_record"],
    )
    add_record("plan", "authenticated-prefix", prefix_copy_record)

    controller_source_records = []
    for label, source in sorted(controller_execution["local_sources"].items()):
        record = snapshot_bytes(
            source["source_bytes"], controller_snapshot,
            f"python-source/{label}", source,
        )
        add_record("controller", "controller-python-source", record)
        controller_source_records.append({
            "label": label,
            "source_path": source["source_path"],
            "execution_binding": source["execution_binding"],
            "path": f"controller/{record['path']}",
            **{field: record[field] for field in ("bytes", "sha256", "md5")},
        })

    python_runtime = controller_execution["python_runtime"]
    python_executable = python_runtime["executable"]
    python_executable_record = snapshot_copy(
        Path(python_executable["path"]), controller_snapshot,
        f"python-runtime/{Path(python_executable['path']).name}",
        python_executable,
    )
    add_record("controller", "controller-python-executable",
               python_executable_record)
    python_elf_records = []
    for path_string, expected in sorted(
        python_runtime["elf_closure"]["files"].items()
    ):
        source = Path(path_string)
        record = snapshot_copy(
            source, controller_snapshot / "python-runtime-elf",
            f"{expected['sha256'][:16]}-{source.name}", expected,
        )
        add_record("controller/python-runtime-elf",
                   "controller-python-runtime-elf", record)
        python_elf_records.append({
            "source_path": path_string,
            "path": f"controller/python-runtime-elf/{record['path']}",
            **{field: record[field] for field in ("bytes", "sha256", "md5")},
        })

    host_tool_records = []
    for label, tool in sorted(controller_execution["host_tools"].items()):
        record = snapshot_copy(
            Path(tool["resolved_path"]), controller_snapshot,
            f"host-tools/{label}-{Path(tool['resolved_path']).name}", tool,
        )
        add_record("controller", "controller-host-tool", record)
        host_tool_records.append({
            "label": label,
            "invocation_path": tool["invocation_path"],
            "resolved_path": tool["resolved_path"],
            "symlink_target": tool["symlink_target"],
            "path": f"controller/{record['path']}",
            **{field: record[field] for field in ("bytes", "sha256", "md5")},
        })

    controller_record = {
        "source_root": controller_execution["source_root"],
        "direct_script_startup": controller_execution["direct_script_startup"],
        "commit_binding": controller_execution["commit_binding"],
        "python_startup_flags": controller_execution["python_startup_flags"],
        "python_startup_options":
            controller_execution["python_startup_options"],
        "initial_top_level_compilation_in_host_trust_boundary":
            controller_execution[
                "initial_top_level_compilation_in_host_trust_boundary"
            ],
        "local_sources": controller_source_records,
        "python_runtime": {
            "execution_binding": python_runtime["execution_binding"],
            "version": python_runtime["version"],
            "executable": {
                "source_path": python_executable["path"],
                "path": f"controller/{python_executable_record['path']}",
                **{field: python_executable_record[field]
                   for field in ("bytes", "sha256", "md5")},
            },
            "elf_policy": python_runtime["elf_closure"]["policy"],
            "elf_dynamic_path_tags":
                python_runtime["elf_closure"]["dynamic_path_tags"],
            "elf_roles": python_runtime["elf_closure"]["roles"],
            "virtual_elf_objects":
                python_runtime["elf_closure"]["virtual_objects"],
            "elf_objects": python_elf_records,
        },
        "host_tools": host_tool_records,
        "git_environment": controller_execution["git_environment"],
        "broader_python_standard_library_in_host_trust_boundary": True,
    }

    for directory in sorted(
        (path for path in snapshot_root.rglob("*") if path.is_dir()),
        key=lambda path: len(path.parts), reverse=True,
    ):
        directory.chmod(0o555)
    snapshot_root.chmod(0o555)

    runtime = {
        **prepared,
        "candle_runtime_root": candle_snapshot,
        "flyspeck_root": flyspeck_snapshot,
        "overlay_root": overlay_snapshot,
        "generated_root": generated_snapshot,
        "source_runtime": source_runtime,
        "source_alias_runtime": source_alias_runtime,
        "normalized_runtime": normalized_runtime,
        "generated_runtime": generated_runtime,
        "lp_certificate_runtime": lp_certificate_runtime,
        "process_runtime": process_runtime,
        "cake_runtime": cake_snapshot,
        "linked_record_snapshot": linked_record_snapshot,
        "bootstrap_record_snapshot": bootstrap_record_snapshot,
        "bootstrap_log_snapshot": bootstrap_log_snapshot,
        "prefix_path": prefix_snapshot / prefix_relative,
    }
    records = list(records_by_path.values())
    snapshot_record = {
        "schema": 2,
        "kind": "candle-flyspeck-attempt-local-runtime-snapshot",
        "file_count": len(records),
        "ordered_file_sha256": canonical_sha256(records),
        "files": records,
        "roots": {
            "candle": str(candle_snapshot),
            "flyspeck": str(flyspeck_snapshot),
            "normalization_overlay": str(overlay_snapshot),
            "generated_inputs": str(generated_snapshot),
            "controller": str(controller_snapshot),
        },
        "controller_execution": controller_record,
        "files_read_only": True,
        "directories_read_only": True,
    }
    return runtime, snapshot_record


def validate_runtime_snapshot(snapshot: dict[str, Any], output_root: Path) -> None:
    snapshot_root = output_root / "snapshot"
    require(set(snapshot) == {
        "schema", "kind", "file_count", "ordered_file_sha256", "files", "roots",
        "controller_execution", "files_read_only", "directories_read_only",
    }, "malformed runtime snapshot record")
    require(snapshot.get("schema") == 2,
            "unsupported runtime snapshot schema")
    require(snapshot.get("kind") ==
            "candle-flyspeck-attempt-local-runtime-snapshot",
            "wrong runtime snapshot kind")
    require(snapshot.get("files_read_only") is True and
            snapshot.get("directories_read_only") is True,
            "runtime snapshot read-only declaration mismatch")
    require(snapshot.get("roots") == {
        "candle": str(snapshot_root / "candle"),
        "flyspeck": str(snapshot_root / "flyspeck"),
        "normalization_overlay": str(snapshot_root / "overlay"),
        "generated_inputs": str(snapshot_root / "generated"),
        "controller": str(snapshot_root / "controller"),
    }, "runtime snapshot root declaration mismatch")
    records = snapshot.get("files")
    require(isinstance(records, list), "missing snapshot file records")
    require(snapshot.get("file_count") == len(records), "snapshot file count mismatch")
    require(canonical_sha256(records) == snapshot.get("ordered_file_sha256"),
            "snapshot ordered-file digest mismatch")
    expected_files: set[str] = set()
    expected_directories = {"."}
    records_by_path: dict[str, dict[str, Any]] = {}
    for record in records:
        relative = safe_relative(record.get("path", ""), "snapshot file record")
        relative_string = relative.as_posix()
        require(relative_string not in expected_files,
                f"duplicate runtime snapshot record: {relative_string}")
        expected_files.add(relative_string)
        records_by_path[relative_string] = record
        expected_directories.update(
            parent.as_posix() for parent in relative.parents
            if parent != Path(".")
        )
        path = snapshot_root / relative
        validate_file(path, record,
                      f"runtime snapshot {relative_string}")
        require(path.stat().st_mode & 0o222 == 0,
                f"runtime snapshot file is writable: {relative_string}")

    controller = snapshot.get("controller_execution")
    require(isinstance(controller, dict) and set(controller) == {
        "source_root",
        "direct_script_startup",
        "commit_binding",
        "python_startup_flags",
        "python_startup_options",
        "initial_top_level_compilation_in_host_trust_boundary",
        "local_sources",
        "python_runtime",
        "host_tools",
        "git_environment",
        "broader_python_standard_library_in_host_trust_boundary",
    }, "malformed controller execution record")
    require(controller["python_startup_flags"] ==
            EXPECTED_PYTHON_STARTUP_FLAGS,
            "controller Python startup isolation mismatch")
    require(controller["python_startup_options"] ==
            EXPECTED_PYTHON_STARTUP_OPTIONS,
            "controller Python startup options mismatch")
    require(controller[
        "initial_top_level_compilation_in_host_trust_boundary"
    ] is True and controller[
        "broader_python_standard_library_in_host_trust_boundary"
    ] is True, "controller host trust-boundary declaration mismatch")

    def validate_retained(
        item: dict[str, Any], expected_class: str, label: str,
    ) -> None:
        require(isinstance(item, dict), f"malformed retained {label}")
        path = item.get("path")
        require(isinstance(path, str) and path in records_by_path,
                f"missing retained {label} snapshot record")
        inventory = records_by_path[path]
        require(inventory.get("classes") == [expected_class],
                f"wrong retained {label} snapshot class")
        require(all(item.get(field) == inventory.get(field)
                    for field in ("bytes", "sha256", "md5")),
                f"retained {label} digest differs from snapshot inventory")

    sources = controller["local_sources"]
    source_root = Path(controller["source_root"])
    require(source_root.is_absolute(), "controller source root is not absolute")
    direct_startup = controller["direct_script_startup"]
    direct_source = source_root / "flyspeck_stratum_runtime.py"
    require(direct_startup == {
        "module_name": "__main__",
        "spec_is_none": True,
        "cached_is_none": True,
        "argv0": str(direct_source),
        "source_path": str(direct_source),
    }, "controller direct-script startup binding mismatch")
    expected_bindings = {
        "cakeml_artifact_provenance.py":
            "compiled-from-captured-source-bytes",
        "cakeml_bootstrap_transition.py":
            "compiled-from-captured-source-bytes",
        "flyspeck_stratum_plan.py": "compiled-from-captured-source-bytes",
        "flyspeck_stratum_runtime.py":
            "startup-captured-after-initial-compilation",
        "reference_protocol.py": "compiled-from-captured-source-bytes",
        "runtime_lock.py": "compiled-from-captured-source-bytes",
    }
    require(isinstance(sources, list) and
            len(sources) == len(expected_bindings),
            "malformed controller local-source closure")
    require({item.get("label") for item in sources} == set(expected_bindings),
            "unexpected retained controller source set")
    commit_binding = controller["commit_binding"]
    require(isinstance(commit_binding, dict) and set(commit_binding) == {
        "candle_commit", "sources",
    }, "malformed controller commit binding")
    commit_sources = commit_binding["sources"]
    require(isinstance(commit_binding["candle_commit"], str) and
            re.fullmatch(r"[0-9a-f]{40}",
                         commit_binding["candle_commit"]) is not None and
            isinstance(commit_sources, dict) and
            set(commit_sources) == set(expected_bindings),
            "malformed controller commit-source closure")
    for item in sources:
        require(set(item) == {
            "label", "source_path", "execution_binding", "path",
            "bytes", "sha256", "md5",
        }, "malformed retained controller source")
        require(item["execution_binding"] == expected_bindings[item["label"]],
                f"wrong controller source execution binding: {item['label']}")
        require(item["source_path"] == str(source_root / item["label"]) and
                item["path"] == f"controller/python-source/{item['label']}",
                f"wrong retained controller source path: {item['label']}")
        validate_retained(item, "controller-python-source",
                          f"controller source {item['label']}")
        committed = commit_sources[item["label"]]
        require(committed == {
            "repository_path": f"candle/{item['label']}",
            "index_tag": "H",
            "bytes": item["bytes"],
            "sha256": item["sha256"],
            "md5": item["md5"],
        }, f"controller commit-source identity mismatch: {item['label']}")

    python_runtime = controller["python_runtime"]
    require(isinstance(python_runtime, dict) and set(python_runtime) == {
        "execution_binding", "version", "executable", "elf_policy",
        "elf_dynamic_path_tags", "elf_roles", "virtual_elf_objects",
        "elf_objects",
    }, "malformed controller Python runtime record")
    require(python_runtime["execution_binding"] ==
            EXPECTED_PYTHON_RUNTIME["execution_binding"] and
            python_runtime["version"] == EXPECTED_PYTHON_RUNTIME["version"],
            "controller Python execution identity mismatch")
    executable = python_runtime["executable"]
    require(isinstance(executable, dict) and set(executable) == {
        "source_path", "path", "bytes", "sha256", "md5",
    }, "malformed retained controller Python executable")
    expected_executable = EXPECTED_PYTHON_RUNTIME["executable"]
    require(executable["source_path"] == expected_executable["path"] and
            executable["path"] == "controller/python-runtime/python3.12" and
            all(executable[field] == expected_executable[field]
                for field in ("bytes", "sha256")),
            "retained controller Python executable identity mismatch")
    validate_retained(executable, "controller-python-executable",
                      "controller Python executable")
    expected_elf = EXPECTED_PYTHON_RUNTIME["elf_closure"]
    require(python_runtime["elf_policy"] == expected_elf["policy"] and
            python_runtime["elf_dynamic_path_tags"] ==
            expected_elf["dynamic_path_tags"] and
            python_runtime["elf_roles"] == expected_elf["roles"] and
            python_runtime["virtual_elf_objects"] ==
            expected_elf["virtual_objects"],
            "controller Python ELF metadata mismatch")
    elf_objects = python_runtime["elf_objects"]
    require(isinstance(elf_objects, list) and
            {item.get("source_path") for item in elf_objects} ==
            set(expected_elf["files"]),
            "controller Python ELF object set mismatch")
    for item in elf_objects:
        require(isinstance(item, dict) and set(item) == {
            "source_path", "path", "bytes", "sha256", "md5",
        }, "malformed retained controller Python ELF object")
        expected = expected_elf["files"][item["source_path"]]
        source = Path(item["source_path"])
        require(item["path"] == (
            "controller/python-runtime-elf/" +
            f"{expected['sha256'][:16]}-{source.name}"
        ), "wrong retained controller Python ELF object path")
        require(all(item[field] == expected[field]
                    for field in ("bytes", "sha256")),
                "retained controller Python ELF object identity mismatch")
        validate_retained(item, "controller-python-runtime-elf",
                          "controller Python ELF object")

    require(controller["git_environment"] == {
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_TERMINAL_PROMPT": "0",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_OPTIONAL_LOCKS": "0",
    }, "controller Git environment mismatch")
    host_tools = controller["host_tools"]
    require(isinstance(host_tools, list) and
            {item.get("label") for item in host_tools} ==
            set(EXPECTED_CONTROLLER_TOOLS),
            "controller host-tool set mismatch")
    for item in host_tools:
        require(isinstance(item, dict) and set(item) == {
            "label", "invocation_path", "resolved_path", "symlink_target",
            "path", "bytes", "sha256", "md5",
        }, "malformed retained controller host tool")
        label = item["label"]
        expected = EXPECTED_CONTROLLER_TOOLS[label]
        require(all(item[field] == expected[field] for field in (
            "invocation_path", "resolved_path", "symlink_target", "bytes",
            "sha256",
        )), f"retained controller host-tool identity mismatch: {label}")
        require(item["path"] == (
            f"controller/host-tools/{label}-" +
            Path(expected["resolved_path"]).name
        ), f"wrong retained controller host-tool path: {label}")
        validate_retained(item, "controller-host-tool",
                          f"controller host tool {label}")
    observed_files: set[str] = set()
    observed_directories = {"."}
    for path in snapshot_root.rglob("*"):
        relative_string = path.relative_to(snapshot_root).as_posix()
        require(not path.is_symlink(),
                f"runtime snapshot contains a symlink: {relative_string}")
        if path.is_file():
            observed_files.add(relative_string)
        elif path.is_dir():
            observed_directories.add(relative_string)
        else:
            raise ContractError(
                f"runtime snapshot contains a special file: {relative_string}"
            )
    require(observed_files == expected_files,
            "runtime snapshot contains unrecorded or missing files")
    require(observed_directories == expected_directories,
            "runtime snapshot contains unrecorded or missing directories")
    for relative_string in sorted(observed_directories):
        directory = (snapshot_root if relative_string == "." else
                     snapshot_root / relative_string)
        require(directory.stat().st_mode & 0o222 == 0,
                f"runtime snapshot directory is writable: {directory}")


def terminate_process_group(process: subprocess.Popen[bytes]) -> int:
    """Idempotently terminate and reap a fresh-session attempt process."""
    if process.poll() is not None:
        return process.returncode
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        return process.wait(timeout=10)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        return process.wait()


def process_limit_preexec(
    cpu_seconds: int,
    address_space_bytes: int,
    output_file_bytes: int,
) -> Any:
    """Return a child-only resource-limit installer for a fresh process."""
    require(cpu_seconds > 0, "CPU-time limit must be positive")
    require(address_space_bytes > 0, "address-space limit must be positive")
    require(output_file_bytes > 0, "output-file limit must be positive")

    def install() -> None:
        resource.setrlimit(resource.RLIMIT_CPU, (cpu_seconds, cpu_seconds))
        resource.setrlimit(
            resource.RLIMIT_AS, (address_space_bytes, address_space_bytes),
        )
        resource.setrlimit(
            resource.RLIMIT_FSIZE, (output_file_bytes, output_file_bytes),
        )

    return install


def _run_attempt_impl(
    candle_script: Path,
    plan_root: Path,
    boundary_id: str,
    output_root: Path,
    timeout_seconds: int,
    max_cpu_seconds: int,
    max_address_space_gib: int,
    max_output_file_gib: int,
    output_ownership: dict[str, Any] | None = None,
) -> dict[str, Any]:
    require(not Path(output_root).is_symlink(),
            "attempt output path must not be a symlink")
    require(not Path(plan_root).is_symlink(),
            "stratum plan root must not be a symlink")
    candle_script = candle_script.resolve()
    plan_root = plan_root.resolve()
    output_root = output_root.resolve()
    require(candle_script.is_file() and os.access(candle_script, os.X_OK),
            f"Candle launcher is not executable: {candle_script}")
    candle_root = candle_script.parent
    require_direct_script_startup()
    controller_execution = collect_controller_execution(candle_root)
    runtime_lock_handle = runtime_lock.acquire_build_lock(candle_root)

    # This must precede interpretation of the host plan: no runtime attempt is
    # prepared for an unbound or stale executable.
    linked = cakeml_bootstrap_transition.validate_linked_record(candle_root)
    bind_controller_sources_to_commit(
        controller_execution, candle_root, linked["candle_commit"],
    )
    prepared = validate_plan(candle_root, linked, plan_root, boundary_id)

    require(timeout_seconds > 0, "timeout must be positive")
    require(0 < max_cpu_seconds <= 172800,
            "CPU-time limit must be between 1 and 172800 seconds")
    require(0 < max_address_space_gib <= 120,
            "address-space limit must be between 1 and 120 GiB")
    require(0 < max_output_file_gib <= 16,
            "output-file limit must be between 1 and 16 GiB")
    require(not output_root.exists(), f"attempt output already exists: {output_root}")
    require(output_root.parent.is_dir(), f"attempt parent does not exist: {output_root.parent}")
    for label, input_root in (
        ("Candle", candle_root), ("plan", plan_root),
        ("Flyspeck", prepared["flyspeck_root"]),
        ("normalization overlay", prepared["overlay_root"]),
        ("generated inputs", prepared["generated_root"]),
    ):
        require(
            output_root != input_root and not output_root.is_relative_to(input_root),
            f"attempt output must be disjoint from {label} root",
        )
    output_root.mkdir()
    if output_ownership is not None:
        opened = os.stat(output_root, follow_symlinks=False)
        nonce = output_ownership["nonce"]
        marker_path = output_root / ".candle-preflight-owner"
        output_ownership.update({
            "created": True,
            "device": opened.st_dev,
            "inode": opened.st_ino,
            "marker_path": marker_path,
            "marker_ready": False,
        })
        marker_path.write_text(nonce + "\n", encoding="ascii")
        output_ownership["marker_ready"] = True
        marker_path.chmod(0o444)
    runtime_prepared, snapshot_record = create_runtime_snapshot(
        output_root, candle_root, prepared, linked, controller_execution,
    )
    snapshot_record_path = output_root / "snapshot.json"
    atomic_write_json(snapshot_record_path, snapshot_record)
    snapshot_record_path.chmod(0o444)
    validate_runtime_snapshot(snapshot_record, output_root)
    archived_linked = load_object(
        runtime_prepared["linked_record_snapshot"],
        "archived linked provenance",
    )
    require(archived_linked == linked,
            "archived linked provenance differs from validated record")
    cakeml_artifact_provenance.validate_elf_dynamic_closure(
        runtime_prepared["cake_runtime"], linked["runtime_elf_closure"],
    )

    control_root = output_root / "control"
    control_root.mkdir()
    program_path = control_root / "instrumented-prefix.ml"
    config_path = control_root / "runtime-config.ml"
    stdin_path = control_root / "stdin.ml"
    postlude_path = control_root / "postlude.ml"
    log_path = output_root / "candle.log"
    attempt_path = output_root / "attempt.json"
    receipt_path = output_root / "receipt.json"

    nonce = secrets.token_hex(16)
    runtime_prepared["attempt_nonce"] = nonce
    program = instrument_prefix(
        runtime_prepared["prefix_path"].read_bytes(), prepared["actions"], nonce,
    )
    program_path.write_bytes(program)
    program_record = hash_file(program_path)
    runtime_candle_root = runtime_prepared["candle_runtime_root"]
    theorem_names = fingerprint_requests(boundary_id)
    dependency_theorem_names = dependency_history_requests(boundary_id)
    logical_source_closure = prepared["logical_source_closure"]
    write_postlude(
        postlude_path, runtime_candle_root, boundary_id, theorem_names, nonce,
        logical_source_closure, dependency_theorem_names,
    )
    source_trace_contract = build_source_trace_contract(
        runtime_prepared, logical_source_closure, program_path, postlude_path,
        theorem_names, nonce,
    )
    runtime_prepared["source_trace_contract"] = source_trace_contract
    semantic_evidence_plan = build_semantic_evidence_plan(
        boundary_id, len(prepared["actions"]), logical_source_closure,
        source_trace_contract, runtime_prepared["lp_certificate_runtime"], {
            "plan_sha256": prepared["plan_record"]["sha256"],
            "host_materialization_sha256":
                prepared["materialization_record"]["sha256"],
            "manifest_sha256": prepared["manifest_record"]["sha256"],
        },
    )
    write_config(
        config_path, runtime_candle_root, runtime_prepared,
        program_path, program_record["md5"],
    )
    stdin_path.write_text(
        f"#use {ocaml_string(str(config_path))};;\n"
        f"#use {ocaml_string(str(runtime_candle_root / SETUP_RELATIVE))};;\n"
        f"#use {ocaml_string(str(program_path))};;\n"
        f"#use {ocaml_string(str(runtime_candle_root / CHECK_RELATIVE))};;\n"
        f"#use {ocaml_string(str(postlude_path))};;\n",
        encoding="utf-8",
    )
    control_records = {
        "instrumented_prefix": hash_file(program_path),
        "runtime_config": hash_file(config_path),
        "stdin": hash_file(stdin_path),
        "postlude": hash_file(postlude_path),
    }
    for path in (program_path, config_path, stdin_path, postlude_path):
        path.chmod(0o444)
    control_root.chmod(0o555)

    runtime_env = cakeml_artifact_provenance.runtime_environment()
    started = utc_now()
    expected_action_events = [
        {
            "index": index,
            "source_sha256": action["source_sha256"],
            "logical_source_delta": action["logical_source_delta"],
            "logical_source_delta_sha256":
                action["logical_source_delta_sha256"],
        }
        for index, action in enumerate(prepared["actions"])
    ]
    attempt = {
        "schema": 5,
        "kind": "candle-flyspeck-compiled-stratum-attempt",
        "claim": DIRECT_V5_EVIDENCE_CLAIM,
        "state": "running",
        "started_utc": started,
        "boundary_id": boundary_id,
        "diagnostic_only": prepared["diagnostic_only"],
        "attempt_nonce": nonce,
        "action_count": len(prepared["actions"]),
        "ordered_expected_action_sha256": canonical_sha256(
            expected_action_events
        ),
        "expected_action_events": expected_action_events,
        "timeout_seconds": timeout_seconds,
        "resource_limits": {
            "cpu_seconds": max_cpu_seconds,
            "address_space_bytes": max_address_space_gib * GIB,
            "output_file_bytes": max_output_file_gib * GIB,
        },
        "fresh_process_replay_from_action_zero": True,
        "cooperative_build_run_lock_held": True,
        "runtime_lock": runtime_lock_handle.record,
        "concurrent_mutation_model": (
            "cooperating build/launcher processes serialized; hostile same-user "
            "path mutation is outside this evidence model"
        ),
        "process_state_checkpoint": None,
        "evidence_contract": {
            "schema": "candle-flyspeck-direct-runtime-evidence-v5",
            "allowed_action_outcomes": list(ACTION_OUTCOMES),
            "physical_loader_cache_skip_allowed":
                "only loader-authenticated needs cache-skip events",
            "logical_source_closure_policy": SOURCE_CLOSURE_POLICY,
            "logical_source_closure_order": SOURCE_CLOSURE_ORDER,
            "selected_loadt_ledger_delta_included": True,
            "physical_loader_cache_trace_included": True,
            "physical_source_trace_protocol": SOURCE_TRACE_PROTOCOL,
            "pre_trace_control_exclusion": "control:runtime-config",
            "s2_s3_approval_included": False,
            "dependency_history_protocol": DEPENDENCY_HISTORY_PREFIX,
            "dependency_history_policy": DEPENDENCY_HISTORY_POLICY,
            "semantic_coverage_policy": SEMANTIC_COVERAGE_POLICY,
            "dependency_history_is_kernel_trace": False,
            "semantic_approval_included": False,
            "pft_used": False,
        },
        "expected_logical_source_closure": logical_source_closure,
        "expected_physical_source_trace": source_trace_contract,
        "semantic_evidence_plan": semantic_evidence_plan,
        "runtime_environment_policy": (
            "minimal PATH/LC_ALL=C/CML sizes; reject LD_*, GLIBC_TUNABLES, "
            "BASH_ENV, and ENV"
        ),
        "runtime_environment": runtime_env,
        "inputs": {
            "plan": prepared["plan_record"],
            "host_materialization": prepared["materialization_record"],
            "manifest": prepared["manifest_record"],
            "linked_provenance": prepared["linked_record"],
            "archived_linked_provenance": hash_file(
                runtime_prepared["linked_record_snapshot"]
            ),
            "archived_bootstrap_provenance": hash_file(
                runtime_prepared["bootstrap_record_snapshot"]
            ),
            "archived_bootstrap_log": hash_file(
                runtime_prepared["bootstrap_log_snapshot"]
            ),
            "runtime_snapshot": hash_file(snapshot_record_path),
            "runtime_executable": {
                "path": str(runtime_prepared["cake_runtime"]),
                **hash_file(runtime_prepared["cake_runtime"]),
            },
            "controller_execution": snapshot_record["controller_execution"],
            "authenticated_prefix": prepared["prefix_record"],
            **control_records,
            "setup": hash_file(runtime_candle_root / SETUP_RELATIVE),
            "check": hash_file(runtime_candle_root / CHECK_RELATIVE),
            "fingerprint_serializer": hash_file(
                runtime_candle_root / FINGERPRINT_RELATIVE
            ),
            "l2_target": hash_file(runtime_candle_root / L2_TARGET_RELATIVE),
        },
        "repositories": {
            "candle": prepared["candle_head"],
            "flyspeck": prepared["plan"]["repositories"]["flyspeck_commit"],
        },
    }
    validate_direct_evidence_v5_artifact(attempt, receipt=False)
    atomic_write_json(attempt_path, attempt)
    if output_ownership is not None:
        output_ownership["marker_path"].unlink()
        output_ownership["committed"] = True
    attempt_path.chmod(0o444)
    attempt_record = hash_file(attempt_path)

    command = [str(runtime_prepared["cake_runtime"]), "--candle"]
    timed_out = False
    exit_code: int | None = None
    execution_error: BaseException | None = None
    process: subprocess.Popen[bytes] | None = None
    previous_sigterm = signal.getsignal(signal.SIGTERM)
    previous_sigint = signal.getsignal(signal.SIGINT)
    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    finished: str | None = None
    child_resources: dict[str, Any] | None = None
    log_record: dict[str, Any] | None = None
    validation_error: str | None = None
    fingerprints: dict[str, Any] | None = None
    dependency_history: dict[str, Any] | None = None
    semantic_coverage: dict[str, Any] | None = None
    action_events: list[dict[str, Any]] | None = None
    observed_source_closure: dict[str, Any] | None = None
    physical_source_trace: dict[str, Any] | None = None
    postflight_reauthenticated = False
    handled_signals = {signal.SIGTERM, signal.SIGINT}
    previous_mask: set[signal.Signals] | None = None

    def interrupted(signum: int, _frame: Any) -> None:
        raise InterruptedError(f"compiled stratum interrupted by signal {signum}")

    signal.signal(signal.SIGTERM, interrupted)
    signal.signal(signal.SIGINT, interrupted)
    try:
        with stdin_path.open("rb") as stdin, log_path.open("wb") as log:
            process = subprocess.Popen(
                command, cwd=runtime_candle_root, stdin=stdin, stdout=log,
                stderr=subprocess.STDOUT, start_new_session=True,
                env=runtime_env,
                preexec_fn=process_limit_preexec(
                    max_cpu_seconds, max_address_space_gib * GIB,
                    max_output_file_gib * GIB,
                ),
            )
            try:
                exit_code = process.wait(timeout=timeout_seconds)
            except subprocess.TimeoutExpired:
                timed_out = True
                exit_code = terminate_process_group(process)
    except BaseException as error:
        execution_error = error
    finally:
        try:
            if process is not None and process.poll() is None:
                exit_code = terminate_process_group(process)
            previous_mask = signal.pthread_sigmask(
                signal.SIG_BLOCK, handled_signals,
            )
        except BaseException as error:
            if execution_error is None:
                execution_error = error
            if previous_mask is None:
                try:
                    previous_mask = signal.pthread_sigmask(
                        signal.SIG_BLOCK, handled_signals,
                    )
                except BaseException as mask_error:
                    if execution_error is error:
                        execution_error = RuntimeError(
                            f"{error}; signal-mask failure: {mask_error}"
                        )

    try:
        finished = utc_now()
        usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
        child_resources = {
            "user_cpu_seconds": usage_after.ru_utime - usage_before.ru_utime,
            "system_cpu_seconds": usage_after.ru_stime - usage_before.ru_stime,
            "max_rss_kib": usage_after.ru_maxrss,
            "major_page_faults": usage_after.ru_majflt - usage_before.ru_majflt,
            "minor_page_faults": usage_after.ru_minflt - usage_before.ru_minflt,
        }
        log_record = hash_file(log_path)
        log_path.chmod(0o444)
        require(execution_error is None,
                f"compiled stratum execution failed: {execution_error}")
        require(not timed_out, "compiled stratum attempt timed out")
        require(exit_code == 0, f"compiled stratum process exited {exit_code}")
        post_linked = cakeml_bootstrap_transition.validate_linked_record(candle_root)
        require(post_linked == linked, "linked provenance changed during attempt")
        validate_plan(candle_root, post_linked, plan_root, boundary_id)
        validate_file(snapshot_record_path, attempt["inputs"]["runtime_snapshot"],
                      "runtime snapshot record")
        validate_file(attempt_path, attempt_record, "initial attempt record")
        archived_attempt = load_object(attempt_path, "initial attempt record")
        require(archived_attempt == attempt,
                "initial direct runtime attempt changed after publication")
        validate_direct_evidence_v5_artifact(archived_attempt, receipt=False)
        validate_runtime_snapshot(snapshot_record, output_root)
        validate_controller_execution(
            controller_execution, candle_root, linked["candle_commit"],
        )
        archived_post = load_object(
            runtime_prepared["linked_record_snapshot"],
            "archived linked provenance",
        )
        require(archived_post == linked,
                "archived linked provenance changed during attempt")
        cakeml_artifact_provenance.validate_elf_dynamic_closure(
            runtime_prepared["cake_runtime"],
            archived_post["runtime_elf_closure"],
        )
        for label, path in (
            ("instrumented_prefix", program_path),
            ("runtime_config", config_path),
            ("stdin", stdin_path),
            ("postlude", postlude_path),
        ):
            validate_file(path, control_records[label], f"attempt control {label}")
        postflight_reauthenticated = True
        log_text = log_path.read_text(encoding="utf-8", errors="replace")
        physical_source_trace = validate_source_trace(
            log_text, source_trace_contract,
        )
        action_events = validate_log(
            log_text, prepared["actions"], boundary_id, nonce, theorem_names,
            dependency_theorem_names,
        )
        observed_source_closure = validate_logical_source_closure(
            log_text, logical_source_closure, boundary_id, nonce,
        )
        fingerprints = parse_fingerprints(
            log_path, theorem_names,
            runtime_candle_root / FINGERPRINT_RELATIVE,
        )
        dependency_history = parse_dependency_history(
            log_path, dependency_theorem_names, boundary_id, nonce,
        )
        semantic_coverage = derive_semantic_coverage(
            semantic_evidence_plan, observed_source_closure,
            physical_source_trace, fingerprints, dependency_history,
        )
    except Exception as error:
        validation_error = f"{type(error).__name__}: {error}"

    if previous_mask is None:
        try:
            previous_mask = signal.pthread_sigmask(
                signal.SIG_BLOCK, handled_signals,
            )
        except Exception as error:
            mask_error = f"{type(error).__name__}: {error}"
            validation_error = (
                mask_error if validation_error is None else
                validation_error + "; receipt signal-mask failure: " +
                mask_error
            )
    if previous_mask is not None:
        pending_interrupts = sorted(
            int(item) for item in signal.sigpending() & handled_signals
        )
        if pending_interrupts:
            pending_error = (
                "interrupt signal(s) pending after child exit: " +
                ",".join(map(str, pending_interrupts))
            )
            validation_error = (
                pending_error if validation_error is None else
                validation_error + "; " + pending_error
            )
    if finished is None:
        finished = utc_now()
    try:
        receipt = {
            **attempt,
            "state": "completed" if validation_error is None else "failed",
            "finished_utc": finished,
            "timed_out": timed_out,
            "exit_code": exit_code,
            "command": command,
            "child_resources": child_resources,
            "log": (
                None if log_record is None else
                {"path": "candle.log", **log_record}
            ),
            "initial_attempt": {"path": "attempt.json", **attempt_record},
            "action_markers_validated": (
                len(prepared["actions"]) if validation_error is None else 0
            ),
            "action_events": action_events,
            "logical_source_closure": observed_source_closure,
            "physical_source_trace": physical_source_trace,
            "semantic_fingerprints": fingerprints,
            "dependency_history": dependency_history,
            "semantic_coverage": semantic_coverage,
            "s2_s3_evidence": False,
            "validation_error": validation_error,
            "postflight_reauthenticated": postflight_reauthenticated,
        }
        validate_direct_evidence_v5_artifact(
            receipt, receipt=True,
            log_path=(log_path if log_record is not None else None),
            runtime_executable_path=runtime_prepared["cake_runtime"],
        )
        atomic_write_json(receipt_path, receipt)
        receipt_path.chmod(0o444)
    finally:
        signal.signal(signal.SIGTERM, previous_sigterm)
        signal.signal(signal.SIGINT, previous_sigint)
        if previous_mask is not None:
            signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
    if validation_error is not None:
        raise ContractError(validation_error)
    return receipt


def cleanup_incomplete_output(output_root: Path) -> None:
    """Remove only a new pre-attempt tree that never gained attempt.json."""
    for directory, _subdirectories, _files in os.walk(
        output_root, topdown=True, followlinks=False,
    ):
        os.chmod(directory, 0o700)
    shutil.rmtree(output_root)


def run_attempt(
    candle_script: Path,
    plan_root: Path,
    boundary_id: str,
    output_root: Path,
    timeout_seconds: int,
    max_cpu_seconds: int,
    max_address_space_gib: int,
    max_output_file_gib: int,
) -> dict[str, Any]:
    """Run an attempt, cleaning only an unpublished pre-attempt failure."""
    unresolved_output = Path(output_root)
    require(not unresolved_output.is_symlink(),
            "attempt output path must not be a symlink")
    resolved_output = unresolved_output.resolve()
    ownership: dict[str, Any] = {
        "nonce": secrets.token_hex(32),
        "created": False,
        "committed": False,
    }
    original_sigterm = signal.getsignal(signal.SIGTERM)
    original_sigint = signal.getsignal(signal.SIGINT)
    original_signal_mask = signal.pthread_sigmask(signal.SIG_BLOCK, set())
    try:
        return _run_attempt_impl(
            candle_script, plan_root, boundary_id, output_root,
            timeout_seconds, max_cpu_seconds, max_address_space_gib,
            max_output_file_gib, ownership,
        )
    except BaseException:
        if ownership["created"] and not ownership["committed"]:
            try:
                current = os.stat(resolved_output, follow_symlinks=False)
                marker = resolved_output / ".candle-preflight-owner"
                inode_owned = (
                    not resolved_output.is_symlink() and
                    current.st_dev == ownership["device"] and
                    current.st_ino == ownership["inode"]
                )
                if ownership.get("marker_ready"):
                    marker_owned = (
                        marker.is_file() and not marker.is_symlink() and
                        marker.read_text(encoding="ascii") ==
                        ownership["nonce"] + "\n"
                    )
                else:
                    marker_owned = not any(resolved_output.iterdir())
                owned = (inode_owned and marker_owned and
                         not (resolved_output / "attempt.json").exists())
            except OSError:
                owned = False
            if owned:
                cleanup_incomplete_output(resolved_output)
        raise
    finally:
        signal.signal(signal.SIGTERM, original_sigterm)
        signal.signal(signal.SIGINT, original_sigint)
        signal.pthread_sigmask(signal.SIG_SETMASK, original_signal_mask)


def main() -> None:
    require_direct_script_startup()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candle-script", type=Path, required=True)
    parser.add_argument("--plan-root", type=Path, required=True)
    parser.add_argument("--boundary", required=True, metavar="BOUNDARY_ID")
    parser.add_argument("--write", type=Path, required=True, metavar="ATTEMPT_ROOT")
    parser.add_argument("--timeout", type=int, default=86400, metavar="SECONDS")
    parser.add_argument(
        "--max-cpu-seconds", type=int, default=86400, metavar="SECONDS",
    )
    parser.add_argument(
        "--max-address-space-gib", type=int, default=48, metavar="GIB",
    )
    parser.add_argument(
        "--max-output-file-gib", type=int, default=8, metavar="GIB",
    )
    arguments = parser.parse_args()
    receipt = run_attempt(
        arguments.candle_script, arguments.plan_root, arguments.boundary,
        arguments.write, arguments.timeout, arguments.max_cpu_seconds,
        arguments.max_address_space_gib, arguments.max_output_file_gib,
    )
    print(
        f"compiled {'diagnostic prefix' if receipt['diagnostic_only'] else 'stratum'} PASS: "
        f"{receipt['boundary_id']} "
        f"({receipt['action_count']} actions); not S2/S3 without semantic fingerprints"
    )


if __name__ == "__main__":
    main()
