#!/usr/bin/env python3
"""Fail-closed provenance records for the pinned local CakeML handoff."""

from __future__ import annotations

import argparse
import copy
import fcntl
import hashlib
import json
import os
import re
import shlex
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Callable


BOOTSTRAP_INPUTS = (
    "cake.S",
    "config_enc_str.txt",
    "candle_boot.ml",
    "basis_ffi.c",
    "Makefile",
)
HOL_BOOTSTRAP_RUNTIME_FILES = (
    "bin/Holmake",
    "bin/hol",
    "bin/hol.state",
    ".kernelidstr",
)
HOL_BOOTSTRAP_ELF_FILES = (
    "bin/Holmake",
    "bin/hol",
)
HOL_KERNEL_ID_BYTES = b"stdknl\n"
HOL_GENERATED_PROOF_INPUTS = (
    "src/parse/base_lexer.sml",
    "src/portableML/HOLsexp.grm-sig.sml",
    "src/portableML/HOLsexp.grm.sml",
    "src/portableML/HOLsexp.lex.sml",
    "src/portableML/poly/SHA1_ML.sml",
    "src/thm/Thm-sig.sml",
    "src/thm/Thm.sml",
)
HOL_PROOF_OBJECT_COUNT = 2907
HOL_SIGOBJ_ORDINARY_COUNT = 6
HOL_SIGOBJ_SYMLINK_COUNT = 2401
HOL_PROOF_OBJECT_PATHS_SHA256 = (
    "0afa5a9326b4de1fc1c3f97824fb30c26455c5f3f1b20528812792c27bf384ce"
)
HOL_SIGOBJ_CONTRACTS_SHA256 = (
    "dac2ec14a569c22cac1127e30223e60a4a663b9fa13010fe0c9290e93525e132"
)
HOL_MAKE_DEPENDENCY_COUNT = 2309
CAKEML_MAKE_DEPENDENCY_ANCESTOR_COUNT = 1785
HOL_MAKE_DEPENDENCY_PATHS_SHA256 = (
    "dc3e187784b21ab208d02c5ee17675337938f401e2aca10e03cf211e360c9dac"
)
CAKEML_MAKE_DEPENDENCY_ANCESTOR_PATHS_SHA256 = (
    "25a8b77fbffd65a688322b1b864015a4fb5e8345c59a1ff4d2c7b27ddf46a0ea"
)
HOL_ELF_ALLOWED_DYNAMIC_PATH_TAGS = {
    "RUNPATH": ["/usr/lib/x86_64-linux-gnu"],
}
GNU_TIME_FOOTER_LABELS = (
    "Command being timed",
    "User time (seconds)",
    "System time (seconds)",
    "Percent of CPU this job got",
    "Elapsed (wall clock) time (h:mm:ss or m:ss)",
    "Average shared text size (kbytes)",
    "Average unshared data size (kbytes)",
    "Average stack size (kbytes)",
    "Average total size (kbytes)",
    "Maximum resident set size (kbytes)",
    "Average resident set size (kbytes)",
    "Major (requiring I/O) page faults",
    "Minor (reclaiming a frame) page faults",
    "Voluntary context switches",
    "Involuntary context switches",
    "Swaps",
    "File system inputs",
    "File system outputs",
    "Socket messages sent",
    "Socket messages received",
    "Signals delivered",
    "Page size (bytes)",
    "Exit status",
)
NATIVE_LINK_ENVIRONMENT = {
    "LC_ALL": "C",
    "PATH": "/usr/bin:/bin",
    "TMPDIR": ".candle-native-tmp",
}
NATIVE_LINK_MAKE_ARGV = (
    "/usr/bin/make",
    "--no-builtin-rules",
    "--no-builtin-variables",
    "-B",
    "-j1",
    "-f",
    "Makefile",
    "OS=Linux",
    "CC=/usr/bin/cc -B.candle-native-tools/",
    "CFLAGS=-O2 -save-temps=obj -v",
    "LOADLIBES=",
    "EVALFLAG=-DEVAL",
    "LDFLAGS=",
    "LDLIBS=-lm",
    "cake",
)
NATIVE_LINK_CC_ARGV = (
    "/usr/bin/cc",
    "-B.candle-native-tools/",
    "-O2",
    "-save-temps=obj",
    "-v",
    "cake.S",
    "basis_ffi.c",
    "-DEVAL",
    "-o",
    "cake",
    "-lm",
)
NATIVE_LINK_INPUTS = ("cake.S", "basis_ffi.c", "Makefile")
NATIVE_TOOL_PATHS = {
    "make": "/usr/bin/make",
    "cc": "/usr/bin/cc",
    "as": "/usr/bin/as",
    "ld": "/usr/bin/ld",
    "shell": "/bin/sh",
}
NATIVE_LINK_TRUSTED_BOUNDARY = {
    "policy": "explicit_host_toolchain_boundary_v1",
    "bound_by_content": [
        "make, cc, as, ld, shell, cc1, collect2, and lto-wrapper executables",
        "GCC target/version/specification bytes and every recorded command/flag",
        "cake.S, basis_ffi.c, Makefile, and the resulting executable bytes",
    ],
    "trusted_not_independently_authenticated": [
        "kernel process and filesystem semantics",
        "dynamic loader and shared libraries used while running host build tools",
        "system C headers, GCC internal data, linker scripts, startup objects, and archives",
        "the semantics of the exact recorded host tool binaries and system inputs",
    ],
}
LINKED_OUTPUTS = (
    "cake.S",
    "cake.S.bootstrap",
    "cake",
    "config_enc_str.txt",
    "candle_boot.ml",
    "basis_ffi.c",
    "Makefile",
    "types.txt",
    "insulate.ml",
    "bootstrap-preflight.json",
    "bootstrap-provenance.json",
    "bootstrap.log",
)
BOOTSTRAP_RELATIVE = Path("compiler/bootstrap/compilation/x64/64")
CAKE_COMPILE_HEAP_RELATIVE = Path("cv_translator/cake_compile_heap")
CAKE_COMPILE_HEAP_HOLMAKEFILE_RELATIVE = (
    "compiler/bootstrap/compilation/x64/64/Holmakefile"
)
MANIFEST_RELATIVE = Path("candle/flyspeck_manifest.json")
LINKED_RECORD_RELATIVE = Path("candle/build/cakeml-build-provenance.json")
BOOTSTRAP_PREFLIGHT_SCHEMA = 3
BOOTSTRAP_PROVENANCE_SCHEMA = 5
LINKED_PROVENANCE_SCHEMA = 6
ELF_DYNAMIC_CLOSURE_POLICY = "ldd_roles_resolved_absolute_paths_and_content_v3"
ELF_DYNAMIC_CLOSURE_FIELDS = frozenset({
    "policy", "dynamic_path_tags", "files", "roles", "virtual_objects",
})
CANDLE_ELF_OBJECTS = {
    "ld-linux-x86-64.so.2",
    "libc.so.6",
    "libm.so.6",
}
CANDLE_ELF_VIRTUAL_OBJECTS = ["linux-vdso.so.1"]
ROOT_RUNTIME_ALIASES = ("config_enc_str.txt", "candle_boot.ml")
LINKED_BOOTSTRAP_RECORD = "bootstrap-provenance.json"
LINKED_BOOTSTRAP_PREFLIGHT = "bootstrap-preflight.json"
LINKED_BOOTSTRAP_LOG = "bootstrap.log"
BOOTSTRAP_CONTROLLER_SOURCES = (
    "build-local-cakeml-bootstrap.sh",
    "candle/cakeml_artifact_provenance.py",
)
BOOTSTRAP_CONTROLLER_TOOLS = {
    "bash": "/bin/bash",
    "chmod": "/usr/bin/chmod",
    "env": "/usr/bin/env",
    "flock": "/usr/bin/flock",
    "git": "/usr/bin/git",
    "ldd": "/usr/bin/ldd",
    "python": "/usr/bin/python3",
    "readelf": "/usr/bin/readelf",
    "realpath": "/usr/bin/realpath",
    "sh": "/bin/sh",
    "stat": "/usr/bin/stat",
    "time": "/usr/bin/time",
}
BOOTSTRAP_LAUNCH_ELF_TOOLS = ("env", "time", "sh")
BOOTSTRAP_LOG_MARKER = "CANDLE_CAKEML_BOOTSTRAP_CONTROLLER_V1"
BOOTSTRAP_TARGETS = (
    "pancake_lexProg",
    "pancake_parseProg",
    "reg_allocProg",
    "inferProg",
    "explorerProg",
    "decodeProg",
    "sexp_parserProg",
    "basis_defProg",
    "printingProg",
    "to_word64Prog",
    "to_target64Prog",
    "from_pancake64Prog",
    "x64Prog",
    "arm8Prog",
    "riscvProg",
    "mipsProg",
    "compiler64Prog",
    "x64Bootstrap",
)
BOOTSTRAP_TRANSLATION_THEORY_SUFFIXES = (
    "ui", "uo", "dat", "sig", "sml", "cachekey",
)
BOOTSTRAP_FINAL_THEORY_SUFFIXES = ("dat", "sig", "sml", "cachekey")
BOOTSTRAP_SCRIPT_TRANSIENT_SUFFIXES = ("ui", "uo")
BOOTSTRAP_DIRECT_GENERATED_OUTPUTS = ("cake.S", "config_enc_str.txt")
BOOTSTRAP_SYMLINK_INPUTS = {
    "candle_boot.ml": (
        "../../../../../candle/prover/candle_boot.ml",
        "candle/prover/candle_boot.ml",
    ),
    "basis_ffi.c": (
        "../../../../../basis/basis_ffi.c",
        "basis/basis_ffi.c",
    ),
    "Makefile": (
        "../Makefile",
        "compiler/bootstrap/compilation/x64/Makefile",
    ),
}
BOOTSTRAP_TRUST_BOUNDARY = {
    "policy": "canonical_sanitized_bootstrap_controller_boundary_v1",
    "bound_by_content": [
        "clean Candle, CakeML, and HOL4 revisions and controller sources",
        "fixed controller tool paths and resolved executable bytes",
        "env, time, Holmake, and hol ELF closures plus hol.state and "
        ".kernelidstr bytes",
        "the complete HOL4 .hol/objs file set, exact sigobj link contracts "
        "and resolved payloads, and exact generated HOL proof inputs",
        "all HOL4 and non-target CakeML .hol/make-deps files, with every "
        "lastmaker pinned to the authenticated HOL4 Holmake",
        "the CakeML cv_translator/cake_compile_heap bytes selected by the "
        "pinned final x64Bootstrap Holmakefile",
        "preflight, exact launch environment/argv/cwd, transcript, and outputs",
    ],
    "trusted_not_independently_authenticated": [
        "the caller environment and dynamic loader before /usr/bin/env and the "
        "controller interpreter have started; invoke the controller through the "
        "documented outer /usr/bin/env -i boundary",
        "kernel process, signal, locking, inode, and filesystem semantics",
        "dynamic-loader behavior and host libraries of non-launch controller tools",
        "the semantics of the exact content-bound host and HOL tool binaries",
        "absence of hostile same-UID transient mutation between guarded observations",
        "derivation and semantics of content-bound pre-existing CakeML .hol/objs "
        "ancestor artifacts outside the freshly rebuilt 18-target stratum",
        "derivation and semantics of the content-bound HOL4 proof-artifact "
        "closure; those artifacts are not independently rebuilt here",
        "derivation and semantics of content-bound HOL4 and ancestor CakeML "
        "make-dependency artifacts outside the fresh target transitions",
        "derivation and semantics of the content-bound CakeML compiler heap; "
        "the heap is not independently rebuilt here",
    ],
}


class ProvenanceError(ValueError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ProvenanceError(message)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        while block := source.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def file_record(path: Path, *, allow_symlink: bool = False) -> dict[str, Any]:
    require(path.is_file() and (allow_symlink or not path.is_symlink()),
            f"missing ordinary provenance input: {path}")
    return {"bytes": path.stat().st_size, "sha256": sha256_file(path)}


def bytes_record(value: bytes) -> dict[str, Any]:
    return {"bytes": len(value), "sha256": hashlib.sha256(value).hexdigest()}


def _captured_ordinary_file(
    path: Path,
) -> tuple[bytes, dict[str, Any], os.stat_result]:
    """Read one stable named ordinary-file image from one O_NOFOLLOW FD."""
    try:
        descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    except OSError as error:
        raise ProvenanceError(f"could not capture ordinary file: {path}") from error
    try:
        before = os.fstat(descriptor)
        require(stat.S_ISREG(before.st_mode), f"not an ordinary file: {path}")
        chunks = []
        while block := os.read(descriptor, 1024 * 1024):
            chunks.append(block)
        after = os.fstat(descriptor)
        require((before.st_dev, before.st_ino, before.st_size,
                 before.st_mtime_ns, before.st_ctime_ns) ==
                (after.st_dev, after.st_ino, after.st_size,
                 after.st_mtime_ns, after.st_ctime_ns),
                f"file changed while being captured: {path}")
        value = b"".join(chunks)
        require(len(value) == before.st_size,
                f"short ordinary-file capture: {path}")
        named = path.stat(follow_symlinks=False)
        require(stat.S_ISREG(named.st_mode) and
                (named.st_dev, named.st_ino) == (after.st_dev, after.st_ino),
                f"file path changed while being captured: {path}")
        return value, bytes_record(value), after
    finally:
        os.close(descriptor)


def captured_ordinary_file(path: Path) -> tuple[bytes, dict[str, Any]]:
    value, record, _ = _captured_ordinary_file(path)
    return value, record


def ordinary_file_identity(path: Path) -> dict[str, Any]:
    value, record, metadata = _captured_ordinary_file(path)
    del value
    return {
        "device": metadata.st_dev,
        "inode": metadata.st_ino,
        "mtime_ns": metadata.st_mtime_ns,
        "ctime_ns": metadata.st_ctime_ns,
        **record,
    }


def validate_ordinary_file_identity(
    path: Path,
    record: dict[str, Any],
    label: str,
) -> None:
    require(isinstance(record, dict) and set(record) == {
        "device", "inode", "mtime_ns", "ctime_ns", "bytes", "sha256",
    }, f"malformed {label} identity")
    require(ordinary_file_identity(path) == record,
            f"{label} identity mismatch: {path}")


def write_new_json(
    path: Path,
    value: dict[str, Any],
    *,
    before_publish: Callable[[], None] | None = None,
    after_publish: Callable[[], None] | None = None,
) -> None:
    """Create a read-only JSON receipt exactly once."""
    path = path.absolute()
    require(path.parent.is_dir() and not path.parent.is_symlink(),
            f"receipt parent is not an ordinary directory: {path.parent}")
    payload = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", dir=path.parent,
    )
    temporary = Path(temporary_name)
    try:
        os.fchmod(descriptor, 0o444)
        offset = 0
        while offset < len(payload):
            offset += os.write(descriptor, payload[offset:])
        os.fsync(descriptor)
        if before_publish is not None:
            before_publish()
        try:
            os.link(temporary, path, follow_symlinks=False)
        except OSError as error:
            raise ProvenanceError(
                f"refusing to overwrite receipt: {path}",
            ) from error
        if after_publish is not None:
            try:
                after_publish()
            except BaseException:
                named = path.stat(follow_symlinks=False)
                source = os.fstat(descriptor)
                if (named.st_dev, named.st_ino) == (source.st_dev, source.st_ino):
                    os.unlink(path)
                raise
        directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        os.close(descriptor)
        if os.path.lexists(temporary):
            os.unlink(temporary)


def resolve_new_output(path: Path, label: str) -> Path:
    require(path.name not in {"", ".", ".."}, f"malformed {label} path")
    parent = path.parent.resolve(strict=True)
    require(parent.is_dir() and not parent.is_symlink(),
            f"{label} parent is not an ordinary directory")
    result = parent / path.name
    require(not os.path.lexists(result), f"{label} already exists: {result}")
    return result


def validate_file_record(
    path: Path,
    record: dict[str, Any],
    label: str,
    *,
    allow_symlink: bool = False,
) -> None:
    require(set(record) == {"bytes", "sha256"}, f"malformed {label} record")
    observed = file_record(path, allow_symlink=allow_symlink)
    require(observed == record, f"{label} provenance mismatch: {path}")


def load_object(path: Path) -> dict[str, Any]:
    require(path.is_file() and not path.is_symlink(), f"missing ordinary provenance record: {path}")
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"expected provenance JSON object: {path}")
    return value


def load_captured_object(path: Path) -> tuple[dict[str, Any], dict[str, Any]]:
    value, identity = captured_ordinary_file(path)
    try:
        decoded = json.loads(value.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ProvenanceError(f"malformed captured JSON object: {path}") from error
    require(isinstance(decoded, dict), f"expected captured JSON object: {path}")
    return decoded, identity


def git_output(root: Path, *arguments: str) -> str:
    return subprocess.run(
        git_command(root, *arguments), check=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        env=git_environment(),
    ).stdout.strip()


def git_bytes(root: Path, *arguments: str) -> bytes:
    return subprocess.run(
        git_command(root, *arguments), check=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        env=git_environment(),
    ).stdout


def git_command(root: Path, *arguments: str) -> list[str]:
    return [
        "/usr/bin/git",
        "-c", "core.fsmonitor=false",
        "-c", "core.untrackedCache=false",
        "-c", "core.preloadIndex=false",
        "-C", str(root), *arguments,
    ]


def validate_git(root: Path, expected_head: str, label: str) -> None:
    require(git_output(root, "rev-parse", "HEAD") == expected_head,
            f"{label} revision mismatch")
    require(not git_output(root, "status", "--porcelain", "--untracked-files=all"),
            f"{label} worktree is not clean")


def committed_source_record(root: Path, relative: str) -> dict[str, Any]:
    path = root / relative
    working_bytes, working_record = captured_ordinary_file(path)
    committed = git_bytes(root, "show", f"HEAD:{relative}")
    committed_record = bytes_record(committed)
    require(working_bytes == committed,
            f"controller source differs from committed bytes: {relative}")
    return {
        "repository_path": relative,
        "path": str(path.resolve(strict=True)),
        **working_record,
        "commit_blob": committed_record,
    }


def bootstrap_symlink_input_record(
    cakeml_root: Path,
    name: str,
) -> dict[str, Any]:
    require(name in BOOTSTRAP_SYMLINK_INPUTS,
            f"unsupported bootstrap symlink input: {name}")
    link_text, target_relative = BOOTSTRAP_SYMLINK_INPUTS[name]
    relative = str(BOOTSTRAP_RELATIVE / name)
    path = cakeml_root / relative
    metadata = path.lstat()
    require(stat.S_ISLNK(metadata.st_mode) and os.readlink(path) == link_text,
            f"bootstrap input is not the exact tracked symlink: {relative}")
    committed = git_bytes(cakeml_root, "show", f"HEAD:{relative}")
    require(committed == link_text.encode(),
            f"bootstrap symlink differs from its commit blob: {relative}")
    stage = git_output(cakeml_root, "ls-files", "--stage", "--", relative)
    fields = stage.split(maxsplit=3)
    require(len(fields) == 4 and fields[0] == "120000" and
            fields[2] == "0" and fields[3] == relative and
            re.fullmatch(r"[0-9a-f]{40}", fields[1]) is not None,
            f"bootstrap symlink is not an ordinary stage-0 120000 entry: {relative}")
    target = path.resolve(strict=True)
    expected_target = (cakeml_root / target_relative).resolve(strict=True)
    require(target == expected_target and target.is_relative_to(cakeml_root) and
            target.is_file() and not target.is_symlink(),
            f"bootstrap symlink target escapes or is not ordinary: {relative}")
    return {
        "relative": relative,
        "path": str(path),
        "link_text": link_text,
        "link_identity": {
            "device": metadata.st_dev,
            "inode": metadata.st_ino,
            "mtime_ns": metadata.st_mtime_ns,
            "ctime_ns": metadata.st_ctime_ns,
        },
        "commit_mode": "120000",
        "commit_blob_oid": fields[1],
        "commit_blob": bytes_record(committed),
        "target_relative": target_relative,
        "target_path": str(target),
        "target_identity": ordinary_file_identity(target),
    }


def validate_bootstrap_symlink_input_record(
    record: Any,
    name: str,
    cakeml_root: Path,
    *,
    require_live: bool,
) -> None:
    require(isinstance(record, dict) and set(record) == {
        "relative", "path", "link_text", "link_identity", "commit_mode",
        "commit_blob_oid", "commit_blob", "target_relative", "target_path",
        "target_identity",
    }, f"malformed bootstrap symlink input: {name}")
    link_text, target_relative = BOOTSTRAP_SYMLINK_INPUTS[name]
    relative = str(BOOTSTRAP_RELATIVE / name)
    expected_path = cakeml_root / relative
    expected_target = cakeml_root / target_relative
    require(record.get("relative") == relative and
            record.get("path") == str(expected_path) and
            record.get("link_text") == link_text and
            record.get("commit_mode") == "120000" and
            re.fullmatch(r"[0-9a-f]{40}",
                         record.get("commit_blob_oid", "")) is not None and
            record.get("commit_blob") == bytes_record(link_text.encode()) and
            record.get("target_relative") == target_relative and
            record.get("target_path") == str(expected_target),
            f"bootstrap symlink contract mismatch: {name}")
    link_identity = record.get("link_identity")
    target_identity = record.get("target_identity")
    require(isinstance(link_identity, dict) and set(link_identity) == {
        "device", "inode", "mtime_ns", "ctime_ns",
    } and isinstance(target_identity, dict) and set(target_identity) == {
        "device", "inode", "mtime_ns", "ctime_ns", "bytes", "sha256",
    }, f"malformed bootstrap symlink identity: {name}")
    if require_live:
        require(record == bootstrap_symlink_input_record(cakeml_root, name),
                f"bootstrap symlink input changed: {name}")


def bootstrap_input_file_record(
    bootstrap_dir: Path,
    name: str,
) -> dict[str, Any]:
    path = bootstrap_dir / name
    if name in BOOTSTRAP_SYMLINK_INPUTS:
        target = path.resolve(strict=True)
        return captured_ordinary_file(target)[1]
    return captured_ordinary_file(path)[1]


def runtime_environment(
    environment: dict[str, str] | None = None,
) -> dict[str, str]:
    """Return the fixed locale environment allowed for linked execution."""
    require(
        not os.path.lexists("/etc/ld.so.preload"),
        "system-wide dynamic-loader preload is outside the runtime model",
    )
    source = os.environ if environment is None else environment
    forbidden_names = {"BASH_ENV", "ENV", "GLIBC_TUNABLES"}
    forbidden = sorted(name for name in source
                       if name.startswith("LD_") or name in forbidden_names)
    require(not forbidden,
            "forbidden dynamic-loader environment: " + ", ".join(forbidden))
    result = {"LC_ALL": "C", "PATH": "/usr/bin:/bin"}
    for name in ("CML_HEAP_SIZE", "CML_STACK_SIZE"):
        if name in source:
            require(re.fullmatch(r"[1-9][0-9]*", source[name]) is not None,
                    f"invalid CakeML runtime size: {name}")
            result[name] = source[name]
    return result


def bootstrap_controller_environment() -> dict[str, str]:
    """Require the Python controller itself to have an exact minimal environment."""
    expected = {"LC_ALL": "C", "PATH": "/usr/bin:/bin"}
    require(dict(os.environ) == expected,
            "bootstrap controller Python environment is not exact")
    runtime_environment(os.environ)
    return expected


def python_controller_record(candle_root: Path) -> dict[str, Any]:
    """Bind the direct isolated Python process interpreting this source file."""
    controller = (candle_root / "candle/cakeml_artifact_provenance.py").resolve(
        strict=True,
    )
    requested_python = Path(BOOTSTRAP_CONTROLLER_TOOLS["python"])
    resolved_python = requested_python.resolve(strict=True)
    proc_executable = Path("/proc/self/exe").resolve(strict=True)
    require(proc_executable == resolved_python,
            "bootstrap controller /proc/self/exe is not /usr/bin/python3")
    require(Path(sys.executable).resolve(strict=True) == resolved_python,
            "bootstrap controller sys.executable is not /usr/bin/python3")
    require(__name__ == "__main__" and __spec__ is None and
            globals().get("__cached__") is None,
            "bootstrap controller was not executed as a direct script")
    require(len(sys.argv) >= 2 and Path(sys.argv[0]).resolve(strict=True) == controller,
            "bootstrap controller argv[0] is not the direct provenance source")
    expected_flags = {
        "isolated": 1,
        "ignore_environment": 1,
        "no_user_site": 1,
        "no_site": 1,
        "safe_path": True,
        "utf8_mode": 1,
    }
    observed_flags = {name: getattr(sys.flags, name) for name in expected_flags}
    require(observed_flags == expected_flags and sys._xoptions == {} and
            sys.warnoptions == [],
            "bootstrap controller Python startup flags are not exact -I defaults")
    source = committed_source_record(
        candle_root, "candle/cakeml_artifact_provenance.py",
    )
    proc_fields = Path("/proc/self/stat").read_text(encoding="ascii").rstrip()
    stat_tail = proc_fields.rsplit(")", 1)[1].strip().split()
    require(len(stat_tail) > 19 and stat_tail[19].isdigit(),
            "malformed bootstrap controller /proc/self/stat")
    return {
        "policy": "direct_usr_bin_python3_isolated_controller_v1",
        "executable": executable_tool_record(requested_python),
        "elf_closure": elf_dynamic_closure(requested_python),
        "proc_self_exe": str(proc_executable),
        "sys_executable": sys.executable,
        "sys_version": sys.version,
        "flags": observed_flags,
        "xoptions": {},
        "warnoptions": [],
        "argv": list(sys.argv),
        "module": {"name": "__main__", "spec": None, "cached": None},
        "process": {
            "pid": os.getpid(),
            "start_time_ticks": int(stat_tail[19]),
        },
        "source": source,
    }


def validate_python_controller_record(
    record: dict[str, Any],
    candle_root: Path | None = None,
) -> None:
    require(isinstance(record, dict) and set(record) == {
        "policy", "executable", "proc_self_exe", "sys_executable",
        "elf_closure", "sys_version", "flags", "xoptions", "warnoptions", "argv",
        "module", "process", "source",
    }, "malformed bootstrap Python controller record")
    require(record.get("policy") ==
            "direct_usr_bin_python3_isolated_controller_v1",
            "unsupported bootstrap Python controller policy")
    validate_executable_tool_record(
        record.get("executable"), "bootstrap Python controller",
    )
    validate_elf_closure_record(
        record.get("elf_closure"), "bootstrap Python controller",
        allowed_dynamic_path_tags={},
    )
    flags = record.get("flags")
    require(flags == {
        "isolated": 1, "ignore_environment": 1, "no_user_site": 1,
        "no_site": 1, "safe_path": True, "utf8_mode": 1,
    } and record.get("xoptions") == {} and record.get("warnoptions") == [] and
            record.get("module") == {
                "name": "__main__", "spec": None, "cached": None,
            } and isinstance(record.get("process"), dict) and
            set(record["process"]) == {"pid", "start_time_ticks"} and
            isinstance(record["process"]["pid"], int) and
            record["process"]["pid"] > 0 and
            isinstance(record["process"]["start_time_ticks"], int) and
            record["process"]["start_time_ticks"] > 0 and
            isinstance(record.get("sys_version"), str) and
            isinstance(record.get("proc_self_exe"), str) and
            Path(record["proc_self_exe"]).is_absolute() and
            isinstance(record.get("sys_executable"), str) and
            Path(record["sys_executable"]).is_absolute() and
            isinstance(record.get("argv"), list) and len(record["argv"]) >= 2 and
            all(isinstance(argument, str) for argument in record["argv"]) and
            Path(record["argv"][0]).is_absolute(),
            "malformed bootstrap Python controller semantics")
    source = record.get("source")
    require(isinstance(source, dict) and set(source) == {
        "repository_path", "path", "bytes", "sha256", "commit_blob",
    } and source.get("repository_path") ==
            "candle/cakeml_artifact_provenance.py" and
            {field: source[field] for field in ("bytes", "sha256")} ==
            source.get("commit_blob"),
            "malformed bootstrap Python source binding")
    if candle_root is not None:
        observed = python_controller_record(candle_root)
        ignored = {"argv", "process"}
        require({field: value for field, value in record.items()
                 if field not in ignored} ==
                {field: value for field, value in observed.items()
                 if field not in ignored},
                "bootstrap Python controller runtime changed after preflight")


def git_environment() -> dict[str, str]:
    """Return the fixed fail-closed environment for host Git validation."""
    runtime_environment()
    return {
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_TERMINAL_PROMPT": "0",
        "GIT_NO_REPLACE_OBJECTS": "1",
        "GIT_OPTIONAL_LOCKS": "0",
    }


def validate_root_runtime_aliases(
    candle_root: Path,
    outputs: dict[str, Any],
) -> None:
    build_dir = candle_root / "candle/build"
    for name in ROOT_RUNTIME_ALIASES:
        alias = candle_root / name
        expected_target = Path("candle/build") / name
        require(alias.is_symlink(), f"runtime alias is not a symlink: {alias}")
        require(Path(os.readlink(alias)) == expected_target,
                f"runtime alias target mismatch: {alias}")
        require(alias.resolve(strict=True) == (build_dir / name).resolve(strict=True),
                f"runtime alias resolution mismatch: {alias}")
        validate_file_record(
            alias, outputs[name], f"runtime alias {name}", allow_symlink=True,
        )


def validate_build_directory(candle_root: Path) -> Path:
    build_dir = candle_root / "candle/build"
    require(build_dir.is_dir() and not build_dir.is_symlink(),
            f"Candle build directory is not an ordinary directory: {build_dir}")
    return build_dir


def expected_pins(candle_root: Path) -> dict[str, str]:
    manifest_path = candle_root / MANIFEST_RELATIVE
    manifest = load_object(manifest_path)
    integration = manifest["dopen_corpus_contract"]["verified_cakeml_integration"]
    return {
        "cakeml_commit": integration["commit"],
        "hol4_commit": integration["proof_hol4_commit"],
        "manifest_sha256": sha256_file(manifest_path),
    }


def version_details(executable: Path) -> tuple[str, str, str]:
    require(executable.is_file(), f"missing linked CakeML executable: {executable}")
    output = subprocess.run(
        [str(executable), "--version"], check=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        env=runtime_environment(),
    ).stdout
    cake_lines = [line.removeprefix("CakeML:").strip()
                  for line in output.splitlines() if line.startswith("CakeML:")]
    hol_lines = [line.removeprefix("HOL4:").strip()
                 for line in output.splitlines() if line.startswith("HOL4:")]
    require(len(cake_lines) == 1 and len(hol_lines) == 1,
            "linked compiler version identity missing or ambiguous")
    return cake_lines[0], hol_lines[0], output


def elf_dynamic_closure(
    executable: Path,
    *,
    allowed_dynamic_path_tags: dict[str, list[str]] | None = None,
) -> dict[str, Any]:
    """Pin the host ELF objects selected for this executable by ldd."""
    executable = executable.resolve()
    require(executable.is_file(), f"missing ELF executable: {executable}")
    with executable.open("rb") as source:
        require(source.read(4) == b"\x7fELF",
                f"runtime executable is not ELF: {executable}")
    try:
        dynamic_tags = subprocess.run(
            ["/usr/bin/readelf", "-d", str(executable)], check=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            timeout=30, env=runtime_environment(),
        ).stdout
        path_tags: dict[str, list[str]] = {}
        for line in dynamic_tags.splitlines():
            if re.search(r"\((?:RPATH|RUNPATH)\)", line) is None:
                continue
            match = re.search(
                r"\((RPATH|RUNPATH)\).*Library (?:rpath|runpath): \[([^]]*)\]",
                line,
            )
            require(match is not None,
                    f"unrecognized RPATH/RUNPATH for {executable}: {line}")
            tag, value = match.groups()
            require(tag not in path_tags,
                    f"duplicate {tag} for {executable}")
            entries = value.split(":")
            require(all(entry.startswith("/") for entry in entries),
                    f"non-absolute {tag} is outside the ELF closure model: {executable}")
            path_tags[tag] = entries
        expected_path_tags = ({} if allowed_dynamic_path_tags is None
                              else allowed_dynamic_path_tags)
        require(path_tags == expected_path_tags,
                f"RPATH/RUNPATH is outside the ELF closure model: {executable}")
        observed = subprocess.run(
            ["/usr/bin/ldd", str(executable)], check=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            timeout=30, env=runtime_environment(),
        ).stdout
    except (OSError, subprocess.SubprocessError) as error:
        raise ProvenanceError(
            f"could not inspect ELF dependencies: {executable}") from error
    require("not found" not in observed,
            f"unresolved ELF dependency for {executable}")

    absolute_path = re.compile(r"(?:=>\s+)?(/[^\s(]+)\s+\(")
    virtual_object = re.compile(r"([^\s]+)\s+\(0x[0-9a-fA-F]+\)")
    files: dict[str, dict[str, Any]] = {}
    roles: dict[str, str] = {}
    virtual_objects: set[str] = set()
    for raw_line in observed.splitlines():
        line = raw_line.strip()
        if not line or line == "statically linked":
            continue
        match = absolute_path.search(line)
        if match:
            path = Path(match.group(1)).resolve(strict=True)
            if "=>" in line:
                role = line.split("=>", 1)[0].strip()
            else:
                role = path.name
            require(role and not any(character.isspace() for character in role),
                    f"malformed ELF dependency role for {executable}: {line}")
            require(role not in roles,
                    f"duplicate ELF dependency role for {executable}: {role}")
            roles[role] = str(path)
            files[str(path)] = file_record(path)
            continue
        match = virtual_object.fullmatch(line)
        require(match is not None,
                f"unrecognized ldd output for {executable}: {line}")
        virtual_objects.add(match.group(1))
    require(files, f"ELF dependency closure is empty: {executable}")
    return {
        "policy": ELF_DYNAMIC_CLOSURE_POLICY,
        "dynamic_path_tags": path_tags,
        "files": {path: files[path] for path in sorted(files)},
        "roles": {role: roles[role] for role in sorted(roles)},
        "virtual_objects": sorted(virtual_objects),
    }


def validate_candle_elf_policy(record: dict[str, Any]) -> None:
    files = record.get("files")
    roles = record.get("roles")
    virtual_objects = record.get("virtual_objects")
    require(isinstance(files, dict), "malformed Candle ELF file closure")
    require(isinstance(roles, dict), "malformed Candle ELF role closure")
    require(record.get("dynamic_path_tags") == {},
            "unexpected Candle RPATH/RUNPATH")
    require(len(files) == len(CANDLE_ELF_OBJECTS),
            "unexpected Candle ELF dependency object count")
    require(set(roles) == CANDLE_ELF_OBJECTS,
            "unexpected Candle ELF dependency roles")
    require(set(roles.values()) == set(files),
            "Candle ELF roles do not bind the exact object closure")
    require(virtual_objects == CANDLE_ELF_VIRTUAL_OBJECTS,
            "unexpected Candle virtual ELF objects")


def validate_elf_dynamic_closure(
    executable: Path,
    record: dict[str, Any],
    *,
    allowed_dynamic_path_tags: dict[str, list[str]] | None = None,
) -> None:
    require(isinstance(record, dict), "malformed ELF dependency closure")
    require(set(record) == ELF_DYNAMIC_CLOSURE_FIELDS,
            "malformed ELF dependency closure")
    require(record["policy"] == ELF_DYNAMIC_CLOSURE_POLICY,
            "unsupported ELF dependency policy")
    observed = elf_dynamic_closure(
        executable, allowed_dynamic_path_tags=allowed_dynamic_path_tags,
    )
    require(observed == record, "ELF dependency closure mismatch")


def validate_elf_closure_record(
    record: dict[str, Any],
    label: str,
    *,
    allowed_dynamic_path_tags: dict[str, list[str]],
) -> None:
    """Check the internal semantics of a retained, relocation-safe closure."""
    require(isinstance(record, dict) and
            set(record) == ELF_DYNAMIC_CLOSURE_FIELDS,
            f"malformed {label} ELF dependency closure")
    require(record.get("policy") == ELF_DYNAMIC_CLOSURE_POLICY,
            f"unsupported {label} ELF dependency policy")
    require(record.get("dynamic_path_tags") == allowed_dynamic_path_tags,
            f"unexpected {label} RPATH/RUNPATH")
    files = record.get("files")
    roles = record.get("roles")
    virtual_objects = record.get("virtual_objects")
    require(isinstance(files, dict) and files,
            f"empty or malformed {label} ELF file closure")
    require(isinstance(roles, dict) and roles and
            set(roles.values()) == set(files),
            f"malformed {label} ELF role closure")
    require(isinstance(virtual_objects, list) and
            all(isinstance(name, str) for name in virtual_objects) and
            virtual_objects == sorted(set(virtual_objects)),
            f"malformed {label} virtual ELF objects")
    for path, identity in files.items():
        require(isinstance(path, str) and Path(path).is_absolute(),
                f"non-absolute {label} ELF object")
        require(isinstance(identity, dict) and
                set(identity) == {"bytes", "sha256"} and
                isinstance(identity["bytes"], int) and identity["bytes"] >= 0 and
                isinstance(identity["sha256"], str) and
                re.fullmatch(r"[0-9a-f]{64}", identity["sha256"]) is not None,
                f"malformed {label} ELF object identity")


def hol_runtime_record(hol_root: Path) -> dict[str, Any]:
    record = {
        "policy": "exact_hol_launchers_state_kernelid_and_elf_closure_v2",
        "files": {
            name: file_record(hol_root / name)
            for name in HOL_BOOTSTRAP_RUNTIME_FILES
        },
        "elf_closures": {
            name: elf_dynamic_closure(
                hol_root / name,
                allowed_dynamic_path_tags=HOL_ELF_ALLOWED_DYNAMIC_PATH_TAGS,
            )
            for name in HOL_BOOTSTRAP_ELF_FILES
        },
    }
    require(record["files"][".kernelidstr"] == bytes_record(HOL_KERNEL_ID_BYTES),
            "HOL kernel identifier is not the pinned stdknl identity")
    return record


def validate_hol_runtime_record(
    record: dict[str, Any],
    *,
    hol_root: Path | None = None,
) -> None:
    require(isinstance(record, dict) and set(record) == {
        "policy", "files", "elf_closures",
    }, "malformed HOL bootstrap runtime record")
    require(record.get("policy") ==
            "exact_hol_launchers_state_kernelid_and_elf_closure_v2",
            "unsupported HOL bootstrap runtime policy")
    files = record.get("files")
    closures = record.get("elf_closures")
    require(isinstance(files, dict) and
            set(files) == set(HOL_BOOTSTRAP_RUNTIME_FILES),
            "HOL bootstrap runtime file set mismatch")
    require(isinstance(closures, dict) and
            set(closures) == set(HOL_BOOTSTRAP_ELF_FILES),
            "HOL bootstrap ELF set mismatch")
    require(files.get(".kernelidstr") == bytes_record(HOL_KERNEL_ID_BYTES),
            "HOL bootstrap kernel identifier mismatch")
    for name in HOL_BOOTSTRAP_RUNTIME_FILES:
        identity = files[name]
        require(isinstance(identity, dict) and
                set(identity) == {"bytes", "sha256"},
                f"malformed HOL bootstrap runtime identity: {name}")
        if hol_root is not None:
            validate_file_record(
                hol_root / name, identity, f"HOL bootstrap runtime {name}",
            )
    for name in HOL_BOOTSTRAP_ELF_FILES:
        validate_elf_closure_record(
            closures[name], f"HOL bootstrap {name}",
            allowed_dynamic_path_tags=HOL_ELF_ALLOWED_DYNAMIC_PATH_TAGS,
        )
        if hol_root is not None:
            validate_elf_dynamic_closure(
                hol_root / name, closures[name],
                allowed_dynamic_path_tags=HOL_ELF_ALLOWED_DYNAMIC_PATH_TAGS,
            )


def _ordinary_identity_is_well_formed(value: Any) -> bool:
    return (
        isinstance(value, dict) and
        set(value) == {
            "device", "inode", "mtime_ns", "ctime_ns", "bytes", "sha256",
        } and
        all(isinstance(value[field], int) and not isinstance(value[field], bool)
            and value[field] >= 0
            for field in (
                "device", "inode", "mtime_ns", "ctime_ns", "bytes",
            )) and
        isinstance(value["sha256"], str) and
        re.fullmatch(r"[0-9a-f]{64}", value["sha256"]) is not None
    )


def _relative_path_is_canonical(relative: str) -> bool:
    path = Path(relative)
    return (
        isinstance(relative, str) and relative != "" and
        not path.is_absolute() and
        all(part not in {"", ".", ".."} for part in path.parts) and
        str(path) == relative
    )


def _canonical_json_sha256(value: Any) -> str:
    encoded = json.dumps(
        value, ensure_ascii=True, separators=(",", ":"), sort_keys=False,
    ).encode("ascii")
    return hashlib.sha256(encoded).hexdigest()


def _captured_in_root_symlink(
    path: Path,
    root: Path,
) -> dict[str, Any]:
    """Capture one stable symlink contract and its in-root ordinary payload."""
    before = path.lstat()
    require(stat.S_ISLNK(before.st_mode), f"not a symlink: {path}")
    link_text = os.readlink(path)
    after_readlink = path.lstat()
    link_fields = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
    require(
        tuple(getattr(before, field) for field in link_fields) ==
        tuple(getattr(after_readlink, field) for field in link_fields),
        f"symlink changed while being captured: {path}",
    )
    target = path.resolve(strict=True)
    root = root.resolve(strict=True)
    require(target.is_relative_to(root) and target.is_file() and
            not target.is_symlink(),
            f"symlink target escapes or is not ordinary: {path}")
    target_identity = ordinary_file_identity(target)
    final = path.lstat()
    require(
        tuple(getattr(before, field) for field in link_fields) ==
        tuple(getattr(final, field) for field in link_fields) and
        os.readlink(path) == link_text and path.resolve(strict=True) == target,
        f"symlink changed while its target was being captured: {path}",
    )
    return {
        "link_text": link_text,
        "link_identity": {
            "device": final.st_dev,
            "inode": final.st_ino,
            "mtime_ns": final.st_mtime_ns,
            "ctime_ns": final.st_ctime_ns,
        },
        "target_relative": str(target.relative_to(root)),
        "target_path": str(target),
        "target_identity": target_identity,
    }


def hol_proof_artifact_inventory(hol_root: Path) -> dict[str, Any]:
    """Bind the conservative pre-existing HOL proof-artifact closure.

    This deliberately makes no source-derivation claim. It captures every
    ordinary file below every HOL ``.hol/objs`` directory, every direct
    ``sigobj`` entry (including the exact symlink text and resolved ordinary
    payload), and the generated sources known to be read by this bootstrap.
    """
    hol_root = hol_root.resolve(strict=True)
    object_entries = []
    object_directories = sorted(hol_root.rglob(".hol/objs"))
    for object_directory in object_directories:
        metadata = object_directory.stat(follow_symlinks=False)
        require(stat.S_ISDIR(metadata.st_mode) and
                not object_directory.is_symlink(),
                f"HOL object directory is not ordinary: {object_directory}")
        for current, directories, files in os.walk(
            object_directory, topdown=True, followlinks=False,
        ):
            current_path = Path(current)
            for directory in directories:
                child = current_path / directory
                require(not child.is_symlink(),
                        f"symlink inside HOL object inventory: {child}")
            for filename in sorted(files):
                path = current_path / filename
                require(not path.is_symlink(),
                        f"symlink inside HOL object inventory: {path}")
                relative = str(path.relative_to(hol_root))
                object_entries.append({
                    "relative": relative,
                    "path": str(path),
                    "identity": ordinary_file_identity(path),
                })
    object_entries.sort(key=lambda entry: entry["relative"])
    require(len(object_entries) == HOL_PROOF_OBJECT_COUNT,
            "HOL proof-object inventory count mismatch")
    require(len({entry["relative"] for entry in object_entries}) ==
            len(object_entries),
            "duplicate HOL proof-object path")
    object_paths_sha256 = _canonical_json_sha256([
        entry["relative"] for entry in object_entries
    ])
    require(object_paths_sha256 == HOL_PROOF_OBJECT_PATHS_SHA256,
            "HOL proof-object path set mismatch")

    sigobj = hol_root / "sigobj"
    metadata = sigobj.stat(follow_symlinks=False)
    require(stat.S_ISDIR(metadata.st_mode) and not sigobj.is_symlink(),
            f"HOL sigobj is not an ordinary directory: {sigobj}")
    sigobj_entries = []
    ordinary_count = 0
    symlink_count = 0
    for path in sorted(sigobj.iterdir(), key=lambda item: item.name):
        relative = str(path.relative_to(hol_root))
        metadata = path.lstat()
        if stat.S_ISREG(metadata.st_mode):
            ordinary_count += 1
            sigobj_entries.append({
                "kind": "ordinary",
                "relative": relative,
                "path": str(path),
                "identity": ordinary_file_identity(path),
            })
        elif stat.S_ISLNK(metadata.st_mode):
            symlink_count += 1
            sigobj_entries.append({
                "kind": "symlink",
                "relative": relative,
                "path": str(path),
                **_captured_in_root_symlink(path, hol_root),
            })
        else:
            raise ProvenanceError(f"unsupported HOL sigobj entry: {path}")
    require(ordinary_count == HOL_SIGOBJ_ORDINARY_COUNT and
            symlink_count == HOL_SIGOBJ_SYMLINK_COUNT,
            "HOL sigobj inventory count mismatch")
    sigobj_contracts = [
        (["ordinary", entry["relative"]]
         if entry["kind"] == "ordinary" else
         ["symlink", entry["relative"], entry["link_text"],
          entry["target_relative"]])
        for entry in sigobj_entries
    ]
    sigobj_contracts_sha256 = _canonical_json_sha256(sigobj_contracts)
    require(sigobj_contracts_sha256 == HOL_SIGOBJ_CONTRACTS_SHA256,
            "HOL sigobj role/target contract mismatch")

    generated_sources = []
    for relative in HOL_GENERATED_PROOF_INPUTS:
        path = hol_root / relative
        generated_sources.append({
            "relative": relative,
            "path": str(path),
            "identity": ordinary_file_identity(path),
        })
    return {
        "policy": "all_hol_objs_sigobj_and_generated_proof_inputs_v1",
        "derivation_claim": "content_bound_not_independently_rebuilt",
        "structure": {
            "object_paths_sha256": object_paths_sha256,
            "sigobj_contracts_sha256": sigobj_contracts_sha256,
        },
        "object_files": object_entries,
        "sigobj_entries": sigobj_entries,
        "generated_sources": generated_sources,
    }


def validate_hol_proof_artifact_inventory(
    record: Any,
    hol_root: Path,
    *,
    require_live: bool,
) -> None:
    require(isinstance(record, dict) and set(record) == {
        "policy", "derivation_claim", "structure", "object_files",
        "sigobj_entries", "generated_sources",
    } and record.get("policy") ==
            "all_hol_objs_sigobj_and_generated_proof_inputs_v1" and
            record.get("derivation_claim") ==
            "content_bound_not_independently_rebuilt",
            "malformed HOL proof-artifact inventory")
    hol_root = Path(hol_root)
    require(record.get("structure") == {
        "object_paths_sha256": HOL_PROOF_OBJECT_PATHS_SHA256,
        "sigobj_contracts_sha256": HOL_SIGOBJ_CONTRACTS_SHA256,
    }, "HOL proof-artifact structure digest mismatch")
    object_files = record.get("object_files")
    require(isinstance(object_files, list) and
            len(object_files) == HOL_PROOF_OBJECT_COUNT,
            "HOL proof-object inventory count mismatch")
    prior = None
    for entry in object_files:
        require(isinstance(entry, dict) and set(entry) == {
            "relative", "path", "identity",
        }, "malformed HOL proof-object entry")
        relative = entry.get("relative")
        require(isinstance(relative, str) and
                _relative_path_is_canonical(relative) and
                relative > (prior or "") and
                "/.hol/objs/" in f"/{relative}" and
                entry.get("path") == str(hol_root / relative) and
                _ordinary_identity_is_well_formed(entry.get("identity")),
                "malformed HOL proof-object entry")
        prior = relative
    require(_canonical_json_sha256([
        entry["relative"] for entry in object_files
    ]) == HOL_PROOF_OBJECT_PATHS_SHA256,
            "HOL proof-object path set mismatch")

    sigobj_entries = record.get("sigobj_entries")
    require(isinstance(sigobj_entries, list) and
            len(sigobj_entries) ==
            HOL_SIGOBJ_ORDINARY_COUNT + HOL_SIGOBJ_SYMLINK_COUNT,
            "HOL sigobj inventory count mismatch")
    prior = None
    ordinary_count = 0
    symlink_count = 0
    for entry in sigobj_entries:
        require(isinstance(entry, dict), "malformed HOL sigobj entry")
        relative = entry.get("relative")
        require(isinstance(relative, str) and
                _relative_path_is_canonical(relative) and
                relative > (prior or "") and
                Path(relative).parent == Path("sigobj") and
                entry.get("path") == str(hol_root / relative),
                "malformed HOL sigobj entry")
        prior = relative
        if entry.get("kind") == "ordinary":
            ordinary_count += 1
            require(set(entry) == {"kind", "relative", "path", "identity"} and
                    _ordinary_identity_is_well_formed(entry.get("identity")),
                    "malformed ordinary HOL sigobj entry")
            continue
        require(entry.get("kind") == "symlink" and set(entry) == {
            "kind", "relative", "path", "link_text", "link_identity",
            "target_relative", "target_path", "target_identity",
        }, "malformed symlink HOL sigobj entry")
        symlink_count += 1
        link_identity = entry.get("link_identity")
        target_relative = entry.get("target_relative")
        require(isinstance(entry.get("link_text"), str) and
                isinstance(link_identity, dict) and set(link_identity) == {
                    "device", "inode", "mtime_ns", "ctime_ns",
                } and
                all(isinstance(value, int) and not isinstance(value, bool) and
                    value >= 0 for value in link_identity.values()) and
                isinstance(target_relative, str) and
                _relative_path_is_canonical(target_relative) and
                entry.get("target_path") == str(hol_root / target_relative) and
                _ordinary_identity_is_well_formed(
                    entry.get("target_identity")),
                "malformed symlink HOL sigobj entry")
    require(ordinary_count == HOL_SIGOBJ_ORDINARY_COUNT and
            symlink_count == HOL_SIGOBJ_SYMLINK_COUNT,
            "HOL sigobj kind count mismatch")
    require(_canonical_json_sha256([
        (["ordinary", entry["relative"]]
         if entry["kind"] == "ordinary" else
         ["symlink", entry["relative"], entry["link_text"],
          entry["target_relative"]])
        for entry in sigobj_entries
    ]) == HOL_SIGOBJ_CONTRACTS_SHA256,
            "HOL sigobj role/target contract mismatch")

    generated_sources = record.get("generated_sources")
    require(isinstance(generated_sources, list) and
            [entry.get("relative") if isinstance(entry, dict) else None
             for entry in generated_sources] == list(HOL_GENERATED_PROOF_INPUTS),
            "HOL generated proof-input set mismatch")
    for entry in generated_sources:
        relative = entry["relative"]
        require(set(entry) == {"relative", "path", "identity"} and
                entry.get("path") == str(hol_root / relative) and
                _ordinary_identity_is_well_formed(entry.get("identity")),
                f"malformed HOL generated proof input: {relative}")
    if require_live:
        require(record == hol_proof_artifact_inventory(hol_root),
                "HOL proof-artifact inventory changed")


def validate_executable_tool_record(record: dict[str, Any], label: str) -> None:
    require(isinstance(record, dict) and set(record) == {
        "requested_path", "symlink_target", "resolved_path", "file",
    }, f"malformed {label} tool record")
    require(isinstance(record["requested_path"], str) and
            Path(record["requested_path"]).is_absolute() and
            (record["symlink_target"] is None or
             isinstance(record["symlink_target"], str)) and
            isinstance(record["resolved_path"], str) and
            Path(record["resolved_path"]).is_absolute(),
            f"malformed {label} tool path")
    identity = record["file"]
    require(isinstance(identity, dict) and
            set(identity) == {"bytes", "sha256"} and
            isinstance(identity["bytes"], int) and identity["bytes"] >= 0 and
            isinstance(identity["sha256"], str) and
            re.fullmatch(r"[0-9a-f]{64}", identity["sha256"]) is not None,
            f"malformed {label} tool identity")


def bootstrap_host_runtime_record() -> dict[str, Any]:
    tools = {
        name: executable_tool_record(Path(path))
        for name, path in BOOTSTRAP_CONTROLLER_TOOLS.items()
    }
    return {
        "policy": "exact_controller_builder_tools_and_launch_elf_closure_v2",
        "tools": tools,
        "launch_elf_closures": {
            name: elf_dynamic_closure(Path(BOOTSTRAP_CONTROLLER_TOOLS[name]))
            for name in BOOTSTRAP_LAUNCH_ELF_TOOLS
        },
    }


def validate_bootstrap_host_runtime_record(
    record: dict[str, Any],
    *,
    require_live: bool,
) -> None:
    require(isinstance(record, dict) and set(record) == {
        "policy", "tools", "launch_elf_closures",
    }, "malformed bootstrap host runtime record")
    require(record.get("policy") ==
            "exact_controller_builder_tools_and_launch_elf_closure_v2",
            "unsupported bootstrap host runtime policy")
    tools = record.get("tools")
    closures = record.get("launch_elf_closures")
    require(isinstance(tools, dict) and
            set(tools) == set(BOOTSTRAP_CONTROLLER_TOOLS),
            "bootstrap controller tool set mismatch")
    require(isinstance(closures, dict) and
            set(closures) == set(BOOTSTRAP_LAUNCH_ELF_TOOLS),
            "bootstrap launch ELF set mismatch")
    for name, tool in tools.items():
        validate_executable_tool_record(tool, f"bootstrap controller {name}")
    for name, closure in closures.items():
        validate_elf_closure_record(
            closure, f"bootstrap launch {name}", allowed_dynamic_path_tags={},
        )
    if require_live:
        require(record == bootstrap_host_runtime_record(),
                "bootstrap host runtime changed after preflight")


def bootstrap_launch(
    cakeml_root: Path,
    hol_root: Path,
    log_path: Path,
) -> dict[str, Any]:
    bootstrap_dir = (cakeml_root / BOOTSTRAP_RELATIVE).resolve(strict=True)
    expected_dir = cakeml_root / BOOTSTRAP_RELATIVE
    require(bootstrap_dir == expected_dir and
            bootstrap_dir.is_dir() and not bootstrap_dir.is_symlink(),
            "bootstrap cwd is not the exact ordinary x64/64 directory")
    timed_argv = [str(hol_root / "bin/Holmake"), "-j1", "cake.S"]
    return {
        "cwd": str(bootstrap_dir),
        "environment": {
            "PATH": "/usr/bin:/bin",
            "LC_ALL": "C",
            "HOLDIR": str(hol_root),
        },
        "time_argv": ["/usr/bin/time", "-v", *timed_argv],
        "timed_argv": timed_argv,
        "build_command": " ".join(timed_argv),
        "log_path": str(log_path),
    }


def bootstrap_log_preamble(preflight: dict[str, Any]) -> str:
    launch = preflight["launch"]
    binding = {
        "cwd": launch["cwd"],
        "environment": launch["environment"],
        "time_argv": launch["time_argv"],
    }
    return (
        BOOTSTRAP_LOG_MARKER + "\n" +
        json.dumps(binding, separators=(",", ":"), sort_keys=True) + "\n"
    )


def _directory_identity(path: Path) -> dict[str, int | str]:
    metadata = path.stat(follow_symlinks=False)
    require(stat.S_ISDIR(metadata.st_mode) and not path.is_symlink(),
            f"lock path is not an ordinary directory: {path}")
    return {
        "path": str(path), "device": metadata.st_dev, "inode": metadata.st_ino,
    }


def validate_inherited_directory_lock(path: Path, descriptor: int) -> None:
    """Require the controller's inherited exclusive lock on this directory."""
    try:
        metadata = os.fstat(descriptor)
        fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError as error:
        raise ProvenanceError("missing inherited bootstrap directory lock") from error
    observed = _directory_identity(path)
    require(stat.S_ISDIR(metadata.st_mode) and
            (metadata.st_dev, metadata.st_ino) ==
            (observed["device"], observed["inode"]),
            "inherited bootstrap lock inode mismatch")


def _bootstrap_archive_root(preflight_path: Path) -> Path:
    return preflight_path.with_name(
        preflight_path.name + ".generated-preimage",
    )


def bootstrap_forced_output_paths(cakeml_root: Path) -> list[tuple[str, Path]]:
    result = [
        (
            f"compiler/bootstrap/compilation/x64/64/{name}",
            cakeml_root / BOOTSTRAP_RELATIVE / name,
        )
        for name in BOOTSTRAP_DIRECT_GENERATED_OUTPUTS
    ]
    translation = Path("compiler/bootstrap/translation/.hol/objs")
    for target in BOOTSTRAP_TARGETS[:-1]:
        for suffix in BOOTSTRAP_TRANSLATION_THEORY_SUFFIXES:
            relative = translation / f"{target}Theory.{suffix}"
            result.append((str(relative), cakeml_root / relative))
    final_objects = BOOTSTRAP_RELATIVE / ".hol/objs"
    for suffix in BOOTSTRAP_FINAL_THEORY_SUFFIXES:
        relative = final_objects / f"x64BootstrapTheory.{suffix}"
        result.append((str(relative), cakeml_root / relative))
    require(len(result) == 2 + 17 * 6 + 4,
            "internal bootstrap forced-output inventory mismatch")
    require(len({relative for relative, _ in result}) == len(result),
            "duplicate bootstrap forced-output path")
    return result


def bootstrap_transient_output_paths(cakeml_root: Path) -> list[tuple[str, Path]]:
    result = []
    translation = Path("compiler/bootstrap/translation/.hol/objs")
    for target in BOOTSTRAP_TARGETS[:-1]:
        for suffix in BOOTSTRAP_SCRIPT_TRANSIENT_SUFFIXES:
            relative = translation / f"{target}Script.{suffix}"
            result.append((str(relative), cakeml_root / relative))
    final_objects = BOOTSTRAP_RELATIVE / ".hol/objs"
    for suffix in BOOTSTRAP_SCRIPT_TRANSIENT_SUFFIXES:
        relative = final_objects / f"x64BootstrapScript.{suffix}"
        result.append((str(relative), cakeml_root / relative))
    require(len(result) == 18 * 2,
            "internal bootstrap transient-output inventory mismatch")
    return result


def bootstrap_dependency_output_paths(
    cakeml_root: Path,
) -> list[tuple[str, Path]]:
    result = []
    translation = Path("compiler/bootstrap/translation/.hol/make-deps")
    final = BOOTSTRAP_RELATIVE / ".hol/make-deps"
    for target in BOOTSTRAP_TARGETS[:-1]:
        for suffix in ("Script.sml.d", "Theory.sig.d", "Theory.sml.d"):
            relative = translation / f"{target}{suffix}"
            result.append((str(relative), cakeml_root / relative))
    for suffix in ("Script.sml.d", "Theory.sig.d", "Theory.sml.d"):
        relative = final / f"x64Bootstrap{suffix}"
        result.append((str(relative), cakeml_root / relative))
    require(len(result) == 18 * 3,
            "internal bootstrap dependency-output inventory mismatch")
    return result


def bootstrap_lastmaker_output_paths(
    cakeml_root: Path,
) -> list[tuple[str, Path]]:
    result = []
    for directory in (
        Path("compiler/bootstrap/translation/.hol/make-deps"),
        BOOTSTRAP_RELATIVE / ".hol/make-deps",
    ):
        relative = directory / "lastmaker"
        result.append((str(relative), cakeml_root / relative))
    return result


def bootstrap_lastmaker_bytes(hol_root: Path) -> bytes:
    return (str(hol_root / "bin/Holmake") + "\n").encode("utf-8")


def bootstrap_cleanup_output_paths(
    cakeml_root: Path,
) -> list[tuple[str, Path, str]]:
    result = [
        (relative, path, "ordinary_fresh")
        for relative, path in bootstrap_forced_output_paths(cakeml_root)
    ] + [
        (relative, path, "absent_after_success")
        for relative, path in bootstrap_transient_output_paths(cakeml_root)
    ] + [
        (relative, path, "ordinary_fresh")
        for relative, path in bootstrap_dependency_output_paths(cakeml_root)
    ] + [
        (relative, path, "exact_holmake_lastmaker")
        for relative, path in bootstrap_lastmaker_output_paths(cakeml_root)
    ]
    require(len({relative for relative, _, _ in result}) == len(result),
            "duplicate bootstrap cleanup-output path")
    return result


def _make_dependency_artifact_entries(
    root: Path,
    *,
    excluded_paths: set[str],
) -> list[dict[str, Any]]:
    entries = []
    dependency_directories = sorted(root.rglob(".hol/make-deps"))
    for dependency_directory in dependency_directories:
        metadata = dependency_directory.stat(follow_symlinks=False)
        require(stat.S_ISDIR(metadata.st_mode) and
                not dependency_directory.is_symlink(),
                f"make-dependency directory is not ordinary: {dependency_directory}")
        for current, directories, files in os.walk(
            dependency_directory, topdown=True, followlinks=False,
        ):
            current_path = Path(current)
            for directory in directories:
                child = current_path / directory
                require(not child.is_symlink(),
                        f"symlink inside make-dependency inventory: {child}")
            for filename in sorted(files):
                path = current_path / filename
                require(not path.is_symlink(),
                        f"symlink inside make-dependency inventory: {path}")
                if str(path) in excluded_paths:
                    continue
                relative = str(path.relative_to(root))
                entries.append({
                    "relative": relative,
                    "path": str(path),
                    "identity": ordinary_file_identity(path),
                })
    entries.sort(key=lambda entry: entry["relative"])
    require(len({entry["relative"] for entry in entries}) == len(entries),
            "duplicate make-dependency artifact path")
    return entries


def bootstrap_make_dependency_artifact_inventory(
    cakeml_root: Path,
    hol_root: Path,
) -> dict[str, Any]:
    """Bind every non-transitioned make-dependency input in both trees."""
    cakeml_root = cakeml_root.resolve(strict=True)
    hol_root = hol_root.resolve(strict=True)
    transitioned = {
        str(path) for _, path in (
            bootstrap_dependency_output_paths(cakeml_root) +
            bootstrap_lastmaker_output_paths(cakeml_root)
        )
    }
    hol_entries = _make_dependency_artifact_entries(
        hol_root, excluded_paths=set(),
    )
    cakeml_entries = _make_dependency_artifact_entries(
        cakeml_root, excluded_paths=transitioned,
    )
    hol_paths_sha256 = _canonical_json_sha256([
        entry["relative"] for entry in hol_entries
    ])
    cakeml_paths_sha256 = _canonical_json_sha256([
        entry["relative"] for entry in cakeml_entries
    ])
    require(len(hol_entries) == HOL_MAKE_DEPENDENCY_COUNT and
            hol_paths_sha256 == HOL_MAKE_DEPENDENCY_PATHS_SHA256,
            "HOL make-dependency artifact path set mismatch")
    require(len(cakeml_entries) == CAKEML_MAKE_DEPENDENCY_ANCESTOR_COUNT and
            cakeml_paths_sha256 ==
            CAKEML_MAKE_DEPENDENCY_ANCESTOR_PATHS_SHA256,
            "CakeML ancestor make-dependency artifact path set mismatch")
    expected_lastmaker = bytes_record(bootstrap_lastmaker_bytes(hol_root))
    for entry in hol_entries + cakeml_entries:
        if Path(entry["relative"]).name == "lastmaker":
            require({field: entry["identity"][field]
                     for field in ("bytes", "sha256")} == expected_lastmaker,
                    f"ancestor lastmaker does not name pinned Holmake: "
                    f"{entry['path']}")
    return {
        "policy": "all_hol_and_cakeml_ancestor_make_dependencies_v1",
        "derivation_claim": "content_bound_not_independently_rebuilt",
        "lastmaker_content": expected_lastmaker,
        "structure": {
            "hol_paths_sha256": hol_paths_sha256,
            "cakeml_ancestor_paths_sha256": cakeml_paths_sha256,
        },
        "hol_entries": hol_entries,
        "cakeml_ancestor_entries": cakeml_entries,
    }


def validate_bootstrap_make_dependency_artifact_inventory(
    record: Any,
    cakeml_root: Path,
    hol_root: Path,
    *,
    require_live: bool,
) -> None:
    require(isinstance(record, dict) and set(record) == {
        "policy", "derivation_claim", "lastmaker_content", "structure",
        "hol_entries", "cakeml_ancestor_entries",
    } and record.get("policy") ==
            "all_hol_and_cakeml_ancestor_make_dependencies_v1" and
            record.get("derivation_claim") ==
            "content_bound_not_independently_rebuilt",
            "malformed make-dependency artifact inventory")
    cakeml_root = Path(cakeml_root)
    hol_root = Path(hol_root)
    expected_lastmaker = bytes_record(bootstrap_lastmaker_bytes(hol_root))
    require(record.get("lastmaker_content") == expected_lastmaker,
            "make-dependency lastmaker contract mismatch")
    require(record.get("structure") == {
        "hol_paths_sha256": HOL_MAKE_DEPENDENCY_PATHS_SHA256,
        "cakeml_ancestor_paths_sha256":
            CAKEML_MAKE_DEPENDENCY_ANCESTOR_PATHS_SHA256,
    }, "make-dependency structure digest mismatch")
    transitioned = {
        str(path) for _, path in (
            bootstrap_dependency_output_paths(cakeml_root) +
            bootstrap_lastmaker_output_paths(cakeml_root)
        )
    }
    roles = (
        ("HOL", record.get("hol_entries"), hol_root,
         HOL_MAKE_DEPENDENCY_COUNT, HOL_MAKE_DEPENDENCY_PATHS_SHA256),
        ("CakeML ancestor", record.get("cakeml_ancestor_entries"), cakeml_root,
         CAKEML_MAKE_DEPENDENCY_ANCESTOR_COUNT,
         CAKEML_MAKE_DEPENDENCY_ANCESTOR_PATHS_SHA256),
    )
    for label, entries, root, expected_count, expected_paths_sha256 in roles:
        require(isinstance(entries, list) and len(entries) == expected_count,
                f"{label} make-dependency artifact count mismatch")
        prior = None
        for entry in entries:
            require(isinstance(entry, dict) and set(entry) == {
                "relative", "path", "identity",
            }, f"malformed {label} make-dependency artifact")
            relative = entry.get("relative")
            require(isinstance(relative, str) and
                    _relative_path_is_canonical(relative) and
                    relative > (prior or "") and
                    "/.hol/make-deps/" in f"/{relative}" and
                    entry.get("path") == str(root / relative) and
                    entry.get("path") not in transitioned and
                    _ordinary_identity_is_well_formed(entry.get("identity")),
                    f"malformed {label} make-dependency artifact")
            if Path(relative).name == "lastmaker":
                require({field: entry["identity"][field]
                         for field in ("bytes", "sha256")} ==
                        expected_lastmaker,
                        f"{label} lastmaker does not name pinned Holmake")
            prior = relative
        require(_canonical_json_sha256([
            entry["relative"] for entry in entries
        ]) == expected_paths_sha256,
                f"{label} make-dependency artifact path set mismatch")
    if require_live:
        require(record == bootstrap_make_dependency_artifact_inventory(
            cakeml_root, hol_root,
        ), "make-dependency artifact inventory changed")


def cake_compile_heap_record(cakeml_root: Path) -> dict[str, Any]:
    path = cakeml_root / CAKE_COMPILE_HEAP_RELATIVE
    return {
        "policy": "x64bootstrap_holmakefile_selected_compile_heap_v2",
        "derivation_claim": "content_bound_not_independently_rebuilt",
        "selection": "HMF_POLY_selects_CAKEMLDIR_cv_translator_cake_compile_heap",
        "holmakefile": committed_source_record(
            cakeml_root, CAKE_COMPILE_HEAP_HOLMAKEFILE_RELATIVE,
        ),
        "relative": str(CAKE_COMPILE_HEAP_RELATIVE),
        "path": str(path),
        "identity": ordinary_file_identity(path),
    }


def validate_cake_compile_heap_record(
    record: Any,
    cakeml_root: Path,
    *,
    require_live: bool,
) -> None:
    expected_path = cakeml_root / CAKE_COMPILE_HEAP_RELATIVE
    require(isinstance(record, dict) and set(record) == {
        "policy", "derivation_claim", "selection", "holmakefile", "relative",
        "path", "identity",
    } and record.get("policy") ==
            "x64bootstrap_holmakefile_selected_compile_heap_v2" and
            record.get("derivation_claim") ==
            "content_bound_not_independently_rebuilt" and
            record.get("selection") ==
            "HMF_POLY_selects_CAKEMLDIR_cv_translator_cake_compile_heap" and
            record.get("relative") == str(CAKE_COMPILE_HEAP_RELATIVE) and
            record.get("path") == str(expected_path) and
            _ordinary_identity_is_well_formed(record.get("identity")),
            "malformed CakeML compile-heap record")
    holmakefile = record.get("holmakefile")
    require(isinstance(holmakefile, dict) and set(holmakefile) == {
        "repository_path", "path", "bytes", "sha256", "commit_blob",
    } and holmakefile.get("repository_path") ==
            CAKE_COMPILE_HEAP_HOLMAKEFILE_RELATIVE and
            holmakefile.get("path") == str(
                cakeml_root / CAKE_COMPILE_HEAP_HOLMAKEFILE_RELATIVE
            ) and
            isinstance(holmakefile.get("commit_blob"), dict) and
            holmakefile["commit_blob"] == {
                field: holmakefile[field] for field in ("bytes", "sha256")
            }, "malformed CakeML compile-heap Holmakefile binding")
    if require_live:
        require(record == cake_compile_heap_record(cakeml_root),
                "CakeML compile heap changed")


def bootstrap_ancestor_artifact_inventory(
    cakeml_root: Path,
) -> dict[str, Any]:
    """Content-bind every pre-existing CakeML .hol/objs file not rebuilt here."""
    excluded = {
        str(path) for _, path, _ in bootstrap_cleanup_output_paths(cakeml_root)
    }
    entries = []
    object_directories = sorted(cakeml_root.rglob(".hol/objs"))
    for object_directory in object_directories:
        metadata = object_directory.stat(follow_symlinks=False)
        require(stat.S_ISDIR(metadata.st_mode) and
                not object_directory.is_symlink(),
                f"CakeML object directory is not ordinary: {object_directory}")
        for current, directories, files in os.walk(
            object_directory, topdown=True, followlinks=False,
        ):
            current_path = Path(current)
            for directory in directories:
                child = current_path / directory
                require(not child.is_symlink(),
                        f"symlink inside CakeML object inventory: {child}")
            for filename in sorted(files):
                path = current_path / filename
                require(not path.is_symlink(),
                        f"symlink inside CakeML object inventory: {path}")
                if str(path) in excluded:
                    continue
                relative = str(path.relative_to(cakeml_root))
                entries.append({
                    "relative": relative,
                    "path": str(path),
                    **ordinary_file_identity(path),
                })
    entries.sort(key=lambda entry: entry["relative"])
    require(len({entry["relative"] for entry in entries}) == len(entries),
            "duplicate CakeML ancestor artifact path")
    return {
        "policy": "all_preexisting_cakeml_hol_objs_outside_fresh_stratum_v1",
        "derivation_claim": "content_bound_not_independently_rebuilt",
        "entries": entries,
    }


def validate_bootstrap_ancestor_artifact_inventory(
    record: Any,
    cakeml_root: Path,
    *,
    require_live: bool,
) -> None:
    require(isinstance(record, dict) and set(record) == {
        "policy", "derivation_claim", "entries",
    } and record.get("policy") ==
            "all_preexisting_cakeml_hol_objs_outside_fresh_stratum_v1" and
            record.get("derivation_claim") ==
            "content_bound_not_independently_rebuilt" and
            isinstance(record.get("entries"), list),
            "malformed CakeML ancestor artifact inventory")
    excluded = {
        str(path) for _, path, _ in bootstrap_cleanup_output_paths(cakeml_root)
    }
    prior = None
    for entry in record["entries"]:
        require(isinstance(entry, dict) and set(entry) == {
            "relative", "path", "device", "inode", "mtime_ns", "ctime_ns",
            "bytes", "sha256",
        } and isinstance(entry["relative"], str) and
                entry["relative"] > (prior or "") and
                entry["path"] == str(cakeml_root / entry["relative"]) and
                "/.hol/objs/" in f"/{entry['relative']}" and
                entry["path"] not in excluded,
                "malformed CakeML ancestor artifact entry")
        prior = entry["relative"]
    if require_live:
        require(record == bootstrap_ancestor_artifact_inventory(cakeml_root),
                "CakeML ancestor artifact inventory changed")


def validate_bootstrap_output_path_inventory(
    record: dict[str, Any],
    cakeml_root: Path,
) -> None:
    """Re-derive every path that the output-preparation command may mutate."""
    outputs = record["forced_outputs"]
    receipt_path = Path(record["receipt_path"])
    require(receipt_path.is_absolute(), "bootstrap receipt path is not absolute")
    archive_root = _bootstrap_archive_root(receipt_path)
    require(outputs["preimage_archive_root"] == str(archive_root),
            "bootstrap preimage archive is not derived from the receipt")
    expected_paths = bootstrap_cleanup_output_paths(cakeml_root)
    require([(entry["relative"], entry["path"], entry["postcondition"],
              entry["preimage_archive_path"])
             for entry in outputs["entries"]] == [
                (relative, str(path), postcondition,
                 str(archive_root / relative))
                for relative, path, postcondition in expected_paths
            ], "bootstrap forced-output path inventory mismatch")


def record_bootstrap_preflight(
    candle_root: Path,
    cakeml_root: Path,
    hol_root: Path,
    log_path: Path,
    final_record_path: Path,
    output_path: Path,
) -> dict[str, Any]:
    runtime_environment({})
    candle_root = candle_root.resolve(strict=True)
    cakeml_root = cakeml_root.resolve(strict=True)
    hol_root = hol_root.resolve(strict=True)
    log_path = resolve_new_output(log_path, "bootstrap log")
    final_record_path = resolve_new_output(
        final_record_path, "final bootstrap record",
    )
    output_path = resolve_new_output(output_path, "bootstrap preflight")
    require(len({log_path, final_record_path, output_path}) == 3,
            "bootstrap receipt paths must be distinct")
    for receipt in (log_path, final_record_path, output_path):
        require(not any(receipt.is_relative_to(root)
                        for root in (candle_root, cakeml_root, hol_root)),
                "bootstrap receipts must be outside all authenticated worktrees")
    for path in (candle_root, cakeml_root, hol_root):
        require(re.fullmatch(r"/[A-Za-z0-9._/+:-]+", str(path)) is not None,
                f"bootstrap path is not safe for exact GNU-time binding: {path}")
    pins = expected_pins(candle_root)
    candle_commit = git_output(candle_root, "rev-parse", "HEAD")
    validate_git(candle_root, candle_commit, "Candle")
    validate_git(cakeml_root, pins["cakeml_commit"], "CakeML")
    validate_git(hol_root, pins["hol4_commit"], "HOL4")
    launch = bootstrap_launch(cakeml_root, hol_root, log_path)
    archive_root = _bootstrap_archive_root(output_path)
    require(not os.path.lexists(archive_root),
            "bootstrap output archive already exists")
    forced_outputs = []
    for relative, path, postcondition in bootstrap_cleanup_output_paths(cakeml_root):
        forced_outputs.append({
            "relative": relative,
            "path": str(path),
            "postcondition": postcondition,
            "preimage": (ordinary_file_identity(path)
                         if os.path.lexists(path) else None),
            "preimage_archive_path": str(archive_root / relative),
        })
    symlink_inputs = {
        name: bootstrap_symlink_input_record(cakeml_root, name)
        for name in BOOTSTRAP_SYMLINK_INPUTS
    }
    python_controller = python_controller_record(candle_root)
    expected_argv = [
        str(candle_root / "candle/cakeml_artifact_provenance.py"),
        "run-bootstrap",
        "--candle-root", str(candle_root),
        "--cakeml-root", str(cakeml_root),
        "--hol-root", str(hol_root),
        "--bootstrap-log", str(log_path),
        "--preflight", str(output_path),
        "--write", str(final_record_path),
    ]
    require(python_controller["argv"] == expected_argv,
            "bootstrap controller argv is not the canonical run command")
    record = {
        "schema": BOOTSTRAP_PREFLIGHT_SCHEMA,
        "kind": "canonical-cakeml-x64-64-bootstrap-preflight",
        **pins,
        "candle_commit": candle_commit,
        "candle_root": str(candle_root),
        "cakeml_root": str(cakeml_root),
        "hol4_root": str(hol_root),
        "receipt_path": str(output_path),
        "final_record_path": str(final_record_path),
        "controller_sources": {
            relative: committed_source_record(candle_root, relative)
            for relative in BOOTSTRAP_CONTROLLER_SOURCES
        },
        "controller_environment": bootstrap_controller_environment(),
        "python_controller": python_controller,
        "lock": _directory_identity(cakeml_root),
        "launch": launch,
        "forced_outputs": {
            "policy": "exact_18_target_outputs_dependencies_transients_lastmaker_v3",
            "preimage_archive_root": str(archive_root),
            "entries": forced_outputs,
        },
        "preserved_symlink_inputs": symlink_inputs,
        "ancestor_artifacts": bootstrap_ancestor_artifact_inventory(cakeml_root),
        "make_dependency_artifacts":
            bootstrap_make_dependency_artifact_inventory(cakeml_root, hol_root),
        "cake_compile_heap": cake_compile_heap_record(cakeml_root),
        "host_runtime": bootstrap_host_runtime_record(),
        "hol_runtime": hol_runtime_record(hol_root),
        "hol_proof_artifacts": hol_proof_artifact_inventory(hol_root),
        "trusted_host_boundary": copy.deepcopy(BOOTSTRAP_TRUST_BOUNDARY),
    }
    write_new_json(output_path, record)
    return record


def _validate_bootstrap_preflight_structure(
    record: dict[str, Any],
) -> None:
    require(isinstance(record, dict) and set(record) == {
        "schema", "kind", "cakeml_commit", "hol4_commit", "manifest_sha256",
        "candle_commit", "candle_root", "cakeml_root", "hol4_root",
        "receipt_path", "final_record_path", "controller_sources", "lock",
        "controller_environment", "python_controller", "launch",
        "forced_outputs", "preserved_symlink_inputs", "ancestor_artifacts",
        "make_dependency_artifacts", "cake_compile_heap", "host_runtime",
        "hol_runtime", "hol_proof_artifacts",
        "trusted_host_boundary",
    }, "malformed bootstrap preflight record")
    require(record.get("schema") == BOOTSTRAP_PREFLIGHT_SCHEMA,
            "unsupported bootstrap preflight schema")
    require(record.get("kind") ==
            "canonical-cakeml-x64-64-bootstrap-preflight",
            "wrong bootstrap preflight kind")
    require(record.get("trusted_host_boundary") == BOOTSTRAP_TRUST_BOUNDARY,
            "bootstrap trusted host boundary mismatch")
    sources = record.get("controller_sources")
    require(isinstance(sources, dict) and
            set(sources) == set(BOOTSTRAP_CONTROLLER_SOURCES),
            "bootstrap controller source set mismatch")
    for relative, source in sources.items():
        require(isinstance(source, dict) and set(source) == {
            "repository_path", "path", "bytes", "sha256", "commit_blob",
        } and source.get("repository_path") == relative and
                isinstance(source.get("commit_blob"), dict) and
                set(source["commit_blob"]) == {"bytes", "sha256"} and
                {field: source[field] for field in ("bytes", "sha256")} ==
                source["commit_blob"],
                f"malformed bootstrap controller source: {relative}")
    require(record.get("controller_environment") == {
        "LC_ALL": "C", "PATH": "/usr/bin:/bin",
    }, "malformed bootstrap controller environment")
    validate_python_controller_record(record.get("python_controller"))
    lock = record.get("lock")
    require(isinstance(lock, dict) and set(lock) == {"path", "device", "inode"},
            "malformed bootstrap lock identity")
    launch = record.get("launch")
    require(isinstance(launch, dict) and set(launch) == {
        "cwd", "environment", "time_argv", "timed_argv", "build_command",
        "log_path",
    }, "malformed bootstrap launch record")
    outputs = record.get("forced_outputs")
    require(isinstance(outputs, dict) and set(outputs) == {
        "policy", "preimage_archive_root", "entries",
    } and outputs.get("policy") ==
            "exact_18_target_outputs_dependencies_transients_lastmaker_v3",
            "malformed bootstrap forced-output preflight")
    entries = outputs.get("entries")
    require(isinstance(entries, list) and
            len(entries) == 108 + 18 * 2 + 18 * 3 + 2,
            "bootstrap forced-output inventory size mismatch")
    for output in entries:
        require(isinstance(output, dict) and set(output) == {
            "relative", "path", "postcondition", "preimage",
            "preimage_archive_path",
        }, "malformed bootstrap forced-output entry")
        require(output["postcondition"] in {
            "ordinary_fresh", "absent_after_success",
            "exact_holmake_lastmaker",
        }, "malformed bootstrap forced-output postcondition")
        preimage = output.get("preimage")
        require(preimage is None or
                (isinstance(preimage, dict) and set(preimage) == {
                    "device", "inode", "mtime_ns", "ctime_ns", "bytes", "sha256",
                }), "malformed bootstrap forced-output preimage")
    symlink_inputs = record.get("preserved_symlink_inputs")
    require(isinstance(symlink_inputs, dict) and
            set(symlink_inputs) == set(BOOTSTRAP_SYMLINK_INPUTS),
            "malformed bootstrap preserved symlink-input inventory")
    for name, symlink_record in symlink_inputs.items():
        validate_bootstrap_symlink_input_record(
            symlink_record, name, Path(record["cakeml_root"]),
            require_live=False,
        )
    validate_bootstrap_ancestor_artifact_inventory(
        record.get("ancestor_artifacts"), Path(record["cakeml_root"]),
        require_live=False,
    )
    validate_bootstrap_make_dependency_artifact_inventory(
        record.get("make_dependency_artifacts"),
        Path(record["cakeml_root"]), Path(record["hol4_root"]),
        require_live=False,
    )
    validate_cake_compile_heap_record(
        record.get("cake_compile_heap"), Path(record["cakeml_root"]),
        require_live=False,
    )
    validate_bootstrap_host_runtime_record(
        record.get("host_runtime"), require_live=False,
    )
    validate_hol_runtime_record(record.get("hol_runtime"))
    validate_hol_proof_artifact_inventory(
        record.get("hol_proof_artifacts"), Path(record["hol4_root"]),
        require_live=False,
    )


def validate_bootstrap_preflight(
    candle_root: Path,
    cakeml_root: Path,
    hol_root: Path,
    record: dict[str, Any],
    *,
    phase: str,
) -> None:
    require(phase in {"preflight", "post", "retained"},
            "invalid bootstrap preflight validation phase")
    _validate_bootstrap_preflight_structure(record)
    if phase == "retained":
        for field in ("candle_root", "cakeml_root", "hol4_root",
                      "receipt_path", "final_record_path"):
            require(isinstance(record[field], str) and
                    Path(record[field]).is_absolute(),
                    f"malformed retained bootstrap path: {field}")
        roots = tuple(Path(record[field]) for field in (
            "candle_root", "cakeml_root", "hol4_root",
        ))
        for receipt in (Path(record["receipt_path"]),
                        Path(record["final_record_path"]),
                        Path(record["launch"]["log_path"])):
            require(not any(receipt.is_relative_to(root) for root in roots),
                    "retained bootstrap receipt is inside an authenticated worktree")
        cakeml_string = record["cakeml_root"]
        hol_string = record["hol4_root"]
        expected_cwd = str(Path(cakeml_string) / BOOTSTRAP_RELATIVE)
        expected_timed = [
            str(Path(hol_string) / "bin/Holmake"), "-j1", "cake.S",
        ]
        launch = record["launch"]
        require(launch == {
            "cwd": expected_cwd,
            "environment": {
                "PATH": "/usr/bin:/bin", "LC_ALL": "C",
                "HOLDIR": hol_string,
            },
            "time_argv": ["/usr/bin/time", "-v", *expected_timed],
            "timed_argv": expected_timed,
            "build_command": " ".join(expected_timed),
            "log_path": launch["log_path"],
        } and Path(launch["log_path"]).is_absolute(),
                "retained bootstrap launch mismatch")
        validate_bootstrap_output_path_inventory(
            record, Path(cakeml_string),
        )
        for name, symlink_record in record["preserved_symlink_inputs"].items():
            validate_bootstrap_symlink_input_record(
                symlink_record, name, Path(cakeml_string), require_live=False,
            )
        validate_bootstrap_ancestor_artifact_inventory(
            record["ancestor_artifacts"], Path(cakeml_string),
            require_live=False,
        )
        validate_bootstrap_make_dependency_artifact_inventory(
            record["make_dependency_artifacts"], Path(cakeml_string),
            Path(hol_string), require_live=False,
        )
        validate_cake_compile_heap_record(
            record["cake_compile_heap"], Path(cakeml_string),
            require_live=False,
        )
        validate_hol_proof_artifact_inventory(
            record["hol_proof_artifacts"], Path(hol_string),
            require_live=False,
        )
        require(record["lock"]["path"] == cakeml_string,
                "retained bootstrap lock path mismatch")
        return
    candle_root = candle_root.resolve(strict=True)
    cakeml_root = cakeml_root.resolve(strict=True)
    hol_root = hol_root.resolve(strict=True)
    require(record["candle_root"] == str(candle_root) and
            record["cakeml_root"] == str(cakeml_root) and
            record["hol4_root"] == str(hol_root),
            "bootstrap preflight root mismatch")
    pins = expected_pins(candle_root)
    for field, expected in pins.items():
        require(record.get(field) == expected,
                f"bootstrap preflight {field} mismatch")
    require(record["launch"] == bootstrap_launch(
        cakeml_root, hol_root, Path(record["launch"]["log_path"]),
    ), "bootstrap preflight launch mismatch")
    require(record["controller_environment"] ==
            bootstrap_controller_environment(),
            "bootstrap controller environment changed after preflight")
    require(record["lock"] == _directory_identity(cakeml_root),
            "bootstrap lock directory identity changed")
    runtime_environment({})
    validate_git(candle_root, record["candle_commit"], "Candle")
    validate_git(cakeml_root, pins["cakeml_commit"], "CakeML")
    validate_git(hol_root, pins["hol4_commit"], "HOL4")
    require(record["controller_sources"] == {
        relative: committed_source_record(candle_root, relative)
        for relative in BOOTSTRAP_CONTROLLER_SOURCES
    }, "bootstrap controller sources changed after preflight")
    validate_python_controller_record(
        record["python_controller"], candle_root=candle_root,
    )
    validate_bootstrap_host_runtime_record(
        record["host_runtime"], require_live=True,
    )
    validate_hol_runtime_record(record["hol_runtime"], hol_root=hol_root)
    validate_hol_proof_artifact_inventory(
        record["hol_proof_artifacts"], hol_root, require_live=True,
    )
    outputs = record["forced_outputs"]
    archive_root = Path(outputs["preimage_archive_root"])
    validate_bootstrap_output_path_inventory(record, cakeml_root)
    for name, symlink_record in record["preserved_symlink_inputs"].items():
        validate_bootstrap_symlink_input_record(
            symlink_record, name, cakeml_root, require_live=True,
        )
    validate_bootstrap_ancestor_artifact_inventory(
        record["ancestor_artifacts"], cakeml_root, require_live=True,
    )
    validate_bootstrap_make_dependency_artifact_inventory(
        record["make_dependency_artifacts"], cakeml_root, hol_root,
        require_live=True,
    )
    validate_cake_compile_heap_record(
        record["cake_compile_heap"], cakeml_root, require_live=True,
    )
    if phase == "preflight":
        require(not os.path.lexists(record["launch"]["log_path"]) and
                not os.path.lexists(record["final_record_path"]),
                "bootstrap output receipt appeared after preflight")
        for output in outputs["entries"]:
            target = Path(output["path"])
            if output["preimage"] is None:
                require(not os.path.lexists(target),
                        f"bootstrap output appeared after preflight: {target}")
            else:
                validate_ordinary_file_identity(
                    target, output["preimage"],
                    f"bootstrap output preimage {output['relative']}",
                )
        require(not os.path.lexists(archive_root),
                "bootstrap transition archive appeared before preparation")
    else:
        for output in outputs["entries"]:
            target = Path(output["path"])
            archive = Path(output["preimage_archive_path"])
            if output["preimage"] is None:
                require(not os.path.lexists(archive),
                        f"unexpected bootstrap preimage archive: {archive}")
            else:
                validate_file_record(
                    archive,
                    {field: output["preimage"][field]
                     for field in ("bytes", "sha256")},
                    f"bootstrap preimage archive {output['relative']}",
                )
            if output["postcondition"] == "absent_after_success":
                require(not os.path.lexists(target),
                        f"bootstrap transient survived successful target: {target}")
            else:
                require(target.is_file() and not target.is_symlink(),
                        f"bootstrap did not freshly produce: {target}")
            if output["postcondition"] == "exact_holmake_lastmaker":
                value, _ = captured_ordinary_file(target)
                require(value == bootstrap_lastmaker_bytes(hol_root),
                        f"bootstrap lastmaker does not name pinned Holmake: {target}")
            if (output["postcondition"] in {
                    "ordinary_fresh", "exact_holmake_lastmaker",
            } and
                    output["preimage"] is not None):
                postimage = ordinary_file_identity(target)
                require(any(postimage[field] != output["preimage"][field]
                            for field in ("inode", "mtime_ns", "ctime_ns")),
                        f"bootstrap output was not freshly replaced: {target}")


def _write_new_bytes(path: Path, value: bytes, mode: int = 0o644) -> None:
    require(path.parent.is_dir() and not path.parent.is_symlink(),
            f"output parent is not an ordinary directory: {path.parent}")
    try:
        descriptor = os.open(
            path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, mode,
        )
    except OSError as error:
        raise ProvenanceError(f"refusing to overwrite output: {path}") from error
    try:
        offset = 0
        while offset < len(value):
            offset += os.write(descriptor, value[offset:])
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def prepare_bootstrap_output(
    candle_root: Path,
    cakeml_root: Path,
    hol_root: Path,
    preflight: dict[str, Any],
) -> None:
    validate_bootstrap_preflight(
        candle_root, cakeml_root, hol_root, preflight, phase="preflight",
    )
    outputs = preflight["forced_outputs"]
    archive_root = Path(outputs["preimage_archive_root"])
    preimages = [entry for entry in outputs["entries"]
                 if entry["preimage"] is not None]
    if preimages:
        try:
            os.mkdir(archive_root, 0o755)
        except OSError as error:
            raise ProvenanceError(
                "could not exclusively create bootstrap preimage archive",
            ) from error
    # Copy and validate every preimage before removing any warm-tree output.
    for output in preimages:
        target = Path(output["path"])
        archive = Path(output["preimage_archive_path"])
        archive.parent.mkdir(parents=True, exist_ok=True)
        value, identity = captured_ordinary_file(target)
        require(identity == {
            field: output["preimage"][field] for field in ("bytes", "sha256")
        }, f"bootstrap output changed before archival: {target}")
        _write_new_bytes(archive, value)
    for output in preimages:
        target = Path(output["path"])
        validate_ordinary_file_identity(
            target, output["preimage"],
            f"bootstrap output before removal {output['relative']}",
        )
        os.unlink(target)
    require(not any(os.path.lexists(entry["path"])
                    for entry in outputs["entries"]),
            "bootstrap generated outputs could not all be made fresh")


def bootstrap_forced_output_transitions(
    preflight: dict[str, Any],
) -> list[dict[str, Any]]:
    transitions = []
    for output in preflight["forced_outputs"]["entries"]:
        preimage = output["preimage"]
        archive = (None if preimage is None else
                   captured_ordinary_file(
                       Path(output["preimage_archive_path"]),
                   )[1])
        transitions.append({
            "relative": output["relative"],
            "postcondition": output["postcondition"],
            "preimage": copy.deepcopy(preimage),
            "preimage_archive": archive,
            "postimage": (
                None if output["postcondition"] == "absent_after_success"
                else ordinary_file_identity(Path(output["path"]))
            ),
        })
    return transitions


def bootstrap_symlink_input_transitions(
    preflight: dict[str, Any],
) -> dict[str, Any]:
    cakeml_root = Path(preflight["cakeml_root"])
    return {
        name: {
            "preimage": copy.deepcopy(preimage),
            "postimage": bootstrap_symlink_input_record(cakeml_root, name),
        }
        for name, preimage in preflight["preserved_symlink_inputs"].items()
    }


def validate_bootstrap_symlink_input_transitions(
    preflight: dict[str, Any],
    transitions: Any,
    *,
    require_live: bool,
) -> None:
    entries = preflight["preserved_symlink_inputs"]
    cakeml_root = Path(preflight["cakeml_root"])
    require(isinstance(transitions, dict) and
            set(transitions) == set(entries),
            "malformed bootstrap preserved symlink-input transitions")
    for name, preimage in entries.items():
        transition = transitions[name]
        require(isinstance(transition, dict) and set(transition) == {
            "preimage", "postimage",
        } and transition.get("preimage") == preimage,
                "malformed bootstrap preserved symlink-input transition")
        validate_bootstrap_symlink_input_record(
            transition.get("postimage"), name, cakeml_root,
            require_live=require_live,
        )
        postimage = transition["postimage"]
        require(postimage["link_identity"] == preimage["link_identity"] and
                postimage["link_text"] == preimage["link_text"] and
                {field: postimage["target_identity"][field]
                 for field in ("bytes", "sha256")} ==
                {field: preimage["target_identity"][field]
                 for field in ("bytes", "sha256")},
                f"bootstrap tracked symlink or target content changed: {name}")


def validate_bootstrap_forced_output_transitions(
    preflight: dict[str, Any],
    transitions: Any,
    *,
    require_live: bool,
) -> None:
    entries = preflight["forced_outputs"]["entries"]
    require(isinstance(transitions, list) and len(transitions) == len(entries),
            "malformed bootstrap forced-output transitions")
    for output, transition in zip(entries, transitions):
        require(isinstance(transition, dict) and set(transition) == {
            "relative", "postcondition", "preimage", "preimage_archive",
            "postimage",
        } and transition.get("relative") == output["relative"] and
                transition.get("postcondition") == output["postcondition"] and
                transition.get("preimage") == output["preimage"],
                "malformed bootstrap forced-output transition")
        postimage = transition.get("postimage")
        if output["postcondition"] == "absent_after_success":
            require(postimage is None,
                    "bootstrap transient unexpectedly has a postimage")
        else:
            require(isinstance(postimage, dict) and set(postimage) == {
                "device", "inode", "mtime_ns", "ctime_ns", "bytes", "sha256",
            }, "malformed bootstrap forced-output postimage")
            if output["postcondition"] == "exact_holmake_lastmaker":
                require(
                    {field: postimage[field] for field in ("bytes", "sha256")} ==
                    bytes_record(bootstrap_lastmaker_bytes(
                        Path(preflight["hol4_root"]),
                    )),
                    "bootstrap lastmaker postimage does not name pinned Holmake",
                )
        preimage = output["preimage"]
        archive = transition.get("preimage_archive")
        if preimage is None:
            require(archive is None,
                    "unexpected bootstrap forced-output preimage archive")
        else:
            require(isinstance(archive, dict) and
                    set(archive) == {"bytes", "sha256"} and archive == {
                        field: preimage[field] for field in ("bytes", "sha256")
                    }, "malformed bootstrap forced-output preimage archive")
        if require_live:
            if output["postcondition"] == "absent_after_success":
                require(not os.path.lexists(output["path"]),
                        "bootstrap transient reappeared after success")
            else:
                require(ordinary_file_identity(Path(output["path"])) == postimage,
                        "bootstrap forced-output postimage changed")
            if preimage is not None:
                validate_file_record(
                    Path(output["preimage_archive_path"]), archive,
                    f"bootstrap preimage archive {output['relative']}",
                )


def validate_bootstrap_log(
    log: str,
    build_command: str,
    *,
    expected_preamble: str | None = None,
) -> None:
    """Require one complete trailing GNU-time -v record for the exact build."""
    lines = log.splitlines()
    if expected_preamble is not None:
        preamble_lines = expected_preamble.splitlines()
        require(lines[:len(preamble_lines)] == preamble_lines and
                lines.count(BOOTSTRAP_LOG_MARKER) == 1,
                "bootstrap log has wrong or duplicate controller preamble")
    require(len(lines) >= len(GNU_TIME_FOOTER_LABELS),
            "bootstrap log has no complete GNU-time footer")
    footer = lines[-len(GNU_TIME_FOOTER_LABELS):]
    expected_command = f'\tCommand being timed: "{build_command}"'
    require(footer[0] == expected_command,
            "bootstrap log command does not match the pinned x64 cake.S build")
    decimal_fields = {"User time (seconds)", "System time (seconds)"}
    elapsed_field = "Elapsed (wall clock) time (h:mm:ss or m:ss)"
    for line, label in zip(footer[1:-1], GNU_TIME_FOOTER_LABELS[1:-1]):
        prefix = f"\t{label}: "
        require(line.startswith(prefix),
                f"malformed GNU-time footer field: {label}")
        value = line.removeprefix(prefix)
        if label in decimal_fields:
            valid = re.fullmatch(r"[0-9]+(?:\.[0-9]+)?", value) is not None
        elif label == "Percent of CPU this job got":
            valid = re.fullmatch(r"[0-9]+%", value) is not None
        elif label == elapsed_field:
            valid = re.fullmatch(
                r"(?:[0-9]+:)?[0-9]+:[0-9]+(?:\.[0-9]+)?", value,
            ) is not None
        else:
            valid = re.fullmatch(r"[0-9]+", value) is not None
        require(valid, f"malformed GNU-time footer value: {label}")
    require(footer[-1] == "\tExit status: 0",
            "bootstrap GNU-time footer does not record final exit status 0")
    require(lines.count(expected_command) == 1,
            "bootstrap log has duplicate or missing GNU-time command records")
    require(lines.count("\tExit status: 0") == 1,
            "bootstrap log has duplicate or missing successful exit status")
    require(not any(line.startswith("Command exited with non-zero status")
                    for line in lines),
            "bootstrap log records a non-zero command exit")
    require(lines.count("Writing cv to file: cake.S") == 1,
            "bootstrap log lacks unique cake.S emission evidence")
    require(lines.count('Exporting theory "x64Bootstrap" ... done.') == 1,
            "bootstrap log lacks unique x64Bootstrap export evidence")
    require(lines.count("Holmake: Building 18 theory files") == 1,
            "bootstrap planner did not report exactly 18 theory targets")
    target_pattern = re.compile(r"Holmake: \[([0-9]+)/([0-9]+)\] ([A-Za-z0-9_]+)")
    observed_targets = [
        (index, int(match.group(1)), int(match.group(2)), match.group(3))
        for index, line in enumerate(lines)
        if (match := target_pattern.fullmatch(line)) is not None
    ]
    expected_targets = [
        (index, 18, name) for index, name in enumerate(BOOTSTRAP_TARGETS, 1)
    ]
    require([(ordinal, total, name)
             for _, ordinal, total, name in observed_targets] == expected_targets,
            "bootstrap log does not prove the exact ordered 18-target rebuild")
    write_index = lines.index("Writing cv to file: cake.S")
    export_index = lines.index('Exporting theory "x64Bootstrap" ... done.')
    footer_index = len(lines) - len(GNU_TIME_FOOTER_LABELS)
    require(write_index < export_index < observed_targets[-1][0] == footer_index - 1,
            "bootstrap completion evidence is not in exact final order")


def record_bootstrap(
    candle_root: Path,
    cakeml_root: Path,
    hol_root: Path,
    log_path: Path,
    preflight_path: Path,
    output_path: Path,
    *,
    before_publish: Callable[[], None] | None = None,
    after_publish: Callable[[], None] | None = None,
) -> dict[str, Any]:
    runtime_environment({})
    candle_root = candle_root.resolve(strict=True)
    cakeml_root = cakeml_root.resolve(strict=True)
    hol_root = hol_root.resolve(strict=True)
    preflight_path = preflight_path.resolve(strict=True)
    preflight_bytes, preflight_identity = captured_ordinary_file(preflight_path)
    try:
        preflight = json.loads(preflight_bytes.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ProvenanceError("malformed captured bootstrap preflight") from error
    require(isinstance(preflight, dict), "bootstrap preflight is not an object")
    require(preflight.get("receipt_path") == str(preflight_path),
            "bootstrap preflight path mismatch")
    log_path = log_path.resolve(strict=True)
    require(preflight["launch"]["log_path"] == str(log_path),
            "bootstrap log path differs from preflight")
    output_path = output_path.absolute()
    require(preflight["final_record_path"] == str(output_path) and
            not os.path.lexists(output_path),
            "final bootstrap record path differs or already exists")
    require(preflight.get("python_controller") ==
            python_controller_record(candle_root),
            "final bootstrap phase is not the original controller process")
    validate_bootstrap_preflight(
        candle_root, cakeml_root, hol_root, preflight, phase="post",
    )
    log_bytes, log_identity = captured_ordinary_file(log_path)
    try:
        log = log_bytes.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ProvenanceError("bootstrap log is not strict UTF-8") from error
    build_command = preflight["launch"]["build_command"]
    validate_bootstrap_log(
        log, build_command,
        expected_preamble=bootstrap_log_preamble(preflight),
    )
    bootstrap_dir = Path(preflight["launch"]["cwd"])
    inputs = {
        name: bootstrap_input_file_record(bootstrap_dir, name)
        for name in BOOTSTRAP_INPUTS
    }
    transitions = bootstrap_forced_output_transitions(preflight)
    symlink_transitions = bootstrap_symlink_input_transitions(preflight)
    record = {
        "schema": BOOTSTRAP_PROVENANCE_SCHEMA,
        "kind": "verified-cakeml-x64-64-bootstrap",
        "cakeml_commit": preflight["cakeml_commit"],
        "hol4_commit": preflight["hol4_commit"],
        "manifest_sha256": preflight["manifest_sha256"],
        "candle_commit": preflight["candle_commit"],
        "candle_root": str(candle_root),
        "cakeml_root": str(cakeml_root),
        "hol4_root": str(hol_root),
        "build_command": build_command,
        "preflight": {
            "path": str(preflight_path), **preflight_identity,
        },
        "bootstrap_log": {
            "path": str(log_path),
            **log_identity,
        },
        "inputs": inputs,
        "host_runtime": copy.deepcopy(preflight["host_runtime"]),
        "hol_runtime": copy.deepcopy(preflight["hol_runtime"]),
        "python_controller": copy.deepcopy(preflight["python_controller"]),
        "controller_environment": copy.deepcopy(
            preflight["controller_environment"],
        ),
        "forced_output_transitions": transitions,
        "preserved_symlink_input_transitions": symlink_transitions,
    }
    write_new_json(
        output_path, record,
        before_publish=before_publish,
        after_publish=after_publish,
    )
    return record


def validate_bootstrap_record(
    candle_root: Path,
    cakeml_root: Path,
    record_path: Path,
) -> dict[str, Any]:
    candle_root = candle_root.resolve()
    cakeml_root = cakeml_root.resolve()
    record_path = record_path.resolve()
    record = load_object(record_path)
    require(set(record) == {
        "schema", "kind", "cakeml_commit", "hol4_commit", "manifest_sha256",
        "candle_commit", "candle_root", "cakeml_root", "hol4_root",
        "build_command", "preflight", "bootstrap_log", "inputs",
        "host_runtime", "hol_runtime", "python_controller",
        "controller_environment", "forced_output_transitions",
        "preserved_symlink_input_transitions",
    }, "malformed bootstrap provenance record")
    require(record.get("schema") == BOOTSTRAP_PROVENANCE_SCHEMA,
            "unsupported bootstrap provenance schema")
    require(record.get("kind") == "verified-cakeml-x64-64-bootstrap",
            "wrong bootstrap provenance kind")
    pins = expected_pins(candle_root)
    for field, expected in pins.items():
        require(record.get(field) == expected, f"bootstrap {field} mismatch")
    require(record.get("candle_root") == str(candle_root),
            "bootstrap Candle root mismatch")
    require(record.get("cakeml_root") == str(cakeml_root),
            "bootstrap CakeML root mismatch")
    hol_root = Path(record.get("hol4_root", "")).resolve()
    preflight_record = record.get("preflight")
    require(isinstance(preflight_record, dict) and
            set(preflight_record) == {"path", "bytes", "sha256"},
            "malformed bootstrap preflight identity")
    preflight_path = Path(preflight_record["path"])
    preflight_bytes, observed_preflight = captured_ordinary_file(preflight_path)
    require(observed_preflight == {
        field: preflight_record[field] for field in ("bytes", "sha256")
    }, "bootstrap preflight changed")
    try:
        preflight = json.loads(preflight_bytes.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ProvenanceError("malformed captured bootstrap preflight") from error
    require(isinstance(preflight, dict) and
            preflight.get("receipt_path") == str(preflight_path),
            "bootstrap preflight path/shape mismatch")
    validate_bootstrap_preflight(
        candle_root, cakeml_root, hol_root, preflight, phase="post",
    )
    require(record.get("candle_commit") == preflight["candle_commit"] and
            record.get("cakeml_commit") == preflight["cakeml_commit"] and
            record.get("hol4_commit") == preflight["hol4_commit"] and
            record.get("manifest_sha256") == preflight["manifest_sha256"],
            "bootstrap final/preflight pin mismatch")
    build_command = preflight["launch"]["build_command"]
    require(record.get("build_command") == build_command,
            "bootstrap command record mismatch")
    log_record = record.get("bootstrap_log")
    require(isinstance(log_record, dict) and
            set(log_record) == {"path", "bytes", "sha256"},
            "malformed bootstrap log record")
    log_path = Path(log_record["path"])
    log_bytes, observed_log = captured_ordinary_file(log_path)
    require(observed_log == {
        field: log_record[field] for field in ("bytes", "sha256")
    }, "bootstrap log changed")
    try:
        log = log_bytes.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ProvenanceError("bootstrap log is not strict UTF-8") from error
    validate_bootstrap_log(
        log, build_command,
        expected_preamble=bootstrap_log_preamble(preflight),
    )
    require(record.get("host_runtime") == preflight["host_runtime"] and
            record.get("hol_runtime") == preflight["hol_runtime"] and
            record.get("python_controller") == preflight["python_controller"] and
            record.get("controller_environment") ==
            preflight["controller_environment"],
            "bootstrap final runtime differs from preflight")
    inputs = record.get("inputs")
    require(isinstance(inputs, dict) and set(inputs) == set(BOOTSTRAP_INPUTS),
            "bootstrap input set mismatch")
    bootstrap_dir = cakeml_root / BOOTSTRAP_RELATIVE
    for name in BOOTSTRAP_INPUTS:
        require(bootstrap_input_file_record(bootstrap_dir, name) == inputs[name],
                f"bootstrap input provenance mismatch: {name}")
    validate_bootstrap_forced_output_transitions(
        preflight, record.get("forced_output_transitions"), require_live=True,
    )
    validate_bootstrap_symlink_input_transitions(
        preflight, record.get("preserved_symlink_input_transitions"),
        require_live=True,
    )
    return record


def materialize_linked_bootstrap(
    build_dir: Path,
    source_record_path: Path,
    bootstrap: dict[str, Any],
) -> dict[str, Any]:
    """Create relocation-safe authenticated copies of bootstrap evidence."""
    source_preflight = Path(bootstrap["preflight"]["path"])
    source_log = Path(bootstrap["bootstrap_log"]["path"])
    local_preflight = build_dir / LINKED_BOOTSTRAP_PREFLIGHT
    local_log = build_dir / LINKED_BOOTSTRAP_LOG
    require(not local_preflight.is_symlink(),
            "refusing symlink destination for linked bootstrap preflight")
    shutil.copyfile(source_preflight, local_preflight)
    validate_file_record(
        local_preflight,
        {field: bootstrap["preflight"][field]
         for field in ("bytes", "sha256")},
        "materialized bootstrap preflight",
    )
    require(not local_log.is_symlink(),
            "refusing symlink destination for linked bootstrap log")
    shutil.copyfile(source_log, local_log)
    validate_file_record(
        local_log,
        {field: bootstrap["bootstrap_log"][field]
         for field in ("bytes", "sha256")},
        "materialized bootstrap log",
    )
    durable = copy.deepcopy(bootstrap)
    durable["kind"] = "candle-linked-bootstrap-provenance-copy"
    durable["source_bootstrap_record"] = file_record(source_record_path)
    durable["preflight"] = {
        "path": LINKED_BOOTSTRAP_PREFLIGHT,
        **file_record(local_preflight),
    }
    durable["bootstrap_log"] = {
        "path": LINKED_BOOTSTRAP_LOG,
        **file_record(local_log),
    }
    local_record = build_dir / LINKED_BOOTSTRAP_RECORD
    require(not local_record.is_symlink(),
            "refusing symlink destination for linked bootstrap record")
    local_record.write_text(
        json.dumps(durable, indent=2, sort_keys=True) + "\n", encoding="utf-8",
    )
    return durable


def validate_linked_bootstrap_copy(
    build_dir: Path,
    record: dict[str, Any],
    pins: dict[str, str],
) -> dict[str, Any]:
    """Validate durable bootstrap semantics without external worktree paths."""
    local_record = build_dir / LINKED_BOOTSTRAP_RECORD
    local_preflight = build_dir / LINKED_BOOTSTRAP_PREFLIGHT
    local_log = build_dir / LINKED_BOOTSTRAP_LOG
    validate_file_record(
        local_record, record.get("bootstrap_record", {}),
        "linked bootstrap provenance copy",
    )
    validate_file_record(
        local_preflight, record.get("bootstrap_preflight", {}),
        "linked bootstrap preflight copy",
    )
    validate_file_record(
        local_log, record.get("bootstrap_log", {}), "linked bootstrap log copy",
    )
    bootstrap = load_object(local_record)
    require(set(bootstrap) == {
        "schema", "kind", "cakeml_commit", "hol4_commit", "manifest_sha256",
        "candle_commit", "candle_root", "cakeml_root", "hol4_root",
        "build_command", "preflight", "bootstrap_log", "inputs",
        "host_runtime", "hol_runtime", "python_controller",
        "controller_environment", "forced_output_transitions",
        "preserved_symlink_input_transitions",
        "source_bootstrap_record",
    }, "malformed linked bootstrap provenance copy")
    require(bootstrap.get("schema") == BOOTSTRAP_PROVENANCE_SCHEMA,
            "unsupported linked bootstrap provenance schema")
    require(bootstrap.get("kind") == "candle-linked-bootstrap-provenance-copy",
            "wrong linked bootstrap provenance kind")
    for field, expected in pins.items():
        require(bootstrap.get(field) == expected,
                f"linked bootstrap {field} mismatch")
    require(bootstrap.get("cakeml_commit") == record.get("cakeml_commit"),
            "linked bootstrap CakeML revision mismatch")
    require(bootstrap.get("hol4_commit") == record.get("hol4_commit"),
            "linked bootstrap HOL4 revision mismatch")
    cakeml_root = bootstrap.get("cakeml_root")
    hol4_root = bootstrap.get("hol4_root")
    require(isinstance(cakeml_root, str) and Path(cakeml_root).is_absolute(),
            "malformed linked bootstrap CakeML root")
    require(isinstance(hol4_root, str) and Path(hol4_root).is_absolute(),
            "malformed linked bootstrap HOL4 root")
    preflight_record = bootstrap.get("preflight")
    require(isinstance(preflight_record, dict) and
            set(preflight_record) == {"path", "bytes", "sha256"} and
            preflight_record.get("path") == LINKED_BOOTSTRAP_PREFLIGHT,
            "malformed linked bootstrap preflight identity")
    require({field: preflight_record[field] for field in ("bytes", "sha256")} ==
            record.get("bootstrap_preflight"),
            "linked bootstrap preflight record mismatch")
    preflight = load_object(local_preflight)
    validate_bootstrap_preflight(
        Path("/retained"), Path("/retained"), Path("/retained"), preflight,
        phase="retained",
    )
    require(preflight.get("cakeml_commit") == bootstrap.get("cakeml_commit") and
            preflight.get("hol4_commit") == bootstrap.get("hol4_commit") and
            preflight.get("manifest_sha256") == bootstrap.get("manifest_sha256") and
            preflight.get("candle_commit") == bootstrap.get("candle_commit"),
            "linked bootstrap preflight pin mismatch")
    build_command = preflight["launch"]["build_command"]
    require(bootstrap.get("build_command") == build_command,
            "linked bootstrap command record mismatch")
    source_record = bootstrap.get("source_bootstrap_record")
    require(isinstance(source_record, dict) and
            set(source_record) == {"bytes", "sha256"},
            "malformed source bootstrap record identity")
    log_record = bootstrap.get("bootstrap_log")
    require(isinstance(log_record, dict) and
            set(log_record) == {"path", "bytes", "sha256"} and
            log_record.get("path") == LINKED_BOOTSTRAP_LOG,
            "malformed linked bootstrap log identity")
    require({field: log_record[field] for field in ("bytes", "sha256")} ==
            record.get("bootstrap_log"),
            "linked bootstrap log record mismatch")
    log = local_log.read_text(encoding="utf-8", errors="strict")
    validate_bootstrap_log(
        log, build_command, expected_preamble=bootstrap_log_preamble(preflight),
    )
    validate_bootstrap_host_runtime_record(
        bootstrap.get("host_runtime"), require_live=False,
    )
    require(bootstrap.get("host_runtime") == preflight.get("host_runtime") and
            bootstrap.get("hol_runtime") == preflight.get("hol_runtime") and
            bootstrap.get("python_controller") ==
            preflight.get("python_controller") and
            bootstrap.get("controller_environment") ==
            preflight.get("controller_environment"),
            "linked bootstrap runtime differs from preflight")
    validate_hol_runtime_record(bootstrap.get("hol_runtime"))
    validate_python_controller_record(bootstrap.get("python_controller"))
    validate_bootstrap_forced_output_transitions(
        preflight, bootstrap.get("forced_output_transitions"), require_live=False,
    )
    validate_bootstrap_symlink_input_transitions(
        preflight, bootstrap.get("preserved_symlink_input_transitions"),
        require_live=False,
    )
    inputs = bootstrap.get("inputs")
    require(isinstance(inputs, dict) and set(inputs) == set(BOOTSTRAP_INPUTS),
            "linked bootstrap input set mismatch")
    direct_transitions = {
        transition["relative"].rsplit("/", 1)[-1]: transition
        for transition in bootstrap["forced_output_transitions"]
        if transition["relative"].rsplit("/", 1)[-1] in
        BOOTSTRAP_DIRECT_GENERATED_OUTPUTS
    }
    require(set(direct_transitions) == set(BOOTSTRAP_DIRECT_GENERATED_OUTPUTS),
            "linked bootstrap direct-output transition set mismatch")
    for name in BOOTSTRAP_INPUTS:
        source = build_dir / ("cake.S.bootstrap" if name == "cake.S" else name)
        validate_file_record(source, inputs[name], f"linked bootstrap input {name}")
        if name in direct_transitions:
            require(inputs[name] == {
                field: direct_transitions[name]["postimage"][field]
                for field in ("bytes", "sha256")
            }, f"linked bootstrap input/transition mismatch: {name}")
        if name in BOOTSTRAP_SYMLINK_INPUTS:
            transition = bootstrap["preserved_symlink_input_transitions"][name]
            require(inputs[name] == {
                field: transition["postimage"]["target_identity"][field]
                for field in ("bytes", "sha256")
            }, f"linked bootstrap symlink target/input mismatch: {name}")
    return bootstrap


def cake_patch_derivation(
    build_dir: Path,
    bootstrap_cake_record: dict[str, Any],
    patch_path: Path,
) -> dict[str, Any]:
    """Reapply the exact patch and require the recorded assembly postimage."""
    preimage = build_dir / "cake.S.bootstrap"
    postimage = build_dir / "cake.S"
    validate_file_record(preimage, bootstrap_cake_record, "CakeML assembly preimage")
    patch = file_record(patch_path)
    expected_postimage = file_record(postimage)
    with tempfile.TemporaryDirectory(prefix="candle-cake-patch-") as temporary:
        candidate = Path(temporary) / "cake.S"
        shutil.copyfile(preimage, candidate)
        try:
            subprocess.run(
                ["/usr/bin/patch", "--batch", "--forward", "cake.S", str(patch_path)],
                check=True, cwd=temporary, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, text=True, timeout=60,
                env=runtime_environment({}),
            )
        except (OSError, subprocess.SubprocessError) as error:
            raise ProvenanceError("could not reproduce CakeML assembly patch") from error
        require(file_record(candidate) == expected_postimage,
                "CakeML assembly patch postimage mismatch")
    return {
        "policy": "gnu_patch_exact_preimage_and_postimage_v1",
        "preimage": bootstrap_cake_record,
        "patch": patch,
        "postimage": expected_postimage,
    }


def executable_tool_record(requested_path: Path) -> dict[str, Any]:
    """Bind both a fixed tool pathname and the ordinary file it resolves to."""
    require(requested_path.is_absolute() and os.path.lexists(requested_path),
            f"missing host tool: {requested_path}")
    symlink_target = (os.readlink(requested_path)
                      if requested_path.is_symlink() else None)
    resolved = requested_path.resolve(strict=True)
    require(resolved.is_file() and not resolved.is_symlink(),
            f"host tool does not resolve to an ordinary file: {requested_path}")
    return {
        "requested_path": str(requested_path),
        "symlink_target": symlink_target,
        "resolved_path": str(resolved),
        "file": file_record(resolved),
    }


def native_toolchain_record() -> dict[str, Any]:
    runtime_environment({})
    environment = {"LC_ALL": "C", "PATH": "/usr/bin:/bin"}

    def cc_output(*arguments: str) -> bytes:
        try:
            return subprocess.run(
                ["/usr/bin/cc", *arguments], check=True,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                timeout=30, env=environment,
            ).stdout
        except (OSError, subprocess.SubprocessError) as error:
            raise ProvenanceError(
                f"could not query host C compiler: {' '.join(arguments)}",
            ) from error

    query_arguments = {
        "dumpmachine": ("-dumpmachine",),
        "dumpfullversion": ("-dumpfullversion",),
        "dumpspecs": ("-dumpspecs",),
    }
    queries = {}
    for name, arguments in query_arguments.items():
        output = cc_output(*arguments)
        queries[name] = {
            "argv": ["/usr/bin/cc", *arguments],
            "bytes": len(output),
            "sha256": hashlib.sha256(output).hexdigest(),
        }
    tools = {
        name: executable_tool_record(Path(path))
        for name, path in NATIVE_TOOL_PATHS.items()
    }
    for name, program in (
        ("cc1", "cc1"),
        ("collect2", "collect2"),
        ("lto_wrapper", "lto-wrapper"),
    ):
        output = cc_output(f"-print-prog-name={program}").decode(
            "utf-8", errors="strict",
        ).strip()
        path = Path(output)
        require(path.is_absolute(), f"C compiler returned non-absolute {program}")
        tools[name] = executable_tool_record(path)
    return {
        "policy": "exact_native_link_tool_files_and_cc_queries_v1",
        "tools": tools,
        "cc_queries": queries,
    }


def tool_wrapper_source(tool_path: str, log_name: str) -> str:
    require(re.fullmatch(r"[a-z]+", log_name) is not None,
            "invalid native tool log name")
    require(Path(tool_path).is_absolute(), "native tool wrapper path is not absolute")
    return (
        "#!/bin/sh\n"
        "set -eu\n"
        "{\n"
        "  printf 'BEGIN %s\\n' \"$#\"\n"
        "  printf 'ARG %s\\n' \"$@\"\n"
        f"}} >> .candle-native-tools/{log_name}.argv\n"
        f"exec {tool_path} \"$@\"\n"
    )


def parse_tool_argv_log(path: Path, tool_path: str) -> list[list[str]]:
    require(path.is_file() and not path.is_symlink(),
            f"missing native tool invocation log: {path}")
    lines = path.read_text(encoding="utf-8", errors="strict").splitlines()
    result: list[list[str]] = []
    offset = 0
    while offset < len(lines):
        match = re.fullmatch(r"BEGIN ([0-9]+)", lines[offset])
        require(match is not None, f"malformed native tool invocation log: {path}")
        count = int(match.group(1))
        arguments = lines[offset + 1:offset + 1 + count]
        require(len(arguments) == count and
                all(argument.startswith("ARG ") for argument in arguments),
                f"truncated native tool invocation log: {path}")
        result.append([tool_path, *(argument[4:] for argument in arguments)])
        offset += count + 1
    return result


def files_are_byte_identical(left: Path, right: Path) -> bool:
    with left.open("rb") as left_file, right.open("rb") as right_file:
        while True:
            left_block = left_file.read(1024 * 1024)
            right_block = right_file.read(1024 * 1024)
            if left_block != right_block:
                return False
            if not left_block:
                return True


def _driver_commands(
    diagnostic_output: str,
    toolchain: dict[str, Any],
) -> dict[str, list[list[str]]]:
    expected_paths = {
        name: details["requested_path"]
        for name, details in toolchain["tools"].items()
        if name in {"cc1", "collect2"}
    }
    expected_resolved = {
        name: details["resolved_path"]
        for name, details in toolchain["tools"].items()
        if name in {"cc1", "collect2"}
    }
    result: dict[str, list[list[str]]] = {"cc1": [], "collect2": []}
    for line in diagnostic_output.splitlines():
        if not line.startswith(" "):
            continue
        try:
            arguments = shlex.split(line)
        except ValueError as error:
            raise ProvenanceError("malformed C compiler diagnostic command") from error
        if not arguments:
            continue
        for name in result:
            if arguments[0] in {expected_paths[name], expected_resolved[name]}:
                result[name].append(arguments)
                break
    require(len(result["cc1"]) == 3,
            "native relink did not execute the exact three expected cc1 stages")
    require(len(result["collect2"]) == 1,
            "native relink did not execute exactly one collect2 link stage")
    return result


def expected_native_driver_commands(
    build_dir: Path,
    toolchain: dict[str, Any],
) -> dict[str, list[list[str]]]:
    """Ask the authenticated GCC driver for its exact non-executing plan."""
    for name in ("cake.S", "basis_ffi.c"):
        require((build_dir / name).is_file(),
                f"missing native driver-plan input: {name}")
    with tempfile.TemporaryDirectory(
        prefix="candle-native-plan-",
    ) as temporary:
        plan_root = Path(temporary)
        tools_dir = plan_root / ".candle-native-tools"
        tools_dir.mkdir()
        (plan_root / NATIVE_LINK_ENVIRONMENT["TMPDIR"]).mkdir()
        for name in ("as", "ld"):
            wrapper = tools_dir / name
            wrapper.write_text(
                tool_wrapper_source(NATIVE_TOOL_PATHS[name], name),
                encoding="utf-8",
            )
            wrapper.chmod(0o755)
        (plan_root / "cake.S").write_bytes(b"")
        (plan_root / "basis_ffi.c").write_bytes(b"")
        arguments = [*NATIVE_LINK_CC_ARGV, "-###"]
        try:
            completed = subprocess.run(
                arguments, check=True, cwd=plan_root,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                timeout=60, env=NATIVE_LINK_ENVIRONMENT,
            )
        except (OSError, subprocess.SubprocessError) as error:
            raise ProvenanceError(
                "could not derive the native GCC command plan",
            ) from error
    result = _driver_commands(completed.stderr, toolchain)
    assemblers: list[list[str]] = []
    for line in completed.stderr.splitlines():
        if not line.startswith(" "):
            continue
        try:
            command = shlex.split(line)
        except ValueError as error:
            raise ProvenanceError("malformed GCC assembler command plan") from error
        if command and Path(command[0]).name == "as":
            command[0] = NATIVE_TOOL_PATHS["as"]
            assemblers.append(command)
    require(len(assemblers) == 2,
            "native GCC command plan does not contain exactly two assemblers")
    result["as"] = assemblers
    return result


def native_link_derivation(build_dir: Path) -> dict[str, Any]:
    """Freshly relink exact inputs, capture the host commands, and byte-compare."""
    runtime_environment({})
    installed = build_dir / "cake"
    installed_identity = file_record(installed)
    inputs = {
        name: file_record(build_dir / name)
        for name in NATIVE_LINK_INPUTS
    }
    toolchain = native_toolchain_record()
    with tempfile.TemporaryDirectory(prefix="candle-native-link-") as temporary:
        replay = Path(temporary)
        for name in NATIVE_LINK_INPUTS:
            shutil.copyfile(build_dir / name, replay / name)
            validate_file_record(replay / name, inputs[name], f"native relink {name}")
        tools_dir = replay / ".candle-native-tools"
        tools_dir.mkdir()
        (replay / NATIVE_LINK_ENVIRONMENT["TMPDIR"]).mkdir()
        wrapper_records = {}
        for name in ("as", "ld"):
            wrapper = tools_dir / name
            source = tool_wrapper_source(NATIVE_TOOL_PATHS[name], name)
            wrapper.write_text(source, encoding="utf-8")
            wrapper.chmod(0o755)
            wrapper_records[name] = file_record(wrapper)
        try:
            completed = subprocess.run(
                list(NATIVE_LINK_MAKE_ARGV), check=True, cwd=replay,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                timeout=1800, env=NATIVE_LINK_ENVIRONMENT,
            )
        except (OSError, subprocess.SubprocessError) as error:
            raise ProvenanceError("fresh deterministic CakeML relink failed") from error
        stdout_lines = [line for line in completed.stdout.splitlines() if line]
        require(len(stdout_lines) == 1,
                "native relink make output does not identify one exact C command")
        require(shlex.split(stdout_lines[0]) == list(NATIVE_LINK_CC_ARGV),
                "native relink C command mismatch")
        tool_commands = {
            name: parse_tool_argv_log(
                tools_dir / f"{name}.argv", NATIVE_TOOL_PATHS[name],
            )
            for name in ("as", "ld")
        }
        require(len(tool_commands["as"]) == 2,
                "native relink did not execute exactly two assembler commands")
        require(len(tool_commands["ld"]) == 1,
                "native relink did not execute exactly one linker command")
        candidate = replay / "cake"
        candidate_identity = file_record(candidate)
        with candidate.open("rb") as source:
            require(source.read(4) == b"\x7fELF",
                    "fresh native relink candidate is not ELF")
        require(files_are_byte_identical(candidate, installed),
                "fresh native relink is not byte-identical to installed cake")
        driver_commands = _driver_commands(completed.stderr, toolchain)
    require(candidate_identity == installed_identity,
            "native relink candidate identity differs from installed cake")
    return {
        "policy": "fresh_exact_inputs_commands_and_byte_comparison_v1",
        "inputs": inputs,
        "environment": dict(NATIVE_LINK_ENVIRONMENT),
        "commands": {
            "make": [list(NATIVE_LINK_MAKE_ARGV)],
            "cc": [list(NATIVE_LINK_CC_ARGV)],
            "cc1": driver_commands["cc1"],
            "as": tool_commands["as"],
            "collect2": driver_commands["collect2"],
            "ld": tool_commands["ld"],
        },
        "tool_wrappers": wrapper_records,
        "toolchain": toolchain,
        "candidate_elf": candidate_identity,
        "installed_elf": installed_identity,
        "comparison": "byte_for_byte_equal",
        "trusted_host_boundary": copy.deepcopy(NATIVE_LINK_TRUSTED_BOUNDARY),
    }


def validate_native_link_derivation(
    build_dir: Path,
    record: dict[str, Any],
) -> None:
    require(isinstance(record, dict) and set(record) == {
        "policy", "inputs", "environment", "commands", "tool_wrappers",
        "toolchain", "candidate_elf", "installed_elf", "comparison",
        "trusted_host_boundary",
    }, "malformed native link derivation")
    require(record.get("policy") ==
            "fresh_exact_inputs_commands_and_byte_comparison_v1",
            "unsupported native link derivation policy")
    require(record.get("environment") == NATIVE_LINK_ENVIRONMENT,
            "native link environment mismatch")
    require(record.get("trusted_host_boundary") == NATIVE_LINK_TRUSTED_BOUNDARY,
            "native link trusted host boundary mismatch")
    inputs = record.get("inputs")
    require(isinstance(inputs, dict) and set(inputs) == set(NATIVE_LINK_INPUTS),
            "native link input set mismatch")
    for name in NATIVE_LINK_INPUTS:
        validate_file_record(build_dir / name, inputs[name], f"native link {name}")
    commands = record.get("commands")
    require(isinstance(commands, dict) and set(commands) == {
        "make", "cc", "cc1", "as", "collect2", "ld",
    }, "malformed native link command set")
    require(commands["make"] == [list(NATIVE_LINK_MAKE_ARGV)],
            "native link make command mismatch")
    require(commands["cc"] == [list(NATIVE_LINK_CC_ARGV)],
            "native link C command mismatch")
    require(isinstance(commands["cc1"], list) and len(commands["cc1"]) == 3,
            "native link cc1 command set mismatch")
    require(isinstance(commands["as"], list) and len(commands["as"]) == 2 and
            all(command and command[0] == NATIVE_TOOL_PATHS["as"]
                for command in commands["as"]),
            "native link assembler command set mismatch")
    require(isinstance(commands["collect2"], list) and
            len(commands["collect2"]) == 1,
            "native link collect2 command set mismatch")
    require(isinstance(commands["ld"], list) and len(commands["ld"]) == 1 and
            commands["ld"][0] and
            commands["ld"][0][0] == NATIVE_TOOL_PATHS["ld"],
            "native link linker command set mismatch")
    toolchain = native_toolchain_record()
    require(record.get("toolchain") == toolchain,
            "native link host toolchain mismatch")
    for name in ("cc1", "collect2"):
        allowed = {
            toolchain["tools"][name]["requested_path"],
            toolchain["tools"][name]["resolved_path"],
        }
        require(all(command and command[0] in allowed
                    for command in commands[name]),
                f"native link {name} command path mismatch")
    expected_commands = expected_native_driver_commands(build_dir, toolchain)
    require(commands["cc1"] == expected_commands["cc1"],
            "native link cc1 commands differ from the authenticated driver plan")
    require(commands["as"] == expected_commands["as"],
            "native link assembler commands differ from the authenticated driver plan")
    require(commands["collect2"] == expected_commands["collect2"],
            "native link collect2 command differs from the authenticated driver plan")
    require(commands["ld"][0][1:] == commands["collect2"][0][1:],
            "native linker command differs from the collect2 link plan")
    wrappers = record.get("tool_wrappers")
    require(isinstance(wrappers, dict) and set(wrappers) == {"as", "ld"},
            "native link tool wrapper set mismatch")
    for name in wrappers:
        source = tool_wrapper_source(NATIVE_TOOL_PATHS[name], name).encode()
        require(wrappers[name] == {
            "bytes": len(source), "sha256": hashlib.sha256(source).hexdigest(),
        }, f"native link {name} wrapper mismatch")
    installed = file_record(build_dir / "cake")
    require(record.get("candidate_elf") == installed and
            record.get("installed_elf") == installed and
            record.get("comparison") == "byte_for_byte_equal",
            "native link candidate/installed comparison mismatch")
    observed = native_link_derivation(build_dir)
    require(observed == record,
            "fresh native link derivation differs from the linked receipt")


def record_linked(
    candle_root: Path,
    cakeml_root: Path,
    bootstrap_record_path: Path,
    output_path: Path,
) -> dict[str, Any]:
    candle_root = candle_root.resolve()
    bootstrap_record_path = bootstrap_record_path.resolve()
    bootstrap = validate_bootstrap_record(
        candle_root, cakeml_root, bootstrap_record_path,
    )
    candle_head = git_output(candle_root, "rev-parse", "HEAD")
    validate_git(candle_root, candle_head, "Candle")
    build_dir = validate_build_directory(candle_root)
    inputs = bootstrap["inputs"]
    for name in ("config_enc_str.txt", "candle_boot.ml", "basis_ffi.c", "Makefile"):
        validate_file_record(build_dir / name, inputs[name], f"copied {name}")
    cake_commit, hol_commit, version_output = version_details(build_dir / "cake")
    require(cake_commit == bootstrap["cakeml_commit"],
            "linked compiler CakeML revision mismatch")
    require(hol_commit == bootstrap["hol4_commit"],
            "linked compiler HOL4 revision mismatch")
    materialize_linked_bootstrap(build_dir, bootstrap_record_path, bootstrap)
    patch_derivation = cake_patch_derivation(
        build_dir, inputs["cake.S"], candle_root / "candle/cake.S.patch",
    )
    link_derivation = native_link_derivation(build_dir)
    record = {
        "schema": LINKED_PROVENANCE_SCHEMA,
        "kind": "candle-linked-pinned-cakeml",
        "candle_commit": candle_head,
        "cakeml_commit": cake_commit,
        "hol4_commit": hol_commit,
        "manifest_sha256": bootstrap["manifest_sha256"],
        "bootstrap_record": file_record(build_dir / LINKED_BOOTSTRAP_RECORD),
        "bootstrap_preflight": file_record(build_dir / LINKED_BOOTSTRAP_PREFLIGHT),
        "bootstrap_log": file_record(build_dir / LINKED_BOOTSTRAP_LOG),
        "cake_patch": file_record(candle_root / "candle/cake.S.patch"),
        "cake_patch_derivation": patch_derivation,
        "native_link_derivation": link_derivation,
        "outputs": {name: file_record(build_dir / name) for name in LINKED_OUTPUTS},
        "runtime_elf_closure": elf_dynamic_closure(build_dir / "cake"),
        "version_output_sha256": hashlib.sha256(version_output.encode()).hexdigest(),
    }
    require(not output_path.is_symlink(),
            "refusing symlink destination for linked provenance record")
    require(output_path.parent.resolve() == build_dir.resolve() and
            output_path.name == LINKED_RECORD_RELATIVE.name,
            "linked provenance destination must be the Candle build record")
    output_path = output_path.resolve()
    validate_candle_elf_policy(record["runtime_elf_closure"])
    output_path.write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8",
    )
    return record


def validate_linked_record(candle_root: Path) -> dict[str, Any]:
    candle_root = candle_root.resolve()
    record_path = candle_root / LINKED_RECORD_RELATIVE
    record = load_object(record_path)
    require(set(record) == {
        "schema", "kind", "candle_commit", "cakeml_commit", "hol4_commit",
        "manifest_sha256", "bootstrap_record", "bootstrap_preflight",
        "bootstrap_log", "cake_patch",
        "cake_patch_derivation", "native_link_derivation", "outputs",
        "runtime_elf_closure",
        "version_output_sha256",
    }, "malformed linked provenance record")
    require(record.get("schema") == LINKED_PROVENANCE_SCHEMA,
            "unsupported linked provenance schema")
    require(record.get("kind") == "candle-linked-pinned-cakeml",
            "wrong linked provenance kind")
    candle_head = record.get("candle_commit")
    require(isinstance(candle_head, str) and len(candle_head) == 40,
            "linked Candle revision missing")
    validate_git(candle_root, candle_head, "Candle")
    pins = expected_pins(candle_root)
    for field, expected in pins.items():
        require(record.get(field) == expected, f"linked {field} mismatch")
    validate_file_record(
        candle_root / "candle/cake.S.patch", record.get("cake_patch", {}),
        "CakeML assembly patch",
    )
    outputs = record.get("outputs")
    require(isinstance(outputs, dict) and set(outputs) == set(LINKED_OUTPUTS),
            "linked output set mismatch")
    build_dir = validate_build_directory(candle_root)
    for name in LINKED_OUTPUTS:
        validate_file_record(build_dir / name, outputs[name], f"linked {name}")
    bootstrap = validate_linked_bootstrap_copy(build_dir, record, pins)
    observed_derivation = cake_patch_derivation(
        build_dir, bootstrap["inputs"]["cake.S"],
        candle_root / "candle/cake.S.patch",
    )
    require(observed_derivation == record.get("cake_patch_derivation"),
            "CakeML assembly patch derivation mismatch")
    validate_native_link_derivation(
        build_dir, record.get("native_link_derivation"),
    )
    validate_root_runtime_aliases(candle_root, outputs)
    validate_elf_dynamic_closure(
        build_dir / "cake", record.get("runtime_elf_closure", {}),
    )
    validate_candle_elf_policy(record["runtime_elf_closure"])
    cake_commit, hol_commit, version_output = version_details(build_dir / "cake")
    require(cake_commit == pins["cakeml_commit"], "runtime CakeML revision mismatch")
    require(hol_commit == pins["hol4_commit"], "runtime HOL4 revision mismatch")
    require(hashlib.sha256(version_output.encode()).hexdigest()
            == record.get("version_output_sha256"),
            "runtime version output mismatch")
    return record


def _write_all(descriptor: int, value: bytes) -> None:
    offset = 0
    while offset < len(value):
        offset += os.write(descriptor, value[offset:])


def run_bootstrap(
    candle_root: Path,
    cakeml_root: Path,
    hol_root: Path,
    log_path: Path,
    preflight_path: Path,
    output_path: Path,
) -> dict[str, Any]:
    """Run the complete canonical bootstrap in this one controller process."""
    bootstrap_controller_environment()
    candle_root = candle_root.resolve(strict=True)
    cakeml_root = cakeml_root.resolve(strict=True)
    hol_root = hol_root.resolve(strict=True)
    try:
        lock_descriptor = os.open(
            cakeml_root,
            os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
        )
    except OSError as error:
        raise ProvenanceError("could not open exact CakeML lock directory") from error
    log_descriptor: int | None = None
    child: subprocess.Popen[bytes] | None = None
    old_handlers: dict[int, Any] = {}
    received_signal: int | None = None
    try:
        try:
            fcntl.flock(lock_descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as error:
            raise ProvenanceError(
                "CakeML checkout is already locked by another bootstrap controller",
            ) from error
        validate_inherited_directory_lock(cakeml_root, lock_descriptor)

        def handle_signal(signum: int, _frame: Any) -> None:
            nonlocal received_signal
            received_signal = signum
            if child is not None and child.poll() is None:
                try:
                    os.killpg(child.pid, signum)
                except ProcessLookupError:
                    pass

        for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            old_handlers[signum] = signal.signal(signum, handle_signal)
        preflight = record_bootstrap_preflight(
            candle_root, cakeml_root, hol_root, log_path, output_path,
            preflight_path,
        )
        require(received_signal is None,
                "bootstrap signal arrived during preflight")
        log_path = Path(preflight["launch"]["log_path"])
        try:
            log_descriptor = os.open(
                log_path,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                0o600,
            )
        except OSError as error:
            raise ProvenanceError(
                f"refusing to overwrite bootstrap log: {log_path}",
            ) from error
        log_metadata = os.fstat(log_descriptor)
        named_log = log_path.stat(follow_symlinks=False)
        require(stat.S_ISREG(log_metadata.st_mode) and
                (log_metadata.st_dev, log_metadata.st_ino) ==
                (named_log.st_dev, named_log.st_ino),
                "bootstrap log path changed during creation")
        _write_all(log_descriptor, bootstrap_log_preamble(preflight).encode())
        os.fsync(log_descriptor)
        prepare_bootstrap_output(
            candle_root, cakeml_root, hol_root, preflight,
        )
        require(received_signal is None,
                "bootstrap signal arrived during output preparation")
        child = subprocess.Popen(
            preflight["launch"]["time_argv"],
            cwd=preflight["launch"]["cwd"],
            env=preflight["launch"]["environment"],
            stdin=subprocess.DEVNULL,
            stdout=log_descriptor,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        return_code = child.wait()
        if received_signal is not None:
            raise ProvenanceError(
                f"bootstrap controller received signal {received_signal}",
            )
        require(return_code == 0,
                f"canonical bootstrap exited with status {return_code}")
        os.fsync(log_descriptor)
        after_log = os.fstat(log_descriptor)
        named_log = log_path.stat(follow_symlinks=False)
        require((after_log.st_dev, after_log.st_ino) ==
                (log_metadata.st_dev, log_metadata.st_ino) ==
                (named_log.st_dev, named_log.st_ino),
                "bootstrap log inode changed during proof")
        os.fchmod(log_descriptor, 0o444)
        os.close(log_descriptor)
        log_descriptor = None
        validate_inherited_directory_lock(cakeml_root, lock_descriptor)

        def require_no_prepublication_signal() -> None:
            require(received_signal is None,
                    "bootstrap signal arrived before final receipt publication")

        return record_bootstrap(
            candle_root, cakeml_root, hol_root, log_path, preflight_path,
            output_path,
            before_publish=require_no_prepublication_signal,
            after_publish=require_no_prepublication_signal,
        )
    finally:
        for signum, handler in old_handlers.items():
            signal.signal(signum, handler)
        if child is not None and child.poll() is None:
            try:
                os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                child.wait(timeout=30)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                child.wait()
        if log_descriptor is not None:
            try:
                os.fsync(log_descriptor)
                os.fchmod(log_descriptor, 0o444)
            finally:
                os.close(log_descriptor)
        os.close(lock_descriptor)


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)

    run_parser = subparsers.add_parser("run-bootstrap")
    run_parser.add_argument("--candle-root", type=Path, required=True)
    run_parser.add_argument("--cakeml-root", type=Path, required=True)
    run_parser.add_argument("--hol-root", type=Path, required=True)
    run_parser.add_argument("--bootstrap-log", type=Path, required=True)
    run_parser.add_argument("--preflight", type=Path, required=True)
    run_parser.add_argument("--write", type=Path, required=True)

    check_parser = subparsers.add_parser("check-bootstrap")
    check_parser.add_argument("--candle-root", type=Path, required=True)
    check_parser.add_argument("--cakeml-root", type=Path, required=True)
    check_parser.add_argument("--record", type=Path, required=True)

    linked_parser = subparsers.add_parser("record-linked")
    linked_parser.add_argument("--candle-root", type=Path, required=True)
    linked_parser.add_argument("--cakeml-root", type=Path, required=True)
    linked_parser.add_argument("--bootstrap-record", type=Path, required=True)
    linked_parser.add_argument("--write", type=Path, required=True)

    runtime_parser = subparsers.add_parser("check-linked")
    runtime_parser.add_argument("--candle-root", type=Path, required=True)

    arguments = parser.parse_args()
    if arguments.command == "run-bootstrap":
        run_bootstrap(
            arguments.candle_root, arguments.cakeml_root, arguments.hol_root,
            arguments.bootstrap_log, arguments.preflight, arguments.write,
        )
        print(f"canonical bootstrap provenance recorded: {arguments.write}")
    elif arguments.command == "check-bootstrap":
        validate_bootstrap_record(
            arguments.candle_root, arguments.cakeml_root, arguments.record,
        )
        print("bootstrap provenance PASS")
    elif arguments.command == "record-linked":
        record_linked(
            arguments.candle_root, arguments.cakeml_root,
            arguments.bootstrap_record, arguments.write,
        )
        print(f"linked CakeML provenance recorded: {arguments.write}")
    else:
        validate_linked_record(arguments.candle_root)
        print("linked CakeML provenance PASS")


if __name__ == "__main__":
    main()
