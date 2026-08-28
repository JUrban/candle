#!/usr/bin/env python3
"""Fail-closed provenance records for the pinned local CakeML handoff."""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any


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
)
HOL_BOOTSTRAP_ELF_FILES = (
    "bin/Holmake",
    "bin/hol",
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
    "bootstrap-provenance.json",
    "bootstrap.log",
)
BOOTSTRAP_RELATIVE = Path("compiler/bootstrap/compilation/x64/64")
MANIFEST_RELATIVE = Path("candle/flyspeck_manifest.json")
LINKED_RECORD_RELATIVE = Path("candle/build/cakeml-build-provenance.json")
BOOTSTRAP_PROVENANCE_SCHEMA = 2
LINKED_PROVENANCE_SCHEMA = 3
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
LINKED_BOOTSTRAP_LOG = "bootstrap.log"


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


def git_output(root: Path, *arguments: str) -> str:
    return subprocess.run(
        git_command(root, *arguments), check=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        env=git_environment(),
    ).stdout.strip()


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
    return {
        "policy": "exact_hol_launchers_state_and_elf_closure_v1",
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


def validate_hol_runtime_record(
    record: dict[str, Any],
    *,
    hol_root: Path | None = None,
) -> None:
    require(isinstance(record, dict) and set(record) == {
        "policy", "files", "elf_closures",
    }, "malformed HOL bootstrap runtime record")
    require(record.get("policy") ==
            "exact_hol_launchers_state_and_elf_closure_v1",
            "unsupported HOL bootstrap runtime policy")
    files = record.get("files")
    closures = record.get("elf_closures")
    require(isinstance(files, dict) and
            set(files) == set(HOL_BOOTSTRAP_RUNTIME_FILES),
            "HOL bootstrap runtime file set mismatch")
    require(isinstance(closures, dict) and
            set(closures) == set(HOL_BOOTSTRAP_ELF_FILES),
            "HOL bootstrap ELF set mismatch")
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


def validate_bootstrap_log(log: str, build_command: str) -> None:
    """Require one complete trailing GNU-time -v record for the exact build."""
    lines = log.splitlines()
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
    target_indices = [
        index for index, line in enumerate(lines)
        if re.fullmatch(r"Holmake: \[([0-9]+)/\1\] x64Bootstrap", line)
    ]
    require(len(target_indices) == 1,
            "bootstrap log lacks unique completed x64Bootstrap target evidence")
    write_index = lines.index("Writing cv to file: cake.S")
    export_index = lines.index('Exporting theory "x64Bootstrap" ... done.')
    footer_index = len(lines) - len(GNU_TIME_FOOTER_LABELS)
    require(write_index < export_index < target_indices[0] == footer_index - 1,
            "bootstrap completion evidence is not in exact final order")


def record_bootstrap(
    candle_root: Path,
    cakeml_root: Path,
    hol_root: Path,
    log_path: Path,
    output_path: Path,
) -> dict[str, Any]:
    candle_root = candle_root.resolve()
    cakeml_root = cakeml_root.resolve()
    hol_root = hol_root.resolve()
    log_path = log_path.resolve()
    output_path = output_path.resolve()
    pins = expected_pins(candle_root)
    validate_git(cakeml_root, pins["cakeml_commit"], "CakeML")
    validate_git(hol_root, pins["hol4_commit"], "HOL4")
    require(log_path.is_file() and not log_path.is_symlink(),
            "bootstrap log must be an ordinary file")
    log = log_path.read_text(encoding="utf-8", errors="replace")
    build_command = f"env HOLDIR={hol_root} {hol_root}/bin/Holmake -j1 cake.S"
    validate_bootstrap_log(log, build_command)
    bootstrap_dir = cakeml_root / BOOTSTRAP_RELATIVE
    inputs = {name: file_record(bootstrap_dir / name) for name in BOOTSTRAP_INPUTS}
    record = {
        "schema": BOOTSTRAP_PROVENANCE_SCHEMA,
        "kind": "verified-cakeml-x64-64-bootstrap",
        **pins,
        "cakeml_root": str(cakeml_root),
        "hol4_root": str(hol_root),
        "build_command": build_command,
        "bootstrap_log": {
            "path": str(log_path),
            **file_record(log_path),
        },
        "inputs": inputs,
        "hol_runtime": hol_runtime_record(hol_root),
    }
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(
        json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8",
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
        "cakeml_root", "hol4_root", "build_command", "bootstrap_log", "inputs",
        "hol_runtime",
    }, "malformed bootstrap provenance record")
    require(record.get("schema") == BOOTSTRAP_PROVENANCE_SCHEMA,
            "unsupported bootstrap provenance schema")
    require(record.get("kind") == "verified-cakeml-x64-64-bootstrap",
            "wrong bootstrap provenance kind")
    pins = expected_pins(candle_root)
    for field, expected in pins.items():
        require(record.get(field) == expected, f"bootstrap {field} mismatch")
    require(record.get("cakeml_root") == str(cakeml_root),
            "bootstrap CakeML root mismatch")
    hol_root = Path(record.get("hol4_root", "")).resolve()
    build_command = f"env HOLDIR={hol_root} {hol_root}/bin/Holmake -j1 cake.S"
    require(record.get("build_command") == build_command,
            "bootstrap command record mismatch")
    validate_git(cakeml_root, pins["cakeml_commit"], "CakeML")
    validate_git(hol_root, pins["hol4_commit"], "HOL4")
    log_record = record.get("bootstrap_log")
    require(isinstance(log_record, dict) and
            set(log_record) == {"path", "bytes", "sha256"},
            "malformed bootstrap log record")
    log_path = Path(log_record["path"])
    require(not log_path.is_symlink(), "bootstrap log must be an ordinary file")
    validate_file_record(
        log_path, {key: log_record[key] for key in ("bytes", "sha256")},
        "bootstrap log",
    )
    log = log_path.read_text(encoding="utf-8", errors="replace")
    validate_bootstrap_log(log, build_command)
    validate_hol_runtime_record(record.get("hol_runtime"), hol_root=hol_root)
    inputs = record.get("inputs")
    require(isinstance(inputs, dict) and set(inputs) == set(BOOTSTRAP_INPUTS),
            "bootstrap input set mismatch")
    bootstrap_dir = cakeml_root / BOOTSTRAP_RELATIVE
    for name in BOOTSTRAP_INPUTS:
        validate_file_record(bootstrap_dir / name, inputs[name], f"bootstrap {name}")
    return record


def materialize_linked_bootstrap(
    build_dir: Path,
    source_record_path: Path,
    bootstrap: dict[str, Any],
) -> dict[str, Any]:
    """Create relocation-safe authenticated copies of bootstrap evidence."""
    source_log = Path(bootstrap["bootstrap_log"]["path"])
    local_log = build_dir / LINKED_BOOTSTRAP_LOG
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
    local_log = build_dir / LINKED_BOOTSTRAP_LOG
    validate_file_record(
        local_record, record.get("bootstrap_record", {}),
        "linked bootstrap provenance copy",
    )
    validate_file_record(
        local_log, record.get("bootstrap_log", {}), "linked bootstrap log copy",
    )
    bootstrap = load_object(local_record)
    require(set(bootstrap) == {
        "schema", "kind", "cakeml_commit", "hol4_commit", "manifest_sha256",
        "cakeml_root", "hol4_root", "build_command", "bootstrap_log", "inputs",
        "hol_runtime", "source_bootstrap_record",
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
    build_command = f"env HOLDIR={hol4_root} {hol4_root}/bin/Holmake -j1 cake.S"
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
    log = local_log.read_text(encoding="utf-8", errors="replace")
    validate_bootstrap_log(log, build_command)
    validate_hol_runtime_record(bootstrap.get("hol_runtime"))
    inputs = bootstrap.get("inputs")
    require(isinstance(inputs, dict) and set(inputs) == set(BOOTSTRAP_INPUTS),
            "linked bootstrap input set mismatch")
    for name in BOOTSTRAP_INPUTS:
        source = build_dir / ("cake.S.bootstrap" if name == "cake.S" else name)
        validate_file_record(source, inputs[name], f"linked bootstrap input {name}")
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
        "manifest_sha256", "bootstrap_record", "bootstrap_log", "cake_patch",
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


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)

    record_parser = subparsers.add_parser("record-bootstrap")
    record_parser.add_argument("--candle-root", type=Path, required=True)
    record_parser.add_argument("--cakeml-root", type=Path, required=True)
    record_parser.add_argument("--hol-root", type=Path, required=True)
    record_parser.add_argument("--bootstrap-log", type=Path, required=True)
    record_parser.add_argument("--write", type=Path, required=True)

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
    if arguments.command == "record-bootstrap":
        record_bootstrap(
            arguments.candle_root, arguments.cakeml_root, arguments.hol_root,
            arguments.bootstrap_log, arguments.write,
        )
        print(f"bootstrap provenance recorded: {arguments.write}")
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
