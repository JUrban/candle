#!/usr/bin/env python3
"""Materialize and run a non-promotable Flyspeck OCaml-parser diagnostic.

The diagnostic is deliberately narrower than a Candle run.  It authenticates
an explicitly selected pilot or all-inventory profile, prepares only the exact
profile-bound source bytes, and submits them to a dedicated
``caml_parser$run`` runtime protocol.  It never substitutes CakeML's
``parse_prog`` parser and never uses the Candle REPL as a parser oracle.

No current linked compiler is assumed to implement that protocol.  The
controller first performs a capability handshake with an empty stdin and
stops before sending corpus bytes unless the linked executable explicitly
identifies itself as parser-only, without inference or evaluation.
"""

from __future__ import annotations

import sys

# On direct execution, reject a non-isolated interpreter before importing any
# module other than the built-in ``sys``.  Tests may import this module under a
# normal harness, but no materialize/run CLI action is reachable that way.
_EARLY_REQUIRED_FLAGS = {
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
    # The pinned interpreter enables UTF-8 mode under this controller's exact
    # LC_ALL=C startup.  Record and require that observed mode explicitly.
    "utf8_mode": 1,
    "warn_default_encoding": 0,
    "safe_path": True,
    "int_max_str_digits": 4300,
}
if __name__ == "__main__":
    _early_observed = {
        name: getattr(sys.flags, name) for name in _EARLY_REQUIRED_FLAGS
    }
    if (_early_observed != _EARLY_REQUIRED_FLAGS or
            dict(sys._xoptions) != {} or list(sys.warnoptions) != []):
        raise SystemExit(
            "parser diagnostic rejected: direct execution requires "
            "/usr/bin/python3 -I -S"
        )

import argparse
import ctypes
import errno
import fcntl
import hashlib
import json
import os
import re
import select
import shutil
import signal
import stat
import subprocess
import tempfile
import types
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SOURCE_BYTES = Path(__file__).read_bytes()
MANIFEST_RELATIVE = Path("candle/flyspeck_manifest.json")
PILOT_RELATIVE = Path("candle/flyspeck_parser_diagnostic_pilot.json")
ALL_INVENTORY_RELATIVE = Path(
    "candle/flyspeck_parser_diagnostic_all_inventory.json"
)
NORMALIZATION_RELATIVE = Path("candle/flyspeck_normalizations.json")
ALL_INVENTORY_SOURCES_RELATIVE = Path(
    "candle/flyspeck_all_inventory_sources.py"
)
NORMALIZATION_CONTROLLER_RELATIVE = Path("candle/flyspeck_normalize.py")
LINKED_RECORD_RELATIVE = Path("candle/build/cakeml-build-provenance.json")
RUNTIME_RELATIVE = Path("candle/build/cake")
CONTROLLER_RELATIVE = Path("candle/flyspeck_parser_diagnostic.py")
RUNTIME_LOCK_RELATIVE = Path("candle/runtime_lock.py")
TRANSITION_CHECKER_RELATIVE = Path("candle/cakeml_bootstrap_transition.py")
PROVENANCE_RELATIVE = Path("candle/cakeml_artifact_provenance.py")
DIRECT_POLICY_RELATIVE = Path("candle/flyspeck_stratum_runtime.py")
AUTHORITY_SOURCE_RELATIVES = (
    PROVENANCE_RELATIVE,
    TRANSITION_CHECKER_RELATIVE,
    Path("candle/flyspeck_stratum_plan.py"),
    Path("candle/reference_protocol.py"),
    RUNTIME_LOCK_RELATIVE,
    DIRECT_POLICY_RELATIVE,
)
ALL_INVENTORY_AUTHORITY_SOURCE_RELATIVES = (
    *AUTHORITY_SOURCE_RELATIVES,
    NORMALIZATION_CONTROLLER_RELATIVE,
    ALL_INVENTORY_SOURCES_RELATIVE,
)
PLAN_NAME = "plan.json"
HOST_RECEIPT_NAME = "host-materialization.json"
RESULT_NAME = "receipt.json"
PILOT_COUNT = 20
ALL_INVENTORY_COUNT = 400
PILOT_PROFILE = "pilot"
ALL_INVENTORY_PROFILE = "all-inventory"
RUNTIME_PROFILES = (PILOT_PROFILE, ALL_INVENTORY_PROFILE)
CHUNK_BYTES = 1024 * 1024
PLAN_ROOT_MODE = 0o555
PLAN_FILE_MODE = 0o444
RESULT_ROOT_MODE = 0o555
RESULT_FILE_MODE = 0o444
PRIVATE_IO_MODE = 0o700
PRIVATE_IO_FILE_MODE = 0o600
AT_FDCWD = -100
RENAME_NOREPLACE = 1
HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")
CAPABILITY_ARGUMENT = "--candle-parser-diagnostic-capability-v1"
RUN_ARGUMENT = "--candle-parser-diagnostic-v1"
CAPABILITY_LINE = (
    b"CANDLE_CAMLPARSER_DIAGNOSTIC_CAPABILITY_V1\t"
    b"caml_parser$run\tstdin-exact-bytes\tparser-only\t"
    b"no-inference\tno-evaluation\n"
)
RESULT_PREFIX = b"CANDLE_CAMLPARSER_DIAGNOSTIC_V1\t"
ERROR_DIGEST_DOMAIN = b"CANDLE_CAMLPARSER_ERROR_V1\0"
PARSER_ERROR_EXIT = 65
PARSER_RUNTIME_PROTOCOL_SCHEMA = 2
DIAGNOSTIC_RECEIPT_SCHEMA = 4
ALL_INVENTORY_PLAN_SCHEMA = 2
ALL_INVENTORY_RECEIPT_SCHEMA = 5
EXECUTION_ENVIRONMENT = {"PATH": "/usr/bin:/bin", "LC_ALL": "C"}
GIT_ENVIRONMENT = {
    **EXECUTION_ENVIRONMENT,
    "GIT_CONFIG_NOSYSTEM": "1",
    "GIT_CONFIG_GLOBAL": "/dev/null",
    "GIT_TERMINAL_PROMPT": "0",
    "GIT_NO_REPLACE_OBJECTS": "1",
    "GIT_OPTIONAL_LOCKS": "0",
}
GIT_OPTIONS = (
    "-c", "core.fsmonitor=false",
    "-c", "core.untrackedCache=false",
    "-c", "core.preloadIndex=false",
)
MASKABLE_STANDALONE_STATUSES = {
    "resolved", "runtime-library", "generated-contract",
}


class ContractError(ValueError):
    """An authenticated input or protocol invariant did not match."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ContractError(message)


def _pairs_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        if key in value:
            raise ContractError(f"duplicate JSON key: {key}")
        value[key] = item
    return value


def load_object(path: Path, label: str = "JSON input") -> dict[str, Any]:
    try:
        data = path.read_bytes()
    except OSError as error:
        raise ContractError(f"cannot read {label}: {path}: {error}") from error
    return decode_object(data, f"{label}: {path}")


def decode_object(data: bytes, label: str = "JSON input") -> dict[str, Any]:
    try:
        value = json.loads(
            data.decode("utf-8"), object_pairs_hook=_pairs_object,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ContractError(f"cannot decode {label}: {error}") from error
    require(isinstance(value, dict), f"{label} is not an object")
    return value


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def bytes_record(data: bytes, relative: str | None = None) -> dict[str, Any]:
    record: dict[str, Any] = {
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest(),
    }
    if relative is not None:
        record["path"] = relative
    return record


def file_record(path: Path, relative: str | None = None) -> dict[str, Any]:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as source:
        while block := source.read(CHUNK_BYTES):
            size += len(block)
            digest.update(block)
    record: dict[str, Any] = {"bytes": size, "sha256": digest.hexdigest()}
    if relative is not None:
        record["path"] = relative
    return record


def validate_file(path: Path, expected: dict[str, Any], label: str) -> bytes:
    try:
        status = path.lstat()
    except OSError as error:
        raise ContractError(f"missing {label}: {path}: {error}") from error
    require(stat.S_ISREG(status.st_mode), f"{label} is not an ordinary file: {path}")
    data = path.read_bytes()
    require(len(data) == expected.get("bytes"), f"{label} byte-count mismatch")
    require(
        hashlib.sha256(data).hexdigest() == expected.get("sha256"),
        f"{label} SHA-256 mismatch",
    )
    if "md5" in expected:
        require(
            hashlib.md5(data, usedforsecurity=False).hexdigest() == expected["md5"],
            f"{label} MD5 mismatch",
        )
    return data


def validate_file_record(
    path: Path, expected: dict[str, Any], label: str,
    relative: str | None = None,
) -> dict[str, Any]:
    """Validate an ordinary file without materializing its bytes in memory."""
    try:
        observed_status = path.lstat()
    except OSError as error:
        raise ContractError(f"missing {label}: {path}: {error}") from error
    require(stat.S_ISREG(observed_status.st_mode),
            f"{label} is not an ordinary file: {path}")
    observed = file_record(path, relative)
    for field in ("bytes", "sha256", "md5"):
        if field in expected:
            if field == "md5" and field not in observed:
                digest = hashlib.md5(usedforsecurity=False)
                with path.open("rb") as source:
                    while block := source.read(CHUNK_BYTES):
                        digest.update(block)
                observed[field] = digest.hexdigest()
            require(observed.get(field) == expected[field],
                    f"{label} {field} mismatch")
    return observed


def resolve_without_symlinks(path: Path, label: str) -> Path:
    """Resolve an existing path only after rejecting symlink path components."""
    candidate = path if path.is_absolute() else Path.cwd() / path
    require(".." not in candidate.parts, f"{label} contains parent traversal")
    current = Path(candidate.anchor)
    for part in candidate.parts[1:]:
        if part in {"", "."}:
            continue
        current /= part
        try:
            observed = current.lstat()
        except OSError as error:
            raise ContractError(f"missing {label} path component: {current}: {error}") from error
        require(not stat.S_ISLNK(observed.st_mode),
                f"symlink component in {label}: {current}")
    return candidate.resolve(strict=True)


def safe_relative_path(relative: Any, label: str) -> Path:
    require(isinstance(relative, str) and relative, f"missing {label} path")
    path = Path(relative)
    require(not path.is_absolute() and ".." not in path.parts and path.as_posix() == relative,
            f"unsafe {label} path: {relative}")
    return path


def validate_fresh_output_root(path: Path, label: str) -> Path:
    """Reject final or ancestor symlinks without resolving the destination."""
    candidate = path if path.is_absolute() else Path.cwd() / path
    require(".." not in candidate.parts, f"{label} contains parent traversal")
    parent = resolve_without_symlinks(candidate.parent, f"{label} parent")
    destination = parent / candidate.name
    try:
        destination.lstat()
    except FileNotFoundError:
        pass
    except OSError as error:
        raise ContractError(f"cannot inspect {label}: {destination}: {error}") from error
    else:
        require(not stat.S_ISLNK(destination.lstat().st_mode),
                f"symlink alias in {label}: {destination}")
        raise ContractError(f"{label} already exists")
    return destination


def git_output(root: Path, *arguments: str, binary: bool = False) -> bytes | str:
    try:
        result = subprocess.run(
            ["/usr/bin/git", *GIT_OPTIONS, "-C", str(root), *arguments],
            check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=GIT_ENVIRONMENT,
        )
    except subprocess.CalledProcessError as error:
        detail = error.stderr.decode(errors="replace").strip()
        raise ContractError(f"Git check failed for {root}: {detail}") from error
    return result.stdout if binary else result.stdout.decode().strip()


def validate_no_git_rebinding(root: Path) -> None:
    common = Path(str(git_output(root, "rev-parse", "--git-common-dir")))
    if not common.is_absolute():
        common = (root / common).resolve()
    require(not (common / "info/grafts").exists(), "Git grafts are not allowed")
    replacements = str(git_output(root, "for-each-ref", "--format=%(refname)", "refs/replace"))
    require(not replacements, "Git replacement refs are not allowed")


def validate_git_blob(root: Path, head: str, relative: str, live: bytes) -> None:
    require(Path(relative).as_posix() == relative, f"non-canonical Git path: {relative}")
    require(not Path(relative).is_absolute() and ".." not in Path(relative).parts,
            f"unsafe Git path: {relative}")
    tree = bytes(git_output(root, "ls-tree", "-z", head, "--", relative, binary=True))
    records = [row for row in tree.split(b"\0") if row]
    require(len(records) == 1, f"missing or ambiguous Git blob: {relative}")
    prefix, observed_path = records[0].split(b"\t", 1)
    mode, kind, _object = prefix.split(b" ", 2)
    # The inherited HOL Light tree tracks a few ML sources executable.  Both
    # ordinary blob modes are content-authenticated by the bound commit; links,
    # submodules, and other tree entries remain inadmissible.
    require(mode in {b"100644", b"100755"} and kind == b"blob",
            f"non-ordinary Git blob: {relative}")
    require(observed_path.decode() == relative, f"Git path mismatch: {relative}")
    committed = bytes(git_output(root, "show", f"{head}:{relative}", binary=True))
    require(committed == live, f"live file differs from Git blob: {relative}")


def _dependency_child(dependency: dict[str, Any], nodes: dict[str, Any]) -> str | None:
    if dependency.get("status") != "resolved":
        return None
    selected = dependency.get("selected")
    return selected if isinstance(selected, str) and selected in nodes else None


def derive_manifest_node_inventory(
    manifest: dict[str, Any],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Derive first-discovery order and bind every unreachable inventory node."""
    nodes = manifest.get("source_nodes")
    roots = manifest.get("build_sequence_roots")
    bootstrap = manifest.get("bootstrap_roots")
    require(isinstance(nodes, dict), "missing manifest source nodes")
    require(isinstance(roots, list), "missing manifest build roots")
    require(isinstance(bootstrap, list), "missing manifest bootstrap roots")
    root_entries: list[tuple[str, dict[str, Any]]] = []
    for index, key in enumerate(bootstrap):
        root_entries.append((key, {"kind": "bootstrap-root", "root_index": index}))
    for action_index, root in enumerate(roots):
        require(root.get("index") == action_index, "manifest action index drift")
        root_entries.append((
            root.get("selected"),
            {
                "kind": "build-action-root",
                "action_index": action_index,
                "target": root.get("target"),
            },
        ))

    ordered: list[dict[str, Any]] = []
    seen: set[str] = set()

    def visit(key: Any, discovery: dict[str, Any]) -> None:
        require(isinstance(key, str) and key in nodes, f"unknown manifest source root: {key}")
        if key in seen:
            return
        seen.add(key)
        ordered.append({"source_key": key, "discovery": discovery})
        dependencies = nodes[key].get("dependencies")
        require(isinstance(dependencies, list), f"missing dependency list: {key}")
        for dependency_index, dependency in enumerate(dependencies):
            require(isinstance(dependency, dict), f"malformed dependency: {key}")
            child = _dependency_child(dependency, nodes)
            if child is not None:
                visit(child, {
                    "kind": "resolved-source-action",
                    "parent_source": key,
                    "dependency_index": dependency_index,
                    "line": dependency.get("line"),
                    "action_kind": dependency.get("kind"),
                })

    for key, discovery in root_entries:
        visit(key, discovery)
    excluded = []
    for missing in sorted(set(nodes) - seen):
        incoming = []
        for parent, parent_node in sorted(nodes.items()):
            for dependency_index, dependency in enumerate(parent_node["dependencies"]):
                selected_targets = dependency.get("selected_targets")
                if isinstance(selected_targets, list) and missing in selected_targets:
                    incoming.append({
                        "parent_source": parent,
                        "dependency_index": dependency_index,
                        "kind": dependency.get("kind"),
                        "line": dependency.get("line"),
                        "status": dependency.get("status"),
                        "syntax_position": dependency.get("syntax_position"),
                    })
        reason = (
            "referenced only through non-resolved dynamic/generated actions"
            if incoming else
            "not reachable from bootstrap/build roots through resolved selected dependencies"
        )
        excluded.append({
            "source_key": missing,
            "repository": nodes[missing]["repository"],
            "path": nodes[missing]["path"],
            "sha256": nodes[missing]["sha256"],
            "reason": reason,
            "incoming_nontraversed_actions": incoming,
        })
    require(len(ordered) + len(excluded) == len(nodes),
            "source discovery/exclusion partition mismatch")
    return ordered, excluded


def derive_manifest_node_order(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    """Compatibility projection of the authenticated first-discovery order."""
    return derive_manifest_node_inventory(manifest)[0]


def build_pilot_descriptor(manifest: dict[str, Any], manifest_data: bytes) -> dict[str, Any]:
    ordered, excluded = derive_manifest_node_inventory(manifest)
    require(len(ordered) >= PILOT_COUNT, "manifest graph is smaller than pilot")
    nodes = manifest["source_nodes"]
    selected = []
    for index, entry in enumerate(ordered[:PILOT_COUNT]):
        key = entry["source_key"]
        node = nodes[key]
        selected.append({
            "index": index,
            "source_key": key,
            "repository": node["repository"],
            "path": node["path"],
            "bytes": node["bytes"],
            "md5": node["md5"],
            "sha256": node["sha256"],
            "discovery": entry["discovery"],
        })
    keys = [entry["source_key"] for entry in selected]
    return {
        "schema": 1,
        "kind": "candle-flyspeck-parser-diagnostic-pilot",
        "claim": (
            "predeclared exact-manifest parser-only diagnostic selection; "
            "not inference, execution, theorem, S1, S2, S3, or release evidence"
        ),
        "selection": {
            "algorithm": (
                "first-discovery-preorder-v1: bootstrap_roots, then "
                "build_sequence_roots in action order; recurse through resolved "
                "selected dependencies in manifest list order"
            ),
            "pilot_source_count": PILOT_COUNT,
            "discovered_source_count": len(ordered),
            "excluded_source_count": len(excluded),
            "manifest_source_count": len(nodes),
            "ordered_source_key_sha256": canonical_sha256(keys),
            "coverage": (
                "bootstrap/core smoke pilot only; not representative Flyspeck corpus coverage"
            ),
        },
        "excluded_from_first_discovery": excluded,
        "manifest": bytes_record(manifest_data, MANIFEST_RELATIVE.as_posix()),
        "inputs": selected,
    }


def build_all_inventory_descriptor(
    manifest: dict[str, Any], manifest_data: bytes,
) -> dict[str, Any]:
    """Select every authenticated node without relabeling graph reachability."""
    ordered, excluded = derive_manifest_node_inventory(manifest)
    nodes = manifest["source_nodes"]
    require(
        len(nodes) == manifest.get("source_node_count") == ALL_INVENTORY_COUNT,
        "all-inventory parser selection requires exactly 400 manifest nodes",
    )
    discoveries = list(ordered)
    discoveries.extend({
        "source_key": entry["source_key"],
        "discovery": {
            "kind": "explicit-first-discovery-remainder",
            "exclusion": entry,
        },
    } for entry in excluded)
    require(
        len(discoveries) == len(nodes) and
        len({entry["source_key"] for entry in discoveries}) == len(nodes) and
        {entry["source_key"] for entry in discoveries} == set(nodes),
        "all-inventory parser selection is not an exact manifest partition",
    )
    inputs = []
    for index, entry in enumerate(discoveries):
        key = entry["source_key"]
        node = nodes[key]
        inputs.append({
            "index": index,
            "source_key": key,
            "repository": node["repository"],
            "path": node["path"],
            "bytes": node["bytes"],
            "md5": node["md5"],
            "sha256": node["sha256"],
            "discovery": entry["discovery"],
        })
    keys = [entry["source_key"] for entry in inputs]
    return {
        "schema": 1,
        "kind": "candle-flyspeck-parser-diagnostic-all-inventory",
        "claim": (
            "predeclared exact-manifest all-inventory parser-only selection; "
            "not a parser run, inference, execution, theorem, S1, S2, S3, or "
            "release evidence"
        ),
        "selection": {
            "algorithm": (
                "first-discovery-preorder-v1 followed by the lexicographically "
                "ordered explicit first-discovery remainder"
            ),
            "inventory_source_count": len(inputs),
            "discovered_source_count": len(ordered),
            "explicit_remainder_source_count": len(excluded),
            "manifest_source_count": len(nodes),
            "ordered_source_key_sha256": canonical_sha256(keys),
            "coverage": (
                "all authenticated manifest source nodes selected explicitly; "
                "parser-only and categorically non-promotable"
            ),
        },
        "excluded_from_first_discovery": excluded,
        "manifest": bytes_record(manifest_data, MANIFEST_RELATIVE.as_posix()),
        "inputs": inputs,
    }


def validate_pilot(
    pilot_data: bytes, manifest: dict[str, Any], manifest_data: bytes,
) -> dict[str, Any]:
    observed = decode_object(pilot_data, "captured parser pilot")
    expected = build_pilot_descriptor(manifest, manifest_data)
    require(observed == expected, "committed parser pilot is stale")
    return observed


def validate_all_inventory(
    descriptor_data: bytes, manifest: dict[str, Any], manifest_data: bytes,
) -> dict[str, Any]:
    observed = decode_object(
        descriptor_data, "captured all-inventory parser selection",
    )
    expected = build_all_inventory_descriptor(manifest, manifest_data)
    require(
        observed == expected,
        "committed all-inventory parser selection is stale",
    )
    return observed


def profile_authority_source_relatives(profile: str) -> tuple[Path, ...]:
    require(profile in RUNTIME_PROFILES, f"unsupported parser profile: {profile}")
    return (
        AUTHORITY_SOURCE_RELATIVES
        if profile == PILOT_PROFILE
        else ALL_INVENTORY_AUTHORITY_SOURCE_RELATIVES
    )


def plan_profile(plan: dict[str, Any]) -> str:
    """Recognize only the two closed, non-relabelable runtime plan shapes."""
    require(isinstance(plan, dict), "parser plan is not an object")
    if (
        plan.get("schema") == 1
        and plan.get("kind") == "candle-flyspeck-caml-parser-diagnostic-plan"
        and "pilot" in plan
        and "profile" not in plan
        and "source_preparation" not in plan
    ):
        return PILOT_PROFILE
    profile = plan.get("profile")
    descriptor = profile.get("descriptor") if isinstance(profile, dict) else None
    source_preparation = plan.get("source_preparation")
    descriptor_file = (
        descriptor.get("file") if isinstance(descriptor, dict) else None
    )
    require(
        plan.get("schema") == ALL_INVENTORY_PLAN_SCHEMA
        and plan.get("kind")
        == "candle-flyspeck-caml-parser-all-inventory-diagnostic-plan"
        and isinstance(profile, dict)
        and set(profile) == {
            "id", "descriptor", "input_count", "ready_count",
            "one_attempt_per_ready_input",
        }
        and profile.get("id") == ALL_INVENTORY_PROFILE
        and type(profile.get("input_count")) is int
        and profile["input_count"] == ALL_INVENTORY_COUNT
        and type(profile.get("ready_count")) is int
        and profile["ready_count"] == ALL_INVENTORY_COUNT
        and profile.get("one_attempt_per_ready_input") is True
        and isinstance(descriptor, dict)
        and set(descriptor) == {
            "path", "canonical_sha256", "file", "selection",
        }
        and descriptor.get("path") == ALL_INVENTORY_RELATIVE.as_posix()
        and isinstance(descriptor.get("canonical_sha256"), str)
        and HEX64.fullmatch(descriptor["canonical_sha256"]) is not None
        and isinstance(descriptor_file, dict)
        and set(descriptor_file) == {"path", "bytes", "sha256"}
        and descriptor_file.get("path") == ALL_INVENTORY_RELATIVE.as_posix()
        and type(descriptor_file.get("bytes")) is int
        and descriptor_file["bytes"] > 0
        and isinstance(descriptor_file.get("sha256"), str)
        and HEX64.fullmatch(descriptor_file["sha256"]) is not None
        and isinstance(descriptor.get("selection"), dict)
        and "pilot" not in plan
        and isinstance(source_preparation, dict)
        and set(source_preparation) == {
            "schema", "kind", "claim", "promotion_allowed", "parser_run",
            "runtime_execution", "canonical_sha256", "authorities",
            "input_count", "effective_kind_counts", "non_utf8_source_keys",
            "loader_actions", "prepared_inputs",
        }
        and source_preparation.get("schema") == 1
        and source_preparation.get("kind")
        == "candle-flyspeck-all-inventory-source-preparation"
        and source_preparation.get("promotion_allowed") is False
        and source_preparation.get("parser_run") is False
        and source_preparation.get("runtime_execution") is False
        and source_preparation.get("input_count") == ALL_INVENTORY_COUNT
        and type(source_preparation.get("input_count")) is int
        and isinstance(source_preparation.get("canonical_sha256"), str)
        and HEX64.fullmatch(source_preparation["canonical_sha256"]) is not None,
        "parser plan has an unknown or relabeled profile",
    )
    inputs = plan.get("inputs")
    prepared_summary = source_preparation.get("prepared_inputs")
    authorities = source_preparation.get("authorities")
    require(
        isinstance(inputs, list)
        and len(inputs) == ALL_INVENTORY_COUNT
        and plan.get("input_count") == ALL_INVENTORY_COUNT
        and type(plan.get("input_count")) is int
        and plan.get("ready_count") == ALL_INVENTORY_COUNT
        and type(plan.get("ready_count")) is int
        and plan.get("unsupported_count") == 0
        and type(plan.get("unsupported_count")) is int
        and all(
            isinstance(entry, dict)
            and type(entry.get("index")) is int
            and entry["index"] == index
            and isinstance(entry.get("source_key"), str)
            and entry.get("repository") in {"candle", "flyspeck"}
            and entry.get("status") == "ready"
            and isinstance(entry.get("prepared_input"), dict)
            and entry["prepared_input"].get("path") == f"inputs/{index:03d}.ml"
            and type(entry["prepared_input"].get("bytes")) is int
            and isinstance(entry["prepared_input"].get("sha256"), str)
            and HEX64.fullmatch(entry["prepared_input"]["sha256"]) is not None
            for index, entry in enumerate(inputs)
        )
        and len({entry["source_key"] for entry in inputs})
        == ALL_INVENTORY_COUNT
        and len({entry["prepared_input"]["path"] for entry in inputs})
        == ALL_INVENTORY_COUNT
        and len({entry["prepared_input"]["sha256"] for entry in inputs})
        == ALL_INVENTORY_COUNT
        and plan.get("ordered_input_sha256") == canonical_sha256(inputs)
        and descriptor["selection"].get("ordered_source_key_sha256")
        == canonical_sha256([entry["source_key"] for entry in inputs])
        and isinstance(prepared_summary, dict)
        and prepared_summary.get("count") == ALL_INVENTORY_COUNT
        and prepared_summary.get("paths_unique") is True
        and prepared_summary.get("sha256_unique") is True
        and prepared_summary.get("ordered_path_sha256")
        == canonical_sha256([
            entry["prepared_input"]["path"] for entry in inputs
        ])
        and prepared_summary.get("ordered_prepared_sha256")
        == canonical_sha256([
            entry["prepared_input"]["sha256"] for entry in inputs
        ])
        and isinstance(authorities, dict)
        and authorities.get("descriptor") == descriptor_file
        and authorities.get("manifest") == plan.get("manifest")
        and isinstance(authorities.get("normalization_contract"), dict)
        and authorities["normalization_contract"].get("path")
        == NORMALIZATION_RELATIVE.as_posix(),
        "all-inventory plan input/profile closure mismatch",
    )
    return ALL_INVENTORY_PROFILE


def profile_input_count(plan: dict[str, Any]) -> int:
    return (
        PILOT_COUNT
        if plan_profile(plan) == PILOT_PROFILE
        else ALL_INVENTORY_COUNT
    )


def classify_dependency(dependency: dict[str, Any]) -> dict[str, Any]:
    position = dependency.get("syntax_position")
    status = dependency.get("status")
    if position == "standalone-phrase" and status in MASKABLE_STANDALONE_STATUSES:
        handling = "masked-exact-manifest-line-before-parser"
        supported = True
    elif position == "embedded-expression":
        handling = "retained-as-parser-input-but-never-executed-by-gate"
        supported = True
    else:
        handling = "unsupported-no-parser-launch-for-source"
        supported = False
    return {
        "kind": dependency.get("kind"),
        "line": dependency.get("line"),
        "status": status,
        "syntax_position": position,
        "handling": handling,
        "parser_preparation_supported": supported,
        "action_semantics_executed": False,
    }


def _mask_line(line: bytes, dependency: dict[str, Any], source_key: str) -> bytes:
    kind = dependency.get("kind")
    require(isinstance(kind, str) and kind, f"missing action kind: {source_key}")
    content = line
    ending = b""
    if content.endswith(b"\r\n"):
        content, ending = content[:-2], b"\r\n"
    elif content.endswith(b"\n"):
        content, ending = content[:-1], b"\n"
    stripped = content.lstrip(b" \t")
    token = kind.encode()
    require(
        stripped.startswith(token) and
        len(stripped) > len(token) and stripped[len(token):len(token) + 1] in b" \t",
        f"manifest action token mismatch at {source_key}:{dependency.get('line')}",
    )
    require(b";;" in stripped, f"unterminated manifest action at {source_key}")
    literal = dependency.get("literal")
    if isinstance(literal, str):
        require(
            json.dumps(literal, ensure_ascii=False).encode() in stripped,
            f"manifest action literal mismatch at {source_key}:{dependency.get('line')}",
        )
    return b" " * len(content) + ending


def prepare_source(
    source_key: str, source_data: bytes, dependencies: list[dict[str, Any]],
) -> tuple[bytes | None, list[dict[str, Any]], list[str]]:
    lines = source_data.splitlines(keepends=True)
    actions: list[dict[str, Any]] = []
    unsupported: list[str] = []
    masked_lines: set[int] = set()
    for index, dependency in enumerate(dependencies):
        classified = classify_dependency(dependency)
        record = {
            "dependency_index": index,
            **classified,
            "manifest_record_sha256": canonical_sha256(dependency),
        }
        actions.append(record)
        if not classified["parser_preparation_supported"]:
            unsupported.append(
                f"dependency {index}: {dependency.get('kind')}/"
                f"{dependency.get('status')}/{dependency.get('syntax_position')}"
            )
            continue
        if classified["handling"] == "masked-exact-manifest-line-before-parser":
            line_number = dependency.get("line")
            require(isinstance(line_number, int) and 1 <= line_number <= len(lines),
                    f"manifest action line out of range: {source_key}")
            require(line_number not in masked_lines,
                    f"multiple manifest actions on one masked line: {source_key}:{line_number}")
            original = lines[line_number - 1]
            record["original_line"] = bytes_record(original)
            lines[line_number - 1] = _mask_line(original, dependency, source_key)
            record["masked_line"] = bytes_record(lines[line_number - 1])
            masked_lines.add(line_number)
    if unsupported:
        return None, actions, unsupported
    prepared = b"".join(lines)
    require(len(prepared) == len(source_data), f"prepared size drift: {source_key}")
    return prepared, actions, unsupported


def _source_path(candle_root: Path, flyspeck_root: Path, node: dict[str, Any]) -> Path:
    repository = node.get("repository")
    require(repository in {"candle", "flyspeck"}, "unknown source repository")
    root = candle_root if repository == "candle" else flyspeck_root
    relative = Path(node["path"])
    require(not relative.is_absolute() and ".." not in relative.parts, "unsafe source path")
    return root / relative


def build_plan(
    candle_root: Path,
    flyspeck_root: Path,
    candle_head: str,
    manifest: dict[str, Any],
    manifest_data: bytes,
    pilot: dict[str, Any],
    pilot_data: bytes,
) -> tuple[dict[str, Any], dict[str, bytes]]:
    require(HEX40.fullmatch(candle_head) is not None, "invalid Candle head")
    nodes = manifest["source_nodes"]
    inputs: list[dict[str, Any]] = []
    files: dict[str, bytes] = {}
    for pilot_input in pilot["inputs"]:
        index = pilot_input["index"]
        source_key = pilot_input["source_key"]
        node = nodes.get(source_key)
        require(isinstance(node, dict), f"pilot source disappeared: {source_key}")
        for field in ("repository", "path", "bytes", "md5", "sha256"):
            require(node.get(field) == pilot_input.get(field),
                    f"pilot source identity drift: {source_key}:{field}")
        source_path = _source_path(candle_root, flyspeck_root, node)
        source_data = validate_file(source_path, node, f"pilot source {source_key}")
        prepared, actions, unsupported = prepare_source(
            source_key, source_data, node["dependencies"],
        )
        relative = f"inputs/{index:03d}.ml"
        record: dict[str, Any] = {
            "index": index,
            "source_key": source_key,
            "repository": node["repository"],
            "source": {
                "path": node["path"], "bytes": node["bytes"],
                "md5": node["md5"], "sha256": node["sha256"],
            },
            "discovery": pilot_input["discovery"],
            "manifest_actions": actions,
            "manifest_action_semantics": (
                "recorded and parser boundaries modeled; never executed by this gate"
            ),
            "generated_inputs_consumed": False,
            "normalization": "unsupported-in-pilot" if "execution_normalization" in node else "none",
            "unsupported_reasons": unsupported,
        }
        if "execution_normalization" in node:
            record["unsupported_reasons"].append(
                "execution normalization requires a separately authenticated overlay-aware parser plan"
            )
            prepared = None
        if prepared is None:
            record["status"] = "unsupported-no-launch"
            record["prepared_input"] = None
        else:
            files[relative] = prepared
            record["status"] = "ready"
            record["prepared_input"] = bytes_record(prepared, relative)
        inputs.append(record)

    generated = []
    for entry in manifest.get("generated_inputs", []):
        generated.append({
            **{field: entry[field] for field in ("class", "path", "bytes", "sha256")},
            "handling": "not-consumed-by-parser-only-diagnostic",
            "semantics_checked": False,
        })
    build_roots = manifest.get("build_sequence_roots")
    action_projection = [
        {
            "index": entry["index"], "target": entry["target"],
            "selected": entry["selected"], "status": entry["status"],
        }
        for entry in build_roots
    ]
    authority_sources = {
        relative.as_posix(): bytes_record(
            (candle_root / relative).read_bytes(), relative.as_posix(),
        )
        for relative in AUTHORITY_SOURCE_RELATIVES
    }
    plan = {
        "schema": 1,
        "kind": "candle-flyspeck-caml-parser-diagnostic-plan",
        "claim": (
            "diagnostic parser acceptance only; never inference, execution, theorem, "
            "S1, S2, S3, checkpoint, fingerprint, equivalence, or release evidence"
        ),
        "promotion": {
            "eligible": False,
            "s1_evidence": False,
            "s2_evidence": False,
            "s3_evidence": False,
            "reason": "parser-only result omits action semantics, inference, evaluation, and theorem identity",
        },
        "repositories": {
            "candle_commit": candle_head,
            "flyspeck_commit": manifest["repositories"]["flyspeck"]["commit"],
            "cakeml_commit": manifest["dopen_corpus_contract"]["verified_cakeml_integration"]["commit"],
            "hol4_commit": manifest["dopen_corpus_contract"]["verified_cakeml_integration"]["proof_hol4_commit"],
        },
        "controller": bytes_record(
            SOURCE_BYTES, "candle/flyspeck_parser_diagnostic.py",
        ),
        "authority_sources": authority_sources,
        "manifest": bytes_record(manifest_data, MANIFEST_RELATIVE.as_posix()),
        "pilot": {
            "path": PILOT_RELATIVE.as_posix(),
            "canonical_sha256": canonical_sha256(pilot),
            "file": bytes_record(
                pilot_data, PILOT_RELATIVE.as_posix(),
            ),
            "selection": pilot["selection"],
        },
        "parser_runtime_protocol": {
            "schema": PARSER_RUNTIME_PROTOCOL_SCHEMA,
            "function": "caml_parser$run",
            "language": "CakeML Candle OCaml parser",
            "capability_argument": CAPABILITY_ARGUMENT,
            "capability_stdout_sha256": hashlib.sha256(CAPABILITY_LINE).hexdigest(),
            "run_argument": RUN_ARGUMENT,
            "input": "one exact prepared source on stdin per fresh process",
            "parse_error_exit_code": PARSER_ERROR_EXIT,
            "parse_error_stdout": (
                "CANDLE_CAMLPARSER_DIAGNOSTIC_V1<TAB>NONCE"
                "<TAB>PARSE_ERROR<LF>"
            ),
            "controller_stderr_digest": {
                "algorithm": "sha256",
                "domain_hex": ERROR_DIGEST_DOMAIN.hex(),
                "canonical_preimage": (
                    "ASCII bytes CANDLE_CAMLPARSER_ERROR_V1, one NUL byte, "
                    "then the exact stderr byte stream without decoding or newline changes"
                ),
                "stderr_encoding": (
                    "runtime emits the caml_parser$run error/location text as UTF-8; "
                    "the controller hashes the resulting bytes without reinterpretation"
                ),
            },
            "forbidden_substitutes": [
                "--print_sexp/parse_prog", "--candle REPL", "host OCaml parser",
            ],
            "required_properties": [
                "parser-only", "no-inference", "no-evaluation", "no-source-actions",
            ],
        },
        "manifest_action_order": {
            "bootstrap_roots": manifest["bootstrap_roots"],
            "build_action_count": len(action_projection),
            "ordered_build_action_sha256": canonical_sha256(action_projection),
            "pilot_selection_preserves_first_discovery_order": True,
        },
        "generated_inputs": {
            "entry_count": len(generated),
            "ordered_binding_sha256": canonical_sha256(generated),
            "bindings": generated,
            "semantics_checked": False,
        },
        "input_count": len(inputs),
        "ready_count": sum(entry["status"] == "ready" for entry in inputs),
        "unsupported_count": sum(entry["status"] != "ready" for entry in inputs),
        "ordered_input_sha256": canonical_sha256(inputs),
        "inputs": inputs,
        "limitations": [
            "standalone manifest source actions are masked but never executed",
            "embedded loading expressions are parsed but never evaluated",
            "generated inputs are identity-bound from the manifest but never consumed",
            "the pilot does not model an incremental type or value environment",
            "a parser pass cannot establish source execution or theorem equivalence",
        ],
    }
    return plan, files


def _prepare_all_inventory_sources(
    candle_root: Path,
    flyspeck_root: Path,
    normalization_source: bytes,
    preparation_source: bytes,
    descriptor_data: bytes,
    manifest_data: bytes,
    normalization_data: bytes,
) -> tuple[dict[str, Any], dict[str, bytes]]:
    """Execute the exact authenticated source-only foundation in-process."""
    normalization_path = candle_root / NORMALIZATION_CONTROLLER_RELATIVE
    preparation_path = candle_root / ALL_INVENTORY_SOURCES_RELATIVE
    missing = object()
    previous_normalization = sys.modules.get("flyspeck_normalize", missing)
    normalization = _load_exact_source_module(
        "_candle_parser_flyspeck_normalize",
        normalization_path, normalization_source,
    )
    sys.modules["flyspeck_normalize"] = normalization
    try:
        preparation = _load_exact_source_module(
            "_candle_parser_all_inventory_sources",
            preparation_path, preparation_source,
        )
        require(
            preparation.flyspeck_normalize is normalization,
            "all-inventory preparation normalization module was rebound",
        )
        try:
            return preparation.prepare_all_sources(
                candle_root,
                flyspeck_root,
                descriptor_data=descriptor_data,
                manifest_data=manifest_data,
                normalization_data=normalization_data,
            )
        except preparation.ContractError as error:
            raise ContractError(
                f"all-inventory source preparation rejected: {error}"
            ) from error
    finally:
        if previous_normalization is missing:
            sys.modules.pop("flyspeck_normalize", None)
        else:
            sys.modules["flyspeck_normalize"] = previous_normalization


def build_all_inventory_plan(
    candle_root: Path,
    flyspeck_root: Path,
    candle_head: str,
    manifest: dict[str, Any],
    manifest_data: bytes,
    descriptor: dict[str, Any],
    descriptor_data: bytes,
    normalization_data: bytes,
    normalization_source: bytes,
    preparation_source: bytes,
) -> tuple[dict[str, Any], dict[str, bytes]]:
    """Build the distinct schema-2 runtime plan over all 400 ready inputs."""
    require(HEX40.fullmatch(candle_head) is not None, "invalid Candle head")
    require(
        decode_object(manifest_data, "captured all-inventory manifest") == manifest
        and validate_all_inventory(
            descriptor_data, manifest, manifest_data,
        ) == descriptor,
        "all-inventory descriptor object/byte authority drift",
    )
    require(
        normalization_source
        == _read_stable_source(candle_root / NORMALIZATION_CONTROLLER_RELATIVE)
        and preparation_source
        == _read_stable_source(candle_root / ALL_INVENTORY_SOURCES_RELATIVE),
        "all-inventory source-preparation controller bytes changed",
    )
    source_plan, files = _prepare_all_inventory_sources(
        candle_root, flyspeck_root, normalization_source, preparation_source,
        descriptor_data, manifest_data, normalization_data,
    )
    source_inputs = source_plan.get("inputs")
    require(
        source_plan.get("schema") == 1
        and source_plan.get("kind")
        == "candle-flyspeck-all-inventory-source-preparation"
        and source_plan.get("promotion_allowed") is False
        and source_plan.get("parser_run") is False
        and source_plan.get("runtime_execution") is False
        and isinstance(source_inputs, list)
        and len(source_inputs) == ALL_INVENTORY_COUNT
        and len(files) == ALL_INVENTORY_COUNT,
        "all-inventory source-preparation plan shape drift",
    )
    inputs: list[dict[str, Any]] = []
    for index, (source, selected) in enumerate(zip(
        source_inputs, descriptor["inputs"], strict=True,
    )):
        require(
            isinstance(source, dict)
            and source.get("index") == index
            and source.get("source_key") == selected.get("source_key")
            and source.get("repository") == selected.get("repository")
            and source.get("source", {}).get("path") == selected.get("path")
            and source.get("prepared_input", {}).get("path")
            == f"inputs/{index:03d}.ml"
            and source.get("parser_or_runtime_invoked") is False,
            f"all-inventory prepared source/descriptor drift: {index}",
        )
        prepared = source["prepared_input"]
        require(
            files.get(prepared["path"]) is not None
            and bytes_record(files[prepared["path"]], prepared["path"])
            == prepared,
            f"all-inventory prepared file identity drift: {index}",
        )
        inputs.append({**source, "status": "ready"})

    generated = [
        {
            **{
                field: entry[field]
                for field in ("class", "path", "bytes", "sha256")
            },
            "handling": "not-consumed-by-parser-only-diagnostic",
            "semantics_checked": False,
        }
        for entry in manifest.get("generated_inputs", [])
    ]
    action_projection = [
        {
            "index": entry["index"], "target": entry["target"],
            "selected": entry["selected"], "status": entry["status"],
        }
        for entry in manifest.get("build_sequence_roots", [])
    ]
    authority_sources = {
        relative.as_posix(): bytes_record(
            _read_stable_source(candle_root / relative), relative.as_posix(),
        )
        for relative in ALL_INVENTORY_AUTHORITY_SOURCE_RELATIVES
    }
    descriptor_record = {
        "path": ALL_INVENTORY_RELATIVE.as_posix(),
        "canonical_sha256": canonical_sha256(descriptor),
        "file": bytes_record(
            descriptor_data, ALL_INVENTORY_RELATIVE.as_posix(),
        ),
        "selection": descriptor["selection"],
    }
    source_preparation = {
        "schema": source_plan["schema"],
        "kind": source_plan["kind"],
        "claim": source_plan["claim"],
        "promotion_allowed": source_plan["promotion_allowed"],
        "parser_run": source_plan["parser_run"],
        "runtime_execution": source_plan["runtime_execution"],
        "canonical_sha256": canonical_sha256(source_plan),
        "authorities": source_plan["authorities"],
        "input_count": source_plan["input_count"],
        "effective_kind_counts": source_plan["effective_kind_counts"],
        "non_utf8_source_keys": source_plan["non_utf8_source_keys"],
        "loader_actions": source_plan["loader_actions"],
        "prepared_inputs": source_plan["prepared_inputs"],
    }
    profile = {
        "id": ALL_INVENTORY_PROFILE,
        "descriptor": descriptor_record,
        "input_count": ALL_INVENTORY_COUNT,
        "ready_count": ALL_INVENTORY_COUNT,
        "one_attempt_per_ready_input": True,
    }
    plan = {
        "schema": ALL_INVENTORY_PLAN_SCHEMA,
        "kind": "candle-flyspeck-caml-parser-all-inventory-diagnostic-plan",
        "profile": profile,
        "claim": (
            "all-inventory parser-only diagnostic acceptance; never inference, "
            "execution, theorem, S1, S2, S3, checkpoint, fingerprint, "
            "equivalence, or release evidence"
        ),
        "promotion": {
            "eligible": False,
            "s1_evidence": False,
            "s2_evidence": False,
            "s3_evidence": False,
            "reason": (
                "parser-only result omits action semantics, inference, "
                "evaluation, and theorem identity"
            ),
        },
        "repositories": {
            "candle_commit": candle_head,
            "flyspeck_commit": manifest["repositories"]["flyspeck"]["commit"],
            "cakeml_commit": manifest["dopen_corpus_contract"]
            ["verified_cakeml_integration"]["commit"],
            "hol4_commit": manifest["dopen_corpus_contract"]
            ["verified_cakeml_integration"]["proof_hol4_commit"],
        },
        "controller": bytes_record(
            SOURCE_BYTES, CONTROLLER_RELATIVE.as_posix(),
        ),
        "authority_sources": authority_sources,
        "manifest": bytes_record(manifest_data, MANIFEST_RELATIVE.as_posix()),
        "source_preparation": source_preparation,
        "parser_runtime_protocol": {
            "schema": PARSER_RUNTIME_PROTOCOL_SCHEMA,
            "function": "caml_parser$run",
            "language": "CakeML Candle OCaml parser",
            "capability_argument": CAPABILITY_ARGUMENT,
            "capability_stdout_sha256": hashlib.sha256(CAPABILITY_LINE).hexdigest(),
            "run_argument": RUN_ARGUMENT,
            "input": "one exact prepared source on stdin per fresh process",
            "parse_error_exit_code": PARSER_ERROR_EXIT,
            "parse_error_stdout": (
                "CANDLE_CAMLPARSER_DIAGNOSTIC_V1<TAB>NONCE"
                "<TAB>PARSE_ERROR<LF>"
            ),
            "controller_stderr_digest": {
                "algorithm": "sha256",
                "domain_hex": ERROR_DIGEST_DOMAIN.hex(),
                "canonical_preimage": (
                    "ASCII bytes CANDLE_CAMLPARSER_ERROR_V1, one NUL byte, "
                    "then the exact stderr byte stream without decoding or "
                    "newline changes"
                ),
                "stderr_encoding": (
                    "runtime emits the caml_parser$run error/location text as "
                    "UTF-8; the controller hashes the resulting bytes without "
                    "reinterpretation"
                ),
            },
            "forbidden_substitutes": [
                "--print_sexp/parse_prog", "--candle REPL", "host OCaml parser",
            ],
            "required_properties": [
                "parser-only", "no-inference", "no-evaluation", "no-source-actions",
            ],
        },
        "manifest_action_order": {
            "bootstrap_roots": manifest["bootstrap_roots"],
            "build_action_count": len(action_projection),
            "ordered_build_action_sha256": canonical_sha256(action_projection),
            "all_inventory_selection_preserves_descriptor_order": True,
        },
        "generated_inputs": {
            "entry_count": len(generated),
            "ordered_binding_sha256": canonical_sha256(generated),
            "bindings": generated,
            "semantics_checked": False,
        },
        "input_count": len(inputs),
        "ready_count": len(inputs),
        "unsupported_count": 0,
        "ordered_input_sha256": canonical_sha256(inputs),
        "inputs": inputs,
        "limitations": [
            "all recognized standalone source actions are masked but never executed",
            "embedded loading expressions are parsed but never evaluated",
            "generated inputs are identity-bound from the manifest but never consumed",
            "normalizations are exact hash-bound lexical repairs, not source semantics",
            "the all-inventory profile does not model an incremental type or value environment",
            "a parser pass cannot establish source execution or theorem equivalence",
        ],
    }
    require(plan_profile(plan) == ALL_INVENTORY_PROFILE,
            "constructed all-inventory profile is not closed")
    return plan, files


def _rename_noreplace(source: Path, destination: Path) -> None:
    libc = ctypes.CDLL(None, use_errno=True)
    try:
        renameat2 = libc.renameat2
    except AttributeError as error:
        raise OSError(errno.ENOSYS, "renameat2 is required") from error
    renameat2.argtypes = [
        ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p,
        ctypes.c_uint,
    ]
    renameat2.restype = ctypes.c_int
    if renameat2(
        AT_FDCWD, os.fsencode(source), AT_FDCWD, os.fsencode(destination),
        RENAME_NOREPLACE,
    ) != 0:
        number = ctypes.get_errno()
        if number == errno.EEXIST:
            raise FileExistsError(number, os.strerror(number), destination)
        raise OSError(number, os.strerror(number), destination)


def _write_tree(root: Path, files: dict[str, bytes], root_mode: int, file_mode: int) -> None:
    for relative, data in files.items():
        target = root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        target.chmod(file_mode)
    for directory, names, _file_names in os.walk(root, topdown=False):
        for name in names:
            (Path(directory) / name).chmod(root_mode)
    root.chmod(root_mode)


def build_host_receipt(
    candle_root: Path,
    flyspeck_root: Path,
    plan_data: bytes,
    controller_execution: dict[str, Any],
) -> dict[str, Any]:
    plan_sha256 = hashlib.sha256(plan_data).hexdigest()
    return {
        "schema": 1,
        "kind": "candle-flyspeck-parser-diagnostic-host-materialization",
        "claim": "host paths and immutable publication only; not parser or release evidence",
        "plan": bytes_record(plan_data, PLAN_NAME),
        "plan_sha256": plan_sha256,
        "controller_source_sha256": hashlib.sha256(SOURCE_BYTES).hexdigest(),
        "controller_execution": controller_execution,
        "host_roots": {"candle": str(candle_root), "flyspeck": str(flyspeck_root)},
        "publication": {
            "policy": "fresh-root-renameat2-noreplace",
            "root_mode": "0555", "file_mode": "0444",
        },
    }


def capture_committed_json(
    root: Path, head: str, relative_path: Path, label: str,
) -> tuple[bytes, dict[str, Any]]:
    """Authenticate, decode, and retain one exact JSON byte capture."""
    relative = relative_path.as_posix()
    path = root / relative_path
    data = _read_stable_source(path)
    validate_git_blob(root, head, relative, data)
    require(_read_stable_source(path) == data,
            f"{label} changed after Git validation")
    return data, decode_object(data, f"captured {label}")


def reconstruct_plan_authority(
    candle_root: Path,
    candle_head: str,
    flyspeck_root: Path,
    flyspeck_head: str,
    profile: str,
) -> tuple[dict[str, Any], dict[str, bytes], dict[str, Any], bytes]:
    """Rebuild the only accepted plan from explicit Git-root authorities."""
    profile_authorities = profile_authority_source_relatives(profile)
    require(HEX40.fullmatch(candle_head) is not None,
            "expected Candle head must be lowercase 40-hex")
    require(HEX40.fullmatch(flyspeck_head) is not None,
            "expected Flyspeck head must be lowercase 40-hex")
    candle_root = resolve_without_symlinks(candle_root, "Candle root")
    flyspeck_root = resolve_without_symlinks(flyspeck_root, "Flyspeck root")
    validate_no_git_rebinding(candle_root)
    validate_no_git_rebinding(flyspeck_root)
    require(str(git_output(candle_root, "rev-parse", "HEAD")) == candle_head,
            "Candle revision differs from explicit authority")
    require(str(git_output(flyspeck_root, "rev-parse", "HEAD")) == flyspeck_head,
            "Flyspeck revision differs from explicit authority")

    controller_relative = CONTROLLER_RELATIVE.as_posix()
    controller_path = candle_root / controller_relative
    controller_data = controller_path.read_bytes()
    validate_git_blob(candle_root, candle_head, controller_relative, controller_data)
    require(controller_data == SOURCE_BYTES,
            "executing controller differs from authenticated Candle controller blob")
    authority_source_data: dict[str, bytes] = {}
    for relative_path in profile_authorities:
        relative = relative_path.as_posix()
        source_data = _read_stable_source(candle_root / relative_path)
        validate_git_blob(candle_root, candle_head, relative, source_data)
        authority_source_data[relative] = source_data

    manifest_data, manifest = capture_committed_json(
        candle_root, candle_head, MANIFEST_RELATIVE, "Flyspeck manifest",
    )
    require(manifest.get("schema") == 1, "unsupported Flyspeck manifest schema")
    require(manifest["repositories"]["flyspeck"]["commit"] == flyspeck_head,
            "explicit Flyspeck authority differs from manifest pin")

    if profile == PILOT_PROFILE:
        descriptor_relative = PILOT_RELATIVE
        descriptor_label = "parser pilot"
    else:
        descriptor_relative = ALL_INVENTORY_RELATIVE
        descriptor_label = "all-inventory parser selection"
    descriptor_data, _descriptor_object = capture_committed_json(
        candle_root, candle_head, descriptor_relative, descriptor_label,
    )
    descriptor = (
        validate_pilot(descriptor_data, manifest, manifest_data)
        if profile == PILOT_PROFILE
        else validate_all_inventory(descriptor_data, manifest, manifest_data)
    )
    for selected in descriptor["inputs"]:
        node = manifest["source_nodes"][selected["source_key"]]
        root = candle_root if node["repository"] == "candle" else flyspeck_root
        head = candle_head if node["repository"] == "candle" else flyspeck_head
        source_path = root / safe_relative_path(node["path"], "selected source")
        live = validate_file(
            source_path, node, f"selected source {selected['source_key']}",
        )
        validate_git_blob(root, head, node["path"], live)
    if profile == PILOT_PROFILE:
        plan, input_files = build_plan(
            candle_root, flyspeck_root, candle_head, manifest, manifest_data,
            descriptor, descriptor_data,
        )
    else:
        normalization_data, _normalization = capture_committed_json(
            candle_root, candle_head, NORMALIZATION_RELATIVE,
            "Flyspeck normalization contract",
        )
        plan, input_files = build_all_inventory_plan(
            candle_root, flyspeck_root, candle_head, manifest, manifest_data,
            descriptor, descriptor_data, normalization_data,
            authority_source_data[NORMALIZATION_CONTROLLER_RELATIVE.as_posix()],
            authority_source_data[ALL_INVENTORY_SOURCES_RELATIVE.as_posix()],
        )
    plan_data = json_bytes(plan)
    policy = _load_direct_runtime_policy(candle_root, candle_head, plan)
    controller_execution = collect_controller_execution(candle_root, policy)
    host = build_host_receipt(
        candle_root, flyspeck_root, plan_data, controller_execution,
    )
    return plan, input_files, host, plan_data


def materialize(
    candle_root: Path, flyspeck_root: Path, output_root: Path, profile: str,
) -> dict[str, Any]:
    profile_authority_source_relatives(profile)
    candle_root = resolve_without_symlinks(candle_root, "Candle root")
    flyspeck_root = resolve_without_symlinks(flyspeck_root, "Flyspeck root")
    output_root = validate_fresh_output_root(output_root, "plan output root")
    for label, authority_root in (
        ("Candle", candle_root), ("Flyspeck", flyspeck_root),
    ):
        require(output_root != authority_root and
                not output_root.is_relative_to(authority_root),
                f"plan output root must be outside {label} root")
    candle_head = str(git_output(candle_root, "rev-parse", "HEAD"))
    flyspeck_head = str(git_output(flyspeck_root, "rev-parse", "HEAD"))
    plan, input_files, host, plan_data = reconstruct_plan_authority(
        candle_root, candle_head, flyspeck_root, flyspeck_head, profile,
    )
    parent = output_root.parent
    staging = Path(tempfile.mkdtemp(prefix=f".{output_root.name}.pending-", dir=parent))
    try:
        files = {
            PLAN_NAME: plan_data,
            HOST_RECEIPT_NAME: json_bytes(host),
            **input_files,
        }
        _write_tree(staging, files, PLAN_ROOT_MODE, PLAN_FILE_MODE)
        _rename_noreplace(staging, output_root)
    except BaseException:
        # Retain staging on failure for inspection; never replace a destination.
        raise
    return host


def validate_plan_root(
    plan_root: Path,
    expected_plan: dict[str, Any],
    expected_inputs: dict[str, bytes],
    expected_host: dict[str, Any],
) -> tuple[dict[str, Any], bytes]:
    """Compare the published tree to an independently reconstructed authority."""
    plan_root = resolve_without_symlinks(plan_root, "plan root")
    require(stat.S_IMODE(plan_root.stat().st_mode) == PLAN_ROOT_MODE,
            "plan root mode mismatch")
    plan_path = plan_root / PLAN_NAME
    host_path = plan_root / HOST_RECEIPT_NAME
    expected_plan_data = json_bytes(expected_plan)
    expected_host_data = json_bytes(expected_host)
    expected_files = {
        PLAN_NAME: expected_plan_data,
        HOST_RECEIPT_NAME: expected_host_data,
        **expected_inputs,
    }
    expected_paths = {Path(relative) for relative in expected_files}
    expected_directories = {Path(".")}
    for relative in expected_paths:
        require(not relative.is_absolute() and ".." not in relative.parts,
                f"unsafe reconstructed plan path: {relative}")
        expected_directories.update(
            parent for parent in relative.parents if parent != Path(".")
        )
    observed_paths: set[Path] = set()
    observed_directories = {Path(".")}
    for current, directory_names, file_names in os.walk(
        plan_root, topdown=True, followlinks=False,
    ):
        current_path = Path(current)
        for name in directory_names:
            path = current_path / name
            observed = path.lstat()
            require(stat.S_ISDIR(observed.st_mode),
                    f"non-directory or symlink in plan tree: {path}")
            require(stat.S_IMODE(observed.st_mode) == PLAN_ROOT_MODE,
                    f"plan directory mode mismatch: {path}")
            observed_directories.add(path.relative_to(plan_root))
        for name in file_names:
            path = current_path / name
            observed = path.lstat()
            require(stat.S_ISREG(observed.st_mode),
                    f"non-ordinary file in plan tree: {path}")
            require(stat.S_IMODE(observed.st_mode) == PLAN_FILE_MODE,
                    f"plan file mode mismatch: {path}")
            relative = path.relative_to(plan_root)
            require(relative in expected_paths,
                    f"unexpected file in parser plan: {relative}")
            observed_paths.add(relative)
            require(path.read_bytes() == expected_files[relative.as_posix()],
                    f"parser plan file differs from reconstructed authority: {relative}")
    require(observed_directories == expected_directories,
            "parser plan directory set differs from reconstructed authority")
    require(observed_paths == expected_paths,
            "parser plan file set differs from reconstructed authority")
    plan_data = plan_path.read_bytes()
    plan = load_object(plan_path, "parser diagnostic plan")
    host = load_object(host_path, "parser diagnostic host receipt")
    require(plan == expected_plan and plan_data == expected_plan_data,
            "parser plan differs from reconstructed authority")
    require(host == expected_host and host_path.read_bytes() == expected_host_data,
            "host receipt differs from reconstructed authority")
    count = profile_input_count(plan)
    inputs = plan.get("inputs")
    require(isinstance(inputs, list) and
            len(inputs) == plan.get("input_count") == count,
            "parser plan input count mismatch")
    for index, entry in enumerate(inputs):
        require(entry.get("index") == index, "parser plan input order mismatch")
        prepared = entry.get("prepared_input")
        if entry.get("status") == "ready":
            require(isinstance(prepared, dict), "ready parser input is missing")
            relative = safe_relative_path(prepared.get("path"), "prepared input")
            require(relative.as_posix() in expected_inputs,
                    "prepared input is absent from reconstruction")
        else:
            require(prepared is None and entry.get("unsupported_reasons"),
                    "unsupported input lacks an explicit reason")
    if plan_profile(plan) == ALL_INVENTORY_PROFILE:
        require(
            plan.get("ready_count") == count
            and plan.get("unsupported_count") == 0
            and all(entry.get("status") == "ready" for entry in inputs)
            and len(expected_inputs) == count,
            "all-inventory plan is not exactly 400 ready inputs",
        )
    require(canonical_sha256(inputs) == plan.get("ordered_input_sha256"),
            "ordered parser input digest mismatch")
    return plan, plan_data


def _read_stable_source(path: Path) -> bytes:
    try:
        descriptor = os.open(
            path, os.O_RDONLY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0),
        )
    except OSError as error:
        raise ContractError(f"cannot open exact controller source: {path}: {error}") from error
    try:
        before = os.fstat(descriptor)
        chunks = []
        while block := os.read(descriptor, CHUNK_BYTES):
            chunks.append(block)
        after = os.fstat(descriptor)
        named = path.stat(follow_symlinks=False)
    finally:
        os.close(descriptor)
    source = b"".join(chunks)
    require(
        stat.S_ISREG(before.st_mode) and
        (before.st_dev, before.st_ino, before.st_size,
         before.st_mtime_ns, before.st_ctime_ns) ==
        (after.st_dev, after.st_ino, after.st_size,
         after.st_mtime_ns, after.st_ctime_ns) and
        (named.st_dev, named.st_ino) == (after.st_dev, after.st_ino) and
        len(source) == before.st_size,
        f"controller source changed while loading: {path}",
    )
    return source


def _load_exact_source_module(name: str, path: Path, expected: bytes):
    source = _read_stable_source(path)
    require(source == expected, f"captured controller source mismatch: {path.name}")
    source_sha256 = hashlib.sha256(source).hexdigest()
    existing = sys.modules.get(name)
    if existing is not None:
        require(
            getattr(existing, "__candle_source_sha256__", None) == source_sha256 and
            getattr(existing, "__candle_source_bytes__", None) == source and
            Path(getattr(existing, "__file__", "")).resolve() == path,
            f"untrusted preloaded local module: {name}",
        )
        return existing
    module = types.ModuleType(name)
    module.__file__ = str(path)
    module.__package__ = ""
    module.__candle_source_sha256__ = source_sha256
    module.__candle_source_bytes__ = source
    sys.modules[name] = module
    try:
        exec(compile(source, str(path), "exec", dont_inherit=True), module.__dict__)
    except BaseException:
        sys.modules.pop(name, None)
        raise
    return module


def _load_direct_runtime_policy(
    candle_root: Path, candle_head: str, plan: dict[str, Any],
):
    captured: dict[str, bytes] = {}
    bindings = plan.get("authority_sources")
    profile_authorities = profile_authority_source_relatives(plan_profile(plan))
    require(isinstance(bindings, dict) and
            set(bindings) == {path.as_posix() for path in profile_authorities},
            "malformed parser-controller authority source closure")
    for relative_path in profile_authorities:
        relative = relative_path.as_posix()
        path = candle_root / relative_path
        source = _read_stable_source(path)
        validate_git_blob(candle_root, candle_head, relative, source)
        require(bindings[relative] == bytes_record(source, relative),
                f"plan authority source differs from commit: {relative}")
        captured[relative] = source

    # Preload every helper from the already captured, commit-authenticated
    # bytes.  The direct runner's own exact-source loader then encounters only
    # these same path/byte identities; neither import lookup nor a second
    # filesystem read gets to select the transition checker or build lock.
    provenance_path = candle_root / PROVENANCE_RELATIVE
    provenance_source = captured[PROVENANCE_RELATIVE.as_posix()]
    _load_exact_source_module(
        "_candle_bootstrap_transition_provenance",
        provenance_path, provenance_source,
    )
    private_modules = (
        ("_candle_stratum_cakeml_artifact_provenance", PROVENANCE_RELATIVE),
        ("_candle_stratum_cakeml_bootstrap_transition", TRANSITION_CHECKER_RELATIVE),
        ("_candle_stratum_flyspeck_stratum_plan", Path("candle/flyspeck_stratum_plan.py")),
        ("_candle_stratum_reference_protocol", Path("candle/reference_protocol.py")),
        ("_candle_stratum_runtime_lock", RUNTIME_LOCK_RELATIVE),
    )
    for name, relative_path in private_modules:
        _load_exact_source_module(
            name, candle_root / relative_path, captured[relative_path.as_posix()],
        )
    policy_path = candle_root / DIRECT_POLICY_RELATIVE
    policy = _load_exact_source_module(
        "_candle_parser_diagnostic_direct_policy",
        policy_path, captured[DIRECT_POLICY_RELATIVE.as_posix()],
    )
    require(policy.RUNNER_SOURCE_BYTES == captured[DIRECT_POLICY_RELATIVE.as_posix()],
            "direct-runtime policy startup capture mismatch")
    expected_modules = {
        "cakeml_artifact_provenance.py": PROVENANCE_RELATIVE,
        "cakeml_bootstrap_transition.py": TRANSITION_CHECKER_RELATIVE,
        "flyspeck_stratum_plan.py": Path("candle/flyspeck_stratum_plan.py"),
        "reference_protocol.py": Path("candle/reference_protocol.py"),
        "runtime_lock.py": RUNTIME_LOCK_RELATIVE,
    }
    observed_modules = {Path(module.__file__).name: module
                        for module in policy.local_python_modules()}
    require(set(observed_modules) == set(expected_modules),
            "direct-runtime policy loaded unexpected source modules")
    for name, relative_path in expected_modules.items():
        module = observed_modules[name]
        expected_path = candle_root / relative_path
        expected_source = captured[relative_path.as_posix()]
        require(Path(module.__file__).resolve() == expected_path and
                module.__candle_source_bytes__ == expected_source and
                module.__candle_source_sha256__ ==
                hashlib.sha256(expected_source).hexdigest(),
                f"direct-runtime policy source rebinding: {name}")
    return policy


def collect_controller_execution(candle_root: Path, policy: Any) -> dict[str, Any]:
    source = candle_root / CONTROLLER_RELATIVE
    require(
        __name__ == "__main__" and __spec__ is None and
        globals().get("__cached__") is None and
        Path(sys.argv[0]).resolve() == source and Path(__file__).resolve() == source,
        "parser controller must execute directly from authenticated source",
    )
    require(set(_EARLY_REQUIRED_FLAGS) == set(policy.EXPECTED_PYTHON_STARTUP_FLAGS),
            "parser-controller startup flag policy shape mismatch")
    require(policy.python_startup_flags() == _EARLY_REQUIRED_FLAGS,
            "parser-controller Python startup flags mismatch")
    require(policy.python_startup_options() == policy.EXPECTED_PYTHON_STARTUP_OPTIONS,
            "parser-controller Python startup options mismatch")
    environment = policy.cakeml_artifact_provenance.bootstrap_controller_environment()
    return {
        "direct_script_startup": {
            "module_name": "__main__", "spec_is_none": True,
            "cached_is_none": True, "argv0": str(source),
            "source_path": str(source),
        },
        "python_startup_flags": policy.python_startup_flags(),
        "python_startup_options": policy.python_startup_options(),
        "python_runtime": policy.validate_python_runtime(),
        "host_tools": policy.validate_controller_tools(),
        "environment": environment,
    }


def validate_linked_runtime(
    candle_root: Path, plan: dict[str, Any], policy: Any,
) -> tuple[dict[str, Any], Path]:
    checker = policy.cakeml_bootstrap_transition
    linked = checker.validate_linked_record(candle_root)
    require(linked.get("candle_commit") == plan["repositories"]["candle_commit"],
            "linked runtime Candle commit mismatch")
    require(linked.get("cakeml_commit") == plan["repositories"]["cakeml_commit"],
            "linked runtime CakeML commit mismatch")
    require(linked.get("hol4_commit") == plan["repositories"]["hol4_commit"],
            "linked runtime HOL4 commit mismatch")
    linked_record = candle_root / LINKED_RECORD_RELATIVE
    require(linked_record.is_file() and not linked_record.is_symlink(),
            "missing linked provenance record")
    runtime = candle_root / RUNTIME_RELATIVE
    output_record = linked.get("outputs", {}).get("cake")
    require(isinstance(output_record, dict), "linked runtime lacks cake output identity")
    validate_file(runtime, output_record, "linked parser runtime")
    return linked, runtime


RUNTIME_MEMFD_SEALS = (
    fcntl.F_SEAL_SHRINK | fcntl.F_SEAL_GROW |
    fcntl.F_SEAL_WRITE | fcntl.F_SEAL_SEAL
)


def sealed_runtime_record(descriptor: int) -> dict[str, Any]:
    status = os.fstat(descriptor)
    require(stat.S_ISREG(status.st_mode), "sealed runtime image is not ordinary")
    digest = hashlib.sha256()
    offset = 0
    while offset < status.st_size:
        block = os.pread(descriptor, min(CHUNK_BYTES, status.st_size - offset), offset)
        require(block, "sealed runtime image truncated during rehash")
        digest.update(block)
        offset += len(block)
    seals = fcntl.fcntl(descriptor, fcntl.F_GET_SEALS)
    return {
        "kind": "sealed-anonymous-runtime-image",
        "bytes": status.st_size,
        "sha256": digest.hexdigest(),
        "mode": f"{stat.S_IMODE(status.st_mode):04o}",
        "seals": seals,
        "required_seals": RUNTIME_MEMFD_SEALS,
        "execution": "inherited-fd-via-/proc/self/fd",
    }


def create_sealed_runtime_image(
    runtime: Path, expected: dict[str, Any],
) -> tuple[int, dict[str, Any]]:
    """Capture one verified runtime inode into an immutable executable memfd."""
    source_fd = os.open(
        runtime,
        os.O_RDONLY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0),
    )
    memfd = -1
    try:
        before = os.fstat(source_fd)
        named_before = runtime.stat(follow_symlinks=False)
        require(stat.S_ISREG(before.st_mode) and
                (before.st_dev, before.st_ino) ==
                (named_before.st_dev, named_before.st_ino),
                "linked runtime capture is not one ordinary named inode")
        memfd = os.memfd_create(
            "candle-parser-runtime",
            os.MFD_CLOEXEC | os.MFD_ALLOW_SEALING,
        )
        digest = hashlib.sha256()
        size = 0
        while block := os.read(source_fd, CHUNK_BYTES):
            digest.update(block)
            size += len(block)
            offset = 0
            while offset < len(block):
                offset += os.write(memfd, block[offset:])
        after = os.fstat(source_fd)
        named_after = runtime.stat(follow_symlinks=False)
        require(
            (before.st_dev, before.st_ino, before.st_size,
             before.st_mtime_ns, before.st_ctime_ns) ==
            (after.st_dev, after.st_ino, after.st_size,
             after.st_mtime_ns, after.st_ctime_ns) and
            (after.st_dev, after.st_ino) ==
            (named_after.st_dev, named_after.st_ino) and
            size == before.st_size,
            "linked runtime changed during sealed capture",
        )
        require(size == expected.get("bytes") and
                digest.hexdigest() == expected.get("sha256"),
                "sealed runtime capture differs from linked identity")
        os.fchmod(memfd, 0o500)
        fcntl.fcntl(memfd, fcntl.F_ADD_SEALS, RUNTIME_MEMFD_SEALS)
        record = sealed_runtime_record(memfd)
        require(record["bytes"] == expected["bytes"] and
                record["sha256"] == expected["sha256"] and
                record["mode"] == "0500" and
                record["seals"] & RUNTIME_MEMFD_SEALS == RUNTIME_MEMFD_SEALS,
                "sealed runtime image postcondition mismatch")
        return memfd, record
    except BaseException:
        if memfd >= 0:
            os.close(memfd)
        raise
    finally:
        os.close(source_fd)


def _wait_capped_process_group(
    process: subprocess.Popen[bytes], timeout_seconds: int,
) -> int:
    """Wait without reaping the session leader, then kill any descendants."""
    try:
        pidfd = os.pidfd_open(process.pid, 0)
    except (AttributeError, OSError) as error:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()
        raise ContractError("pidfd supervision is required for parser children") from error
    try:
        poller = select.poll()
        poller.register(pidfd, select.POLLIN)
        completed = bool(poller.poll(timeout_seconds * 1000))
        if not completed:
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            poller.poll(1000)
        # The leader has not been reaped, so its PID cannot be reused here.
        # SIGKILL therefore reaches every remaining member of its fresh session
        # without risking an unrelated process group.
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        return_code = process.wait()
        if not completed:
            raise subprocess.TimeoutExpired(process.args, timeout_seconds)
        return return_code
    finally:
        os.close(pidfd)


def _fresh_private_file(path: Path, data: bytes | None = None) -> int:
    flags = (
        os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW |
        getattr(os, "O_CLOEXEC", 0)
    )
    descriptor = os.open(path, flags, PRIVATE_IO_FILE_MODE)
    os.fchmod(descriptor, PRIVATE_IO_FILE_MODE)
    if data is None:
        return descriptor
    try:
        offset = 0
        while offset < len(data):
            offset += os.write(descriptor, data[offset:])
    finally:
        os.close(descriptor)
    return -1


def run_child_capped(
    command: list[str], input_bytes: bytes, cwd: Path, timeout_seconds: int,
    environment: dict[str, str], preexec_fn: Any, io_root: Path, stem: str,
    max_output_bytes: int, pass_fds: tuple[int, ...] = (),
) -> subprocess.CompletedProcess[bytes]:
    """Run one fresh session with RLIMIT_FSIZE-backed ordinary-file capture."""
    require(re.fullmatch(r"[a-z0-9-]+", stem) is not None,
            "unsafe private parser I/O stem")
    observed_root = io_root.lstat()
    require(stat.S_ISDIR(observed_root.st_mode) and
            stat.S_IMODE(observed_root.st_mode) == PRIVATE_IO_MODE,
            "parser private I/O root is not an exact mode-0700 directory")
    require(max_output_bytes > 0, "parser output cap must be positive")
    stdin_path = io_root / f"{stem}.stdin"
    stdout_path = io_root / f"{stem}.stdout"
    stderr_path = io_root / f"{stem}.stderr"
    _fresh_private_file(stdin_path, input_bytes)
    stdin_fd = os.open(
        stdin_path,
        os.O_RDONLY | os.O_NOFOLLOW | getattr(os, "O_CLOEXEC", 0),
    )
    stdout_fd = _fresh_private_file(stdout_path)
    stderr_fd = _fresh_private_file(stderr_path)
    process = None
    try:
        process = subprocess.Popen(
            command, stdin=stdin_fd, stdout=stdout_fd, stderr=stderr_fd,
            env=environment, cwd=cwd, preexec_fn=preexec_fn,
            start_new_session=True, pass_fds=pass_fds,
        )
    finally:
        os.close(stdin_fd)
        os.close(stdout_fd)
        os.close(stderr_fd)
    require(process is not None, "parser child did not start")
    try:
        return_code = _wait_capped_process_group(process, timeout_seconds)
    except BaseException:
        if process.poll() is None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            process.wait()
        raise
    stdout_size = stdout_path.lstat().st_size
    stderr_size = stderr_path.lstat().st_size
    require(stdout_size <= max_output_bytes and stderr_size <= max_output_bytes,
            "parser child output exceeded its effective file cap")
    stdout = _read_stable_source(stdout_path)
    stderr = _read_stable_source(stderr_path)
    require(len(stdout) == stdout_size and len(stderr) == stderr_size,
            "parser child output size changed during capped capture")
    return subprocess.CompletedProcess(command, return_code, stdout, stderr)


def capability_handshake(
    runtime: Path, runtime_cwd: Path, timeout_seconds: int,
    environment: dict[str, str], preexec_fn: Any, io_root: Path,
    max_output_bytes: int, pass_fds: tuple[int, ...] = (),
) -> tuple[dict[str, Any], dict[str, bytes]]:
    result = run_child_capped(
        [str(runtime), CAPABILITY_ARGUMENT], b"",
        runtime_cwd, timeout_seconds, environment,
        preexec_fn, io_root, "capability", max_output_bytes, pass_fds,
    )
    stdout_name = "capability.stdout"
    stderr_name = "capability.stderr"
    record = {
        "command": [RUNTIME_RELATIVE.as_posix(), CAPABILITY_ARGUMENT],
        "exit_code": result.returncode,
        "stdin": bytes_record(b""),
        "stdout": bytes_record(result.stdout, stdout_name),
        "stderr": bytes_record(result.stderr, stderr_name),
    }
    require(result.returncode == 0, "parser runtime capability command failed")
    require(result.stdout == CAPABILITY_LINE, "parser runtime capability mismatch")
    require(result.stderr == b"", "parser runtime capability wrote stderr")
    return record, {
        stdout_name: result.stdout,
        stderr_name: result.stderr,
    }


def parse_protocol_result(
    nonce: str, result: subprocess.CompletedProcess[bytes],
) -> dict[str, Any]:
    require(HEX64.fullmatch(nonce) is not None, "invalid parser request nonce")
    ok = RESULT_PREFIX + nonce.encode() + b"\tOK\n"
    if result.returncode == 0 and result.stdout == ok and result.stderr == b"":
        return {"outcome": "parse-ok", "controller_stderr_digest": None}
    parse_error = RESULT_PREFIX + nonce.encode() + b"\tPARSE_ERROR\n"
    if result.returncode == PARSER_ERROR_EXIT and result.stdout == parse_error:
        try:
            result.stderr.decode("utf-8", errors="strict")
        except UnicodeDecodeError as error:
            raise ContractError("parser-error stderr is not well-formed UTF-8") from error
        digest = hashlib.sha256(
            ERROR_DIGEST_DOMAIN + result.stderr,
        ).hexdigest()
        return {
            "outcome": "parse-error",
            "controller_stderr_digest": {
                "algorithm": "sha256",
                "domain_hex": ERROR_DIGEST_DOMAIN.hex(),
                "sha256": digest,
                "preimage_bytes": len(ERROR_DIGEST_DOMAIN) + len(result.stderr),
                "stderr_bytes": len(result.stderr),
            },
        }
    raise ContractError("parser runtime response violates protocol")


def run_runtime(
    runtime: Path, runtime_cwd: Path, plan_root: Path,
    plan: dict[str, Any], timeout_seconds: int,
    environment: dict[str, str], preexec_fn: Any, io_root: Path,
    max_output_bytes: int, pass_fds: tuple[int, ...] = (),
) -> tuple[dict[str, Any], dict[str, bytes]]:
    require(plan.get("unsupported_count") == 0,
            "plan contains unsupported actions; no parser process launched")
    count = profile_input_count(plan)
    inputs = plan.get("inputs")
    require(
            plan.get("ready_count") == count
            and plan.get("input_count") == count
            and isinstance(inputs, list) and len(inputs) == count
            and all(
                isinstance(entry, dict)
                and entry.get("status") == "ready"
                and isinstance(entry.get("prepared_input"), dict)
                for entry in inputs
            ),
            "plan contains unsupported actions; no parser process launched")
    capability, files = capability_handshake(
        runtime, runtime_cwd, timeout_seconds, environment, preexec_fn,
        io_root, max_output_bytes, pass_fds,
    )
    attempts = []
    for entry in inputs:
        nonce = os.urandom(32).hex()
        prepared = entry["prepared_input"]
        source = validate_file(
            plan_root / prepared["path"], prepared,
            f"prepared parser input {entry['index']}",
        )
        result = run_child_capped(
            [str(runtime), RUN_ARGUMENT, nonce], source,
            runtime_cwd, timeout_seconds, environment,
            preexec_fn, io_root, f"attempt-{entry['index']:03d}",
            max_output_bytes, pass_fds,
        )
        protocol = parse_protocol_result(nonce, result)
        stdout_name = f"attempts/{entry['index']:03d}.stdout"
        stderr_name = f"attempts/{entry['index']:03d}.stderr"
        files[stdout_name] = result.stdout
        files[stderr_name] = result.stderr
        attempts.append({
            "index": entry["index"], "source_key": entry["source_key"],
            "prepared_input": prepared, "nonce": nonce,
            "command": [RUNTIME_RELATIVE.as_posix(), RUN_ARGUMENT, nonce],
            "exit_code": result.returncode,
            "outcome": protocol["outcome"],
            "controller_stderr_digest": protocol["controller_stderr_digest"],
            "stdout": bytes_record(result.stdout, stdout_name),
            "stderr": bytes_record(result.stderr, stderr_name),
        })
    outcome = "parse-pass" if all(row["outcome"] == "parse-ok" for row in attempts) else "parse-failure"
    return {
        "capability": capability,
        "attempt_count": len(attempts),
        "ordered_attempt_sha256": canonical_sha256(attempts),
        "attempts": attempts,
        "outcome": outcome,
    }, files


def snapshot_inventory(
    files: dict[str, bytes], copied_records: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    records = [bytes_record(data, relative) for relative, data in sorted(files.items())]
    records.extend(copied_records or [])
    records.sort(key=lambda record: record["path"])
    paths = [record["path"] for record in records]
    require(len(paths) == len(set(paths)), "duplicate durable snapshot path")
    return {
        "schema": 1,
        "kind": "candle-parser-diagnostic-durable-snapshot",
        "file_count": len(records),
        "ordered_file_sha256": canonical_sha256(records),
        "closed_file_inventory": True,
        "files": records,
    }


def copy_snapshot_file(
    source: Path, staging_root: Path, relative_value: str,
    expected: dict[str, Any], label: str,
) -> dict[str, Any]:
    """Stream-copy one exact ordinary file; mutable hardlinks are forbidden."""
    relative = safe_relative_path(relative_value, "durable snapshot")
    destination = staging_root / relative
    require(not os.path.lexists(destination),
            f"durable snapshot destination collision: {relative}")
    validate_file_record(source, expected, label)
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, destination, follow_symlinks=False)
    destination.chmod(RESULT_FILE_MODE)
    observed = validate_file_record(
        destination, expected, f"copied {label}", relative.as_posix(),
    )
    validate_file_record(source, expected, f"post-copy {label}")
    return {
        "path": observed["path"],
        "bytes": observed["bytes"],
        "sha256": observed["sha256"],
    }


def validate_snapshot_tree(
    result_root: Path, inventory: dict[str, Any],
) -> None:
    """Rehash a closed, ordinary-file-only durable snapshot inventory."""
    require(set(inventory) == {
        "schema", "kind", "file_count", "ordered_file_sha256",
        "closed_file_inventory", "files",
    } and inventory.get("schema") == 1 and
            inventory.get("kind") ==
            "candle-parser-diagnostic-durable-snapshot" and
            inventory.get("closed_file_inventory") is True,
            "snapshot inventory is not closed")
    records = inventory.get("files")
    require(isinstance(records, list) and
            inventory.get("file_count") == len(records) and
            inventory.get("ordered_file_sha256") == canonical_sha256(records),
            "malformed durable snapshot inventory")
    expected: dict[str, dict[str, Any]] = {}
    expected_directories = {Path("snapshot")}
    for record in records:
        require(isinstance(record, dict) and set(record) == {
            "path", "bytes", "sha256",
        }, "malformed durable snapshot file record")
        relative = safe_relative_path(record["path"], "snapshot inventory")
        require(relative.parts and relative.parts[0] == "snapshot",
                "snapshot inventory path is outside snapshot tree")
        require(relative.as_posix() not in expected,
                "duplicate snapshot inventory record")
        expected[relative.as_posix()] = record
        expected_directories.update(
            parent for parent in relative.parents if parent != Path(".")
        )
    snapshot_root = result_root / "snapshot"
    snapshot_status = snapshot_root.lstat()
    require(stat.S_ISDIR(snapshot_status.st_mode) and
            stat.S_IMODE(snapshot_status.st_mode) == RESULT_ROOT_MODE,
            "durable snapshot root is not an exact read-only directory")
    observed_paths = set()
    observed_directories = {Path("snapshot")}
    for current, directory_names, file_names in os.walk(
        snapshot_root, topdown=True, followlinks=False,
    ):
        current_path = Path(current)
        for name in directory_names:
            path = current_path / name
            status = path.lstat()
            require(stat.S_ISDIR(status.st_mode),
                    f"non-directory in durable snapshot: {path}")
            require(stat.S_IMODE(status.st_mode) == RESULT_ROOT_MODE,
                    f"writable durable snapshot directory: {path}")
            observed_directories.add(path.relative_to(result_root))
        for name in file_names:
            path = current_path / name
            relative = path.relative_to(result_root).as_posix()
            require(relative in expected,
                    f"unrecorded durable snapshot file: {relative}")
            require(stat.S_IMODE(path.lstat().st_mode) == RESULT_FILE_MODE,
                    f"writable durable snapshot file: {relative}")
            validate_file_record(
                path, expected[relative], f"durable snapshot {relative}",
            )
            observed_paths.add(relative)
    require(observed_paths == set(expected),
            "durable snapshot file inventory is incomplete")
    require(observed_directories == expected_directories,
            "durable snapshot directory inventory is not closed")


def capture_authority_snapshot(
    candle_root: Path, plan: dict[str, Any],
) -> dict[str, bytes]:
    """Capture only bytes equal to the reconstructed controller authority."""
    bindings = {
        CONTROLLER_RELATIVE.as_posix(): plan.get("controller"),
        **plan.get("authority_sources", {}),
    }
    profile_authorities = profile_authority_source_relatives(plan_profile(plan))
    expected_paths = {
        CONTROLLER_RELATIVE.as_posix(),
        *(relative.as_posix() for relative in profile_authorities),
    }
    require(set(bindings) == expected_paths,
            "malformed authority snapshot closure")
    captured = {}
    for relative in sorted(expected_paths):
        data = _read_stable_source(candle_root / relative)
        require(bindings[relative] == bytes_record(data, relative),
                f"authority source changed before snapshot: {relative}")
        captured[relative] = data
    return captured


def parser_process_preexec(
    policy: Any, cpu_seconds: int, address_space_bytes: int,
    output_file_bytes: int,
) -> Any:
    """Extend the authenticated direct-runner limits with a no-fork policy."""
    inherited = policy.process_limit_preexec(
        cpu_seconds, address_space_bytes, output_file_bytes,
    )

    def install() -> None:
        inherited()
        policy.resource.setrlimit(policy.resource.RLIMIT_NPROC, (0, 0))
        policy.resource.setrlimit(policy.resource.RLIMIT_CORE, (0, 0))

    return install


def selected_original_source_specs(
    candle_root: Path, flyspeck_root: Path, plan: dict[str, Any],
) -> list[tuple[Path, str, dict[str, Any], str]]:
    """Return the closed, collision-free original-blob archive specification."""
    count = profile_input_count(plan)
    inputs = plan.get("inputs")
    require(isinstance(inputs, list) and len(inputs) == count,
            "durable source snapshot does not have the exact profile")
    copies: list[tuple[Path, str, dict[str, Any], str]] = []
    destinations = set()
    for index, entry in enumerate(inputs):
        require(entry.get("index") == index and
                entry.get("repository") in {"candle", "flyspeck"},
                "malformed selected source snapshot binding")
        repository = entry["repository"]
        source_record = entry.get("source")
        require(isinstance(source_record, dict),
                "selected source snapshot lacks identity")
        relative = safe_relative_path(
            source_record.get("path"), "selected original source",
        )
        destination = (
            Path("snapshot/original-sources") / repository / relative
        ).as_posix()
        require(destination not in destinations,
                "selected original source snapshot path collision")
        destinations.add(destination)
        source_root = candle_root if repository == "candle" else flyspeck_root
        copies.append((
            source_root / relative, destination, source_record,
            f"selected original source {entry['source_key']}",
        ))
    require(len(copies) == count and len(destinations) == count,
            "selected original source snapshot inventory is not closed")
    return copies


def durable_snapshot_sources(
    candle_root: Path, flyspeck_root: Path,
    plan: dict[str, Any], linked: dict[str, Any],
    controller_execution: dict[str, Any], policy: Any,
) -> tuple[dict[str, bytes], list[tuple[Path, str, dict[str, Any], str]], str | None]:
    """Close the durable evidence set over source, link, and ELF authorities."""
    byte_files: dict[str, bytes] = {}
    manifest_data = _read_stable_source(candle_root / MANIFEST_RELATIVE)
    require(bytes_record(manifest_data, MANIFEST_RELATIVE.as_posix()) ==
            plan["manifest"], "manifest changed before durable snapshot")
    byte_files["snapshot/authority/candle/flyspeck_manifest.json"] = manifest_data
    if plan_profile(plan) == PILOT_PROFILE:
        pilot_data = _read_stable_source(candle_root / PILOT_RELATIVE)
        require(bytes_record(pilot_data, PILOT_RELATIVE.as_posix()) ==
                plan["pilot"]["file"], "pilot changed before durable snapshot")
        byte_files[
            "snapshot/authority/candle/flyspeck_parser_diagnostic_pilot.json"
        ] = pilot_data
    else:
        descriptor_data = _read_stable_source(
            candle_root / ALL_INVENTORY_RELATIVE,
        )
        descriptor_record = plan["profile"]["descriptor"]["file"]
        require(
            bytes_record(descriptor_data, ALL_INVENTORY_RELATIVE.as_posix())
            == descriptor_record,
            "all-inventory descriptor changed before durable snapshot",
        )
        normalization_data = _read_stable_source(
            candle_root / NORMALIZATION_RELATIVE,
        )
        normalization_record = plan["source_preparation"]["authorities"][
            "normalization_contract"
        ]
        require(
            bytes_record(normalization_data, NORMALIZATION_RELATIVE.as_posix())
            == normalization_record,
            "normalization contract changed before durable snapshot",
        )
        byte_files[
            "snapshot/authority/candle/"
            "flyspeck_parser_diagnostic_all_inventory.json"
        ] = descriptor_data
        byte_files[
            "snapshot/authority/candle/flyspeck_normalizations.json"
        ] = normalization_data

    copies = selected_original_source_specs(candle_root, flyspeck_root, plan)

    outputs = linked.get("outputs")
    require(isinstance(outputs, dict), "linked record lacks output closure")
    expected_outputs = set(policy.cakeml_artifact_provenance.LINKED_OUTPUTS)
    transition_relative = None
    if linked.get("schema") == policy.cakeml_bootstrap_transition.TRANSITION_LINKED_SCHEMA:
        expected_outputs.add(
            policy.cakeml_bootstrap_transition.LINKED_TRANSITION_RECORD,
        )
        transition_relative = (
            "snapshot/linked/outputs/" +
            policy.cakeml_bootstrap_transition.LINKED_TRANSITION_RECORD
        )
    require(set(outputs) == expected_outputs,
            "linked output closure differs from authenticated schema")
    build_dir = candle_root / "candle/build"
    for name, expected in sorted(outputs.items()):
        require(Path(name).name == name and name not in {"", ".", ".."},
                f"unsafe linked output name: {name}")
        copies.append((
            build_dir / name, f"snapshot/linked/outputs/{name}", expected,
            f"linked output {name}",
        ))

    patch = linked.get("cake_patch")
    patch_derivation = linked.get("cake_patch_derivation")
    native_derivation = linked.get("native_link_derivation")
    require(isinstance(patch, dict) and isinstance(patch_derivation, dict) and
            patch_derivation.get("patch") == patch and
            patch_derivation.get("preimage") == outputs.get("cake.S.bootstrap") and
            patch_derivation.get("postimage") == outputs.get("cake.S"),
            "Cake patch derivation does not bind archived inputs")
    require(isinstance(native_derivation, dict) and
            native_derivation.get("inputs") == {
                name: outputs[name]
                for name in policy.cakeml_artifact_provenance.NATIVE_LINK_INPUTS
            } and
            native_derivation.get("installed_elf") == outputs.get("cake") and
            native_derivation.get("candidate_elf") == outputs.get("cake"),
            "native-link derivation does not bind archived inputs")
    copies.append((
        candle_root / "candle/cake.S.patch",
        "snapshot/linked/derivation/cake.S.patch", patch,
        "CakeML assembly patch",
    ))

    runtime_closure = linked.get("runtime_elf_closure")
    closure_files = runtime_closure.get("files") if isinstance(runtime_closure, dict) else None
    require(isinstance(closure_files, dict) and closure_files,
            "linked runtime ELF closure has no files")
    for index, (path_string, expected) in enumerate(sorted(closure_files.items())):
        source = Path(path_string)
        require(source.is_absolute(), "runtime ELF closure path is not absolute")
        copies.append((
            source,
            f"snapshot/linked/runtime-elf/{index:03d}-{expected['sha256']}-{source.name}",
            expected, f"runtime ELF object {path_string}",
        ))

    python_runtime = controller_execution["python_runtime"]
    python_executable = python_runtime["executable"]
    copies.append((
        Path(python_executable["path"]),
        f"snapshot/controller/python/{python_executable['sha256']}-{Path(python_executable['path']).name}",
        python_executable, "controller Python executable",
    ))
    for index, (path_string, expected) in enumerate(sorted(
        python_runtime["elf_closure"]["files"].items(),
    )):
        source = Path(path_string)
        copies.append((
            source,
            f"snapshot/controller/python-elf/{index:03d}-{expected['sha256']}-{source.name}",
            expected, f"controller Python ELF object {path_string}",
        ))
    for label, tool in sorted(controller_execution["host_tools"].items()):
        source = Path(tool["resolved_path"])
        copies.append((
            source,
            f"snapshot/controller/host-tools/{label}-{tool['sha256']}-{source.name}",
            tool, f"controller host tool {label}",
        ))

    toolchain = native_derivation.get("toolchain", {}).get("tools", {})
    require(isinstance(toolchain, dict) and toolchain,
            "native-link toolchain closure is missing")
    for label, tool in sorted(toolchain.items()):
        require(isinstance(tool, dict) and isinstance(tool.get("file"), dict),
                f"malformed native-link tool identity: {label}")
        source = Path(tool["resolved_path"])
        copies.append((
            source,
            f"snapshot/linked/native-tools/{label}-{tool['file']['sha256']}-{source.name}",
            tool["file"], f"native-link tool {label}",
        ))
    return byte_files, copies, transition_relative


RUNTIME_RESULT_FIELDS = frozenset({
    "capability", "attempt_count", "ordered_attempt_sha256", "attempts", "outcome",
})
CAPABILITY_RESULT_FIELDS = frozenset({
    "command", "exit_code", "stdin", "stdout", "stderr",
})
ATTEMPT_RESULT_FIELDS = frozenset({
    "index", "source_key", "prepared_input", "nonce", "command", "exit_code",
    "outcome", "controller_stderr_digest", "stdout", "stderr",
})
DIAGNOSTIC_RECEIPT_FIELDS = frozenset({
    "schema", "kind", "claim", "promotion", "plan", "host_materialization",
    "controller", "controller_execution", "runtime_lock", "resource_limits",
    "linked_provenance", "linked_provenance_schema", "bootstrap_transition",
    "runtime", "runtime_execution", "snapshot", "capability", "attempt_count",
    "ordered_attempt_sha256", "attempts", "outcome", "limitations",
})
ALL_INVENTORY_RECEIPT_FIELDS = frozenset({
    *DIAGNOSTIC_RECEIPT_FIELDS,
    "profile", "source_preparation",
})
SEALED_RUNTIME_EXECUTION_FIELDS = frozenset({
    "kind", "bytes", "sha256", "mode", "seals", "required_seals", "execution",
})


def validate_runtime_result(
    plan: dict[str, Any], runtime_result: dict[str, Any],
    transcript_files: dict[str, bytes],
) -> None:
    """Bind a receipt to one exact parser attempt for every selected input."""
    require(isinstance(plan, dict), "parser result plan is not an object")
    require(isinstance(runtime_result, dict) and
            set(runtime_result) == RUNTIME_RESULT_FIELDS,
            "parser runtime result field set is not closed")
    require(
        isinstance(transcript_files, dict) and
        all(type(path) is str and type(data) is bytes
            for path, data in transcript_files.items()),
        "parser transcript byte map is malformed",
    )

    def exact_json_equal(left: Any, right: Any) -> bool:
        try:
            return canonical_bytes(left) == canonical_bytes(right)
        except (TypeError, ValueError):
            return False

    def exact_record(
        record: Any, data: bytes, path: str | None, label: str,
    ) -> None:
        expected = bytes_record(data, path)
        require(
            isinstance(record, dict) and set(record) == set(expected) and
            type(record.get("bytes")) is int and
            isinstance(record.get("sha256"), str) and
            (path is None or type(record.get("path")) is str) and
            exact_json_equal(record, expected),
            f"{label} byte record is not exact",
        )

    def record_shape(record: Any, label: str) -> None:
        require(
            isinstance(record, dict) and
            set(record) == {"path", "bytes", "sha256"} and
            type(record.get("path")) is str and
            type(record.get("bytes")) is int and record["bytes"] >= 0 and
            isinstance(record.get("sha256"), str) and
            HEX64.fullmatch(record["sha256"]) is not None,
            f"{label} byte record shape is not exact",
        )

    inputs = plan.get("inputs")
    attempts = runtime_result.get("attempts")
    require(
        isinstance(inputs, list) and
        type(plan.get("input_count")) is int and
        plan["input_count"] == len(inputs) and
        isinstance(attempts, list) and
        type(runtime_result.get("attempt_count")) is int and
        runtime_result["attempt_count"] == len(attempts) == len(inputs) and
        len(inputs) > 0,
        "parser result must contain exactly one attempt per selected input",
    )
    capability = runtime_result.get("capability")
    base_transcripts = {"capability.stdout", "capability.stderr"}
    require(base_transcripts <= set(transcript_files),
            "parser capability transcript bytes are missing")
    require(
        isinstance(capability, dict) and
        set(capability) == CAPABILITY_RESULT_FIELDS and
        capability.get("command") == [
            RUNTIME_RELATIVE.as_posix(), CAPABILITY_ARGUMENT,
        ] and
        type(capability.get("exit_code")) is int and
        capability["exit_code"] == 0,
        "parser capability result does not match the exact protocol",
    )
    exact_record(capability.get("stdin"), b"", None, "parser capability stdin")
    exact_record(
        capability.get("stdout"), transcript_files["capability.stdout"],
        "capability.stdout", "parser capability stdout",
    )
    exact_record(
        capability.get("stderr"), transcript_files["capability.stderr"],
        "capability.stderr", "parser capability stderr",
    )
    require(
        transcript_files["capability.stdout"] == CAPABILITY_LINE and
        transcript_files["capability.stderr"] == b"",
        "parser capability transcript violates the exact protocol",
    )
    nonces = set()
    expected_transcript_paths = set(base_transcripts)
    for index, (entry, attempt) in enumerate(zip(inputs, attempts, strict=True)):
        prepared_input = entry.get("prepared_input") if isinstance(entry, dict) else None
        record_shape(prepared_input, "parser plan prepared input")
        require(
            isinstance(entry, dict) and
            type(entry.get("index")) is int and entry["index"] == index and
            entry.get("status") == "ready" and
            isinstance(entry.get("source_key"), str),
            "parser plan input is not an ordered ready input",
        )
        attempt_prepared = attempt.get("prepared_input") if isinstance(attempt, dict) else None
        record_shape(attempt_prepared, "parser attempt prepared input")
        require(
            isinstance(attempt, dict) and
            set(attempt) == ATTEMPT_RESULT_FIELDS and
            attempt.get("index") == index and
            type(attempt.get("index")) is int and
            attempt.get("source_key") == entry.get("source_key") and
            exact_json_equal(attempt_prepared, prepared_input),
            "parser attempt does not match its selected plan input",
        )
        nonce = attempt.get("nonce")
        require(
            isinstance(nonce, str) and HEX64.fullmatch(nonce) is not None and
            nonce not in nonces and
            attempt.get("command") == [
                RUNTIME_RELATIVE.as_posix(), RUN_ARGUMENT, nonce,
            ],
            "parser attempt nonce or command is invalid",
        )
        nonces.add(nonce)
        outcome = attempt.get("outcome")
        require(isinstance(outcome, str) and
                outcome in {"parse-ok", "parse-error"},
                "parser attempt outcome is invalid")
        exit_code = attempt.get("exit_code")
        require(type(exit_code) is int,
                "parser attempt exit code is not an exact integer")
        stdout = attempt.get("stdout")
        stderr = attempt.get("stderr")
        stdout_path = f"attempts/{index:03d}.stdout"
        stderr_path = f"attempts/{index:03d}.stderr"
        expected_transcript_paths.update({stdout_path, stderr_path})
        require(
            stdout_path in transcript_files and stderr_path in transcript_files,
            "parser attempt transcript bytes are missing",
        )
        stdout_data = transcript_files[stdout_path]
        stderr_data = transcript_files[stderr_path]
        exact_record(stdout, stdout_data, stdout_path, "parser attempt stdout")
        exact_record(stderr, stderr_data, stderr_path, "parser attempt stderr")
        derived = parse_protocol_result(
            nonce,
            subprocess.CompletedProcess(
                attempt["command"], exit_code, stdout_data, stderr_data,
            ),
        )
        require(
            outcome == derived["outcome"] and
            exact_json_equal(
                attempt.get("controller_stderr_digest"),
                derived["controller_stderr_digest"],
            ),
            "parser attempt metadata differs from the exact transcript",
        )
    require(set(transcript_files) == expected_transcript_paths,
            "parser transcript byte-map closure mismatch")
    require(runtime_result.get("ordered_attempt_sha256") ==
            canonical_sha256(attempts),
            "ordered parser attempt digest mismatch")
    expected_outcome = (
        "parse-pass"
        if all(attempt["outcome"] == "parse-ok" for attempt in attempts)
        else "parse-failure"
    )
    require(runtime_result.get("outcome") == expected_outcome,
            "aggregate parser outcome mismatch")


def build_diagnostic_receipt(
    plan: dict[str, Any], expected_plan_data: bytes, expected_host: dict[str, Any],
    controller_execution: dict[str, Any], runtime_lock_record: dict[str, Any],
    timeout_seconds: int, max_cpu_seconds: int, max_address_space_gib: int,
    max_output_bytes: int, linked_bytes: bytes, linked: dict[str, Any],
    transition_snapshot: dict[str, Any] | None, runtime_snapshot: dict[str, Any],
    runtime_execution: dict[str, Any], inventory: dict[str, Any],
    runtime_result: dict[str, Any], transcript_files: dict[str, bytes],
) -> dict[str, Any]:
    """Build closed profile-specific parser-only diagnostic evidence."""
    profile_id = plan_profile(plan)
    count = profile_input_count(plan)
    require(
        decode_object(expected_plan_data, "captured receipt plan") == plan,
        "receipt plan bytes differ from selected plan object",
    )
    protocol = plan.get("parser_runtime_protocol")
    require(isinstance(protocol, dict) and
            protocol.get("schema") == PARSER_RUNTIME_PROTOCOL_SCHEMA,
            "receipt plan does not use parser runtime protocol schema 2")
    validate_runtime_result(plan, runtime_result, transcript_files)
    require(set(runtime_execution) == SEALED_RUNTIME_EXECUTION_FIELDS and
            runtime_execution.get("kind") == "sealed-anonymous-runtime-image" and
            runtime_execution.get("mode") == "0500" and
            runtime_execution.get("execution") == "inherited-fd-via-/proc/self/fd" and
            runtime_execution.get("required_seals") == RUNTIME_MEMFD_SEALS and
            isinstance(runtime_execution.get("seals"), int) and
            runtime_execution["seals"] & RUNTIME_MEMFD_SEALS == RUNTIME_MEMFD_SEALS,
            "receipt sealed runtime execution record is malformed")
    require(set(runtime_snapshot) == {"path", "bytes", "sha256"} and
            runtime_snapshot.get("path") == "snapshot/linked/outputs/cake" and
            runtime_execution["bytes"] == runtime_snapshot["bytes"] and
            runtime_execution["sha256"] == runtime_snapshot["sha256"],
            "receipt executed runtime is not bound to archived linked runtime")

    inventory_files = inventory.get("files") if isinstance(inventory, dict) else None
    require(isinstance(inventory, dict) and set(inventory) == {
                "schema", "kind", "file_count", "ordered_file_sha256",
                "closed_file_inventory", "files",
            } and inventory.get("schema") == 1 and
            inventory.get("kind") == "candle-parser-diagnostic-durable-snapshot" and
            inventory.get("closed_file_inventory") is True and
            isinstance(inventory_files, list) and
            inventory.get("file_count") == len(inventory_files) and
            inventory.get("ordered_file_sha256") == canonical_sha256(inventory_files) and
            all(isinstance(record, dict) and
                isinstance(record.get("path"), str)
                for record in inventory_files) and
            len({record["path"] for record in inventory_files}) == len(inventory_files),
            "receipt durable snapshot inventory shape is not closed")
    require(runtime_snapshot in inventory_files,
            "receipt runtime is absent from durable snapshot inventory")
    if profile_id == ALL_INVENTORY_PROFILE:
        descriptor_file = plan["profile"]["descriptor"]["file"]
        normalization_file = plan["source_preparation"]["authorities"][
            "normalization_contract"
        ]
        preparation_file = plan["authority_sources"][
            ALL_INVENTORY_SOURCES_RELATIVE.as_posix()
        ]
        required_profile_authorities = {
            canonical_bytes(bytes_record(
                expected_plan_data, f"snapshot/plan/{PLAN_NAME}",
            )),
            canonical_bytes(bytes_record(
                json_bytes(expected_host),
                f"snapshot/plan/{HOST_RECEIPT_NAME}",
            )),
            canonical_bytes({
                **descriptor_file,
                "path": (
                    "snapshot/authority/candle/"
                    "flyspeck_parser_diagnostic_all_inventory.json"
                ),
            }),
            canonical_bytes({
                **normalization_file,
                "path": "snapshot/authority/candle/flyspeck_normalizations.json",
            }),
            canonical_bytes({
                **preparation_file,
                "path": (
                    "snapshot/authority/candle/"
                    "flyspeck_all_inventory_sources.py"
                ),
            }),
        }
        observed_inventory_records = {
            canonical_bytes(record) for record in inventory_files
        }
        require(
            required_profile_authorities <= observed_inventory_records,
            "all-inventory durable profile authority closure mismatch",
        )
    expected_transcripts = {
        canonical_bytes(bytes_record(
            data, f"snapshot/runtime/{relative}",
        ))
        for relative, data in transcript_files.items()
    }
    observed_transcripts = {
        canonical_bytes(record)
        for record in inventory_files
        if isinstance(record, dict) and
        isinstance(record.get("path"), str) and
        record["path"].startswith("snapshot/runtime/")
    }
    require(observed_transcripts == expected_transcripts,
            "receipt runtime transcript snapshot closure mismatch")
    original_prefix = "snapshot/original-sources/"
    observed_originals = {
        record.get("path"): record
        for record in inventory_files
        if isinstance(record, dict) and
        isinstance(record.get("path"), str) and
        record["path"].startswith(original_prefix)
    }
    expected_originals: dict[str, dict[str, Any]] = {}
    inputs = plan.get("inputs")
    require(isinstance(inputs, list) and len(inputs) == count,
            "receipt plan does not contain the exact parser profile")
    for index, entry in enumerate(inputs):
        require(entry.get("index") == index and
                entry.get("repository") in {"candle", "flyspeck"} and
                isinstance(entry.get("source"), dict),
                "receipt plan has malformed selected source")
        source = entry["source"]
        relative = safe_relative_path(source.get("path"), "receipt original source")
        destination = (
            Path(original_prefix) / entry["repository"] / relative
        ).as_posix()
        require(destination not in expected_originals,
                "receipt original source snapshot path collision")
        expected_originals[destination] = {
            "path": destination,
            "bytes": source.get("bytes"),
            "sha256": source.get("sha256"),
        }
    require(observed_originals == expected_originals,
            "receipt original source snapshot closure mismatch")

    receipt: dict[str, Any] = {
        "schema": (
            DIAGNOSTIC_RECEIPT_SCHEMA
            if profile_id == PILOT_PROFILE
            else ALL_INVENTORY_RECEIPT_SCHEMA
        ),
        "kind": (
            "candle-flyspeck-caml-parser-diagnostic-receipt"
            if profile_id == PILOT_PROFILE
            else "candle-flyspeck-caml-parser-all-inventory-diagnostic-receipt"
        ),
        "claim": "parser-only diagnostic; categorically non-promotable",
        "promotion": plan["promotion"],
        "plan": bytes_record(
            expected_plan_data, f"snapshot/plan/{PLAN_NAME}",
        ),
        "host_materialization": bytes_record(
            json_bytes(expected_host), f"snapshot/plan/{HOST_RECEIPT_NAME}",
        ),
        "controller": plan["controller"],
        "controller_execution": controller_execution,
        "runtime_lock": runtime_lock_record,
        "resource_limits": {
            "timeout_seconds": timeout_seconds,
            "cpu_seconds": max_cpu_seconds,
            "address_space_bytes": max_address_space_gib * 1024 * 1024 * 1024,
            "effective_stdout_file_bytes": max_output_bytes,
            "effective_stderr_file_bytes": max_output_bytes,
            "capture": "fresh-private-ordinary-files-rlimit-fsize",
            "child_process_creation_rlimit_nproc": 0,
            "core_file_bytes": 0,
        },
        "linked_provenance": bytes_record(
            linked_bytes, "snapshot/linked/cakeml-build-provenance.json",
        ),
        "linked_provenance_schema": linked.get("schema"),
        "bootstrap_transition": transition_snapshot,
        "runtime": runtime_snapshot,
        "runtime_execution": runtime_execution,
        "snapshot": inventory,
        **runtime_result,
        "limitations": plan["limitations"],
    }
    expected_fields = DIAGNOSTIC_RECEIPT_FIELDS
    if profile_id == ALL_INVENTORY_PROFILE:
        receipt["profile"] = plan["profile"]
        receipt["source_preparation"] = plan["source_preparation"]
        expected_fields = ALL_INVENTORY_RECEIPT_FIELDS
    require(set(receipt) == expected_fields,
            "diagnostic receipt field set is not closed")
    return receipt


def run(
    plan_root: Path,
    candle_root: Path,
    candle_head: str,
    flyspeck_root: Path,
    flyspeck_head: str,
    output_root: Path,
    timeout_seconds: int,
    max_cpu_seconds: int,
    max_address_space_gib: int,
    max_output_mib: int,
    profile: str,
) -> dict[str, Any]:
    profile_authority_source_relatives(profile)
    plan_root = resolve_without_symlinks(plan_root, "plan root")
    candle_root = resolve_without_symlinks(candle_root, "Candle root")
    flyspeck_root = resolve_without_symlinks(flyspeck_root, "Flyspeck root")
    output_root = validate_fresh_output_root(output_root, "result output root")
    for label, authority_root in (
        ("plan", plan_root), ("Candle", candle_root),
        ("Flyspeck", flyspeck_root),
    ):
        require(output_root != authority_root and
                not output_root.is_relative_to(authority_root),
                f"result output root must be outside {label} root")
    require(timeout_seconds > 0, "timeout must be positive")
    require(0 < max_cpu_seconds <= 172800,
            "CPU-time limit must be between 1 and 172800 seconds")
    require(0 < max_address_space_gib <= 120,
            "address-space limit must be between 1 and 120 GiB")
    require(0 < max_output_mib <= 16,
            "per-stream output limit must be between 1 and 16 MiB")

    expected_plan, expected_inputs, expected_host, expected_plan_data = (
        reconstruct_plan_authority(
            candle_root, candle_head, flyspeck_root, flyspeck_head, profile,
        )
    )
    plan, plan_data = validate_plan_root(
        plan_root, expected_plan, expected_inputs, expected_host,
    )
    require(plan_data == expected_plan_data,
            "validated plan bytes differ from authority reconstruction")
    policy = _load_direct_runtime_policy(candle_root, candle_head, plan)
    controller_execution = collect_controller_execution(candle_root, policy)
    require(controller_execution == expected_host["controller_execution"],
            "controller execution changed after plan reconstruction")
    environment = policy.cakeml_artifact_provenance.runtime_environment()
    max_output_bytes = max_output_mib * 1024 * 1024
    preexec_fn = parser_process_preexec(
        policy,
        max_cpu_seconds,
        max_address_space_gib * 1024 * 1024 * 1024,
        max_output_bytes,
    )

    runtime_lock_handle = policy.runtime_lock.acquire_build_lock(candle_root)
    runtime_descriptor = -1
    try:
        linked, runtime = validate_linked_runtime(candle_root, plan, policy)
        linked_path = candle_root / LINKED_RECORD_RELATIVE
        linked_bytes = _read_stable_source(linked_path)
        require(decode_object(linked_bytes, "captured linked provenance") == linked,
                "linked provenance bytes differ from validated object")
        runtime_before = file_record(runtime, RUNTIME_RELATIVE.as_posix())
        runtime_expected = linked["outputs"]["cake"]
        runtime_descriptor, runtime_execution = create_sealed_runtime_image(
            runtime, runtime_expected,
        )
        execution_runtime = Path(f"/proc/self/fd/{runtime_descriptor}")
        with tempfile.TemporaryDirectory(
            prefix=f".{output_root.name}.parser-io-", dir=output_root.parent,
        ) as private_io_string:
            private_io_root = Path(private_io_string)
            private_io_root.chmod(PRIVATE_IO_MODE)
            runtime_result, files = run_runtime(
                execution_runtime, candle_root, plan_root, plan,
                timeout_seconds, environment, preexec_fn, private_io_root,
                max_output_bytes, (runtime_descriptor,),
            )

        authority_snapshot = capture_authority_snapshot(candle_root, plan)
        snapshot_files = {
            f"snapshot/plan/{PLAN_NAME}": expected_plan_data,
            f"snapshot/plan/{HOST_RECEIPT_NAME}": json_bytes(expected_host),
            **{
                f"snapshot/plan/{relative}": data
                for relative, data in expected_inputs.items()
            },
            "snapshot/linked/cakeml-build-provenance.json": linked_bytes,
            **{
                f"snapshot/authority/{relative}": data
                for relative, data in authority_snapshot.items()
            },
            **{
                f"snapshot/runtime/{relative}": data
                for relative, data in files.items()
            },
        }
        durable_bytes, snapshot_sources, transition_relative = (
            durable_snapshot_sources(
                candle_root, flyspeck_root, plan, linked,
                controller_execution, policy,
            )
        )
        require(not set(snapshot_files).intersection(durable_bytes),
                "durable snapshot byte-path collision")
        snapshot_files.update(durable_bytes)

        linked_post, runtime_post = validate_linked_runtime(
            candle_root, plan, policy,
        )
        require(linked_post == linked,
                "linked provenance changed during parser diagnostic")
        require(_read_stable_source(linked_path) == linked_bytes,
                "linked provenance bytes changed during parser diagnostic")
        require(runtime_post == runtime and
                file_record(runtime_post, RUNTIME_RELATIVE.as_posix()) == runtime_before,
                "linked parser runtime changed during diagnostic")
        require(sealed_runtime_record(runtime_descriptor) == runtime_execution,
                "executed sealed runtime changed during diagnostic")
        require(collect_controller_execution(candle_root, policy) == controller_execution,
                "controller execution changed during parser diagnostic")

        staging = Path(tempfile.mkdtemp(
            prefix=f".{output_root.name}.pending-", dir=output_root.parent,
        ))
        copied_records = [
            copy_snapshot_file(source, staging, relative, expected, label)
            for source, relative, expected, label in snapshot_sources
        ]
        inventory = snapshot_inventory(snapshot_files, copied_records)
        transition_snapshot = (
            next(
                record for record in inventory["files"]
                if record["path"] == transition_relative
            )
            if transition_relative is not None else None
        )
        runtime_snapshot = next(
            record for record in inventory["files"]
            if record["path"] == "snapshot/linked/outputs/cake"
        )
        receipt = build_diagnostic_receipt(
            plan, expected_plan_data, expected_host, controller_execution,
            runtime_lock_handle.record, timeout_seconds, max_cpu_seconds,
            max_address_space_gib, max_output_bytes, linked_bytes, linked,
            transition_snapshot, runtime_snapshot, runtime_execution, inventory,
            runtime_result, files,
        )
        files.update(snapshot_files)
        files[RESULT_NAME] = json_bytes(receipt)
        _write_tree(staging, files, RESULT_ROOT_MODE, RESULT_FILE_MODE)
        validate_snapshot_tree(staging, inventory)
        # One final in-lock validation precedes publication of the captured receipt.
        linked_final, runtime_final = validate_linked_runtime(
            candle_root, plan, policy,
        )
        durable_authority_unchanged = (
            _read_stable_source(candle_root / MANIFEST_RELATIVE)
            == durable_bytes[
                "snapshot/authority/candle/flyspeck_manifest.json"
            ]
        )
        if profile == PILOT_PROFILE:
            durable_authority_unchanged = (
                durable_authority_unchanged
                and _read_stable_source(candle_root / PILOT_RELATIVE)
                == durable_bytes[
                    "snapshot/authority/candle/"
                    "flyspeck_parser_diagnostic_pilot.json"
                ]
            )
        else:
            durable_authority_unchanged = (
                durable_authority_unchanged
                and _read_stable_source(candle_root / ALL_INVENTORY_RELATIVE)
                == durable_bytes[
                    "snapshot/authority/candle/"
                    "flyspeck_parser_diagnostic_all_inventory.json"
                ]
                and _read_stable_source(candle_root / NORMALIZATION_RELATIVE)
                == durable_bytes[
                    "snapshot/authority/candle/flyspeck_normalizations.json"
                ]
            )
        require(linked_final == linked and runtime_final == runtime and
                _read_stable_source(linked_path) == linked_bytes and
                file_record(runtime_final, RUNTIME_RELATIVE.as_posix()) == runtime_before and
                sealed_runtime_record(runtime_descriptor) == runtime_execution and
                capture_authority_snapshot(candle_root, plan) == authority_snapshot and
                durable_authority_unchanged,
                "linked authority changed before receipt publication")
        validate_snapshot_tree(staging, inventory)
        _rename_noreplace(staging, output_root)
        return receipt
    finally:
        if runtime_descriptor >= 0:
            os.close(runtime_descriptor)
        runtime_lock_handle.close()


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    check = subparsers.add_parser("check-pilot")
    check.add_argument("--candle-root", type=Path, default=ROOT)
    write = subparsers.add_parser("write-pilot")
    write.add_argument("--candle-root", type=Path, default=ROOT)
    check_inventory = subparsers.add_parser("check-all-inventory")
    check_inventory.add_argument("--candle-root", type=Path, default=ROOT)
    write_inventory = subparsers.add_parser("write-all-inventory")
    write_inventory.add_argument("--candle-root", type=Path, default=ROOT)
    materializer = subparsers.add_parser("materialize")
    materializer.add_argument(
        "--profile", choices=RUNTIME_PROFILES, required=True,
    )
    materializer.add_argument("--candle-root", type=Path, required=True)
    materializer.add_argument("--flyspeck-root", type=Path, required=True)
    materializer.add_argument("--output-root", type=Path, required=True)
    runner = subparsers.add_parser("run")
    runner.add_argument("--profile", choices=RUNTIME_PROFILES, required=True)
    runner.add_argument("--plan-root", type=Path, required=True)
    runner.add_argument("--candle-root", type=Path, required=True)
    runner.add_argument("--candle-head", required=True)
    runner.add_argument("--flyspeck-root", type=Path, required=True)
    runner.add_argument("--flyspeck-head", required=True)
    runner.add_argument("--output-root", type=Path, required=True)
    runner.add_argument("--timeout-seconds", type=int, default=600)
    runner.add_argument("--max-cpu-seconds", type=int, default=600)
    runner.add_argument("--max-address-space-gib", type=int, default=16)
    runner.add_argument("--max-output-mib", type=int, default=1)
    arguments = parser.parse_args()
    require(dict(os.environ) == EXECUTION_ENVIRONMENT,
            "controller requires exact PATH=/usr/bin:/bin and LC_ALL=C environment")
    require(not os.path.lexists("/etc/ld.so.preload"),
            "system-wide dynamic-loader preload is outside the controller model")
    if arguments.command in {
        "check-pilot", "write-pilot",
        "check-all-inventory", "write-all-inventory",
    }:
        candle_root = resolve_without_symlinks(arguments.candle_root, "Candle root")
        path = candle_root / MANIFEST_RELATIVE
        data = _read_stable_source(path)
        manifest = decode_object(data, "captured Flyspeck manifest")
        if arguments.command in {"check-pilot", "write-pilot"}:
            expected = build_pilot_descriptor(manifest, data)
            descriptor_relative = PILOT_RELATIVE
            count = PILOT_COUNT
            label = "pilot"
        else:
            expected = build_all_inventory_descriptor(manifest, data)
            descriptor_relative = ALL_INVENTORY_RELATIVE
            count = ALL_INVENTORY_COUNT
            label = "all-inventory selection"
        if arguments.command in {"write-pilot", "write-all-inventory"}:
            sys.stdout.buffer.write(json_bytes(expected))
        else:
            descriptor_data = _read_stable_source(
                candle_root / descriptor_relative,
            )
            if arguments.command == "check-pilot":
                validate_pilot(descriptor_data, manifest, data)
            else:
                validate_all_inventory(descriptor_data, manifest, data)
            print(
                f"parser diagnostic {label} PASS: {count} exact manifest nodes"
            )
        return
    if arguments.command == "materialize":
        receipt = materialize(
            arguments.candle_root, arguments.flyspeck_root, arguments.output_root,
            arguments.profile,
        )
        print(f"parser diagnostic plan materialized: {receipt['plan_sha256']}")
        return
    receipt = run(
        arguments.plan_root,
        arguments.candle_root, arguments.candle_head,
        arguments.flyspeck_root, arguments.flyspeck_head,
        arguments.output_root, arguments.timeout_seconds,
        arguments.max_cpu_seconds, arguments.max_address_space_gib,
        arguments.max_output_mib, arguments.profile,
    )
    print(f"parser diagnostic {receipt['outcome']}: {receipt['attempt_count']} inputs")


if __name__ == "__main__":
    try:
        main()
    except (ContractError, OSError, subprocess.SubprocessError) as error:
        raise SystemExit(f"parser diagnostic rejected: {error}") from error
