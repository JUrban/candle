#!/usr/bin/env python3
"""Materialize and run a non-promotable Flyspeck OCaml-parser diagnostic.

The diagnostic is deliberately narrower than a Candle run.  It authenticates
an exact manifest-selected pilot, masks only manifest-classified standalone
loader phrases (which the Candle loader consumes before the OCaml parser), and
submits the remaining exact bytes to a dedicated ``caml_parser$run`` runtime
protocol.  It never substitutes CakeML's ``parse_prog`` parser and never uses
the Candle REPL as a parser oracle.

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
    "isolated": 1,
    "ignore_environment": 1,
    "no_user_site": 1,
    "no_site": 1,
    "safe_path": True,
}
if __name__ == "__main__":
    _early_observed = {
        name: getattr(sys.flags, name) for name in _EARLY_REQUIRED_FLAGS
    }
    if _early_observed != _EARLY_REQUIRED_FLAGS:
        raise SystemExit(
            "parser diagnostic rejected: direct execution requires "
            "/usr/bin/python3 -I -S"
        )

import argparse
import ctypes
import errno
import hashlib
import json
import os
import re
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
PLAN_NAME = "plan.json"
HOST_RECEIPT_NAME = "host-materialization.json"
RESULT_NAME = "receipt.json"
PILOT_COUNT = 20
CHUNK_BYTES = 1024 * 1024
PLAN_ROOT_MODE = 0o555
PLAN_FILE_MODE = 0o444
RESULT_ROOT_MODE = 0o555
RESULT_FILE_MODE = 0o444
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


def validate_pilot(candle_root: Path, manifest: dict[str, Any], manifest_data: bytes) -> dict[str, Any]:
    observed = load_object(candle_root / PILOT_RELATIVE, "parser pilot")
    expected = build_pilot_descriptor(manifest, manifest_data)
    require(observed == expected, "committed parser pilot is stale")
    return observed


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
            "sha256": canonical_sha256(pilot),
            "selection": pilot["selection"],
        },
        "parser_runtime_protocol": {
            "schema": 1,
            "function": "caml_parser$run",
            "language": "CakeML Candle OCaml parser",
            "capability_argument": CAPABILITY_ARGUMENT,
            "capability_stdout_sha256": hashlib.sha256(CAPABILITY_LINE).hexdigest(),
            "run_argument": RUN_ARGUMENT,
            "input": "one exact prepared source on stdin per fresh process",
            "parse_error_exit_code": PARSER_ERROR_EXIT,
            "parse_error_digest": {
                "algorithm": "sha256",
                "domain_hex": ERROR_DIGEST_DOMAIN.hex(),
                "canonical_preimage": (
                    "ASCII bytes CANDLE_CAMLPARSER_ERROR_V1, one NUL byte, "
                    "then the exact stderr byte stream without decoding or newline changes"
                ),
                "wire_encoding": "exactly 64 lowercase ASCII hexadecimal digits",
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


def reconstruct_plan_authority(
    candle_root: Path,
    candle_head: str,
    flyspeck_root: Path,
    flyspeck_head: str,
) -> tuple[dict[str, Any], dict[str, bytes], dict[str, Any], bytes]:
    """Rebuild the only accepted plan from explicit Git-root authorities."""
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
    for relative_path in AUTHORITY_SOURCE_RELATIVES:
        relative = relative_path.as_posix()
        source_data = (candle_root / relative_path).read_bytes()
        validate_git_blob(candle_root, candle_head, relative, source_data)

    manifest_path = candle_root / MANIFEST_RELATIVE
    manifest_data = manifest_path.read_bytes()
    validate_git_blob(
        candle_root, candle_head, MANIFEST_RELATIVE.as_posix(), manifest_data,
    )
    manifest = load_object(manifest_path, "Flyspeck manifest")
    require(manifest.get("schema") == 1, "unsupported Flyspeck manifest schema")
    require(manifest["repositories"]["flyspeck"]["commit"] == flyspeck_head,
            "explicit Flyspeck authority differs from manifest pin")

    pilot_path = candle_root / PILOT_RELATIVE
    pilot_data = pilot_path.read_bytes()
    validate_git_blob(candle_root, candle_head, PILOT_RELATIVE.as_posix(), pilot_data)
    pilot = validate_pilot(candle_root, manifest, manifest_data)
    for pilot_input in pilot["inputs"]:
        node = manifest["source_nodes"][pilot_input["source_key"]]
        root = candle_root if node["repository"] == "candle" else flyspeck_root
        head = candle_head if node["repository"] == "candle" else flyspeck_head
        source_path = root / safe_relative_path(node["path"], "pilot source")
        live = validate_file(
            source_path, node, f"pilot source {pilot_input['source_key']}",
        )
        validate_git_blob(root, head, node["path"], live)
    plan, input_files = build_plan(
        candle_root, flyspeck_root, candle_head, manifest, manifest_data, pilot,
    )
    plan_data = json_bytes(plan)
    policy = _load_direct_runtime_policy(candle_root, candle_head, plan)
    controller_execution = collect_controller_execution(candle_root, policy)
    host = build_host_receipt(
        candle_root, flyspeck_root, plan_data, controller_execution,
    )
    return plan, input_files, host, plan_data


def materialize(
    candle_root: Path, flyspeck_root: Path, output_root: Path,
) -> dict[str, Any]:
    candle_root = resolve_without_symlinks(candle_root, "Candle root")
    flyspeck_root = resolve_without_symlinks(flyspeck_root, "Flyspeck root")
    output_root = validate_fresh_output_root(output_root, "plan output root")
    candle_head = str(git_output(candle_root, "rev-parse", "HEAD"))
    flyspeck_head = str(git_output(flyspeck_root, "rev-parse", "HEAD"))
    plan, input_files, host, plan_data = reconstruct_plan_authority(
        candle_root, candle_head, flyspeck_root, flyspeck_head,
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
    inputs = plan.get("inputs")
    require(isinstance(inputs, list) and len(inputs) == plan.get("input_count") == PILOT_COUNT,
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
    require(isinstance(bindings, dict) and
            set(bindings) == {path.as_posix() for path in AUTHORITY_SOURCE_RELATIVES},
            "malformed parser-controller authority source closure")
    for relative_path in AUTHORITY_SOURCE_RELATIVES:
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
    require(policy.python_startup_flags() == policy.EXPECTED_PYTHON_STARTUP_FLAGS,
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


def capability_handshake(
    runtime: Path, timeout_seconds: int, environment: dict[str, str],
    preexec_fn: Any,
) -> dict[str, Any]:
    result = subprocess.run(
        [str(runtime), CAPABILITY_ARGUMENT], input=b"",
        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        env=environment, cwd=runtime.parent.parent.parent,
        timeout=timeout_seconds, preexec_fn=preexec_fn,
    )
    record = {
        "command": [RUNTIME_RELATIVE.as_posix(), CAPABILITY_ARGUMENT],
        "exit_code": result.returncode,
        "stdin": bytes_record(b""),
        "stdout": bytes_record(result.stdout),
        "stderr": bytes_record(result.stderr),
    }
    require(result.returncode == 0, "parser runtime capability command failed")
    require(result.stdout == CAPABILITY_LINE, "parser runtime capability mismatch")
    require(result.stderr == b"", "parser runtime capability wrote stderr")
    return record


def parse_protocol_result(nonce: str, result: subprocess.CompletedProcess[bytes]) -> str:
    require(HEX64.fullmatch(nonce) is not None, "invalid parser request nonce")
    ok = RESULT_PREFIX + nonce.encode() + b"\tOK\n"
    error_prefix = RESULT_PREFIX + nonce.encode() + b"\tPARSE_ERROR\t"
    if result.returncode == 0 and result.stdout == ok and result.stderr == b"":
        return "parse-ok"
    if (result.returncode == PARSER_ERROR_EXIT and
            result.stdout.startswith(error_prefix) and result.stdout.endswith(b"\n")):
        try:
            result.stderr.decode("utf-8", errors="strict")
        except UnicodeDecodeError as error:
            raise ContractError("parser-error stderr is not well-formed UTF-8") from error
        digest = result.stdout[len(error_prefix):-1]
        require(HEX64.fullmatch(digest.decode(errors="replace")) is not None,
                "malformed parser-error digest")
        expected_digest = hashlib.sha256(
            ERROR_DIGEST_DOMAIN + result.stderr,
        ).hexdigest().encode()
        require(digest == expected_digest,
                "parser-error digest does not bind exact stderr bytes")
        return "parse-error"
    raise ContractError("parser runtime response violates protocol")


def run_runtime(
    runtime: Path, plan_root: Path, plan: dict[str, Any], timeout_seconds: int,
    environment: dict[str, str], preexec_fn: Any,
) -> tuple[dict[str, Any], dict[str, bytes]]:
    require(plan.get("unsupported_count") == 0,
            "plan contains unsupported actions; no parser process launched")
    capability = capability_handshake(
        runtime, timeout_seconds, environment, preexec_fn,
    )
    attempts = []
    files: dict[str, bytes] = {}
    for entry in plan["inputs"]:
        nonce = os.urandom(32).hex()
        prepared = entry["prepared_input"]
        source = validate_file(
            plan_root / prepared["path"], prepared,
            f"prepared parser input {entry['index']}",
        )
        result = subprocess.run(
            [str(runtime), RUN_ARGUMENT, nonce], input=source,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            env=environment, cwd=runtime.parent.parent.parent,
            timeout=timeout_seconds, preexec_fn=preexec_fn,
        )
        status = parse_protocol_result(nonce, result)
        stdout_name = f"attempts/{entry['index']:03d}.stdout"
        stderr_name = f"attempts/{entry['index']:03d}.stderr"
        files[stdout_name] = result.stdout
        files[stderr_name] = result.stderr
        attempts.append({
            "index": entry["index"], "source_key": entry["source_key"],
            "prepared_input": prepared, "nonce": nonce,
            "command": [RUNTIME_RELATIVE.as_posix(), RUN_ARGUMENT, nonce],
            "exit_code": result.returncode, "outcome": status,
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


def snapshot_inventory(files: dict[str, bytes]) -> dict[str, Any]:
    records = [bytes_record(data, relative) for relative, data in sorted(files.items())]
    return {
        "file_count": len(records),
        "ordered_file_sha256": canonical_sha256(records),
        "files": records,
    }


def capture_authority_snapshot(
    candle_root: Path, plan: dict[str, Any],
) -> dict[str, bytes]:
    """Capture only bytes equal to the reconstructed controller authority."""
    bindings = {
        CONTROLLER_RELATIVE.as_posix(): plan.get("controller"),
        **plan.get("authority_sources", {}),
    }
    expected_paths = {
        CONTROLLER_RELATIVE.as_posix(),
        *(relative.as_posix() for relative in AUTHORITY_SOURCE_RELATIVES),
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
    max_output_file_gib: int,
) -> dict[str, Any]:
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
    require(0 < max_output_file_gib <= 16,
            "output-file limit must be between 1 and 16 GiB")

    expected_plan, expected_inputs, expected_host, expected_plan_data = (
        reconstruct_plan_authority(
            candle_root, candle_head, flyspeck_root, flyspeck_head,
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
    preexec_fn = policy.process_limit_preexec(
        max_cpu_seconds,
        max_address_space_gib * 1024 * 1024 * 1024,
        max_output_file_gib * 1024 * 1024 * 1024,
    )

    runtime_lock_handle = policy.runtime_lock.acquire_build_lock(candle_root)
    try:
        linked, runtime = validate_linked_runtime(candle_root, plan, policy)
        linked_path = candle_root / LINKED_RECORD_RELATIVE
        linked_bytes = _read_stable_source(linked_path)
        require(decode_object(linked_bytes, "captured linked provenance") == linked,
                "linked provenance bytes differ from validated object")
        runtime_before = file_record(runtime, RUNTIME_RELATIVE.as_posix())
        runtime_result, files = run_runtime(
            runtime, plan_root, plan, timeout_seconds, environment, preexec_fn,
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
        }
        transition_snapshot = None
        if linked.get("schema") == policy.cakeml_bootstrap_transition.TRANSITION_LINKED_SCHEMA:
            transition_path = candle_root / "candle/build/bootstrap-transition.json"
            transition_bytes = _read_stable_source(transition_path)
            transition_expected = linked.get("transition_record")
            require(isinstance(transition_expected, dict),
                    "schema-7 linked record lacks transition identity")
            require(bytes_record(transition_bytes) == transition_expected,
                    "schema-7 bootstrap transition evidence changed")
            transition_relative = "snapshot/linked/bootstrap-transition.json"
            snapshot_files[transition_relative] = transition_bytes
            transition_snapshot = bytes_record(
                transition_bytes, transition_relative,
            )

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
        require(collect_controller_execution(candle_root, policy) == controller_execution,
                "controller execution changed during parser diagnostic")

        inventory = snapshot_inventory(snapshot_files)
        receipt = {
            "schema": 2,
            "kind": "candle-flyspeck-caml-parser-diagnostic-receipt",
            "claim": "parser-only diagnostic; categorically non-promotable",
            "promotion": plan["promotion"],
            "plan": bytes_record(
                expected_plan_data, f"snapshot/plan/{PLAN_NAME}",
            ),
            "host_materialization": bytes_record(
                json_bytes(expected_host),
                f"snapshot/plan/{HOST_RECEIPT_NAME}",
            ),
            "controller": plan["controller"],
            "controller_execution": controller_execution,
            "runtime_lock": runtime_lock_handle.record,
            "resource_limits": {
                "timeout_seconds": timeout_seconds,
                "cpu_seconds": max_cpu_seconds,
                "address_space_bytes": max_address_space_gib * 1024 * 1024 * 1024,
                "output_file_bytes": max_output_file_gib * 1024 * 1024 * 1024,
            },
            "linked_provenance": bytes_record(
                linked_bytes, "snapshot/linked/cakeml-build-provenance.json",
            ),
            "linked_provenance_schema": linked.get("schema"),
            "bootstrap_transition": transition_snapshot,
            "runtime": runtime_before,
            "snapshot": inventory,
            **runtime_result,
            "limitations": plan["limitations"],
        }
        files.update(snapshot_files)
        files[RESULT_NAME] = json_bytes(receipt)
        staging = Path(tempfile.mkdtemp(
            prefix=f".{output_root.name}.pending-", dir=output_root.parent,
        ))
        _write_tree(staging, files, RESULT_ROOT_MODE, RESULT_FILE_MODE)
        # One final in-lock validation precedes publication of the captured receipt.
        linked_final, runtime_final = validate_linked_runtime(
            candle_root, plan, policy,
        )
        require(linked_final == linked and runtime_final == runtime and
                _read_stable_source(linked_path) == linked_bytes and
                file_record(runtime_final, RUNTIME_RELATIVE.as_posix()) == runtime_before and
                capture_authority_snapshot(candle_root, plan) == authority_snapshot,
                "linked authority changed before receipt publication")
        _rename_noreplace(staging, output_root)
        return receipt
    finally:
        runtime_lock_handle.close()


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    check = subparsers.add_parser("check-pilot")
    check.add_argument("--candle-root", type=Path, default=ROOT)
    write = subparsers.add_parser("write-pilot")
    write.add_argument("--candle-root", type=Path, default=ROOT)
    materializer = subparsers.add_parser("materialize")
    materializer.add_argument("--candle-root", type=Path, required=True)
    materializer.add_argument("--flyspeck-root", type=Path, required=True)
    materializer.add_argument("--output-root", type=Path, required=True)
    runner = subparsers.add_parser("run")
    runner.add_argument("--plan-root", type=Path, required=True)
    runner.add_argument("--candle-root", type=Path, required=True)
    runner.add_argument("--candle-head", required=True)
    runner.add_argument("--flyspeck-root", type=Path, required=True)
    runner.add_argument("--flyspeck-head", required=True)
    runner.add_argument("--output-root", type=Path, required=True)
    runner.add_argument("--timeout-seconds", type=int, default=600)
    runner.add_argument("--max-cpu-seconds", type=int, default=600)
    runner.add_argument("--max-address-space-gib", type=int, default=16)
    runner.add_argument("--max-output-file-gib", type=int, default=1)
    arguments = parser.parse_args()
    require(dict(os.environ) == EXECUTION_ENVIRONMENT,
            "controller requires exact PATH=/usr/bin:/bin and LC_ALL=C environment")
    require(not os.path.lexists("/etc/ld.so.preload"),
            "system-wide dynamic-loader preload is outside the controller model")
    if arguments.command in {"check-pilot", "write-pilot"}:
        candle_root = resolve_without_symlinks(arguments.candle_root, "Candle root")
        path = candle_root / MANIFEST_RELATIVE
        data = path.read_bytes()
        manifest = load_object(path, "Flyspeck manifest")
        expected = build_pilot_descriptor(manifest, data)
        if arguments.command == "write-pilot":
            sys.stdout.buffer.write(json_bytes(expected))
        else:
            validate_pilot(candle_root, manifest, data)
            print(f"parser diagnostic pilot PASS: {PILOT_COUNT} exact manifest nodes")
        return
    if arguments.command == "materialize":
        receipt = materialize(
            arguments.candle_root, arguments.flyspeck_root, arguments.output_root,
        )
        print(f"parser diagnostic plan materialized: {receipt['plan_sha256']}")
        return
    receipt = run(
        arguments.plan_root,
        arguments.candle_root, arguments.candle_head,
        arguments.flyspeck_root, arguments.flyspeck_head,
        arguments.output_root, arguments.timeout_seconds,
        arguments.max_cpu_seconds, arguments.max_address_space_gib,
        arguments.max_output_file_gib,
    )
    print(f"parser diagnostic {receipt['outcome']}: {receipt['attempt_count']} inputs")


if __name__ == "__main__":
    try:
        main()
    except (ContractError, OSError, subprocess.SubprocessError) as error:
        raise SystemExit(f"parser diagnostic rejected: {error}") from error
