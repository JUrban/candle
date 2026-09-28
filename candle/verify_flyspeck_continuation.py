#!/usr/bin/env python3
"""Fail-closed preflight for a generated cumulative Flyspeck continuation.

The continuation is checked against the authoritative manifest rather than
trusted as generated text.  This tool is deliberately read-only apart from an
optional JSON receipt.  It verifies every action directive, source identity,
source byte record, action-ledger delta, stratum gate, normalization overlay,
and the final target before a continuation is submitted to a live Candle
process.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
from typing import Any


HERE = Path(__file__).resolve().parent
DEFAULT_MANIFEST = HERE / "flyspeck_manifest.json"
DEFAULT_RUNTIME = HERE / "flyspeck_stratum_runtime.py"

COMMENT_RE = re.compile(
    r"^\(\* (?P<index>[0-9]+) (?P<key>[^ ]+) "
    r"sha256=(?P<sha256>[0-9a-f]{64}) \*\)$"
)
DIRECTIVE_RE = re.compile(r'^#flyspeck_needs (?P<target>"(?:[^"\\]|\\.)*");;$')
COMMIT_RE = re.compile(
    r"^candle_flyspeck_stratum_commit_action (?P<index>[0-9]+) "
    r"\((?P<basename>\"(?:[^\"\\]|\\.)*\"),"
    r"(?P<md5>\"[0-9a-f]{32}\")\) "
    r"(?P<marker>\"(?:[^\"\\]|\\.)*\");;$"
)
MANIFEST_HEADER_RE = re.compile(r"Manifest SHA-256: (?P<sha256>[0-9a-f]{64})")
INITIAL_GATE_RE = re.compile(
    r"if !Cakeml\.pendingLoadedSourceIds <> \[\] \|\|\s+"
    r"List\.length !candle_flyspeck_stratum_action_events <> (?P<count>[0-9]+)\s+"
    r"then failwith (?P<message>\"(?:[^\"\\]|\\.)*\");;"
)
BOUNDARY_GATE_RE = re.compile(
    r"if !Cakeml\.pendingLoadedSourceIds = \[\] &&\s+"
    r"List\.length !candle_flyspeck_stratum_action_events = (?P<count>[0-9]+)\s+"
    r"then print_endline (?P<marker>\"(?:[^\"\\]|\\.)*\")\s+"
    r"else failwith (?P<failure>\"(?:[^\"\\]|\\.)*\");;"
)
FINAL_MARKER_RE = re.compile(
    r'^print_endline (?P<marker>"CANDLE_FLYSPECK_[^"\\]*DIRECT_FULL_OK");;$',
    re.MULTILINE,
)


class PreflightError(ValueError):
    """The continuation or one of its authenticated inputs did not match."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise PreflightError(message)


def load_runtime(path: Path) -> Any:
    spec = importlib.util.spec_from_file_location(
        "_candle_continuation_runtime", path,
    )
    require(spec is not None and spec.loader is not None,
            "could not construct runtime module loader")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def regular_unaliased_file(path: Path, label: str) -> os.stat_result:
    try:
        observed = path.lstat()
    except FileNotFoundError as error:
        raise PreflightError(f"missing {label}: {path}") from error
    require(stat.S_ISREG(observed.st_mode), f"{label} is not a regular file: {path}")
    require(observed.st_nlink == 1, f"{label} is hard-linked: {path}")
    return observed


def hash_file(path: Path) -> dict[str, Any]:
    regular_unaliased_file(path, "authenticated file")
    sha256 = hashlib.sha256()
    md5 = hashlib.md5(usedforsecurity=False)
    size = 0
    with path.open("rb") as source:
        while block := source.read(1024 * 1024):
            size += len(block)
            sha256.update(block)
            md5.update(block)
    return {"bytes": size, "sha256": sha256.hexdigest(), "md5": md5.hexdigest()}


def require_record(path: Path, expected: dict[str, Any], label: str) -> dict[str, Any]:
    observed = hash_file(path)
    wanted = {key: expected[key] for key in ("bytes", "sha256", "md5")}
    require(observed == wanted,
            f"{label} byte identity mismatch: expected {wanted}, observed {observed}")
    return observed


def git_text(root: Path, *arguments: str) -> str:
    process = subprocess.run(
        ["git", "-C", str(root), *arguments],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    require(process.returncode == 0,
            f"git {' '.join(arguments)} failed for {root}: {process.stderr.strip()}")
    return process.stdout.strip()


def parse_json_string(value: str, label: str) -> str:
    try:
        decoded = json.loads(value)
    except json.JSONDecodeError as error:
        raise PreflightError(f"malformed {label}") from error
    require(isinstance(decoded, str), f"non-string {label}")
    return decoded


def parse_actions(source: str) -> list[dict[str, Any]]:
    lines = source.splitlines()
    records: list[dict[str, Any]] = []
    for offset, line in enumerate(lines):
        comment = COMMENT_RE.fullmatch(line)
        if comment is None:
            continue
        require(offset + 2 < len(lines), "truncated action record")
        directive = DIRECTIVE_RE.fullmatch(lines[offset + 1])
        commit = COMMIT_RE.fullmatch(lines[offset + 2])
        require(directive is not None,
                f"missing action directive after line {offset + 1}")
        require(commit is not None,
                f"missing action commit after line {offset + 1}")
        marker = parse_json_string(commit.group("marker"), "action marker")
        records.append({
            "line": offset + 1,
            "comment_line": line,
            "directive_line": lines[offset + 1],
            "commit_line": lines[offset + 2],
            "index": int(comment.group("index")),
            "key": comment.group("key"),
            "source_sha256": comment.group("sha256"),
            "target": parse_json_string(directive.group("target"), "action target"),
            "commit_index": int(commit.group("index")),
            "identity_basename": parse_json_string(
                commit.group("basename"), "identity basename",
            ),
            "identity_md5": parse_json_string(commit.group("md5"), "identity MD5"),
            "marker": marker,
        })
    directive_count = len(re.findall(r"^#flyspeck_needs ", source, re.MULTILINE))
    commit_count = len(re.findall(
        r"^candle_flyspeck_stratum_commit_action ", source, re.MULTILINE,
    ))
    require(len(records) == directive_count == commit_count,
            "orphaned or unparsed action directive/commit")
    require(records, "continuation contains no action records")
    return records


def source_record_for_key(
    key: str,
    node: dict[str, Any],
    candle_root: Path,
    source_root: Path,
) -> tuple[Path, dict[str, Any]]:
    repository = node.get("repository")
    logical_path = node.get("path")
    require(isinstance(repository, str) and isinstance(logical_path, str),
            f"malformed source node: {key}")
    require(key == f"{repository}:{logical_path}",
            f"source logical identity mismatch: {key}")
    roots = {"candle": candle_root, "flyspeck": source_root}
    require(repository in roots, f"unsupported source repository: {repository}")
    path = roots[repository] / logical_path
    return path, require_record(path, node, f"source {key}")


def expected_ledger_record(
    runtime: Any,
    nodes: dict[str, dict[str, Any]],
    keys: list[str],
) -> tuple[list[dict[str, str]], str]:
    delta = []
    for delta_index, key in enumerate(keys):
        node = nodes.get(key)
        require(isinstance(node, dict), f"unbound ledger source: {key}")
        delta.append({
            "key": key,
            "classification": (
                "observed-outer-source" if delta_index == 0 else
                "observed-nested-source"
            ),
            "source_sha256": node["sha256"],
            "identity_basename": Path(node["path"]).name,
            "identity_md5": node["md5"],
        })
    return delta, runtime.canonical_sha256(delta)


def verify_overlay(
    source: str,
    records: list[dict[str, Any]],
    nodes: dict[str, dict[str, Any]],
    source_root: Path,
    overlay_root: Path,
    expected_existing_count: int,
) -> dict[str, Any]:
    candidates = []
    for record in records:
        node = nodes[record["key"]]
        normalization = node.get("execution_normalization")
        if not isinstance(normalization, dict):
            continue
        candidate = overlay_root / node["path"]
        if candidate.exists() or candidate.is_symlink():
            candidates.append((record, node, normalization, candidate))
    require(len(candidates) == 1,
            "continuation must add exactly one run-local normalization mapping")
    record, node, normalization, candidate = candidates[0]
    original = source_root / node["path"]
    normalized_record = {
        "bytes": normalization.get("normalized_bytes"),
        "sha256": normalization.get("normalized_sha256"),
        "md5": normalization.get("normalized_md5"),
    }
    require(all(isinstance(normalized_record[key], (int, str))
                for key in normalized_record),
            f"malformed normalization record: {record['key']}")
    observed = require_record(candidate, normalized_record,
                              f"normalized source {record['key']}")

    assignment_re = re.compile(
        r'^let (?P<name>[a-zA-Z0-9_]+) =\s+'
        r'(?P<value>"(?:[^"\\]|\\.)*");;$',
        re.MULTILINE,
    )
    assignments = {
        parse_json_string(match.group("value"), "overlay path"): match.group("name")
        for match in assignment_re.finditer(source)
    }
    require(str(original) in assignments,
            "continuation does not bind the expected original overlay path")
    require(str(candidate) in assignments,
            "continuation does not bind the expected candidate overlay path")
    original_name = assignments[str(original)]
    candidate_name = assignments[str(candidate)]

    digest_check = re.compile(
        rf"Digest\.to_hex \(Digest\.file {re.escape(candidate_name)}\) <>\s+"
        rf'"{normalization["normalized_md5"]}"'
    )
    require(digest_check.search(source) is not None,
            "normalized candidate MD5 gate is absent or stale")

    old_count_match = re.search(
        r"List\.length (?P<name>[a-zA-Z0-9_]+) <> (?P<count>[0-9]+) \|\|\s+"
        r"List\.exists\s+\(fun \(original,_\) -> original = "
        rf"{re.escape(original_name)}\)\s+(?P=name)",
        source,
    )
    require(old_count_match is not None, "predecessor overlay gate is malformed")
    old_count = int(old_count_match.group("count"))
    old_name = old_count_match.group("name")
    require(old_count == expected_existing_count,
            "predecessor overlay cardinality does not match the checkpoint contract")

    insert_re = re.compile(
        rf"Some \(\({re.escape(original_name)},{re.escape(candidate_name)}\) ::\s+"
        rf"{re.escape(old_name)}\);;"
    )
    require(insert_re.search(source) is not None,
            "overlay insertion does not use the authenticated mapping")
    new_count_match = re.search(
        r"List\.length mappings <> (?P<count>[0-9]+)\s+\| None -> true\)",
        source,
    )
    require(new_count_match is not None, "post-insertion overlay gate is missing")
    new_count = int(new_count_match.group("count"))
    require(new_count == old_count + len(candidates),
            "post-insertion overlay cardinality is inconsistent")

    return {
        "action_index": record["index"],
        "logical_source": record["key"],
        "normalization_id": normalization.get("id"),
        "original_path": str(original),
        "candidate_path": str(candidate),
        "candidate_record": observed,
        "existing_mapping_count": old_count,
        "resulting_mapping_count": new_count,
    }


def verify(args: argparse.Namespace) -> dict[str, Any]:
    manifest_path = args.manifest.resolve(strict=True)
    runtime_path = args.runtime.resolve(strict=True)
    continuation_path = args.continuation.resolve(strict=True)
    source_root = args.source_root.resolve(strict=True)
    overlay_root = args.overlay_root.resolve(strict=True)
    candle_root = manifest_path.parent.parent

    regular_unaliased_file(manifest_path, "manifest")
    regular_unaliased_file(runtime_path, "stratum runtime")
    regular_unaliased_file(continuation_path, "continuation")
    continuation_record = hash_file(continuation_path)
    manifest_record = hash_file(manifest_path)
    runtime_record = hash_file(runtime_path)

    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        source = continuation_path.read_text(encoding="utf-8")
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise PreflightError("manifest or continuation decoding failed") from error
    require(isinstance(manifest, dict), "manifest root is not an object")
    nodes = manifest.get("source_nodes")
    roots = manifest.get("build_sequence_roots")
    build_sequence = manifest.get("build_sequence")
    strata = manifest.get("build_strata")
    repositories = manifest.get("repositories")
    require(isinstance(nodes, dict) and isinstance(roots, list) and
            isinstance(build_sequence, list) and isinstance(strata, list) and
            isinstance(repositories, dict), "manifest continuation inputs are malformed")

    header_hashes = MANIFEST_HEADER_RE.findall(source)
    require(header_hashes == [manifest_record["sha256"]],
            "continuation manifest header is absent, duplicated, or stale")

    source_head = git_text(source_root, "rev-parse", "HEAD")
    source_status = git_text(source_root, "status", "--porcelain=v1")
    source_repository = repositories.get("flyspeck")
    require(isinstance(source_repository, dict), "missing Flyspeck repository record")
    require(source_head == source_repository.get("commit"),
            "Flyspeck source repository commit mismatch")
    require(source_status == "", "Flyspeck source repository is not clean")

    relative_inputs = [
        str(path.relative_to(candle_root))
        for path in (manifest_path, runtime_path)
    ]
    candle_status = git_text(
        candle_root, "status", "--porcelain=v1", "--", *relative_inputs,
    )
    require(candle_status == "", "manifest or runtime has uncommitted changes")
    candle_head = git_text(candle_root, "rev-parse", "HEAD")

    records = parse_actions(source)
    expected_indices = list(range(args.expected_start, args.expected_end + 1))
    require([record["index"] for record in records] == expected_indices,
            "action comment indices are not the exact expected range")
    require([record["commit_index"] for record in records] == expected_indices,
            "action commit indices are not the exact expected range")
    require(args.expected_end < len(roots) == len(build_sequence),
            "manifest action range mismatch")

    initial_gates = list(INITIAL_GATE_RE.finditer(source))
    require(len(initial_gates) == 1 and
            int(initial_gates[0].group("count")) == args.expected_start,
            "clean predecessor-state gate is absent, duplicated, or stale")

    runtime = load_runtime(runtime_path)
    ledger_keys = runtime.derive_action_ledger_delta_keys(
        manifest, args.expected_end + 1,
    )
    used_source_keys: set[str] = set()
    action_projection = []
    for record in records:
        index = record["index"]
        root = roots[index]
        require(isinstance(root, dict) and root.get("index") == index and
                root.get("status") == "resolved", f"malformed action root: {index}")
        key = root.get("selected")
        node = nodes.get(key)
        require(isinstance(key, str) and isinstance(node, dict),
                f"unbound action source: {index}")
        require(record["key"] == key, f"logical action source mismatch: {index}")
        require(record["target"] == root.get("target") == build_sequence[index],
                f"action target mismatch: {index}")
        require(record["source_sha256"] == node.get("sha256"),
                f"action source SHA-256 mismatch: {index}")
        require(record["identity_basename"] == Path(node["path"]).name and
                record["identity_md5"] == node.get("md5"),
                f"action source identity mismatch: {index}")

        delta, delta_sha256 = expected_ledger_record(runtime, nodes, ledger_keys[index])
        require(ledger_keys[index][0] == key,
                f"outer ledger source mismatch: {index}")
        expected_marker = (
            f"{runtime.ACTION_PREFIX} {args.attempt_nonce} {index:03d} "
            f"{node['sha256']} {delta_sha256}"
        )
        require(record["marker"] == expected_marker,
                f"action marker or ledger delta mismatch: {index}")
        used_source_keys.update(ledger_keys[index])
        action_projection.append({
            "index": index,
            "logical_source": key,
            "target": root["target"],
            "source_sha256": node["sha256"],
            "identity_basename": Path(node["path"]).name,
            "identity_md5": node["md5"],
            "ledger_delta_sha256": delta_sha256,
            "ledger_source_count": len(delta),
        })

    source_records = {}
    for key in sorted(used_source_keys):
        node = nodes[key]
        path, observed = source_record_for_key(
            key, node, candle_root, source_root,
        )
        source_records[key] = {"path": str(path), **observed}

    gates = list(BOUNDARY_GATE_RE.finditer(source))
    gate_by_count = {
        int(match.group("count")): {
            "event_count": int(match.group("count")),
            "success_marker": parse_json_string(match.group("marker"), "gate marker"),
            "failure_message": parse_json_string(match.group("failure"), "gate failure"),
            "offset": match.start(),
        }
        for match in gates
    }
    require(len(gate_by_count) == len(gates), "duplicate continuation boundary gate")
    expected_gate_counts = {
        stratum["end_index"] + 1
        for stratum in strata
        if (isinstance(stratum, dict) and
            args.expected_start <= stratum.get("start_index", -1) and
            stratum.get("end_index", -1) <= args.expected_end)
    }
    require(set(gate_by_count) == expected_gate_counts,
            "continuation stratum gates do not match the manifest partitions")
    for count, gate in gate_by_count.items():
        action = records[count - args.expected_start - 1]
        commit_offset = source.find(action["commit_line"])
        require(commit_offset >= 0 and commit_offset < gate["offset"],
                f"stratum gate precedes its final action: {count - 1}")
        if count <= args.expected_end:
            next_action = records[count - args.expected_start]
            next_offset = source.find(next_action["comment_line"])
            require(gate["offset"] < next_offset,
                    f"stratum gate follows the next action: {count - 1}")
        gate.pop("offset")

    overlay = verify_overlay(
        source, records, nodes, source_root, overlay_root,
        args.expected_existing_overlay_count,
    )

    final_target = manifest.get("final_target")
    require(isinstance(final_target, dict), "missing final target contract")
    final_key = final_target.get("source")
    final_node = nodes.get(final_key)
    require(isinstance(final_key, str) and isinstance(final_node, dict),
            "unbound final target source")
    final_path, final_record = source_record_for_key(
        final_key, final_node, candle_root, source_root,
    )
    final_directive = f"needs {json.dumps(final_node['path'])};;"
    require(source.count(final_directive) == 1,
            "final target directive is absent, duplicated, or stale")
    final_directive_offset = source.index(final_directive)
    require(final_directive_offset > max(match.end() for match in gates),
            "final target is loaded before the action ledger closes")
    final_markers = list(FINAL_MARKER_RE.finditer(source))
    require(len(final_markers) == 1 and
            final_markers[0].start() > final_directive_offset,
            "final success marker is absent, duplicated, or premature")

    projection_sha256 = runtime.canonical_sha256(action_projection)
    return {
        "schema": "candle-flyspeck-continuation-preflight-v1",
        "status": "pass",
        "issued_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "tool": {
            "path": str(Path(__file__).resolve()),
            "record": hash_file(Path(__file__).resolve()),
        },
        "candle": {
            "root": str(candle_root),
            "git_head": candle_head,
            "manifest": {"path": str(manifest_path), **manifest_record},
            "stratum_runtime": {"path": str(runtime_path), **runtime_record},
        },
        "flyspeck": {
            "root": str(source_root),
            "git_head": source_head,
            "tracked_worktree_clean": True,
        },
        "continuation": {
            "path": str(continuation_path),
            "record": continuation_record,
            "attempt_nonce": args.attempt_nonce,
            "start_index": args.expected_start,
            "end_index": args.expected_end,
            "action_count": len(records),
            "action_projection_sha256": projection_sha256,
            "logical_source_count": len(source_records),
            "boundary_gates": [gate_by_count[count] for count in sorted(gate_by_count)],
            "final_success_marker": parse_json_string(
                final_markers[0].group("marker"), "final marker",
            ),
        },
        "overlay": overlay,
        "final_target": {
            "logical_source": final_key,
            "name": final_target.get("name"),
            "statement": final_target.get("statement"),
            "path": str(final_path),
            "record": final_record,
        },
        "checks": {
            "manifest_header": True,
            "source_repository_identity": True,
            "source_bytes": True,
            "action_records": True,
            "action_ledger_deltas": True,
            "clean_predecessor_gate": True,
            "normalization_overlay": True,
            "stratum_gates": True,
            "final_target": True,
        },
    }


def write_json(path: Path, value: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f"{path.name}.tmp.{os.getpid()}")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    os.replace(temporary, path)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("continuation", type=Path)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--runtime", type=Path, default=DEFAULT_RUNTIME)
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--overlay-root", type=Path, required=True)
    parser.add_argument("--expected-start", type=int, required=True)
    parser.add_argument("--expected-end", type=int, required=True)
    parser.add_argument("--attempt-nonce", required=True)
    parser.add_argument("--expected-existing-overlay-count", type=int, required=True)
    parser.add_argument("--output", type=Path)
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        receipt = verify(args)
        if args.output is not None:
            write_json(args.output, receipt)
        print(json.dumps(receipt, sort_keys=True))
        return 0
    except (PreflightError, OSError, subprocess.SubprocessError) as error:
        print(f"continuation preflight failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
