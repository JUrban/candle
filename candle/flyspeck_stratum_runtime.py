#!/usr/bin/env python3
"""Run one authenticated cumulative Flyspeck stratum in compiled Candle.

The input is a materialized plan produced by ``flyspeck_stratum_plan.py``.
Every attempt starts a fresh process, reauthenticates the linked CakeML
artifact and all plan inputs, and writes an immutable attempt directory.  A
successful receipt proves only that the selected source actions completed; it
does not become S2/S3 evidence without the separately specified semantic
fingerprints.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import re
import signal
import subprocess
from pathlib import Path
from typing import Any

import cakeml_artifact_provenance


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
ACTION_PREFIX = "CANDLE_FLYSPECK_STRATUM_ACTION_OK"
PREFLIGHT_MARKER = "CANDLE_FLYSPECK_STRATUM_PREFLIGHT_OK"
SUCCESS_MARKER = "CANDLE_FLYSPECK_STRATUM_BOUNDARY_OK"
FINGERPRINT_MARKER = "CANDLE_FINGERPRINT_V1"
FINGERPRINT_SUCCESS_MARKER = "CANDLE_FLYSPECK_STRATUM_FINGERPRINTS_OK"
SAFE_VALUE_PATH = re.compile(r"^[A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9_']*)*$")


class ContractError(ValueError):
    """An authenticated runtime input or execution invariant did not match."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ContractError(message)


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


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
            ["git", "-C", str(root), *arguments], check=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
        ).stdout.strip()
    except subprocess.CalledProcessError as error:
        raise ContractError(f"git check failed for {root}: {error.stderr.strip()}") from error


def validate_clean_descendant(root: Path, ancestor: str, label: str) -> str:
    head = git_output(root, "rev-parse", "HEAD")
    result = subprocess.run(
        ["git", "-C", str(root), "merge-base", "--is-ancestor", ancestor, head],
        stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,
    )
    require(result.returncode == 0, f"{label} head is not descended from {ancestor}")
    require(not git_output(root, "status", "--porcelain", "--untracked-files=all"),
            f"{label} root is not clean")
    return head


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


def validate_plan(
    candle_root: Path,
    linked_record: dict[str, Any],
    plan_root: Path,
    boundary_id: str,
) -> dict[str, Any]:
    """Reauthenticate a host plan and return exact runtime material."""
    plan_path = plan_root / "plan.json"
    materialization_path = plan_root / "host-materialization.json"
    plan = load_object(plan_path, "stratum plan")
    materialization = load_object(materialization_path, "host materialization")
    require(plan.get("schema") == 1, "unsupported stratum plan schema")
    require(plan.get("kind") == "candle-flyspeck-cumulative-stratum-plan",
            "wrong stratum plan kind")
    require("not Candle execution" in plan.get("claim", ""), "stratum plan claim drift")
    plan_hash = hash_file(plan_path)
    require(materialization.get("schema") == 1, "unsupported materialization schema")
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
    candle_head = validate_clean_descendant(
        candle_root, repositories["candle_materialization_head"], "Candle",
    )
    require(candle_head == linked_record.get("candle_commit"),
            "linked executable does not bind the current Candle head")
    validate_clean_exact(flyspeck_root, repositories["flyspeck_commit"], "Flyspeck")

    manifest_path = candle_root / MANIFEST_RELATIVE
    manifest = load_object(manifest_path, "Flyspeck manifest")
    require(hash_file(manifest_path)["sha256"] == plan.get("manifest_sha256"),
            "runtime manifest digest mismatch")
    require(manifest["repositories"]["flyspeck"]["commit"] == repositories["flyspeck_commit"],
            "runtime manifest Flyspeck pin mismatch")

    planner_source = candle_root / "candle/flyspeck_stratum_plan.py"
    require(hash_file(planner_source)["sha256"] == materialization.get("planner_source_sha256"),
            "planner source digest drift after materialization")

    source_graph = plan.get("source_graph")
    require(isinstance(source_graph, dict), "missing source graph")
    source_bindings = source_graph.get("bindings")
    require(isinstance(source_bindings, list), "missing source bindings")
    require(source_graph.get("entry_count") == len(source_bindings) == 400,
            "source binding count mismatch")
    require(canonical_sha256(source_bindings) == source_graph.get("ordered_binding_sha256"),
            "source binding order digest mismatch")
    source_by_key: dict[str, dict[str, Any]] = {}
    for binding in source_bindings:
        key = binding.get("key")
        require(isinstance(key, str) and key not in source_by_key, "duplicate source binding")
        validate_file(resolve_source(binding, candle_root, flyspeck_root), binding,
                      f"source binding {key}")
        source_by_key[key] = binding

    digest_contract = manifest.get("source_digest_contract")
    require(isinstance(digest_contract, dict), "missing source digest contract")
    require(digest_contract.get("entry_count") == 399, "source digest count drift")
    validate_file(candle_root / SOURCE_DIGEST_RELATIVE, {
        "sha256": digest_contract["generated_source_sha256"],
        "md5": digest_contract["generated_source_md5"],
    }, "source digest program")

    normalization = plan.get("normalization_overlay")
    require(isinstance(normalization, dict), "missing normalization overlay")
    normalization_bindings = normalization.get("bindings")
    require(isinstance(normalization_bindings, list), "missing normalization bindings")
    require(normalization.get("entry_count") == len(normalization_bindings) == 16,
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
            "original": str(source), "output": str(output), "md5": binding["normalized_md5"],
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
        generated_runtime.append({"path": str(source), "md5": observed["md5"]})
    validate_file(generated_root / GENERATED_RECEIPT, {
        "sha256": generated["receipt_sha256"],
    }, "generated-input receipt")

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
        process_runtime.append({"path": str(source), "md5": observed["md5"]})

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
    selected = [entry for entry in boundaries if entry.get("boundary_id") == boundary_id]
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

    action_runtime = []
    for action in actions[:count]:
        source = source_by_key[action["selected_source"]]
        action_runtime.append({
            **action,
            "identity_basename": Path(source["path"]).name,
            "identity_md5": source["md5"],
        })

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
        "boundary": boundary,
        "actions": action_runtime,
        "normalized_runtime": normalized_runtime,
        "generated_runtime": generated_runtime,
        "process_runtime": process_runtime,
    }


def ocaml_string(value: str) -> str:
    require(all(32 <= ord(char) < 127 for char in value), "unsafe non-ASCII runtime string")
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def instrument_prefix(prefix: bytes, actions: list[dict[str, Any]]) -> bytes:
    """Insert one output-only completion phrase after every exact action."""
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
                f"{ACTION_PREFIX} {action_index:03d} "
                f"{actions[action_index]['source_sha256']}"
            )
            output.append(f"print_endline {ocaml_string(marker)};;\n")
            action_index += 1
    require(action_index == len(actions), "prefix contains too few actions")
    return "".join(output).encode()


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


def write_postlude(
    path: Path,
    candle_root: Path,
    boundary_id: str,
    theorem_names: list[str],
) -> None:
    lines = ["(* Generated theorem-observation postlude; not an approval record. *)"]
    if boundary_id.startswith("07-"):
        lines.append(f"#use {ocaml_string(str(candle_root / L2_TARGET_RELATIVE))};;")
    if theorem_names:
        lines.append(f"#use {ocaml_string(str(candle_root / FINGERPRINT_RELATIVE))};;")
        for name in theorem_names:
            require(SAFE_VALUE_PATH.fullmatch(name) is not None,
                    f"unsafe theorem value path: {name}")
            lines.append(f"candle_s1_emit_fingerprint {ocaml_string(name)} {name};;")
        marker = f"{FINGERPRINT_SUCCESS_MARKER} {boundary_id} {len(theorem_names)}"
        lines.append(f"print_endline {ocaml_string(marker)};;")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_config(
    path: Path,
    candle_root: Path,
    prepared: dict[str, Any],
    execution_program: Path,
    execution_md5: str,
) -> None:
    def string(value: Path | str) -> str:
        return ocaml_string(str(value))

    lines = [
        "(* Generated by flyspeck_stratum_runtime.py; do not edit. *)",
        f"let candle_hollight_root = {string(candle_root)};;",
        f"let candle_flyspeck_root = {string(prepared['flyspeck_root'])};;",
        f"let candle_flyspeck_overlay_root = {string(prepared['overlay_root'])};;",
        f"let candle_flyspeck_generated_root = {string(prepared['generated_root'])};;",
        'let candle_flyspeck_build_mode = "stratum-runtime";;',
        f"let candle_flyspeck_stratum_boundary = {string(prepared['boundary']['boundary_id'])};;",
        f"let candle_flyspeck_stratum_action_count = {len(prepared['actions'])};;",
        f"let candle_flyspeck_stratum_program = {string(execution_program)};;",
        f"let candle_flyspeck_stratum_program_md5 = {string(execution_md5)};;",
        "let candle_flyspeck_stratum_normalized_sources = [",
    ]
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
        "",
    ])
    path.write_text("\n".join(lines), encoding="utf-8")


def parse_fingerprints(log: str, theorem_names: list[str], serializer: Path) -> dict[str, Any]:
    records: dict[str, dict[str, Any]] = {}
    for line in log.splitlines():
        if not line.startswith(FINGERPRINT_MARKER + "\t"):
            continue
        fields = line.split("\t")
        require(len(fields) == 8, f"malformed {FINGERPRINT_MARKER} record")
        (_, name_hex, theorem_hex, hypotheses_hex, conclusion_hex,
         axioms_hex, hypothesis_count, axiom_count) = fields

        def decode(field: str, label: str) -> bytes:
            require(re.fullmatch(r"(?:[0-9a-f]{2})*", field) is not None,
                    f"malformed fingerprint hex: {label}")
            return bytes.fromhex(field)

        try:
            name = decode(name_hex, "name").decode("ascii")
        except UnicodeDecodeError as error:
            raise ContractError("non-ASCII theorem fingerprint name") from error
        require(name not in records, f"duplicate theorem fingerprint: {name}")
        try:
            parsed_hypotheses = int(hypothesis_count)
            parsed_axioms = int(axiom_count)
        except ValueError as error:
            raise ContractError(f"non-numeric fingerprint count: {name}") from error
        record = {
            "name": name,
            "theorem_sha256": hashlib.sha256(decode(theorem_hex, "theorem")).hexdigest(),
            "hypotheses_sha256": hashlib.sha256(
                decode(hypotheses_hex, "hypotheses")
            ).hexdigest(),
            "conclusion_sha256": hashlib.sha256(
                decode(conclusion_hex, "conclusion")
            ).hexdigest(),
            "global_axioms_sha256": hashlib.sha256(
                decode(axioms_hex, "global axioms")
            ).hexdigest(),
            "hypothesis_count": parsed_hypotheses,
            "global_axiom_count": parsed_axioms,
        }
        records[name] = record

    require(list(records) == theorem_names,
            f"fingerprint request mismatch: expected {theorem_names}, got {list(records)}")
    axiom_identities = {
        (record["global_axioms_sha256"], record["global_axiom_count"])
        for record in records.values()
    }
    require(len(axiom_identities) <= 1, "global axiom identity changed between fingerprints")
    for record in records.values():
        require(record["hypothesis_count"] == 0,
                f"unexpected theorem hypotheses: {record['name']}")
        require(record["global_axiom_count"] == 3,
                f"unexpected global axiom count: {record['name']}")
    return {
        "status": "observed_uncompared" if theorem_names else "not_requested",
        "approved_reference_present": False,
        "serializer": {
            "path": FINGERPRINT_RELATIVE.as_posix(),
            "sha256": hash_file(serializer)["sha256"],
        } if theorem_names else None,
        "theorems": [records[name] for name in theorem_names],
    }


def validate_log(
    log: str,
    actions: list[dict[str, Any]],
    boundary_id: str,
    theorem_names: list[str] | None = None,
) -> None:
    theorem_names = theorem_names or []
    require(log.count(PREFLIGHT_MARKER) == 1, "missing or duplicate stratum preflight marker")
    positions = [log.index(PREFLIGHT_MARKER)]
    for index, action in enumerate(actions):
        marker = f"{ACTION_PREFIX} {index:03d} {action['source_sha256']}"
        require(log.count(marker) == 1, f"missing or duplicate action marker: {index}")
        positions.append(log.index(marker))
    final = f"{SUCCESS_MARKER} {boundary_id} {len(actions)}"
    require(log.count(final) == 1, "missing or duplicate boundary success marker")
    positions.append(log.index(final))
    if theorem_names:
        fingerprint_final = (
            f"{FINGERPRINT_SUCCESS_MARKER} {boundary_id} {len(theorem_names)}"
        )
        require(log.count(fingerprint_final) == 1,
                "missing or duplicate fingerprint success marker")
        positions.append(log.index(fingerprint_final))
    require(positions == sorted(positions), "stratum markers are out of order")
    require(not re.search(r"^(?:ERROR|EXCEPTION):|Parsing failed", log, re.MULTILINE),
            "compiled stratum log contains a top-level error")


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat().replace("+00:00", "Z")


def run_attempt(
    candle_script: Path,
    plan_root: Path,
    boundary_id: str,
    output_root: Path,
    timeout_seconds: int,
) -> dict[str, Any]:
    candle_script = candle_script.resolve()
    plan_root = plan_root.resolve()
    output_root = output_root.resolve()
    require(candle_script.is_file() and os.access(candle_script, os.X_OK),
            f"Candle launcher is not executable: {candle_script}")
    candle_root = candle_script.parent

    # This must precede interpretation of the host plan: no runtime attempt is
    # prepared for an unbound or stale executable.
    linked = cakeml_artifact_provenance.validate_linked_record(candle_root)
    prepared = validate_plan(candle_root, linked, plan_root, boundary_id)

    require(timeout_seconds > 0, "timeout must be positive")
    require(not output_root.exists(), f"attempt output already exists: {output_root}")
    require(output_root.parent.is_dir(), f"attempt parent does not exist: {output_root.parent}")
    output_root.mkdir()
    program_path = output_root / "instrumented-prefix.ml"
    config_path = output_root / "runtime-config.ml"
    stdin_path = output_root / "stdin.ml"
    postlude_path = output_root / "postlude.ml"
    log_path = output_root / "candle.log"
    attempt_path = output_root / "attempt.json"
    receipt_path = output_root / "receipt.json"

    program = instrument_prefix(prepared["prefix_path"].read_bytes(), prepared["actions"])
    program_path.write_bytes(program)
    program_record = hash_file(program_path)
    write_config(config_path, candle_root, prepared, program_path, program_record["md5"])
    theorem_names = fingerprint_requests(boundary_id)
    write_postlude(postlude_path, candle_root, boundary_id, theorem_names)
    stdin_path.write_text(
        f"#use {ocaml_string(str(config_path))};;\n"
        f"#use {ocaml_string(str(candle_root / SETUP_RELATIVE))};;\n"
        f"#use {ocaml_string(str(program_path))};;\n"
        f"#use {ocaml_string(str(candle_root / CHECK_RELATIVE))};;\n"
        f"#use {ocaml_string(str(postlude_path))};;\n",
        encoding="utf-8",
    )

    started = utc_now()
    attempt = {
        "schema": 1,
        "kind": "candle-flyspeck-compiled-stratum-attempt",
        "claim": "compiled cumulative source-action attempt; not S2/S3 without semantic fingerprints",
        "state": "running",
        "started_utc": started,
        "boundary_id": boundary_id,
        "action_count": len(prepared["actions"]),
        "timeout_seconds": timeout_seconds,
        "fresh_process_replay_from_action_zero": True,
        "process_state_checkpoint": None,
        "inputs": {
            "plan": prepared["plan_record"],
            "host_materialization": prepared["materialization_record"],
            "manifest": prepared["manifest_record"],
            "linked_provenance": prepared["linked_record"],
            "authenticated_prefix": prepared["prefix_record"],
            "instrumented_prefix": program_record,
            "runtime_config": hash_file(config_path),
            "stdin": hash_file(stdin_path),
            "postlude": hash_file(postlude_path),
            "setup": hash_file(candle_root / SETUP_RELATIVE),
            "check": hash_file(candle_root / CHECK_RELATIVE),
            "fingerprint_serializer": hash_file(candle_root / FINGERPRINT_RELATIVE),
            "l2_target": hash_file(candle_root / L2_TARGET_RELATIVE),
        },
        "repositories": {
            "candle": prepared["candle_head"],
            "flyspeck": prepared["plan"]["repositories"]["flyspeck_commit"],
        },
    }
    attempt_path.write_bytes(json_bytes(attempt))

    command = ["/usr/bin/time", "-v", str(candle_script)]
    timed_out = False
    exit_code: int | None = None
    with stdin_path.open("rb") as stdin, log_path.open("wb") as log:
        process = subprocess.Popen(
            command, cwd=candle_root, stdin=stdin, stdout=log,
            stderr=subprocess.STDOUT, start_new_session=True,
        )
        try:
            exit_code = process.wait(timeout=timeout_seconds)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(process.pid, signal.SIGTERM)
            try:
                exit_code = process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                exit_code = process.wait()

    finished = utc_now()
    log_record = hash_file(log_path)
    validation_error: str | None = None
    fingerprints: dict[str, Any] | None = None
    try:
        require(not timed_out, "compiled stratum attempt timed out")
        require(exit_code == 0, f"compiled stratum process exited {exit_code}")
        validate_log(
            log_path.read_text(encoding="utf-8", errors="replace"),
            prepared["actions"], boundary_id, theorem_names,
        )
        fingerprints = parse_fingerprints(
            log_path.read_text(encoding="utf-8", errors="replace"),
            theorem_names, candle_root / FINGERPRINT_RELATIVE,
        )
    except ContractError as error:
        validation_error = str(error)

    receipt = {
        **attempt,
        "state": "completed" if validation_error is None else "failed",
        "finished_utc": finished,
        "timed_out": timed_out,
        "exit_code": exit_code,
        "command": command,
        "log": log_record,
        "action_markers_validated": len(prepared["actions"]) if validation_error is None else 0,
        "semantic_fingerprints": fingerprints,
        "s2_s3_evidence": False,
        "validation_error": validation_error,
    }
    receipt_path.write_bytes(json_bytes(receipt))
    if validation_error is not None:
        raise ContractError(validation_error)
    return receipt


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candle-script", type=Path, required=True)
    parser.add_argument("--plan-root", type=Path, required=True)
    parser.add_argument("--boundary", required=True, metavar="BOUNDARY_ID")
    parser.add_argument("--write", type=Path, required=True, metavar="ATTEMPT_ROOT")
    parser.add_argument("--timeout", type=int, default=86400, metavar="SECONDS")
    arguments = parser.parse_args()
    receipt = run_attempt(
        arguments.candle_script, arguments.plan_root, arguments.boundary,
        arguments.write, arguments.timeout,
    )
    print(
        f"compiled stratum PASS: {receipt['boundary_id']} "
        f"({receipt['action_count']} actions); not S2/S3 without semantic fingerprints"
    )


if __name__ == "__main__":
    main()
