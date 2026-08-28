#!/usr/bin/env python3
"""Run one authenticated cumulative Flyspeck stratum in compiled Candle.

The input is a materialized plan produced by ``flyspeck_stratum_plan.py``.
Every attempt starts a fresh process, reauthenticates the linked CakeML
artifact and all plan inputs, and writes an authenticated read-only runtime
snapshot plus an append-only-by-convention attempt directory.  A
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
import resource
import secrets
import shutil
import signal
import subprocess
from pathlib import Path
from typing import Any

import cakeml_artifact_provenance
import flyspeck_stratum_plan


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
    expected_materialization = {
        "schema": 1,
        "claim": "host path and validation receipt only; not S2/S3 evidence",
        "plan_sha256": plan_hash["sha256"],
        "planner_source_sha256": hash_file(
            candle_root / "candle/flyspeck_stratum_plan.py"
        )["sha256"],
        "host_roots": {
            "candle": str(candle_root),
            "flyspeck": str(flyspeck_root),
            "normalization_overlay": str(overlay_root),
            "generated_inputs": str(generated_root),
        },
        "validated_counts": {
            "source_nodes": len(derived_validated["source_bindings"]),
            "normalization_outputs": len(derived_validated["normalization_bindings"]),
            "generated_inputs": len(derived_validated["generated_bindings"]),
            "actions": len(derived_audit["actions"]),
            "boundaries": len(derived_plan["boundaries"]),
        },
    }
    require(materialization == expected_materialization,
            "stored host materialization differs from independent reconstruction")
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
    certificate_by_basename: dict[str, dict[str, str]] = {}
    for item in generated_runtime:
        if item["class"] not in ("lp-certificate", "lp-certificate-prepared"):
            continue
        basename = Path(item["relative"]).name
        require(basename not in certificate_by_basename,
                f"duplicate LP certificate basename: {basename}")
        certificate_by_basename[basename] = item
    require(list(certificate_by_basename) == expected_certificate_basenames,
            "LP certificate basename order/set mismatch")
    lp_certificate_runtime = [
        certificate_by_basename[basename] for basename in expected_certificate_basenames
    ]
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
        "harness_records": harness_records,
        "boundary": boundary,
        "actions": action_runtime,
        "source_runtime": source_runtime,
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
                f"{actions[action_index]['source_sha256']}"
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
    nonce: str,
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
        marker = (
            f"{FINGERPRINT_SUCCESS_MARKER} {nonce} {boundary_id} "
            f"{len(theorem_names)}"
        )
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
        f"let candle_flyspeck_stratum_attempt_nonce = {string(prepared['attempt_nonce'])};;",
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
    nonce: str,
    theorem_names: list[str] | None = None,
) -> None:
    theorem_names = theorem_names or []
    lines = log.splitlines()

    def exact_position(marker: str, label: str) -> int:
        positions = [index for index, line in enumerate(lines) if line == marker]
        require(len(positions) == 1, f"missing or duplicate {label} marker")
        return positions[0]

    preflight = f"{PREFLIGHT_MARKER} {nonce}"
    positions = [exact_position(preflight, "stratum preflight")]
    for index, action in enumerate(actions):
        marker = f"{ACTION_PREFIX} {nonce} {index:03d} {action['source_sha256']}"
        positions.append(exact_position(marker, f"action {index}"))
    final = f"{SUCCESS_MARKER} {nonce} {boundary_id} {len(actions)}"
    positions.append(exact_position(final, "boundary success"))
    if theorem_names:
        fingerprint_final = (
            f"{FINGERPRINT_SUCCESS_MARKER} {nonce} {boundary_id} {len(theorem_names)}"
        )
        positions.append(exact_position(fingerprint_final, "fingerprint success"))
    require(positions == sorted(positions), "stratum markers are out of order")
    require(not re.search(r"^(?:ERROR|EXCEPTION):|Parsing failed", log, re.MULTILINE),
            "compiled stratum log contains a top-level error")


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


def create_runtime_snapshot(
    output_root: Path,
    candle_root: Path,
    prepared: dict[str, Any],
    linked: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Copy every runtime-consumed byte into one disjoint read-only tree."""
    snapshot_root = output_root / "snapshot"
    candle_snapshot = snapshot_root / "candle"
    flyspeck_snapshot = snapshot_root / "flyspeck"
    overlay_snapshot = snapshot_root / "overlay"
    generated_snapshot = snapshot_root / "generated"
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

    for binding in prepared["source_runtime"]:
        destination_root = candle_snapshot if binding["repository"] == "candle" else flyspeck_snapshot
        record = snapshot_copy(
            Path(binding["absolute"]), destination_root, binding["path"], binding,
        )
        add_record(binding["repository"], f"source:{binding['repository']}", record)

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
        "normalized_runtime": normalized_runtime,
        "generated_runtime": generated_runtime,
        "lp_certificate_runtime": lp_certificate_runtime,
        "process_runtime": process_runtime,
        "cake_runtime": cake_snapshot,
        "prefix_path": prefix_snapshot / prefix_relative,
    }
    records = list(records_by_path.values())
    snapshot_record = {
        "schema": 1,
        "kind": "candle-flyspeck-attempt-local-runtime-snapshot",
        "file_count": len(records),
        "ordered_file_sha256": canonical_sha256(records),
        "files": records,
        "roots": {
            "candle": str(candle_snapshot),
            "flyspeck": str(flyspeck_snapshot),
            "normalization_overlay": str(overlay_snapshot),
            "generated_inputs": str(generated_snapshot),
        },
        "files_read_only": True,
        "directories_read_only": True,
    }
    return runtime, snapshot_record


def validate_runtime_snapshot(snapshot: dict[str, Any], output_root: Path) -> None:
    snapshot_root = output_root / "snapshot"
    records = snapshot.get("files")
    require(isinstance(records, list), "missing snapshot file records")
    require(snapshot.get("file_count") == len(records), "snapshot file count mismatch")
    require(canonical_sha256(records) == snapshot.get("ordered_file_sha256"),
            "snapshot ordered-file digest mismatch")
    for record in records:
        path = snapshot_root / record["path"]
        validate_file(path, record,
                      f"runtime snapshot {record['path']}")
        require(path.stat().st_mode & 0o222 == 0,
                f"runtime snapshot file is writable: {record['path']}")
    for directory in [snapshot_root, *(
        path for path in snapshot_root.rglob("*") if path.is_dir()
    )]:
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
    require(0 < max_cpu_seconds <= 172800,
            "CPU-time limit must be between 1 and 172800 seconds")
    require(0 < max_address_space_gib <= 56,
            "address-space limit must be between 1 and 56 GiB")
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
    runtime_prepared, snapshot_record = create_runtime_snapshot(
        output_root, candle_root, prepared, linked,
    )
    snapshot_record_path = output_root / "snapshot.json"
    atomic_write_json(snapshot_record_path, snapshot_record)

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
    write_config(
        config_path, runtime_candle_root, runtime_prepared,
        program_path, program_record["md5"],
    )
    theorem_names = fingerprint_requests(boundary_id)
    write_postlude(
        postlude_path, runtime_candle_root, boundary_id, theorem_names, nonce,
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

    started = utc_now()
    attempt = {
        "schema": 1,
        "kind": "candle-flyspeck-compiled-stratum-attempt",
        "claim": "compiled cumulative source-action attempt; not S2/S3 without semantic fingerprints",
        "state": "running",
        "started_utc": started,
        "boundary_id": boundary_id,
        "attempt_nonce": nonce,
        "action_count": len(prepared["actions"]),
        "timeout_seconds": timeout_seconds,
        "resource_limits": {
            "cpu_seconds": max_cpu_seconds,
            "address_space_bytes": max_address_space_gib * GIB,
            "output_file_bytes": max_output_file_gib * GIB,
        },
        "fresh_process_replay_from_action_zero": True,
        "process_state_checkpoint": None,
        "inputs": {
            "plan": prepared["plan_record"],
            "host_materialization": prepared["materialization_record"],
            "manifest": prepared["manifest_record"],
            "linked_provenance": prepared["linked_record"],
            "runtime_snapshot": hash_file(snapshot_record_path),
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
    atomic_write_json(attempt_path, attempt)

    command = ["/usr/bin/time", "-v", str(runtime_prepared["cake_runtime"]), "--candle"]
    timed_out = False
    exit_code: int | None = None
    execution_error: BaseException | None = None
    process: subprocess.Popen[bytes] | None = None
    previous_sigterm = signal.getsignal(signal.SIGTERM)
    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)

    def interrupted(signum: int, _frame: Any) -> None:
        raise InterruptedError(f"compiled stratum interrupted by signal {signum}")

    signal.signal(signal.SIGTERM, interrupted)
    try:
        with stdin_path.open("rb") as stdin, log_path.open("wb") as log:
            process = subprocess.Popen(
                command, cwd=runtime_candle_root, stdin=stdin, stdout=log,
                stderr=subprocess.STDOUT, start_new_session=True,
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
        signal.signal(signal.SIGTERM, previous_sigterm)
        if process is not None and process.poll() is None:
            exit_code = terminate_process_group(process)

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
    validation_error: str | None = None
    fingerprints: dict[str, Any] | None = None
    postflight_reauthenticated = False
    try:
        require(execution_error is None,
                f"compiled stratum execution failed: {execution_error}")
        require(not timed_out, "compiled stratum attempt timed out")
        require(exit_code == 0, f"compiled stratum process exited {exit_code}")
        post_linked = cakeml_artifact_provenance.validate_linked_record(candle_root)
        validate_plan(candle_root, post_linked, plan_root, boundary_id)
        validate_file(snapshot_record_path, attempt["inputs"]["runtime_snapshot"],
                      "runtime snapshot record")
        validate_runtime_snapshot(snapshot_record, output_root)
        for label, path in (
            ("instrumented_prefix", program_path),
            ("runtime_config", config_path),
            ("stdin", stdin_path),
            ("postlude", postlude_path),
        ):
            validate_file(path, control_records[label], f"attempt control {label}")
        postflight_reauthenticated = True
        validate_log(
            log_path.read_text(encoding="utf-8", errors="replace"),
            prepared["actions"], boundary_id, nonce, theorem_names,
        )
        fingerprints = parse_fingerprints(
            log_path.read_text(encoding="utf-8", errors="replace"),
            theorem_names, runtime_candle_root / FINGERPRINT_RELATIVE,
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
        "child_resources": child_resources,
        "log": log_record,
        "action_markers_validated": len(prepared["actions"]) if validation_error is None else 0,
        "semantic_fingerprints": fingerprints,
        "s2_s3_evidence": False,
        "validation_error": validation_error,
        "postflight_reauthenticated": postflight_reauthenticated,
    }
    atomic_write_json(receipt_path, receipt)
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
        f"compiled stratum PASS: {receipt['boundary_id']} "
        f"({receipt['action_count']} actions); not S2/S3 without semantic fingerprints"
    )


if __name__ == "__main__":
    main()
