#!/usr/bin/env python3
"""Materialize authenticated cumulative Flyspeck stratum prefixes.

This is a host-side scheduling tool.  It does not run Candle and its output is
not S2/S3 evidence.  A boundary can only be revisited by replaying its
cumulative prefix from action zero in a fresh process; this tool neither saves
nor restores CakeML process state.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any


MANIFEST_PATH = "candle/flyspeck_manifest.json"
FULL_BUILD_PATH = "candle/flyspeck_full_build.ml"
NORMALIZATION_CONTRACT_PATH = "candle/flyspeck_normalizations.json"
NORMALIZATION_RECEIPT = "flyspeck_normalization_receipt.json"
GENERATED_CONTRACT_PATH = "candle/flyspeck_lp_archive_contract.json"
GENERATED_RECEIPT = "flyspeck_lp_archive_receipt.json"
FRESH_PUBLICATION = {
    "policy": "fresh-root-renameat2-noreplace",
    "failed_staging": "retained",
    "concurrent_same_uid_mutation": "trusted",
}
PREPARED_INPUT_CLASS = "lp-certificate-prepared"
CHUNK_BYTES = 1024 * 1024
GIT_ENVIRONMENT = {
    "LC_ALL": "C",
    "PATH": "/usr/bin:/bin",
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


class ContractError(ValueError):
    """An authenticated planning input or invariant did not match."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ContractError(message)


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def hash_file(path: Path) -> tuple[int, str, str]:
    sha256 = hashlib.sha256()
    md5 = hashlib.md5(usedforsecurity=False)
    size = 0
    with path.open("rb") as source:
        while block := source.read(CHUNK_BYTES):
            size += len(block)
            sha256.update(block)
            md5.update(block)
    return size, sha256.hexdigest(), md5.hexdigest()


def sha256_file(path: Path) -> str:
    return hash_file(path)[1]


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ContractError(f"cannot read JSON object {path}: {error}") from error
    require(isinstance(value, dict), f"expected JSON object: {path}")
    return value


def git_output(root: Path, *arguments: str) -> str:
    try:
        return subprocess.run(
            ["/usr/bin/git", *GIT_OPTIONS, "-C", str(root), *arguments],
            check=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            env=GIT_ENVIRONMENT,
        ).stdout.strip()
    except subprocess.CalledProcessError as error:
        raise ContractError(f"git check failed for {root}: {error.stderr.strip()}") from error


def validate_clean_git_root(root: Path, expected_head: str, label: str) -> None:
    require(root.is_dir(), f"missing {label} root: {root}")
    observed_head = git_output(root, "rev-parse", "HEAD")
    require(
        observed_head == expected_head,
        f"{label} revision mismatch: expected {expected_head}, got {observed_head}",
    )
    status = git_output(root, "status", "--porcelain", "--untracked-files=all")
    require(not status, f"{label} root is not clean")


def validate_clean_git_descendant(root: Path, expected_base: str, label: str) -> str:
    """Require a clean tree descended from the pinned manifest integration base."""
    require(root.is_dir(), f"missing {label} root: {root}")
    observed_head = git_output(root, "rev-parse", "HEAD")
    result = subprocess.run(
        ["/usr/bin/git", *GIT_OPTIONS, "-C", str(root), "merge-base",
         "--is-ancestor", expected_base, observed_head],
        stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,
        env=GIT_ENVIRONMENT,
    )
    require(
        result.returncode == 0,
        f"{label} head {observed_head} is not descended from integration base {expected_base}",
    )
    status = git_output(root, "status", "--porcelain", "--untracked-files=all")
    require(not status, f"{label} root is not clean")
    return observed_head


def validate_record(path: Path, record: dict[str, Any], label: str) -> None:
    require(path.is_file() and not path.is_symlink(), f"missing ordinary {label}: {path}")
    size, sha256, md5 = hash_file(path)
    require(size == record["bytes"], f"{label} byte-count mismatch: {path}")
    require(sha256 == record["sha256"], f"{label} SHA-256 mismatch: {path}")
    if "md5" in record:
        require(md5 == record["md5"], f"{label} MD5 mismatch: {path}")


def action_marker(index: int, root: dict[str, Any], node: dict[str, Any]) -> str:
    marker = f"(* {index:03d} selected={root['selected']} sha256={node['sha256']}"
    normalization = node.get("execution_normalization")
    if isinstance(normalization, dict):
        marker += (
            f" normalization={normalization['id']} "
            f"normalized_sha256={normalization['normalized_sha256']}"
        )
    return marker + " *)"


def audit_manifest(candle_root: Path) -> dict[str, Any]:
    """Check the static manifest/driver contract and derive ordered actions."""
    manifest_path = candle_root / MANIFEST_PATH
    manifest = load_json(manifest_path)
    require(manifest.get("schema") == 1, "unsupported Flyspeck manifest schema")
    require(manifest.get("build_mode") == "full", "manifest is not a full build")
    require(
        manifest.get("build_strata_policy") ==
        "contiguous operational checkpoint partitions in authoritative load order; "
        "labels do not imply mathematical dependency isolation",
        "build stratum policy drift",
    )

    sequence = manifest.get("build_sequence")
    roots = manifest.get("build_sequence_roots")
    nodes = manifest.get("source_nodes")
    strata = manifest.get("build_strata")
    require(isinstance(sequence, list), "missing build sequence")
    require(isinstance(roots, list), "missing build roots")
    require(isinstance(nodes, dict), "missing source nodes")
    require(isinstance(strata, list) and strata, "missing build strata")
    require(len(sequence) == manifest.get("build_sequence_count") == 297, "build count drift")
    require(len(roots) == len(sequence), "root count drift")

    stratum_for_index: dict[int, str] = {}
    expected_index = 0
    for stratum in strata:
        start = stratum.get("start_index")
        end = stratum.get("end_index")
        name = stratum.get("name")
        require(isinstance(start, int) and isinstance(end, int), f"invalid stratum range: {name}")
        require(start == expected_index and end >= start, f"non-contiguous stratum: {name}")
        require(end < len(sequence), f"stratum exceeds action sequence: {name}")
        require(stratum.get("entry_count") == end - start + 1, f"stratum count drift: {name}")
        require(stratum.get("first") == sequence[start], f"stratum first action drift: {name}")
        require(stratum.get("last") == sequence[end], f"stratum last action drift: {name}")
        rows = []
        for index in range(start, end + 1):
            root = roots[index]
            require(root.get("index") == index, f"root index drift: {index}")
            require(root.get("target") == sequence[index], f"root target drift: {index}")
            require(root.get("status") == "resolved", f"unresolved build root: {index}")
            selected = root.get("selected")
            require(isinstance(selected, str) and selected in nodes, f"unknown selected root: {index}")
            rows.append({
                "index": index,
                "target": sequence[index],
                "selected": selected,
                "sha256": nodes[selected]["sha256"],
            })
            require(index not in stratum_for_index, f"stratum overlap: {index}")
            stratum_for_index[index] = name
        require(
            canonical_sha256(rows) == stratum.get("ordered_root_sha256"),
            f"ordered stratum digest drift: {name}",
        )
        expected_index = end + 1
    require(expected_index == len(sequence), "strata do not cover full action sequence")

    contract = manifest.get("static_full_build_contract")
    require(isinstance(contract, dict), "missing static full-build contract")
    require(contract.get("directive") == "#flyspeck_needs", "loader directive drift")
    require(contract.get("entry_count") == len(sequence), "driver entry count drift")
    require(
        canonical_sha256(sequence) == contract.get("ordered_target_sha256"),
        "ordered target digest drift",
    )
    driver_path = candle_root / FULL_BUILD_PATH
    require(driver_path.is_file() and not driver_path.is_symlink(), "missing ordinary full driver")
    driver = driver_path.read_bytes()
    require(hashlib.sha256(driver).hexdigest() == contract.get("generated_source_sha256"),
            "full driver SHA-256 mismatch")
    require(hashlib.md5(driver, usedforsecurity=False).hexdigest() == contract.get("generated_source_md5"),
            "full driver MD5 mismatch")

    lines = driver.splitlines(keepends=True)
    directive_prefix = b"#flyspeck_needs "
    offsets: list[int] = []
    targets: list[str] = []
    previous = b""
    consumed = 0
    for line in lines:
        consumed += len(line)
        if line.startswith(directive_prefix):
            body = line.rstrip(b"\r\n")
            require(body.endswith(b";;"), "malformed full-driver directive")
            try:
                target = json.loads(body[len(directive_prefix):-2].decode("utf-8"))
            except (UnicodeDecodeError, json.JSONDecodeError) as error:
                raise ContractError("malformed full-driver target literal") from error
            index = len(targets)
            require(index < len(roots), "too many full-driver actions")
            expected_marker = action_marker(index, roots[index], nodes[roots[index]["selected"]]).encode()
            require(previous.rstrip(b"\r\n") == expected_marker, f"full-driver marker drift: {index}")
            targets.append(target)
            offsets.append(consumed)
        previous = line
    require(targets == sequence, "full-driver action order drift")

    actions: list[dict[str, Any]] = []
    for index, (target, root) in enumerate(zip(sequence, roots, strict=True)):
        selected = root["selected"]
        node = nodes[selected]
        action = {
            "index": index,
            "stratum": stratum_for_index[index],
            "target": target,
            "selected_source": selected,
            "source_bytes": node["bytes"],
            "source_md5": node["md5"],
            "source_sha256": node["sha256"],
        }
        normalization = node.get("execution_normalization")
        if isinstance(normalization, dict):
            action["execution_normalization"] = {
                key: normalization[key] for key in (
                    "id", "kind", "normalized_bytes", "normalized_md5",
                    "normalized_sha256", "operation_count",
                )
            }
        actions.append(action)
    return {
        "manifest": manifest,
        "manifest_sha256": sha256_file(manifest_path),
        "driver": driver,
        "action_offsets": offsets,
        "actions": actions,
        "strata": strata,
    }


def validate_inputs(
    candle_root: Path,
    expected_candle_base: str,
    flyspeck_root: Path,
    overlay_root: Path,
    generated_root: Path,
    audit: dict[str, Any],
) -> dict[str, Any]:
    """Authenticate every source node, normalized output, and generated input."""
    manifest = audit["manifest"]
    expected_flyspeck = manifest["repositories"]["flyspeck"]["commit"]
    candle_head = validate_clean_git_descendant(candle_root, expected_candle_base, "Candle")
    validate_clean_git_root(flyspeck_root, expected_flyspeck, "Flyspeck")

    source_bindings: list[dict[str, Any]] = []
    for key, record in sorted(manifest["source_nodes"].items()):
        repository = record.get("repository")
        require(repository in ("candle", "flyspeck"), f"unknown source repository: {key}")
        root = candle_root if repository == "candle" else flyspeck_root
        validate_record(root / record["path"], record, f"source node {key}")
        binding = {
            field: record[field] for field in ("repository", "path", "bytes", "md5", "sha256")
        }
        binding["key"] = key
        normalization = record.get("execution_normalization")
        if isinstance(normalization, dict):
            binding["execution_normalization"] = {
                field: normalization[field] for field in (
                    "id", "kind", "normalized_bytes", "normalized_md5",
                    "normalized_sha256", "operation_count",
                )
            }
        source_bindings.append(binding)

    normalization = manifest["source_normalization_contract"]
    normalization_contract = candle_root / NORMALIZATION_CONTRACT_PATH
    require(
        sha256_file(normalization_contract) == normalization["contract_sha256"],
        "normalization contract digest mismatch",
    )
    normalization_receipt_path = overlay_root / NORMALIZATION_RECEIPT
    receipt = load_json(normalization_receipt_path)
    require(receipt.get("schema") == 3, "unsupported normalization receipt schema")
    require(receipt.get("publication") == FRESH_PUBLICATION,
            "normalization publication contract mismatch")
    require(receipt.get("flyspeck_commit") == expected_flyspeck, "overlay Flyspeck pin mismatch")
    require(receipt.get("contract_sha256") == normalization["contract_sha256"],
            "overlay normalization contract mismatch")
    contract_entries = {entry["path"]: entry for entry in normalization["entries"]}
    receipt_entries = {entry["path"]: entry for entry in receipt.get("entries", [])}
    require(receipt_entries.keys() == contract_entries.keys(), "overlay entry-set mismatch")
    normalization_bindings: list[dict[str, Any]] = []
    for relative, record in sorted(contract_entries.items()):
        observed = receipt_entries[relative]
        for field in ("id", "normalized_bytes", "normalized_md5", "normalized_sha256"):
            require(observed.get(field) == record[field], f"overlay receipt {field} mismatch: {relative}")
        validate_record(overlay_root / relative, {
            "bytes": record["normalized_bytes"],
            "sha256": record["normalized_sha256"],
            "md5": record["normalized_md5"],
        }, f"normalized source {relative}")
        normalization_bindings.append({
            field: record[field] for field in (
                "id", "path", "source_key", "source_md5", "source_sha256",
                "normalized_bytes", "normalized_md5", "normalized_sha256",
                "operation_count",
            )
        })

    generated_contract_path = candle_root / GENERATED_CONTRACT_PATH
    generated_contract_sha256 = sha256_file(generated_contract_path)
    prep_contract = manifest["lp_archive_preparation_contract"]
    require(
        generated_contract_sha256 == prep_contract["contract_sha256"],
        "generated-input contract digest mismatch",
    )
    generated_receipt_path = generated_root / GENERATED_RECEIPT
    generated_receipt = load_json(generated_receipt_path)
    require(generated_receipt.get("schema") == 2, "unsupported generated-input receipt schema")
    require(generated_receipt.get("publication") == FRESH_PUBLICATION,
            "generated-input publication contract mismatch")
    require(generated_receipt.get("flyspeck_commit") == expected_flyspeck,
            "generated-input Flyspeck pin mismatch")
    require(generated_receipt.get("contract_sha256") == generated_contract_sha256,
            "generated-input receipt contract mismatch")
    expected_outputs = [entry for entry in manifest["generated_inputs"]
                        if entry["class"] == PREPARED_INPUT_CLASS]
    observed_outputs = generated_receipt.get("outputs")
    require(isinstance(observed_outputs, list), "missing generated-input receipt outputs")
    require(len(expected_outputs) == len(observed_outputs) == 1,
            "generated-input output-set mismatch")
    expected_output = expected_outputs[0]
    observed_output = observed_outputs[0]
    for field in ("path", "bytes", "sha256"):
        require(observed_output.get(field) == expected_output[field],
                f"generated-input receipt {field} mismatch")

    generated_bindings: list[dict[str, Any]] = []
    for record in manifest["generated_inputs"]:
        root = generated_root if record["class"] == PREPARED_INPUT_CLASS else flyspeck_root
        validate_record(root / record["path"], record, f"generated input {record['path']}")
        generated_bindings.append({field: record[field] for field in ("class", "path", "bytes", "sha256")})

    return {
        "candle_head": candle_head,
        "source_bindings": source_bindings,
        "normalization_bindings": normalization_bindings,
        "generated_bindings": generated_bindings,
        "normalization_contract_sha256": normalization["contract_sha256"],
        "normalization_receipt_sha256": sha256_file(normalization_receipt_path),
        "generated_contract_sha256": generated_contract_sha256,
        "generated_receipt_sha256": sha256_file(generated_receipt_path),
    }


def boundary_records(audit: dict[str, Any]) -> tuple[list[dict[str, Any]], dict[str, bytes]]:
    actions = audit["actions"]
    driver = audit["driver"]
    offsets = audit["action_offsets"]
    records: list[dict[str, Any]] = []
    prefixes: dict[str, bytes] = {}
    for number, stratum in enumerate(audit["strata"]):
        end = stratum["end_index"]
        count = end + 1
        name = stratum["name"]
        filename = f"prefix-{number:02d}-{name}-through-{end:03d}.ml"
        prefix = driver[:offsets[end]]
        require(prefix.count(b"\n#flyspeck_needs ") == count,
                f"cumulative prefix directive count drift: {name}")
        prefixes[filename] = prefix
        next_index = count if count < len(actions) else None
        records.append({
            "boundary_id": f"{number:02d}-{name}-through-{end:03d}",
            "stratum": name,
            "stratum_start_index": stratum["start_index"],
            "stratum_end_index": end,
            "stratum_ordered_root_sha256": stratum["ordered_root_sha256"],
            "completed_action_count": count,
            "last_action": actions[end],
            "next_action_index": next_index,
            "next_stratum": actions[next_index]["stratum"] if next_index is not None else None,
            "cumulative_action_sha256": canonical_sha256(actions[:count]),
            "cumulative_prefix": {
                "path": filename,
                "bytes": len(prefix),
                "md5": hashlib.md5(prefix, usedforsecurity=False).hexdigest(),
                "sha256": hashlib.sha256(prefix).hexdigest(),
            },
            "restart_mode": "fresh-process-replay-from-action-0",
            "suffix_launch_authorized": False,
            "process_state_checkpoint": "not-captured",
        })
    require(prefixes[records[-1]["cumulative_prefix"]["path"]] == driver,
            "final cumulative prefix is not exact full driver")
    return records, prefixes


def diagnostic_records(audit: dict[str, Any]) -> tuple[list[dict[str, Any]], dict[str, bytes]]:
    """Return small exact cumulative cutpoints for rebuilt-binary diagnosis."""
    actions = audit["actions"]
    driver = audit["driver"]
    offsets = audit["action_offsets"]
    records: list[dict[str, Any]] = []
    prefixes: dict[str, bytes] = {}
    for number, end in enumerate((2, 18)):
        count = end + 1
        filename = f"prefix-d{number}-diagnostic-through-{end:03d}.ml"
        prefix = driver[:offsets[end]]
        require(prefix.count(b"\n#flyspeck_needs ") == count,
                f"diagnostic prefix directive count drift: {end}")
        prefixes[filename] = prefix
        records.append({
            "boundary_id": f"d{number}-diagnostic-through-{end:03d}",
            "diagnostic_only": True,
            "stratum": actions[end]["stratum"],
            "stratum_start_index": 0,
            "stratum_end_index": end,
            "completed_action_count": count,
            "last_action": actions[end],
            "next_action_index": count,
            "next_stratum": actions[count]["stratum"],
            "cumulative_action_sha256": canonical_sha256(actions[:count]),
            "cumulative_prefix": {
                "path": filename,
                "bytes": len(prefix),
                "md5": hashlib.md5(prefix, usedforsecurity=False).hexdigest(),
                "sha256": hashlib.sha256(prefix).hexdigest(),
            },
            "restart_mode": "fresh-process-replay-from-action-0",
            "suffix_launch_authorized": False,
            "process_state_checkpoint": "not-captured",
            "assurance_limit": (
                "rebuilt-binary compatibility diagnostic only; not a completed "
                "roadmap stratum and not S2/S3 evidence"
            ),
        })
    return records, prefixes


def make_plan(
    expected_candle_base: str,
    audit: dict[str, Any],
    validated: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, bytes]]:
    manifest = audit["manifest"]
    boundaries, prefixes = boundary_records(audit)
    diagnostic_cutpoints, diagnostic_prefixes = diagnostic_records(audit)
    require(not set(prefixes).intersection(diagnostic_prefixes),
            "diagnostic prefix filename collision")
    prefixes.update(diagnostic_prefixes)
    contract = manifest["static_full_build_contract"]
    plan = {
        "schema": 1,
        "kind": "candle-flyspeck-cumulative-stratum-plan",
        "claim": "authenticated host-side action plan only; not Candle execution or S2/S3 evidence",
        "repositories": {
            "candle_integration_base": expected_candle_base,
            "candle_materialization_head": validated["candle_head"],
            "flyspeck_commit": manifest["repositories"]["flyspeck"]["commit"],
        },
        "manifest_sha256": audit["manifest_sha256"],
        "full_driver": {
            "path": FULL_BUILD_PATH,
            "bytes": len(audit["driver"]),
            "md5": contract["generated_source_md5"],
            "sha256": contract["generated_source_sha256"],
            "ordered_target_sha256": contract["ordered_target_sha256"],
        },
        "loader_action_contract": {
            "directive": contract["directive"],
            "required_action": contract["required_loader_action"],
            "failure_policy": contract["failure_policy"],
            "assurance_limit": contract["assurance_limit"],
        },
        "source_graph": {
            "entry_count": len(validated["source_bindings"]),
            "ordered_binding_sha256": canonical_sha256(validated["source_bindings"]),
            "bindings": validated["source_bindings"],
        },
        "normalization_overlay": {
            "contract_sha256": validated["normalization_contract_sha256"],
            "receipt_sha256": validated["normalization_receipt_sha256"],
            "entry_count": len(validated["normalization_bindings"]),
            "ordered_binding_sha256": canonical_sha256(validated["normalization_bindings"]),
            "bindings": validated["normalization_bindings"],
        },
        "generated_inputs": {
            "contract_sha256": validated["generated_contract_sha256"],
            "receipt_sha256": validated["generated_receipt_sha256"],
            "entry_count": len(validated["generated_bindings"]),
            "ordered_binding_sha256": canonical_sha256(validated["generated_bindings"]),
            "bindings": validated["generated_bindings"],
        },
        "action_count": len(audit["actions"]),
        "ordered_action_sha256": canonical_sha256(audit["actions"]),
        "actions": audit["actions"],
        "stratum_policy": manifest["build_strata_policy"],
        "boundaries": boundaries,
        "diagnostic_cutpoints": diagnostic_cutpoints,
        "resume_contract": {
            "supported_mode": "fresh-process cumulative replay",
            "instruction": (
                "select a boundary's authenticated cumulative prefix and execute it "
                "from action 0 in a fresh process; after failure, replay that same "
                "prefix or an earlier prefix from action 0"
            ),
            "same_process_continuation": "outside-this-plan",
            "saved_process_or_kernel_state": False,
            "suffix_only_programs_emitted": False,
            "checkpoint_replay_claim": False,
        },
        "evidence_boundary": {
            "host_plan_or_schedule": "not S2/S3 evidence",
            "future_compiled_run": (
                "requires a separately authenticated verified Candle binary, exact "
                "runtime inputs, complete action-success log through the boundary, "
                "zero exit, and required semantic fingerprints"
            ),
            "host_status_cannot_upgrade_assurance": True,
        },
    }
    return plan, prefixes


def materialize(
    candle_root: Path,
    expected_candle_base: str,
    flyspeck_root: Path,
    overlay_root: Path,
    generated_root: Path,
    output_root: Path,
) -> dict[str, Any]:
    roots = [candle_root, flyspeck_root, overlay_root, generated_root]
    candle_root, flyspeck_root, overlay_root, generated_root = [root.resolve() for root in roots]
    output_root = output_root.resolve()
    require(len(expected_candle_base) == 40 and all(c in "0123456789abcdef" for c in expected_candle_base),
            "expected Candle base must be a lowercase 40-character hex commit")
    audit = audit_manifest(candle_root)
    validated = validate_inputs(
        candle_root, expected_candle_base, flyspeck_root, overlay_root,
        generated_root, audit,
    )
    plan, prefixes = make_plan(expected_candle_base, audit, validated)
    plan_data = json_bytes(plan)
    plan_sha256 = hashlib.sha256(plan_data).hexdigest()
    schedule = {
        "schema": 1,
        "kind": "candle-flyspeck-host-schedule-template",
        "claim": "host scheduling state only; never S2/S3 evidence",
        "plan_path": "plan.json",
        "plan_sha256": plan_sha256,
        "allowed_states": ["not-started", "running", "failed", "completed"],
        "initial_state": "not-started",
        "failure_restart": "fresh-process replay of an authenticated cumulative prefix from action 0",
        "process_state_checkpoint": None,
        "boundaries": [
            {
                "boundary_id": entry["boundary_id"],
                "prefix_path": entry["cumulative_prefix"]["path"],
                "prefix_sha256": entry["cumulative_prefix"]["sha256"],
                "state": "not-started",
                "attempt_receipt": None,
                "s2_s3_evidence": False,
            }
            for entry in plan["boundaries"]
        ],
        "diagnostic_cutpoints": [
            {
                "boundary_id": entry["boundary_id"],
                "prefix_path": entry["cumulative_prefix"]["path"],
                "prefix_sha256": entry["cumulative_prefix"]["sha256"],
                "state": "not-started",
                "attempt_receipt": None,
                "s2_s3_evidence": False,
            }
            for entry in plan["diagnostic_cutpoints"]
        ],
    }
    host_materialization = {
        "schema": 1,
        "claim": "host path and validation receipt only; not S2/S3 evidence",
        "plan_sha256": plan_sha256,
        "planner_source_sha256": sha256_file(Path(__file__)),
        "host_roots": {
            "candle": str(candle_root),
            "flyspeck": str(flyspeck_root),
            "normalization_overlay": str(overlay_root),
            "generated_inputs": str(generated_root),
        },
        "validated_counts": {
            "source_nodes": len(validated["source_bindings"]),
            "normalization_outputs": len(validated["normalization_bindings"]),
            "generated_inputs": len(validated["generated_bindings"]),
            "actions": len(audit["actions"]),
            "boundaries": len(plan["boundaries"]),
            "diagnostic_cutpoints": len(plan["diagnostic_cutpoints"]),
        },
    }

    require(not output_root.exists(), f"output root already exists: {output_root}")
    require(output_root.parent.is_dir(), f"output parent does not exist: {output_root.parent}")
    temporary = output_root.with_name(f"{output_root.name}.tmp.{os.getpid()}")
    require(not temporary.exists(), f"temporary output already exists: {temporary}")
    temporary.mkdir()
    try:
        for filename, content in prefixes.items():
            (temporary / filename).write_bytes(content)
        (temporary / "plan.json").write_bytes(plan_data)
        (temporary / "host-schedule-template.json").write_bytes(json_bytes(schedule))
        (temporary / "host-materialization.json").write_bytes(json_bytes(host_materialization))
        os.rename(temporary, output_root)
    except BaseException:
        shutil.rmtree(temporary)
        raise
    return {
        "plan_sha256": plan_sha256,
        "action_count": len(audit["actions"]),
        "boundary_count": len(plan["boundaries"]),
        "diagnostic_cutpoint_count": len(plan["diagnostic_cutpoints"]),
        "source_count": len(validated["source_bindings"]),
        "generated_input_count": len(validated["generated_bindings"]),
    }


def main() -> None:
    require(sys.flags.isolated == 1 and sys.flags.no_site == 1,
            "stratum planner requires /usr/bin/python3 -I -S")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--candle-root", type=Path, required=True)
    parser.add_argument("--expected-candle-base", required=True)
    parser.add_argument("--flyspeck-root", type=Path, required=True)
    parser.add_argument("--overlay-root", type=Path, required=True)
    parser.add_argument("--generated-root", type=Path, required=True)
    parser.add_argument("--write", type=Path, required=True, metavar="OUTPUT_ROOT")
    arguments = parser.parse_args()
    result = materialize(
        arguments.candle_root, arguments.expected_candle_base,
        arguments.flyspeck_root, arguments.overlay_root,
        arguments.generated_root, arguments.write,
    )
    print(
        f"stratum plan {result['plan_sha256']}: {result['action_count']} actions, "
        f"{result['boundary_count']} cumulative boundaries and "
        f"{result['diagnostic_cutpoint_count']} diagnostic cutpoints; "
        "host-only, not S2/S3 evidence"
    )


if __name__ == "__main__":
    main()
