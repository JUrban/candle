#!/usr/bin/env python3
"""Collect review-only S1 identities from a pinned HOL Light reference.

The output is deliberately not an EXPECTED_IDENTITIES object.  Collection and
approval are separate operations; this tool implements collection only.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import secrets
import subprocess
import sys
import tempfile

import regression


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "candle" / "top100_manifest.json"
SERIALIZER = ROOT / "candle" / "fingerprint.ml"
SESSION_MARKER = "CANDLE_REFERENCE_SESSION_V1"
COMPLETE_MARKER = "CANDLE_REFERENCE_COMPLETE_V1"
CANDIDATE_SCHEMA = "candle-s1-reference-candidate-v1"


class CollectionError(Exception):
    """Reference collection failed its provenance or transcript contract."""


def _sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _git(root, *args):
    return subprocess.check_output(
        ["git", "-C", str(root), *args], text=True).strip()


def _pin_file(path):
    path = Path(path).resolve(strict=True)
    if not path.is_file():
        raise CollectionError(f"not a regular file: {path}")
    return {"path": str(path), "sha256": _sha256(path)}


def _ocaml_string(value):
    """JSON string escaping is a safe subset for these generated OCaml paths."""
    return json.dumps(str(value), ensure_ascii=True)


def _target_from_manifest(target_name):
    payload = json.loads(MANIFEST.read_text(encoding="utf-8"))
    matches = [target for target in payload["targets"]
               if target["name"] == target_name]
    if len(matches) != 1:
        raise CollectionError(f"unknown or duplicate manifest target: {target_name}")
    return payload, matches[0]


def _request_source(target, serializer_path, nonce):
    request = target["fingerprint_request"]
    theorem_names = [item["name"] for item in request["theorems"]]
    lines = [
        f'print_endline ({_ocaml_string(SESSION_MARKER + chr(9) + nonce)});;',
        f'loadt {_ocaml_string(Path(serializer_path).resolve())};;',
    ]
    lines.extend(f'loadt {_ocaml_string(path)};;'
                 for path in target["load_files"])
    lines.append(regression._fingerprint_request_source(theorem_names).rstrip())
    lines.extend([
        f'print_endline ({_ocaml_string(COMPLETE_MARKER + chr(9) + nonce)});;',
        "exit 0;;",
    ])
    return "\n".join(lines) + "\n"


def build_plan(target_name, reference_root, launcher, runtime, ocamlc,
               nonce=None):
    """Pin a clean reference tree and generate, but do not execute, a request."""
    manifest, target = _target_from_manifest(target_name)
    request = target["fingerprint_request"]
    if request["mapping_status"] != "audited":
        raise CollectionError(
            f"manual-review theorem mapping cannot be collected: {target_name}")
    if request.get("expected_identities") is not None:
        raise CollectionError(
            f"approved expected identities already exist: {target_name}")

    reference_root = Path(reference_root).resolve(strict=True)
    status = _git(reference_root, "status", "--porcelain=v1", "--untracked-files=all")
    if status:
        raise CollectionError("reference git tree is not clean")
    reference_head = _git(reference_root, "rev-parse", "HEAD")
    if not re.fullmatch(r"[0-9a-f]{40}", reference_head):
        raise CollectionError("reference git HEAD is not a full SHA-1")

    load_files = []
    for relative in target["load_files"]:
        pin = _pin_file(reference_root / relative)
        expected_sha256 = target["load_file_sha256"][relative]
        if pin["sha256"] != expected_sha256:
            raise CollectionError(
                f"reference source differs from manifest: {relative}")
        load_files.append({
            "relative_path": relative,
            "path": pin["path"],
            "sha256": pin["sha256"],
        })

    launcher_pin = _pin_file(launcher)
    runtime_pin = _pin_file(runtime)
    ocamlc_pin = _pin_file(ocamlc)
    try:
        ocaml_version = subprocess.check_output(
            [ocamlc_pin["path"], "-version"], text=True,
            stderr=subprocess.STDOUT, timeout=10).strip()
    except (OSError, subprocess.SubprocessError) as error:
        raise CollectionError("could not obtain pinned OCaml version") from error
    if not re.fullmatch(r"[0-9]+\.[0-9]+(?:\.[0-9]+)?(?:[+~].*)?", ocaml_version):
        raise CollectionError(f"unexpected OCaml version: {ocaml_version!r}")

    nonce = nonce or secrets.token_hex(32)
    if not re.fullmatch(r"[0-9a-f]{64}", nonce):
        raise CollectionError("session nonce must be 64 lowercase hex characters")
    source = _request_source(target, SERIALIZER, nonce)
    serializer_pin = _pin_file(SERIALIZER)
    theorem_names = [item["name"] for item in request["theorems"]]
    launcher_environment = {
        "HOME": os.environ.get("HOME", ""),
        "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
        "LC_ALL": "C",
        "LINE_EDITOR": "/usr/bin/env",
    }
    if not launcher_environment["HOME"]:
        raise CollectionError("HOME is required by the sanitized launcher environment")
    return {
        "schema": "candle-s1-reference-plan-v1",
        "status": "planned_not_executed",
        "session_nonce": nonce,
        "fresh_process_contract": {
            "required": True,
            "preloaded_checkpoint_allowed": False,
            "working_directory": str(reference_root),
            "environment_policy": "sanitized_allowlist_no_inherited_overrides",
            "launcher_environment": launcher_environment,
        },
        "reference": {
            "root": str(reference_root),
            "git_head": reference_head,
            "git_status": [],
            "launcher": launcher_pin,
            "runtime_executable": runtime_pin,
            "ocamlc": {**ocamlc_pin, "version": ocaml_version},
            "hol_ml": _pin_file(reference_root / "hol.ml"),
        },
        "input": {
            "collector": _pin_file(Path(__file__)),
            "manifest": {"path": str(MANIFEST), "sha256": _sha256(MANIFEST)},
            "manifest_schema_version": manifest["schema_version"],
            "target": target_name,
            "load_files": load_files,
            "theorem_names": theorem_names,
            "mapping_status": request["mapping_status"],
            "serializer": serializer_pin,
        },
        "request": {
            "source": source,
            "sha256": hashlib.sha256(source.encode("utf-8")).hexdigest(),
        },
    }


def _stable_plan_pins(plan):
    """Return only inputs which must be unchanged after the reference run."""
    return {
        "reference": plan["reference"],
        "input": plan["input"],
        "request_sha256": plan["request"]["sha256"],
        "fresh_process_contract": plan["fresh_process_contract"],
    }


def candidate_from_transcript(plan, transcript, exit_code=0):
    """Validate a completed transcript and return an unapproved candidate."""
    if plan.get("schema") != "candle-s1-reference-plan-v1":
        raise CollectionError("unsupported collection plan")
    if exit_code != 0:
        raise CollectionError(f"reference process exited with status {exit_code}")
    nonce = plan["session_nonce"]
    start = f"{SESSION_MARKER}\t{nonce}"
    complete = f"{COMPLETE_MARKER}\t{nonce}"
    lines = transcript.splitlines()
    if lines.count(start) != 1 or lines.count(complete) != 1:
        raise CollectionError("missing or duplicate reference session markers")
    start_index = lines.index(start)
    complete_index = lines.index(complete)
    if start_index >= complete_index:
        raise CollectionError("reference completion marker precedes session marker")
    wire_prefix = regression.FINGERPRINT_MARKER + "\t"
    outside_session = lines[:start_index] + lines[complete_index + 1:]
    if any(line.startswith(wire_prefix) for line in outside_session):
        raise CollectionError("fingerprint record outside reference session")
    session_transcript = "\n".join(
        lines[start_index + 1:complete_index]) + "\n"

    with tempfile.NamedTemporaryFile(
            mode="w", encoding="utf-8", delete=False) as transcript_file:
        transcript_file.write(session_transcript)
        transcript_path = Path(transcript_file.name)
    try:
        identities = regression._read_fingerprint_records(
            transcript_path, tuple(plan["input"]["theorem_names"]),
            plan["input"]["mapping_status"])
    except regression.LoadFailure as error:
        raise CollectionError(str(error)) from error
    finally:
        transcript_path.unlink()

    if identities["status"] != "observed_uncompared":
        raise CollectionError("reference collection unexpectedly compared identities")
    return {
        "schema": CANDIDATE_SCHEMA,
        "artifact_kind": "reference_identity_candidate",
        "approval_status": "candidate_unapproved",
        "promotion_allowed": False,
        "warning": (
            "Review provenance and identities independently; this artifact is "
            "not an EXPECTED_IDENTITIES value and no automatic promotion exists."
        ),
        "plan_pins": _stable_plan_pins(plan),
        "session_nonce": nonce,
        "process_exit_code": exit_code,
        "transcript_sha256": hashlib.sha256(
            transcript.encode("utf-8")).hexdigest(),
        "candidate_identities": identities,
    }


def validate_candidate(candidate):
    """Reject artifacts that are not structurally review-only candidates."""
    required = {
        "schema", "artifact_kind", "approval_status", "promotion_allowed",
        "warning", "plan_pins", "session_nonce", "process_exit_code",
        "transcript_sha256", "candidate_identities",
    }
    if set(candidate) != required:
        raise CollectionError("malformed reference candidate fields")
    if candidate["schema"] != CANDIDATE_SCHEMA:
        raise CollectionError("unsupported reference candidate schema")
    if (candidate["artifact_kind"] != "reference_identity_candidate"
            or candidate["approval_status"] != "candidate_unapproved"
            or candidate["promotion_allowed"] is not False):
        raise CollectionError("reference artifact is not fail-closed")
    if candidate["process_exit_code"] != 0:
        raise CollectionError("reference candidate records a failed process")
    if candidate["candidate_identities"].get("status") != "observed_uncompared":
        raise CollectionError("reference candidate is not explicitly incomparable")
    return candidate


def collect(plan, transcript_path, candidate_path, wall_timeout):
    """Launch one fresh reference process, recheck pins, and write a candidate."""
    launcher = plan["reference"]["launcher"]["path"]
    env = dict(plan["fresh_process_contract"]["launcher_environment"])
    completed = subprocess.run(
        [launcher], input=plan["request"]["source"], text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        cwd=plan["fresh_process_contract"]["working_directory"], env=env,
        timeout=wall_timeout, check=False)
    transcript_path.write_text(completed.stdout, encoding="utf-8")

    rebuilt = build_plan(
        plan["input"]["target"], plan["reference"]["root"],
        plan["reference"]["launcher"]["path"],
        plan["reference"]["runtime_executable"]["path"],
        plan["reference"]["ocamlc"]["path"], plan["session_nonce"])
    if _stable_plan_pins(rebuilt) != _stable_plan_pins(plan):
        raise CollectionError("reference inputs changed during collection")
    candidate = candidate_from_transcript(
        plan, completed.stdout, completed.returncode)
    validate_candidate(candidate)
    candidate_path.write_text(
        json.dumps(candidate, indent=2) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    for command in ("plan", "collect"):
        sub = subparsers.add_parser(command)
        sub.add_argument("--target", required=True)
        sub.add_argument("--reference-root", type=Path, required=True)
        sub.add_argument("--launcher", type=Path, required=True)
        sub.add_argument("--runtime", type=Path, required=True)
        sub.add_argument("--ocamlc", type=Path, required=True)
        sub.add_argument("--plan", type=Path, required=True)
        sub.add_argument("--request", type=Path, required=True)
        if command == "collect":
            sub.add_argument("--transcript", type=Path, required=True)
            sub.add_argument("--candidate", type=Path, required=True)
            sub.add_argument("--wall-timeout", type=float, required=True)
    validate = subparsers.add_parser("validate")
    validate.add_argument("candidate", type=Path)
    args = parser.parse_args()

    try:
        if args.command == "validate":
            validate_candidate(json.loads(args.candidate.read_text()))
            print(f"candidate valid and unapproved: {args.candidate}")
            return 0
        plan = build_plan(
            args.target, args.reference_root, args.launcher,
            args.runtime, args.ocamlc)
        args.plan.write_text(json.dumps(plan, indent=2) + "\n", encoding="utf-8")
        args.request.write_text(plan["request"]["source"], encoding="utf-8")
        if args.command == "plan":
            print(f"collection planned but not executed: {args.plan}")
            return 0
        if args.wall_timeout <= 0:
            raise CollectionError("--wall-timeout must be positive")
        collect(plan, args.transcript, args.candidate, args.wall_timeout)
        print(f"unapproved reference candidate: {args.candidate}")
        return 0
    except (CollectionError, OSError, subprocess.SubprocessError,
            json.JSONDecodeError) as error:
        print(f"reference collection failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
