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
import stat
import subprocess
import sys
import tempfile

import regression


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "candle" / "top100_manifest.json"
SERIALIZER = ROOT / "candle" / "fingerprint.ml"
SOURCE_CONTRACT = ROOT / "candle" / "reference_source_contracts.json"
SESSION_MARKER = "CANDLE_REFERENCE_SESSION_V1"
COMPLETE_MARKER = "CANDLE_REFERENCE_COMPLETE_V1"
PLAN_SCHEMA = "candle-s1-reference-plan-v6"
CANDIDATE_SCHEMA = "candle-s1-reference-candidate-v6"
HISTORICAL_REFERENCE_COMMIT = "3170739521d88d04580f61385c95b497690b7002"
EXACT_SOURCE_REFERENCE_COMMIT = "1258c129c3ddf0b239b649ba7024eab677cd953b"
CONTROLLER_LOCK_FD_ENV = "CANDLE_REFERENCE_CONTROLLER_LOCK_FD"


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


def _json_sha256(value):
    encoded = (json.dumps(value, indent=2) + "\n").encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _load_source_contract():
    contract = json.loads(SOURCE_CONTRACT.read_text(encoding="utf-8"))
    if not isinstance(contract, dict) or set(contract) != {
            "schema", "historical_upstream_commit",
            "exact_source_reference_commit", "compatibility_deltas"}:
        raise CollectionError("malformed reference source contract")
    if (contract["schema"] != "candle-s1-reference-source-contract-v1" or
            contract["historical_upstream_commit"] !=
            HISTORICAL_REFERENCE_COMMIT or
            contract["exact_source_reference_commit"] !=
            EXACT_SOURCE_REFERENCE_COMMIT):
        raise CollectionError("unsupported exact reference source contract")
    deltas = contract["compatibility_deltas"]
    if not isinstance(deltas, list) or len(deltas) != 3:
        raise CollectionError("reference contract must contain three deltas")
    expected = {
        "100/e_is_transcendental.ml", "100/euler.ml", "100/lagrange.ml"}
    if {delta.get("path") for delta in deltas if isinstance(delta, dict)} != expected:
        raise CollectionError("reference source delta set mismatch")
    for delta in deltas:
        if set(delta) != {
                "path", "historical_sha256", "selected_sha256", "reason"}:
            raise CollectionError("malformed reference source delta")
        if any(re.fullmatch(r"[0-9a-f]{64}", delta[field]) is None
               for field in ("historical_sha256", "selected_sha256")):
            raise CollectionError("malformed reference source delta hash")
        if not isinstance(delta["reason"], str) or not delta["reason"]:
            raise CollectionError("reference source delta lacks rationale")
    return contract


def _pin_tree(path):
    """Pin the names, kinds, modes, links, and contents of a directory tree."""
    root = Path(path).resolve(strict=True)
    if not root.is_dir():
        raise CollectionError(f"not a directory: {root}")
    records = []
    for entry in sorted(root.rglob("*"), key=lambda item: item.as_posix()):
        relative = entry.relative_to(root).as_posix()
        metadata = entry.lstat()
        mode = stat.S_IMODE(metadata.st_mode)
        if entry.is_symlink():
            target = os.readlink(entry)
            resolved = entry.resolve(strict=True)
            record = {
                "path": relative, "kind": "symlink", "mode": mode,
                "target": target, "resolved_path": str(resolved),
            }
            if resolved.is_file():
                record["resolved_sha256"] = _sha256(resolved)
            elif not resolved.is_dir():
                raise CollectionError(f"unsupported symlink target: {entry}")
            records.append(record)
        elif entry.is_file():
            records.append({
                "path": relative, "kind": "file", "mode": mode,
                "sha256": _sha256(entry),
            })
        elif entry.is_dir():
            records.append({"path": relative, "kind": "directory", "mode": mode})
        else:
            raise CollectionError(f"unsupported filesystem entry: {entry}")
    digest = hashlib.sha256()
    for record in records:
        digest.update(json.dumps(
            record, sort_keys=True, separators=(",", ":")).encode("utf-8"))
        digest.update(b"\n")
    return {
        "root": str(root),
        "entry_count": len(records),
        "inventory_sha256": digest.hexdigest(),
        "inventory_policy": "relative_path_kind_mode_link_target_and_content_v1",
    }


def _runtime_interpreter(runtime):
    first_line = Path(runtime).read_bytes().split(b"\n", 1)[0]
    match = re.fullmatch(br"#!(/[^\x00-\x20]+)(?:[ \t]+.*)?", first_line)
    if not match:
        raise CollectionError("runtime must have an absolute shebang interpreter")
    return _pin_file(Path(os.fsdecode(match.group(1))))


def _controller_lock_pass_fds():
    """Preserve an outer controller's flock through this process and HOL."""
    value = os.environ.get(CONTROLLER_LOCK_FD_ENV)
    if value is None:
        return ()
    if re.fullmatch(r"[1-9][0-9]*", value) is None:
        raise CollectionError("malformed inherited controller lock descriptor")
    descriptor = int(value)
    try:
        metadata = os.fstat(descriptor)
    except OSError as error:
        raise CollectionError("closed inherited controller lock descriptor") from error
    if not stat.S_ISREG(metadata.st_mode):
        raise CollectionError("controller lock descriptor is not a regular file")
    return (descriptor,)


def _elf_dependencies(paths):
    """Return the recursively resolved dynamic-library closure of ELF files."""
    pending = [Path(path).resolve(strict=True) for path in paths]
    checked = set()
    dependencies = {}
    absolute_path = re.compile(r"(?:=>\s+)?(/[^\s(]+)\s+\(")
    while pending:
        path = pending.pop()
        if path in checked:
            continue
        checked.add(path)
        if path.read_bytes()[:4] != b"\x7fELF":
            continue
        try:
            output = subprocess.check_output(
                ["/usr/bin/ldd", str(path)], text=True,
                stderr=subprocess.STDOUT, timeout=30,
                env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"})
        except (OSError, subprocess.SubprocessError) as error:
            raise CollectionError(f"could not inspect ELF dependencies: {path}") from error
        if "not found" in output:
            raise CollectionError(f"unresolved ELF dependency for {path}")
        for line in output.splitlines():
            match = absolute_path.search(line)
            if not match:
                continue
            dependency = Path(match.group(1)).resolve(strict=True)
            dependencies[str(dependency)] = _pin_file(dependency)
            if dependency not in checked:
                pending.append(dependency)
    return [dependencies[path] for path in sorted(dependencies)]


def _runtime_stub_files(*roots):
    stubs = {}
    for root in roots:
        root = Path(root)
        if not root.exists():
            continue
        root = root.resolve(strict=True)
        if not root.is_dir():
            raise CollectionError(f"runtime stub root is not a directory: {root}")
        for path in root.glob("*.so"):
            pin = _pin_file(path)
            stubs[pin["path"]] = pin
    return [stubs[path] for path in sorted(stubs)]


def _collector_repository_pin():
    head = _git(ROOT, "rev-parse", "HEAD")
    status = _git(ROOT, "status", "--porcelain=v1", "--untracked-files=all")
    relative = Path(__file__).resolve().relative_to(ROOT).as_posix()
    committed = subprocess.check_output(
        ["git", "-C", str(ROOT), "show", f"{head}:{relative}"])
    committed_sha256 = hashlib.sha256(committed).hexdigest()
    working_sha256 = _sha256(Path(__file__))
    return {
        "root": str(ROOT), "git_head": head,
        "git_status": status.splitlines() if status else [],
        "collector_relative_path": relative,
        "collector_at_head_sha256": committed_sha256,
        "collector_matches_head": committed_sha256 == working_sha256,
    }


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


def build_plan(target_name, reference_root, runtime, runtime_stublib, ocamlc,
               ocamlfind, nonce=None, source_mode="manifest-exact"):
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

    if source_mode not in {"manifest-exact", "historical-original"}:
        raise CollectionError("unsupported reference source mode")
    source_contract = _load_source_contract()
    if (source_mode == "manifest-exact" and reference_head !=
            EXACT_SOURCE_REFERENCE_COMMIT):
        raise CollectionError(
            "manifest-exact source mode requires exact reference HEAD")
    if (source_mode == "historical-original" and reference_head !=
            HISTORICAL_REFERENCE_COMMIT):
        raise CollectionError("historical source mode requires exact upstream HEAD")
    delta_by_path = {
        delta["path"]: delta for delta in source_contract["compatibility_deltas"]}
    load_files = []
    for relative in target["load_files"]:
        pin = _pin_file(reference_root / relative)
        expected_sha256 = target["load_file_sha256"][relative]
        source_role = "selected-manifest-source"
        if source_mode == "historical-original" and relative in delta_by_path:
            delta = delta_by_path[relative]
            if delta["selected_sha256"] != expected_sha256:
                raise CollectionError(
                    f"selected source differs from delta contract: {relative}")
            expected_sha256 = delta["historical_sha256"]
            source_role = "reviewed-historical-side-of-exact-delta"
        if pin["sha256"] != expected_sha256:
            raise CollectionError(
                f"reference source differs from manifest: {relative}")
        load_files.append({
            "relative_path": relative,
            "path": pin["path"],
            "sha256": pin["sha256"],
            "source_role": source_role,
        })

    runtime_pin = _pin_file(runtime)
    runtime_stublib_pin = _pin_file(runtime_stublib)
    runtime_interpreter_pin = _runtime_interpreter(runtime_pin["path"])
    ocamlc_pin = _pin_file(ocamlc)
    ocamlfind_pin = _pin_file(ocamlfind)
    try:
        ocaml_version = subprocess.check_output(
            [ocamlc_pin["path"], "-version"], text=True,
            stderr=subprocess.STDOUT, timeout=10).strip()
        ocaml_where = subprocess.check_output(
            [ocamlc_pin["path"], "-where"], text=True,
            stderr=subprocess.STDOUT, timeout=10).strip()
    except (OSError, subprocess.SubprocessError) as error:
        raise CollectionError("could not obtain pinned OCaml version") from error
    if not re.fullmatch(r"[0-9]+\.[0-9]+(?:\.[0-9]+)?(?:[+~].*)?", ocaml_version):
        raise CollectionError(f"unexpected OCaml version: {ocaml_version!r}")
    ocaml_where = str(Path(ocaml_where).resolve(strict=True))
    findlib_environment = {
        "PATH": "/usr/bin:/bin", "LC_ALL": "C", "OCAMLPATH": ""}
    try:
        findlib_version = subprocess.check_output(
            [ocamlfind_pin["path"], "query", "findlib", "-format", "%v"],
            text=True,
            stderr=subprocess.STDOUT, timeout=10,
            env=findlib_environment).strip()
        findlib_config_path = subprocess.check_output(
            [ocamlfind_pin["path"], "printconf", "conf"], text=True,
            stderr=subprocess.STDOUT, timeout=10,
            env=findlib_environment).strip()
    except (OSError, subprocess.SubprocessError) as error:
        raise CollectionError("could not obtain pinned findlib configuration") from error
    findlib_config_pin = _pin_file(findlib_config_path)
    findlib_environment["OCAMLFIND_CONF"] = findlib_config_pin["path"]
    try:
        findlib_paths = subprocess.check_output(
            [ocamlfind_pin["path"], "printconf", "path"], text=True,
            stderr=subprocess.STDOUT, timeout=10,
            env=findlib_environment).splitlines()
    except (OSError, subprocess.SubprocessError) as error:
        raise CollectionError("could not obtain pinned findlib package path") from error
    if not findlib_paths:
        raise CollectionError("findlib package path is empty")
    findlib_package_roots = [_pin_tree(path) for path in findlib_paths]

    nonce = nonce or secrets.token_hex(32)
    if not re.fullmatch(r"[0-9a-f]{64}", nonce):
        raise CollectionError("session nonce must be 64 lowercase hex characters")
    source = _request_source(target, SERIALIZER, nonce)
    serializer_pin = _pin_file(SERIALIZER)
    theorem_names = [item["name"] for item in request["theorems"]]
    hol_ml_pin = _pin_file(reference_root / "hol.ml")
    boot_files = [
        _pin_file(reference_root / "hol_loader.cmo"),
        _pin_file(reference_root / "pa_j.cmo"),
        _pin_file(reference_root / "load_camlp5_topfind.ml"),
    ]
    runtime_library_tree = _pin_tree(Path(runtime_stublib_pin["path"]).parent)
    ocaml_library_tree = _pin_tree(ocaml_where)
    runtime_stub_files = _runtime_stub_files(
        Path(runtime_stublib_pin["path"]).parent,
        Path(ocaml_where) / "stublibs",
        *(Path(root["root"]) / "stublibs" for root in findlib_package_roots),
    )
    dynamic_libraries = _elf_dependencies([
        runtime_interpreter_pin["path"],
        *(pin["path"] for pin in runtime_stub_files),
    ])
    collector_repository = _collector_repository_pin()
    runtime_environment = {
        "HOME": str(reference_root),
        "PATH": "/usr/bin:/bin",
        "LC_ALL": "C",
        "HOLLIGHT_DIR": str(reference_root),
        "HOLLIGHT_USE_MODULE": "0",
        "OCAMLRUNPARAM": "l=2000000000",
        "CAML_LD_LIBRARY_PATH": str(Path(runtime_stublib_pin["path"]).parent),
        "OCAML_TOPLEVEL_PATH": ocaml_where,
        "OCAMLFIND_CONF": findlib_config_pin["path"],
    }
    runtime_argv = [
        runtime_pin["path"], "-init", hol_ml_pin["path"],
        "-I", str(reference_root), "-noprompt",
    ]
    return {
        "schema": PLAN_SCHEMA,
        "status": "planned_not_executed",
        "session_nonce": nonce,
        "fresh_process_contract": {
            "required": True,
            "preloaded_checkpoint_allowed": False,
            "working_directory": str(reference_root),
            "environment_policy": "sanitized_allowlist_no_inherited_overrides",
            "runtime_argv": runtime_argv,
            "runtime_environment": runtime_environment,
        },
        "reference": {
            "root": str(reference_root),
            "git_head": reference_head,
            "git_status": [],
            "runtime_executable": runtime_pin,
            "runtime_interpreter": runtime_interpreter_pin,
            "runtime_stublib": runtime_stublib_pin,
            "runtime_library_tree": runtime_library_tree,
            "runtime_stub_files": runtime_stub_files,
            "dynamic_libraries": dynamic_libraries,
            "ocamlc": {
                **ocamlc_pin, "version": ocaml_version,
                "stdlib_directory": ocaml_where,
            },
            "findlib": {
                "executable": ocamlfind_pin,
                "version": findlib_version,
                "configuration": findlib_config_pin,
                "package_roots": findlib_package_roots,
            },
            "hol_ml": hol_ml_pin,
            "generated_boot_files": boot_files,
            "ocaml_library_tree": ocaml_library_tree,
        },
        "input": {
            "collector": _pin_file(Path(__file__)),
            "collector_repository": collector_repository,
            "manifest": {"path": str(MANIFEST), "sha256": _sha256(MANIFEST)},
            "manifest_schema_version": manifest["schema_version"],
            "target": target_name,
            "load_files": load_files,
            "theorem_names": theorem_names,
            "mapping_status": request["mapping_status"],
            "serializer": serializer_pin,
            "source_mode": source_mode,
            "source_contract": {
                "path": str(SOURCE_CONTRACT),
                "sha256": _sha256(SOURCE_CONTRACT),
                "historical_upstream_commit":
                    source_contract["historical_upstream_commit"],
                "exact_source_reference_commit":
                    source_contract["exact_source_reference_commit"],
                "compatibility_deltas":
                    source_contract["compatibility_deltas"],
            },
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


def _rebuild_plan(plan):
    return build_plan(
        plan["input"]["target"], plan["reference"]["root"],
        plan["reference"]["runtime_executable"]["path"],
        plan["reference"]["runtime_stublib"]["path"],
        plan["reference"]["ocamlc"]["path"],
        plan["reference"]["findlib"]["executable"]["path"],
        plan["session_nonce"], plan["input"]["source_mode"])


def _require_current_plan_pins(plan):
    rebuilt = _rebuild_plan(plan)
    if _stable_plan_pins(rebuilt) != _stable_plan_pins(plan):
        raise CollectionError("reference or collector inputs differ from plan pins")


def candidate_from_transcript(plan, transcript, exit_code=0):
    """Validate a completed transcript and return an unapproved candidate."""
    if plan.get("schema") != PLAN_SCHEMA:
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
    wire_prefixes = (
        regression.FINGERPRINT_MARKER + "\t",
        regression.STATE_FINGERPRINT_MARKER + "\t")
    outside_session = lines[:start_index] + lines[complete_index + 1:]
    if any(line.startswith(wire_prefixes) for line in outside_session):
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
        "artifact_hashes": {
            "plan_sha256": _json_sha256(plan),
            "request_sha256": plan["request"]["sha256"],
            "transcript_sha256": hashlib.sha256(
                transcript.encode("utf-8")).hexdigest(),
        },
        "candidate_identities": identities,
    }


def validate_candidate(candidate, plan=None, request=None, transcript=None):
    """Reject malformed candidates and optionally replay all artifact links."""
    required = {
        "schema", "artifact_kind", "approval_status", "promotion_allowed",
        "warning", "plan_pins", "session_nonce", "process_exit_code",
        "artifact_hashes", "candidate_identities",
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
    if not re.fullmatch(r"[0-9a-f]{64}", candidate["session_nonce"]):
        raise CollectionError("malformed candidate session nonce")
    hashes = candidate["artifact_hashes"]
    if set(hashes) != {"plan_sha256", "request_sha256", "transcript_sha256"}:
        raise CollectionError("malformed candidate artifact hashes")
    if any(not re.fullmatch(r"[0-9a-f]{64}", value)
           for value in hashes.values()):
        raise CollectionError("malformed candidate artifact hash")
    plan_pins = candidate["plan_pins"]
    if (set(plan_pins) != {"reference", "input", "request_sha256",
                           "fresh_process_contract"}
            or plan_pins["request_sha256"] != hashes["request_sha256"]):
        raise CollectionError("malformed candidate plan pins")
    if candidate["candidate_identities"].get("status") != "observed_uncompared":
        raise CollectionError("reference candidate is not explicitly incomparable")
    supplied = (plan is not None, request is not None, transcript is not None)
    if any(supplied) and not all(supplied):
        raise CollectionError("plan, request, and transcript must be supplied together")
    if all(supplied):
        if hashes["plan_sha256"] != _json_sha256(plan):
            raise CollectionError("candidate plan artifact hash mismatch")
        request_sha256 = hashlib.sha256(request.encode("utf-8")).hexdigest()
        if (request != plan["request"]["source"]
                or request_sha256 != hashes["request_sha256"]):
            raise CollectionError("candidate request artifact mismatch")
        transcript_sha256 = hashlib.sha256(transcript.encode("utf-8")).hexdigest()
        if transcript_sha256 != hashes["transcript_sha256"]:
            raise CollectionError("candidate transcript artifact hash mismatch")
        rebuilt = candidate_from_transcript(
            plan, transcript, candidate["process_exit_code"])
        if rebuilt != candidate:
            raise CollectionError("candidate does not replay from linked artifacts")
    return candidate


def collect(plan, transcript_path, candidate_path, wall_timeout):
    """Launch one fresh reference process, recheck pins, and write a candidate."""
    collector_repository = plan["input"]["collector_repository"]
    if (collector_repository["git_status"]
            or not collector_repository["collector_matches_head"]):
        raise CollectionError(
            "collector repository must be clean with the collector at HEAD")
    _require_current_plan_pins(plan)
    argv = list(plan["fresh_process_contract"]["runtime_argv"])
    env = dict(plan["fresh_process_contract"]["runtime_environment"])
    completed = subprocess.run(
        argv, input=plan["request"]["source"], text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        cwd=plan["fresh_process_contract"]["working_directory"], env=env,
        timeout=wall_timeout, check=False,
        pass_fds=_controller_lock_pass_fds())
    transcript_path.write_text(completed.stdout, encoding="utf-8")

    _require_current_plan_pins(plan)
    candidate = candidate_from_transcript(
        plan, completed.stdout, completed.returncode)
    validate_candidate(candidate, plan, plan["request"]["source"], completed.stdout)
    candidate_path.write_text(
        json.dumps(candidate, indent=2) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    for command in ("plan", "collect"):
        sub = subparsers.add_parser(command)
        sub.add_argument("--target", required=True)
        sub.add_argument("--reference-root", type=Path, required=True)
        sub.add_argument("--runtime", type=Path, required=True)
        sub.add_argument("--runtime-stublib", type=Path, required=True)
        sub.add_argument("--ocamlc", type=Path, required=True)
        sub.add_argument("--ocamlfind", type=Path, required=True)
        sub.add_argument("--plan", type=Path, required=True)
        sub.add_argument("--request", type=Path, required=True)
        sub.add_argument(
            "--source-mode", choices=("manifest-exact", "historical-original"),
            default="manifest-exact")
        if command == "collect":
            sub.add_argument("--transcript", type=Path, required=True)
            sub.add_argument("--candidate", type=Path, required=True)
            sub.add_argument("--wall-timeout", type=float, required=True)
    validate = subparsers.add_parser("validate")
    validate.add_argument("candidate", type=Path)
    validate.add_argument("--plan", type=Path, required=True)
    validate.add_argument("--request", type=Path, required=True)
    validate.add_argument("--transcript", type=Path, required=True)
    args = parser.parse_args()

    try:
        if args.command == "validate":
            candidate = json.loads(args.candidate.read_text())
            plan = json.loads(args.plan.read_text())
            request = args.request.read_text(encoding="utf-8")
            transcript = args.transcript.read_text(encoding="utf-8")
            validate_candidate(candidate, plan, request, transcript)
            _require_current_plan_pins(plan)
            print(f"candidate and linked artifacts valid but unapproved: {args.candidate}")
            return 0
        plan = build_plan(
            args.target, args.reference_root, args.runtime,
            args.runtime_stublib, args.ocamlc, args.ocamlfind,
            source_mode=args.source_mode)
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
