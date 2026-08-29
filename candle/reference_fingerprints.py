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
import types


REFERENCE_PROTOCOL_RELATIVE = "candle/reference_protocol.py"
REFERENCE_PROTOCOL_SHA256 = \
    "e44ed73330e65058f759e30e90ede0bca0bfdedc7920534d632ecb6806299f68"


def _load_reference_protocol():
    """Load only the exact stdlib-only sibling bound by this collector."""
    path = Path(__file__).resolve().with_name("reference_protocol.py")
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        before = os.fstat(descriptor)
        chunks = []
        while True:
            block = os.read(descriptor, 1024 * 1024)
            if not block:
                break
            chunks.append(block)
        after = os.fstat(descriptor)
        named = path.stat(follow_symlinks=False)
    finally:
        os.close(descriptor)
    source = b"".join(chunks)
    if (not stat.S_ISREG(before.st_mode) or before.st_nlink != 1 or
            (before.st_dev, before.st_ino, before.st_size,
             before.st_mtime_ns, before.st_ctime_ns) !=
            (after.st_dev, after.st_ino, after.st_size,
             after.st_mtime_ns, after.st_ctime_ns) or
            (named.st_dev, named.st_ino) != (after.st_dev, after.st_ino) or
            hashlib.sha256(source).hexdigest() != REFERENCE_PROTOCOL_SHA256):
        raise RuntimeError("reference protocol module differs from collector pin")
    module = types.ModuleType("candle_reference_protocol")
    module.__file__ = str(path)
    exec(compile(source, str(path), "exec"), module.__dict__)
    return module


regression = _load_reference_protocol()


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "candle" / "top100_manifest.json"
SERIALIZER = ROOT / "candle" / "fingerprint.ml"
SOURCE_CONTRACT = ROOT / "candle" / "reference_source_contracts.json"
SESSION_MARKER = "CANDLE_REFERENCE_SESSION_V1"
COMPLETE_MARKER = "CANDLE_REFERENCE_COMPLETE_V1"
PLAN_SCHEMA = "candle-s1-reference-plan-v8"
CANDIDATE_SCHEMA = "candle-s1-reference-candidate-v8"
HISTORICAL_REFERENCE_COMMIT = "3170739521d88d04580f61385c95b497690b7002"
EXACT_SOURCE_REFERENCE_COMMIT = "1258c129c3ddf0b239b649ba7024eab677cd953b"
CONTROLLER_LOCK_FD_ENV = "CANDLE_REFERENCE_CONTROLLER_LOCK_FD"
PARI_GP_PROBE_SOURCE = \
    "echo 'print(default(nbthreads)); print(factorint(15))  \n quit' | gp"
RUNTIME_ENVIRONMENT_KEYS = {
    "HOME", "PATH", "LC_ALL", "GPRC", "GP_DATA_DIR", "HOLLIGHT_DIR",
    "HOLLIGHT_USE_MODULE", "OCAMLRUNPARAM", "CAML_LD_LIBRARY_PATH",
    "OCAML_TOPLEVEL_PATH", "OCAMLFIND_CONF",
}
ELF_EVIDENCE_POLICY = "authenticated_explicit_bash_ldd_closure_v1"
ELF_OUTPUT_NORMALIZATION_POLICY = \
    "strict_recognized_lines_replace_only_aslr_addresses_v1"
ELF_BASH_PATH = Path("/bin/bash")
ELF_LDD_PATH = Path("/usr/bin/ldd")
ELF_CACHE_PATH = Path("/etc/ld.so.cache")
ELF_PRELOAD_PATH = Path("/etc/ld.so.preload")
ELF_LOADER_PATHS = (
    Path("/lib/ld-linux.so.2"),
    Path("/lib64/ld-linux-x86-64.so.2"),
    Path("/libx32/ld-linux-x32.so.2"),
)
ELF_OBSERVER_ENVIRONMENT = {
    "PATH": "/usr/bin:/bin", "LC_ALL": "C", "LANG": "C",
}
ELF_VIRTUAL_OBJECTS = ["linux-vdso.so.1"]


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
        "root_mode": stat.S_IMODE(root.lstat().st_mode),
        "entry_count": len(records),
        "inventory_sha256": digest.hexdigest(),
        "inventory_policy": "relative_path_kind_mode_link_target_and_content_v1",
    }


def _pin_executable_route(path, label):
    """Pin a PATH or fixed-shell route as well as its resolved executable."""
    argument = Path(os.path.abspath(path))
    try:
        metadata = argument.lstat()
        parent_metadata = argument.parent.lstat()
        resolved = argument.resolve(strict=True)
        resolved_metadata = resolved.lstat()
    except (FileNotFoundError, RuntimeError, OSError) as error:
        raise CollectionError(f"could not resolve {label}: {argument}") from error
    if not stat.S_ISREG(resolved_metadata.st_mode):
        raise CollectionError(f"resolved {label} is not a regular file: {resolved}")
    if stat.S_IMODE(resolved_metadata.st_mode) & 0o111 == 0:
        raise CollectionError(f"resolved {label} is not executable: {resolved}")

    def route_record(route, route_metadata):
        if stat.S_ISLNK(route_metadata.st_mode):
            return {
                "path": str(route), "kind": "symlink",
                "mode": stat.S_IMODE(route_metadata.st_mode),
                "target": os.readlink(route),
                "resolved_path": str(route.resolve(strict=True)),
            }
        if stat.S_ISDIR(route_metadata.st_mode):
            return {
                "path": str(route), "kind": "directory",
                "mode": stat.S_IMODE(route_metadata.st_mode),
                "resolved_path": str(route.resolve(strict=True)),
            }
        if stat.S_ISREG(route_metadata.st_mode):
            return {
                "path": str(route), "kind": "file",
                "mode": stat.S_IMODE(route_metadata.st_mode),
                "resolved_path": str(route.resolve(strict=True)),
            }
        raise CollectionError(f"unsupported {label} route component: {route}")

    return {
        "argument_path": str(argument),
        "argument_parent": route_record(argument.parent, parent_metadata),
        "argument": route_record(argument, metadata),
        "resolved_executable": {
            **_pin_file(resolved),
            "mode": stat.S_IMODE(resolved_metadata.st_mode),
        },
    }


def _valid_sha256(value):
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value)


def _validate_executable_route(route, label):
    if not isinstance(route, dict) or set(route) != {
            "argument_path", "argument_parent", "argument",
            "resolved_executable"}:
        raise CollectionError(f"malformed {label} route")
    if (not isinstance(route["argument_path"], str) or
            not Path(route["argument_path"]).is_absolute()):
        raise CollectionError(f"malformed {label} argument")
    for component_label in ("argument_parent", "argument"):
        component = route[component_label]
        kind = component.get("kind") if isinstance(component, dict) else None
        expected = ({"path", "kind", "mode", "resolved_path", "target"}
                    if kind == "symlink" else
                    {"path", "kind", "mode", "resolved_path"})
        if (kind not in {"symlink", "directory", "file"} or
                set(component) != expected or
                not isinstance(component["path"], str) or
                not Path(component["path"]).is_absolute() or
                type(component["mode"]) is not int or
                not isinstance(component["resolved_path"], str) or
                not Path(component["resolved_path"]).is_absolute() or
                (kind == "symlink" and
                 not isinstance(component["target"], str))):
            raise CollectionError(
                f"malformed {label} {component_label}")
    if (route["argument_parent"]["kind"] not in {"directory", "symlink"} or
            route["argument"]["kind"] not in {"file", "symlink"}):
        raise CollectionError(f"malformed {label} route component kinds")
    resolved = route["resolved_executable"]
    if (not isinstance(resolved, dict) or set(resolved) != {
            "path", "sha256", "mode"} or
            not isinstance(resolved["path"], str) or
            not Path(resolved["path"]).is_absolute() or
            not _valid_sha256(resolved["sha256"]) or
            type(resolved["mode"]) is not int or
            resolved["mode"] & 0o111 == 0):
        raise CollectionError(f"malformed {label} executable")
    if (route["argument"]["path"] != route["argument_path"] or
            route["argument_parent"]["path"] !=
            str(Path(route["argument_path"]).parent) or
            route["argument"]["resolved_path"] != resolved["path"] or
            (route["argument"]["kind"] == "file" and
             route["argument"]["resolved_path"] != route["argument_path"])):
        raise CollectionError(f"inconsistent {label} route")


def _pin_elf_file(path, label):
    path = Path(path).resolve(strict=True)
    if not path.is_file():
        raise CollectionError(f"not a regular file: {path}")
    try:
        source = path.read_bytes()
    except OSError as error:
        raise CollectionError(f"could not inspect ELF file: {label}") from error
    if not source.startswith(b"\x7fELF"):
        raise CollectionError(f"non-ELF file in runtime closure: {label}")
    return {
        "path": str(path), "sha256": hashlib.sha256(source).hexdigest()}


def _pin_loader_route(path):
    path = Path(path)
    try:
        path.lstat()
    except FileNotFoundError:
        return {"argument_path": str(path), "status": "absent"}
    except OSError as error:
        raise CollectionError(f"could not inspect loader route: {path}") from error
    return {
        "argument_path": str(path), "status": "present",
        "route": _pin_executable_route(path, f"ELF loader {path}"),
    }


def _elf_oracle_inputs():
    """Pin every host input used by the explicit bash/ldd observer."""
    if os.path.lexists(ELF_PRELOAD_PATH):
        raise CollectionError("/etc/ld.so.preload must be absent")
    cache_metadata = ELF_CACHE_PATH.lstat()
    if (not stat.S_ISREG(cache_metadata.st_mode) or
            ELF_CACHE_PATH.is_symlink() or
            ELF_CACHE_PATH.resolve(strict=True) != ELF_CACHE_PATH):
        raise CollectionError("/etc/ld.so.cache must be a canonical regular file")
    bash = _pin_executable_route(ELF_BASH_PATH, "ELF observer bash")
    ldd = _pin_executable_route(ELF_LDD_PATH, "ELF observer ldd")
    ldd_source = Path(ldd["resolved_executable"]["path"]).read_bytes()
    if (hashlib.sha256(ldd_source).hexdigest() !=
            ldd["resolved_executable"]["sha256"]):
        raise CollectionError("ldd changed while its contract was inspected")
    loader_matches = re.findall(br'^RTLDLIST="([^"\n]+)"$', ldd_source, re.MULTILINE)
    expected_loader_bytes = b" ".join(
        os.fsencode(str(path)) for path in ELF_LOADER_PATHS)
    if loader_matches != [expected_loader_bytes]:
        raise CollectionError("ldd hardcoded loader route contract changed")
    return {
        "tools": {"bash": bash, "ldd": ldd},
        "hardcoded_loader_routes": [
            _pin_loader_route(path) for path in ELF_LOADER_PATHS],
        "ld_so_cache": _pin_file(ELF_CACHE_PATH),
        "ld_so_preload": {
            "path": str(ELF_PRELOAD_PATH), "status": "absent"},
        "environment": dict(ELF_OBSERVER_ENVIRONMENT),
    }


def _parse_ldd_output(stdout, label):
    """Parse every ldd line or fail; addresses remain only in retained stdout."""
    if not isinstance(stdout, str) or not stdout.endswith("\n"):
        raise CollectionError(f"malformed ldd stdout for {label}")
    mapped = re.compile(
        r"(?P<role>[^\s]+)\s+=>\s+(?P<path>/[^\s(]+)\s+"
        r"\(0x[0-9a-fA-F]+\)")
    direct = re.compile(r"(?P<path>/[^\s(]+)\s+\(0x[0-9a-fA-F]+\)")
    virtual = re.compile(
        r"(?P<role>linux-(?:vdso|gate)\.so\.1)\s+"
        r"\(0x[0-9a-fA-F]+\)")
    files = []
    virtual_objects = []
    roles = set()
    for raw_line in stdout.splitlines():
        line = raw_line.strip()
        match = mapped.fullmatch(line)
        if match is not None:
            role = match.group("role")
            reported_path = match.group("path")
            item = {"role": role, "reported_path": reported_path}
        else:
            match = direct.fullmatch(line)
            if match is not None:
                reported_path = match.group("path")
                role = Path(reported_path).name
                item = {"role": role, "reported_path": reported_path}
            else:
                match = virtual.fullmatch(line)
                if match is not None:
                    role = match.group("role")
                    if role in roles:
                        raise CollectionError(
                            f"duplicate ldd role for {label}: {role}")
                    roles.add(role)
                    virtual_objects.append(role)
                    continue
                raise CollectionError(
                    f"unrecognized ldd output for {label}: {line}")
        if role in roles:
            raise CollectionError(f"duplicate ldd role for {label}: {role}")
        roles.add(role)
        files.append(item)
    files.sort(key=lambda item: (item["role"], item["reported_path"]))
    virtual_objects.sort()
    if not files or virtual_objects != ELF_VIRTUAL_OBJECTS:
        raise CollectionError(f"incomplete ldd output for {label}")
    return files, virtual_objects


def _normalize_ldd_stdout(stdout, label):
    """Strip only validated ASLR address tokens from otherwise exact output."""
    _parse_ldd_output(stdout, label)
    return re.sub(r"\(0x[0-9a-fA-F]+\)", "(0xADDRESS)", stdout)


def _observe_elf_root(root, oracle):
    root_pin = _pin_elf_file(root, str(root))
    argv = [str(ELF_BASH_PATH), str(ELF_LDD_PATH), root_pin["path"]]
    try:
        completed = subprocess.run(
            argv, env=dict(ELF_OBSERVER_ENVIRONMENT),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, encoding="utf-8", errors="strict", timeout=30,
            check=False)
    except (OSError, subprocess.SubprocessError, UnicodeError) as error:
        raise CollectionError(
            f"could not inspect ELF dependencies: {root_pin['path']}") from error
    if completed.returncode != 0 or completed.stderr != "":
        raise CollectionError(f"ldd failed for {root_pin['path']}")
    parsed, virtual_objects = _parse_ldd_output(
        completed.stdout, root_pin["path"])
    resolved_files = []
    for item in parsed:
        dependency = _pin_elf_file(
            Path(item["reported_path"]).resolve(strict=True),
            item["reported_path"])
        resolved_files.append({**item, **dependency})
    resolved_files.sort(
        key=lambda item: (item["role"], item["reported_path"], item["path"]))
    present_loaders = {
        item["argument_path"]
        for item in oracle["hardcoded_loader_routes"]
        if item["status"] == "present"
    }
    if not any(item["reported_path"] in present_loaders
               for item in resolved_files):
        raise CollectionError(f"ldd omitted the selected loader for {root_pin['path']}")
    return {
        "root": root_pin,
        "argv": argv,
        "environment": dict(ELF_OBSERVER_ENVIRONMENT),
        "return_code": completed.returncode,
        "stdout": completed.stdout,
        "stdout_sha256": hashlib.sha256(completed.stdout.encode()).hexdigest(),
        "normalized_stdout": _normalize_ldd_stdout(
            completed.stdout, root_pin["path"]),
        "normalized_stdout_sha256": hashlib.sha256(
            _normalize_ldd_stdout(
                completed.stdout, root_pin["path"]).encode()).hexdigest(),
        "stderr": completed.stderr,
        "stderr_sha256": hashlib.sha256(completed.stderr.encode()).hexdigest(),
        "resolved_files": resolved_files,
        "virtual_objects": virtual_objects,
    }


def _authenticated_elf_closure(paths):
    requested_paths = sorted({
        str(Path(path).resolve(strict=True)) for path in paths})
    if not requested_paths:
        raise CollectionError("ELF closure requires at least one root")
    oracle = _elf_oracle_inputs()
    requested_roots = [
        _pin_elf_file(path, f"ELF root {path}") for path in requested_paths]
    observation_paths = sorted(set(requested_paths) | {
        oracle["tools"]["bash"]["resolved_executable"]["path"]})
    observations = [
        _observe_elf_root(path, oracle) for path in observation_paths]
    if _elf_oracle_inputs() != oracle:
        raise CollectionError("ELF observer inputs changed during inspection")
    closure_by_path = {}
    for observation in observations:
        for dependency in observation["resolved_files"]:
            pin = {key: dependency[key] for key in ("path", "sha256")}
            previous = closure_by_path.get(pin["path"])
            if previous is not None and previous != pin:
                raise CollectionError("conflicting ELF dependency identities")
            closure_by_path[pin["path"]] = pin
    closure = [closure_by_path[path] for path in sorted(closure_by_path)]
    if ([_pin_elf_file(path, f"ELF root {path}")
         for path in requested_paths] != requested_roots or
            [_pin_elf_file(pin["path"], f"ELF dependency {pin['path']}")
             for pin in closure] != closure):
        raise CollectionError("ELF runtime files changed during inspection")
    present_loader_pins = [
        item["route"]["resolved_executable"]
        for item in oracle["hardcoded_loader_routes"]
        if item["status"] == "present"]
    if (not present_loader_pins or
            any(closure_by_path.get(pin["path"], {}).get("sha256") !=
                pin["sha256"] for pin in present_loader_pins)):
        raise CollectionError("ELF closure does not bind every present loader")
    evidence = {
        "policy": ELF_EVIDENCE_POLICY,
        "output_normalization": ELF_OUTPUT_NORMALIZATION_POLICY,
        **oracle,
        "requested_roots": requested_roots,
        "observations": observations,
        "closure": closure,
    }
    validate_elf_closure_evidence(evidence, requested_paths)
    return evidence


def validate_elf_closure_evidence(evidence, expected_roots=None):
    """Validate retained v8 evidence without consulting live host paths."""
    if not isinstance(evidence, dict) or set(evidence) != {
            "policy", "output_normalization", "tools",
            "hardcoded_loader_routes", "ld_so_cache", "ld_so_preload",
            "environment", "requested_roots",
            "observations", "closure"} or evidence["policy"] != \
            ELF_EVIDENCE_POLICY or evidence["output_normalization"] != \
            ELF_OUTPUT_NORMALIZATION_POLICY:
        raise CollectionError("malformed authenticated ELF evidence")
    tools = evidence["tools"]
    if not isinstance(tools, dict) or set(tools) != {"bash", "ldd"}:
        raise CollectionError("malformed ELF observer tools")
    for name, path in (("bash", ELF_BASH_PATH), ("ldd", ELF_LDD_PATH)):
        _validate_executable_route(tools[name], f"ELF observer {name}")
        if tools[name]["argument_path"] != str(path):
            raise CollectionError(f"unexpected ELF observer {name} path")
    loader_routes = evidence["hardcoded_loader_routes"]
    if (not isinstance(loader_routes, list) or len(loader_routes) !=
            len(ELF_LOADER_PATHS)):
        raise CollectionError("malformed hardcoded loader routes")
    present_loaders = {}
    for expected, value in zip(ELF_LOADER_PATHS, loader_routes):
        if (not isinstance(value, dict) or
                value.get("argument_path") != str(expected) or
                value.get("status") not in {"absent", "present"}):
            raise CollectionError("malformed hardcoded loader route")
        if value["status"] == "absent":
            if set(value) != {"argument_path", "status"}:
                raise CollectionError("malformed absent loader route")
        else:
            if set(value) != {"argument_path", "status", "route"}:
                raise CollectionError("malformed present loader route")
            _validate_executable_route(value["route"], "hardcoded ELF loader")
            if value["route"]["argument_path"] != str(expected):
                raise CollectionError("inconsistent hardcoded loader route")
            present_loaders[str(expected)] = \
                value["route"]["resolved_executable"]
    if not present_loaders:
        raise CollectionError("no hardcoded ELF loader is present")
    cache = evidence["ld_so_cache"]
    if (not isinstance(cache, dict) or set(cache) != {"path", "sha256"} or
            cache["path"] != str(ELF_CACHE_PATH) or
            not _valid_sha256(cache["sha256"])):
        raise CollectionError("malformed dynamic-loader cache pin")
    if evidence["ld_so_preload"] != {
            "path": str(ELF_PRELOAD_PATH), "status": "absent"}:
        raise CollectionError("malformed dynamic-loader preload contract")
    if evidence["environment"] != ELF_OBSERVER_ENVIRONMENT:
        raise CollectionError("ELF observer environment is not exact")

    roots = evidence["requested_roots"]
    if (not isinstance(roots, list) or not roots or
            any(not isinstance(pin, dict) or set(pin) != {"path", "sha256"} or
                not isinstance(pin["path"], str) or
                not Path(pin["path"]).is_absolute() or
                not _valid_sha256(pin["sha256"]) for pin in roots) or
            [pin["path"] for pin in roots] !=
            sorted({pin["path"] for pin in roots})):
        raise CollectionError("malformed ELF requested roots")
    root_paths = [pin["path"] for pin in roots]
    if expected_roots is not None and root_paths != sorted(set(expected_roots)):
        raise CollectionError("ELF requested root set mismatch")
    expected_observation_paths = sorted(set(root_paths) | {
        tools["bash"]["resolved_executable"]["path"]})
    root_by_path = {pin["path"]: pin for pin in roots}
    observations = evidence["observations"]
    if (not isinstance(observations, list) or
            [item.get("root", {}).get("path")
             if isinstance(item, dict) else None for item in observations] !=
            expected_observation_paths):
        raise CollectionError("ELF observation root set mismatch")
    closure_by_path = {}
    for observation in observations:
        if not isinstance(observation, dict) or set(observation) != {
                "root", "argv", "environment", "return_code", "stdout",
                "stdout_sha256", "normalized_stdout",
                "normalized_stdout_sha256", "stderr", "stderr_sha256",
                "resolved_files", "virtual_objects"}:
            raise CollectionError("malformed ELF observation")
        root = observation["root"]
        if (not isinstance(root, dict) or set(root) != {"path", "sha256"} or
                not _valid_sha256(root.get("sha256"))):
            raise CollectionError("malformed ELF observation root")
        if root["path"] in root_by_path and root != root_by_path[root["path"]]:
            raise CollectionError("ELF observation root identity mismatch")
        if (observation["argv"] != [
                str(ELF_BASH_PATH), str(ELF_LDD_PATH), root["path"]] or
                observation["environment"] != ELF_OBSERVER_ENVIRONMENT or
                observation["return_code"] != 0 or
                not isinstance(observation["stdout"], str) or
                hashlib.sha256(observation["stdout"].encode()).hexdigest() !=
                observation["stdout_sha256"] or
                observation["normalized_stdout"] != _normalize_ldd_stdout(
                    observation["stdout"], root["path"]) or
                hashlib.sha256(
                    observation["normalized_stdout"].encode()).hexdigest() !=
                observation["normalized_stdout_sha256"] or
                observation["stderr"] != "" or
                observation["stderr_sha256"] != hashlib.sha256(b"").hexdigest()):
            raise CollectionError("malformed ELF observation process evidence")
        parsed, virtual_objects = _parse_ldd_output(
            observation["stdout"], root["path"])
        resolved = observation["resolved_files"]
        if (not isinstance(resolved, list) or not resolved or
                any(not isinstance(item, dict) or set(item) != {
                    "role", "reported_path", "path", "sha256"} or
                    not isinstance(item["path"], str) or
                    not Path(item["path"]).is_absolute() or
                    not _valid_sha256(item["sha256"]) for item in resolved) or
                [{key: item[key] for key in ("role", "reported_path")}
                 for item in resolved] != parsed or
                resolved != sorted(resolved, key=lambda item: (
                    item["role"], item["reported_path"], item["path"])) or
                observation["virtual_objects"] != virtual_objects):
            raise CollectionError("ELF observation parse projection mismatch")
        loader_records = [
            item for item in resolved if item["reported_path"] in present_loaders]
        if (not loader_records or any(
                item["path"] != present_loaders[item["reported_path"]]["path"] or
                item["sha256"] !=
                present_loaders[item["reported_path"]]["sha256"]
                for item in loader_records)):
            raise CollectionError("ELF observation omitted or changed its loader")
        for item in resolved:
            pin = {key: item[key] for key in ("path", "sha256")}
            previous = closure_by_path.get(pin["path"])
            if previous is not None and previous != pin:
                raise CollectionError("conflicting retained ELF identities")
            closure_by_path[pin["path"]] = pin
    expected_closure = [
        closure_by_path[path] for path in sorted(closure_by_path)]
    if evidence["closure"] != expected_closure:
        raise CollectionError("ELF closure is not the exact sorted union")
    if any(closure_by_path.get(pin["path"]) != {
            "path": pin["path"], "sha256": pin["sha256"]}
           for pin in present_loaders.values()):
        raise CollectionError("ELF closure omitted a hardcoded loader")
    return evidence


def elf_oracle_projection(evidence):
    """Return the plan-independent v8 observer inputs for collection binding."""
    validate_elf_closure_evidence(evidence)
    return {
        key: evidence[key] for key in (
            "policy", "output_normalization", "tools",
            "hardcoded_loader_routes", "ld_so_cache", "ld_so_preload",
            "environment")
    }


def _stable_elf_evidence(evidence):
    """Discard only ASLR-varying raw output when comparing fresh observations."""
    stable = json.loads(json.dumps(evidence))
    for observation in stable["observations"]:
        observation.pop("stdout")
        observation.pop("stdout_sha256")
    return stable


def validate_elf_closure_evidence_live(evidence, expected_roots):
    validate_elf_closure_evidence(evidence, expected_roots)
    observed = _authenticated_elf_closure(expected_roots)
    if _stable_elf_evidence(observed) != _stable_elf_evidence(evidence):
        raise CollectionError("live ELF observer evidence differs from plan")
    return evidence


def _pin_external_runtime(reference_root, pari_gp_root, pari_gp_package,
                          command_shell):
    """Authenticate the exact shell/GP route used by HOL Light's Sys.command."""
    gp_root_argument = Path(os.path.abspath(pari_gp_root))
    try:
        gp_root_metadata = gp_root_argument.lstat()
        gp_root = gp_root_argument.resolve(strict=True)
    except (FileNotFoundError, RuntimeError, OSError) as error:
        raise CollectionError("could not resolve PARI/GP package root") from error
    if (not stat.S_ISDIR(gp_root_metadata.st_mode) or
            gp_root != gp_root_argument):
        raise CollectionError("PARI/GP package root must be a canonical directory")
    gp_bin = gp_root / "usr/bin"
    gp_path = gp_bin / "gp"
    gprc = gp_root / "candle-gprc"
    data_root = gp_root / "candle-data"
    if not gp_bin.is_dir() or gp_bin.is_symlink():
        raise CollectionError("PARI/GP bin path must be an ordinary directory")
    if not data_root.is_dir() or data_root.is_symlink():
        raise CollectionError("PARI/GP data path must be an ordinary directory")
    if stat.S_IMODE(data_root.lstat().st_mode) != 0o555:
        raise CollectionError("PARI/GP data path mode must be exactly 0555")
    data_tree_pin = _pin_tree(data_root)
    if data_tree_pin["entry_count"] != 0:
        raise CollectionError("PARI/GP data path must be empty")
    gprc_pin = _pin_file(gprc)
    if stat.S_IMODE(gprc.lstat().st_mode) != 0o444:
        raise CollectionError("PARI/GP configuration mode must be exactly 0444")
    gp_route = _pin_executable_route(gp_path, "PARI/GP executable")
    if Path(os.path.abspath(command_shell)) != Path("/bin/sh"):
        raise CollectionError("Sys.command shell argument must be exactly /bin/sh")
    shell_route = _pin_executable_route(command_shell, "Sys.command shell")
    package_argument = Path(os.path.abspath(pari_gp_package))
    try:
        package_metadata = package_argument.lstat()
        package_resolved = package_argument.resolve(strict=True)
    except (FileNotFoundError, RuntimeError, OSError) as error:
        raise CollectionError("could not resolve PARI/GP package archive") from error
    if (not stat.S_ISREG(package_metadata.st_mode) or
            package_resolved != package_argument or
            stat.S_IMODE(package_metadata.st_mode) != 0o444):
        raise CollectionError(
            "PARI/GP package archive must be a canonical 0444 regular file")
    package_pin = _pin_file(package_argument)
    environment = {
        "HOME": str(Path(reference_root).resolve(strict=True)),
        "PATH": str(gp_bin),
        "LC_ALL": "C",
        "GPRC": gprc_pin["path"],
        "GP_DATA_DIR": str(data_root),
    }
    version = subprocess.run(
        [gp_route["argument_path"], "--version-short"],
        env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, timeout=30, check=False,
    )
    if (version.returncode != 0 or version.stderr != "" or
            re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+\n", version.stdout) is None):
        raise CollectionError("could not obtain exact PARI/GP version")
    probe = subprocess.run(
        [shell_route["argument_path"], "-c", PARI_GP_PROBE_SOURCE],
        env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, timeout=30, check=False,
    )
    expected_gprc_stderr = (
        f"Reading GPRC: {gprc_pin['path']}\nGPRC Done.\n\n")
    if (probe.returncode != 0 or
            probe.stderr not in {"", expected_gprc_stderr} or
            re.search(r"(?:^|\n)1\n", probe.stdout) is None or
            "[3, 1; 5, 1]" not in probe.stdout):
        raise CollectionError(
            "PARI/GP single-thread shell-route factor probe failed")
    return {
        "policy": "single_private_path_gp_with_pinned_shell_v2",
        "command_shell": shell_route,
        "pari_gp": gp_route,
        "pari_gp_version": {
            "stdout": version.stdout,
            "sha256": hashlib.sha256(version.stdout.encode()).hexdigest(),
        },
        "package_archive": package_pin,
        "package_tree": _pin_tree(gp_root),
        "configuration": gprc_pin,
        "data_tree": data_tree_pin,
        "elf_runtime": _authenticated_elf_closure([
            shell_route["resolved_executable"]["path"],
            gp_route["resolved_executable"]["path"],
        ]),
        "probe": {
            "shell_argv": [
                shell_route["argument_path"], "-c", PARI_GP_PROBE_SOURCE],
            "environment": environment,
            "return_code": probe.returncode,
            "stdout": probe.stdout,
            "stdout_sha256": hashlib.sha256(probe.stdout.encode()).hexdigest(),
            "stderr": probe.stderr,
            "stderr_sha256": hashlib.sha256(probe.stderr.encode()).hexdigest(),
        },
    }


def validate_external_runtime_provenance(external, reference_root,
                                         runtime_environment):
    """Validate the closed, non-live v8 shell/GP provenance projection."""
    if not isinstance(external, dict) or set(external) != {
            "policy", "command_shell", "pari_gp", "pari_gp_version",
            "package_archive", "package_tree", "configuration", "data_tree",
            "elf_runtime", "probe"} or external["policy"] != \
            "single_private_path_gp_with_pinned_shell_v2":
        raise CollectionError("malformed external-runtime provenance")

    for label in ("command_shell", "pari_gp"):
        route = external[label]
        _validate_executable_route(route, f"external {label}")

    version = external["pari_gp_version"]
    if (not isinstance(version, dict) or set(version) != {"stdout", "sha256"} or
            not isinstance(version["stdout"], str) or
            re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+\n", version["stdout"]) is None or
            hashlib.sha256(version["stdout"].encode()).hexdigest() !=
            version["sha256"]):
        raise CollectionError("malformed external PARI/GP version")
    for label in ("package_archive", "configuration"):
        value = external[label]
        if (not isinstance(value, dict) or set(value) != {"path", "sha256"} or
                not isinstance(value["path"], str) or
                not Path(value["path"]).is_absolute() or
                not _valid_sha256(value["sha256"])):
            raise CollectionError(f"malformed external {label}")
    for label in ("package_tree", "data_tree"):
        value = external[label]
        if (not isinstance(value, dict) or set(value) != {
                "root", "root_mode", "entry_count", "inventory_sha256",
                "inventory_policy"} or
                not isinstance(value["root"], str) or
                not Path(value["root"]).is_absolute() or
                type(value["root_mode"]) is not int or
                type(value["entry_count"]) is not int or
                value["entry_count"] < 0 or
                not _valid_sha256(value["inventory_sha256"]) or
                value["inventory_policy"] !=
                "relative_path_kind_mode_link_target_and_content_v1"):
            raise CollectionError(f"malformed external {label}")
    package_root = Path(external["package_tree"]["root"])
    if (external["command_shell"]["argument_path"] != "/bin/sh" or
            external["pari_gp"]["argument_path"] !=
            str(package_root / "usr/bin/gp") or
            external["configuration"]["path"] !=
            str(package_root / "candle-gprc") or
            external["data_tree"]["root"] !=
            str(package_root / "candle-data") or
            external["data_tree"]["root_mode"] != 0o555 or
            external["data_tree"]["entry_count"] != 0):
        raise CollectionError("external PARI/GP package path contract mismatch")
    external_elf_roots = sorted(({
        key: external[label]["resolved_executable"][key]
        for key in ("path", "sha256")}
        for label in ("command_shell", "pari_gp")),
        key=lambda item: item["path"])
    validate_elf_closure_evidence(
        external["elf_runtime"],
        [item["path"] for item in external_elf_roots])
    if external["elf_runtime"]["requested_roots"] != external_elf_roots:
        raise CollectionError("external ELF roots differ from executable pins")
    probe = external["probe"]
    expected_environment = {
        "HOME": str(reference_root),
        "PATH": str(package_root / "usr/bin"),
        "LC_ALL": "C",
        "GPRC": str(package_root / "candle-gprc"),
        "GP_DATA_DIR": str(package_root / "candle-data"),
    }
    expected_stderr = (
        f"Reading GPRC: {expected_environment['GPRC']}\nGPRC Done.\n\n")
    if (not isinstance(probe, dict) or set(probe) != {
            "shell_argv", "environment", "return_code", "stdout",
            "stdout_sha256", "stderr", "stderr_sha256"} or
            probe["shell_argv"] != [
                "/bin/sh", "-c", PARI_GP_PROBE_SOURCE] or
            probe["environment"] != expected_environment or
            probe["return_code"] != 0 or
            not isinstance(probe["stdout"], str) or
            re.search(r"(?:^|\n)1\n", probe["stdout"]) is None or
            "[3, 1; 5, 1]" not in probe["stdout"] or
            hashlib.sha256(probe["stdout"].encode()).hexdigest() !=
            probe["stdout_sha256"] or
            probe["stderr"] not in {"", expected_stderr} or
            hashlib.sha256(probe["stderr"].encode()).hexdigest() !=
            probe["stderr_sha256"]):
        raise CollectionError("malformed external PARI/GP probe")
    if (not isinstance(runtime_environment, dict) or
            set(runtime_environment) != RUNTIME_ENVIRONMENT_KEYS or
            any(runtime_environment.get(key) != value
                for key, value in expected_environment.items())):
        raise CollectionError("runtime environment differs from exact allowlist")
    expected_internal_environment = {
        "HOLLIGHT_DIR": str(reference_root),
        "HOLLIGHT_USE_MODULE": "0",
        "OCAMLRUNPARAM": "l=2000000000",
    }
    if any(runtime_environment.get(key) != value
           for key, value in expected_internal_environment.items()):
        raise CollectionError("runtime environment has malformed HOL pins")
    for key in ("CAML_LD_LIBRARY_PATH", "OCAML_TOPLEVEL_PATH",
                "OCAMLFIND_CONF"):
        value = runtime_environment.get(key)
        if not isinstance(value, str) or not Path(value).is_absolute():
            raise CollectionError("runtime environment has non-absolute OCaml pin")
    return external


def validate_reference_runtime_provenance(plan):
    """Validate the complete non-live HOL/OCaml fresh-process projection."""
    if not isinstance(plan, dict) or set(plan) != {
            "schema", "status", "session_nonce", "fresh_process_contract",
            "reference", "input", "request"}:
        raise CollectionError("malformed reference plan fields")
    reference_root = plan["reference"].get("root") \
        if isinstance(plan.get("reference"), dict) else None
    if (not isinstance(reference_root, str) or
            not Path(reference_root).is_absolute()):
        raise CollectionError("malformed reference root")
    reference = plan["reference"]
    if set(reference) != {
            "root", "git_head", "git_status", "runtime_executable",
            "runtime_interpreter", "runtime_stublib", "runtime_library_tree",
            "runtime_stub_files", "elf_runtime", "ocamlc", "findlib",
            "hol_ml", "generated_boot_files", "ocaml_library_tree",
            "external_runtime"}:
        raise CollectionError("malformed reference runtime fields")

    def file_pin(value, label):
        if (not isinstance(value, dict) or set(value) != {"path", "sha256"} or
                not isinstance(value["path"], str) or
                not Path(value["path"]).is_absolute() or
                re.fullmatch(r"[0-9a-f]{64}", value["sha256"]) is None):
            raise CollectionError(f"malformed {label} file pin")

    def tree_pin(value, label):
        if (not isinstance(value, dict) or set(value) != {
                "root", "root_mode", "entry_count", "inventory_sha256",
                "inventory_policy"} or
                not isinstance(value["root"], str) or
                not Path(value["root"]).is_absolute() or
                type(value["root_mode"]) is not int or
                type(value["entry_count"]) is not int or
                value["entry_count"] < 0 or
                re.fullmatch(r"[0-9a-f]{64}",
                             value["inventory_sha256"]) is None or
                value["inventory_policy"] !=
                "relative_path_kind_mode_link_target_and_content_v1"):
            raise CollectionError(f"malformed {label} tree pin")

    for key in ("runtime_executable", "runtime_interpreter", "runtime_stublib",
                "hol_ml"):
        file_pin(reference[key], key.replace("_", " "))
    for key in ("runtime_library_tree", "ocaml_library_tree"):
        tree_pin(reference[key], key.replace("_", " "))
    for key in ("runtime_stub_files",):
        values = reference[key]
        if not isinstance(values, list) or not values:
            raise CollectionError(f"empty reference {key.replace('_', ' ')}")
        for value in values:
            file_pin(value, key.replace("_", " "))
        paths = [value["path"] for value in values]
        if paths != sorted(set(paths)):
            raise CollectionError(
                f"reference {key.replace('_', ' ')} is not unique and sorted")
    reference_elf_roots = sorted((
        reference["runtime_interpreter"],
        *reference["runtime_stub_files"]), key=lambda item: item["path"])
    validate_elf_closure_evidence(
        reference["elf_runtime"],
        [item["path"] for item in reference_elf_roots])
    if reference["elf_runtime"]["requested_roots"] != reference_elf_roots:
        raise CollectionError("reference ELF roots differ from runtime pins")
    if (reference["runtime_library_tree"]["root"] !=
            str(Path(reference["runtime_stublib"]["path"]).parent) or
            not all(Path(value["path"]).parent ==
                    Path(reference["runtime_library_tree"]["root"])
                    or Path(value["path"]).parent.name == "stublibs"
                    for value in reference["runtime_stub_files"])):
        raise CollectionError("reference runtime stub closure mismatch")

    ocamlc = reference["ocamlc"]
    if (not isinstance(ocamlc, dict) or set(ocamlc) != {
            "path", "sha256", "version", "stdlib_directory"}):
        raise CollectionError("malformed OCaml compiler provenance")
    file_pin({key: ocamlc[key] for key in ("path", "sha256")}, "OCaml compiler")
    if (not isinstance(ocamlc["version"], str) or not ocamlc["version"] or
            not isinstance(ocamlc["stdlib_directory"], str) or
            not Path(ocamlc["stdlib_directory"]).is_absolute()):
        raise CollectionError("malformed OCaml compiler metadata")
    findlib = reference["findlib"]
    if (not isinstance(findlib, dict) or set(findlib) != {
            "executable", "version", "configuration", "package_roots"}):
        raise CollectionError("malformed findlib provenance")
    file_pin(findlib["executable"], "findlib executable")
    file_pin(findlib["configuration"], "findlib configuration")
    if not isinstance(findlib["version"], str) or not findlib["version"]:
        raise CollectionError("malformed findlib version")
    package_roots = findlib["package_roots"]
    if not isinstance(package_roots, list) or not package_roots:
        raise CollectionError("empty findlib package roots")
    for root in package_roots:
        tree_pin(root, "findlib package root")
    if ([root["root"] for root in package_roots] !=
            sorted({root["root"] for root in package_roots}) or
            reference["ocaml_library_tree"] not in package_roots):
        raise CollectionError("findlib package roots are inconsistent")
    boot_files = reference["generated_boot_files"]
    expected_boots = [
        str(Path(reference_root) / "hol_loader.cmo"),
        str(Path(reference_root) / "pa_j.cmo"),
        str(Path(reference_root) / "load_camlp5_topfind.ml"),
    ]
    if not isinstance(boot_files, list) or len(boot_files) != 3:
        raise CollectionError("malformed generated boot-file provenance")
    for value in boot_files:
        file_pin(value, "generated boot")
    if [value["path"] for value in boot_files] != expected_boots:
        raise CollectionError("generated boot-file set mismatch")

    fresh = plan["fresh_process_contract"]
    if (not isinstance(fresh, dict) or set(fresh) != {
            "required", "preloaded_checkpoint_allowed", "working_directory",
            "environment_policy", "runtime_argv", "runtime_environment"} or
            fresh["required"] is not True or
            fresh["preloaded_checkpoint_allowed"] is not False or
            fresh["working_directory"] != reference_root or
            fresh["environment_policy"] !=
            "sanitized_allowlist_no_inherited_overrides" or
            fresh["runtime_argv"] != [
                reference["runtime_executable"]["path"], "-init",
                reference["hol_ml"]["path"], "-I", reference_root,
                "-noprompt"]):
        raise CollectionError("malformed fresh-process runtime contract")
    environment = fresh["runtime_environment"]
    validate_external_runtime_provenance(
        reference["external_runtime"], reference_root, environment)
    if (environment["CAML_LD_LIBRARY_PATH"] !=
            reference["runtime_library_tree"]["root"] or
            environment["OCAML_TOPLEVEL_PATH"] != ocamlc["stdlib_directory"] or
            environment["OCAMLFIND_CONF"] != findlib["configuration"]["path"]):
        raise CollectionError("fresh-process OCaml environment mismatch")
    return plan


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
    support_path = ROOT / REFERENCE_PROTOCOL_RELATIVE
    support_committed = subprocess.check_output([
        "git", "-C", str(ROOT), "show",
        f"{head}:{REFERENCE_PROTOCOL_RELATIVE}"])
    support_committed_sha256 = hashlib.sha256(support_committed).hexdigest()
    support_working_sha256 = _sha256(support_path)
    return {
        "root": str(ROOT), "git_head": head,
        "git_status": status.splitlines() if status else [],
        "collector_relative_path": relative,
        "collector_at_head_sha256": committed_sha256,
        "collector_matches_head": committed_sha256 == working_sha256,
        "support_relative_path": REFERENCE_PROTOCOL_RELATIVE,
        "support_at_head_sha256": support_committed_sha256,
        "support_matches_head": (
            support_committed_sha256 == support_working_sha256 ==
            REFERENCE_PROTOCOL_SHA256),
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
               ocamlfind, pari_gp_root, pari_gp_package, command_shell,
               nonce=None, source_mode="manifest-exact"):
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
    elf_runtime = _authenticated_elf_closure([
        runtime_interpreter_pin["path"],
        *(pin["path"] for pin in runtime_stub_files),
    ])
    collector_repository = _collector_repository_pin()
    external_runtime = _pin_external_runtime(
        reference_root, pari_gp_root, pari_gp_package, command_shell)
    runtime_environment = {
        "HOME": str(reference_root),
        "PATH": external_runtime["probe"]["environment"]["PATH"],
        "LC_ALL": "C",
        "GPRC": external_runtime["configuration"]["path"],
        "GP_DATA_DIR": external_runtime["data_tree"]["root"],
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
            "elf_runtime": elf_runtime,
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
            "external_runtime": external_runtime,
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
    reference = dict(plan["reference"])
    reference["elf_runtime"] = _stable_elf_evidence(
        reference["elf_runtime"])
    external = dict(reference["external_runtime"])
    external["elf_runtime"] = _stable_elf_evidence(
        external["elf_runtime"])
    reference["external_runtime"] = external
    return {
        "reference": reference,
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
        plan["reference"]["external_runtime"]["package_tree"]["root"],
        plan["reference"]["external_runtime"]["package_archive"]["path"],
        plan["reference"]["external_runtime"]["command_shell"]["argument_path"],
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
        try:
            validate_reference_runtime_provenance(plan)
        except (KeyError, TypeError) as error:
            raise CollectionError(
                "malformed external-runtime plan binding") from error
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
        sub.add_argument("--pari-gp-root", type=Path, required=True)
        sub.add_argument("--pari-gp-package", type=Path, required=True)
        sub.add_argument("--command-shell", type=Path, required=True)
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
            args.pari_gp_root, args.pari_gp_package, args.command_shell,
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
