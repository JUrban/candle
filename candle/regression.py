"""
!!! Large amount of LLM generated code !!!

Parallel regression test runner for Candle.

Each test runs in its own fresh Candle process that loads hol.ml and then the
test file(s). There is no checkpointing (no criu/DMTCP, no sudo): running one
process per test, up to -j at a time, is what hides the cost of reloading
hol.ml for every test.

The Candle REPL transcript for each test is written to its own log.  Without a
report or explicit --log-dir this remains a temporary file under /tmp.  A JSON
report retains logs in a sibling directory by default.

Two suites are available:
  * REGRESSION - a small subset, run by default.
  * TOP100     - the full "Top 100 theorems" set (from holtest.mk's
                 GREAT_100_THEOREMS), run with --top100.

Each result includes wall time and sampled peak RSS.  Pass --json-report PATH
to preserve the complete per-test table, exact source/executable identity, and
per-target logs.  --log-dir can select a different persistent log directory.

Timeouts have two independent meanings.  The inactivity timeout is reset by
each complete REPL output line.  An optional total wall timeout is an
absolute per-target deadline from process spawn through fingerprint capture;
progress never extends it.
"""
import sys
import os
import time
import argparse
import hashlib
import json
import re
import secrets
import signal
import subprocess
import tempfile
import threading
import concurrent.futures
from dataclasses import dataclass
from datetime import datetime, timezone
from enum import Enum
from pathlib import Path

import pexpect

# <root>/candle/regression.py
CANDLE_ROOT = Path(__file__).resolve().parent.parent

# The Top 100 suite needs a larger CakeML heap than the build's default.
# Set via CML_HEAP_SIZE (MB) per candle process; parallelism is capped so the
# combined heap reservation stays within available memory.
TOP100_HEAP_MB = 6000


def _reject_duplicate_json_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result

# ---------------------------------------------------------------------------
# Exceptions
# ---------------------------------------------------------------------------

class StartFailure(Exception):
    """Starting Candle failed (pre-boot)."""


class BootFailure(Exception):
    """Booting Candle failed (pre-boot)."""


class LoadFailure(Exception):
    """Loading a file failed."""


class RunnerTimeout(Exception):
    """Base class for an explicitly classified runner timeout."""


class InactivityTimeout(RunnerTimeout):
    """No recognized REPL progress arrived within the inactivity limit."""


class WallTimeout(RunnerTimeout):
    """The total process/target wall deadline expired."""


def _effective_expect_timeout(inactivity_timeout, wall_deadline, now=None):
    """Return (pexpect timeout, wall-limited) without extending wall time."""
    if inactivity_timeout <= 0:
        raise ValueError("inactivity timeout must be positive")
    if wall_deadline is None:
        return float(inactivity_timeout), False
    if now is None:
        now = time.monotonic()
    wall_remaining = wall_deadline - now
    if wall_remaining <= 0:
        raise WallTimeout("total wall deadline expired")
    if wall_remaining <= inactivity_timeout:
        return wall_remaining, True
    return float(inactivity_timeout), False


def _timeout_policy(inactivity_timeout, wall_timeout):
    """Return the machine-readable timeout contract used by a suite run."""
    return {
        "inactivity_timeout_seconds": inactivity_timeout,
        "inactivity_resets_on": (
            "each complete REPL output line"),
        "inactivity_scope": "each REPL expect wait, including initial boot",
        "total_wall_timeout_seconds": wall_timeout,
        "total_wall_scope": "process spawn through fingerprint capture",
        "progress_extends_total_wall_deadline": False,
    }


# ---------------------------------------------------------------------------
# Test definitions
# ---------------------------------------------------------------------------

class TestStatus(Enum):
    PASS = "PASS"
    FAIL = "FAIL"
    TIMEOUT = "TIMEOUT"


@dataclass(frozen=True)
class Test:
    """A named test, defined by the file(s) it loads (in order) on top of hol.ml."""
    name: str
    files: tuple
    fingerprint_theorems: tuple = ()
    fingerprint_mapping_status: str | None = None
    fingerprint_expected_identities: dict | None = None


def _t(name, *files):
    """Build a Test. With no explicit files, loads "<name>.ml"."""
    return Test(name, files if files else (f"{name}.ml",))


# The default regression subset.
REGRESSION = [
    _t("100/arithmetic"),
    _t("100/cantor"),
    _t("100/konigsberg"),
    _t("100/gcd"),
    _t("100/wilson"),
    _t("100/combinations"),
    _t("100/ratcountable"),
    _t("100/euler"),
    _t("100/lhopital"),
    _t("100/stirling"),
    _t("100/liouville"),
    _t("100/cayley_hamilton"),
]

def _load_top100_manifest():
    """Load the audited suite inventory and reject any hidden skip."""
    path = CANDLE_ROOT / "candle" / "top100_manifest.json"
    payload = json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=_reject_duplicate_json_keys)
    if payload.get("schema_version") != 1:
        raise ValueError(f"unsupported Great 100 manifest schema: {path}")
    targets = payload.get("targets", [])
    if payload.get("target_count") != len(targets):
        raise ValueError(f"Great 100 target_count does not match targets: {path}")
    covered = {source for target in targets for source in target["load_files"]}
    requests = sum(len(target["fingerprint_request"]["theorems"])
                   for target in targets)
    if (len(targets), len(covered), requests) != (65, 66, 97):
        raise ValueError("Great 100 manifest is not the canonical 65/66/97 inventory")
    inventory = payload.get("inventory_contract")
    if not isinstance(inventory, dict) or (
            inventory.get("target_count"),
            inventory.get("covered_source_count"),
            inventory.get("theorem_request_count")) != (65, 66, 97):
        raise ValueError("Great 100 inventory contract is malformed")
    if any(target.get("skip") is not None for target in targets):
        raise ValueError(f"Great 100 manifest contains a skipped target: {path}")
    tests = []
    for target in targets:
        request = target.get("fingerprint_request")
        if not request:
            raise ValueError(
                f"Great 100 target has no fingerprint request: {target['name']}")
        theorem_names = tuple(item["name"] for item in request["theorems"])
        if set(target.get("load_file_sha256", {})) != set(target["load_files"]):
            raise ValueError(f"Great 100 source hash set mismatch: {target['name']}")
        for source in target["load_files"]:
            source_path = CANDLE_ROOT / source
            if source_path.is_symlink() or not source_path.is_file():
                raise ValueError(f"unsafe Great 100 source: {source}")
            try:
                source_path.resolve(strict=True).relative_to(
                    CANDLE_ROOT.resolve(strict=True))
            except ValueError as error:
                raise ValueError(f"Great 100 source escapes root: {source}") from error
            if hashlib.sha256(source_path.read_bytes()).hexdigest() != \
                    target["load_file_sha256"][source]:
                raise ValueError(f"Great 100 source hash mismatch: {source}")
        tests.append(Test(
            target["name"], tuple(target["load_files"]), theorem_names,
            request["mapping_status"], request.get("expected_identities")))
    return tests


# The machine-readable manifest is generated from GREAT_100_THEOREMS and also
# records dependencies, exclusions, and missing fingerprint/resource evidence.
TOP100 = _load_top100_manifest()

# Lookup by name, so --test can reuse multi-file definitions (e.g. the
# bertrand-primerecip pairing) rather than always assuming "<name>.ml".
BY_NAME = {t.name: t for t in TOP100}

LINKED_RECORD_PATH = CANDLE_ROOT / "candle/build/cakeml-build-provenance.json"
APPROVAL_PATH = CANDLE_ROOT / "candle/top100_identity_approval.json"
EXECUTION_CONTRACT_PATHS = (
    "candle/cakeml_artifact_provenance.py",
    "candle/regression.py",
    "candle/top100_manifest.json",
    "candle/fingerprint.ml",
    "candle.sh",
)


def _sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def _ordinary_file_record(path, display_path=None):
    path = Path(path)
    metadata = path.lstat()
    if path.is_symlink() or not path.is_file() or metadata.st_nlink != 1:
        raise ValueError(f"retained input is not an ordinary file: {path}")
    data = path.read_bytes()
    if path.lstat().st_ino != metadata.st_ino or path.lstat().st_dev != metadata.st_dev:
        raise ValueError(f"retained input changed while hashing: {path}")
    return {
        "path": str(display_path if display_path is not None else path.resolve()),
        "bytes": len(data),
        "sha256": _sha256_bytes(data),
    }


def _canonical_digest(value):
    return _sha256_bytes(json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
    ).encode("ascii"))


def _git_state():
    head = subprocess.check_output(
        ["/usr/bin/git", "-C", str(CANDLE_ROOT), "rev-parse", "HEAD"],
        text=True, env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"}).strip()
    status = subprocess.check_output(
        ["/usr/bin/git", "-C", str(CANDLE_ROOT), "status", "--porcelain=v1",
         "--untracked-files=all"], text=True,
        env={"PATH": "/usr/bin:/bin", "LC_ALL": "C"}).splitlines()
    if not re.fullmatch(r"[0-9a-f]{40}", head):
        raise ValueError("Candle Git HEAD is not a full SHA-1")
    return head, status


def _source_closure(manifest):
    targets = manifest["targets"]
    ordered_targets = [{
        "name": target["name"],
        "load_files": list(target["load_files"]),
        "theorem_names": [
            theorem["name"]
            for theorem in target["fingerprint_request"]["theorems"]
        ],
    } for target in targets]
    ordered_paths = []
    for target in targets:
        for source in target["load_files"]:
            if source not in ordered_paths:
                ordered_paths.append(source)
    files = [_ordinary_file_record(CANDLE_ROOT / source, source)
             for source in ordered_paths]
    closure = {
        "target_count": len(targets),
        "source_file_count": len(files),
        "fingerprint_request_count": sum(
            len(target["fingerprint_request"]["theorems"])
            for target in targets),
        "ordered_targets": ordered_targets,
        "files": files,
    }
    if (closure["target_count"], closure["source_file_count"],
            closure["fingerprint_request_count"]) != (65, 66, 97):
        raise ValueError("Great 100 source closure is not canonical 65/66/97")
    closure["sha256"] = _canonical_digest(closure)
    return closure


def _capture_suite_contract(require_approved=True):
    head, status = _git_state()
    if status:
        raise ValueError("promotable Great 100 execution requires a clean Git tree")
    manifest_path = CANDLE_ROOT / "candle/top100_manifest.json"
    manifest = json.loads(
        manifest_path.read_text(encoding="utf-8"),
        object_pairs_hook=_reject_duplicate_json_keys)
    execution_contract = {
        relative: {
            key: value for key, value in
            _ordinary_file_record(CANDLE_ROOT / relative, relative).items()
            if key != "path"
        }
        for relative in EXECUTION_CONTRACT_PATHS
    }
    approval = _ordinary_file_record(
        APPROVAL_PATH, APPROVAL_PATH.relative_to(CANDLE_ROOT).as_posix())
    approval_payload = json.loads(
        APPROVAL_PATH.read_text(encoding="utf-8"),
        object_pairs_hook=_reject_duplicate_json_keys)
    manifest_approval = manifest.get("identity_approval", {})
    if (manifest_approval.get("sha256") != approval["sha256"] or
            manifest_approval.get("approval_status") !=
            approval_payload.get("approval_status") or
            manifest_approval.get("promotion_allowed") is not
            approval_payload.get("promotion_allowed")):
        raise ValueError("manifest and identity approval artifact disagree")
    if require_approved and (
            approval_payload.get("approval_status") != "approved" or
            approval_payload.get("promotion_allowed") is not True or
            any(target["fingerprint_request"].get("expected_identities") is None
                for target in manifest["targets"])):
        raise ValueError("Great 100 identities are not independently approved")
    if require_approved:
        serializer_sha256 = execution_contract["candle/fingerprint.ml"]["sha256"]
        for target in manifest["targets"]:
            expected = target["fingerprint_request"]["expected_identities"]
            if (not isinstance(expected, dict) or
                    expected.get("approval_sha256") != approval["sha256"] or
                    expected.get("serializer_sha256") != serializer_sha256):
                raise ValueError(
                    f"Great 100 expected identity provenance mismatch: "
                    f"{target['name']}")
    linked = _ordinary_file_record(
        LINKED_RECORD_PATH,
        LINKED_RECORD_PATH.relative_to(CANDLE_ROOT).as_posix())
    linked_payload = json.loads(
        LINKED_RECORD_PATH.read_text(encoding="utf-8"),
        object_pairs_hook=_reject_duplicate_json_keys)
    if (linked_payload.get("schema") != 6 or
            linked_payload.get("candle_commit") != head):
        raise ValueError("linked schema-6 record does not bind clean Candle HEAD")
    executable = _ordinary_file_record(CANDLE_ROOT / "candle/build/cake")
    source_closure = _source_closure(manifest)
    return {
        "candle_git_head": head,
        "candle_git_status": [],
        "execution_contract": execution_contract,
        "execution_contract_sha256": _canonical_digest(execution_contract),
        "source_closure": source_closure,
        "independent_approval": approval,
        "linked_record": linked,
        "candle_executable": executable,
    }


def _runtime_state(contract):
    current = _capture_suite_contract(require_approved=True)
    for field in (
            "candle_git_head", "candle_git_status", "execution_contract",
            "execution_contract_sha256", "source_closure",
            "independent_approval", "linked_record", "candle_executable"):
        if current[field] != contract[field]:
            raise ValueError(f"Great 100 runtime input changed: {field}")
    return {
        "candle_git_head": current["candle_git_head"],
        "candle_git_status": current["candle_git_status"],
        "linked_record_sha256": current["linked_record"]["sha256"],
        "candle_executable": current["candle_executable"],
        "execution_contract_sha256": current["execution_contract_sha256"],
        "source_closure_sha256": current["source_closure"]["sha256"],
    }


# ---------------------------------------------------------------------------
# CandleREPL
# ---------------------------------------------------------------------------

class CandleREPL:
    def __init__(self, logfile, inactivity_timeout, wall_deadline, env=None):
        self._logfile = logfile
        self.inactivity_timeout = inactivity_timeout
        self.wall_deadline = wall_deadline
        self.load_stack = []
        self.last_val = None

        try:
            self.process = pexpect.spawn(
                str(CANDLE_ROOT / "candle.sh"),
                encoding="utf-8",
                logfile=logfile,
                cwd=str(CANDLE_ROOT),
                env=env,
            )
        except Exception as e:
            raise StartFailure from e

        try:
            self._check_boot()
        except (BootFailure, RunnerTimeout):
            self.kill()
            raise

    def _check_boot(self):
        timeout, wall_limited = _effective_expect_timeout(
            self.inactivity_timeout, self.wall_deadline)
        try:
            index = self.process.expect([
                r'\n# ',
                r'\n(ERROR: .+)',
                pexpect.TIMEOUT,
                pexpect.EOF,
            ], timeout=timeout)
        except Exception as e:
            raise BootFailure from e

        if index == 0:
            return
        if index == 1:
            raise BootFailure(str(self._get_match(1)))
        if index == 2:
            if wall_limited:
                raise WallTimeout("total wall deadline expired while booting")
            raise InactivityTimeout("no REPL output while booting")
        if index == 3:
            raise BootFailure("Process exited unexpectedly")
        assert False, "Unreachable: unexpected boot pattern"

    def _get_match(self, idx):
        return self.process.match.group(idx)

    def load_stack_str(self):
        return f"[while loading: {' > '.join(self.load_stack)}]"

    def _check_output(self):
        while True:
            timeout, wall_limited = _effective_expect_timeout(
                self.inactivity_timeout, self.wall_deadline)
            try:
                index = self.process.expect([
                    r'(?:^|\n)\- Loading (\S+)',
                    r'(?:^|\n)val (\w+) =',
                    r'(?:^|\n)(ERROR: .+)',
                    r'(?:^|\n)(Parsing failed)',
                    r'(?:^|\n)(EXCEPTION: .+)',
                    r'(?:^|\n)\- Finished loading (\S+)',
                    # Semantic sentinels take priority at the same position.
                    # Consume any other complete line as progress, bounding
                    # the unmatched buffer and restarting inactivity only.
                    # Recomputing the timeout preserves the absolute wall
                    # deadline across every progress line.
                    r'(?:^|\n)[^\n]*\n',
                    pexpect.TIMEOUT,
                    pexpect.EOF,
                ], timeout=timeout)
            except Exception as e:
                raise LoadFailure from e

            match index:
                case 0:
                    dependency = self._get_match(1)
                    self.load_stack.append(dependency)
                    return
                case 1:
                    self.last_val = self._get_match(1)
                    return
                case 2 | 3 | 4:
                    raise LoadFailure(self._get_match(1))
                case 5:
                    finished = self._get_match(1)
                    expected = self.load_stack.pop()
                    assert finished == expected, (
                        f"Expected to finish loading {expected}. Actual: {finished}")
                    return
                case 6:
                    continue
                case 7:
                    if wall_limited:
                        raise WallTimeout(
                            "total wall deadline expired while loading")
                    raise InactivityTimeout(
                        "no complete REPL output while loading")
                case 8:
                    raise LoadFailure("Process exited unexpectedly")
                case _:
                    assert False, (
                        "Unreachable: Did you add a new case in _check_output?")

    def load(self, file):
        self.process.sendline(f'#use "{file}";;')
        self._check_output()

        while self.load_stack:
            self._check_output()

    def finish(self):
        """Request an ordinary zero exit and return the observed exit status."""
        timeout, wall_limited = _effective_expect_timeout(
            self.inactivity_timeout, self.wall_deadline)
        self.process.sendline("exit 0;;")
        index = self.process.expect([pexpect.EOF, pexpect.TIMEOUT], timeout=timeout)
        if index == 1:
            if wall_limited:
                raise WallTimeout("total wall deadline expired while exiting")
            raise InactivityTimeout("Candle did not exit after completion")
        self.process.close()
        if self.process.exitstatus != 0:
            raise LoadFailure(
                f"Candle completed but exited with status {self.process.exitstatus}")
        return self.process.exitstatus

    def kill(self):
        # pexpect makes candle.sh a session/process-group leader and cake stays
        # in that foreground group.  Kill the verified isolated group so a
        # timed-out cake child cannot outlive its shell.  Never target a group
        # that is not rooted at the pexpect child.
        pid = self.process.pid
        try:
            if os.getpgid(pid) == pid and os.getsid(pid) == pid:
                os.killpg(pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass
        try:
            self.process.close(force=True)
        except (OSError, pexpect.ExceptionPexpect):
            pass


# ---------------------------------------------------------------------------
# Canonical theorem fingerprint requests
# ---------------------------------------------------------------------------

FINGERPRINT_MARKER = "CANDLE_FINGERPRINT_V2"
STATE_FINGERPRINT_MARKER = "CANDLE_STATE_FINGERPRINT_V2"
SUITE_MARKER = "CANDLE_GREAT100_SUITE_V1"
PROCESS_MARKER = "CANDLE_GREAT100_PROCESS_V1"
LINKED_RECORD_MARKER = "CANDLE_LINKED_PROVENANCE_V1"
FINGERPRINT_HELPER = CANDLE_ROOT / "candle" / "fingerprint.ml"
OCAML_VALUE_PATH_RE = re.compile(
    r"^[A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9_']*)*$")


def _fingerprint_request_source(theorem_names, suite_nonce=None,
                                process_nonce=None):
    lines = []
    for name in theorem_names:
        if not OCAML_VALUE_PATH_RE.fullmatch(name):
            raise ValueError(f"unsafe theorem value path in manifest: {name!r}")
        lines.append(f'candle_s1_emit_fingerprint "{name}" {name};;')
    lines.append("candle_s1_emit_state_fingerprint ();;")
    if suite_nonce is not None or process_nonce is not None:
        if (not re.fullmatch(r"[0-9a-f]{64}", suite_nonce or "") or
                not re.fullmatch(r"[0-9a-f]{64}", process_nonce or "")):
            raise ValueError("invalid Great 100 process marker nonce")
        marker = f"{PROCESS_MARKER}\t{suite_nonce}\t{process_nonce}\tCOMPLETE"
        lines.append(f"print_endline ({json.dumps(marker)});;")
    return "\n".join(lines) + "\n"


def _decode_fingerprint_hex(field, label):
    """Decode one fail-closed lowercase-hex wire field."""
    if not re.fullmatch(r"(?:[0-9a-f]{2})*", field):
        raise LoadFailure(f"malformed hexadecimal fingerprint field: {label}")
    return bytes.fromhex(field)


def _identity_sha256(serialized):
    return hashlib.sha256(serialized).hexdigest()


EMPTY_HYPOTHESES_WIRE = b"4:list1:0"


def _match_expected_identities(records, post_state, expected_identities,
                               serializer_sha256, mapping_status):
    """Fail closed unless every approved structural identity matches exactly."""
    if expected_identities is None:
        return "observed_uncompared", False
    if mapping_status != "audited":
        raise LoadFailure(
            "expected fingerprints cannot approve a manual-review mapping")
    if set(expected_identities) != {
            "approval_sha256", "serializer_sha256", "theorems", "post_state"}:
        raise LoadFailure("malformed expected fingerprint identity object")
    if not re.fullmatch(r"[0-9a-f]{64}", expected_identities["approval_sha256"]):
        raise LoadFailure("malformed expected fingerprint approval identity")
    if expected_identities["serializer_sha256"] != serializer_sha256:
        raise LoadFailure("expected fingerprint serializer identity mismatch")
    if expected_identities["theorems"] != records:
        raise LoadFailure("observed theorem or global-axiom fingerprint mismatch")
    if expected_identities["post_state"] != post_state:
        raise LoadFailure("observed post-load kernel-state fingerprint mismatch")
    return "matched", True


def _read_fingerprint_records(log_path, theorem_names, mapping_status,
                              expected_identities=None):
    """Parse structural identities emitted by candle/fingerprint.ml."""
    records = {}
    state_records = []
    for line in Path(log_path).read_text(encoding="utf-8").splitlines():
        if not line.startswith(FINGERPRINT_MARKER + "\t"):
            continue
        fields = line.split("\t")
        if len(fields) != 8:
            raise LoadFailure(
                f"malformed {FINGERPRINT_MARKER} record with "
                f"{len(fields)} fields")
        (_, name_hex, theorem_hex, hypotheses_hex, conclusion_hex,
         assumptions_hex,
         hypothesis_count, assumption_count) = fields
        name_bytes = _decode_fingerprint_hex(name_hex, "name")
        try:
            name = name_bytes.decode("ascii")
        except UnicodeDecodeError as error:
            raise LoadFailure("non-ASCII theorem name in fingerprint") from error
        if name in records:
            raise LoadFailure(f"duplicate theorem fingerprint: {name}")
        theorem = _decode_fingerprint_hex(theorem_hex, "theorem")
        hypotheses = _decode_fingerprint_hex(hypotheses_hex, "hypotheses")
        conclusion = _decode_fingerprint_hex(conclusion_hex, "conclusion")
        assumptions = _decode_fingerprint_hex(assumptions_hex, "assumptions")
        try:
            parsed_hypothesis_count = int(hypothesis_count)
            parsed_assumption_count = int(assumption_count)
        except ValueError as error:
            raise LoadFailure(
                f"non-numeric fingerprint count for {name}") from error
        if (parsed_hypothesis_count != 0 or
                hypotheses != EMPTY_HYPOTHESES_WIRE):
            raise LoadFailure(f"Great 100 theorem is not closed: {name}")
        if parsed_assumption_count != 3:
            raise LoadFailure(
                f"Great 100 theorem does not use exactly three axioms: {name}")
        records[name] = {
            "name": name,
            "theorem_sha256": _identity_sha256(theorem),
            "hypotheses_sha256": _identity_sha256(hypotheses),
            "conclusion_sha256": _identity_sha256(conclusion),
            "global_axioms_sha256": _identity_sha256(assumptions),
            "hypothesis_count": parsed_hypothesis_count,
            "global_axiom_count": parsed_assumption_count,
        }
    for line in Path(log_path).read_text(encoding="utf-8").splitlines():
        if not line.startswith(STATE_FINGERPRINT_MARKER + "\t"):
            continue
        fields = line.split("\t")
        if len(fields) != 10:
            raise LoadFailure(
                f"malformed {STATE_FINGERPRINT_MARKER} record with "
                f"{len(fields)} fields")
        serialized = [
            _decode_fingerprint_hex(field, label)
            for field, label in zip(fields[1:6], (
                "kernel state", "type constants", "term constants",
                "definitions", "state axioms"))
        ]
        try:
            counts = [int(field) for field in fields[6:10]]
        except ValueError as error:
            raise LoadFailure("non-numeric post-state fingerprint count") from error
        if any(count < 0 for count in counts):
            raise LoadFailure("negative post-state fingerprint count")
        state_records.append({
            "kernel_state_sha256": _identity_sha256(serialized[0]),
            "type_constants_sha256": _identity_sha256(serialized[1]),
            "term_constants_sha256": _identity_sha256(serialized[2]),
            "definitions_sha256": _identity_sha256(serialized[3]),
            "global_axioms_sha256": _identity_sha256(serialized[4]),
            "type_constant_count": counts[0],
            "term_constant_count": counts[1],
            "definition_count": counts[2],
            "global_axiom_count": counts[3],
        })

    expected = list(theorem_names)
    missing = [name for name in expected if name not in records]
    unexpected = [name for name in records if name not in expected]
    if missing or unexpected:
        raise LoadFailure(
            "fingerprint request mismatch: "
            f"missing={missing}, unexpected={unexpected}")

    axiom_identities = {
        (record["global_axioms_sha256"], record["global_axiom_count"])
        for record in records.values()
    }
    if len(axiom_identities) != 1:
        raise LoadFailure("global axiom identity changed between theorem requests")
    if len(state_records) != 1:
        raise LoadFailure(
            f"expected exactly one post-state fingerprint; got {len(state_records)}")
    post_state = state_records[0]
    if next(iter(axiom_identities)) != (
            post_state["global_axioms_sha256"],
            post_state["global_axiom_count"]):
        raise LoadFailure("theorem and post-state global axiom identity mismatch")
    if post_state["global_axiom_count"] != 3:
        raise LoadFailure("post-state does not contain exactly three global axioms")

    serializer_sha256 = hashlib.sha256(FINGERPRINT_HELPER.read_bytes()).hexdigest()
    ordered_records = [records[name] for name in expected]
    status, expected_present = _match_expected_identities(
        ordered_records, post_state, expected_identities, serializer_sha256,
        mapping_status)
    return {
        "status": status,
        "mapping_status": mapping_status,
        "expected_identities_present": expected_present,
        "serializer": {
            "path": FINGERPRINT_HELPER.relative_to(CANDLE_ROOT).as_posix(),
            "sha256": serializer_sha256,
        },
        "theorems": ordered_records,
        "post_state": post_state,
        "approval_sha256": (
            expected_identities["approval_sha256"]
            if expected_identities is not None else None),
    }


def _read_process_markers(log_path, suite_nonce, process_nonce,
                          linked_record_sha256):
    data = Path(log_path).read_bytes()
    try:
        lines = data.decode("utf-8").splitlines()
    except UnicodeDecodeError as error:
        raise LoadFailure("Great 100 transcript is not UTF-8") from error
    expected = {
        "suite": f"{SUITE_MARKER}\t{suite_nonce}",
        "start": f"{PROCESS_MARKER}\t{suite_nonce}\t{process_nonce}\tSTART",
        "linked": f"{LINKED_RECORD_MARKER}\t{linked_record_sha256}",
        "complete": (
            f"{PROCESS_MARKER}\t{suite_nonce}\t{process_nonce}\tCOMPLETE"),
    }
    indices = {}
    for name, marker in expected.items():
        matches = [index for index, line in enumerate(lines) if line == marker]
        if len(matches) != 1:
            raise LoadFailure(f"missing or duplicate Great 100 {name} marker")
        indices[name] = matches[0]
    if not (indices["suite"] < indices["start"] < indices["linked"] <
            indices["complete"]):
        raise LoadFailure("Great 100 process markers are out of order")
    fingerprint_indices = [
        index for index, line in enumerate(lines)
        if line.startswith((FINGERPRINT_MARKER + "\t",
                            STATE_FINGERPRINT_MARKER + "\t"))
    ]
    if not fingerprint_indices or any(
            not indices["linked"] < index < indices["complete"]
            for index in fingerprint_indices):
        raise LoadFailure("fingerprint record lies outside process markers")
    return {
        "suite_line": indices["suite"],
        "start_line": indices["start"],
        "linked_line": indices["linked"],
        "complete_line": indices["complete"],
    }


# ---------------------------------------------------------------------------
# Resource sampling
# ---------------------------------------------------------------------------

class ProcessTreeSampler:
    """Sample RSS for a process and all of its descendants on Linux."""

    def __init__(self, root_pid, interval=0.25):
        self.root_pid = root_pid
        self.interval = interval
        self.peak_process_rss_kib = 0
        self.peak_tree_rss_kib = 0
        self.sample_count = 0
        self.root_observed = False
        self.error = None
        self._stop = threading.Event()
        self._thread = threading.Thread(target=self._run, daemon=True)

    @staticmethod
    def _process_snapshot():
        parents = {}
        rss = {}
        page_kib = os.sysconf("SC_PAGE_SIZE") // 1024
        for entry in Path("/proc").iterdir():
            if not entry.name.isdigit():
                continue
            try:
                pid = int(entry.name)
                stat = (entry / "stat").read_text(encoding="utf-8")
                fields = stat[stat.rfind(")") + 2:].split()
                parent = int(fields[1])
                statm = (entry / "statm").read_text(encoding="utf-8").split()
                resident = int(statm[1]) * page_kib
                parents[pid] = parent
                rss[pid] = resident
            except (FileNotFoundError, ProcessLookupError, PermissionError,
                    ValueError, IndexError):
                continue
        return parents, rss

    def _sample(self):
        parents, rss = self._process_snapshot()
        self.sample_count += 1
        self.root_observed = self.root_observed or self.root_pid in rss
        tree = {self.root_pid}
        changed = True
        while changed:
            changed = False
            for pid, parent in parents.items():
                if parent in tree and pid not in tree:
                    tree.add(pid)
                    changed = True
        live_rss = [rss[pid] for pid in tree if pid in rss]
        if live_rss:
            self.peak_process_rss_kib = max(
                self.peak_process_rss_kib, max(live_rss))
            self.peak_tree_rss_kib = max(
                self.peak_tree_rss_kib, sum(live_rss))

    def _run(self):
        try:
            self._sample()
            while not self._stop.wait(self.interval):
                self._sample()
        except Exception as error:  # pylint: disable=broad-exception-caught
            self.error = f"{error.__class__.__name__}: {error}"

    def start(self):
        self._thread.start()

    def stop(self):
        self._stop.set()
        self._thread.join()
        try:
            self._sample()
        except Exception as error:  # pylint: disable=broad-exception-caught
            self.error = f"{error.__class__.__name__}: {error}"

    def evidence(self):
        completed = not self._thread.is_alive() and self.error is None
        return {
            "interval_seconds": self.interval,
            "sample_count": self.sample_count,
            "root_observed": self.root_observed,
            "sampler_completed": completed,
            "peak_process_rss_kib": self.peak_process_rss_kib,
            "peak_tree_rss_kib": self.peak_tree_rss_kib,
        }


# ---------------------------------------------------------------------------
# Test result and runner
# ---------------------------------------------------------------------------

@dataclass
class TestResult:
    name: str
    status: TestStatus
    boot_elapsed: float = 0.0
    hol_elapsed: float = 0.0
    test_elapsed: float = 0.0
    fingerprint_elapsed: float = 0.0
    peak_process_rss_kib: int = 0
    peak_tree_rss_kib: int = 0
    error_message: str = ""
    log_path: str = ""
    fingerprints: dict | None = None
    timeout_kind: str | None = None
    process_evidence: dict | None = None

    @property
    def total(self):
        return (self.boot_elapsed + self.hol_elapsed + self.test_elapsed
                + self.fingerprint_elapsed)


def _format_error(repl, exc):
    """One-line failure summary: the error, where it happened, last value bound."""
    err = str(exc) or exc.__class__.__name__
    if repl is not None:
        if repl.load_stack:
            err += f" {repl.load_stack_str()}"      # where: the file/dep being loaded
        if repl.last_val:
            err += f" (last val: {repl.last_val})"   # last value bound before failure
    return err


def _open_test_log(safe_name, log_dir=None):
    """Create a unique test log, optionally in a persistent directory."""
    if log_dir is not None:
        log_dir = Path(log_dir)
        log_dir.mkdir(parents=True, exist_ok=True)
    fd, path = tempfile.mkstemp(
        prefix=f"candle-{safe_name}-", suffix=".log",
        dir=str(log_dir) if log_dir is not None else None)
    return os.fdopen(fd, "w"), str(Path(path).resolve())


def run_test(test, inactivity_timeout, wall_timeout=None, env=None,
             log_dir=None, suite_nonce=None, suite_contract=None):
    """Run one fresh process with distinct inactivity and total wall limits."""
    safe_name = test.name.replace("/", "_")
    logfile, log_path = _open_test_log(safe_name, log_dir)

    repl = None
    sampler = None
    result = None
    start = None          # set once Candle is booted; marks the start of hol.ml load
    run_started = time.perf_counter()
    wall_deadline = (time.monotonic() + wall_timeout
                     if wall_timeout is not None else None)
    boot_elapsed = 0.0
    hol_elapsed = 0.0
    test_elapsed = 0.0
    fingerprint_elapsed = 0.0
    request_path = None
    process_nonce = secrets.token_hex(32) if suite_contract is not None else None
    process_started_utc = datetime.now(timezone.utc).isoformat()
    process_pid = None
    exit_code = None
    markers = None
    pre_runtime_state = None
    post_runtime_state = None
    if suite_contract is not None:
        pre_runtime_state = _runtime_state(suite_contract)
        env = dict(os.environ if env is None else env)
        env["CANDLE_GREAT100_SUITE_NONCE"] = suite_nonce
        env["CANDLE_GREAT100_PROCESS_NONCE"] = process_nonce
    try:
        repl = CandleREPL(
            logfile=logfile, inactivity_timeout=inactivity_timeout,
            wall_deadline=wall_deadline, env=env)
        boot_elapsed = time.perf_counter() - run_started
        process_pid = repl.process.pid
        sampler = ProcessTreeSampler(repl.process.pid)
        sampler.start()

        start = time.perf_counter()
        repl.load("hol.ml")
        hol_elapsed = time.perf_counter() - start

        for f in test.files:
            repl.load(f)
        test_elapsed = time.perf_counter() - start - hol_elapsed

        fingerprints = None
        if test.fingerprint_theorems:
            fingerprint_start = time.perf_counter()
            repl.load(FINGERPRINT_HELPER.relative_to(CANDLE_ROOT).as_posix())
            request_fd, request_path = tempfile.mkstemp(
                prefix=f"candle-{safe_name}-fingerprints-", suffix=".ml")
            with os.fdopen(request_fd, "w", encoding="utf-8") as request_file:
                request_file.write(
                    _fingerprint_request_source(
                        test.fingerprint_theorems, suite_nonce, process_nonce))
            repl.load(request_path)
            logfile.flush()
            fingerprints = _read_fingerprint_records(
                log_path, test.fingerprint_theorems,
                test.fingerprint_mapping_status,
                test.fingerprint_expected_identities)
            if suite_contract is not None:
                markers = _read_process_markers(
                    log_path, suite_nonce, process_nonce,
                    suite_contract["linked_record"]["sha256"])
            fingerprint_elapsed = time.perf_counter() - fingerprint_start

        exit_code = repl.finish()

        result = TestResult(
            test.name, TestStatus.PASS, boot_elapsed=boot_elapsed,
            hol_elapsed=hol_elapsed,
            test_elapsed=test_elapsed,
            fingerprint_elapsed=fingerprint_elapsed, log_path=log_path,
            fingerprints=fingerprints)

    except Exception as e:  # pylint: disable=broad-exception-caught
        # A test must never crash the runner: record any failure and move on.
        # Attribute elapsed time to whichever phase we failed in.
        if not boot_elapsed:
            boot_elapsed = time.perf_counter() - run_started
        if start is not None:
            if hol_elapsed:
                elapsed_after_hol = time.perf_counter() - start - hol_elapsed
                if test_elapsed:
                    fingerprint_elapsed = elapsed_after_hol - test_elapsed
                else:
                    test_elapsed = elapsed_after_hol
            else:
                hol_elapsed = time.perf_counter() - start
        is_timeout = isinstance(e, (pexpect.TIMEOUT, RunnerTimeout))
        status = TestStatus.TIMEOUT if is_timeout else TestStatus.FAIL
        timeout_kind = (
            "wall" if isinstance(e, WallTimeout) else
            "inactivity" if isinstance(e, (InactivityTimeout, pexpect.TIMEOUT))
            else None)
        result = TestResult(
            test.name, status, boot_elapsed=boot_elapsed,
            hol_elapsed=hol_elapsed,
            test_elapsed=test_elapsed,
            fingerprint_elapsed=fingerprint_elapsed,
            error_message=_format_error(repl, e), log_path=log_path,
            timeout_kind=timeout_kind)

    finally:
        if sampler is not None:
            sampler.stop()
            if result is not None:
                result.peak_process_rss_kib = sampler.peak_process_rss_kib
                result.peak_tree_rss_kib = sampler.peak_tree_rss_kib
        if repl is not None:
            repl.kill()
        logfile.close()
        if request_path is not None:
            Path(request_path).unlink(missing_ok=True)
        if suite_contract is not None and result is not None:
            evidence_error = None
            try:
                post_runtime_state = _runtime_state(suite_contract)
                transcript = _ordinary_file_record(log_path)
                resource = sampler.evidence() if sampler is not None else {
                    "interval_seconds": 0.25,
                    "sample_count": 0,
                    "root_observed": False,
                    "sampler_completed": False,
                    "peak_process_rss_kib": 0,
                    "peak_tree_rss_kib": 0,
                }
                if result.status is TestStatus.PASS:
                    final_fingerprints = _read_fingerprint_records(
                        log_path, test.fingerprint_theorems,
                        test.fingerprint_mapping_status,
                        test.fingerprint_expected_identities,
                    )
                    final_markers = _read_process_markers(
                        log_path, suite_nonce, process_nonce,
                        suite_contract["linked_record"]["sha256"],
                    )
                    if (final_fingerprints != result.fingerprints or
                            final_markers != markers):
                        raise LoadFailure(
                            "final Great 100 transcript differs from prefix parse")
                    result.fingerprints = final_fingerprints
                    markers = final_markers
                if result.status is TestStatus.PASS and (
                        exit_code != 0 or markers is None or
                        pre_runtime_state != post_runtime_state or
                        resource["sample_count"] <= 0 or
                        not resource["root_observed"] or
                        not resource["sampler_completed"] or
                        resource["peak_process_rss_kib"] <= 0 or
                        resource["peak_tree_rss_kib"] <= 0):
                    raise LoadFailure("incomplete Great 100 process evidence")
                result.process_evidence = {
                    "suite_nonce": suite_nonce,
                    "process_nonce": process_nonce,
                    "pid": process_pid,
                    "started_utc": process_started_utc,
                    "completed_utc": datetime.now(timezone.utc).isoformat(),
                    "exit_code": exit_code,
                    "markers": markers,
                    "linked_record_sha256":
                        suite_contract["linked_record"]["sha256"],
                    "transcript": transcript,
                    "pre_runtime_state": pre_runtime_state,
                    "post_runtime_state": post_runtime_state,
                    "resource_sampling": resource,
                }
            except Exception as error:  # pylint: disable=broad-exception-caught
                evidence_error = error
            if evidence_error is not None and result.status is TestStatus.PASS:
                result.status = TestStatus.FAIL
                result.error_message = f"evidence validation failed: {evidence_error}"
    return result


# ---------------------------------------------------------------------------
# Reporter
# ---------------------------------------------------------------------------

class Reporter:
    STATUS_SYMBOLS = {
        TestStatus.PASS:    "PASS",
        TestStatus.FAIL:    "FAIL",
        TestStatus.TIMEOUT: "TIME",
    }

    @staticmethod
    def result_record(result, files):
        """Return one deterministic machine-readable result row."""
        return {
            "name": result.name,
            "files": list(files),
            "status": result.status.value,
            "timeout_kind": result.timeout_kind,
            "boot_elapsed_seconds": result.boot_elapsed,
            "hol_elapsed_seconds": result.hol_elapsed,
            "test_elapsed_seconds": result.test_elapsed,
            "fingerprint_elapsed_seconds": result.fingerprint_elapsed,
            "total_elapsed_seconds": result.total,
            "peak_process_rss_kib": result.peak_process_rss_kib,
            "peak_tree_rss_kib": result.peak_tree_rss_kib,
            "error_message": result.error_message,
            "log_path": result.log_path,
            "fingerprints": result.fingerprints,
            "process_evidence": result.process_evidence,
        }

    @staticmethod
    def s1_evidence_summary(results, tests, suite):
        """Summarize S1 closure without treating a load-only pass as evidence."""
        matched = 0
        observed_uncompared = 0
        missing = len(tests) - len(results)
        for result in results:
            status = ((result.fingerprints or {}).get("status")
                      if result.status is TestStatus.PASS else None)
            if status == "matched":
                matched += 1
            elif status == "observed_uncompared":
                observed_uncompared += 1
            else:
                missing += 1
        expected_count = sum(
            test.fingerprint_expected_identities is not None for test in tests)
        manual_review_count = sum(
            test.fingerprint_mapping_status == "manual_review" for test in tests)
        return {
            "requested_target_count": len(tests),
            "reported_target_count": len(results),
            "expected_identity_target_count": expected_count,
            "manual_review_mapping_target_count": manual_review_count,
            "matched_target_count": matched,
            "observed_uncompared_target_count": observed_uncompared,
            "missing_or_failed_fingerprint_target_count": missing,
            "suite_closed": (
                suite == "top100" and len(results) == len(tests)
                and matched == len(tests) and expected_count == len(tests)
                and manual_review_count == 0
                and all(result.status is TestStatus.PASS and
                        result.process_evidence is not None and
                        result.process_evidence.get("exit_code") == 0
                        for result in results)),
        }

    @staticmethod
    def print_summary(results, wall):
        print()
        print(f"{'Test':<40} {'Status':>6} {'Time':>9} {'Peak RSS':>12}")
        print("-" * 71)
        for r in results:
            sym = Reporter.STATUS_SYMBOLS[r.status]
            peak_rss = f"{r.peak_process_rss_kib / 1024:.1f} MiB"
            print(
                f"{r.name:<40} {sym:>6} {f'{r.total:.1f}s':>9} "
                f"{peak_rss:>12}")
        print("-" * 71)

        counts = {}
        for s in TestStatus:
            c = sum(1 for r in results if r.status == s)
            if c:
                counts[s] = c
        parts = [f"{s.value}: {c}" for s, c in counts.items()]

        sum_total = sum(r.total for r in results)
        hol_times = [r.hol_elapsed for r in results if r.hol_elapsed > 0]
        avg_hol = sum(hol_times) / len(hol_times) if hol_times else 0.0

        print(f"Total: {len(results)}  |  " + "  ".join(parts))
        print(f"Sum of per-test time: {sum_total:.1f}s")
        print(f"Wall clock:           {wall:.1f}s")
        print(f"Average hol.ml load:  {avg_hol:.1f}s")

        failures = [r for r in results if r.status in (TestStatus.FAIL, TestStatus.TIMEOUT)]
        if failures:
            print()
            print("FAILURES:")
            for r in failures:
                msg = f"  {r.name}: {r.status.value}"
                if r.error_message:
                    msg += f" — {r.error_message}"
                print(msg)
                print(f"    log: {r.log_path}")

    @staticmethod
    def write_json(results, wall, path, suite, jobs, inactivity_timeout,
                   wall_timeout, tests, log_dir, suite_nonce=None,
                   suite_contract=None, suite_started_utc=None):
        if suite == "top100":
            if suite_contract is None or not re.fullmatch(
                    r"[0-9a-f]{64}", suite_nonce or ""):
                raise ValueError("schema-4 Great 100 report lacks suite evidence")
            _runtime_state(suite_contract)
            _validate_top100_results(
                results, tests, suite_nonce, suite_contract)
        files_by_name = {test.name: list(test.files) for test in tests}
        counts = {
            status.value: sum(result.status == status for result in results)
            for status in TestStatus
        }
        payload = {
            "schema": 4,
            "generated_utc": datetime.now(timezone.utc).isoformat(),
            "suite_started_utc": suite_started_utc,
            "suite": suite,
            "test_count": len(results),
            "jobs": jobs,
            "timeout_policy": _timeout_policy(
                inactivity_timeout, wall_timeout),
            "wall_seconds": wall,
            "sum_test_seconds": sum(result.total for result in results),
            "counts": counts,
            "candle_root": str(CANDLE_ROOT),
            "candle_git_head": (
                suite_contract["candle_git_head"]
                if suite_contract is not None else _git_state()[0]),
            "candle_git_status": (
                suite_contract["candle_git_status"]
                if suite_contract is not None else _git_state()[1]),
            "candle_executable": (
                suite_contract["candle_executable"]
                if suite_contract is not None else
                _ordinary_file_record(CANDLE_ROOT / "candle/build/cake")),
            "log_directory": str(Path(log_dir).resolve()),
            "fingerprint_contract": {
                "serializer": "candle/fingerprint.ml structural v2",
                "load_pass_is_fingerprint_match": False,
                "expected_identity_source": (
                    "separate independently reviewed approval artifact, "
                    "fail-closed through top100_manifest.json"),
                "expected_mismatch_result": "FAIL",
            },
            "s1_evidence": Reporter.s1_evidence_summary(
                results, tests, suite),
            "results": [
                Reporter.result_record(result, files_by_name[result.name])
                for result in results
            ],
        }
        if suite_contract is not None:
            payload.update({
                "execution_contract": suite_contract["execution_contract"],
                "source_closure": suite_contract["source_closure"],
                "independent_approval": suite_contract["independent_approval"],
                "linked_record": suite_contract["linked_record"],
                "run_evidence": {
                    "suite_nonce": suite_nonce,
                    "marker_contract": "candle-great100-process-markers-v1",
                    "linked_record_sha256":
                        suite_contract["linked_record"]["sha256"],
                    "source_closure_sha256":
                        suite_contract["source_closure"]["sha256"],
                    "independent_approval_sha256":
                        suite_contract["independent_approval"]["sha256"],
                },
            })
        with path.open("x", encoding="utf-8") as report_file:
            json.dump(payload, report_file, indent=2)
            report_file.write("\n")
        print(f"Machine-readable report: {path}")
        return payload


PROCESS_EVIDENCE_KEYS = {
    "suite_nonce", "process_nonce", "pid", "started_utc", "completed_utc",
    "exit_code", "markers", "linked_record_sha256", "transcript",
    "pre_runtime_state", "post_runtime_state", "resource_sampling",
}
FINGERPRINT_REPORT_KEYS = {
    "status", "mapping_status", "expected_identities_present", "serializer",
    "theorems", "post_state", "approval_sha256",
}
RESOURCE_EVIDENCE_KEYS = {
    "interval_seconds", "sample_count", "root_observed", "sampler_completed",
    "peak_process_rss_kib", "peak_tree_rss_kib",
}


def _validate_top100_results(results, tests, suite_nonce, suite_contract):
    """Rehash persistent evidence and reject a structurally false PASS."""
    if len(tests) != 65 or [result.name for result in results] != [
            test.name for test in tests]:
        raise ValueError("schema-4 report is not the ordered 65-target suite")
    expected_runtime = _runtime_state(suite_contract)
    process_nonces = set()
    for result, test in zip(results, tests):
        if result.status is not TestStatus.PASS:
            continue
        evidence = result.process_evidence
        if not isinstance(evidence, dict) or set(evidence) != PROCESS_EVIDENCE_KEYS:
            raise ValueError(f"{result.name}: malformed process evidence")
        if (evidence["suite_nonce"] != suite_nonce or
                not re.fullmatch(r"[0-9a-f]{64}", evidence["process_nonce"]) or
                evidence["process_nonce"] in process_nonces):
            raise ValueError(f"{result.name}: invalid or reused process nonce")
        process_nonces.add(evidence["process_nonce"])
        if (isinstance(evidence["pid"], bool) or
                not isinstance(evidence["pid"], int) or evidence["pid"] <= 0 or
                evidence["exit_code"] != 0):
            raise ValueError(f"{result.name}: process did not complete normally")
        try:
            started = datetime.fromisoformat(evidence["started_utc"])
            completed = datetime.fromisoformat(evidence["completed_utc"])
        except (TypeError, ValueError) as error:
            raise ValueError(f"{result.name}: malformed process time") from error
        if (started.tzinfo is None or completed.tzinfo is None or
                completed < started):
            raise ValueError(f"{result.name}: invalid process time interval")
        markers = evidence["markers"]
        if not isinstance(markers, dict) or set(markers) != {
                "suite_line", "start_line", "linked_line", "complete_line"}:
            raise ValueError(f"{result.name}: malformed process marker record")
        positions = [markers[key] for key in (
            "suite_line", "start_line", "linked_line", "complete_line")]
        if (any(isinstance(value, bool) or not isinstance(value, int)
                for value in positions) or positions != sorted(set(positions))):
            raise ValueError(f"{result.name}: process markers are not ordered")
        transcript = _ordinary_file_record(result.log_path)
        if (evidence["transcript"] != transcript or
                transcript["path"] != str(Path(result.log_path).resolve())):
            raise ValueError(f"{result.name}: transcript changed after validation")
        try:
            final_markers = _read_process_markers(
                result.log_path, suite_nonce, evidence["process_nonce"],
                suite_contract["linked_record"]["sha256"],
            )
            final_fingerprints = _read_fingerprint_records(
                result.log_path, test.fingerprint_theorems,
                test.fingerprint_mapping_status,
                test.fingerprint_expected_identities,
            )
        except LoadFailure as error:
            raise ValueError(
                f"{result.name}: final transcript replay failed: {error}"
            ) from error
        if (final_markers != markers or
                final_fingerprints != result.fingerprints):
            raise ValueError(
                f"{result.name}: cached evidence differs from final transcript")
        if (evidence["linked_record_sha256"] !=
                suite_contract["linked_record"]["sha256"] or
                evidence["pre_runtime_state"] != expected_runtime or
                evidence["post_runtime_state"] != expected_runtime):
            raise ValueError(f"{result.name}: runtime provenance mismatch")
        resource = evidence["resource_sampling"]
        if (not isinstance(resource, dict) or set(resource) !=
                RESOURCE_EVIDENCE_KEYS or
                isinstance(resource["interval_seconds"], bool) or
                not isinstance(resource["interval_seconds"], (int, float)) or
                resource["interval_seconds"] <= 0 or
                any(isinstance(resource[field], bool) or
                    not isinstance(resource[field], int) or resource[field] <= 0
                    for field in ("sample_count", "peak_process_rss_kib",
                                  "peak_tree_rss_kib")) or
                resource["root_observed"] is not True or
                resource["sampler_completed"] is not True):
            raise ValueError(f"{result.name}: incomplete resource sampling")
        fingerprints = result.fingerprints
        expected = test.fingerprint_expected_identities
        if (not isinstance(fingerprints, dict) or
                set(fingerprints) != FINGERPRINT_REPORT_KEYS or
                fingerprints["status"] != "matched" or
                fingerprints["expected_identities_present"] is not True or
                fingerprints["approval_sha256"] !=
                suite_contract["independent_approval"]["sha256"] or
                expected is None or fingerprints["theorems"] !=
                expected["theorems"] or fingerprints["post_state"] !=
                expected["post_state"]):
            raise ValueError(f"{result.name}: fingerprint evidence mismatch")


# ---------------------------------------------------------------------------
# Runner
# ---------------------------------------------------------------------------

def _available_memory_mb():
    """Best-effort available RAM in MB (Linux /proc/meminfo), else None."""
    try:
        with open("/proc/meminfo", encoding="utf-8") as f:
            for line in f:
                if line.startswith("MemAvailable:"):
                    return int(line.split()[1]) // 1024
    except (OSError, ValueError, IndexError):
        pass
    return None


def cap_jobs_for_heap(jobs, heap_mb):
    """Cap workers so heap_mb * jobs stays within available RAM.

    Each candle process reserves its full heap, so heap_mb * jobs is the
    memory ceiling. Falls back to the requested jobs if memory is unknown.
    """
    avail = _available_memory_mb()
    if avail is None:
        return jobs
    return max(1, min(jobs, avail // heap_mb))


def _prepare_top100_evidence_paths(report_path, log_dir):
    report_path = Path(report_path)
    log_dir = Path(log_dir)
    if not report_path.is_absolute() or not log_dir.is_absolute():
        raise ValueError("Great 100 report and log paths must be absolute")
    candle_root = CANDLE_ROOT.resolve(strict=True)
    for path, label in ((report_path, "report"), (log_dir, "log directory")):
        try:
            path.resolve().relative_to(candle_root)
        except ValueError:
            pass
        else:
            raise ValueError(f"Great 100 {label} must be outside the Candle tree")
    parent = report_path.parent
    if (parent.is_symlink() or not parent.is_dir() or
            parent.resolve(strict=True) != parent):
        raise ValueError("Great 100 report parent is not an ordinary directory")
    if report_path.exists() or report_path.is_symlink():
        raise ValueError("Great 100 report path must not already exist")
    if log_dir.exists() or log_dir.is_symlink():
        if (log_dir.is_symlink() or not log_dir.is_dir() or
                log_dir.resolve(strict=True) != log_dir):
            raise ValueError("Great 100 log path is not an ordinary directory")
        if any(log_dir.iterdir()):
            raise ValueError("Great 100 log directory must be empty")
    else:
        if (log_dir.parent.is_symlink() or not log_dir.parent.is_dir() or
                log_dir.parent.resolve(strict=True) != log_dir.parent):
            raise ValueError("Great 100 log parent is not an ordinary directory")
        log_dir.mkdir(mode=0o700)
    return report_path, log_dir


def run_suite(tests, jobs, inactivity_timeout, wall_timeout=None, env=None,
              log_dir=None, suite_nonce=None, suite_contract=None):
    total = len(tests)
    print(f"Running {total} test(s) with {jobs} parallel worker(s).")
    wall_description = (f"{wall_timeout:g}s" if wall_timeout is not None
                        else "unbounded")
    print(f"Timeouts: {inactivity_timeout:g}s inactivity; "
          f"{wall_description} total wall per target.")
    log_description = (str(Path(log_dir).resolve()) if log_dir is not None
                       else "/tmp/candle-<test>-*.log")
    print(f"Logs: {log_description}\n")

    results = []
    done = 0
    wall_start = time.perf_counter()

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        futures = {
            ex.submit(
                run_test, t, inactivity_timeout,
                wall_timeout=wall_timeout, env=env, log_dir=log_dir,
                suite_nonce=suite_nonce, suite_contract=suite_contract): t
            for t in tests
        }
        try:
            for fut in concurrent.futures.as_completed(futures):
                r = fut.result()
                done += 1
                sym = Reporter.STATUS_SYMBOLS[r.status]
                print(f"[{done}/{total}] {sym}  {r.name}  ({r.total:.1f}s)")
                if r.status is not TestStatus.PASS:
                    if r.error_message:
                        print(f"          {r.error_message}")
                    print(f"          log: {r.log_path}")
                results.append(r)
        except KeyboardInterrupt:
            print("\nInterrupted — cancelling pending tests; showing results so far.")
            for fut in futures:
                fut.cancel()

    wall = time.perf_counter() - wall_start
    order = {test.name: index for index, test in enumerate(tests)}
    results.sort(key=lambda result: order[result.name])
    return results, wall


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Candle parallel regression suite")
    parser.add_argument(
        "--top100", action="store_true",
        help="Run the full Top 100 theorems suite instead of the regression subset",
    )
    parser.add_argument(
        "--test", nargs="+",
        help="Run specific test name(s), e.g. 100/arithmetic (overrides suite selection)",
    )
    parser.add_argument(
        "--list", action="store_true",
        help="List the selected suite and exit",
    )
    parser.add_argument(
        "-j", "--jobs", type=int, default=max(1, (os.cpu_count() or 2) - 1),
        help="Number of parallel workers (default: CPU count - 1)",
    )
    parser.add_argument(
        "--timeout", "--inactivity-timeout", dest="inactivity_timeout",
        type=float, default=600,
        help=("seconds without a complete REPL output line before a "
              "target times out; --timeout is retained as an alias "
              "(default: 600)"),
    )
    parser.add_argument(
        "--wall-timeout", type=float, default=0,
        help=("total seconds per target from process spawn through "
              "fingerprints, unaffected by progress; 0 is unbounded "
              "(default: 0)"),
    )
    parser.add_argument(
        "--json-report", type=Path,
        help="write a machine-readable result and resource report",
    )
    parser.add_argument(
        "--log-dir", type=Path,
        help=("retain per-target logs in this directory; with --json-report, "
              "the default is a sibling <report-stem>-logs directory"),
    )

    args = parser.parse_args()

    if args.jobs <= 0:
        parser.error("--jobs must be positive")
    if args.inactivity_timeout <= 0:
        parser.error("--inactivity-timeout must be positive")
    if args.wall_timeout < 0:
        parser.error("--wall-timeout must be non-negative")
    wall_timeout = args.wall_timeout or None

    if args.test:
        tests = [BY_NAME.get(name, _t(name)) for name in args.test]
        running_top100 = False
        suite_name = "selected"
    elif args.top100:
        tests = TOP100
        running_top100 = True
        suite_name = "top100"
    else:
        tests = REGRESSION
        running_top100 = False
        suite_name = "regression"

    if args.list:
        for t in tests:
            extra = f"  ({', '.join(t.files)})" if t.files != (f"{t.name}.ml",) else ""
            print(f"  {t.name}{extra}")
        print(f"\n{len(tests)} test(s)")
        return

    suite_contract = None
    suite_nonce = None
    suite_started_utc = datetime.now(timezone.utc).isoformat()
    if running_top100:
        if args.json_report is None:
            parser.error("--top100 requires --json-report")
        if wall_timeout is None:
            parser.error("--top100 requires a positive --wall-timeout")
        if args.json_report.exists():
            parser.error("--json-report must not already exist")
        suite_contract = _capture_suite_contract(require_approved=True)
        suite_nonce = secrets.token_hex(32)

    # The Top 100 suite gets a larger heap; cap parallelism so the combined
    # per-process heap reservation does not exceed available memory.
    child_env = None
    jobs = args.jobs
    if running_top100:
        child_env = {**os.environ, "CML_HEAP_SIZE": str(TOP100_HEAP_MB)}
        jobs = cap_jobs_for_heap(args.jobs, TOP100_HEAP_MB)
        if jobs < args.jobs:
            print(f"Capping workers {args.jobs} -> {jobs}: {TOP100_HEAP_MB} MB heap "
                  f"x {args.jobs} workers exceeds available RAM.")

    log_dir = args.log_dir
    if log_dir is None and args.json_report is not None:
        log_dir = args.json_report.parent / f"{args.json_report.stem}-logs"
    if running_top100:
        try:
            args.json_report, log_dir = _prepare_top100_evidence_paths(
                args.json_report, log_dir)
        except ValueError as error:
            parser.error(str(error))

    results, wall = run_suite(
        tests, jobs, args.inactivity_timeout,
        wall_timeout=wall_timeout, env=child_env, log_dir=log_dir,
        suite_nonce=suite_nonce, suite_contract=suite_contract)
    Reporter.print_summary(results, wall)
    if args.json_report:
        Reporter.write_json(
            results, wall, args.json_report, suite_name, jobs,
            args.inactivity_timeout, wall_timeout, tests, log_dir,
            suite_nonce=suite_nonce, suite_contract=suite_contract,
            suite_started_utc=suite_started_utc)

    unexpected = [r for r in results if r.status in (TestStatus.FAIL, TestStatus.TIMEOUT)]
    s1 = Reporter.s1_evidence_summary(results, tests, suite_name)
    sys.exit(1 if unexpected or (running_top100 and not s1["suite_closed"]) else 0)


if __name__ == "__main__":
    main()
