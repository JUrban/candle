"""
!!! Large amount of LLM generated code !!!

Parallel regression test runner for Candle.

Each test runs in its own fresh Candle process that loads hol.ml and then the
test file(s). There is no checkpointing (no criu/DMTCP, no sudo): running one
process per test, up to -j at a time, is what hides the cost of reloading
hol.ml for every test.

The Candle REPL transcript for each test is written to its own temporary log
file under /tmp (via tempfile.mkstemp), e.g. /tmp/candle-100_arithmetic-XXXX.log.

Two suites are available:
  * REGRESSION - a small subset, run by default.
  * TOP100     - the full "Top 100 theorems" set (from holtest.mk's
                 GREAT_100_THEOREMS), run with --top100.

Each result includes wall time and sampled peak RSS.  Pass --json-report PATH
to preserve the complete per-test table and exact source/executable identity.

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
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("schema_version") != 1:
        raise ValueError(f"unsupported Great 100 manifest schema: {path}")
    targets = payload.get("targets", [])
    if payload.get("target_count") != len(targets):
        raise ValueError(f"Great 100 target_count does not match targets: {path}")
    if any(target.get("skip") is not None for target in targets):
        raise ValueError(f"Great 100 manifest contains a skipped target: {path}")
    tests = []
    for target in targets:
        request = target.get("fingerprint_request")
        if not request:
            raise ValueError(
                f"Great 100 target has no fingerprint request: {target['name']}")
        theorem_names = tuple(item["name"] for item in request["theorems"])
        tests.append(Test(
            target["name"], tuple(target["load_files"]), theorem_names,
            request["mapping_status"]))
    return tests


# The machine-readable manifest is generated from GREAT_100_THEOREMS and also
# records dependencies, exclusions, and missing fingerprint/resource evidence.
TOP100 = _load_top100_manifest()

# Lookup by name, so --test can reuse multi-file definitions (e.g. the
# bertrand-primerecip pairing) rather than always assuming "<name>.ml".
BY_NAME = {t.name: t for t in TOP100}


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

FINGERPRINT_MARKER = "CANDLE_FINGERPRINT_V1"
FINGERPRINT_HELPER = CANDLE_ROOT / "candle" / "fingerprint.ml"
OCAML_VALUE_PATH_RE = re.compile(
    r"^[A-Za-z][A-Za-z0-9_']*(?:\.[A-Za-z][A-Za-z0-9_']*)*$")


def _fingerprint_request_source(theorem_names):
    lines = []
    for name in theorem_names:
        if not OCAML_VALUE_PATH_RE.fullmatch(name):
            raise ValueError(f"unsafe theorem value path in manifest: {name!r}")
        lines.append(f'candle_s1_emit_fingerprint "{name}" {name};;')
    return "\n".join(lines) + "\n"


def _decode_fingerprint_hex(field, label):
    """Decode one fail-closed lowercase-hex wire field."""
    if not re.fullmatch(r"(?:[0-9a-f]{2})*", field):
        raise LoadFailure(f"malformed hexadecimal fingerprint field: {label}")
    return bytes.fromhex(field)


def _identity_sha256(serialized):
    return hashlib.sha256(serialized).hexdigest()


def _read_fingerprint_records(log_path, theorem_names, mapping_status):
    """Parse structural identities emitted by candle/fingerprint.ml."""
    records = {}
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
        records[name] = {
            "name": name,
            "theorem_sha256": _identity_sha256(theorem),
            "hypotheses_sha256": _identity_sha256(hypotheses),
            "conclusion_sha256": _identity_sha256(conclusion),
            "global_axioms_sha256": _identity_sha256(assumptions),
            "hypothesis_count": parsed_hypothesis_count,
            "global_axiom_count": parsed_assumption_count,
        }

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

    return {
        "status": "observed_uncompared",
        "mapping_status": mapping_status,
        "expected_identities_present": False,
        "serializer": {
            "path": FINGERPRINT_HELPER.relative_to(CANDLE_ROOT).as_posix(),
            "sha256": hashlib.sha256(FINGERPRINT_HELPER.read_bytes()).hexdigest(),
        },
        "theorems": [records[name] for name in expected],
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
        self._sample()
        while not self._stop.wait(self.interval):
            self._sample()

    def start(self):
        self._thread.start()

    def stop(self):
        self._stop.set()
        self._thread.join()
        self._sample()


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


def run_test(test, inactivity_timeout, wall_timeout=None, env=None):
    """Run one fresh process with distinct inactivity and total wall limits."""
    safe_name = test.name.replace("/", "_")
    fd, log_path = tempfile.mkstemp(prefix=f"candle-{safe_name}-", suffix=".log")
    logfile = os.fdopen(fd, "w")

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
    try:
        repl = CandleREPL(
            logfile=logfile, inactivity_timeout=inactivity_timeout,
            wall_deadline=wall_deadline, env=env)
        boot_elapsed = time.perf_counter() - run_started
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
                    _fingerprint_request_source(test.fingerprint_theorems))
            repl.load(request_path)
            logfile.flush()
            fingerprints = _read_fingerprint_records(
                log_path, test.fingerprint_theorems,
                test.fingerprint_mapping_status)
            fingerprint_elapsed = time.perf_counter() - fingerprint_start

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
                   wall_timeout, tests):
        executable = CANDLE_ROOT / "candle" / "build" / "cake"
        executable_sha256 = hashlib.sha256(executable.read_bytes()).hexdigest()
        git_head = subprocess.check_output(
            ["git", "-C", str(CANDLE_ROOT), "rev-parse", "HEAD"],
            text=True,
        ).strip()
        git_status = subprocess.check_output(
            ["git", "-C", str(CANDLE_ROOT), "status", "--short"],
            text=True,
        ).splitlines()
        files_by_name = {test.name: list(test.files) for test in tests}
        counts = {
            status.value: sum(result.status == status for result in results)
            for status in TestStatus
        }
        payload = {
            "schema": 3,
            "generated_utc": datetime.now(timezone.utc).isoformat(),
            "suite": suite,
            "test_count": len(results),
            "jobs": jobs,
            "timeout_policy": _timeout_policy(
                inactivity_timeout, wall_timeout),
            "wall_seconds": wall,
            "sum_test_seconds": sum(result.total for result in results),
            "counts": counts,
            "candle_root": str(CANDLE_ROOT),
            "candle_git_head": git_head,
            "candle_git_status": git_status,
            "candle_executable": str(executable.resolve()),
            "candle_executable_sha256": executable_sha256,
            "fingerprint_contract": {
                "serializer": "candle/fingerprint.ml structural v1",
                "load_pass_is_fingerprint_match": False,
                "expected_identity_source": "top100_manifest.json",
            },
            "results": [
                Reporter.result_record(result, files_by_name[result.name])
                for result in results
            ],
        }
        path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        print(f"Machine-readable report: {path}")


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


def run_suite(tests, jobs, inactivity_timeout, wall_timeout=None, env=None):
    total = len(tests)
    print(f"Running {total} test(s) with {jobs} parallel worker(s).")
    wall_description = (f"{wall_timeout:g}s" if wall_timeout is not None
                        else "unbounded")
    print(f"Timeouts: {inactivity_timeout:g}s inactivity; "
          f"{wall_description} total wall per target.")
    print("Logs: /tmp/candle-<test>-*.log\n")

    results = []
    done = 0
    wall_start = time.perf_counter()

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        futures = {
            ex.submit(
                run_test, t, inactivity_timeout,
                wall_timeout=wall_timeout, env=env): t
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

    results, wall = run_suite(
        tests, jobs, args.inactivity_timeout,
        wall_timeout=wall_timeout, env=child_env)
    Reporter.print_summary(results, wall)
    if args.json_report:
        Reporter.write_json(
            results, wall, args.json_report, suite_name, jobs,
            args.inactivity_timeout, wall_timeout, tests)

    unexpected = [r for r in results if r.status in (TestStatus.FAIL, TestStatus.TIMEOUT)]
    sys.exit(1 if unexpected else 0)


if __name__ == "__main__":
    main()
