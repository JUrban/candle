# Compiled cumulative Flyspeck stratum runner

`flyspeck_stratum_runtime.py` consumes a materialized output of
`flyspeck_stratum_plan.py` and starts one selected cumulative prefix in a fresh
compiled Candle process.  It first validates the linked CakeML provenance.
It independently reconstructs the plan and every prefix from the pinned
manifest/full driver rather than trusting plan-supplied self-digests, then
requires exact equality and rechecks the clean repository revisions, all 400
source nodes, all 18 normalization outputs, all 43 generated inputs,
deterministic `date`/`whoami` inputs, and the selected prefix.  The config also
provides the exact ordered 39-certificate list required by normalized
`verify_all.hl`.

In addition to the eight stratum boundaries, the plan exposes diagnostic
cutpoints `d0-diagnostic-through-002` and
`d1-diagnostic-through-018`.  They use the same snapshot, action-ledger, and
receipt validation, but do not claim that the base stratum completed.

The runner inserts one pinned ledger-checker phrase immediately after each
exact `#flyspeck_needs` directive.  It adds no theorem or axiom.  For each action the
checker requires the exact next index and logical identity, then requires the
CakeML logical-source ledger either to remain exactly unchanged for a loader
skip or to become exactly the expected identity consed onto the previous
ledger for a load.  Any other delta fails before the marker is printed.  The
boundary check requires the complete ordered action-event ledger and no pending
source identity.  Every event line contains a fresh 128-bit attempt nonce and
must match the exact line grammar; quoted source text and prefixed or suffixed
strings cannot satisfy the parser.  The host accepts an attempt only when every
exact marker appears once in order, the final boundary marker appears once, no
top-level error is present, and the process exits zero.

Before generating the control program, the runner copies every compiled-
process runtime source,
normalization, generated input, deterministic process input, linked CakeML
output, harness file, and selected cumulative prefix into a disjoint attempt-
local snapshot.  It also archives the complete linked-provenance JSON and exact
relocation-safe bootstrap record/log copies plus the exact loader, libc, and
libm objects named by its ELF closure.  The same inventory retains the exact
captured bytes used to compile the four local Python helper modules, the
startup-captured top-level runner bytes, the pinned `/proc/self/exe` Python
image, and its pinned base ELF role/file closure.  The exact fixed `git`,
`readelf`, `ldd`, and `patch` program files used by the controller are retained
too.  Every copied byte must match the independently reconstructed plan, linked
provenance, or pinned controller contract; duplicate
paths must be byte-identical, and the snapshot inventory is content-addressed.
Snapshot files and directories and the generated control inputs are made
read-only.  Before and after execution, the runner resolves the exact snapshot
executable's ELF closure and requires it to match the archived record; linked
artifacts with RPATH/RUNPATH or unexpected dependency roles are rejected.  The
compiled process reads only attempt-local source/input paths under a minimal
fixed `PATH` and `LC_ALL=C`; only validated decimal CakeML heap/stack sizes are
forwarded and the exact mapping is written into the attempt/receipt, while
`LD_*`, `GLIBC_TUNABLES`, `BASH_ENV`, and `ENV` are forbidden.
It is launched directly, without an unrecorded timing wrapper; host Python
`getrusage` supplies diagnostic child measurements, not a compiled-Candle
attestation.  The runner then rehashes the complete snapshot and all control
inputs and reauthenticates the original repositories, plan, linked executable,
captured local Python sources and their exact linked-commit blobs, pinned Python
image/ELF closure, and retained host tools after the process exits.

Each run writes the generated config, instrumented prefix, standard input,
fingerprint postlude, combined log, initial `attempt.json`, and final
`receipt.json` into a new output directory.  Failed and timed-out runs also
retain a receipt once process launch has begun.  The initial attempt and
snapshot records are made read-only, rehashed postflight, and their exact
digests are retained by the receipt.  SIGTERM/SIGINT interrupt and fail a live
child; after reaping they are blocked through postflight and the atomic final
write, with already pending interrupts recorded as failure.  A
snapshot/preflight failure before `attempt.json` exists removes only the newly
created incomplete output tree, so the same requested path can be retried.
Process groups are terminated
and reaped on timeout, interruption, or runner exceptions, and receipt writes
are atomic.  A retry is always a fresh cumulative replay from action zero; no
process-state checkpoint or suffix-only continuation is claimed.

The default child limits are 24 hours of CPU time, 48 GiB of virtual address
space, and 8 GiB per output file, in addition to the 24-hour wall timeout.
They are recorded in the attempt and enforced before the CakeML process is
executed.  The receipt records child user/system CPU, maximum resident set,
and major/minor page faults.  Command-line limits may be lowered; address space
and output-file limits cannot be raised above 120 GiB and 16 GiB respectively.
The address-space default remains 48 GiB; the higher ceiling is reserved for
measured proof/corpus stages that need it.

The LP-support and later boundaries emit the canonical structural identity of
`Linear_programming_results.linear_programming_results_th`.  At the final
boundary, the postlude additionally loads the pinned Candle L2 target and emits
identities for the nonlinear theorem, Flyspeck implication, and final Candle
implication.  The same postlude emits the structural-v2 post-state identity for
the complete type-constant, term-constant, primitive-definition, and global-
axiom tables.  Every observed theorem must have zero hypotheses, and theorem
and post-state evidence must agree on exactly three global axioms.  Until
independently approved reference identities are installed, receipts label
these records `observed_uncompared`.

Example (after a linked verified binary exists):

```sh
/usr/bin/python3 -I -S candle/flyspeck_stratum_runtime.py \
  --candle-script ./candle.sh \
  --plan-root /project/flyspeck-candle-runs/v13-stratum-plan-$(GIT_CONFIG_NOSYSTEM=1 GIT_CONFIG_GLOBAL=/dev/null /usr/bin/git rev-parse --short=7 HEAD) \
  --boundary 00-base-through-029 \
  --write /project/flyspeck-candle-runs/v13-stratum-base-attempt-001
```

A successful source-action receipt is not by itself S2 or S3 evidence.  Those
claims additionally require the approved semantic fingerprints and the exact
coverage/assumption checks specified by the release contract.

The runner requires exact direct-script `.py` startup under the complete pinned
default `-I -S` flag set; imported/module/cache startup and optimization flags
are rejected.  It executes its four local helpers from captured `.py` bytes
under private module names rather than consulting bytecode caches, and rejects
a runner or helper outside the authenticated Candle tree.  Git validation uses
fixed paths, locale/path, disabled system/global configuration, and no
prompting; it disables replacement objects and index accelerators, rejects
special index flags on the five controller sources, and compares their captured
bytes with blobs from the exact linked Candle commit.  The broader Python
standard library/native-extension closure,
dynamic/interpreter closures of the four retained host tools, the kernel/vDSO,
and hostile pre-start mutation remain in the host trust boundary; the retained
Python image/base ELF and host-tool files are not presented as a complete host
execution proof.  An independent verifier should recheck the raw snapshot,
log, attempt, and receipt before promoting an approved fingerprint result.

The read-only content-addressed snapshot closes ordinary mutable-input races,
and the action checker now distinguishes each outer action's exact logical-
ledger load or skip transition.  It is still not a loader-owned trace of the
internal physical-path cache and does not expose every ordinary nested
`needs`/`loads` event.  Filesystem modes also are not a kernel-level immutable
snapshot against a hostile same-UID process that can change and later restore
them. Build, repository-launcher, and direct-attempt processes take a
cooperative exclusive/shared lock to prevent accidental concurrent mutation;
noncooperating hostile same-user mutation remains outside the evidence model.
Consequently a successful receipt remains diagnostic and
`s2_s3_evidence` stays false pending approved semantic identities and the
release coverage gates.  The per-file limit is not an aggregate disk quota,
and process-count/aggregate descendant RSS remain external-supervisor
responsibilities in this revision.
