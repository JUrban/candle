# Flyspeck decimal-float performance gates

These gates address the v1.3 performance risk created by lowering every OCaml
decimal literal to a call of `Option.valOf (Double.fromString ...)`.  They are
performance evidence only.  They do not check theorem identities, proof
history, or the final Flyspeck result and are never S2 or S3 evidence.

## Exact real-source histogram and load

`generate_flyspeck_float_performance.py` requires the production manifest and
a clean Flyspeck worktree at pinned commit
`1ce0353008eba83d3c76ae9a25c3c242e4802d53`.  It authenticates
the manifest at branch base `5358f96fd52191a321893db8db25810efaafbbbb`
with SHA-256
`2bb61e249baa2e8158da4b57f419a269504c7617f6bccefdec5465fcaab85380`
and authenticates
`text_formalization/nonlinear/break_case_log.hl` as:

- 827,309 bytes;
- MD5 `0d51ddd36c8501cdf881eef684752195`; and
- SHA-256
  `2b3c74156a5ee9a6b3b5b6905ff28a7fb21e7c50052ad37887b90b9ed3d5e499`.

After masking nested comments and strings, the generator requires exactly
15,462 decimal tokens and 15,462 `Iarg_facet` constructors.  Their complete
1,705-spelling histogram has canonical SHA-256
`242086f2834fbcb3028d411b40bb37a7105be13ff78b6c1d487805ac7ee7edda`;
11,640 entries are spelled exactly `0.5000`.  The same source must contain
7,479 `Iarg_leaf` constructors and 463 `add_case` actions.  The generated JSON
retains the complete histogram, not only these headline counts.

The compiled gate loads the small `break_case_type.hl` setup outside the
measurement interval, then measures an exact `#use` of the authenticated
`break_case_log.hl` copy through its EOF marker.  Both source files and the
manifest that authenticates them are copied read-only into the evidence
directory before any session.  It subsequently requires the resulting
`Break_case_log.break_data` to contain exactly 463 cases.

## Call-time versus hoisted conversion

The generator also emits two matched workloads, each using the exact decimal
spellings `10000.0`, `1.0`, and `1.0e-10` and checking their expected Word64
representations on every iteration.

- In `candle_float_call_time_loop.ml`, all three literals remain textually
  inside the called observation function.
- In `candle_float_hoisted_loop.ml`, the literals are evaluated in three
  top-level bindings and the otherwise matching observation function reads
  those bindings.

The default is 10,000 calls.  The comparison measures externally observed
wall time; it does not claim a specific optimizer conversion count.  Each
workload runs in its own fresh process.

## Provenance and measurement boundary

`run_flyspeck_float_performance_gate.py` rejects a Candle tree unless
`cakeml_artifact_provenance.py` validates its linked record, exact Git state,
manifest pin, verified CakeML/HOL4 coordinates, executable, generated boot
inputs, launcher aliases, and ELF dependency closure.  It then launches only
that tree's authenticated `candle.sh` with the fixed runtime environment.

Every one of the three measured sessions must:

1. reach the initial Candle prompt;
2. load that Candle tree's `hol.ml` through the explicit finished-loading EOF
   marker;
3. evaluate `(check_axioms (); true)` successfully; and
4. load the measured source through its EOF and source-specific success
   boundary without a parser, error, exception, inactivity, or wall-time
   failure; then
5. evaluate `(check_axioms (); true)` again as a session postflight.

Elapsed time begins immediately before sending the measured `#use` and ends at
its EOF marker.  RSS sampling begins immediately before that
`#use` and ends after its EOF and prompt, at 50 ms intervals.  Reported RSS is
total root-process/process-tree RSS during the interval and includes the
retained full-HOL baseline; it is not attributed incremental allocation.
Process-tree RSS is a sum and can double-count shared pages.  Fresh processes
prevent the large retained `break_data` value from contaminating either loop
comparison.  Successful sessions send EOF and require zero exit status and no
terminating signal; forced termination is reserved for failed sessions.

Optional elapsed and ratio ceilings can turn a reviewed baseline into an
explicit regression threshold.  When no ceiling is supplied, the gate checks
only successful completion within the independently recorded wall timeout and
still emits exact elapsed/RSS observations; it does not invent an unreviewed
performance acceptance threshold.  Machine-readable output is therefore
`observation_complete`, not `pass`, unless all three ceilings are supplied and
the pinned 10,000-iteration workload is used.  A complete supplied policy is
reported as `thresholds_satisfied` or `thresholds_failed` and separately sets
the boolean `performance_accepted`.

On a completed run, the user-selected evidence directory is never temporary.
It retains the generated histogram and both generated loop sources, their
content-addressed input receipt, the exact linked-provenance JSON, its durable
bootstrap record and successful build log, the exact loader/libc/libm object
bytes, the exact gate configuration and fixed runtime environment, three
complete session transcripts, and `report.json` with elapsed/RSS observations
and hashes.  The runner revalidates the linked record, pinned Flyspeck
manifest/source, all generated inputs, and every archived runtime-provenance
input after the sessions.  Each successful scenario is journaled immediately.
After attempt creation, a later failure atomically produces a `receipt.json`
with the error, completed scenario measurements, any malformed-journal hashes,
feasible linked/source postflight, and a content inventory of all retained
files.  An I/O failure that prevents that receipt is reported explicitly
alongside the original gate error.  The linked-record revalidation is the same
fail-closed check used by `cakeml_artifact_provenance.py check-linked`; the
report records all of these postflights.

## Commands

Generate and inspect the exact host-side inputs:

```text
/usr/bin/python3 -I candle/compatibility/generate_flyspeck_float_performance.py \
  --candle-root /path/to/clean/candle \
  --flyspeck-root /path/to/pinned/flyspeck \
  --output-dir /tmp/candle-flyspeck-float-performance-inputs \
  --iterations 10000
```

Run the compiled performance gate into a new, user-selected evidence
directory:

```text
/usr/bin/python3 -I candle/compatibility/run_flyspeck_float_performance_gate.py \
  --candle-root /path/to/provenance-bound/candle \
  --flyspeck-root /path/to/pinned/flyspeck \
  --evidence-dir /path/to/results/flyspeck-float-performance-attempt-001 \
  --iterations 10000
```

The evidence directory must not already exist and cannot be inside either
source tree.  Successful output contains `attempt.json`, `gate-config.json`,
`provenance/`, `sources/`, `generated/`, `transcripts/`, per-scenario journals,
`report.json`, and `receipt.json`.

Reviewed thresholds, when available, are passed explicitly with
`--max-break-case-seconds`, `--max-call-time-seconds`, and
`--max-call-to-hoisted-ratio` and are preserved in the report.

## Current evidence limit

The host generator and its fail-closed unit tests reproduce the pinned source
histogram and generated input receipts.  No compiled elapsed/RSS result is
claimed by this document.  A local build record, if present, is acceptable
only when the complete current schema-2 linked-provenance check passes.  The
gate must not be weakened to use an unbound executable or skip the full-HOL
EOF/`check_axioms` preflight.  A run becomes performance evidence only after
the verified parser bootstrap is linked and that complete provenance check
passes; even then it remains outside S2 and S3.
