# Flyspeck certificate reflection: profiling boundary

Date: 2026-09-19 UTC  
Status: DEVELOPMENT / NON-RELEASE; no S2/S3 or speedup claim

## Outcome so far

The expensive paths are now separated into externally measurable phases
without changing theorem expressions or checker interfaces. Candle's selected
runtime deliberately makes `Sys.time` and `Unix.gettimeofday` return zero and
does not expose `Gc.stat`, so in-process elapsed/GC measurements would be
fiction. The profiler instead inserts flushed text markers and uses a read-only
external observer to sample wall time, process CPU, RSS, and high-water RSS from
`/proc`.

The first plan-changing nonlinear result is structural. The authenticated
`break_case_log.hl` contains:

- 463 explicit partition trees;
- 7,479 `Iarg_leaf` nodes;
- 15,462 facet nodes and 7,016 bisect nodes;
- 22,941 generated explicit subdomains (`leaf + facet`), at maximum tree depth
  40; and
- 28,691,131 ms (7h 58m 11.131s) of stored C++ interval-check runtime.

The median explicit tree has 6 leaves, 20 generated subdomains, and 24.219 s
of stored C++ time; the 90th percentiles are 45 leaves, 127 subdomains, and
162.722 s, and the 99th percentiles are 134 leaves, 389 subdomains, and
476.538 s. The largest tree has 167 leaves and 491 subdomains, so it is a
bounded but substantial first reconstruction profile rather than a toy leaf.

The last number is historical checker telemetry embedded in the certificate,
not a measurement of Candle reconstruction. It does confirm that useful
reflection must include the nonlinear leaf-checking semantics eventually, not
only list/tree plumbing. The current direct source separately requires 23,242
`all_parameters` and reconstructs 7,479 leaf nodes at runtime.

## Exact current checker boundaries

### LP terminal

`Flyspeck_lp.verify_lp_certificate` first converts the serialized hypermap,
runs `compute_all`, derives contravening conditions and reusable base
inequalities, and then traverses the split tree. Each terminal:

1. converts certificate `int64` coefficients to HOL real-integer terms;
2. selects and simplifies named inequality theorems;
3. multiplies and combines their linear forms;
4. assembles variable-bound and target-variable cancellation theorems; and
5. proves the final numeral is nonzero before discharging the hypermap
   hypotheses.

The marker profile splits those into file decode, inequality initialization,
`compute_all`, base inequalities, certificate reification, constraint theorem
construction, constraint combination, the global inequality, variable bounds,
cancellation, the final numeral check, and final discharge.

The smallest performance-bearing reflective boundary is not Marshal decoding.
A native OCaml diagnostic decoded and traversed the exact `hard_2.dat` 1,000
times in 1.467294 s (1.467 ms/call), and `hard_10.dat` 1,000 times in
5.768445 s (5.768 ms/call). These are native lower bounds, not Candle timings,
but they make file decode an unlikely explanation for 14--24 minute focused
proofs.

The promising LP object-logic boundary is a normalized exact linear
combination checker: encode the selected inequality indices, integer
coefficients, and normalized variable map; compute that the combination
cancels to the required contradiction; and use one generic proved soundness
theorem to recover the existing terminal conclusion. The current fine-grained
theorem path remains the fallback and equivalence oracle.

### Nonlinear reconstruction

`Mk_all_ineq.prep_nonlinear_thml` maps
`Break_case_exec.prove_prep` over the nonlinear IDs. For each ID,
`prove_serialize_processed_idq`:

1. enumerates subdomain propositions with `mk_case_list`;
2. calls `Serialization.mk_ser_thm` for every subdomain;
3. constructs the bisect/facet proof tree with `prove_iargs_cases`;
4. discharges every serialized leaf theorem with `PROVE_HYP`; and
5. rewrites list lengths before the global conjunction is assembled.

This is a better coarse target than reflecting individual `PROVE_HYP` calls.
A proved object-logic partition checker could validate a whole partition tree
and substantially reduce reconstruction theorem traffic while returning the
same inequality theorem.

There is an important assurance boundary: current `mk_ser_thm` checks the
authenticated theorem digest and uses the existing `deserialization` axiom.
Reflecting only the partition tree preserves that existing interface and axiom
set, but does not independently check the analytic leaf result. Eliminating the
axiom requires an explicit interval/nonlinear certificate representation plus
a proved checker for the leaf semantics. A `cv_compute` wrapper around the
current digest import cannot supply that proof. The staged plan should
therefore distinguish:

- near-term: reflected partition coverage/reconstruction over the existing
  authenticated leaf statements; and
- long-term: proof-producing exact interval/nonlinear leaf checking, followed
  by removal of the serialization axiom from this path.

## Instrumentation and reproducibility

- `certificate_profile_instrument.py` fails closed on the input SHA-256 and on
  every exact source anchor. It supports the current LP source and both
  nonlinear reconstruction sources. It also normalizes the development-only
  nonlinear visit counter from OCaml's unavailable `incr r` to the equivalent
  Candle expression `r := !r + 1`; this changes only profiling telemetry.
- `certificate_phase_profile.py` timestamps markers and samples `/proc` without
  writing to the proof process.
- `certificate_profile_summary.py` aggregates repeated terminal/case phases.
- `lp_certificate_shape_profile.ml` and
  `nonlinear_iarg_shape_profile_runner.ml` are native diagnostics only; their
  output is never proof evidence.

Current exact inputs used to validate instrumentation:

- LP source SHA-256:
  `552440a25ea043ab73776775213cb231865e34b46b57e0eea4fb5a33c3363b39`;
- nonlinear `break_case_exec.hl` SHA-256:
  `6bbc369d708b4c5710c6ff91fa98ab0408b72f5178f1873c263bfad5ee88e1b2`;
- nonlinear `mk_all_ineq.hl` SHA-256:
  `08ff0eb708c6b6370e042c1d888ba8bd457b7dbaec12390edd30a57b2afea5dc`.

All probes use fresh checkpoint copies. Failed or partially loaded states are
never reused. Instrumented runs remain development evidence and must reproduce
the existing conclusion, hypotheses, and axiom fingerprint before any speed
comparison is accepted.
