# Direct boundary 00--029 development attempt

This records DEVELOPMENT / NON-RELEASE evidence only.  It is schema 5,
explicitly has `s2_s3_evidence = false`, and makes no S1, S2, S3, or release
claim.  No qualified S1 runtime, source, report, transcript, or evidence byte
was changed.

## Bound inputs and launch

The attempt used Candle commit
`ee253a1061092ebfaed9fcc2dfac798562af30ff`, Flyspeck commit
`1ce0353008eba83d3c76ae9a25c3c242e4802d53`, and the authenticated linked
CakeML provenance record with SHA-256
`e38af6d97d7c19869271fdf50ec3c1f0f6d4c9596906cc9ce5696f1d9f22c107`.
The source-contract transition receipt has SHA-256
`fceaf04e06ab3b8840a919ae3947c75907d16b28da756d993af6034a8dab5d8f`.

The fresh plan was
`/project/flyspeck-candle-runs/v14-stratum-plan-ee253a1-attempt-001/plan.json`
(SHA-256
`441727ed943a7f18c9c34add046ef29252830598fb19194b6cbc79e8282ce011`).
The fresh output root was
`/project/flyspeck-candle-runs/v14-stratum-base-ee253a1-attempt-001`.
The exact launch was:

```text
/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C /usr/bin/python3 -I -S candle/flyspeck_stratum_runtime.py --candle-script ./candle.sh --plan-root /project/flyspeck-candle-runs/v14-stratum-plan-ee253a1-attempt-001 --boundary 00-base-through-029 --cml-heap-size-mib 4096 --evidence-schema 5 --write /project/flyspeck-candle-runs/v14-stratum-base-ee253a1-attempt-001
```

The controller PID was 3572173 and the Candle child PID was 3579290.  The
attempt ran from `2026-09-10T03:00:12.607204Z` to
`2026-09-10T03:06:28.512997Z`, did not time out, and reported a maximum child
RSS of 4,234,496 KiB.  Its configured limits were 4 GiB Candle heap, 48 GiB
address space, 24 hours of CPU/wall time, and 8 GiB per output file.

## Result and first genuine failure

The corrected loader authority worked: relocated `hol.ml`, `hol_loader.ml`,
`hol_lib.ml`, and the lexical linked-build request
`candle/build/insulate.ml` were authenticated and evaluated.  The previous
pre-action linked-runtime provenance blocker is therefore cleared.

The first genuine Candle/Flyspeck compatibility failure is the normalized
`text_formalization/general/parser_verbose.hl`.  Its source-trace request 102
is a child of request 101 for normalized
`text_formalization/build/strictbuild.hl`.  Candle reports at line 74:

```text
ERROR: Type mismatch between string -> string and string * pretype -> _162 at line 74

let parse_preterm_verbose =
^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

No Flyspeck action was reached and no action passed: 0 reached, 0 passed (30
actions were planned for this boundary).  The later undefined `loadt` while
entering `hol_pervasives.hl`, undefined action-ledger state in the check, and
terminal `Failure "Candle source trace has failed"` are cascades after the
parser error, not additional independent boundary failures.

The immutable log is
`/project/flyspeck-candle-runs/v14-stratum-base-ee253a1-attempt-001/candle.log`
(SHA-256
`b4a4132c8cc5773810948f89989eaa8f1e23d7817c776c4b13f762e244730dd8`).
The immutable failed receipt is
`/project/flyspeck-candle-runs/v14-stratum-base-ee253a1-attempt-001/receipt.json`
(SHA-256
`a43090b05f2d2a78904dfcacde26692cf0590d568eb06ed58e5659f0c4a47ffd`).
Both are mode 0444.  The receipt is failed, has zero validated action markers,
and says `postflight_reauthenticated = true`; its fail-closed validation error
is `ContractError: physical source trace failed: repl`.

The expected trace contract is schema 2 with 131 exact bindings and ordered
binding SHA-256
`e56791417d0103753062abd2fa5a8a56c260209dc1dec367f4c50883bf1a8f6a`.
An independent prefix check matched every request field to those bindings and
validated request IDs, parent stack, outcomes, and cache state through the
first failure: 103 requests, 100 outcomes, 43 cache skips, and 59 distinct
keys.  The active stack at failure is exactly runtime setup / strictbuild
request 101 / parser request 102.  The initial request record carries the
interactive prompt prefix (`# `); this prefix normalization was explicit in
the independent diagnostic and is not represented as a successful closed
trace.

## Relocation dry-run audit status

Before this run, the relocation harness was tightened to call the runner's
complete `validate_plan`, bind and compare the logical source,
alias/loader/normalization closures, compare the attempt's expected physical
trace, validate the receipt-bound log observation, and use each boundary's
real fingerprint requests (including boundaries 05--07).  The linked-runtime
authority and those audit corrections passed 69 focused tests together,
including changed bytes, symlink, hard-link, substituted parent/path, missing
linked output, and relocation-identity adversaries.

The post-failure relocation command did not yield a success report.  It
stopped before log-observation validation because direct reconstruction from
the plan's host roots is physically different from the immutable attempt
snapshot paths; independently, the failed attempt has no closed physical
observation.  The host/snapshot reconstruction mismatch is a
development-harness follow-up, not evidence that the parser attempt
succeeded, and it was not extended or patched in this turn.

The next functional work item is therefore the `parser_verbose.hl` type
mismatch above.  This preserved attempt must not be promoted or reused as
release evidence.
