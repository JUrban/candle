# Direct boundary 00--029 development attempt at ac97c042

This completed DEVELOPMENT / NON-RELEASE attempt invoked or reached one direct
boundary action, passed zero actions, and emitted zero authenticated action
success markers. It is not schema-5 or schema-6 evidence and makes no S1, S2,
S3, qualification, promotion, or release claim. No qualified Great100/S1
runtime, source, report, transcript, or evidence byte was changed.

## Inputs and execution

The current source head was
`ac97c042a88e78a3a5ca0e52ea579c9cc42121b7`; the pinned Flyspeck commit was
`1ce0353008eba83d3c76ae9a25c3c242e4802d53`. The fresh plan at
`/project/flyspeck-candle-runs/v14-stratum-plan-ac97c04-dev-001` contains 297
actions and its 00-base-through-029 cumulative boundary contains 30. The plan
SHA-256 is
`c489f212fe9ff7432ebfe382ed17b0398d61049ef6cf8216e08282a6a32b80fb`.
The normalization overlay contains 24 authenticated outputs and the generated
input projection contains 43 bindings.

The attempt root is
`/project/flyspeck-candle-runs/v14-dev-direct-boundary-ac97c04-attempt-001`.
It used the existing development CakeML binary with SHA-256
`7c6705199dae8ecf79a72a85d65ab6a4727b411cdfd34f86f999151a2d292ced`,
linked at Candle commit `ee253a1061092ebfaed9fcc2dfac798562af30ff`.
It was not relabeled as an exact-current-head runtime. The stdin loaded only
the minimal no-trace runtime config, current setup, and current instrumented
prefix; check, postlude, archive, publication, and source-trace observation
were deliberately absent.

Nonce `5c7ecb6cb1528ef8c98ce70bf559e12b` appeared exactly once in the runtime
config and once in the nonce file, and in all 30 exact instrumented marker
strings. Removing the 30 instrumentation lines reproduced the 6,656-byte plan
prefix exactly. The instrumented prefix and runtime-config SHA-256 identities
are respectively
`67fab69d59c84c61478d78db576f4df97ecce6772cd6a1c60a48266da1cccef1`
and
`04b139d8163144abb14a00543cb24f43e915ef882b7ab5ac9c18eac8f1ff0b58`.

## Actual progress and failure

Setup completed and emitted its exact nonce-bound preflight marker at log line
184082. The first cumulative directive then invoked action 0 for normalized
`general/hol_pervasives.hl`: line 184086 records normalized-source selection,
and line 184087 records the physical loader cache hit, `Already loaded`.
Action 0 therefore was genuinely invoked or reached.

It did not pass. The instrumentation calls the ledger commit only after the
loader directive returns successfully. Here that commit failed at line 184088
with:

```text
Failure "Flyspeck action was skipped by the physical loader cache without its logical identity"
```

Consequently the exact counts are one action invoked/reached, zero passed, and
zero authenticated nonce-bound action success markers. “Reached” describes
entry into the planned action and loader; the authenticated marker describes a
successfully completed source action plus its post-action logical-ledger check.
Conflating these counts would hide the real progress and the fail-closed
ledger result. No later action was invoked, and no independent cascade followed.

The underlying defect is setup-to-action loader-ledger closure. Setup had
already selected and loaded normalized `hol_pervasives.hl` at log lines
20551--20552, but the logical `loaded_files` state captured after strictbuild
listed only `parser_verbose.hl`, `debug.hl`, and `state_manager.hl`. Thus the
physical cache recognized Hol_pervasives while the authenticated logical
ledger did not contain its expected original identity
`("hol_pervasives.hl","5917b805cae8737b5dd296e2a91613b0")`.
The action correctly failed closed. This is not a new Flyspeck theorem,
semantic, parse, or runtime-API compatibility failure, and this report does not
propose or implement a loader correction.

The run consumed 41:37.70 wall time at 99% of one CPU and reached a maximum RSS
of 4,341,120 KiB. The interactive REPL exited zero at EOF after reporting the
caught source exception; that process exit does not override the missing
authenticated success marker. The immutable log and timing file have SHA-256
identities
`840c115cbb55ac1f6d204fd4e41c1b0c399d2f424fa9f6e6c0452bc144fb9892`
and
`d408603240d239f518cf8ce08b48d669156fe1a4f11abf3e509b1655508786`.
The attempt-local development result receipt records these identities and the
marker/invocation distinction. This attempt must never be promoted.
