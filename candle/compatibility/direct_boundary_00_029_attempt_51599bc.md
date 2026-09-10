# Direct boundary 00--029 development attempt at 51599bc

This records DEVELOPMENT / NON-RELEASE evidence only. It is not qualified or
promotable evidence and makes no S1, S2, S3, or release claim. No qualified S1
runtime, source, report, transcript, or evidence byte was changed.

## Hol_pervasives compatibility batch

The immutable predecessor attempt at
`/project/flyspeck-candle-runs/v14-dev-direct-boundary-67be95d-attempt-001`
failed before every boundary action in `general/hol_pervasives.hl`: its dynamic
`needs` definition referenced the unavailable `loadt`. Its log has SHA-256
`246685eda25eb901ca0853a77ae4d5268ebc28dd1a60cb5a39e53961498f2f36`
and its receipt has SHA-256
`c769119680e26649f8b923d3efaf9ad5e8011ddfeb447698aee6e21450376076`.

Commit `51599bc14dc4e9d03cc0f11a3bdf5fcc098569c2` adds the hash-pinned
`PROJECT-HOL-PERVASIVES-S3-COMPATIBILITY-001` normalization. The selected
graph has no call to `Hol_pervasives.needs`, so that dynamic loader definition
is replaced with an explicit failure. The file's old string-list `sort (<)` is
replaced with the exact comparator already used for the same free-variable
expression by current Candle tactics:
`fun x y -> String.compare x y < 0`.

The normalized file is 2,365 bytes, SHA-256
`a082b217a7942fa1344ae3034ee9776ed1368d0a732043a43d52f8dc2b23ad41`,
and MD5 `fe90a871fbd8e40750f5445480af2e40`. A complete streamed file probe after
the real `hol.ml` exported the module, observed the dynamic `needs` failure,
and passed the string-order oracle. The probe log has SHA-256
`4f6d052eda7af8ef6526dfce43d723d4bc3d7983a5cacd4c6be36dc9a109bcc1`.

The final focused gates passed: normalizer 17/17, manifest 28/28, parser
diagnostic 56/56, all-inventory 17/17, pilot selection 20 exact nodes,
all-inventory selection 400 exact nodes, and the new Hol_pervasives runtime
gate. Manifest reconstruction passed 297 roots, 400 nodes, and 43 inputs. The
regenerated manifest, normalization contract, pilot descriptor, and
all-inventory descriptor SHA-256 identities are respectively
`b1f60b07361601624bc8d13c7bf05d8495dc97692016a1efc8ab1b1361f4dc49`,
`76f459b6dff99255bbf935fdbd989f63faca4681177cd737b3352f17c00558d1`,
`f7caba9aec27fc7dacf866dc0af2d77147d2f4c0ea901a54fd592cd3878ba669`,
and `52acd5654179726f91ce5e54215c6ac184742df4603111d1fd704cb3d7037422`.

## Fresh development run

Fresh exact-head overlay, generated-input, and plan roots are:

- `/project/flyspeck-candle-runs/v14-normalized-overlay-51599bc-dev-001`;
- `/project/flyspeck-candle-runs/v14-generated-inputs-51599bc-dev-001`;
- `/project/flyspeck-candle-runs/v14-stratum-plan-51599bc-dev-001`.

Independent reconstruction matched all 297 plan actions and all 10 prefixes.
The plan SHA-256 is
`90c2345a0ed4b5ffcbf94f720d9b0289e2e5c6c06291b78706ffdbd78f2697d6`.
The attempt root is
`/project/flyspeck-candle-runs/v14-dev-direct-boundary-51599bc-attempt-002`.
Its exact launch is in `launch-command.txt`. It used one CPU and the existing
development Candle binary, SHA-256
`7c6705199dae8ecf79a72a85d65ab6a4727b411cdfd34f86f999151a2d292ced`,
not an exact-head rebuilt runtime. The source-trace observer and release
check/postlude were deliberately omitted.

The nonce `f84a975381900399e6415e07dbba1c8e` was exact across the nonce file, both
runtime-config fields, and all 30 instrumented markers. The actual prefix has
SHA-256
`a0bbb5d977538a837bd88ae6d905a6b6fe8afddff8dc286e33ce13405e683975`
and MD5 `2f4e7fa31c88b2fd3c1639b0f6071ff5`.

An independent post-launch audit found inactive copied source-trace metadata
that still names the prior prefix identities `88f54834...` / `87bcbe86...`
and an `ee253a1` postlude path. This functional run never calls
`Cakeml.configureSourceTrace`; its stdin loads only the current config, setup,
and current prefix, and omits check/postlude. The stale table was therefore not
consumed and does not explain the observed failure. It is nevertheless a real
harness-copy defect and must be removed or regenerated before another copied
development launch. Action counting below uses only exact nonce-bound lines.

## Result and next genuine failure

Normalized `parser_verbose.hl`, `debug.hl`, `print_types.hl`, and
`hol_pervasives.hl` loaded successfully. The setup also completed
`Multivariate/flyspeck.ml` and the `general/state_manager.hl` source action.
This closes the observed Hol_pervasives incompatibility for this functional
run.

The next genuine compatibility failure is near the terminal utility section
of normalized `text_formalization/build/strictbuild.hl`. Original line 248,
normalized line 237, defines the unused reporting helper with:

```text
let oc = open_out_gen [Open_append;Open_text] 436 (flyspeckpath "logs/log.txt") in
```

Candle reports `Undefined variable: open_out_gen at line 9` while compiling
`let build_and_report() =`. This is a bootstrap-source/runtime-API
compatibility failure after the prerequisite loads and before stratum
preflight; it is not a direct Flyspeck action failure. Candle exposes only the
truncating `open_out`, so silently mapping the append/permission operation to
that API would not preserve its semantics.

No preflight marker and no line beginning with the exact nonce-bound action
success marker were emitted: 0 actions were reached and 0 passed. The later
action-0 `Already loaded` message does not count. Its following `Undefined
variable: candle_flyspeck_stratum_commit_action` is a cascade because setup
failed before defining the ledger helper.

The run took 41:06.34 at 99% of one CPU, with maximum RSS 4,340,224 KiB. The
interactive runtime exited zero despite the source errors. The immutable log
has SHA-256
`1822c8db3bb511f196490e1689f4e758ca2d9758f2ee207884f023c638f0e537`.
The fail-closed development receipt has SHA-256
`f7ba0d5566a422d67349ff97c79a02639812d16337986a203ab40830bd6f896a`.

Repository-wide selected-source audit finds only the exact
`build_and_report` definition and no caller. The narrow next hypothesis is to
extend the existing strictbuild normalization by replacing that whole unused
binding with an explicit fail-closed unit function, protected by an
exact-definition-only selected-graph non-use gate. It must not introduce a
general `open_out_gen` shim. This preserved attempt must never be promoted.
