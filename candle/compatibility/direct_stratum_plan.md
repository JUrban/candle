# Direct Flyspeck stratum/prefix plan

`flyspeck_stratum_plan.py` turns the manifest's eight contiguous strata into
eight **cumulative** `#flyspeck_needs` programs.  It also emits two smaller
diagnostic cumulative prefixes through actions 2 and 18 for rebuilt-binary
compatibility triage.  It is a deterministic, fail-closed host planner, not a
Candle runner or checkpoint implementation.

The strata retain the exact 297-entry order from `flyspeck_full_build.ml`:

| boundary | stratum | action indexes | cumulative actions |
|---|---|---:|---:|
| 00 | base | 0--29 | 30 |
| 01 | arithmetic | 30--37 | 38 |
| 02 | nonlinear_support | 38--49 | 50 |
| 03 | analysis | 50--60 | 61 |
| 04 | geometry | 61--151 | 152 |
| 05 | lp_support | 152--184 | 185 |
| 06 | text_formalization | 185--290 | 291 |
| 07 | final_assembly | 291--296 | 297 |

These labels are operational partitions, not claims that a stratum is an
independent dependency unit.  The planner emits no suffix programs.  To retry
or advance to a boundary in a new process, a scheduler must select that
boundary's authenticated cumulative prefix and replay it from action 0.  The
metadata does not serialize, restore, or attest CakeML process or kernel state.

The `d0-diagnostic-through-002` and `d1-diagnostic-through-018` cutpoints are
not roadmap strata.  They run through the same authenticated runtime and exact
outer-action ledger checks, but their receipts remain compatibility diagnostics
and have `s2_s3_evidence` set to false.

For the integration input audited here, materialize with:

```sh
candle_head=$(git rev-parse HEAD)
python3 candle/flyspeck_stratum_plan.py \
  --candle-root /project/worktrees/candle-integration-v13 \
  --expected-candle-base "$candle_head" \
  --flyspeck-root /project/worktrees/flyspeck-v13-source \
  --overlay-root /project/flyspeck-candle-runs/v13-normalized-overlay-ac925270aa6a8605 \
  --generated-root /project/flyspeck-candle-runs/v13-generated-lp-0ca1b5b6 \
  --write /path/to/new-empty-output-directory
```

The command requires a clean Candle descendant of the exact integration base,
an exact clean Flyspeck revision, and authenticates all 400
selected source nodes, all 18 normalized outputs and their receipt, all 43
generated inputs and the prepared-archive receipt, the manifest, and the exact
full-build driver.  Descendant commits cannot silently change a selected input:
the byte checks still use the base manifest's individual hashes.  Output
creation is fail-closed and refuses an existing directory.

`plan.json` is path-independent and content-addressed by the SHA-256 recorded
in the two companion files.  Each action binds its selected original source
digest and, where applicable, its normalization identity and output digest.
Each boundary binds the exact cumulative program bytes and ordered action
prefix.  `host-materialization.json` records machine paths separately.

`host-schedule-template.json` is only a scheduling template.  Its
`not-started`, `running`, `failed`, and `completed` labels can never establish
S2 or S3.  A later verified run must separately authenticate the compiled
Candle binary and runtime inputs, observe every required loader action through
the boundary, terminate successfully, and collect the required semantic
fingerprints.  This planner neither performs nor claims any of those gates.

The lightweight static test is:

```sh
python3 candle/test_flyspeck_stratum_plan.py
```
