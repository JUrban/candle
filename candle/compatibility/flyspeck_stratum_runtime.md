# Compiled cumulative Flyspeck stratum runner

`flyspeck_stratum_runtime.py` consumes an immutable output of
`flyspeck_stratum_plan.py` and starts one selected cumulative prefix in a fresh
compiled Candle process.  It first validates the linked CakeML provenance.  It
then rechecks the clean repository revisions, the exact plan and
materialization hashes, all 400 source nodes, all 16 normalization outputs,
all 43 generated inputs, deterministic `date`/`whoami` inputs, and the selected
prefix.

The runner inserts one `print_endline` phrase immediately after each exact
`#flyspeck_needs` directive.  This instrumentation changes output only.  A
marker is therefore reachable only after that action has either completed or
made the authenticated already-loaded observation.  The boundary check also
requires no pending source identity and requires every selected logical source
identity to be present in HOL Light's loaded-file ledger.  The host accepts an
attempt only when every exact marker appears once in order, the final boundary
marker appears once, no top-level error is present, and the process exits zero.

Each run writes the generated config, instrumented prefix, standard input,
combined log, initial `attempt.json`, and final `receipt.json` into a new output
directory.  Failed and timed-out runs also retain a receipt.  A retry is always
a fresh cumulative replay from action zero; no process-state checkpoint or
suffix-only continuation is claimed.

Example (after a linked verified binary exists):

```sh
python3 candle/flyspeck_stratum_runtime.py \
  --candle-script ./candle.sh \
  --plan-root /project/flyspeck-candle-runs/v13-stratum-plan-aac2a6a \
  --boundary 00-base-through-029 \
  --write /project/flyspeck-candle-runs/v13-stratum-base-attempt-001
```

A successful source-action receipt is not by itself S2 or S3 evidence.  Those
claims additionally require the approved semantic fingerprints and the exact
coverage/assumption checks specified by the release contract.
