# Direct Flyspeck boundary 04: v41 combined Marchal3 repair

Date: 2026-09-12 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct action progress

The exact cumulative frontier remains 92 actions reached and 91 passed at
boundary 04 (`00-base-through-151`): actions 000--090 are exact-green, and
action 091 is `packing/marchal3.hl`. The first 30-action boundary is 30/30
exact-green. Full direct S2 and nonlinear/LP S3 remain open.

The v40 exact replay passed preflight and emitted 91 ordered nonce-bound
success markers for actions 000--090. Its normalized action 091 selected the
native Strictbuild function and traversed many finite proof searches, but
failed once with `Failure "solve_goal: Too deep"` and emitted no action-091
marker. The run consumed 1:22:26 wall time with maximum RSS 4,482,688 KiB.
Its frozen `candle.log` SHA-256 is
`442d9cd76b92e4c1974a9498cf034ceaf0028af1c35f92c960e9350b857c30e9`;
the complete failure record is stored beside that log.

## Complete observed Marchal3 compatibility set

The v40 result separates two independent defects:

1. Candle's transitive `open` behavior leaked imported
   `prove_by_refinement` members from intermediate modules, unlike native
   OCaml. The v40 qualified line-40 binding corrected function selection and
   eliminated the v38/v39 reverse-path runaway.
2. On the correctly selected Strictbuild path, the exact replay reproduced
   the preserved step-indexed failure signature in
   `LEFT_ACTION_LIST_3_EXISTS`, zero-based refinement step 23, on goal
   `{u0,u1,u2,u3} = {x,z,t}`. Five later cases contain the same source
   construct and proof obligation class.

The v41 batch therefore retains the validated qualified binding and restores
the six deterministic set substitutions first developed in v38. It excludes
the v39 inverse rewrite: correctly resolved Strictbuild has not independently
failed at that final inverse proof, whose original bytes remain present.

Neither `fix-top100` nor the relevant historical Candle branches contains a
Marchal3 repair. Historical branches were treated as leads only; both actual
failures and both repair components were reproduced independently.

## Bounded proof-preserving repair

The first operation binds the native function after the complete open chain:

```ocaml
let prove_by_refinement = Prove_by_refinement.prove_by_refinement;;
```

Each of the six equality cases has already proved one equality among `x`,
`y`, `z`, and `t` and retains
`{x,y,z,t} = {u0,u1,u2,u3}`. Its broad `SET_TAC` search is replaced by:

```text
ONCE_REWRITE_TAC[GSYM (ASSUME retained_set_equality)] THEN
SUBST1_TAC (ASSUME proved_point_equality) THEN
REWRITE_TAC[INSERT_AC]
```

This proves the identical three-element set goal deterministically. The case
order, preceding point-equality proofs, intermediate goals, following
cardinality contradictions, and final theorem are unchanged. No theorem
statement, hypothesis, definition, axiom, proof intent, or global search limit
changes.

The pinned upstream source remains 254,482 bytes, MD5
`ad1052eeb7d9979e8fd3069d2eb4a35c`, SHA-256
`191528d2c1dc3542751507d2b44880f3b4f07efe00ea9267b66bc10e28d21926`.
The v41 normalized source is 254,857 bytes, MD5
`343bf227429455b5a0150624094c145c`, SHA-256
`2905495ab3463933a8d88f44bcc406cfd1fa51192a9f578e8ac85f77679f9397`.
Its exact operation lines are 40, 3869, 3878, 3887, 3896, 3905, and 3914.
The original `UP_ASM_TAC THEN MESON_TAC[PERMUTES_INVERSE_EQ; ...]` remains
present, and the v39 replacement is absent.

## Validation and frozen identities

- native/original/normalized open-resolution oracle: PASS;
- all-six polymorphic deterministic set-substitution theorem gate: PASS;
- normalization contract check: PASS, 58 entries and 232 unique operations;
- normalization tests: PASS, 18/18;
- manifest tests: PASS, 28/28;
- manifest write/check fixed point: PASS, 297 roots, 400 source nodes, 43
  generated inputs;
- exact seven-operation materialization, normalized identity, and original
  inverse-proof preservation: PASS;
- JSON parse, shell syntax, and `git diff --check`: PASS.

The frozen implementation commit is
`50e66f65a327c1b94a9caeb92753861dfe77bc6f`. Derived identities are:

- normalization contract SHA-256:
  `7a9085530d9e147e57ac3936e8eea7584464e2af4ed1314653f7040f59299d4e`;
- manifest SHA-256:
  `d0e947a4dda1940bd1b778eb610cbe5d6677c0fa895ba8b2fde9c2245db7e18c`;
- loader SHA-256:
  `fc27dae92a7ae705991401f8600fa2d03af573ebc63bfa1c86f28863c45e7a73`;
- generated source-digest/full-build MD5:
  `c66f3ae6caa53e0257a557b4768d9f5c` /
  `dd8e7ba2d365d11b3ce7a0ac82f937ad`.

## Next work

Materialize a fresh overlay and boundary-04 plan from the final report head,
then launch a fresh exact DEVELOPMENT / NON-RELEASE cumulative replay from
action zero. Action 091 receives no pass credit until normalized Marchal3
completes and emits its nonce-bound marker. If it passes, continue through
actions 092--101 and only then integrate the separately isolated action-102
`YSSKQOY.hl` open-resolution candidate if the exact run reproduces that
failure.
