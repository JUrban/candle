# Direct Flyspeck boundary 04: v42 complete Marchal3 normalization

Date: 2026-09-13 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct action progress

The exact cumulative frontier remains **92 actions reached / 91 passed** at
boundary 04 (`00-base-through-151`): actions 000--090 are exact-green and
action 091 is `packing/marchal3.hl`. The first 30-action boundary remains
30/30 exact-green. Full direct S2 and nonlinear/LP S3 remain open.

The fresh v41 exact replay again passed actions 000--090 with 91 ordered,
nonce-bound success markers. Its v41 Marchal stream selected the qualified
Strictbuild path and cleared all six deterministic set substitutions, so the
v40 zero-based refinement-step-23 `solve_goal: Too deep` failure did not
recur. It then reproduced v38's final `PERMUTES_INVERSE_EQ` MESON runaway
trace exactly through 4,544,914 search nodes without an action-091 marker.
The bounded run was intentionally interrupted after 1:29:55. Candle emitted
one `EXCEPTION: Interrupt`, returned to the development prompt, and exited 0
under non-release REPL behavior. Its immutable `candle.log` SHA-256 is
`041ba43f32a64c46eecf0209043d5510b1b76d2faa6e8b6d9f933e4a2fbf3b62`;
the adjacent interruption note has SHA-256
`c73974ced910e39f00512aaa245a11ad0dcc1e89cd758fe14eb269d6bc8471d4`.

## Historical lead and independently reproduced defect

Earlier bounded historical inspection found no Marchal source patch in
Candle `origin/fix-top100` or `upstream/fix-top100`, and the relevant
Flyspeck refs retain the same source construct. The isolated v39 branch
contained a direct inverse rewrite as a development lead. It was not treated
as authority: v41 independently reached the qualified Strictbuild path,
cleared the preceding six cases, and reproduced the exact final runaway
sequence before the rewrite was adopted.

## Narrow proof-preserving completion

At the unchanged final intermediate goal, the context contains
`p permutes 0..3` and the already-proved conjunction
`p i1 = 0 /\ p i2 = 1 /\ p i3 = 2 /\ p i4 = 3`. The unique broad search

```text
UP_ASM_TAC THEN MESON_TAC[PERMUTES_INVERSE_EQ; ASSUME image_equalities]
```

is replaced by

```text
REWRITE_TAC[MATCH_MP PERMUTES_INVERSE_EQ
  (ASSUME `p permutes 0..3`)] THEN ASM_REWRITE_TAC[]
```

`MATCH_MP` instantiates the existing permutation theorem; the rewrites reduce
the four inverse equalities to the retained image equalities, which
`ASM_REWRITE_TAC` closes. No theorem statement, hypothesis, definition,
axiom, intermediate goal, case order, or proof intent changes, and no global
search limit is raised.

The v42 normalization has exactly eight hash-pinned operations: the v41
qualified Strictbuild binding, its complete six set substitutions, and this
one inverse rewrite. The pinned original remains 254,482 bytes, MD5
`ad1052eeb7d9979e8fd3069d2eb4a35c`, SHA-256
`191528d2c1dc3542751507d2b44880f3b4f07efe00ea9267b66bc10e28d21926`.
The v42 output is 254,835 bytes, MD5
`29073443eaf8e958b05cb238f3f3aacc`, SHA-256
`a3c523ac09ac587fdc335a89a50b711edb7b83051d5bb0b3ba36ffa7b74a9b23`.

## Focused validation and identities

- native/Candle transitive-open oracle: PASS;
- all-six set substitutions plus exact inverse theorem oracle: PASS;
- normalization tests: PASS, 18/18;
- manifest tests: PASS, 28/28;
- manifest write and independent fixed-point check: PASS, 297 roots,
  400 source nodes, 43 generated inputs;
- JSON parsing, shell syntax, and `git diff --check`: PASS.

The implementation commit is
`7fc48f0b1b78b40d37e8d12b25a18f3cddd359dd`. Derived identities are:

- normalization contract SHA-256:
  `73c6a502b62686a0237c2b01dc1fec03297db4d7779c81b2f34cba17cf07e6fd`;
- manifest SHA-256:
  `23a6d434f4451494b234cbdc1b68ecca9c4c9333fb8fa33afaf56ac304b75824`;
- loader SHA-256:
  `ec11f3fd1f20454b25925e71f89920c26d25923876da45c3f6a91adeabf499f7`;
- generated source-digest/full-build MD5:
  `a0dcac45e77624ce58ccd86630491fb1` /
  `02cf9e0fbcb4ac78d84cb4cc7c1ea52e`.

## Next exact work

Only a fresh cumulative replay from action zero may credit v42. It must load
the full eight-operation Marchal stream, emit the action-091 success marker,
and continue through actions 092--101. If the already localized action-102
YSSKQOY open-resolution failure then reproduces, its one-line qualified
binding can be promoted as the next coherent batch; it receives no credit
before that exact-state result.
