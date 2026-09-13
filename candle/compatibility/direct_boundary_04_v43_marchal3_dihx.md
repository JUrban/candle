# Direct Flyspeck boundary 04: v43 Marchal3 localization and repair

Date: 2026-09-13 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, publication, or release claim. No qualified
Great100 runtime, source, report, transcript, or semantic-evidence byte was
changed.

## Actual direct action progress

The exact cumulative frontier remains **92 actions reached / 91 passed** at
boundary 04 (`00-base-through-151`): actions 000--090 are exact-green and
action 091 is `packing/marchal3.hl`. The first 30-action boundary remains
30/30 exact-green. Full direct S2 and nonlinear/LP S3 remain open.

No additional action receives pass credit from the probes in this report. A
fresh exact replay from action zero is required against implementation commit
`b9a198e82dcd9a32e8767f01a0b70ec58a6f02fe`.

## Exact localization

The v41 and v42 cumulative replays both ended with the same large MESON node
sequence, which made two different source sites look identical. The v43
diagnostic replayed the unchanged authenticated actions 000--090 and then
loaded a mechanically instrumented copy of the v42 normalized Marchal source.
It inserted theorem-entry and refinement-step reports across all 50
`prove_by_refinement` proofs and 4,856 tactic-list elements, without changing
the statements or tactics.

The diagnostic emitted 91 ordered predecessor action-ok markers and entered
37 Marchal refinement theorems. In particular,
`LEFT_ACTION_LIST_3_EXISTS` completed all 233 refinement steps, including the
direct four-index inverse rewrite, and execution continued through later
theorems. The first repeated runaway was then localized exactly to
`DIHX_SYM`, zero-based refinement step 109:

```ocaml
(AP_TERM_TAC THEN SET_TAC[])
```

at upstream line 5085. Its search reproduced the characteristic sequence
through 4,544,914 nodes. The run was boundedly interrupted after 1:32:28;
maximum RSS was 4,478,208 KiB. Candle caught the interrupt and evaluated the
next queued report phrase, so the trailing
`CANDLE_MARCHAL3_DIAGNOSTIC_SOURCE_PASS` text is explicitly not a pass. The
full log and timing SHA-256 values are respectively
`8eb805ff98288e7de633c8dd9f50a3b51db14b39484966db95991e38825b125e`
and `69b41466fd9769fb088a30fbf16998765cbbf8ee373dc906db59525838572135`.
The instrumented source SHA-256 is
`67469df8d9373316ae3c744511d424a6b4f601195e790645b565b9e6c512d6e5`;
its generator SHA-256 is
`ebd4f671d2641a01449855997da3f75c9271027a0cc9d877601c37124aff1b97`.

This tracing also corrects the v42 interpretation. The direct inverse rewrite
did clear the earlier blocker; the visually identical search in v42 came
from the later DIHX tactic. A separate bounded focused probe reconstructed
Flyspeck's `UP_ASM_TAC` and evaluated the original four-index inverse proof
under its exact logical assumptions. It independently failed with
`solve_goal: Too deep` at 679,114 nodes. Its log SHA-256 is
`89ececd2c37177e33fd0d0cff71a19aa25c2005c22b8329b09f0104a11c8ad6d`.
As with the interrupt probe, its next queued sentinel is not a proof pass.

The upstream source contains the identical DIHX cardinality tactic again at
line 5308. Neither `fix-top100` nor relevant historical Candle branches
contain a Marchal repair. All inspected Flyspeck branches retain both original
sites. Historical content was used only as a lead; every adopted correction
was independently reproduced and checked.

## Proof-preserving compatibility batch

After `AP_TERM_TAC`, the DIHX goal is the context-free equality

```text
{w0,w1,w2,w3} = {w3,w0,w1,w2}
```

but the broad legacy `SET_TAC` also consumes DIHX's large ambient assumption
set. At both mechanically identical sites, v43 instead constructs that exact
set theorem independently and rewrites the unchanged cardinality equality:

```ocaml
REWRITE_TAC[
  SET_RULE `{w0,w1,w2,w3:real^3} = {w3,w0,w1,w2}`
]
```

A focused Candle probe proved the exact permutation and cardinality equality
with both the standard and reconstructed legacy SET implementations. It
exited 0 after 2:14.93 with maximum RSS 4,235,392 KiB. Its stdin/log/time
SHA-256 values are `bf5b2e4771abc1f82a0209c14f685556d0f5b12c78f32f01addd9a3fa6dcc735`,
`a03cf775d374daafe01e7b1e1451dab78bd97626dbedf9cb7a7efb50d71ee553`,
and `3368c45b2d200880421d65a82b7d7c6d9b152928a82d083195a34f4d412038e4`.

The coherent v43 normalization therefore contains:

- the qualified Strictbuild binding after the final open declaration;
- all six deterministic `LEFT_ACTION_LIST_3_EXISTS` set substitutions;
- the direct four-index `PERMUTES_INVERSE_EQ` rewrite;
- both context-free DIHX cardinality-permutation rewrites.

These are nine contract operations covering ten exact source replacements.
The earlier three-index inverse proof at lines 3824--3825 remains unchanged.
No theorem statement, hypothesis, definition, axiom, case order, proof intent,
or global search limit changes.

## Frozen implementation and focused validation

Implementation commit:
`b9a198e82dcd9a32e8767f01a0b70ec58a6f02fe`.

The source input remains 254,482 bytes with SHA-256
`191528d2c1dc3542751507d2b44880f3b4f07efe00ea9267b66bc10e28d21926`.
The materialized v43 Marchal stream is 254,903 bytes with MD5
`eabad795902f49dd173171a0611bc459` and SHA-256
`be0425bdda6c5c922448756fd146401fb52df1167ef9dedde93fd6f0de29088e`.
Its receipt SHA-256 is
`60d22c2d3e267526015a100ef10c7bf233adedffd4859b26f045d9cd83b7605b`.

Focused gates:

- standard and legacy exact set-permutation/cardinality oracle: PASS;
- direct inverse rewrite theorem plus six prior substitutions: PASS;
- original inverse proof reproducer: expected `solve_goal: Too deep`;
- normalization unit suite: PASS, 18/18;
- manifest unit suite: PASS, 28/28;
- manifest write/check fixed point: PASS, 297 roots, 400 source nodes, 43
  generated inputs;
- exact 58-entry overlay materialization: PASS;
- JSON parse, shell syntax, and `git diff --check`: PASS.

Derived SHA-256 identities:

- normalization contract:
  `418a319189bdf16ccbe487e860539f3de18cf0f31f577858f7ebdca691fabe5b`;
- manifest:
  `4e7fc654efcc23536ab1aff10b89e3f116278c3531503c60a834f20c8ea04d8d`;
- loader:
  `053210dc23a693e6862e910a9c9bcb017d2af2c95b73a1b7dd300e7b87af6fa9`;
- generated source-digest/full-build MD5:
  `274776131cb95585e784752211a63611` /
  `9a54c31711c02e3e59f08718c3249050`.

## Next execution

Prepare a fresh boundary-04 DEVELOPMENT / NON-RELEASE run from this exact
implementation commit and materialized normalization identity, then replay
from action zero. Action 091 receives pass credit only if normalized Marchal
completes and emits its nonce-bound action marker. If it does, continue the
same cumulative process to collect the complete next failure set through the
available boundary rather than stopping after the first unrelated later
failure.
