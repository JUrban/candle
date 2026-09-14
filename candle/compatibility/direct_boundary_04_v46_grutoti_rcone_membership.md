# Direct boundary 04: GRUTOTI rcone membership

Status: SUPERSEDED DEVELOPMENT / NON-RELEASE experiment. The line-2713 proof
rewrite described below is not part of v47. Complete GRUTOTI replay exposed a
second runaway, and the subsequent scope audit found one common native-module
resolution defect. The replacement v47 normalization preserves the original
line-2713 proof and restores native `SET_TAC`/`SET_RULE` lookup for the whole
module; see `direct_boundary_04_v47_grutoti_native_set_scope.md`.

This document does not
claim S1, S2, S3, qualification, promotion, or release evidence. The exact
cumulative frontier remains 93 actual actions reached / 92 passed until a
fresh action-zero replay completes action 092.

## Clean predecessor and localization

Marchal action 091 first passed from a fresh pre-Marchal checkpoint copy and
was independently confirmed by the committed v45 cumulative action-zero run.
A new development checkpoint was then captured only after the exact action-091
marker, a 92-event state check, an empty pending-loader list, and a clean REPL
wait. Its immutable 811,933,141-byte image has SHA-256
`1a0a9a54d74009f0d5cdb99c4f927f8d4d0e7e0bc73084cbf23209ee31e63a44`;
its receipt records that GRUTOTI had not been loaded or evaluated. Every
focused attempt uses a new hash-verified reflink, and no failed or partially
loaded copy is resumed.

The compact whole-source trace preserved every original GRUTOTI tactic
expression and reported only refinement application. It completed eager
tactic construction, passed steps 0--2122, and reproduced the cumulative
run's exact monotonically growing search at step 2123 through 1,695,156 nodes:

```text
0..0..3..11..30..64..135..288..697..1589..3977..8581..25932..61180..199702..492794..1695156..
```

The 105,008-byte localization log has SHA-256
`2602eb681de437f60922788b762d5f9b1bfc7e99929447bbb02a6cef0374e968`.
The source-return marker after its caught interrupt is rejected. Step 2123
maps uniquely to upstream `text_formalization/packing/GRUTOTI.hl` line 2713:

```ocaml
 (UP_ASM_TAC THEN SET_TAC[RCONE_GT_SUBSET_RCONE_GE]);
```

The local Flyspeck history and relevant Candle/fix-top100 branches contain no
alternative proof patch; historical GRUTOTI differences are only old file and
module names.

## Narrow direct proof

The preceding refinement steps have established
`x IN rcone_gt u0 u1 a'`; this step needs the corresponding `rcone_ge`
membership. The candidate preserves `UP_ASM_TAC` and directly accepts the
membership implication obtained by rewriting the existing subset theorem:

```ocaml
 (UP_ASM_TAC THEN MATCH_ACCEPT_TAC
   (REWRITE_RULE[SUBSET]
     Marchal_cells_2_new.RCONE_GT_SUBSET_RCONE_GE));
```

Explicit qualification names the theorem's defining module and avoids relying
on Candle's non-native re-export of opened bindings. The replacement changes
no theorem statement, hypothesis, intermediate goal, refinement order,
definition, axiom, or proof intent. It does not touch the distinct deterministic
use at GRUTOTI line 7840 or preemptively patch the identical unreached source
construct in `REUHADY.hl`.

A fail-closed focused theorem in the real post-Marchal runtime proves the exact
membership implication with this tactic and emits no search or error. Its
150-byte log has SHA-256
`69d2cc6a13c6bdc065155f484969741fc0c3fc2bf7ab8f239e74cfaf204b3b60`.
The full real-context candidate subsequently emitted step 2124 and continued
beyond the formerly divergent site. That same trace remains responsible for
collecting the complete available later GRUTOTI failure set.

The one-line hash-bound normalization is committed as
`PROJECT-GRUTOTI-S2-DIRECT-RCONE-MEMBERSHIP-001`. From upstream SHA-256
`bd9904546baab73ea85b01fd29237ceb10dd7259ce2aa1018747616ea1d4d875`,
it produces 297,872 bytes with SHA-256
`e502fd38e727863f1c3653881778e3720c4d574a9b43622c60467e148f04961d`
and MD5 `e99e4426ae07737bafa75ab4bf98df25`.

## Remaining acceptance

The current trace must either complete all 6,300 refinement steps or preserve
and classify the next genuine blocker. After the coherent GRUTOTI batch is
complete, acceptance requires normalizer and manifest fixed-point checks, the
exact action 092 from a fresh clean predecessor, and finally a fresh cumulative
action-zero replay. Focused checkpoint evidence alone cannot raise the direct
action metric.
