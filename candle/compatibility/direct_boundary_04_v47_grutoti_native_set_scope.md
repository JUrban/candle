# Direct boundary 04: GRUTOTI native set-tactic scope

Status: DEVELOPMENT / NON-RELEASE accepted compatibility repair. The focused
whole-source candidate, authenticated action replay, and subsequent fresh
cumulative action-zero replay have all passed. This is functional evidence,
not an S1 archival artifact or an S2/S3 release claim.

## Root cause

The first GRUTOTI runaway mapped to upstream line 2713, whose original proof is:

```ocaml
 (UP_ASM_TAC THEN SET_TAC[RCONE_GT_SUBSET_RCONE_GE]);
```

An exact clean-state capture reduced its pre-MESON goal to:

```text
(!z w h x. rcone_gt z w h x ==> rcone_ge z w h x)
 ==> rcone_gt u0 u1 a' x ==> rcone_ge u0 u1 a' x
```

The captured goal has SHA-256
`cc4b9eae95aecd9fb726984f5d0662abd2e05559c7c6fa813e37b279516ddae4`.
The theorem and ordinary MESON settings matched native HOL Light, but a focused
proof under GRUTOTI's exact open scope exhausted bounds 0 through 49. Its log
has SHA-256
`1684eaf45fbc85e2ff9ab0dcfaec95024b23e8c8c22dee48ed5fe6baa245f466`.

Native OCaml `open` affects lexical lookup without re-exporting names that the
opened module imported from another module. GRUTOTI opens
`Euler_main_theorem`, which opens `Trigonometry2`; `Trigonometry2` defines a
custom Flyspeck `SET_TAC` and `SET_RULE`. Candle's current transitive open
behavior makes those custom names visible inside GRUTOTI, whereas native HOL
Light resolves GRUTOTI's unqualified calls to the outer core bindings. The
custom tactic preprocesses the goal before adding supplied theorems, so the
supplied theorem's `SUBSET` remains opaque and its search diverges in the large
context.

## Narrow source-scoped normalization

The normalization captures the outer bindings immediately after entering
`module Grutoti`, before any opens:

```ocaml
let candle_grutoti_native_set_tac = SET_TAC;;
let candle_grutoti_native_set_rule = SET_RULE;;
```

After the complete original open sequence, it restores only those two lexical
names:

```ocaml
let SET_TAC = candle_grutoti_native_set_tac;;
let SET_RULE = candle_grutoti_native_set_rule;;
```

All original theorem statements, hypotheses, definitions, proof expressions,
227 direct `SET_TAC` occurrences, 204 `SET_RULE` occurrences, and their order
remain unchanged. The superseded line-2713 direct proof rewrite is removed.
The hash-pinned entry is
`PROJECT-GRUTOTI-S2-NATIVE-SET-SCOPE-001`. Starting from upstream SHA-256
`bd9904546baab73ea85b01fd29237ceb10dd7259ce2aa1018747616ea1d4d875`,
it produces 298,005 bytes with SHA-256
`65aeef691f1a5015488489e5df1e8b0b18e7d4bff3767bdfb212be5c4aba079b`
and MD5 `89f7d30f49d505a21d27a5eec9904b37`.

## Clean predecessor validation

Every experiment used a fresh hash-verified copy of the immutable clean
post-Marchal checkpoint; failed or partially loaded states were not resumed.
The checkpoint image has SHA-256
`1a0a9a54d74009f0d5cdb99c4f927f8d4d0e7e0bc73084cbf23209ee31e63a44`.

From that predecessor, the complete normalized GRUTOTI source passed in 711
seconds wall time with no exception, error, or too-deep failure. The final
assertions found `Grutoti.GRUTOTI` bound, its conclusion exactly equal to
`Grutoti.GRUTOTI1_concl`, the predecessor still at 92 action events, and an
empty pending-loader list. The immutable whole-source log has SHA-256
`8e84ba6d7c776dfb9bf768d554db48ac16555767c89312902eb2af16a6c4e59a`.

The candidate emitted 2,364 MESON progress records. They match the retained
native PFT GRUTOTI records byte-for-byte and in the same order; both streams
have SHA-256
`72cc25686891885bada232cb66ec8f9ff0c1a88952257807dea0c273c43d9448`.
This is strong output-level evidence against a remaining rule-order or early-
search-choice difference for the repaired source, although it is not an
independent trace of every internal MESON decision. No comparator-ordering or
pointer-equality diagnosis is inferred for this incident: the demonstrated
cause is the transitive-open binding mismatch, and the residual timing
difference is not a functional blocker. The earlier comparator-ordering and
generic "too much ambient context" hypotheses are retired for GRUTOTI.

## Cumulative confirmation

The normalized GRUTOTI source subsequently passed authenticated action 092
from a fresh clean predecessor. It also passed as part of the fresh action-zero
cumulative replay through action 151 documented in
`direct_boundary_04_v48_cumulative_000_151.md`. That run completed all 152
actions without diagnostics, so this source-scoped binding repair is accepted
for the direct functional lane. The obsolete prepared v46 cumulative plan was
not used.
