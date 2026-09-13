# Direct boundary 04: Marchal3 context-free set swaps

Status: DEVELOPMENT / NON-RELEASE compatibility batch. This document does not
claim S1, S2, S3, qualification, promotion, or release evidence.

## Clean-predecessor localization

The authenticated pre-Marchal DMTCP image contains the exact v44 actions
000--090 state, 91 ordered predecessor markers, no pending source identity, and
no evaluated Marchal source. Its receipt is
`/project/flyspeck-candle-runs/v44-pre-marchal-checkpoint-63c227f-dev-001/snapshot-receipt.json`;
the immutable 813,882,045-byte image has SHA-256
`f49de79bc47ea0a889f04625cfb9a878c94a96a8737d92a93a86bc4c260ed29b`.
Each focused attempt starts from a newly hash-verified reflink copy. A failed or
partially loaded copy is never resumed.

The first exact v44 action-091 attempt from a fresh image passed the prior
four-selected-member site and later entered another monotonically growing
search. Its log is
`/project/flyspeck-candle-runs/v44-marchal3-action091-clean-restore-63c227f-attempt-001/candle.log`,
with SHA-256
`f411a22ee2acc4a412a561dcec290738f020008a348085f4ac0a52202830ae519`.
A second fresh image loaded the mechanically traced v44 Marchal source. The
trace passed `DIHX_SYM` steps 122 and 192 and isolated the next runaway at
step 286, upstream line 5325. The immutable trace root is
`/project/flyspeck-candle-runs/v44-marchal3-post-four-localization-clean-restore-dev-001`;
its log SHA-256 is
`ac708e43b26a9963e2a3ed84c252f69dd725dd4bd49a1a17ac8225706ec7dd6d`.
The search retained one fingerprint and grew through 9,643,978 nodes before
the verified restored Cake process was interrupted. Any queued text after the
caught interrupt is not accepted as a pass.

## Minimal paired normalization

At line 5325, the preceding refinement step has already reduced the obligation
to the literal identity `{u,v,a} = {v,u,a}`. Broad `SET_TAC[]` unnecessarily
imports the large `DIHX_SYM` ambient assumption set. The paired site at line
5426 has the identical root cause for `{u,v,a,b} = {v,u,a,b}`. Both exact lines
now use `REWRITE_TAC[SET_RULE ...]`, proving only their context-free set
permutation.

The two-line change preserves all theorem statements, hypotheses, refinement
order, goals, and proof intent. It introduces no axiom, alias, search-limit
change, or runtime exception. The normalization remains pinned to upstream
Marchal SHA-256
`191528d2c1dc3542751507d2b44880f3b4f07efe00ea9267b66bc10e28d21926`.
Its v45 output is 255,426 bytes with SHA-256
`fcba24dc44bd3ca3aa581bd30ca3c1aa56cf38c621a8a2df50673d70c5732814`
and MD5 `be8cba1fe893b5bcff75e3a6a4424219`.

## Acceptance sequence and result

The committed deterministic fixture proved both exact identities in the real
development Cake runtime. The complete candidate action 091 then passed from a
new authenticated pre-Marchal image copy. The focused 637,796-byte log has
SHA-256
`b4715fdf16a4e565ba67a75eab1a624ad1ea0a2f277d3a0ba03bbb6ee5cc1bef`
and contains exactly one expected action marker, the 92-event clean post-state
marker, and no exception or error token. The failed copy was not resumed.

A fresh exact cumulative replay from action zero independently confirmed that
result on committed v45 head
`45acc8a86e194276d0cc8873d04225b601095a8b`. It completed exactly the ordered
actions 000--091, including Marchal, then reached the next real source action,
092 `packing/GRUTOTI.hl`. GRUTOTI entered a distinct monotonically growing
proof search and did not complete. The cumulative log has SHA-256
`af4c165eea3f5da71390f0422f00c949c7273713b452bc75b726d27d577a10fe`.

The resulting direct DEVELOPMENT frontier is therefore 93 actual actions
reached / 92 passed. Marchal is green; GRUTOTI is the first remaining genuine
compatibility blocker in boundary `04-geometry-through-151`.
