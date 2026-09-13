# Direct boundary 04: Marchal3 four-selected-member exhaustion

Status: DEVELOPMENT / NON-RELEASE compatibility batch. This document does not
claim S1, S2, S3, qualification, promotion, or release evidence.

## Exact cumulative localization

The v43 exact boundary attempt reached action 091, `packing/marchal3.hl`, after
91 ordered predecessor successes but was interrupted during a monotonically
growing proof search. A subsequent mechanically traced v43 source replay used
the same unchanged actions 000--090. It confirmed that:

- the repaired `DIHX_SYM` cardinality-reordering step 109 passes;
- the independently reconstructed three-selected-member step 122 passes in the
  actual cumulative state and therefore is not the blocker;
- the first post-v43 runaway is `DIHX_SYM` step 192, the five-pop `SET_TAC[]`
  at upstream lines 5196--5197;
- that search grew through 3,005,878 nodes before the verified Cake process was
  interrupted.

The immutable trace is
`/project/flyspeck-candle-runs/v44-marchal3-post-v43-localization-dev-001`.
Its log SHA-256 is
`a83d69faa047f4668c8d38512d9346ebf3dfca129adb2b1c8b201b1b1579ca7b`;
the traced source SHA-256 is
`93c1a763e7347f28aae54e66367154229034c4eb55f97438c8e834985478426f`.
The trace also mechanically identifies the paired source occurrence at lines
5422--5423. The trailing diagnostic PASS text after the caught interrupt is
explicitly not a source pass.

## Minimal compatibility normalization

At each paired site the existing context has selected distinct `u` and `v`, a
third member `w` outside their pair, and a fourth member `m` outside the first
three, all from the literal set `{w0,w1,w2,w3}`. The new local theorem
`FOUR_SELECTED_MEMBERS_EXHAUST` proves exactly the required set equality by
splitting only these bounded membership cases. Each site now applies that
theorem with `MATCH_MP_TAC` and discharges its already-present assumptions with
`ASM_REWRITE_TAC[]`.

The change preserves the theorem statement, hypotheses, refinement order, and
proof intent. It does not add an axiom, raise a global search limit, alter the
three-member sites at lines 5099 and 5322, or alter the distinct non-emptiness
sites at lines 5182 and 5408.

The normalization remains pinned to upstream Marchal SHA-256
`191528d2c1dc3542751507d2b44880f3b4f07efe00ea9267b66bc10e28d21926`.
Its v44 output is 255,344 bytes with SHA-256
`a2a0b8ca3aca281923fce521596299088bfd8c97e2975a77c0e557645fa49932`
and MD5 `6c588724246e6408e96cb9a96d5bed3e`.

## Focused checks

The exact four-member implication passed independently in
`/project/flyspeck-candle-runs/v44-marchal3-four-selected-cases-focused-001`.
The committed fixture checks both the helper and its `MATCH_MP_TAC`
application against the real development Cake runtime. The normalization unit
test checks the four exact line anchors, bounded helper, output identity, and
operation uniqueness. Full Marchal acceptance still requires action 091 to
pass from a clean action-090 predecessor, followed by a fresh cumulative replay
from action zero.
