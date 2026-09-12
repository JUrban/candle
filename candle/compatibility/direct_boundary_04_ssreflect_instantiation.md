# Direct Flyspeck boundary 04: ssreflect tactic instantiation

Date: 2026-09-11 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct progress

The latest completed exact cumulative run remains boundary
`03-analysis-through-060` at 61/61 actions. Its immutable DEVELOPMENT /
NON-RELEASE receipt has SHA-256
`d84ad3c08e228b87cd1dcb7d371224410d2cbed54206684c2e6d34ce4427a331`.
A fresh exact boundary-04 predecessor replay is in progress and awards no new
credit until its nonce-bound markers are checked. Full direct S2 and
nonlinear/LP S3 remain open.

The earlier complete dirty boundary-04 diagnostic identified a later
compatibility failure at action 126, `jHOLLight/caml/ssreflect.hl`. It is
discovery evidence only and awards no exact cumulative action credit.

## Historical inspection and diagnosis

The relevant lines 57--70 have identical SHA-256
`9595f0b12100c9dd2f4b589e8d90c8ec3941f04d51b41811d1c7b4f9266dea77`
in `origin/fix-top100`, `upstream/fix-top100`, and the pinned Flyspeck source.
The relevant historical direct branches contain no repair. Historical code
therefore supplied no patch to adopt.

A focused fixture containing the exact copied `THENL_FIRST` / `THENL_LAST`
implementation reproduces Candle's recorded type mismatch. Adding types only
to the recursive helper fails unchanged, eliminating the cheapest annotation
guess. Comparing the copied 2013 helper with this Candle head's current
`tactics.ml` identifies a linked API change: the second tactic sequence's
instantiation must be propagated into the first sequence's pending goals and
justification before the sequences are combined.

The v32 normalization makes only those linked changes:

```text
compose_justs n just1 just2 i ths
just1 i ths1
gls1 @ gls2

compose_justs n just1 just2 insts2 i ths
just1 (compose_insts insts2 i) ths1
map (inst_goal insts2) gls1 @ gls2
```

The argument flow and expressions are the same as current `tactics.ml`.
`THENL_FIRST` still applies the requested tactic only to the first generated
subgoal; `THENL_LAST` still applies it only to the last. Focused normalized
Candle execution constructs the theorem `T /\ T` with each combinator. No
theorem statement, hypothesis, proof script, proof intent, definition outside
the copied helper, or axiom is changed.

`ssreflect.hl` already had a distinct hash-pinned fail-closed normalization
for unused dynamic Toploop lookup. The new operations are deliberately
composed into that one existing logical artifact entry, rather than creating
a duplicate-path authority.

The exact source/combined-output identities are:

- source SHA-256
  `9fefd64395673d3813762b90f0c99e86942a29fd2b80d0725dab3ba15aba9ed9`,
  MD5 `6f69a400e5f3922f4d572840748b35c7`, 33,828 bytes;
- combined normalized SHA-256
  `eacedecebf58df95389c07d20f022dbb5819b1b790418b2e24d280cde93f4421`,
  MD5 `da2027a209d53cdf0276a178b4f20ed1`, 33,324 bytes.

## Focused validation

- exact old block reproduces the Candle mismatch: PASS;
- annotation-only negative probe still reproduces it: PASS;
- normalized definitions load and both theorem constructions pass: PASS;
- normalized operation text matches current `tactics.ml` propagation: PASS;
- normalization unit tests: PASS, 18/18;
- manifest unit tests: PASS, 28/28;
- all-inventory source preparation: PASS, 17/17 over 400/400 sources;
- parser descriptor identities: PASS, pilot 20/20 and all-inventory 400/400;
- normalization contract check: PASS, 54 unique-path entries;
- JSON parsing and `git diff --check`: PASS.

The v32 derived authority identities are:

- normalization contract SHA-256:
  `52946418d9205f665fec34ffeeabed3f19df9cc390ffd178919b0a5dc92cba2c`;
- manifest SHA-256:
  `3d7907e7e10eddf35bc7c6bbb55f47e0a2acd8725732d8a43320f19c96466bb5`;
- pilot descriptor SHA-256:
  `71a3b2c7baab0dec26492901d1ad58516f914ae127be1e9ffd4ee6a44093f7e0`;
- all-inventory descriptor SHA-256:
  `d86f1dccd7d9ea6717c15b019918f52e1db5433fd9781b7480f827b2fad61e93`;
- ordered effective/prepared SHA-256:
  `0d22c743cf0b326324a1ac9ffe1a43551abd66c97d7fd5afb9a0c7f40f063e50`
  / `324d81877388004c04b7235684363f9b930fbc9e89f93dac855fda0f6e78df3d`;
- effective loader action-site SHA-256 (unchanged):
  `22a085f371da64d61febc91d1ff111f1f392efbb14598640052a86e6d44bfd48`;
- generated source-digest/full-build MD5:
  `789b66cff58e848bc19544a06c4a5584` /
  `e398f93bc7b550f3178e7274929086d0`.

## Next exact boundary work

Only a fresh cumulative replay from action zero may credit v32. The running
v29 replay must first preserve the action-070 result and expose the next
failure; v30 and v31 then test actions 079 and 083 in order. v32 remains
queued behind those exact predecessors and cannot count as S2/S3 evidence.
