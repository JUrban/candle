# Direct Flyspeck boundary 04: WRGCVDR discarded theorem effect

Date: 2026-09-12 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct progress

The latest completed exact cumulative run reached action 079 and passed all 79
actions 000--078. Its immutable DEVELOPMENT / NON-RELEASE failure receipt has
SHA-256
`e0b1507d883e6c088143d6d8d31220bfe407ccd65ee668d5fae40336ad0e52e1`.
The v34 exact replay is currently running from action zero and awards no new
credit until it terminates. Cumulative boundary 04, full direct S2, and
nonlinear/LP S3 remain open.

The complete v34 dirty diagnostic attempted all 152 actions and reached its
single completion marker. It recorded 52 actions with failure diagnostics:
four independent-looking root candidates at actions 079, 089, 102, and 126,
plus 48 dependency, cache, undefined-name, and parser-recovery diagnostics
that require a clean cumulative replay before they can be promoted to roots.
This collector is discovery evidence only. Its result receipt has SHA-256
`0e16cb29c73e9720204dd290fc86c53d63b2043213a4060ef8b0079349051c3e`.

## Historical inspection and failure localization

Neither `origin/fix-top100` nor `upstream/fix-top100` contains the Flyspeck
source or a normalization manifest. The relevant Flyspeck `master`,
`develop`, and Candle-replay refs all identify the same WRGCVDR blob,
`909a6a8675da5a79b77b8a553b4fd6fdf3bebe28`; the construct has been unchanged
since the original 2010 source commit. The prior v30 patch was therefore used
only as a lead for the module-structure class.

The v30 normalization lets action 079 pass the two parser registrations at
lines 75--76. Candle then reports a `thm` versus theorem-producing function
type mismatch while underlining the following `X_IN_HYP_ORBITS` binding. The
actual unbound structure item is the deliberately discarded theorem proof at
WRGCVDR line 238:

```text
prove(` UNIONS E SUBSET V /\ {a, b} IN E ==> a IN V /\ b IN V `,
...
MESON_TAC[]);;
```

A module-scoped fixture independently reproduces the same Candle rejection
with a theorem-valued `prove(...)` structure effect. Giving the unchanged
expression an explicit wildcard binding makes the module load and preserves
the bindings on either side:

```text
let _ = prove(` UNIONS E SUBSET V /\ {a, b} IN E ==> a IN V /\ b IN V `,
...
MESON_TAC[]);;
```

The proof is still evaluated exactly once in its original position, with the
same theorem statement, tactic, effects, returned theorem, and exceptions; the
same returned theorem remains deliberately discarded. A native trace oracle
independently confirms that explicit wildcard binding preserves the order and
effect of a value-returning structure expression. No retained theorem,
hypothesis, proof step, proof intent, definition, or axiom is changed.

The exact source identity remains SHA-256
`9d1378418c444f1ec9ce63567cb085fd9def0142ef3a4fb203689e34b9bc636d`.
The three-operation normalized output is 95,420 bytes, MD5
`9dd09663b6f25b2fca262908c6d4002a`, and SHA-256
`d63e3cd9230fd5aadf98930f790a2c3baeea56f73ffa5d20c01e9c76a52fce69`.

## Focused validation

- historical branch/blob comparison: PASS;
- native unit- and value-effect/order oracle: PASS;
- focused Candle original rejection and normalized acceptance: PASS;
- normalization unit tests: PASS, 18/18;
- exact normalization contract over all 55 unique paths: PASS;
- manifest regeneration: PASS, 297 roots, 400 source nodes, 43 generated
  inputs;
- JSON parsing and `git diff --check`: PASS.

The v35 derived authority identities before the next compatibility commit are:

- normalization contract SHA-256:
  `c6f0a91a9ae9dff0d1e7343b85ac361d6db136a1e8b870a7734c40806b86383e`;
- manifest SHA-256:
  `1b2a8767154038e948d205f5e281820f44dd7b1d702e4811f1428ec8af953729`;
- generated source-digest/full-build MD5:
  `cee9911948e5a43316f5977b53089cb4` /
  `354e56467eae5a412718083e901e9075`.

## Next cumulative check

This repair requires a fresh action-zero boundary-04 replay. The dirty
collector's later action-089, action-102, and action-126 candidates remain
leads only until each is reached with all predecessors green. The already
identified action-126 unary term-list `setify` site can be validated and
included in the next coherent boundary batch without treating dirty fallout
as exact evidence.
