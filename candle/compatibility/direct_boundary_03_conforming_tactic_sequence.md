# Direct Flyspeck boundary 03: Conforming tactic sequence

Date: 2026-09-11 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct progress

The fresh v27 cumulative replay through action 049 completed with 50/50
nonce-bound action-success markers, one preflight marker, a returned cumulative
prefix, zero diagnostics, and exit status zero. It closes development boundary
`02-nonlinear_support-through-049`. Its immutable development result receipt
has SHA-256
`fe544680a939aae8ee502f4b917fc2a12a2c31ff2a25e68947675b7fa9d262f4`.

The separate fresh v27 replay through action 060 reached 60 actions and passed
59. Actions 000--058 are exact-green. Action 059,
`text_formalization/fan/Conforming.hl`, failed before its success marker with
the tactic-composition type mismatch reported at prepared line 1225. Action
060 was not reached. Its immutable development result receipt has SHA-256
`eabe2ae9960291248c1e61c459e956f85587469ce0b337f05972463a66c49f1a`.

Boundary 03 remains open. Full direct S2 and nonlinear/LP S3 remain open.

## Historical lead and bounded normalization

The `fix-top100` branch contains no matching Conforming normalization. The
relevant historical Candle worktrees were inspected before implementing a
fix. An uncommitted v25 development candidate identified the redundant
separator in the original source at line 1424 as a lead; it was not treated as
authority or transplanted wholesale.

The v28 contract independently binds the exact original Conforming source and
performs one `exact_bytes_replace_once` operation:

```text
REWRITE_TAC[conforming_fan]; THEN ASSUME_TAC
REWRITE_TAC[conforming_fan] THEN ASSUME_TAC
```

The selected native `pa_j` preprocessor emits byte-identical OCaml for the two
forms. The original minimal phrase reproduces Candle's tactic-composition type
mismatch, while the normalized phrase loads and exports the same tactic
function. The change therefore removes only a redundant source-level
separator. The theorem statement, hypotheses, theorem argument, tactic
sequence, proof intent, and allowed axioms are unchanged.

The normalized Conforming output has SHA-256
`a5cd590474eaa2adcc95ef5a885a6331400387da689f1f4ee37a8c9ed37883b5`.

## Focused validation

- native preprocessor identity: PASS, byte-for-byte;
- focused Candle original rejection and normalized acceptance: PASS;
- normalization unit tests: PASS, 18/18;
- manifest unit tests: PASS, 28/28;
- all-inventory source preparation: PASS, 17/17 over 400/400 sources;
- parser descriptor identities: PASS, pilot 20/20 and all-inventory 400/400;
- normalization overlay materialization: PASS, 50 entries;
- manifest fixed point: PASS, 297 roots, 400 source nodes, 43 generated
  inputs;
- JSON parsing and `git diff --check`: PASS.

The v28 derived authority identities are:

- normalization contract SHA-256:
  `6e3f60d72df4e0ba32e9468936caad1af92da66534d1964e4f0853f337f5767b`;
- manifest SHA-256:
  `3a10b2e5c18aff92155ef06bfa029dafc27a3e77ad9c7e9bbe87d3d79b2824d7`;
- pilot descriptor SHA-256:
  `0aa5db246a2b19061cd2b12880f414b87dafc2a7ba94b657b7004288ba39903d`;
- all-inventory descriptor SHA-256:
  `49bb44c768624bc1fdb0ebde0c847b24e46ca33b14e822efd2a02746355cf171`;
- ordered effective/prepared SHA-256:
  `32cf5b113e408bf5df9a66a0574f03f405eeb880a558d9726d2a57a8d1409e9a`
  / `f8789fbf7c6d17783d5f908a3398c36c280a4979b12690dbff24eee94171cba1`;
- generated source-digest/full-build MD5:
  `7c94364f2ca04da62164e96a98dca8b0` /
  `febcc33f2b1b990c0af76f9cc5c4a588`.

Only a fresh cumulative replay from action zero through action 060 on the
committed v28 bytes may validate the normalization, credit action 059 or 060,
and close boundary 03.
