# Direct Flyspeck boundary 04: v42 inverse localization falsified

Date: 2026-09-13 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 byte was
changed.

## Actual direct progress

The fresh v42 exact replay passed preflight and actions 000--090 with 91
ordered, nonce-bound action-success markers. Action 091 selected the expected
eight-operation `packing/marchal3.hl` overlay but emitted no success marker.
The exact headline therefore remains **92 actions reached / 91 passed** at
boundary 04. The first 30-action boundary remains 30/30 green; full direct S2
and nonlinear/LP S3 remain open.

## Falsification result

The authenticated v42 Marchal stream contains the v41 qualified Strictbuild
binding and six deterministic set substitutions plus the direct line-4127
`PERMUTES_INVERSE_EQ` rewrite. Its SHA-256 is
`a3c523ac09ac587fdc335a89a50b711edb7b83051d5bb0b3ba36ffa7b74a9b23`.
Despite that rewrite, exact execution reproduced the same v38/v39/v41 search
prefix through 9,536,057 nodes. Thus the large search is not eliminated by
the suspected final inverse proof, and the eighth operation is not justified
as a fix for the observed failure.

The run was boundedly interrupted after 1:31:48. Candle emitted one
`EXCEPTION: Interrupt`, returned to the development prompt, and exited 0 under
non-release REPL behavior. Maximum RSS was 4,475,520 KiB. Frozen SHA-256
identities are:

- `candle.log`: `723709d9fc6d0866eba37ff5385eefbf9e61a67d5a2699bb99707b167dadb38f`;
- `time.txt`: `d71b802f3adc772b5299b7b711a0fa0f88aa516222ba339d951c0ac56edf5f32`;
- preparation receipt:
  `85b0f376e7a8254dd72696010a54f3a771debf8b8479328f8c13436e42f7a50c`;
- instrumented prefix:
  `4ed94669dd66ea8383e0ba122e26b62bc98e65802f1a107ff351b90143450c8e`;
- runtime config:
  `95d0120644beb88e09b70aaf384f52c46fefd3e216dee7da314be62fadb59fb6`;
- stdin:
  `f2b7020c481374160db0cae1d50df82f5613c2a4256ccba98031900c292e49d4`.

The adjacent immutable interruption note has SHA-256
`3a6982616e61d5342b50fa59082c5950c9d796afcb59afcc54a23e5a7f85bbcf`.

## Correct next experiment

The inverse operation must be excluded from the next source candidate. A
faithful diagnostic should start from the proven v41 seven-operation stream,
insert a separate theorem-begin marker before every Marchal refinement
binding, and wrap successfully constructed tactic lists with step-begin/fail
markers. A separate top-level marker is required because Cake can evaluate a
tactic-list element before a function-call wrapper is entered. This bounded
probe identifies the real theorem and distinguishes tactic construction from
refinement-step execution before any further proof edit is proposed.
