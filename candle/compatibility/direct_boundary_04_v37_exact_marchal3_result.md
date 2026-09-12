# Direct Flyspeck boundary 04: v37 exact Marchal3 result

Date: 2026-09-12 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Exact action result

The fresh cumulative v37 replay at Candle source commit
`3b91328a1a36dd3e72f652d0be204036ee7635db` emitted exactly one authenticated
preflight marker and exactly 91 unique nonce-bound action-success markers for
indices 000--090, in order. Their identities equal the first 91 actions in the
exact instrumented prefix. Action 091, `packing/marchal3.hl`, was reached and
failed before its success marker; no later action was reached.

The exact DEVELOPMENT / NON-RELEASE headline is therefore:

```text
actions reached: 92
actions passed:  91
passed indices:  000--090
current boundary: 04-geometry-through-151
```

The process exited zero under the development REPL's source-error behavior
after 1:24:28 and used a maximum 4,480,896 KiB RSS. No boundary-success marker
was emitted.

## Validated compatibility batch

This fresh cumulative run validates the complete v37 compatibility batch:

- action 079 `local/WRGCVDR.hl`: PASS;
- action 080 `local/LVDUCXU.hl`: PASS;
- action 081 `local/LDURDPN.hl`: PASS;
- action 082 `local/local_lemmas.hl`: PASS;
- actions 083--088: PASS;
- action 089 `packing/AJRIPQN.hl`: PASS;
- action 090 `packing/QZYZMJC.hl`: PASS.

In particular, the complete five-site WRG theorem/structure-effect
normalization, two-site `local_lemmas` parser-effect normalization, and
three-site AJRIPQN `Pack1.KIUMVTC` resolution are now exact-green in a fresh
process. The prior exact frontier of 80 reached / 79 passed is superseded by
92 reached / 91 passed.

## First genuine failure

The sole exception is `Failure "solve_goal: Too deep"` in original action 091.
Independent step-indexed localization identifies theorem
`LEFT_ACTION_LIST_3_EXISTS`, zero-based refinement step 23, at upstream source
lines 3872--3873, while deriving `{u0,u1,u2,u3} = {x,z,t}`. The v38 successor
branch contains the bounded six-site deterministic substitution candidate and
is being replayed from action zero; this report gives that candidate no exact
credit.

The immutable exact failure receipt is:

```text
/project/flyspeck-candle-runs/v37-dev-direct-boundary04-3b91328-attempt-002/development-failure-receipt.json
SHA-256 1b4b927b8e523aead3f866678632c274cc8b8362db369cd366fcd46628cf6506
```

Receipt validation recomputed every artifact hash, matched the 91 emitted
markers to instrumented actions 000--090 exactly (including their load versus
skip-ledger modes), and confirmed one preflight marker, one exception, and no
final boundary marker. Key preserved artifacts are:

- preparation receipt SHA-256
  `10e566dc380037aa840fdb6fc0d1a4433c8936a16681997c63340a369fcae61d`;
- exact instrumented prefix SHA-256
  `f14fcb20b55b8246e4deb44be5f21557ebbae6a701ea513b964e3ddec71849f9`;
- runtime configuration SHA-256
  `19d064328ee2ac0a274b7995ea9714e5c0b95a346d308533c7cb4d672288efe5`;
- transcript SHA-256
  `e0f50cb6ae2b29826f07d25107b810136cce3dbbd228b9ff1b19975203b3ef4c`;
- usage report SHA-256
  `0c3020b987847c07312934e47467662b9806d7accd53adb2572161d01689e338`.

## Next work

Preserve the v37 result and let the already launched fresh v38 cumulative
replay exercise the normalized full action 091. Only a nonce-bound action-091
success marker advances exact credit. If it passes, continue the same replay
through the complete boundary-04 failure set. Full direct S2 and nonlinear/LP
S3 remain open.
