# Direct Flyspeck boundary 04: AJRIPQN open resolution

Date: 2026-09-12 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct progress

The latest completed exact cumulative replay reached action 079 and passed all
79 actions 000--078. The independent v34 replay confirmed the same frontier;
its immutable failure receipt has SHA-256
`75eaf13f1aea18e831fd522b26d8fbcb6ccf3f8669cdc200106f0a20c44f29f5`.
The v35 exact replay is running from action zero and has not yet awarded a new
completed-run result. Thus the exact headline remains **80 reached / 79
passed**. Cumulative boundary 04, full direct S2, and nonlinear/LP S3 remain
open.

The complete v34 dirty diagnostic identified action 089,
`packing/AJRIPQN.hl`, as the next independent-looking candidate after the
action-079 WRGCVDR blocker. That diagnostic is discovery evidence only; its
result receipt has SHA-256
`0e16cb29c73e9720204dd290fc86c53d63b2043213a4060ef8b0079349051c3e`.

## Historical inspection and root cause

Neither `origin/fix-top100` nor `upstream/fix-top100` contains the Flyspeck
AJRIPQN source or a normalization manifest. The pinned Flyspeck commit,
current Candle-replay checkout, `master`, and `origin/master` all select the
same AJRIPQN Git blob,
`973ffa5e0a1909a6e313fb562f4567c0f5e814d1`. Historical branches therefore
provided no patch to adopt.

AJRIPQN opens `Pack1`, then several later modules, ending with `Ddzuphj`.
Native OCaml `open` imports a module's members into the current lexical scope
but does not re-export members that the opened module merely imported. All
three unqualified AJRIPQN uses of `KIUMVTC` therefore select
`Pack1.KIUMVTC` natively.

Candle currently includes an opened environment in the enclosing module's
exported environment. The v34 transcript demonstrates the resulting chain:
`Packing3.KIUMVTC`, `Rogers.KIUMVTC`, and ultimately
`Ddzuphj.KIUMVTC` are all exported with the weaker no-radius statement

```text
!p r V. packing V ==> FINITE (V INTER ball (p,r))
```

while `Pack1.KIUMVTC` has the intended additional `&0 <= r` hypothesis. At
AJRIPQN line 137 the wrong weaker theorem closes the goal before the source's
nonnegative-radius proof steps. Subsequent tactics are consequently shifted,
and the observed `linear_ineqs: no contradiction` is raised on the following
existential goal. This is a module-name-resolution compatibility defect, not a
failed Flyspeck arithmetic argument.

## Narrow normalization

The exact hash-bound normalization qualifies the complete mechanically
enumerated AJRIPQN use set at lines 137, 333, and 626:

```text
KIUMVTC  ->  Pack1.KIUMVTC
```

The original source is 36,567 bytes, MD5
`70225b9f9242276e9b068e7ecb21b298`, and SHA-256
`692cab21cb7ce13343b4fcdfc8223dbfdc38aa556a958a903274aad93adfc56c`.
The normalized source is 36,585 bytes, MD5
`803d1bae0841fb4d55d6b14a04934576`, and SHA-256
`dfd7636c347a07c7fc365dcc9f20cc7e4bd72fdadcc303de27f3595aee071281`.

This does not authorize a basename alias or alter loader path identity. It
selects at each use the exact theorem selected by native OCaml. The theorem
statements, hypotheses, tactic arguments and order, proof intent, definitions,
and axioms remain unchanged.

## Focused and source-only validation

- native OCaml module-resolution oracle: PASS;
- focused Candle unqualified rejection and qualified acceptance: PASS;
- normalization unit tests: PASS, 18/18;
- manifest unit tests: PASS, 28/28;
- exact normalization contract: PASS, 56 entries;
- parser descriptor validation: PASS, 20/20 pilot and 400/400 inventory;
- independent all-source preparation: PASS, 344 original plus 56 normalized;
- exact loader inventory: PASS, 725 sites and unchanged kind counts;
- JSON parsing and `git diff --check`: PASS.

Committed Candle head is
`1cfaf234fe179a067841f7dcadca629c7138c717`. The corresponding authority
identities are:

- normalization contract SHA-256:
  `2a6c0ff47868fe8384dba4336f9ae39cd62caff0e61c14da686aacce257586f9`;
- manifest SHA-256:
  `908c630f8ceb730f8de40aefcd94d08f530220e2543f358211a44084f53f81be`;
- generated source-digest/full-build MD5:
  `b4978be98c1c692922ea35d32ac3eb5c` /
  `e83d983c6bda45068339eeae2f5380c9`;
- overlay receipt SHA-256:
  `d34001ef25fa43144739e7a87af2bd694340108171ec6fde6af27db6dc601e80`;
- cumulative plan SHA-256:
  `31b9c05580507b94231f0de7aeef09e5a23743dd8e043363df850fe830ee2daa`.

## Exact cumulative check

The fresh v36 action-zero replay of all 152 boundary-04 actions is running at
`/project/flyspeck-candle-runs/v36-dev-direct-boundary04-1cfaf23-attempt-001`.
Its preparation receipt has SHA-256
`1ec5725f7a0efeeee79b6f641de2f929f52ba0de508e8309ec481c670111df1f`.
No pass credit is assigned before the exact nonce-bound result is validated.
