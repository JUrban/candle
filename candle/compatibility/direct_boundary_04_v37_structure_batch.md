# Direct Flyspeck boundary 04: v37 structure-effect batch

Date: 2026-09-12 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct action progress

The latest completed exact cumulative run remains 80 actions reached and 79
passed: actions 000--078 are exact-green, and action 079 failed in
`local/WRGCVDR.hl`. Its immutable failure receipt has SHA-256
`84b9cfda311f4811e0339a1a0a3e801097b31010ae09f0abdac040845a580718`.

A retained real state with the same exact actions 000--078 then exercised the
v37 candidates as focused DEVELOPMENT / NON-RELEASE evidence. It reached 92
logical actions with 91 passing candidates: repaired actions 079--090 passed,
and action 091 failed. This focused path does not award exact-ledger credit.
The observed sequence was:

- 079 `local/WRGCVDR.hl`: full normalized source passed;
- 080 `local/LVDUCXU.hl` and 081 `local/LDURDPN.hl`: passed;
- 082 `local/local_lemmas.hl`: original source rejected its first anonymous
  parser registration; the two-site normalized full source passed;
- 083--088: all six sources passed;
- 089 `packing/AJRIPQN.hl`: the production three-site `Pack1.KIUMVTC`
  normalization passed the full source;
- 090 `packing/QZYZMJC.hl`: passed;
- 091 `packing/marchal3.hl`: failed in theorem
  `LEFT_ACTION_LIST_3_EXISTS`, refinement step 23 (zero-based), with
  `Failure "solve_goal: Too deep"` on goal
  `{u0,u1,u2,u3} = {x,z,t}`.

Two earlier attempts to resume after the experimental WRG `#use` failed only
because the focused harness had not committed the manually loaded overlay as
the authenticated logical WRG dependency. Before continuing, the harness
asserted both the exact original identity and normalized MD5 and then recorded
that one logical node. Those path-accounting failures are retained in the log
but are not classified as Flyspeck source failures.

## Complete structure-effect repair

The v35 WRG normalization fixed the anonymous theorem expression at source
line 238 but exposed two later deliberately discarded theorem-valued module
expressions at lines 2496 and 2500. The complete mechanically enumerated WRG
set is now lines 75, 76, 238, 2496, and 2500. The last two expressions receive
the same explicit wildcard binding as the prior sites. Their theorem
construction, arguments, order, effects, returned theorems, and exceptions are
unchanged; the returned values remain discarded.

The first two module expressions in `local_lemmas.hl`, source lines 19 and 20,
are the same anonymous parser-registration class. A lexical structure scan
found exactly those two anonymous structure phrases; later `REWRITE_RULE` and
`prove` occurrences are within named theorem bindings or tactic arguments.
The normalized forms are:

```text
let _ = parse_as_infix("has_orders",(12,"right"));;
let _ = parse_as_infix("cyclic_on",(13,"right"));;
```

Both calls still execute once in their original order with identical names,
precedences, associativity, effects, unit results, and exceptions. No theorem
statement, hypothesis, proof, definition, proof intent, or axiom changed.

The `local_lemmas.hl` source identity is SHA-256
`935a70e862fd3783a73df0cc6bc5afca94f90fefeccb1c49696b75870a031990`,
MD5 `4aaa29b2a1125f638ca39419cd2cf008`, 224,870 bytes. Its normalized identity is
SHA-256 `b68a839b7e31df60c7a70b5f9f5833aa45a1ec64869e661ee8a80be9f96b7b3b`,
MD5 `5ba3d39c65b535e98f4af9dfbce0f82a`, 224,886 bytes.

Neither `origin/fix-top100` nor `upstream/fix-top100` contains WRGCVDR,
`local_lemmas`, Marchal3, or a patch for these constructs. Relevant historical
Candle branches contain the earlier WRG sites but no `local_lemmas` or
Marchal3 repair. Flyspeck history retains the source constructs. Historical
work was therefore used only as a lead; the exact failures and candidates were
reproduced independently.

## Validation and identities

- full WRG candidate in the retained real state: PASS;
- full `local_lemmas.hl` candidate in that state: PASS;
- focused native/Candle original-reject and normalized-accept structure
  oracle: PASS;
- full production AJRIPQN candidate in that state: PASS;
- normalization and manifest unit tests: PASS, 46/46;
- normalization contract check: PASS, 57 entries;
- manifest fixed point: PASS, 297 roots, 400 source nodes, 43 generated
  inputs;
- JSON parsing and `git diff --check`: PASS.

The frozen implementation commit is
`1f549b04e140c9f0bfc2c52644f9ad109f64714b`. Derived identities are:

- normalization contract SHA-256:
  `f9e1c4048843f62b09fd5547d6389787c70a9923532bbc1ee6f552d778adbc00`;
- manifest SHA-256:
  `bfeba70a51a8625d34df25cea8c8bda8cdb2464b532c61c049f95d2042fe3483`;
- loader SHA-256:
  `2e8185a2aaf727c40cb5bbea702fc561f48fb6e030cc5e5698a490b35351fa7d`;
- generated source-digest/full-build MD5:
  `bcab954c3281f1d55e097147fce6da96` /
  `38573ca51c9aa534f8f93f79456caeb5`;
- experimental overlay receipt SHA-256:
  `7d85ff3ae5890b576cd9d12c713f26a2cb77cbabae7013d6a9bfcb1ba5157867`.

## Next work

A fresh exact cumulative boundary-04 replay from action zero must validate the
frozen v37 bytes. In parallel on a successor branch, the preserved Marchal3
failure will be replaced, if full-source validation succeeds, by a bounded
deterministic substitution/rewrite proof of the same set equality. Full direct
S2 and nonlinear/LP S3 remain open.
