# Direct Flyspeck boundary 04: v38 Marchal3 set substitution

Date: 2026-09-12 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct action progress

The latest completed exact cumulative run remains 80 actions reached and 79
passed: actions 000--078 are exact-green, and action 079 failed in
`local/WRGCVDR.hl`. Its immutable failure receipt has SHA-256
`84b9cfda311f4811e0339a1a0a3e801097b31010ae09f0abdac040845a580718`.

The retained focused DEVELOPMENT / NON-RELEASE state has reached 92 logical
actions with 91 passing candidates. Repaired actions 079--090 passed, and
original action 091 failed in `packing/marchal3.hl`. This focused path does not
award exact-ledger credit. A fresh exact v37 replay is independently running
from action zero while this successor batch is developed.

## Preserved failure and localization

The original `marchal3.hl` failure is in theorem
`LEFT_ACTION_LIST_3_EXISTS`, zero-based refinement step 23, at upstream source
lines 3872--3873. Candle reports `Failure "solve_goal: Too deep"` while the
goal is:

```text
{u0,u1,u2,u3} = {x,z,t}
```

The theorem has already retained `{x,y,z,t} = {u0,u1,u2,u3}` and proved
`x = y` in that case. A complete lexical inspection found the same expensive
`UNDISCH_TAC ... THEN UP_ASM_TAC THEN SET_TAC[]` derivation in all six equality
cases at lines 3869, 3878, 3887, 3896, 3905, and 3914. The step-indexed
diagnostic, original source failure, failed weaker rewrite candidate, and
successful deterministic candidates remain in the retained development log;
they are not release evidence.

Neither `origin/fix-top100` nor `upstream/fix-top100` contains Marchal3 or a
patch for this proof. Relevant historical Candle branches likewise contain no
Marchal3 normalization. Flyspeck history retains the original construct.
Historical work was therefore only a search lead; the failure and repair were
reproduced and checked independently.

## Narrow proof-preserving repair

Each of the six `SET_TAC` searches is replaced by the same bounded proof of
the identical intermediate set equality:

```text
ONCE_REWRITE_TAC[GSYM (ASSUME retained_set_equality)] THEN
SUBST1_TAC (ASSUME proved_point_equality) THEN
REWRITE_TAC[INSERT_AC]
```

The rewrite first substitutes the retained four-point set identity, the
second step substitutes the point equality already proved by the surrounding
case, and `INSERT_AC` removes the resulting duplicate insertion. The six-case
order, preceding equality subproofs, following cardinality contradictions,
and final theorem are unchanged. No theorem statement, hypothesis,
definition, allowed axiom, or proof intent changed, and no global proof-search
limit was raised.

The original source identity is SHA-256
`191528d2c1dc3542751507d2b44880f3b4f07efe00ea9267b66bc10e28d21926`,
MD5 `ad1052eeb7d9979e8fd3069d2eb4a35c`, 254,482 bytes. The normalized identity
is SHA-256
`16a6add24b6bf5d31f18af745c5c95dbc2d32b04eb96f41ab77372c2e25ad26d`,
MD5 `3ce51a98ce251632482e277b15662f63`, 254,788 bytes. A direct diff contains
exactly those six replacements.

## Validation and identities

- step-indexed localization of the original real-state failure: PASS;
- all six polymorphic deterministic subgoals in retained Candle state: PASS;
- standalone Candle six-theorem fixture: PASS;
- normalization and manifest unit tests: PASS, 46/46;
- normalization contract check: PASS, 58 entries;
- manifest fixed point: PASS, 297 roots, 400 source nodes, 43 generated
  inputs;
- JSON parsing, shell syntax, and `git diff --check`: PASS.

A dirty full-file reload is preserved but is not treated as authoritative: it
is recomputing `marchal3.hl` after the original action already partially loaded
that file and is dominated by a MESON search in that duplicate-state execution
exceeding 181 million nodes. It has not emitted another exception or a
full-file completion marker. The required authoritative full-source result
will instead come from the fresh exact cumulative v38 replay.

The frozen implementation commit is
`354ad69c240e62b9749daa9bdfd607f2e3410c68`. Derived identities are:

- normalization contract SHA-256:
  `d4e281f741b0d3bcbfc98fa3d4a74dce6f3c8396ab14c9b0bb9e691a127504b4`;
- manifest SHA-256:
  `8f15c791725b5273436bc338268ea047de91e7f3363b602e03d3765d18c6d360`;
- loader SHA-256:
  `7a5f32bd856761587f3ef33fb48feb59b054cdada41c6e5033d13e120d76dcf8`;
- generated source-digest/full-build MD5:
  `925d4f1ebe26de1f4685037990998bbc` /
  `858a53a5e6918cdd84b22b4e54e1a0f3`;
- fresh normalization receipt SHA-256:
  `a879be69ec4a85e717f9135ec6e1c600dfff94113165d19857b6e5af12fdf75c`.

## Next work

Generate a cumulative boundary-04 plan from the final report head and launch a
fresh exact DEVELOPMENT / NON-RELEASE replay from action zero. It must pass
the full normalized action 091 before action 91 receives exact or focused
full-source credit. If it does, continue actions 092--101 and validate the
already localized action-102 `YSSKQOY.hl` name-resolution candidate. Full
direct S2 and nonlinear/LP S3 remain open.
