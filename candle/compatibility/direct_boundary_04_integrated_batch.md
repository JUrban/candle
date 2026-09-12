# Direct Flyspeck boundary 04: integrated compatibility batch

Date: 2026-09-12 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct progress

The latest completed exact cumulative run reached 73 actions and passed 72.
Actions 000--071 are exact-green. Action 072,
`text_formalization/packing/SLTSTLO.hl`, is the first genuine Candle/Flyspeck
failure in that run, and action 073 was not reached. The immutable
DEVELOPMENT / NON-RELEASE failure receipt has SHA-256
`6634b9ad5fd08c898f8a2b90e5179d1886747f0c2cd6266e45e36ffbbff5a149`.

An isolated v33 exact replay is now testing the action-072 normalization.
This integrated v34 batch is deliberately queued behind that predecessor and
awards no additional action credit until a fresh nonce-bound cumulative replay
from action zero validates it. Cumulative boundary 04, full direct S2, and
nonlinear/LP S3 remain open.

## Integrated compatibility classes

The branch composes four narrow, independently reproduced compatibility
classes across the five currently known boundary-04 sites:

- action 070, `packing/EMNWUUS.hl`: supply `Term.(<)` to the unary term
  `setify` call (already exact-green in v29);
- action 072, `packing/SLTSTLO.hl`: supply the same canonical term comparator
  to the third active copy of the exact `seans_fn` helper;
- action 079, `local/WRGCVDR.hl`: make two unchanged module-initialization
  `parse_as_infix` effects explicit wildcard bindings;
- action 083, `tame/Inequalities.hl`: make the unchanged `g` goal-setting
  effect an explicit wildcard binding; and
- action 126, `jHOLLight/caml/ssreflect.hl`: propagate the second tactic
  sequence's instantiation through the copied 2013 `seqapply`, matching the
  current HOL Light tactic API.

The action-072 source class was fully enumerated before integration: the only
active `setify (flat vss)` copies are EMNWUUS, OXLZLEZ2, and SLTSTLO; the
fourth textual occurrence is inside a comment. Historical branches provided
no SLTSTLO or ssreflect repair to adopt. Each normalization remains bound to
an exact source identity and exact source location. The changes alter no
theorem statement, hypothesis, proof step, proof intent, geometric definition,
or axiom.

## Integrated validation

- normalization contract evaluation: PASS, 55/55 unique paths;
- normalization unit tests: PASS, 18/18;
- manifest unit tests: PASS, 28/28;
- all-inventory source preparation: PASS, 17/17 over 400/400 sources;
- parser descriptor identities: PASS, pilot 20/20 and all-inventory 400/400;
- packing term-order focused original-reject/normalized-accept probe: PASS;
- WRGCVDR native-effect/original-reject/normalized-accept probe: PASS;
- Inequalities native-effect/original-reject/normalized-accept probe: PASS;
- ssreflect original-reject/current-instantiation normalized proof probe:
  PASS;
- manifest fixed-point check: PASS, 297 roots, 400 source nodes, 43 generated
  inputs;
- JSON parsing and `git diff --check`: PASS.

The integrated derived authority identities are:

- normalization contract SHA-256:
  `484f0b23f671bfee16ad1cc1cfc4b278c7cb932614fd4e06707fbe4803b2627d`;
- manifest SHA-256:
  `4ec7d4563f754e4f81b452122723741fb53b73ce3534fffbcb4e752f117937b1`;
- pilot descriptor SHA-256:
  `498aa4486432fde4c18095ffefacee7d20a8018f3a486c20c1dd9e37fac52d60`;
- all-inventory descriptor SHA-256:
  `8e088269815da18021e11f046f96df2396333c5f76f1280848cfd2da90747391`;
- ordered effective/prepared SHA-256:
  `15f8717db5d61074c27ec28e43886863e201f22200b5ef4bb410b2e8cc58be52`
  / `9b3133d2bcf025b158d77f6643d7d7d27c1f2be1bd160be5458df62e371ff194`;
- effective loader action-site SHA-256:
  `145ec788ee51e68052de03e644eca8ac035d0ecd43ce04bde3deee2436706773`;
- generated source-digest/full-build MD5:
  `ac5899d0c2c8b6c00a4610252e2d595a` /
  `63bec30fc190c4bef6d7e605b9f74dbd`.

## Next exact boundary work

First preserve the v33 result: it must pass action 072 and expose the next
failure without relying on the later integrated normalizations. If it does,
materialize this exact v34 source state and run one fresh cumulative
boundary-04 replay. That replay will determine the first genuine failure after
the integrated action-070/072/079/083/126 batch and provide the next complete
compatibility class to investigate.
