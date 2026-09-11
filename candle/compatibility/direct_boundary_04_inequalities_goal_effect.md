# Direct Flyspeck boundary 04: Inequalities goal structure effect

Date: 2026-09-11 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct progress

The latest completed exact cumulative run reached and passed all 61 actions
000--060. Its immutable DEVELOPMENT / NON-RELEASE result receipt has SHA-256
`d84ad3c08e228b87cd1dcb7d371224410d2cbed54206684c2e6d34ce4427a331`.
Boundary `03-analysis-through-060` is exact-green at 61/61. A fresh exact
boundary-04 run is in progress on the preceding v29 batch; it awards no new
action credit until its nonce-bound markers are checked. Full direct S2 and
nonlinear/LP S3 remain open.

The earlier complete dirty boundary-04 diagnostic identified a compatibility
failure at action 083, `text_formalization/tame/Inequalities.hl`. It is
discovery evidence only and awards no exact cumulative action credit.

## Historical inspection and bounded normalization

Neither `origin/fix-top100` nor `upstream/fix-top100` contains an
`Inequalities.hl` patch, and the relevant historical direct-Flyspeck branches
contain no normalization of this construct. Existing module-structure effect
repairs were treated only as leads. The exact source construct was then
reproduced independently inside its enclosing `Tame_inequalities` module.

After constructing `DIH_Y_INEQ_concl`, the source evaluates one bare
goal-setting expression immediately before the `DIH_Y_INEQ` proof binding.
Candle associates that bare module structure expression with the surrounding
item and reports the dirty run's `term` versus `(term -> goalstack) -> ...`
type mismatch. The v31 contract makes the discarded result explicit:

```text
g(DIH_Y_INEQ_concl);;

let _ = g(DIH_Y_INEQ_concl);;
```

The identical term is passed to the identical `g` function exactly once at
the original module-initialization position. The wildcard binding discards
the same goal-stack result while preserving effects and exceptions. A native
OCaml trace oracle confirms identical call count, argument, effect, discarded
result, and following binding. The normalized module-scoped Candle fixture
loads and retains its following value. No theorem statement, hypothesis,
tactic, proof step, proof intent, definition, or axiom is changed.

The exact source/output identities are:

- source SHA-256
  `cb89eb6e98594a2f3b76dd2f6ea5e26b5b1c948da617470fb462afa771ef58b4`,
  MD5 `32e850f39c74cb9d2bdb3ca1073335d5`, 27,047 bytes;
- normalized SHA-256
  `4ed68544b82ce151111746a78f3457a9bf025e043d339e5ab4c97ee92e795587`,
  MD5 `6bd3fcbea3dafde94e05f8d4ae7cf95f`, 27,055 bytes.

## Focused validation

- focused native effect/result oracle: PASS;
- focused Candle original rejection and normalized acceptance: PASS;
- normalization unit tests: PASS, 18/18;
- manifest unit tests: PASS, 28/28;
- all-inventory source preparation: PASS, 17/17 over 400/400 sources;
- parser descriptor identities: PASS, pilot 20/20 and all-inventory 400/400;
- normalization contract check: PASS, 54 entries, including the pre-existing
  unselected OCaml-3.10 source;
- manifest fixed point: PASS, 297 roots, 400 source nodes, 43 generated
  inputs;
- JSON parsing and `git diff --check`: PASS.

The v31 derived authority identities are:

- normalization contract SHA-256:
  `64b0d1c231d226581b389c2275c991ad992692c562b3f41c8cf5dc493deb4663`;
- manifest SHA-256:
  `467efdecad8e43b29e4b4e974f597c899ceab5ec590a13f6ba8339e18f051d05`;
- pilot descriptor SHA-256:
  `e6c53b5c8bc594061ce40a9eff8ba2e8f7e575fa19a59047ae7afb4a295bf750`;
- all-inventory descriptor SHA-256:
  `f2b2881e2ebed31c7e1ac0bd1ab9dc16f3b46ce68b95e4f2d3023a87dd85cfce`;
- ordered effective/prepared SHA-256:
  `df616ab1938f2dba55a77da73f4bbc21338681962e62bcca03c4a444c86c9780`
  / `90fe9018d1bf4544934ff83a6fbbb25e7b771baa92e8243e4a50fed838eb9d9e`;
- effective loader action-site SHA-256:
  `22a085f371da64d61febc91d1ff111f1f392efbb14598640052a86e6d44bfd48`;
- generated source-digest/full-build MD5:
  `25b36f072964e70f8c6e88e19724752d` /
  `ad2bd9931ebb760a6b97f0e155789c1b`.

## Next exact boundary work

Only a fresh cumulative replay from action zero may credit this batch. The
running v29 replay first tests the earlier action-070 term-`setify` batch and
is expected to expose action 079. The already committed v30 replay then tests
the WRGCVDR repair and is expected to expose action 083. This v31 batch will
be replayed only after those predecessors preserve their exact results.

The later action-126 `jHOLLight/caml/ssreflect.hl` failure has separately been
reproduced. A first annotation-only guess failed unchanged; a second probe
using current HOL Light's instantiation propagation passed. That work remains
an isolated lead for a later compatibility batch and is not part of v31.
