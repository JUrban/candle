# Direct Flyspeck boundary 02: `optimize` and `merge_ineq` batch

Date: 2026-09-11 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct progress

The latest completed exact cumulative run still reached 47 actions and passed
46: actions `000--045` are green and action 046,
`text_formalization/nonlinear/parse_ineq.hl`, was the first failure. Boundary
`00-base-through-029` remains 30/30 green and the cumulative boundary through
action 037 remains 38/38 green. Boundary
`02-nonlinear_support-through-049` is open; full direct S2 and nonlinear and
LP/S3 are open.

An exact run of the committed action-046 repair is in progress independently.
This batch prepares the already observed action-047 and action-049
compatibility classes, but does not award either action new exact credit.

## Historical leads and bounded changes

The `fix-top100` branch contains no matching direct-source normalization for
these files. Relevant historical Candle development commits were inspected.
Commit `64832cd3811e98fab7d31878c8186285b3f4bccb` supplied two useful leads, which
were transplanted onto the clean committed action-046 parent and regenerated
from the current authorities. Its parent also contained the falsified action-046
dereference-grouping experiment; that operation and its associated assertion
were explicitly excluded.

The retained changes are:

1. In `text_formalization/nonlinear/optimize.hl`, bind each generated `x`/`a`
   name immediately before the same `mk_var(name,real_ty)` call. This avoids
   the independently reproduced CakeML tuple-constructor inference failure
   while preserving the generated string, type, term, order, effects, and
   exceptions.
2. In `text_formalization/nonlinear/merge_ineq.hl`, supply the existing binary
   `setify` with the exact lexicographic comparator for its
   `(term * (term * term))` representation:
   `Pair.compare Term.compare (Pair.compare Term.compare Term.compare)`, with
   the non-strict `<= 0` boundary used by Flyspeck's native `setify`.

The comparator change is confined to this exact hash-pinned bound
representation. It preserves ordering and duplicate removal and changes no
inequality, theorem statement, hypothesis, proof, proof intent, or axiom.

## Focused validation

- native OCaml nested-comparator equivalence oracle: PASS;
- focused Candle nested HOL-term ordering/deduplication fixture: PASS;
- complete nonlinear boundary compatibility gate: PASS;
- normalization and manifest unit tests: PASS, 46/46;
- all-inventory source preparation: PASS, 17/17 over 400/400 sources;
- parser descriptor checks: PASS, pilot 20/20 and all-inventory 400/400;
- manifest fixed point: PASS, 297 roots, 400 source nodes, 43 generated
  inputs;
- JSON parsing, conflict-marker scan, and `git diff --check`: PASS.

Current derived authority identities are:

- normalization contract SHA-256:
  `1a2cac4218669a0e4e30c1f432594a3e26b0dd28827a8986e88fb1ffec141522`;
- manifest SHA-256:
  `7948def8e017e2349f82998212c859e823329d992e61315c266382a2565eb56b`;
- pilot descriptor SHA-256:
  `72efcb6dc71a29784573fc544dc1dc021400c93d0f112575907d227de1fa4c9a`;
- all-inventory descriptor SHA-256:
  `ef2e511469acf8d816cc83b3d07c19842bc8a50ae0f3609f1c694beb4c8f9ce4`;
- ordered effective/prepared SHA-256:
  `337d371f176393e4d4dda93ce20ef84bccc5a25f585019ca358c63530fdbdb6a`
  / `d673ff23907902db9db2c191f680769e9ee876eccd209e39ddf2008180cd84f2`;
- generated source-digest/full-build MD5:
  `fe3296eff52dcc7556731fa15cb12b5e` /
  `2424d81f22a463b238ace014647e9be8`.

The next action credit must come from a fresh exact cumulative run through
action 049 on committed bytes.
