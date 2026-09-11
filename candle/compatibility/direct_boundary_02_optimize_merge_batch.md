# Direct Flyspeck boundary 02: `optimize` and `merge_ineq` batch

Date: 2026-09-11 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct progress

The latest completed exact cumulative run reached 48 actions and passed 47:
actions `000--046` are green and action 047,
`text_formalization/nonlinear/optimize.hl`, failed at the anticipated inline
generated-name tuple. Boundary
`00-base-through-029` remains 30/30 green and the cumulative boundary through
action 037 remains 38/38 green. Boundary
`02-nonlinear_support-through-049` is open; full direct S2 and nonlinear and
LP/S3 are open.

That exact v26 run validates the committed action-046 repair. Its immutable
development result receipt has SHA-256
`ff78642bad6b28e72b7ec49810a4389160940cf2d9d2600af28deede30410a34`.
In the persistent development process containing the exact successful
actions `000--045`, the final normalized whole-file candidates have now passed
actions `046--051`, including complete proof execution in `merge_ineq.hl`,
`vol1.hl`, and `hypermap.hl`. Thus the development probe reached and passed 52
source actions, and boundary 02 is development-green through action 049. This
does not award new exact action credit. A manual action-052 probe bypassed the
runner's action-commit bookkeeping and was rejected while resolving an already
loaded dependency; that is a probe artifact, not a Flyspeck failure.

## Historical leads and bounded changes

The `fix-top100` branch contains no matching direct-source normalization for
these files. Relevant historical Candle development commits were inspected.
Commit `64832cd3811e98fab7d31878c8186285b3f4bccb` supplied two useful leads, which
were transplanted onto the clean committed action-046 parent and regenerated
from the current authorities. Its parent also contained the falsified action-046
dereference-grouping experiment; that operation and its associated assertion
were explicitly excluded.

The initial retained changes were:

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

Whole-file probing then exposed and closed three further language classes:

1. CakeML gave the same tuple-constructor type error to the two
   `preprocess` calls whose first triple component was an inline generated
   string. Binding the pure name, and the selected case within the existing
   `Failure` handler, preserves left-to-right evaluation and exception scope.
2. CakeML interpreted `Ineq.TSKAJXY_DERIVED.ineq` as a nested module path.
   Binding the exact record before selecting the same `ineq` field preserves
   the lookup, value, order, and exceptions.
3. `merge_ineq.hl` contained another inline generated-name `mk_var` tuple and
   exactly two active bare top-level `g` effects. The name is bound before the
   identical constructor call, and each goal initializer receives an explicit
   wildcard binding while remaining evaluated once at the same position.

## Focused validation

- native OCaml string, tuple, qualified-record, and nested-comparator
  equivalence oracle: PASS;
- focused Candle tuple and qualified-record rejection/acceptance fixtures:
  PASS;
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
  `ba8a251ec5882b5adad2fc31d4eb0b52b9efe88bf5db635d72eb13c8d3947ac2`;
- manifest SHA-256:
  `c33be9b418441af9c97ca1eab0eaedf26de22450253b59f536a6b39038740685`;
- pilot descriptor SHA-256:
  `2ed60cd44537f92f38b7c82f295e42836675b2a8442571121857461c41641709`;
- all-inventory descriptor SHA-256:
  `b6409d7e96a68bb93a59d0d18ea42b97e8a59846b393c4d21219d99aaf860450`;
- ordered effective/prepared SHA-256:
  `51e8d2d2afd5c153a5d528138e64a9ea5f65f9fc7b72f9e743a00bd01c69a9e9`
  / `649bc20c70bb305c7ac041662fb7490db148270b494baf9f436c026d57c67230`;
- generated source-digest/full-build MD5:
  `b69802703c5096d4e9d7a5ccabc4016a` /
  `87d45dd69ad86aa57b80b428e2870783`.

The next action credit must come from a fresh exact cumulative run through
action 049 on committed bytes.
