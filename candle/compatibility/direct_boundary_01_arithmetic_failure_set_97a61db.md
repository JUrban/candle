# Direct Flyspeck boundary 01 arithmetic: first failure and repair batch

Date: 2026-09-11 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim.

## Headline progress

- The exact cumulative run reached 31 actions and passed actions 000--029: 31
  reached / 30 passed.
- The current cumulative boundary is `01-arithmetic-through-037` (38 actions).
- The first genuine failure is action 030,
  `text_formalization/trigonometry/trig1.hl`.
- The complete failure set available from the exact fail-fast run is one
  compatibility class: anonymous structure expressions rejected by CakeML.
- A five-expression batch covers the observed `trig1.hl` occurrence and the
  four occurrences of the same class statically identified in the next source,
  `trig2.hl`.
- Full direct S2 is open. Nonlinear and LP/S3 are open.

The frozen exact run is
`/project/flyspeck-candle-runs/v16-dev-direct-boundary01-97a61db-attempt-001`.
It used Candle `97a61db513b9870efcc4ac550e97a92f81cc9f38`, Flyspeck
`1ce0353008eba83d3c76ae9a25c3c242e4802d53`, and the checked
development/nonpromotable runtime built from CakeML
`cea7c49d441c749bed4c8a987bee6d321816fbde`. It took 47:21.32 and reached
4,333,952 KiB maximum RSS. Its identities are:

- result receipt SHA-256:
  `f1a23ab3a624275824ff5ace7b24b6182f902984372552396abb0cd0c191c518`;
- transcript SHA-256:
  `9d32445f3751eec01f76cbf3e2c3ce03bc93deb709b4440d95763b30192ffdf9`;
- timing SHA-256:
  `c1ec7cfa17c33bf14b55e218af94ada87b9f8da7b2d2c9c391c86a04750c923c`;
- preparation receipt SHA-256:
  `d186448e365a18ee2addf324cfaf678211ac3a9d05dfff2c372f90a15fbc22bc`.

Thirty exact nonce-bound success markers authenticate actions 000--029. Action
030 was invoked but emitted no success marker. Its first diagnostic was:

```
ERROR: Type mismatch between thm and (unit -> unit) -> _0 at line 8
```

The enclosing module diagnostic highlighted its first binding, while the
source watchpoint is original `trig1.hl` line 24:
`prioritize_real();;`.

## Minimized coherent repair

`PROJECT-TRIG1-S3-STRUCTURE-EFFECT-001` changes only that exact anonymous
call to `let _ = prioritize_real();;`. The same call is evaluated once in the
same module-initialization position, its unit result is discarded, and its
priority-state effect, exceptions, and following definitions are preserved.

A static pass over all eight arithmetic-boundary sources found four further
instances of the identical structure-expression class, all in `trig2.hl`:

- `parse_as_infix("polar_lt",(12,"right"));;`
- `parse_as_infix("polar_le",(12,"right"));;`
- `parse_as_infix("polar_cycle_on",(12,"right"));;`
- `parse_as_infix("re_eqvl",(12,"right"));;`

`PROJECT-TRIG2-S3-STRUCTURE-EFFECT-001` gives each exact call an explicit
wildcard binding. Every parser registration keeps its name, precedence,
associativity, position, order, effects, and exception behavior. No definition,
theorem statement, hypothesis, proof body, or axiom changes.

The normalized source identities are:

- `trig1.hl` SHA-256:
  `0425a46e53b1254736c47d432e66bcfa487080ef2798568bba2cceb373a7c360`;
- `trig2.hl` SHA-256:
  `d42ea72e66494a07db2b337c0d06f638a7ace0311946db35045713927275a3e0`.

## Historical leads and focused validation

`fix-top100` and the relevant historical Candle branches contain the original
anonymous `prioritize_real` spelling and no patch for these trigonometry
sources. The existing, independently validated Candle normalization for the
same OCaml/CakeML module-structure class supplied the implementation pattern,
not evidence for these new instances.

Focused validation on the candidate bytes is green:

- the native OCaml effect/order oracle equates the original anonymous calls
  with the normalized wildcard bindings;
- all 17 normalization tests pass;
- all 28 manifest/generator tests pass;
- the independently derived 400-source preparation passes all 17 tests with
  362 exact-original and 38 exact-normalized source inputs;
- both generated parser-selection descriptors reproduce exactly at 20/20 and
  400/400;
- all 47 direct stratum-runtime tests pass;
- manifest regeneration/check and `git diff --check` pass.

The broader parser-diagnostic suite retains a pre-existing fail-closed source
anchor mismatch: the manifest names CakeML `cea7c49d...`, while
`flyspeck_loader_quotation.py` still pins the older `8a892690...` loader
source. The same focused test fails on the untouched `97a61db` baseline, so it
is not a regression from this arithmetic batch and is not being folded into a
direct-runtime compatibility change.

The next required gate is a fresh exact DEVELOPMENT / NON-RELEASE cumulative
run of actions 000--037 from the committed candidate bytes. Only that run can
raise this boundary above 31 reached / 30 passed and reveal any subsequent
independent arithmetic failure.
