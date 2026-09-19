# Proof-producing reflection for Flyspeck `list_of_faces`

Status: DEVELOPMENT / NON-RELEASE

## Boundary and supported fragment

Flyspeck's `compute_all` is an ML table builder, not a logical function that
can be translated wholesale. Its first eager theorem-producing leaf is
`List_hypermap_computations.eval_list_of_faces`; the returned interface is:

```text
|- list_of_faces concrete_input = concrete_faces
```

`candle/flyspeck_cv_compute.ml` supplies that same interface through a narrow
manual representation. The supported fragment is exactly what this leaf
needs: natural numbers, lists, pairs of naturals, nested lists, cyclic adjacent
pairs, and `list_of_faces`. It does not introduce a general HOL-to-CakeML
translator.

The cval representation uses `Cexp_num 0` for an empty list and `Cexp_pair`
for a cons cell. Three all-variable equations are submitted to
`Kernel.compute`:

1. `candle_cv_list_pairs_aux`;
2. `candle_cv_list_pairs`; and
3. `candle_cv_list_of_faces`.

Pattern equations are not submitted to the kernel primitive. The bridge proves
the representation and decoding round trips and proves the cval program
correct against Flyspeck's `list_pairs2`, `list_pairs_eq_list_pairs2`,
`list_pairs`, and `list_of_faces` theorem interfaces. The final theorem is
assembled only with ordinary kernel inference from:

- the proved input representation theorem;
- the theorem returned by `Kernel.compute`;
- the proved program-correctness theorem; and
- the proved decoder round trip.

The conversion returns no assumptions. The existing theorem statement,
Flyspeck definitions, and downstream `compute_all` interface are unchanged.

## Validation and timing

The core test starts from fresh HOL and checks the exact cval computation and
empty hypothesis list. It completed in 146.73 seconds total process time with
1,089,536 KiB peak RSS; almost all of that is the standard fresh HOL load.

The adapter test uses an independently clean minimal closure with the exact
Flyspeck theorem interfaces and a copy of the existing specialized
`eval_list_of_faces` algorithm. On the 18-face, 58-entry shape of the real
`hard_2` certificate it checks that both paths produce alpha-equivalent
conclusions and that the reflected result has no assumptions.

Because Candle deliberately makes `Sys.time` deterministic, the companion
Python controller measures wall time between flushed REPL protocol markers.
For three alternating samples of 100 calls in one warmed fresh process, median
times were:

| Path | 100 calls | Per call |
| --- | ---: | ---: |
| Existing specialized theorem builder | 0.066684 s | 0.667 ms |
| Reflective bridge | 0.737292 s | 7.373 ms |

The prototype is 11.06 times slower at this already-efficient leaf. The result
is therefore a proof-producing integration milestone, not a speedup or a
recommendation to replace `eval_list_of_faces`. Exact samples and runtime
identity are in `candle/cv_compute_flyspeck_lists_benchmark.json`.

The focused `hard_2` profile independently found that the entire real
`compute_all` phase takes only 4.061 seconds (1.269% of its 320.126-second
verifier), while constraint theorem construction, combination, variable-bound
construction, and cancellation take 313.484 seconds. This rules out broadening
the list bridge as the next performance stage.

## Recommended next reflective prototype

The next target should be the normalized exact linear-combination path inside
`Flyspeck_lp.prove_flyspeck_lp_step1`, beginning with each `sum_step`:

```text
get_ineqs
  -> map Prove_lp.transform_le_ineq
  -> fold_left Prove_lp.add_step' Prove_lp.dummy
```

`hard_2` has 1,218 constraint references. The current run spends 179.060
seconds constructing their theorems and another 78.507 seconds combining
them. A useful first prototype should:

1. keep `get_ineqs` and its authenticated input theorems as the premise
   oracle;
2. encode only selected indices, nonnegative integer multipliers, normalized
   `(coefficient, variable)` maps, and the integer right-hand side;
3. use a proved generic list soundness theorem to connect all selected input
   inequalities to one normalized sum theorem; and
4. compute and prove the normalized coefficient map and right-hand side with
   `Kernel.compute`, returning the same inequality theorem consumed by the
   existing terminal checker.

The existing `transform_le_ineq`/`add_step'` fold remains an equivalence oracle
and fallback. After this first boundary is validated, the same normalized
representation can absorb `mul_step`, `var1_le_transform`/`add_le_ineqs`, and
finally `add_cancel_step`. Every stage must compare conclusion, hypotheses, and
axiom fingerprint against the existing terminal theorem; no certificate bytes
or theorem interfaces need change.
