# Direct Flyspeck allocated-identity normalization audit

Date: 2026-08-27  
Pinned Flyspeck: `1ce0353008eba83d3c76ae9a25c3c242e4802d53`

## Result

The selected direct graph contains twelve built-in physical-identity operators
over allocated values: ten sharing controls in `general/lib.hl`, one string
filter in `general/print_types.hl`, and one term filter in
`jordan/tactics_jordan.hl`.  Schema 2 of
`candle/flyspeck_normalizations.json` covers those sites with seven ordered,
hash-bound operations across three source files.  Together with the existing
immediate-integer operation, the contract contains four source entries and
eight operations.

This is a regression-pending source remedy, not a completed compatibility
claim.  The compiled direct loader does not yet materialize the overlay, and
the final full-run theorem/assumption fingerprints remain mandatory.

## Site-specific rules

- `filter`, `partition`, `uniq`, and Patricia-tree `undefine` return an explicit
  change/all-unchanged result from their recursive workers.  They preserve the
  original structural result, callback and exception order, and the exact
  original object on an unchanged route without observing physical identity.
- The selected graph has no `qmap` caller outside its own definition and
  recursive body.  The normalized binding therefore raises explicitly on any
  call.  This is fail-closed selected-graph non-use, not general `qmap`
  compatibility.
- The selected graph has no `Print_types.unsuppress` occurrence outside its
  signature and definition.  Its normalized binding likewise raises on any
  call.
- Jordan's `relabel_bound_conv` structurally excludes copies equal to the
  abstraction binder.  The result remains alpha-equivalent, but a separately
  allocated equal variable can cause OCaml's physical filter and the
  normalized filter to choose differently spelled fresh binders.  The host
  oracle freezes that known general-input difference; an exact selected-run
  fingerprint difference blocks release.

The generator freezes the four `qmap`/`unsuppress` signature, definition, and
recursive-body occurrences.  Any new caller aborts regeneration.

## Authenticated outputs

| Source | Original SHA-256 | Normalized SHA-256 | Normalized bytes |
|---|---|---|---:|
| `text_formalization/general/lib.hl` | `a429247955e1e095e5663813e9609c43697d83d80f357c7855af3b76a3145865` | `d1ae25218cce2f2f510966d574d48d283c04748a1b6c8d8dfc0c2ca52438a60f` | 29,873 |
| `text_formalization/general/print_types.hl` | `193abcdff7657f421398203c67e67d32ce5204ce4ba5a04adad53f37fd161ae6` | `cb6ab239f202554f204188a3feac089cd2cc69645088e0d95659aeabb304b6de` | 3,140 |
| `text_formalization/jordan/tactics_jordan.hl` | `3af61cf6961097eae9b67f3f3aaeef8fbd8c9a2ec2dfef1e95594561bac58ebe` | `e34517f72ed00eeb30275f1dca01210604665a43d96aa1d759c9f6890f0312e5` | 54,860 |

The complete normalization contract SHA-256 is
`a8c94a3d9bd7d01a3858d42d7f913ae39cceb1d71e153089950fb70bf0e20752`.
The generated full-build program is SHA-256
`44ae6acc8b43e9408694f64457e0c1fe8b481865abc9afdd2921fcf981094b4a`
and MD5 `fa440c6eae11574a55adab1f881fd834`.

## Evidence

`flyspeck_identity_ocaml_oracle.ml` exhaustively checks lists through length
five over a three-value alphabet and different predicates, including
structural results, callback order, predicate-exception traces, and
unchanged-object sharing for the four transformed algorithms.  It also checks
valid Patricia-tree deletion and missing-key sharing, checks that both non-use
bindings fail closed, and records the Jordan fresh-name boundary.
`flyspeck_identity_normalized_oracle.ml` compiles and passes with the pinned
Candle executable without using `==` or `!=`.
`check_flyspeck_normalized_identity.py` independently masks comments, strings,
and HOL quotations and reports zero executable physical-identity operators in
all four normalized files; its masker regression covers both rejected operator
forms and false-positive quotation/comment examples.

The host microbenchmark uses 100 repetitions over 5,000-element lists.  One
sample showed comparable CPU time and these allocations: mixed `filter`,
6.0 MB reference versus 14.0 MB normalized; mixed `partition`, 24.0 MB versus
32.0 MB; duplicate `uniq`, 6.0 MB versus 14.0 MB.  This is measurement, not a
stable performance threshold.  The extra short-lived option values are an
open scale concern to reassess in the full run.

Validation commands:

```sh
(cd candle && python3 -m unittest -v test_flyspeck_normalize.py)
python3 candle/flyspeck_normalize.py \
  --flyspeck-root /project/worktrees/flyspeck-v13-source --check
CANDLE_BINARY=/project/worktrees/candle-loader-v13/candle.sh \
FLYSPECK_ROOT=/project/worktrees/flyspeck-v13-source \
  candle/test_flyspeck_identity_normalization.sh
ocaml -noinit -noprompt candle/flyspeck_identity_benchmark.ml
```

## Open release gates

1. Integrate ordered original-hash check, materialization, normalized-hash
   check, parsing, and evaluation in the compiled direct loader.
2. Reach all normalized files in an exact full-loader run and prove the two
   fail-closed bindings are not called.
3. Compare exact theorem, definition, assumption, and selected binder-name
   fingerprints with the pinned OCaml run.
4. Re-measure time and peak memory at Flyspeck scale; the local allocation
   increase is not waived.
5. Keep the umbrella identity ledger at `regression_pending` until all four
   gates pass.  No S milestone is advanced by this patch alone.
