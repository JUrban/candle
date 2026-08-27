# `fix-top100` integration audit

Audited 2026-08-27 against public Candle `master`
`5b1888b9a0c1da7ca0ef2e80526b726f2e27df9d` and the recorded anchor
`7792fc9f3de2470f10085e3bab42fc1c042cf9c4`.

## Branch relationship

The merge base is `bc9fdcf897ff93d921d095f10f11048be35ef493`.
`master` has one runner commit after that base; `fix-top100` has eight commits.
`git cherry` marks all eight with `+`, so none is patch-equivalent to a commit
already on `master`. The PFT and PFT-coverage branches descend from `master`,
not from `fix-top100`, and likewise contain none of the eight commits.

## Anchor changes requiring integration

| Commit | Corpus slice | Compatibility class | Integration assessment |
| --- | --- | --- | --- |
| `5c44565` | `100/cubic` | polymorphic comparison | Explicit `Term.(<)` calls; small source normalization, missing oracle and fingerprints. |
| `badbd63` | `100/e_is_transcendental` | source syntax | Removes a stray semicolon inside a call; source correction rather than a runtime feature. |
| `02ed7f7` | `100/heron` | polymorphic comparison | Supplies `Term.(<)` to `setify`; small source normalization, missing fingerprints. |
| `1bfc727` | `100/piseries` | numerics and value restriction | Adds `round_num`, `ceiling_num`, changes negative rational floor behavior, and adds a type annotation. Needs OCaml boundary tests before promotion. |
| `2ae8a2c` | `100/ramsey` | let-polymorphism and parser overload state | Splits a polymorphic local helper and adds inferior overload insertion. The overload-state change needs order/reset tests. |
| `dceb27d` | `100/bertrand-primerecip` | floats, bytes, FFI, filesystem | Adds `frexp`, byte packing, float/num conversion and source normalization. Its custom FFI silently ignores unknown commands and uses assertions, so it does not yet meet the v1.3 FFI contract. |
| `218c7c9` | `100/ceva`, `100/thales` via `Examples/sos.ml` | comparison, finite maps, value restriction, numeric and process FFI | Large mechanical rewrite plus helpers. Split into independently tested compatibility changes; retain solver output as untrusted evidence. |
| `7792fc9` | numeric users including SOS | negative rational powers | Corrects `power_num` for negative exponents. Add zero/negative/boundary tests and divide-by-zero behavior before promotion. |

The changes therefore should not be merged as one “Top 100 fix.” In
particular, the FFI and numeric changes cross trust/semantic boundaries while
the comparator and syntax changes are mostly source normalization.

## Actual suite and current evidence

`holtest.mk:GREAT_100_THEOREMS` contains 65 execution targets. The combined
`100/bertrand-primerecip` target loads two files, giving 66 covered source
files. `100/sqrt.ml` exists but is not in the upstream variable; its exclusion
has not yet been approved or assessed for the Flyspeck dependency closure.
There is no skip mechanism in the runner and the committed manifest records no
skipped target.

The runner's prior success condition was only “all requested files finished
loading.” It captured no canonical theorem or assumption fingerprint. Thus all
65 target fingerprint records begin as missing, even where a load passes.

The manifest now resolves 97 proposed named result bindings across all 65
ordered target sessions. It records shadowed declarations and the binding that
is actually visible after the load. Four broad or repeatedly rebound targets
(`cantor`, `fourier`, `piseries`, and `quartic`) remain explicit manual-review
mappings. The runner can request structural theorem, conclusion, sorted
hypothesis, and sorted global-axiom identities after a load, but no expected
reference hashes are populated yet. An observed identity is therefore reported
as `observed_uncompared`, never as a fingerprint match.

The clean compiled-Candle baseline observed
`100/bertrand-primerecip` fail after 212.6 seconds. The failure occurs before
the target declaration is elaborated: Candle rejects the first OCaml float
literal in `num_of_float`. The minimized difference is ledger entry
`CANDLE-OCAML-FLOAT-LITERAL-001`. OCaml 4.14.1 accepts the one-line reproducer;
the pinned compiled Candle reports a parse failure. The anchor's float rewrite
is not being imported: it combines the syntax workaround with broad float/byte
FFI. The smaller implementation under test restores CakeML's retained decimal
float token to the parser and lowers through the existing `Double.fromString`
operation. Exact reference words and negative parses are pinned in
`float_literal_cases.json`. CakeML commit `30e014bd9` has passed the targeted
four-theory build and its 10 positive normalization plus six rejection tests.
The first translated-program build then completed 193 of its 194-theory closure
and saved the direct float bridge theorems, but failed the final
`caml_parserProgTheory` target at `ptree_Expr_preconds`. The failure reproduced
the exact side-proof line removed by upstream commit `5bfcf6b40` during the
float-disable cleanup. CakeML commit `8ef793fd8` restores that single historical
unfolding step; its rerun is pending a shared-HOL handoff. The rebuilt-Candle
IEEE differential, end-to-end rejection run, performance comparison, clean
target load, and fingerprints therefore remain missing.

## Integration sequence

1. Land the generated inventory, ledger, and static checks on the integration
   branch; merge the independent timing/RSS report changes afterward.
2. Import the two small comparator normalizations and the syntax correction
   separately, each with an OCaml/Candle reproducer and regression test.
3. Specify and test `floor_num`, rounding, ceiling, and negative powers at
   OCaml boundary cases before importing numeric implementations.
4. Specify literal normalization and the float/byte encoding, then replace the
   anchor's assertion/silent-return FFI behavior with total checked statuses.
5. Split the SOS rewrite by compatibility class; validate `ceva` and `thales`
   before attempting solver-heavy uses.
6. Teach the runner to request named target theorems and canonicalize theorem
   plus assumption fingerprints. A load-only pass remains provisional until
   those fields are populated.
7. Run the complete 65-target matrix twice from clean state only after the
   targeted failures and fingerprint plumbing are green.
