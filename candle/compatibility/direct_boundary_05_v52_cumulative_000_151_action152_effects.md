# Direct boundary 05: cumulative 000--151 and action-152 effect failure

Status: DEVELOPMENT / NON-RELEASE. This is direct functional evidence only;
it makes no S1, S2, S3, qualification, promotion, or release claim.

> **Superseded diagnosis (2026-09-16).** The complete fixed-head v116
> cumulative replay applied the two seed bindings proposed below and failed at
> the same action-152 parse location.  It therefore falsifies the seed-only
> hypothesis and candidate in this report.  The retained report is historical
> evidence, not current authority; see
> `direct_boundary_05_v53_action152_nested_for_structure.md` for the minimized
> nested-module bare-loop reproducer and replacement candidate.

## Headline Flyspeck progress

- Fresh cumulative action-zero execution: **153 actions reached / 152 passed**.
- Exact cumulative green prefix: actions **000--151 = 152/152**.
- Current cumulative boundary: `05-lp_support-through-184`.
- First genuine failure: action 152, `formal_lp/hypermap/arith_link.hl`,
  while loading normalized `formal_ineqs/arith/arith_num.hl`.
- Current failure class: two anonymous theorem-table seed effects left to the
  rebuilt frontend's known-defective general structure-expression lowering.
- Full direct S2: open.
- Nonlinear plus LP / S3: open.

The immutable failed attempt is:

```text
/project/flyspeck-candle-runs/v109-dev-direct-boundary05-e68a9eb-attempt-001
```

It used Candle `e68a9eb01eea0f70d3eb71380dbf204e16f89694`, CakeML
`73945eca14ee1866bfa6f96de09bf5744dce485d`, Flyspeck
`1ce0353008eba83d3c76ae9a25c3c242e4802d53`, and runtime SHA-256
`3aaa248c0d5d6c96fa8e36445d1a945a751f0cf11a8b734a6142e9fab1088b2b`.
The attempt nonce is `411c417fafe1865d5c016f534bcd8107`.

The run emitted exactly 152 ordered nonce-bound action-success records,
indices 000--151. The final accepted theorem source was
`text_formalization/local/lp_details.hl`; action 152 emitted no success or
boundary record. The process exited 0 only because the Candle REPL returned
after the nested parse failure, so the marker ledger, not process status, is
the result authority.

Run identities and resources:

- complete log SHA-256:
  `7ed12f3b31e18b6ba3e480251889bd4d8574408977e3dc4451ad68893eb2b2c7`;
- timing record SHA-256:
  `eaea2c8f633326364c16a6a663381325a6cf8e9a97a8dc00c2b3acfa714125de`;
- preparation receipt SHA-256:
  `64cd61c9ed4358a68967484425c3ecbfae9fe951f047a6b67c5d24006a8c1fb8`;
- wall time: `3:20:53`;
- maximum resident set: 33,872,384 KiB;
- swaps and major page faults: zero.

Action 145, `add_triangle-compiled.hl`, passed from this complete cumulative
state but took about 72 minutes under `CML_HEAP_SIZE=32768`, versus about seven
minutes in the earlier reduced focused state. This is recorded as a runtime
performance anomaly, not a semantic or compatibility failure. An exact 16 GiB
heap A/B replay is retained separately and does not alter the 152/152 result.

## First failure

Action 152 selected the authenticated normalized arithmetic sources, loaded
`misc_functions.hl` and `misc_vars.hl`, and then reported:

```text
Expected to be at EOF
Parsing failed at line 5

module Arith_num : Arith_num_sig = struct
^^^^^^
```

The reported module start is the enclosing-phrase backtracking location, not
evidence that constrained-module syntax is unsupported. A minimized control
with a module type, two anonymous effects, and a constrained module passes in
both OCaml 4.14.1 and the exact compiled Candle binary. Its source is
`compatibility/fixtures/ocaml_structure_effect_constrained_module_control.ml`,
SHA-256
`d4c28e353cbc846b73ef293427c2686c1e7ca37fc761db650237a54a47dcdd09`.

The previously accepted action-152 focused source used direct equivalents for
all 37 loops and five indexed assignments while the verified frontend build
was pending. Comparing that complete passing source with the cumulative input
leaves exactly two additional non-loop/non-assignment changes:

```ocaml
let _ = Hashtbl.add even_thm_table names_array.(0) EVEN_B0;;
let _ = Hashtbl.add odd_thm_table names_array.(0) ODD_B0;;
```

The raw source spells both as anonymous structure expressions. This matches
the separately retained compiled reproducer in which the rebuilt frontend's
`Pany` lowering loses a preceding module binding. The central loop and indexed
assignment gates remain green and are not rewritten here.

`fix-top100`, `codex/v16-arithmetic-boundary`, and their remote counterparts
retain the original two effects and contain no repair for this source. The
historical focused candidate supplies a lead only; the correction below is
independently minimized and hash-bound.

## Narrow candidate correction

The existing `PROJECT-ARITH-NUM-S2-VALUE-RESTRICTION-001` entry gains one
exact-line operation covering all two and only the bare theorem-table seed
insertions. Each `Hashtbl.add`, table, key, theorem value, mutation, unit
result, exception, and evaluation position is unchanged; only the discarded
result is made explicit. No loop, indexed assignment, arithmetic definition,
conversion, theorem statement, hypothesis, proof, tactic, or axiom changes.

The candidate normalized `arith_num.hl` is 55,937 bytes, MD5
`d762b035245535922c850badfab719a8`, and SHA-256
`2c05e8d13878e1de6f253dbab610e1758365e877fb8551c53105d4c729b40f12`.
The 80-entry / 273-operation normalization contract has SHA-256
`915fc455ed4b2985628920468918af34f70480de385b76a9091f0055a02245e7`.

Focused authority checks are green:

- normalization contract validation: 80 entries;
- 18 normalization tests;
- manifest regeneration and independent fixed-point check: 297 roots,
  400 source nodes, 43 generated inputs;
- 28 manifest tests;
- 10 stratum-plan tests;
- `git diff --check`.

The separate all-inventory source-only test retains pre-existing stale
hard-coded authority identities and remains fail-closed before preparing any
source. Its pinned manifest/normalization SHA-256 values are `908c630f...` and
`2a6c0ff4...`; the untouched parent `e68a9eb` already contains `f4eb770e...`
and `cf4ac534...`. This functional batch does not refresh that unrelated
assurance subsystem. Complete current-runtime action-152 loading and a fresh
cumulative replay are still required; this report does not credit action 152.
