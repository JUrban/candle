# Direct boundary 05: action-152 nested-module loop structure effects

Status: DEVELOPMENT / NON-RELEASE. This is direct functional evidence only;
it makes no S1, S2, S3, qualification, promotion, or release claim.

## Headline Flyspeck progress

- Flyspeck actions reached / passed: **153 / 152**.
- Exact cumulative green prefix: actions **000--151 = 152/152**.
- Current cumulative boundary: `05-lp_support-through-184`.
- First genuine failure remains action 152,
  `formal_lp/hypermap/arith_link.hl`, while loading
  `formal_ineqs/arith/arith_num.hl`.
- Current failure class: bare `for` expressions used as structure items inside
  a constrained nested module hit the rebuilt frontend's retained anonymous
  structure-expression (`Pany`) scope defect.
- Full direct S2: open. Nonlinear plus LP / S3: open.

No action beyond 151 is credited by this report. A fresh cumulative replay of
the candidate is required.

## Complete replay falsified the seed-only diagnosis

The immutable fixed-head attempt

```text
/project/flyspeck-candle-runs/v116-dev-direct-boundary05-7a47d29-heap16-attempt-001
```

used Candle `7a47d296907be67296d24b944a554001d3b1c208`, CakeML
`73945eca14ee1866bfa6f96de09bf5744dce485d`, Flyspeck
`1ce0353008eba83d3c76ae9a25c3c242e4802d53`, and runtime SHA-256
`3aaa248c0d5d6c96fa8e36445d1a945a751f0cf11a8b734a6142e9fab1088b2b`.
Its nonce was `cee4a686caf2ec166bb46ad2425e7a54`.

It emitted exactly 152 ordered success markers, indices 000--151, and then
reproduced the prior failure exactly:

```text
Expected to be at EOF
Parsing failed at line 5

module Arith_num : Arith_num_sig = struct
^^^^^^
```

The attempted input already contained explicit discarded-result bindings for
both standalone theorem-table seed insertions. Those two expressions were not
the sufficient cause. The candidate and diagnosis in v52 are superseded.

Evidence identities and resources:

- `candle.log` SHA-256:
  `21bb83b920c78924736663ad060445f5cdf40d9bc2e1edfb0ea00db7165058cd`;
- `time.txt` SHA-256:
  `15770df0832c727c6343cad5a5717a9f764f83c7e6ab335ca08af17dfb54eee0`;
- preparation receipt SHA-256:
  `60a0daf3e48a51bf888df1cafb22246444ad5fd2e409f297a1c4a67e5d027a50`;
- wall time: `2:58:43`;
- maximum resident set: 17,105,536 KiB;
- swaps and major page faults: zero.

An independent 16 GiB replay of the pre-candidate head is retained at
`v110-dev-direct-boundary05-e68a9eb-heap16-attempt-001`. It also reached and
passed exactly actions 000--151, took `3:08:08`, used 17,097,472 KiB maximum
RSS, and had zero swaps and major faults. Action 145 occupied approximately
65 minutes in v110 and 63 minutes in v116. Reducing the heap from 32 GiB to
16 GiB therefore did not remove the cumulative-state performance anomaly;
the earlier clean focused predecessor remains the important approximately
seven-minute contrast.

## Minimized nested-module reproducer

Comparison with the previously passing transient source showed that all 24
outer `for` loops in `Arith_num` are bare expressions in the constrained
module structure. Existing central gates covered top-level loops and loops
inside value expressions, but not this nested-module structure-item context.

The source
`compatibility/fixtures/ocaml_for_nested_structure_effect_deferred.ml`
(SHA-256
`40faf8b08aa21ae1b920c90ecc98a0232715ddaa537817ee362e4d9c74beb25f`)
contains one such bare loop. Native OCaml 4.14.1 retains the preceding binding
and evaluates the expected result to `true`; the exact compiled Candle runtime
fails at the enclosing module declaration with `Expected to be at EOF`.

The paired source
`compatibility/fixtures/ocaml_for_nested_structure_effect_wrapped_control.ml`
(SHA-256
`981ad5f698288d30776fec33043617df70eeaa95691b15fd302644ed2d119f43`)
changes only the bare structure expression to
`let _ = for ... done`. Native OCaml and the exact compiled Candle runtime
both produce `[0;1;2]` and the expected boolean `true`.

The immutable four-way evidence is retained at:

```text
/project/flyspeck-candle-runs/v118-nested-module-for-structure-controls-001
```

The bare Candle log has SHA-256
`a36d4031e70fe5882ff9f0a1e0f844b6530c70e3ef518686e0de71207ebafa7b`;
the wrapped Candle log has SHA-256
`8d230606991e1eaf46e8cf342e3741da7f4c14a8403d3382f2cae47a9c3ede43`.

## Narrow candidate correction

The `PROJECT-ARITH-NUM-S2-VALUE-RESTRICTION-001` normalization now enumerates
all 24 and only the outer module-structure loops at source lines 114, 169, 211,
325, 377, 442, 503, 577, 671, 703, 718, 745, 777, 792, 929, 955, 963, 974,
1127, 1137, 1203, 1253, 1487, and 1495. Each exact line receives the same
explicit discarded-result binding as the passing control:

```ocaml
let _ = for i = ... do
```

Every bound, direction, body, nested loop, mutation, unit result, exception,
and evaluation position remains unchanged. No indexed assignment, definition,
conversion, theorem statement, hypothesis, proof, tactic, or axiom changes.
The central native lowering still handles each loop expression itself; this
source normalization only avoids the diagnosed nested structure-item defect.

The candidate normalized `arith_num.hl` is 56,129 bytes, MD5
`f25a3edd6ec52d04c0086bc6bb2a9879`, and SHA-256
`0d16e338cf878a600758e194464a450ad393523b57666ae75c984b8544afd855`.
The 80-entry / 274-operation normalization contract has SHA-256
`723f44528a79647e33993a6d529c3a2f42fbcccfe448962bbb039b8fac69a7fc`.
The regenerated 297-root / 400-source / 43-generated-input manifest has
SHA-256
`f891c5320314cdacd76c571f707ddb35703ef9222093b6de675418d4cafa7da7`.

Focused checks completed before the cumulative replay:

- native and exact-runtime bare/wrapped nested-module controls;
- 18 normalization tests;
- arithmetic normalization gate, including exact enumeration of 24 wrapped
  outer loops and rejection of any remaining bare outer loop;
- 28 manifest tests;
- independent manifest fixed-point check: 297 roots, 400 source nodes,
  43 generated inputs;
- `git diff --check`.

The old-runtime post-action-150 checkpoint cannot validate this candidate:
it predates the central frontend loop and indexed-assignment lowering. It is
therefore not used as authority. Full current-runtime action-152 loading and a
fresh action-zero cumulative replay remain required before action 152 can be
credited.

## MESON-ordering issue disposition

No comparator-ordering or pointer-equality investigation is carried into this
LP failure. The earlier GRUTOTI runaway was specifically caused by unintended
transitive exposure of `Trigonometry2.SET_TAC` / `SET_RULE`; restoring the
intended bindings made the complete file finish in about 11 minutes 51 seconds
with all 2,364 MESON progress records matching native output byte-for-byte.
That name-resolution diagnosis is recorded separately in
`direct_boundary_04_v47_grutoti_native_set_scope.md`.
