# Direct Flyspeck boundary 00--029: failure set and focused repair batch

Date: 2026-09-11 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim.

## Headline progress

- Exact promoted progress remains 3 actions reached / 2 passed.
- The current cumulative boundary remains `00-base-through-029`.
- The frozen dirty all-action diagnostic invoked all 30 actions and found 24
  independently clean actions. Its initial failures were actions 015, 022,
  and 025 plus apparent dependency cascades at 023, 026, and 027.
- A persistent real-source probe confirmed 023 as a cascade, then exposed 026
  and 027 as genuine additional failures. The complete available failure set
  for this batch is therefore five compatibility classes at 015, 022, 025,
  026, and 027.
- Focused candidates now load all five sources through their selected exports.
  A fresh exact cumulative run is still required before claiming 30/30.
- Full direct S2 is open. Nonlinear and LP/S3 are open.

The original complete diagnostic is frozen at
`/project/flyspeck-candle-runs/v16-dirty-all-actions-00-029-a01868b-run-006`.
It used Candle `a01868bd204b86be0cb15e38a5c0f2f257b96a76`, Flyspeck
`1ce0353008eba83d3c76ae9a25c3c242e4802d53`, and a checked nonpromotable
development runtime built from CakeML
`cea7c49d441c749bed4c8a987bee6d321816fbde`. It took 44:04.52 and reached
4,337,536 KiB maximum RSS. Its evidence identities are:

- result receipt SHA-256:
  `f3e1be9e1c99e47e69230f35d40a1f2129f91e84e22727e6090819b420d3f71b`;
- transcript SHA-256:
  `5f59b88e5a5dba987585b96e74175b3c7196d61caf8fa5c7df17aabcf7c5315f`;
- timing SHA-256:
  `c27b7b75dbe97dd023afdc04e08e20e295039b92056b3f55bb0d6117921145ae`;
- preparation receipt SHA-256:
  `93af8b6ff82039788346e80f685626c7f67167f9a041da31013028deda223f32`.

Its independently clean indices were 000--014, 016--021, 024, and 028--029.

## Complete failure set and minimized repairs

### Action 015: `leg/collect_geom2.hl`

Candle's enclosing error was caused by two anonymous theorem computations at
original lines 870 and 1328. The normalization adds `let _ =` to exactly those
expressions. Both theorem computations still run once in their original
positions and their results remain discarded. The complete source loads
through `Collect_geom2.VBVYGGT`.

Normalized SHA-256:
`3dd6402c9dad7f5957f7a900811f829b556a7bdaadbc0942765ed759a49b1b26`.

### Actions 022 and 023: `tactics_jordan.hl` and its consumer

The first failure was CakeML's premature unification of the inline constructor
name pair passed to `new_basic_type_definition`. The repair evaluates the same
two pure string concatenations into `absname` and `repname`, then passes the
identical pair to the same kernel function. Three later anonymous `dropq_conv`
examples also require explicit wildcard bindings; all three conversions still
execute and fail closed in their original positions.

The complete source loads through `Tactics_jordan.HASHIFY`. With that module
present, action 023 (`num_ext_nabs.hl`) loads completely, confirming that its
original failure was only a dependency cascade.

Normalized SHA-256:
`b9b0d263d84603e7c9c6bd4893a3ad9080d18b88b7fdc97d4c862ffed8927a1b`.

### Action 025: `jordan/float.hl`

Exact phrase enumeration found 24 formerly anonymous `add_test` computations,
including a top-level `let ... in add_test` and a comment-prefixed call that a
column-zero scan missed. Together with the source's already explicit
`dest_interval` binding, all 25 tests remain active and ordered. Four OCaml
`assert` expressions are expanded to identical boolean guards that raise the
runtime's distinct `Assert_failure` constructor; they are not converted to
`Failure` and cannot be absorbed by a `Failure` handler.

The two rounding functions use Candle's existing `float_fabs` name and an
explicit `Cake.Double.(>=)` comparator. The runtime supplies exact-source
`ceil` and field-based `ldexp`. The complete source loads and exports
`Float.REAL_INEQUALITY_CALCULATOR`.

Normalized SHA-256:
`34cfe8f531c899aea86ca8402db38710f2c638c0f8f29a8163775c2360058f59`.

### Action 026: `jordan/flyspeck_constants.hl`

Once `Float` loaded, the first real failure was
`INTERVAL_OF_TERM : SQRT`. Per-conjunct isolation showed that the three
non-pi square-root pairs passed while every pi-derived interval failed.
Instrumenting `heron_sqrt` exposed recursion-depth exhaustion.

The root cause was `Num.float_of_num`: it converted an arbitrary-precision
numerator and denominator separately through a Word64-backed double primitive,
truncating the large rational seeds produced by the pi series. The replacement
scales the exact rational directly and constructs the nearest binary64 value,
with ties-to-even, subnormal, signed, carry, and overflow handling. It does not
add an FFI or approximate the rational before rounding. Focused binary64 edge
tests pass, and the persistent source probe then loads action 026 through
`Flyspeck_constants.bounds`.

### Action 027: `jordan/misc_defs_and_lemmas.hl`

The failure localized to the base case of `NUM2_COUNTABLE`. After
`NAME_CONFLICT_TAC`, the goal retains the first coordinate `x`, but the modern
script constructed its diagonal sum and generalized the unrelated renamed
`x'`. Historical Candle source supplied the lead. The bounded repair retains
the current `SUBGOAL_MP_TAC` API and changes only those two references from
`x'` to `x`. The theorem statement, recursive enumerator, induction, hypotheses,
proof intent, and axioms are unchanged. The complete source loads through
`Misc_defs_and_lemmas.POW_2_LE1`.

Normalized SHA-256:
`e0df2788785223bd3d5f22f69839bdaa92b8221bc1540be0ccc76c60b0ac9538`.

## Historical leads and independent validation

The same constructs were checked in `fix-top100` and relevant historical
Candle/Flyspeck branches before finalizing each repair. Historical source
provided the `float_fabs` and `NUM2_COUNTABLE` variable-selection leads, but
`fix-top100` retained the lossy large-rational conversion. No historical patch
was treated as authority: every adopted spelling was minimized and rerun in the
current real-source environment.

The persistent probe is frozen at
`/project/flyspeck-candle-runs/v16-persistent-boundary-batch-a01868b-probe-001`.
Its 11,796,400-byte transcript has SHA-256
`0bf8029f61f0e46670fad37758177249691efe14e35bd6b7937877a0602db22f`.
It is diagnostic only: action 026 used an injected equivalent of the pending
numeric runtime so that the already-loaded REPL did not need an expensive
relink. It is not cumulative or release evidence.

## Validation and next gate

- The 36-entry normalization contract reproduces every candidate byte-for-byte.
- 45 normalization and manifest unit tests pass.
- The compiled selected-OCaml compatibility slice passes, including large
  rationals, nearest-even boundaries, normal/subnormal `ldexp`, `ceil`, and
  distinct `Assert_failure` behavior.
- The base-prefix structural/runtime oracle passes.
- The independently derived all-400 source-preparation projection passes all
  17 tests with 364 exact-original and 36 exact-normalized inputs.
- Both exact parser-selection descriptors validate at 20/20 and 400/400.

The next gate is an exact rebuild from the committed runtime and normalization
bytes, followed by a fresh complete DEVELOPMENT / NON-RELEASE run of actions
000--029. Only that cumulative result can establish the 30/30 milestone.
