# Direct Flyspeck boundary 03: analysis structure-effect batch

Status: DEVELOPMENT / NON-RELEASE. This report assigns no S1, S2, S3,
qualification, promotion, or release credit.

## Functional lead

The last completed exact cumulative run reached 43 actions and passed 42,
with the exact green prefix ending at action 041. The fresh v21 cumulative
run through action 049 is in progress on the preceding committed nonlinear
empty-reference batch. Boundary 03 (actions 050--060) remains open.

The completed separate-phrase diagnostic attempted all 61 actions through
060. It found four independent compatibility failures and eight dependency
cascades. The v21 batch addresses the action-042 and action-046 failures. The
remaining two observed failures are:

- action 050, `text_formalization/volume/vol1.hl`: anonymous theorem-valued
  module phrases at original lines 1168--1169;
- action 051, `text_formalization/hypermap/hypermap.hl`: anonymous numeric
  priority and parser-registration module phrases at original lines 21--27.

The same unit-valued module-structure class is present later in the available
boundary at action 053 (`fan/fan.hl`) and action 060
(`fan/polyhedron.hl`). Those later files could not receive action credit in
the dirty probe because their prerequisites had failed. They are included
proactively in this coherent batch, subject to the exact cumulative gate.

## Historical inspection

Before implementing the repair, the source and construct were searched in
`fix-top100`, the PFT development history, current historical Candle
worktrees, and the pinned/upstream Flyspeck branches. They retain the original
anonymous spellings and contain no patch for these four sources. Earlier
independently validated Candle/Flyspeck compatibility work supplied only the
general lead that an explicit wildcard binding is the faithful CakeML
module-structure representation; that lead was revalidated here with new
fixtures.

## Exact normalization

The pinned Flyspeck checkout remains unchanged at
`1ce0353008eba83d3c76ae9a25c3c242e4802d53`. The versioned normalization
contract adds four hash-bound entries and 23 exact source-line rewrites:

- `vol1.hl`: bind `REAL_LE_SQUARE_ABS` and `REAL_ABS_REFL` to `_`;
- `hypermap.hl`: bind `prioritize_num()` and all three existing
  `parse_as_infix` calls to `_`;
- `fan.hl`: bind all eight mechanically enumerated invariant registrations
  and the existing `POWER` infix registration to `_`;
- `polyhedron.hl`: bind all eight mechanically enumerated invariant
  registrations to `_`.

Every expression, argument, theorem value, parser precedence, associativity,
and source ordering is unchanged. Each computation is still evaluated once;
only its otherwise discarded result is named by the wildcard pattern. No
definition, theorem statement, hypothesis, proof tactic, proof intent, or
axiom is replaced.

The normalized output identities are:

- `vol1.hl`: SHA-256
  `48caae47ee5c442fff61c3a5fcd7ad2ffc73550dd133d634749827ee477ea6e0`;
- `hypermap.hl`: SHA-256
  `7abdc628daa5447393f66038aa8634604f6d88ac462082a85c9f6b046ef29df7`;
- `fan.hl`: SHA-256
  `916b8e4aa69fae8f4553ccbf11e1870c6ab2f3ba2e2ea28977cd57aad34b7670`;
- `polyhedron.hl`: SHA-256
  `4d72e360c3ce7cece81ba935db13fd12bc83f74288e790f12a88826f5f619697`.

## Focused validation

New original fixtures reproduce Candle's rejection of both anonymous
theorem-valued and anonymous unit-valued module phrases. The normalized
fixture loads in Candle, retains following module exports, and observes the
exact evaluation order. A native OCaml oracle independently compares the
original and wildcard forms and obtains identical effect/order projections.

Focused results so far:

- analysis structure-effect Candle/native oracle: PASS;
- normalization contract application to all pinned entries: PASS (49/49);
- focused normalization/manifest/all-inventory unit tests: PASS (63/63);
- materialized hashes of the four new outputs: exact matches.
- exact effective-byte parser/inference probes for actions 050, 051, 053,
  and 060: no parse failure and no theorem/unit structure mismatch (the
  expected isolated undefined-prerequisite diagnostics remain non-crediting);
- generated manifest fixed point: PASS (297 roots, 400 source nodes, 43
  generated inputs);
- parser descriptor identity checks: PASS (20/20 and 400/400);
- independent source-only preparation: PASS (400/400, 351 exact-original and
  49 exact-normalized).

The v22 authority identities are:

- normalization contract SHA-256:
  `2e7a1091202662dd4f02e407a8eef4e9ea049d0070c4fd5c306a377eaea7d3c0`;
- manifest SHA-256:
  `fe3f38ce987898d4cde8cb9f667dedde8ac1544031c357c1c9c81a48229cd49c`;
- pilot descriptor SHA-256:
  `66dd347da6864fce6dd13291fa50b244fc6f720d09443221cf9d91d29df97879`;
- all-inventory descriptor SHA-256:
  `1a1bded1fd97ccb518c67a0e40da89a441f43543e2dc2787b83f5499b69e4895`;
- ordered effective/prepared SHA-256:
  `8468fe4f20f724008ae7e87119b922efab348daa87d07546743eb03c2044ab4e`
  / `1e4cfc2a2478c2fe80be7d69336192a81d1f5017a2e4f5c8728c518efaff3a1f`.

The exact cumulative direct run remains the functional gate. Only that run
can advance action or boundary credit.
