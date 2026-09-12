# Direct Flyspeck boundary 04: v39 Marchal3 inverse rewrite

Date: 2026-09-12 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct action progress

The exact cumulative frontier remains 92 actions reached and 91 passed at
boundary 04 (`00-base-through-151`): actions 000--090 are exact-green, and
action 091 is `packing/marchal3.hl`. The first 30-action boundary is therefore
already 30/30 exact-green. Full direct S2 and nonlinear/LP S3 remain open.

The completed v37 run preserved the original action-091 failure at zero-based
refinement step 23, upstream lines 3872--3873, with
`Failure "solve_goal: Too deep"`. Its failure receipt SHA-256 is
`1b4b927b8e523aead3f866678632c274cc8b8362db369cd366fcd46628cf6506`.

The v38 exact replay independently passed actions 000--090 and traversed the
six deterministic set-substitution replacements that removed that original
failure. It then entered the final `PERMUTES_INVERSE_EQ` MESON proof at lines
4127--4128 and grew through 181,964,983 search nodes without an action-091
success marker. It was intentionally interrupted after 2:13:05, with one
`EXCEPTION: Interrupt`, exit status 0 under development REPL behavior, and
maximum RSS 4,478,208 KiB. Its frozen `candle.log` SHA-256 is
`2aa02624fe1436f27712e1d702c9e77e1eba19a9c1e5731d33c5bb08a7b4a1cc`;
the bounded-interruption note is stored beside that log.

## Localization and historical leads

A theorem-only trace first reproduced the original step-23 failure. After the
six replacements, a fresh exact run and a retained focused run both produced
the same distinctive later MESON growth sequence. A step-start wrapper then
finished opening the theorem's exact lexical module context but did not enter
step 0: Cake eagerly constructs the refinement tactic list, and construction
of the final theorem-specific MESON tactic is itself the runaway boundary.
This agrees with the only remaining nontrivial supplied-theorem MESON at the
end of `LEFT_ACTION_LIST_3_EXISTS`, lines 4127--4128.

As recorded by the preceding v38 batch, neither `origin/fix-top100` nor
`upstream/fix-top100` contains Marchal3 or a patch for this proof, relevant
historical Candle branches contain no Marchal3 normalization, and Flyspeck
history retains the original construct. Those searches were leads only; the
failure and replacement were reproduced and validated independently.

## Narrow proof-preserving repair

At the unchanged final intermediate goal,

```text
inverse p 0 = i1 /\ inverse p 3 = i4 /\
inverse p 1 = i2 /\ inverse p 2 = i3
```

the context retains `p permutes 0..3` and the already-proved conjunction
`p i1 = 0 /\ p i2 = 1 /\ p i3 = 2 /\ p i4 = 3`. The original broad search

```text
UP_ASM_TAC THEN MESON_TAC[PERMUTES_INVERSE_EQ; ASSUME image_equalities]
```

is replaced by

```text
REWRITE_TAC[MATCH_MP PERMUTES_INVERSE_EQ
  (ASSUME `p permutes 0..3`)] THEN ASM_REWRITE_TAC[]
```

`MATCH_MP` instantiates the existing permutation theorem, its four rewrites
turn the inverse equalities directly into the four retained image equalities,
and `ASM_REWRITE_TAC` closes the identical conjunction. No theorem statement,
hypothesis, intermediate goal, definition, axiom, or proof intent changes;
no global search limit is raised.

The upstream source remains SHA-256
`191528d2c1dc3542751507d2b44880f3b4f07efe00ea9267b66bc10e28d21926`,
MD5 `ad1052eeb7d9979e8fd3069d2eb4a35c`, 254,482 bytes. The v39 normalized
source is SHA-256
`82857d6a9db661dc0cb9a4123c84eb4b51d6686bf17711fe90d2e6433a5a679d`,
MD5 `5d5478849ff5a78548d457710143537d`, 254,766 bytes. Its seven exact
hash-bound operations are the six v38 set substitutions plus this one inverse
rewrite.

## Validation and frozen identities

- standalone Candle fixture for all six polymorphic set equalities and the
  exact four-conjunct inverse rewrite: PASS;
- normalization contract check: PASS, 58 entries and 232 unique operations;
- normalization tests: PASS, 18/18;
- manifest tests: PASS, 28/28 (46/46 combined);
- manifest write/check fixed point: PASS, 297 roots, 400 source nodes, 43
  generated inputs;
- JSON parse, shell syntax, and `git diff --check`: PASS.

The frozen implementation commit is
`e5e307f489730363efc00b1299af76e91fc18704`. Derived identities are:

- normalization contract SHA-256:
  `f23aefc881a471b9c2daa7f149f185d550d7bd28622a2f66b9f50aede41635f5`;
- manifest SHA-256:
  `c711ee9b205f3756ded6eb03bd362dcfeca1e67ae8844e6386af6a39ce9f43c0`;
- loader SHA-256:
  `1c7103085a42ded4c931c55661159741c7a4e2f7a7de96ae9f041f41d25d2dec`;
- generated source-digest/full-build MD5:
  `8fe9a78b735356314017be0aac7af4b2` /
  `6ebecb4ab241b30438448b5a4df1f04b`.

## Next work

Materialize a fresh overlay from these committed contract bytes, generate the
boundary-04 plan from the final report head, and launch a fresh exact
DEVELOPMENT / NON-RELEASE cumulative replay. Action 091 receives no pass credit
until normalized `marchal3.hl` completes in that replay. If it passes, continue
through actions 092--101 and validate the already localized action-102
`YSSKQOY.hl` name-resolution candidate against the first complete available
failure set.
