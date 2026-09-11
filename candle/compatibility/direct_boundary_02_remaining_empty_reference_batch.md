# Direct Flyspeck boundary 02: remaining empty-reference batch

Date: 2026-09-11 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct progress

The latest completed exact cumulative run reached 43 actions and passed 42.
Actions `000--041` are the exact green prefix. Consequently
`00-base-through-029` is 30/30 direct green and the cumulative arithmetic
boundary through action 037 is 38/38 green. Boundary
`02-nonlinear_support-through-049` remains open. Full direct S2 remains open;
nonlinear and LP/S3 remain open.

The exact v20 `000--049` run is still in progress on unchanged committed
Candle and normalized-source bytes. This v21 batch does not alter that run and
does not claim that either newly audited site has yet been reached by exact
cumulative execution.

## Bounded empty-reference audit

The v19 exact failure at `ineqdoc = ref []` justified one bounded scan for the
same CakeML immediate value-restriction class, rather than waiting to repair
the same class one binding at a time. Among the current nonlinear boundary
sources it found two additional top-level empty mutable lists:

- `nonlinear/ineq.hl` line 1833, `dart_classes = ref []`; and
- `nonlinear/parse_ineq.hl` line 151, `autogen = ref[]`.

Every selected use uniquely fixes the first value to `thm list`: `define_dart`
conses the result of `new_definition`, and selected consumers use the list as
rewrite theorems. Every selected use uniquely fixes the second value to
`term list`: `prep_autogen` produces terms and all updates, mappings, code
formatters, and dereferences consume those terms. Neither reference has a
second selected element type.

`fix-top100`, PFT, and Flyspeck `upstream/native`, `upstream/develop`, and
`upstream/master` retain the unannotated spellings and contain no correction
for Candle. They were inspected as leads only and supplied no adopted patch.

## Narrow compatibility normalization

The exact hash-pinned replacements are:

```ocaml
let dart_classes = ref ([]:thm list);;
let autogen = ref ([]:term list);;
```

Each annotation states the single type already forced by the original
program. The initial value remains the same empty list, subsequent mutation
and dereference behavior is unchanged, and no expression is moved or
suppressed. No inequality, theorem statement, hypothesis, proof body, proof
intent, tag, or allowed axiom changes.

The resulting effective identities are:

- `nonlinear/ineq.hl`: 122,226 bytes, SHA-256
  `16c59317378370832e0847be809b568edd65d35045f3ed7f1a74127e3509aff8`,
  MD5 `5b359b87557684fe9fa91cbd938e26fb`;
- `nonlinear/parse_ineq.hl`: 21,876 bytes, SHA-256
  `ab9a224653fca378093a366ee93b2c47a923ee92eeb0134a63d5fd38982400d0`,
  MD5 `8e7bcdecdd536e618a1c3e9224d07d40`.

Original Flyspeck source remains byte-identical at commit
`1ce0353008eba83d3c76ae9a25c3c242e4802d53`.

## Focused validation

- Dedicated CakeML fixtures reject each original empty reference with
  `Value restriction violated` and accept each typed form with the expected
  list content.
- The native OCaml oracle shows the original and annotated forms returning,
  mutating, and retaining the same values.
- Normalization and manifest unit tests: 46/46 pass.
- Independent all-400 effective-source preparation tests: 17/17 pass.
- Combined normalization/manifest/source-preparation set: 63/63 pass.
- Parser descriptor fixed points: pilot 20/20 and all-inventory 400/400 pass.
- Manifest fixed point: 297 roots, 400 source nodes, and 43 generated inputs
  passes.
- Exact source profile remains 355 original plus 45 normalized; the quotation
  inventory remains 318,813.
- Ordered effective root:
  `c6e90861ebb0a4bf6d020ff709dee0fc2deda54f07011c92d1bbbab6b9e1be96`.
- Ordered prepared root:
  `0f69e5b62e0ff6ee891f4a780544e55666500e6ed3b4894f607b09fc4d6c7378`.
- Normalization contract SHA-256:
  `31256c56b142aabc97ec968f113b78a1506e4353e65a07de3009b058ffb1b3f3`.
- Manifest SHA-256:
  `076b47dd5414787dc7ba4e5852b71655db1066d4f771e7bc874148c72f48b06c`.
- Pilot/all-inventory descriptor SHA-256 values are
  `45f08bf95a0d0d7575e01c0cfa58fb56ac8702e76c37c74764940eae3d72870c`
  and
  `56d0082b344b02737422c4df7ef7175233793d73d5e8618ffefb37d8719ea381`.
- Generated source-digest/full-build program MD5 values are
  `48233b4aae6635e305f5e82657de4b31` and
  `86c4898fefc58d355a69a20514870550`.
- JSON parsing and `git diff --check`: pass.

The next exact action credit must come from a fresh cumulative run on the
committed v21 bytes. The active v20 run is preserved first so its genuine
earliest outcome can be recorded without reinterpretation.
