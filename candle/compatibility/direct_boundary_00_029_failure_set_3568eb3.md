# Direct Flyspeck 00--029 failure-set diagnostic at 3568eb3

The current exact cumulative result remains **3 actions reached / 2 passed**
at `00-base-through-029`.  A separate DEVELOPMENT / NON-RELEASE diagnostic
invoked all 30 actions on the same ordered boundary: 18 completed independently
or were already authenticated, two exposed genuine failures, and ten failed
only because one of those dependencies had not completed.  This diagnostic is
not schema-5/schema-6 evidence and makes no S1, S2, S3, promotion, or release
claim.

Full direct S2 remains open.  Nonlinear and LP/S3 remain open.

## Complete available failure set

Actions 000--004 completed without a diagnostic.  Actions 005 and 006 then
failed at the same module-structure pattern:

```text
005 general/hales_tactic.hl:
ERROR: Undefined variable: REBIND_CONV at line 483

006 general/truong_tactic.hl:
ERROR: Undefined variable: REBIND_CONV at line 430
```

The errors are attributed to the following bare theorem-valued examples inside
each module, rather than to either preceding `REBIND_CONV` definition:

```ocaml
REBIND_CONV (`x:real`,"y") (`pi + (\ x . x + pi) pi`);;
REBIND_RULE (`x:real`,"y")
  (ASSUME (`pi + (\ x . x + pi) pi = &1`));;
```

A minimal Candle reproducer accepts uppercase function bindings and their use
from a later binding, rejects the bare module expression with the same
`Undefined variable: REBIND_CONV` diagnostic, and accepts `let _ = ...` at the
same position.  Thus both genuine failures are one CakeML module-structure
anonymous-expression compatibility class, not a theorem, proof, or
mathematical-semantic failure.

The ten remaining failures are dependency cascades:

- action 007 and 026 require `Hales_tactic`;
- action 014 requires `Hales_tactic.BY`;
- action 015 requires completed `collect_geom.hl`;
- action 021 and 024 require members of `Collect_geom`;
- action 022 requires `Real_ext`;
- action 023 and 027 require `Tactics_jordan`; and
- action 025 requires completed `taylor_atn.hl`.

Actions 008--013, 016--020, and 028--029 completed despite the earlier failures.
Together with 000--004 these are the 18 independently clean actions.  Every
`AFTER` marker was treated only as REPL continuation: it did not override an
error or establish action success.

## Historical inspection and bounded correction

Before editing, `origin/fix-top100`, `origin/pft`, `origin/ptr-eq`,
`origin/merge/jrh13-master-20260825`, and the pinned Flyspeck origin/upstream
branches were inspected.  The Candle branches have no direct Flyspeck patch,
and every inspected Flyspeck branch retains the same two bare examples in both
modules.  They therefore supplied no source correction to adopt.

The normalization contract adds exactly four replacements: each bare
`REBIND_CONV` or `REBIND_RULE` example becomes `let _ =` followed by the
identical expression.  OCaml evaluates both forms once in the same module
initialization position and discards the returned theorem.  The replacements
preserve evaluation order, effects, exceptions, theorem construction, and all
subsequent bindings.  No theorem statement, hypothesis, proof body, or allowed
axiom changes.

Focused validation after the correction passed:

- the exact Candle negative fixture reproduced `Undefined variable:
  REBIND_CONV` for the original form;
- the wildcard form compiled and exported its later module bindings;
- the native OCaml original/wildcard effect-and-order projections matched;
- the combined normalized compatibility gate passed with exactly its five
  intended negative diagnostics and no unexpected error; and
- the normalization contract unit suite passed 17/17.

The passing focused Candle log is
`/tmp/candle-flyspeck-base-prefix-api.zF94b7/candle.log`, SHA-256
`8eb4d3005c5afa300a5b8b4907ac92b4fcd49829085d26c8e926738ae008aae8`.
The native oracle log SHA-256 is
`ceda2490bf679734f27b0071d33fa668ba910211fcc9f56266dfb4edae54c382`.

## Preserved diagnostic

The frozen run is
`/project/flyspeck-candle-runs/v16-dirty-all-actions-00-029-3568eb3-run-004`.
Its log SHA-256 is
`4a53d4be92e31ae544ec8ccf4c79ea3f06f4b974a256760fbb34cfc98fc7a00e`,
its timing SHA-256 is
`7649fc5062abf216564847c30bb89956f793edcb9ce813f92f1d2f1c1527f580`,
and its result-receipt SHA-256 is
`c582ce0d32349c2b1d3afc723ad2a3d114d9cd20adb46c38cc2d7a1869d2cbb1`.
It used 41:28.68 wall time, one CPU, and 4,344,704 KiB maximum RSS.

The next gate is a fresh complete 00--029 development replay on committed
bytes.  Only its exact cumulative action markers may advance the official
3/2 progress metric.
