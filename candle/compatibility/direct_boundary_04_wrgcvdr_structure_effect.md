# Direct Flyspeck boundary 04: WRGCVDR structure effects

Date: 2026-09-11 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct progress

The latest completed exact cumulative run reached and passed all 61 actions
000--060. It emitted exactly one authenticated preflight marker and 61
nonce-bound ordered success markers, returned from the cumulative prefix with
no error, exception, parse-failure, or failed-load diagnostic, and exited zero.
Its immutable DEVELOPMENT / NON-RELEASE result receipt has SHA-256
`d84ad3c08e228b87cd1dcb7d371224410d2cbed54206684c2e6d34ce4427a331`.
Boundary `03-analysis-through-060` is therefore exact-green at 61/61. Full
direct S2 and nonlinear/LP S3 remain open.

The prior complete dirty boundary-04 diagnostic identifies a separate
compatibility failure at action 079, `text_formalization/local/WRGCVDR.hl`.
It is discovery evidence only and awards no exact cumulative action credit.

## Historical inspection and bounded normalization

Neither `origin/fix-top100` nor `upstream/fix-top100` contains a WRGCVDR
source patch. The relevant historical direct-Flyspeck branches contain no
WRGCVDR normalization. Existing module-structure effect normalizations were
therefore used only as leads, and the exact WRGCVDR construct was reproduced
independently.

Inside module `Wrgcvdr`, the theorem binding `hypermap` is followed by two
bare parser-registration effects. Candle associates the first bare module
structure expression with the theorem-valued item and reports the same
`thm` versus `(string * (int * string) -> unit) -> ...` mismatch recorded by
the dirty boundary run. A focused module-scoped fixture reproduces that exact
class. The v30 contract gives each unchanged effect an explicit wildcard
binding:

```text
parse_as_infix("has_orders",(12,"right"));;
parse_as_infix("cyclic_on",(13,"right"));;

let _ = parse_as_infix("has_orders",(12,"right"));;
let _ = parse_as_infix("cyclic_on",(13,"right"));;
```

Both calls still execute exactly once, at their original positions and in
their original order, with the same names, precedences, associativity,
effects, and exceptions. A native OCaml trace oracle confirms identical
registration order and arguments. The normalized Candle fixture loads and
retains the preceding theorem value. No theorem statement, hypothesis, proof,
definition, proof intent, or axiom is changed.

The exact source/output identities are:

- source SHA-256
  `9d1378418c444f1ec9ce63567cb085fd9def0142ef3a4fb203689e34b9bc636d`,
  MD5 `d7b9d317226c36f2cbea68879c67ea74`, 95,396 bytes;
- normalized SHA-256
  `63ca37dfc173b5170ab660461d7b09ce4037120eec45fb5f8fef030d697bb3c5`,
  MD5 `e5c7bfc4dba1b13cd610eaf51134eb20`, 95,412 bytes.

## Focused validation

- focused native effect/order oracle: PASS;
- focused Candle original rejection and normalized acceptance: PASS;
- normalization unit tests: PASS, 18/18;
- manifest unit tests: PASS, 28/28;
- all-inventory source preparation: PASS, 17/17 over 400/400 sources;
- parser descriptor identities: PASS, pilot 20/20 and all-inventory 400/400;
- normalization overlay materialization: PASS, 53 entries, including the
  pre-existing unselected OCaml-3.10 source;
- manifest fixed point: PASS, 297 roots, 400 source nodes, 43 generated
  inputs;
- JSON parsing and `git diff --check`: PASS.

The v30 derived authority identities are:

- normalization contract SHA-256:
  `e350256e26f75fe7cefdf8c00cff1911ff8cab2ae69180d332d7b4385b6e748c`;
- manifest SHA-256:
  `68247870ca8db8017f5c79f4e1bb8623bb2399e31de8f59d54209ec8ba17a7c8`;
- pilot descriptor SHA-256:
  `ddc7e7d86b6dd85fe2b35d77e5527623bdc6a86531da33d8be0c1430587d0609`;
- all-inventory descriptor SHA-256:
  `2963b6b1d1f0830ea335056238f6a3b39caf35a67a37694475963e783ca34c5f`;
- ordered effective/prepared SHA-256:
  `1c4d439bb1ee67eaa4c5969a540bfe4fe3c10d64e767886cec14003f669dc080`
  / `1664f4c2cd591f3b3b802cc5350845359e4fed5bf82de16a2ea14025607d990b`;
- generated source-digest/full-build MD5:
  `bddbcac710951bab7b35ce75fa2005b8` /
  `b59c121fff1003544598e07d0335b0d3`.

## Next exact boundary work

Only fresh cumulative replays from action zero may credit either pending
batch. With boundary 03 closed, the exact v29 term-`setify` batch must run
through boundary 04; v30 then tests this WRGCVDR normalization on the same
cumulative boundary. The old dirty action-083 failure is a second
module-structure effect at `g(DIH_Y_INEQ_concl)`. A corrected module-scoped
miniature now independently reproduces and eliminates that error, so it is a
validated lead for a later isolated batch rather than an untested change in
v30.
