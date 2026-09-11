# Direct Flyspeck boundary 02: Ineq structure effects

Status: DEVELOPMENT / NON-RELEASE. This note makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct progress

The latest exact cumulative `000--049` run reached 43 actions and passed 42.
Actions `000--041` are the exact green prefix (42/42). Action 042,
`text_formalization/nonlinear/ineq.hl`, is the first current direct Flyspeck
blocker. Boundary `02-nonlinear_support-through-049` remains open; full direct
S2 remains open; nonlinear and LP/S3 remain open.

The immutable predecessor receipt is
`/project/flyspeck-candle-runs/v18-dev-direct-boundary02-8cee94e-attempt-001/development-result-receipt.json`
(SHA-256
`aa0be9ecbdba2d0af5478cff65d11ccbb53ceaabbc873bb0118cbf9efb22cfbb`).
That exact run used Candle commit
`8cee94e20fe747a3324c8bb105d4176270fc639a`, ran for 53:58, and had a
4.34-GiB maximum RSS. Its transactional diagnostic attributed rollback to the
opening `module Ineq = struct`; the bounded reproducer below localized the
actual parser incompatibility inside that structure.

## Bounded diagnosis

The faithful reproducer expands the exact source through the authenticated
`flyspeck_loader_quotation.py` path and submits it to the real linked Candle
REPL. Prefix bisection showed that the module parses through original line 121
and first fails when the anonymous structure phrase beginning at line 125
applies `add` to an inequality record.

A raw parser-only experiment was rejected as an isolator because it also
rejects otherwise valid top-level modules. Inspection of `fix-top100`, PFT,
and relevant historical Candle branches found no existing correction for this
construct. Flyspeck's native branch removes the entire `Ineq` wrapper, but
that relies on native OCaml file-module behavior while downstream direct
sources use `Ineq.*` and `open Ineq`; it is therefore a lead that cannot be
faithfully adopted in Candle.

The independently minimized compatibility spelling is the already validated
OCaml equivalence

```ocaml
effectful_expression;;
```

to

```ocaml
let _ = effectful_expression;;
```

inside a module structure. The wildcard binding evaluates the identical
expression once, at the same initialization position, and discards the same
result. It does not move, synthesize, or suppress any effect or exception.

## Exact correction

`PROJECT-INEQ-S3-STRUCTURE-EFFECTS-001` mechanically enumerates all 218
anonymous structure phrases in this one `Ineq` module: 189 `add` registrations,
18 `addtex` registrations, eight `skip` registrations, and three loop/other
effect phrases. Each whole physical source line is separately recorded and
checked before any mutation. The normalizer rejects missing, changed,
duplicated, or reordered anchors and verifies the complete source and output
SHA-256/MD5/byte-count identities.

The pinned original remains unchanged at SHA-256
`d1160305349bbe0af190e78e178169f5b9165fbc7b5e9f83156094b1afeb2c68`.
The normalized result is 122,178 bytes, SHA-256
`e2d3be55e7a23c2335e974eba5b90a523f479eb660f034dbc1c447c8a0dd1f90`,
and MD5 `3dc965c4ebc926ed30a466f220118f33`.

No inequality term, theorem statement, hypothesis, proof step, proof intent,
tag, or allowed axiom changes. The existing `Ineq` namespace is retained.

## Validation before cumulative execution

- A dynamic whole-file probe applied all 218 exact bindings, expanded the
  exact quotations, and submitted the materialized `ineq.hl` to real Candle;
  the structure parser failure disappeared. The only isolated-probe error was
  the expected absent earlier `Sphere` dependency.
- Native OCaml and focused Candle fixtures prove effect-order equivalence,
  show Candle rejecting the original anonymous structure-record form, and
  show Candle accepting the normalized form.
- Normalizer, manifest, and all-inventory tests pass 63/63.
- The exact manifest fixed-point check passes with 297 roots, 400 source nodes,
  and 43 generated inputs.
- Parser diagnostic selections pass at 20/20 pilot nodes and 400/400 inventory
  nodes.
- The prepared 400-source profile remains 355 original plus 45 normalized
  sources; quotation expansion is unchanged at 318,813 actions.
- JSON parsing, `git diff --check`, and the focused nonlinear boundary oracle
  pass.

The broader stratum-runtime unit file passes 56/57 tests. Its sole error also
occurs unchanged on the clean parent: the host `/usr/bin/python3.12` was
rebuilt on 2026-08-31 while that assurance test pins the former 2026-06-19
executable identity. This environmental runtime-pin drift is unrelated to the
normalization and is not expanded into assurance work in the functional edit
loop.

## Next direct step

Commit these exact bytes, materialize an exact-head normalized overlay and
stratum plan, and rerun cumulative actions `000--049`. Only that run may credit
action 042 or expose the next genuine direct Candle/Flyspeck failure.

Headline status: 43 reached / 42 passed; exact cumulative prefix 42/42;
boundary 02 open; one currently observed compatibility class (anonymous
effect phrases in `Ineq`) corrected but awaiting exact cumulative validation;
full direct S2 open; nonlinear and LP/S3 open.
