# Direct Flyspeck boundary 02: first nonlinear failure and tuple fix

Status: DEVELOPMENT / NON-RELEASE. This note makes no S1, S2, S3,
qualification, promotion, or release claim.

## Actual direct progress

The exact cumulative `02-nonlinear_support-through-049` attempt at Candle
`3ed0e79a6bb70185d16c775c67d5e8b44c175770` reached 39 actions and passed
38. Actions 000--037 emitted the exact ordered nonce-bound success markers.
Action 038 reached
`text_formalization/nonlinear/calc_derivative.hl` and failed before its
success marker with:

```text
ERROR: Type mismatch between string -> string and string * hol_type -> _18 at line 1215

  let differentiate =
  ^^^^^^^^^^^^^^^^^^^^
```

The immutable attempt is
`/project/flyspeck-candle-runs/v16-dev-direct-boundary02-3ed0e79-attempt-001`.
Its log SHA-256 is
`4ec5d3689e049a44f46c6807e14560c098c68a967ea42ac271c2129f29899f4b`;
its result receipt SHA-256 is
`10fadfad4d606187dd01c181fc3ce152fa9b9281f1883b802d2061293ab8c9b9`.
The run used the unchanged checked non-promotable interpreter
`dd8a693bc88b75b5599a91777b93629417993cdb5338bb7cb0f40d38d246190f`,
exited zero at REPL EOF after the typed error, took 48:18.84, and had a
4,332,160 KiB maximum RSS. No formal boundary postlude was present in this
manual development harness.

## Classification and historical review

The failing expression generated a fresh variable as
`mk_var("F"^(string_of_int !c),real_ty)`. The pinned runtime reports the same
CakeML inference failure on a standalone minimized constructor/function
fixture. Splitting only the pure generated name before passing the identical
pair to `mk_var` makes that fixture typecheck and evaluate in Candle. Native
OCaml accepts both spellings and returns the same ordered `F1` and `F2` terms
with the same counter state.

Before adopting the change, the exact source and construct were searched in
Candle `fix-top100`, `pft`, master, and the relevant Flyspeck/Candle replay
branches. Candle's historical compatibility branches contain no copy or fix
of this Flyspeck source. Flyspeck master and `codex/candle-replay` retain the
same 2011 spelling. The historical search therefore supplied no patch to
trust; the normalization was minimized and validated independently. The same
narrow inference class was already independently demonstrated at the pinned
`parser_verbose.hl` and `hash_term.hl` tuple-constructor sites.

The new hash-bound overlay operation changes only:

```ocaml
mk_var("F"^(string_of_int !c),real_ty)
```

to:

```ocaml
let name = "F"^(string_of_int !c) in
mk_var(name,real_ty)
```

It changes no theorem statement, hypothesis, proof operation, derivative
rule, proof intent, or allowed axiom. The original Flyspeck checkout remains
unchanged.

## Focused validation

- normalization unit tests: 17/17 pass;
- manifest plus normalization contract tests: 45/45 pass;
- exact minimized native/Candle rejection-and-acceptance oracle: pass;
- all-inventory prepared-source tests: 17/17 pass, with 400 inputs partitioned
  into 361 exact originals and 39 exact normalized sources;
- parser descriptor regeneration/check: 20/20 pilot and 400/400 inventory;
- manifest byte regeneration/check: 297 roots, 400 sources, 43 generated
  inputs;
- normalization byte regeneration/check: 39/39 entries;
- JSON and `git diff --check`: pass.

The broader stratum-runtime unit file ran 46/47; its sole failure is the
host-Python runtime-identity snapshot check and reproduces unchanged on the
parent `3ed0e79` worktree. It is therefore recorded as a pre-existing
environmental diagnostic gate, not attributed to this normalization and not
expanded in this functional edit loop.

## Next direct step

After committing these exact bytes, materialize a fresh 39-output overlay and
400-source plan. Run one DEVELOPMENT / NON-RELEASE persistent dirty
continuation over actions 000--049 as separate REPL phrases. That run is
needed to distinguish the complete available action-039--049 failure set from
dependency cascades without paying for twelve independent base boots. Batch
the resulting shared root causes, then rerun the exact cumulative boundary.

Headline status until that runtime continuation returns: 39 actions reached,
38 passed; boundary 02 is open; one confirmed tuple-constructor compatibility
class is fixed in source-contract tests but not yet credited as a direct
action pass; full direct S2 and nonlinear/LP S3 remain open.
