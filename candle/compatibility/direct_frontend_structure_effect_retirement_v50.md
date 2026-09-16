# Direct frontend normalization retirement (v50)

Status: DEVELOPMENT / NON-RELEASE.  A corrected-runtime cumulative replay is
still required before this batch can replace the v49 execution authority.

## Scope

This branch starts from Candle `1109fdfcf3c754e80d3e14bce6cb0caad6977bb9`
and uses the corrected CakeML frontend at
`cc36ecadde2d13d377e26ccb9610a450c477f737`.  The frontend preserves `T_semis`
inside `struct` and `sig`, so a nested-module `;;` separates structure items
rather than terminating a top-level REPL phrase.  Its existing central OCaml
`for` lowering also accepts the four loops that had been rewritten in the
Flyspeck overlay.

The normalization contract is reduced from 80 entries / 274 operations to 47
entries / 167 operations.  The selected loader table is reduced from 79 to 46
entries because the OCaml-3.10 database output remains deliberately
unselected.  The retired inventory comprises:

- 896 source sites whose only change was an explicit discarded-result
  binding, including exact and line-batch operations;
- four source-level loop rewrites now handled by central `for` lowering; and
- the two-operation GRUTOTI source-scope shim.

Thirty-one overlay entries disappear completely; thirteen mixed entries keep
their unrelated compatibility operations.  No Flyspeck source file is edited.
Every remaining input and normalized output retains exact source and result
hashes, and loader selection remains by exact authenticated original path.

## GRUTOTI classification

GRUTOTI was not a polymorphic-comparison or generic MESON-order failure.
Candle's formerly transitive module opens exposed
`Trigonometry2.SET_TAC`/`SET_RULE` where native HOL Light selected its standard
bindings.  The custom tactic introduced the supplied subset theorem after the
relevant set rewriting, leaving `SUBSET` unprocessed and causing runaway
search.  Restoring the intended bindings completed the full file in about
11 minutes 51 seconds, and all 2,364 MESON progress records matched native
output byte-for-byte.  The removed local shim is therefore replaced only by
the already-corrected central `open` export semantics; raw GRUTOTI remains a
required cumulative replay gate.

## Gates

At contract hash
`396e82a76d740b6ac86945870e472103e80ad6cdd7d92e67920695d68d044213`:

- the 47-entry overlay materializes and validates against frozen Flyspeck
  `1ce0353008eba83d3c76ae9a25c3c242e4802d53`;
- the identity scan reports 47 files and zero executable physical operators;
- all 48 normalization/manifest/identity unit tests pass;
- manifest generation and an independent fixed-point check report 297 roots,
  400 source nodes, and 43 generated inputs; and
- the compiled raw/wrapped nested-module and `for` differential gate passes;
- the focused base-prefix integration gate loads raw `refinement.hl`,
  `goal_printer.hl`, and `tactics.hl` successfully while retaining its four
  unrelated negative controls.

The fresh cumulative corrected-runtime replay is recorded separately when
complete.  Until it passes
through every affected source, v49 remains the direct-run authority and this
branch advances no S2/S3 or release claim.

## First post-152 boundary

The fresh v49 cumulative run completed actions 000--152.  This validates the
24 exact outer-loop bindings in normalized `arith_num.hl` from a clean action-0
predecessor and raises the functional high-water mark to 153 completed
actions.  Action 153 then failed in normalized
`formal_lp/glpk/glpk_link.ml` because unqualified `find_all` was absent after
`open List`.

The historical `fix-top100` branch contains no fix for this site.  Pinned OCaml
exposes `List.find_all` as the same operation as `List.filter`; Candle already
had the latter.  The bounded correction adds only
`let find_all f l = filter f l` to the compatibility `List`.  The GLPK gate
checks the unqualified lookup under `open List`, selected values `[2;4]`, and
left-to-right predicate visits `[1;2;3;4]` against native OCaml.  It passes on
the corrected runtime/source view.  Actual action-153 credit remains pending a
fresh clean cumulative replay.
