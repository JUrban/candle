# Direct Flyspeck boundary 02: `parse_ineq` runtime batch

Date: 2026-09-11 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct progress

The latest completed exact cumulative run reached 47 actions and passed 46:
actions `000--045` are the exact green prefix and action 046,
`text_formalization/nonlinear/parse_ineq.hl`, failed. Thus
`00-base-through-029` remains 30/30 green and the cumulative boundary through
action 037 remains 38/38 green. Boundary
`02-nonlinear_support-through-049` is still open pending a fresh exact run.
Full direct S2 is open; nonlinear and LP/S3 are open.

In a persistent development process containing the exact successful
actions `000--045`, the normalized whole-file candidate for action 046 now
loads to `Finished loading`. This is a faithful development result, not new
exact action credit. Its source is byte-identical to the output of the
versioned normalization contract at SHA-256
`9513a040c6b25b4361ab212e292e373e3b3189cf6a5e72ef428ce02a3397079a`.

## Bounded diagnosis

Before changing the contract, `fix-top100`, the relevant historical direct
Candle branches, and the corresponding pinned Flyspeck source were searched
for this source and these constructs. They retained the original spellings.
The earlier structure-effect and value-restriction branches supplied useful
leads, but every transformation below was minimized and independently tested
against the actual action-046 state.

The live-state sequence exposed six exact runtime-language incompatibilities:

1. the bare `autogen := ...` module initializer was absorbed into the prior
   function after Candle's internal structure-phrase separator erasure;
2. after binding it explicitly, the analogous bare `macros := ...`
   initializer failed for the same reason;
3. OCaml's polymorphic `max` specialized to doubles in `geteps`, while
   Candle's selected `max` is integer-only;
4. the private `counter` closure retained an unused polymorphic argument and
   violated CakeML's value restriction when returned in a pair;
5. CakeML does not expose OCaml's `Match_failure` exception constructor to
   this source; and
6. the bare `output_filestring sphere_ml ocaml_code` initializer was absorbed
   into the preceding string binding.

Grouping dereferences, explicit reference types, explicit function types,
and `List.append` substitutions were separately falsified and are not part of
the contract.

## Narrow compatibility normalization

The hash-bound `PROJECT-PARSE-INEQ-S3-CANDLE-COMPATIBILITY-001` entry adds six
exact operations:

- give the `autogen`, `macros`, and Sphere_math output initializers explicit
  wildcard structure bindings;
- spell the maximum over the selected strictly-positive finite `Eps`
  literals and zero default with CakeML's primitive binary64 `>`;
- restrict `counter` to `unit`, the argument at every selected call; and
- replace the exception-driven `acs` list destructuring with the same
  singleton/empty/other arity split as an explicit match.

Each initializer is still evaluated once in the same order, with its result
discarded and its effects and exceptions preserved. The selected `Eps`
inventory contains only `1.0e-8` and `1.0e-12`, so the replacement returns the
same numeric maximum as OCaml `max`; equal inputs have identical binary64
values. The explicit arity match returns the same strings and raises the same
`Failure "ocaml:acs"` for every other list length. No HOL term conversion,
inequality, theorem, statement, hypothesis, tactic, proof intent, or axiom is
changed.

## Focused validation

- exact action-046 live-state candidate through `Finished loading`: PASS;
- independent native OCaml equivalence oracle: PASS;
- focused Candle runtime fixture for maximum, counter, arity, and initializer
  behavior: PASS;
- nonlinear boundary compatibility gate: PASS;
- normalization contract application: PASS, 49/49 entries;
- normalization unit tests: PASS, 18/18;
- manifest tests: PASS, 28/28;
- all-inventory source preparation: PASS, 17/17 over 400/400 sources;
- parser descriptor checks: PASS, pilot 20/20 and all-inventory 400/400;
- manifest fixed point: PASS, 297 roots, 400 source nodes, 43 generated
  inputs;
- JSON parsing and `git diff --check`: PASS.

The complete parser-controller assurance suite was intentionally not run in
the edit loop: several tests reconstruct the 400-source plan repeatedly and
belong at an integration boundary. The source-only 400-source preparation
gate and both descriptor checks were run instead.

Current derived authority identities are:

- normalization contract SHA-256:
  `b001233045c2351d4fb2c0b6e6694363b74b945368530ad0e6fec37bcdc2c4b9`;
- manifest SHA-256:
  `084b358c81d311d9c0cfc5c47f5d9e194d92e872ad69d559db384964ecb35abf`;
- pilot descriptor SHA-256:
  `a1699d1b07f0d05dfa4ef31d3f23201c7c3808b2314a8c89e532795ebb4b7782`;
- all-inventory descriptor SHA-256:
  `6e0b993096673defd55d05194a4be782854edd6cb9e37d6da8c73f941348139b`;
- ordered effective/prepared SHA-256:
  `a30e4ebf3f65d4e5ff67025ee0cfb5ca1591eb563c9e5a95464a85b12d444c81`
  / `69481904b36004d8d11a8ef787cd1bf5490286bf963f44d0d61fdc69a73142c8`;
- generated source-digest/full-build MD5:
  `6a272b66dc20fa16f034275574af7cfb` /
  `7b930279fe7f8eacb4b69fa53c697644`.

The next action credit must come from a fresh exact cumulative run through
action 049 on the committed bytes.
