# Direct Flyspeck boundary 04: ssreflect context term setify

Date: 2026-09-12 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 byte was
changed.

## Actual direct progress and discovery status

The latest completed exact cumulative replay reached action 079 and passed all
79 actions 000--078, so the exact headline is **80 reached / 79 passed**.
The v34 dirty collector attempted all 152 boundary-04 actions and found the
action-126 failure described here only after earlier failures. It is therefore
a compatibility lead, not exact cumulative evidence. The dirty result receipt
has SHA-256
`0e16cb29c73e9720204dd290fc86c53d63b2043213a4060ef8b0079349051c3e`.

## Historical inspection and bounded normalization

Neither Candle `origin/fix-top100` nor `upstream/fix-top100` contains the
Flyspeck source or normalization manifest. The relevant Flyspeck `master`,
`develop`, and Candle-replay refs all identify the same ssreflect source blob,
`0cf045f6a41c8e447d856fd29d41e15e5ca677f4`. Its historical source commits do
not supply a comparator-explicit repair.

The existing action-126 normalization successfully updates the copied tactic
sequencer to Candle's current instantiation protocol. Evaluation then reaches
`get_context_vars` and reports:

```text
Type mismatch between ('a -> 'a -> bool) -> 'a list -> 'a list
and term list -> _
```

The source constructs `tms` exclusively from a goal term and theorem
conclusions; `map frees tms` is therefore a term-list list and its flattening
is a term list. Native Flyspeck uses OCaml structural comparison for the unary
`setify`; Candle's verified library requires the comparator explicitly. The
hash-pinned replacement at source line 115 is:

```text
let f_vars = setify (flat (map frees tms)) in

let f_vars = setify Term.(<) (flat (map frees tms)) in
```

`Term.(<)` is Candle's canonical strict HOL-term order. The existing exhaustive
native/Candle term-constructor oracle establishes the same ordering and
duplicate removal. A new focused fixture reproduces the exact nested
`flat (map frees tms)` source shape and confirms original rejection plus
normalized acceptance and result order. No theorem statement, hypothesis,
proof step, proof intent, definition, goal context, or axiom is changed.

The original source remains 33,828 bytes with SHA-256
`9fefd64395673d3813762b90f0c99e86942a29fd2b80d0725dab3ba15aba9ed9`.
The four-operation normalized output is 33,333 bytes, MD5
`c3dd5eb34cd4d139e3af3199cc633b0d`, and SHA-256
`be790d5251d3b6b4f29259be1aff09cb73877476f92c5c93370f6c54e009a048`.

## Focused validation

- historical branch/blob comparison: PASS;
- exact normalization contract over all 55 unique paths: PASS;
- normalization unit tests: PASS, 18/18;
- focused Candle exact-shape original rejection and normalized acceptance:
  PASS;
- manifest regeneration: PASS, 297 roots, 400 source nodes, 43 generated
  inputs;
- JSON parsing and `git diff --check`: PASS.

The resulting source state has these derived identities:

- normalization contract SHA-256:
  `34dff50590d35bb96f0898935086f7bf0b8cf17b39bfbfd88e73c70b91988233`;
- manifest SHA-256:
  `561040d05764cb1b85e54ffceab20addec22272c6d828946cbebdd7170e11159`;
- generated source-digest/full-build MD5:
  `1425eb8427785c4fee6dae747daf27a1` /
  `35781ea2f948e82899631cc315f251ff`.

## Next cumulative check

This repair is intentionally batched with the already committed action-079
WRG repair for one fresh action-zero boundary-04 replay. Since action 126 was
seen in dirty state, exact credit is forbidden until every predecessor passes
and the nonce-bound action-126 success marker is emitted. The expected nearer
frontier is action 089; its dirty `AJRIPQN` proof failure remains provisional
until reached cleanly.
