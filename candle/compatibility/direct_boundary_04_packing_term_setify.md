# Direct Flyspeck boundary 04: packing term `setify` batch

Date: 2026-09-12 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct progress

The completed v29 exact cumulative run reached 73 actions and passed 72.
Actions 000--071 are exact-green, including this batch's action-070
`EMNWUUS.hl` normalization. It emitted exactly one authenticated preflight
marker and 72 unique nonce-bound success markers equal to the first 72
instrumented-prefix markers. Its immutable DEVELOPMENT / NON-RELEASE failure
receipt has SHA-256
`6634b9ad5fd08c898f8a2b90e5179d1886747f0c2cd6266e45e36ffbbff5a149`.

Action 072, `text_formalization/packing/SLTSTLO.hl`, is the first genuine
failure; action 073 was not reached. The separate action-108 `OXLZLEZ2.hl`
site therefore remains focused/dirty evidence only. Boundary
`03-analysis-through-060` is closed at 61/61, while cumulative boundary 04,
full direct S2, and nonlinear/LP S3 remain open.

## Historical inspection and bounded normalization

The `origin/fix-top100` and `upstream/fix-top100` branches contain neither
source nor normalization for `EMNWUUS.hl` or `OXLZLEZ2.hl`. Relevant historical
direct-Flyspeck worktrees likewise contain no patch for either file. Existing
term-order normalizations and their native/Candle oracle were used only as a
lead and independently reapplied to the exact two source types here.

Both files contain the same helper body. `map frees (tm::tms)` has type
`term list list`; `flat vss` therefore has type `term list`. Native Flyspeck's
unary `setify` sorts and deduplicates this list with OCaml structural
comparison. Candle's verified HOL library makes the comparator an explicit
first argument. The v29 contract supplies `Term.(<)` at exactly these two
hash-bound sites:

```text
let vs = setify (flat vss) in
let vs = setify Term.(<) (flat vss) in
```

The existing independent native/Candle ordering oracle covers every HOL-term
constructor and duplicate removal. A focused exact-shape fixture additionally
reproduces Candle's original type mismatch and verifies that the normalized
form returns the expected ordered, deduplicated `dest_var` list. No theorem,
hypothesis, proof, tactic, geometric definition, proof intent, or axiom is
changed.

The exact source/output identities are:

- `EMNWUUS.hl`: source SHA-256
  `d9945fdd8f34300708c43cb0df4cbd832b02d196696b546650a012d317b7eff4`,
  normalized SHA-256
  `e6a824a3871005daf6b41dd99b4f33820f4fa1d50d3916cb079ccd9a31b29200`;
- `OXLZLEZ2.hl`: source SHA-256
  `8c068facbc067aa2990210e45c9945e7b010d1e150a6b623a59af5199a1a0235`,
  normalized SHA-256
  `09aff5b7b7eb1d7ba78074671b22498d4575048c262d0ee52e2e6d874ebfb261`.

## Focused validation

- focused Candle original rejection and normalized acceptance: PASS;
- existing exact native/Candle term-order and duplicate-removal oracle: PASS;
- normalization unit tests: PASS, 18/18;
- manifest unit tests: PASS, 28/28;
- all-inventory source preparation: PASS, 17/17 over 400/400 sources;
- parser descriptor identities: PASS, pilot 20/20 and all-inventory 400/400;
- normalization overlay materialization: PASS, 52 entries, including the
  pre-existing unselected OCaml-3.10 source;
- manifest generation: PASS, 297 roots, 400 source nodes, 43 generated inputs;
- JSON parsing and `git diff --check`: PASS.

The v29 derived authority identities are:

- normalization contract SHA-256:
  `7aca96ca76ba565ce95b506abd001c0805adfd3e0dbe725507cccdc7a6a074a3`;
- manifest SHA-256:
  `5eaa4d513f6189d9627390660efdcee8454093d8509dd6dedba0f12b4eb5c7f4`;
- pilot descriptor SHA-256:
  `c746375579836693e55a9eb93d1c536061a4243f6f31c5e5630962757cbbe088`;
- all-inventory descriptor SHA-256:
  `4e2398818974735745094fa7268e2ce1f491c507ca429bc5de68e9805373a224`;
- ordered effective/prepared SHA-256:
  `5040e99d8a144e67e740afa6ca036aca139e50fc8a12ce707f9d099c0caaa2f1`
  / `85bdb24cf503bb57d93589d836204e74a629e2ec5fe460ac8d2341ce1cd9be8e`;
- generated source-digest/full-build MD5:
  `015a7828dbaa05c708ff6fa77549ef9c` /
  `f4c2ee31c424e9c98eb73af2beaae1e6`.

## Next exact boundary work

Only a fresh cumulative replay from action zero may credit later batches. The
v29 replay has validated action 070 and exposed action 072. The next isolated
batch supplies the same already-validated comparator at SLTSTLO's third active
copy of this exact helper. The previously prepared action-079 and action-083
batches remain queued after that new predecessor and cannot claim exact action
credit yet.
