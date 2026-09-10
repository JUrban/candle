# Direct Flyspeck `lib.hl` compatibility batch from cf97a2cd5

The current exact cumulative boundary result remains **2 actions reached / 1
passed** at `00-base-through-029`: action 000 passed and action 001 reached
authenticated `general/lib.hl`. The completed boundary attempt at
`cf97a2cd530954b9cd8d17e6bae96304b570c6d2` passed the prior `rev` binding and
then stopped at `let length =`. This DEVELOPMENT / NON-RELEASE batch closes the
complete failure set exposed by a faithful whole-`lib.hl` probe. It does not
claim action 001, the 30-action boundary, S2, S3, promotion, or release success.

## Historical leads and minimized fixes

Before changing each class, the `origin/fix-top100`, `origin/pft`,
`origin/ptr-eq`, `origin/merge/jrh13-master-20260825`, and current Candle
histories were inspected. They retain the same expansive Patricia-tree helper
constructs, so they supplied no direct pair-splitting fix. Candle's current
`lib.ml` did supply two useful leads: its `rev` and `length` have outer
parameters, and its Num layer already provides `gcd_num` without Flyspeck's
unavailable `Big_int` conversions. Those leads were independently reduced and
validated against the pinned Flyspeck source rather than copied as authority.

The final normalization performs these compatibility-only changes:

- eta-expands `length`, `mapf`, `foldl`, `foldr`, `applyd`, and the already
  identity-normalized `undefine`, following the independently validated `rev`
  fix already present at the base commit;
- omits Flyspeck's redundant local `gcd_num` definition so the already-loaded
  Candle Num implementation remains in scope; and
- splits the expansive `(|->),combine` pair into two parameterized public
  functions, retaining the original private update and combine algorithms and
  argument order.

No HOL theorem statement, hypothesis, proof, definition, or allowed axiom was
changed. Every operation is anchored to the exact pinned source line/span and
the complete normalized output remains size- and digest-locked.

## Faithful failure-set collection

Each probe booted the checked DEVELOPMENT / NONPROMOTABLE Candle runtime,
loaded full `hol.ml`, and then loaded the complete normalized
`text_formalization/general/lib.hl`. The sequence exposed one next failure at a
time:

1. `length`: CakeML value restriction;
2. `gcd_num`: unavailable `num_of_big_int`/`Big_int` API;
3. `mapf`: CakeML value restriction;
4. `foldl`: CakeML value restriction;
5. `foldr`: CakeML value restriction;
6. `applyd`: CakeML value restriction;
7. `undefine`: CakeML value restriction; and
8. `(|->),combine`: CakeML value restriction on the expansive pair.

The final probe at
`/project/flyspeck-candle-runs/v15-value-restriction-probe-cf97a2c-run-011`
loaded the entire file successfully and exported all affected functions with
their expected polymorphic types. It took 1:55.75, used 4,234,496 KiB maximum
RSS, and exited zero. Its log and timing SHA-256 identities are
`06f55c624ac32372f876764785bbe0af150667618547a135b9faa31ad39cf634`
and `f869dd7b8205a3759cc1a72bf2742499dbb10f3a752ecc56bc428a7c75219eef`.

The original paired algorithm and the split form were additionally exercised
under insert, replace, multi-branch merge, reversed noncommutative merge, and
zero-elision cases. Their five exact marshaled-structure MD5 projections were
identical:

```text
336dd913cf7895fa2e314c719ac14991
f99cff5fb2552bb01c20fc818f663e07
9e05541eb9f9f0464a6db22373a0da89
ccd148ece9aefaf57c834da6ba0ff4c6
4553333c987b65e64c8841c78c702560
```

## Regenerated authorities and focused gates

The final normalized `lib.hl` is exactly 30,000 bytes, MD5
`9c119e851799375ea9e0b65080eafa0f`, and SHA-256
`6380ec1b92532ab613d6d5157c4b32f50acd5c6a9be1b3d387bddaf268673ab5`.
The normalization contract and regenerated manifest SHA-256 identities are
`33e5d6a6448bf48c59c8ba2efc22aa5d3865177bb95330fbf957947b13506a98`
and `74a29b019f9aaac7f3a939ae3711e55ae7dc87b197c4d215f101f16c99408bad`.
The pilot and all-inventory descriptor identities are respectively
`573fa60c7932d5f5dcf3ec029c709aa23a18ee0e7bfe5c34d3671a9241348992`
and `6593257baa2450973084c92e1c1da9cbc3318907385ba443fec8af12a6e0f1d3`.

Focused validation passed:

- normalization/manifest/stratum unit tests: 55/55;
- source-only all-inventory preparation: 17/17;
- parser descriptor selection: 20/20 pilot and 400/400 all inventory;
- prepared-input unit tests: 10/10; and
- compiled base-prefix API test, including the full normalized `lib.hl`: PASS.

A broader parser-controller unit invocation was stopped because each case
recomputed the 318,813-site quotation corpus. A representative failure was
confirmed as a pre-existing parent-commit authority mismatch: the quotation
model pins CakeML `8a8926906ec97204eeec961496d191103cda3229`, while the parent manifest
already records development runtime `cea7c49d441c749bed4c8a987bee6d321816fbde`.
That unrelated assurance issue was not folded into this functional batch.

No qualified Great100 runtime, source, report, transcript, or semantic-evidence
byte was modified.
