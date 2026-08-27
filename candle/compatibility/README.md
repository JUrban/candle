# Candle OCaml compatibility ledger

`ledger.json` records observable differences against the pinned OCaml
behavior. Every entry names a minimal reproducer, the affected corpus slice,
the proposed remedy, and the evidence still required before closure.

The first entry was reduced from the clean-process Great 100 baseline. OCaml
4.14.1 accepts `oracles/float_literal.ml`; compiled Candle rejects the same
declaration in its parser. The `fix-top100` anchor avoids the construct in
`100/bertrand.ml`, but that workaround is not yet integrated or certified as
a general source-normalization rule.
