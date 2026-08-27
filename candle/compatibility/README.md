# Candle OCaml compatibility ledger

`ledger.json` records observable differences against the pinned OCaml
behavior. Every entry names a minimal reproducer, the affected corpus slice,
the proposed remedy, and the evidence still required before closure.

The first entry was reduced from the clean-process Great 100 baseline. OCaml
4.14.1 accepts `oracles/float_literal.ml`; compiled Candle rejects the same
declaration in its parser. The `fix-top100` anchor avoids the construct in
`100/bertrand.ml`, but also imports broad float/byte FFI changes. The selected
smaller remedy instead restores CakeML's retained decimal-float token to the
OCaml grammar and lowers it through the existing `Double.fromString` basis
operation. It adds no FFI command.

`float_literal_cases.json` defines the supported decimal subset and pins exact
OCaml 4.14.1 IEEE-754 words as well as invalid parses. Run the reference side:

```sh
python3 candle/compatibility/test_float_literals.py
```

After rebuilding Candle with the parser branch, run both sides:

```sh
python3 candle/compatibility/test_float_literals.py --candle-root /path/to/candle
```

The script reports the Candle half as `NOT RUN` unless a built tree is supplied;
reference-only success is not closure evidence. Hexadecimal OCaml float syntax
is explicitly out of scope because CakeML's retained scanner is decimal-only
and the audited Great 100 slice contains no hexadecimal float literal.
The ledger entry remains under test until the proof build, rebuilt differential,
clean target load, and theorem/assumption fingerprints are present.
