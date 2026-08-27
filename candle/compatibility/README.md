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
`float_literal_progress.json` records the completed proof build without treating
it as runtime evidence. `benchmark_float_literals.py` measures representative
compiled-Candle load time for integer controls, explicit `Double.fromString`,
and source literals; the latter remains a recorded rejection on the baseline.
The pinned baseline command is:

```sh
python3 candle/compatibility/benchmark_float_literals.py \
  --candle-root /path/to/isolated/baseline --terms 100 --repetitions 3
```

Repeat it with `--require-literals` against the rebuilt isolated tree. Compare
the rebuilt medians with `float_literal_benchmark_baseline.json`; the rejected
baseline literal time is diagnostic only and is not a valid performance ratio.
The ledger entry remains under test until the rebuilt IEEE differential,
end-to-end negative parses, load-time comparison, clean target load, and
theorem/assumption fingerprints are present.

`oracles/multiline_string.ml` minimizes
`CANDLE-OCAML-MULTILINE-STRING-001`, which was exposed when the baseline reached
`100/constructible`. OCaml 4.14.1 parses the embedded newline; the pinned
compiled Candle reports a lexer error. No new parser implementation is needed:
the audited CakeML source already contains `c26aa71d2b1`, including a parser
regression specifically citing `100/constructible.ml`. The remaining gate is an
isolated Candle rebuild followed by the minimal oracle and clean target load.

`oracles/polymorphic_comparison.ml` minimizes
`CANDLE-OCAML-POLYMORPHIC-COMPARISON-001`. OCaml uses polymorphic bare `(<)` and
accepts it where an `int list -> int list -> bool` comparator is required;
Candle's compatibility environment resolves the same spelling to the integer
operator and reports a type mismatch. The `cubic` failure needs term ordering,
so the selected remedy is the existing two-site `Term.(<)` source normalization
from `5c44565`, not a general polymorphic-comparison implementation.
