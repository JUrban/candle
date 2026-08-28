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
operation. It adds no FFI command. Because that lowering is expressed as
`Option.valOf (Double.fromString ...)`, the generated insulation layer retains
exactly those two global functions while stubbing the remainder of both
CakeML modules. This is required for literals parsed after `hol.ml` loads the
insulation layer. Since `metis.ml` later replaces the global `Option` module,
its compatibility module also preserves `valOf`. The differential gate
loads the complete `hol.ml` stack before checking the literal corpus, so later
module shadowing cannot silently invalidate the parser runtime.

`float_literal_cases.json` defines the currently evidenced ten-case non-ERANGE
decimal subset and pins exact OCaml 4.14.1 IEEE-754 words as well as invalid
parses. Broader non-ERANGE decimal support remains implementation intent until
the direct corpus execution gates exercise it. Run the reference side:

```sh
python3 candle/compatibility/test_float_literals.py
```

After rebuilding Candle with the parser branch, run both sides:

```sh
python3 candle/compatibility/test_float_literals.py --candle-root /path/to/candle
```

The direct-source corpus gate is separate from that small grammar/boundary
suite. `flyspeck_float_corpus.json` binds manifest SHA-256
`2bb61e249baa2e8158da4b57f419a269504c7617f6bccefdec5465fcaab85380`,
Flyspeck `1ce0353008eba83d3c76ae9a25c3c242e4802d53`, and normalization
contract `ac925270aa6a8605a8f70ab170ff965c3e4a4d6410623e3d3a6d51976ff1da08`.
It records 15,775 decimal-float code occurrences in nine selected runtime
files and all 1,741 exact spellings. The scanner follows the proved CakeML
decimal grammar and excludes nested comments, strings, and HOL backtick
quotations. Before scanning, it authenticates all 400 original manifest nodes,
the exact schema-2 normalization receipt, and all 18 normalized outputs.

An independent completeness gate then lexes the same authenticated runtime
sources with the actual OCaml 4.14.1 compiler-libs lexer. It requires an exact
match of site records (including locations), spellings, counts, and file
projections. OCaml's lexer, rather than the Python scanner, classifies comments,
strings, character literals, identifiers, numeric forms, and suffixes. A small
separate quotation skipper starts only when OCaml emits `BACKQUOTE`, because HOL
quotation bodies are not OCaml syntax. Recovery for source forms rejected by
stock OCaml (such as Flyspeck's `0in`) is permitted only when the rejected token
cannot be a potential float; malformed potential floats fail closed. Run this
host completeness check directly with:

```sh
python3 candle/compatibility/check_flyspeck_float_completeness.py \
  --candle-root /path/to/candle \
  --flyspeck-root /path/to/flyspeck-at-1ce0353 \
  --overlay-root /path/to/ac925270-overlay \
  --ocamlc /usr/bin/ocamlc
```

Regenerate the complete inventory and all OCaml 4.14.1 Word64 observations:

```sh
python3 candle/compatibility/flyspeck_float_corpus.py \
  --candle-root /path/to/candle \
  --flyspeck-root /path/to/flyspeck-at-1ce0353 \
  --overlay-root /path/to/ac925270-overlay \
  --ocamlc /usr/bin/ocamlc --check
```

This also compares every spelling with C-locale host `strtod`; the pinned
corpus has no `ERANGE` case and all 1,741 words match OCaml. That host result is
primitive-boundary evidence only. It is not a substitute for the compiled
gate, which first repeats both the Python regeneration and independent OCaml
lexer completeness check, validates the linked Candle runtime record, loads the
full `hol.ml` insulation stack, and checks every exact spelling in bounded
chunks:

```sh
python3 candle/compatibility/check_flyspeck_float_corpus.py \
  --candle-root /path/to/clean-linked-candle \
  --flyspeck-root /path/to/flyspeck-at-1ce0353 \
  --overlay-root /path/to/ac925270-overlay \
  --ocamlc /usr/bin/ocamlc
```

The committed inventory and generator do not constitute a compiled PASS. A
PASS from the second command establishes the decimal spelling/Word64
compatibility of this exact selected graph; it does not establish that the
graph loaded, that its theorems have approved fingerprints, or S2/S3.

The script reports the Candle half as `NOT RUN` unless a built tree is supplied;
reference-only success is not closure evidence. Hexadecimal OCaml float syntax
is explicitly out of scope because CakeML's retained scanner is decimal-only
and the audited Great 100 slice contains no hexadecimal float literal. The
compiled-Candle half explicitly requires the representative hexadecimal form
to remain rejected, checks that invalid `Double.fromString` returns `None`, and
checks that `Option.valOf None` raises after insulation. The bridge uses host
`strtod` and maps `ERANGE` to `None`; consequently the gate also records the
intentional current divergence for decimal overflow (`1e309`) and underflow
(`1e-4000`), which OCaml maps to infinity and zero. Those forms are not in the
claimed subset.

The linked-artifact provenance also pins the resolved ELF loader, libc, and
libm contents used by the executable, because the conversion depends on host
`strtod` behavior. Promotable gates use a fixed `/usr/bin:/bin` path and C
locale, preserve only validated decimal CakeML heap/stack sizes, reject loader
and noninteractive-shell injection variables, require the exact three
dependency roles, and archive the record and object bytes in each
direct-attempt snapshot. This does not claim
to pin the kernel, vDSO implementation, CPU/IFUNC choice, NSS/gconv inputs, or
libraries opened later with `dlopen`; a fixed runtime image remains the stronger
release option if those affect an observed result.

The privileged-mode repository launcher uses absolute isolated Python and runs
the linked-provenance validator before every ordinary Candle session. It also
requires the root boot/config aliases to be the exact relative symlinks whose
resolved bytes appear in the record. Standalone compatibility scripts cannot
report a compiled PASS against a dirty tree, an obsolete record schema, or a
different executable. The direct stratum runner bypasses the launcher only
after performing its stronger original-plus-snapshot preflight itself.

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
The direct audit also exposes a larger performance obligation than this
100-term benchmark: `break_case_log.hl` contains 15,462 load-time literals,
including 11,640 copies of `0.5000`, while `break_case_exec.hl` places
`10000.0`, `1.0`, and `1.0e-10` inside repeatedly evaluated functions and
recursive traversals. A corpus-shaped load and repeated-function comparison
against hoisted constants remain required performance evidence.
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
`cubic_target_observation.json` records the resulting clean target pass and
structural `CUBIC` identity. Its `observed_uncompared` status is intentional:
the recorded hash is evidence, not a reference-approved fingerprint.

`oracles/trailing_semicolon_argument.ml` minimizes
`CANDLE-OCAML-TRAILING-SEMICOLON-001`. OCaml 4.14.1 accepts the trailing
semicolon in a parenthesized argument expression; compiled Candle rejects the
enclosing module phrase. Its diagnostic points at `module Pm_eqn4_rhs`, but
`oracles/module_identifier_underscore.ml` proves that the same module name is
accepted without the interior semicolon. The selected remedy is therefore the
one-token source normalization from `badbd63`, not a module-parser change.
`trailing_semicolon_observation.json` preserves both compiled-Candle runs.
After that normalization, `e_is_transcendental_target_observation.json`
records a clean target pass and the structural identity requested through the
actual module-scoped value `Finale.TRANSCENDENTAL_E`. Its fingerprint remains
`observed_uncompared`, not reference-approved.

`num_rational_cases.json` isolates the pure Num portion of the `ceva` failure.
The old `fix-top100` history bundled rounding with broad SOS representation and
process changes.  The selected remedy instead implements exact rational floor,
ceiling, half-away-from-zero rounding, and reciprocal negative powers without
adding FFI.  Run the pinned HOL Light reference cases with:

```sh
python3 candle/compatibility/test_num_rationals.py \
  --ocaml /path/to/ocaml-4.14.1/bin/ocaml \
  --zarith-dir /path/to/ocaml-4.14.1/lib/zarith
```

Add `--candle-root /path/to/candle` for the compiled-Candle half. A green Num
oracle does not authorize importing the rest of `Examples/sos.ml`; its finite
map, printer, float, filesystem, and solver boundaries remain separate work.
The pinned 25-case OCaml/Candle run passes on this branch. In addition to the
15 rational cases, it covers `Num.num_of_string` on decimal plus/minus signs,
leading-zero, unbounded, empty, and invalid inputs. The implementation consumes
`Cake.Int.fromString` directly, avoiding the `Bind` raised by Candle's
`Option.valOf`-based global wrapper while preserving the reference `Failure`
contract. It explicitly rejects the SML-only `~` negative sign and trailing
junk. This is the integer-token subset exercised by Flyspeck's SOS decimal
parser, not a claim of complete Zarith `Z.of_string` compatibility. Zero to a
negative power remains an explicit excluded boundary
because the reference Zarith layer admits an infinite rational while Candle
rejects denominator zero.

`sos_finite_func_cases.json` isolates the first representation boundary after
the numeric SOS gate.  The reference HOL Light implementation uses
polymorphic comparison inside canonical Patricia-tree finite functions;
Candle's association-list representation instead requires an explicit key
comparator.  The selected adaptation supplies only the concrete `Int`, pair,
`Term`, `Num`, and nested monomial comparators needed by the prefix of
`Examples/sos.ml`.  It does not add general polymorphic comparison or import
the anchor's later printer, float, value-restriction, filesystem, or solver
changes.  Run both sides with:

```sh
python3 candle/compatibility/test_sos_finite_functions.py \
  --reference-root /path/to/pinned/hol-light \
  --candle-root /path/to/candle
```

The six cases cover integer and pair maps, combining with zero elision,
nested finite-function keys and equality, a real-term monomial used as a
polynomial-style key, and map/fold behavior.  Both pinned OCaml 4.14.1/HOL
Light and a fresh compiled-Candle process pass.  This remains a differential
sub-gate until the affected source targets load and their theorem/assumption
fingerprints are approved.

The isolated post-Num `100/ceva` rerun confirms the expected boundary in the
real source target: it reaches `let mapa f (d,v)` and fails because bare
`undefined` is comparator-parameterized in Candle.  The machine report and
resource observation are pinned in `sos_finite_func_observation.json`.  This
also advances the Num entry beyond its original failure, but it does not make
Ceva a pass; the comparator remedy still needs a clean target run.

The post-patch prefix load reaches and defines `print_poly` before stopping at
the separately classified unsupported `#install_printer` directive.  Its
141.98-second, 1,232,000-KiB observation and exact log hash are recorded with
the frontier artifact.  That is evidence that the comparator prefix advances;
it is not evidence for the later SOS body or a clean Ceva result.

The next independent boundary is OCaml's display-only `#install_printer`
directive.  Candle does not execute this toplevel directive.  The selected
source adaptation retains the four ordinary `print_* : ... -> unit` values and
adds four distinct `pp_* : ... -> pp_data` adapters, then comments out only the
directives.  In particular it uses `pp_poly`; it does not import the audited
anchor's accidental second `print_poly` definition.  The isolated load records
all eight types and advances to the later explicit-comparator `increasing`
boundary.  `sos_printer_observation.json` pins both logs and keeps this
display-only step separate from theorem semantics.

The next patch does not restore a misleading global polymorphic ordering
helper.  It adds the separately named `increasing_by` and supplies explicit
lexicographic integer comparators only at the two SDPA sites reached by the
load.  This avoids changing the arity of HOL Light's conventional
`increasing` name for unrelated files.  The isolated load elaborates
`sdpa_of_blockdiagonal`, `sdpa_of_matrix`, and `sdpa_of_problem`, then advances
to the independent missing `Num.num_of_string` binding in the decimal parser.
`sos_order_observation.json` pins the 129.78-second, 1,233,792-KiB run and its
exact transcript hash.

The pure `Num.num_of_string` addition then passes all 25 reference/Candle
cases and advances the same SOS load through `decimal`, `parse_decimal`, both
solver-output parsers, and `sdpa_run_succeeded`. The next failure is the first
embedded newline in `sdpa_default_parameters`. That is not a new source
adaptation: it is the existing `CANDLE-OCAML-MULTILINE-STRING-001` rebuild
gate, already repaired and proved in the audited CakeML source by
`c26aa71d2b1`. `num_string_observation.json` records the 136.46-second,
1,232,000-KiB load and exact transcript hash without claiming a complete SOS
or target pass.
