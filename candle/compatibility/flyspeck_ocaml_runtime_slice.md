# Selected Flyspeck OCaml runtime slice

This revision supplies the OCaml-library surface required by the normalized
direct Flyspeck source graph: `Array.init`, `float_of_num`, `frexp`, selected
`Stdlib` I/O and square-root operations, `Sys.word_size`, `Gc.compact`, and the
selected `Hashtbl` operations.  The implementation is CakeML source and adds no
foreign-function interface.

`Float.frexp` is implemented from CakeML's IEEE-754 double primitives and is
covered for normal values, signed zero, the minimum subnormal, and infinity.
`Gc.compact` is a deterministic no-op because it is only an observational
request.  The record-valued `Gc.stat` telemetry in `verify_all.hl` is replaced
by an exact, digest-bound normalization that reports that resource telemetry is
owned by the outer runner.

The compatibility layer deliberately does not pretend to implement generic
polymorphic ordering or hashing.  `Stdlib.compare` returns equality only when
CakeML equality proves equality and otherwise fails with an explicit request
for a typed comparator.  `Hashtbl.hash` also fails closed.  The active selected
uses are replaced by exact, source-digest-bound typed operations:

- term ordering in `prove_flyspeck_lp.hl` uses `Term.compare`;
- section-name ordering in `sections.hl` uses `String.compare`;
- integer occurrence-count ordering in `lpproc.ml` uses `Int.compare`;
- term hashing in `tactics_jordan.hl` uses `Hash_term.hash_of_term`.

The OCaml-compatible unary `Hashtbl.create` uses a linear association list and
preserves the duplicate-binding stack behavior of `add`, `find`, and `remove`.
`Hashtbl.create_ordered` exposes CakeML's ordered bucket implementation when a
caller supplies a typed hash and ordering function; it is used by Candle's
internal compute table.  Its duplicate-binding behavior is intentionally not
claimed to match OCaml's unary table.

The static compatibility manifest evaluates capability uses against the exact
normalized bytes that will be executed while retaining raw-source dependency
and non-use checks.  The current manifest binds 18 normalization entries and
reports no unsupported compatibility use.  Its scanner also distinguishes
public `Array` calls from `Cake.Array` calls.

`test_flyspeck_ocaml_slice.sh` has passed as a compiled source oracle by loading
these sources through a previously linked clean Candle executable.  That result
checks parser, type, and runtime behavior for the selected slice, but it is not
evidence about a newly linked executable and is not S2 or S3 evidence.  The
remaining promotion gate is to finish the pinned CakeML bootstrap, rebuild and
authenticate Candle at this exact revision, rerun the oracle against that
artifact, and then execute the cumulative direct-source prefix through the
first table-heavy Flyspeck action.
