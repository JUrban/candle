# Reflective nonlinear verifier development boundary

Status: DEVELOPMENT / NON-RELEASE

## Objective

Exercise Flyspeck's existing proof-producing interval/nonlinear verifier in
Candle on the exact public leaf consumed by the current serialized nonlinear
reconstruction. The serialized theorem is an oracle for conclusion,
hypotheses, and axioms only. It is not proof evidence for the new path.

The target interface is an ordinary kernel theorem from
`M_verifier_main.verify_ineq`. The experiment must compare its public
conclusion and hypotheses to the existing leaf theorem and must leave the
global axiom set unchanged.

## Authenticated source boundary

`flyspeck_nonlinear_verifier_closure.py` recursively follows the literal source
actions of `formal_ineqs/verifier/m_verifier_main.hl` using the same scanner and
lexical resolver as the direct manifest. Its generated closure contains:

- 90 exact source nodes and 193 selected literal edges;
- 28 Candle/HOL nodes and 62 Flyspeck nodes;
- 34 nodes already present in the direct 400-source manifest; and
- 56 additional Flyspeck logical identities.

There are no missing, dynamic, or ambiguous source edges. Every extension
entry carries repository identity, logical relative path, MD5, and SHA-256.
Absolute worktree paths remain run-local observations and basenames never
authorize a source.

The closure is deliberately separate from the release manifest while this is
an isolated experiment. A production integration must merge the same logical
identities into the one generated direct authority before parsing or evaluating
any of them. A failed or partial source load is never a reusable predecessor.

## Runtime compatibility found by the closure

The previously selected 400-source graph did not exercise several ordinary
OCaml library members used by the formal verifier. This branch adds the
following central compatibility support without changing Flyspeck source:

- the complete selected legacy `Big_int` surface over CakeML's
  arbitrary-precision integers: representation/conversion, zero, sign,
  absolute value, successor/predecessor, addition/subtraction/multiplication,
  Euclidean quotient/remainder, comparison, positive integer powers, and
  exact floor square root;
- the representation-preserving `Num.num_of_big_int`/`big_int_of_num` bridge
  for integers, with native-compatible failure on a non-integer rational;
- the complete missing subset from a mechanical audit of native `Num` names
  in the 90-source closure: `pred_num`, `compare_num`, and exact rational
  `approx_num_exp` rendering;
- the missing top-level `sign_num` export expected after native `open Num`,
  sourced from the same central `Num.sign_num` implementation;
- an exact, hash-bound normalization of the private raw-float comparator's
  `Num.num` exponent ordering from unavailable polymorphic `<=` to `le_num`;
- exact binary64 definitions of OCaml's `infinity`, `neg_infinity`, and
  canonical `nan` constants, with the active nonlinear closure mechanically
  restricted to its observed `infinity` and `nan` subset;
- a typed `float_ieee_equal` bridge plus four exact checker normalizations,
  preserving native equality for signed zero, infinities, finite values, and
  NaNs where CakeML's generic equality compares binary representations;
- typed `float_ieee_lt`/`float_ieee_le`/`float_ieee_gt`/`float_ieee_ge`
  bridges, the six adjacent float-splitting orderings, and all 12 active
  raw-double threshold/angle-reduction comparisons in seven authenticated
  checker sources, preserving native finite, infinity, signed-zero, and NaN
  branches;
- an exact four-site normalization of `2.0 *. atan 1.0` to the bit-identical
  binary64 literal `1.5707963267948966` in the two cosine-table builders;
- a central condition-preserving `candle_assert` helper and all 14 active
  assertion sites in the authenticated closure, retaining the distinct
  `Assert_failure` constructor on false;
- order-preserving `Array.to_list`;
- qualified and implicitly opened `abs_float`, plus `Stdlib.ignore`; and
- the `Format.std_formatter` value needed by the verifier's diagnostic-printer
  interfaces.

The IEEE comparison differential gate compares all four ordering operators for
every pair in a seven-value matrix containing finite negatives and positives,
both signed zeros, both infinities, and NaN: 196 native/Candle observations in
total. The `Big_int`/`Num` differential gate covers every selected member, values beyond
the signed 64-bit range, all sign combinations for Euclidean division,
positive integer powers, 0, adjacent nonsquares/squares, and `2^128 - 1`.
Array order, qualified and unqualified float absolute value, ignored-result
behavior, and formatter callback typing are checked against native OCaml
4.14.1. The `approx_num_exp` cases cover signs, zero, fractions, very small
and very large magnitudes, decimal rounding, and mantissa carry.

The current first-leaf controller extracts this one source-authoritative
`Big_int` module from `candle/nums.ml` and overlays it after the older linked
development runtime starts. The controller records both source and extracted
module hashes. This avoids a costly relink during compatibility discovery,
but is deliberately non-release: the same committed module must be absorbed
by a fresh linked runtime before any cumulative or release claim.

`Format.std_formatter` currently preserves the source type and diagnostic
callback interface. It accumulates pretty-print tokens but is not a faithful
stdout-flushing formatter. This does not weaken kernel theorem checking, but
if a real verifier run relies on the associated diagnostic output, formatter
flushing must be implemented and differentially tested before that output can
be claimed equivalent.

The closure generator inventories qualified compatibility uses and fails its
regression if any member falls outside the central support table. This avoids
letting the experimental source list and runtime support drift independently.
The current closure contains 404 such uses of 34 distinct module members and
zero unsupported uses. It separately records 13 lexical uses of supported
top-level compatibility names; this catches the implicitly opened
`abs_float` at `trig/exp_eval.hl:345` while retaining the local definitions
that require later inference to disambiguate.

Both focused differential gates pass against native OCaml 4.14.1. The
arithmetic gate covers exact floor square root around adjacent squares and at
`2^128 - 1`, multiplication beyond signed 64-bit range, equality, and negative
input rejection. The runtime gate covers array order, qualified and
unqualified binary64 absolute value, discarded results, and the formatter
callback type. The Candle halves load only `insulate.ml`, `nums.ml`,
`pretty.ml`, and `ocaml.ml`, so these checks take seconds rather than paying for
an unrelated full HOL replay.

## Gates

1. Parser-only gate all 56 extension sources through the dedicated
   `caml_parser$run` capability after exact loader-action masking and HOL
   quotation expansion. This performs no inference or evaluation.
2. From a fresh clean predecessor, authenticate the complete source extension,
   then load the formal verifier closure. Stop at the first parser, inference,
   evaluation, or runtime failure and repair the smallest shared cause.
3. Extract the exact first public `ineqm` leaf and its `ineq6m`/`ineq9m`
   conversion from the largest reconstruction case.
4. Run `M_verifier_main.verify_ineq` on that exact public term and compare
   conclusion, hypotheses, theorem digest, and global axioms to the serialized
   oracle.
5. Profile verifier setup, interval evaluation, subdivision/search, theorem
   construction, and final public conversion before deciding which computation
   is worth reflecting further.

The fourteenth fresh first-leaf replay completed `arith/float_pow.hl`, the
large `trig/exp_log.hl` analysis dependency chain, and `trig/poly_eval.hl` in
4,210.637 seconds (peak RSS 1,178,240 KiB). It then failed during inference of
`trig/exp_eval.hl:184`, where native OCaml inferred `r <= t` over two doubles
but Candle's unqualified operator is integer-only. A complete audit found the
same boundary at 12 sites rather than just patching the observed line. The
focused 196-observation differential gate is green; the next expensive replay
uses that coherent batch.

The fifteenth fresh replay passed that typed-threshold boundary and loaded the
large trigonometric development through `trig/poly_eval.hl`. It stopped while
inferring `trig/cos_bounds_eval.hl:89` because Candle does not export native
OCaml's `atan`. This was a frontend/name-availability failure before proof
execution, not a failed theorem. The failed run is preserved with elapsed time
4,595.625 seconds, child CPU 4,525.855 user + 65.453 system seconds, peak RSS
1,184,512 KiB, and log SHA-256
`150b065ff3396252e2284861bf522ae884ebde71c0e57c31af207da1ea250d01`.

A complete audit of the authenticated active closure found exactly four
`atan` occurrences: two each in `trig/cos_bounds_eval.hl` and
`informal/informal_sin_cos.hl`. Every occurrence is the closed expression
`2.0 *. atan 1.0`, used only to choose an even or odd cosine Taylor-table
degree. Native OCaml 4.14.1 gives the same binary64 bits
`0x3ff921fb54442d18` for that expression and the decimal literal above. The
focused differential gate also checks all 42 upper/lower degree choices for
precisions 0 through 20. The raw expression reproduces Candle's undefined-name
failure and the exact-literal form passes. This deliberately does not add an
unverified general transcendental implementation.

Closure compatibility version 8 applies only those four exact replacements.
Its parser gate passes 56/56 sources with zero parser errors: 23 changed
prepared inputs were executed freshly in 20.261 parser-seconds and 33 exact
unchanged prior successes were reused by prepared-input hash. The complete
gate took 3,170.820 elapsed seconds because it retained the known generated
parser hotspot. Closure SHA-256 is
`b82746f4378a6c256ae9a81abdba66334b71d891503f6fd40fadb8edd0d1fc15`.

The parser-only survey has exposed one material frontend hotspot rather than a
syntax incompatibility: the 469,938-byte generated
`multivariate_taylor-compiled.hl` source occupied one parser process for about
27 minutes before passing and advancing to the next exact source. The gate's
per-source timeout is therefore 30 minutes. This observation argues for
persisting parser progress and avoiding repeated whole-closure parser surveys;
it is not evidence about proof execution time.

None of these gates changes the qualified Great100 runtime or evidence. Parser
results, checkpoint probes, and oracle comparisons remain non-release evidence
until a fresh cumulative direct run uses a single authenticated manifest and
the production runtime.
