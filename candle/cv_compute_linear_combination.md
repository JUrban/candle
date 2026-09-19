# Reflected exact linear-combination prototype

Status: DEVELOPMENT / NON-RELEASE; no Flyspeck theorem replacement or speedup
claim

## Why this boundary

The exact `hard_2` profile spends 313.484 seconds of its 320.126-second
verifier in constraint theorem construction, constraint combination,
variable-bound construction, and cancellation. The first two phases alone take
257.567 seconds. By comparison, file decoding takes 0.053 seconds and
`compute_all` takes 4.061 seconds. The working performance boundary is therefore
the normalized arithmetic inside `prove_flyspeck_lp_step1`, beginning with
`transform_le_ineq` and `add_step'`.

## First proof-producing core

`cv_compute_linear_combination_core.ml` represents an exact signed integer as
a pair of naturals `(positive,negative)`, denoting their difference. It never
uses machine integers or unchecked subtraction. A coefficient vector is a list
of those pairs. A weighted row consists of a nonnegative natural multiplier, a
coefficient vector, and a signed right-hand side.

The cval program scales and bulk-adds rows into one normalized accumulator. Its
six all-variable evaluator equations cover signed-pair add/scale, vector
add/scale, row accumulation, and row-list folding. Proved representation
theorems connect every operation and the complete fold to corresponding
ordinary HOL definitions. Thus `Kernel.compute` returns an ordinary kernel
theorem about the exact aggregate; malformed ML output is not accepted as a
theorem.

This dense representation is intentionally the smallest machinery probe. The
real adapter may switch to a sorted sparse map after measuring actual
reification and evaluator costs; doing so requires a new representation and
correctness theorem, not an unchecked implementation substitution.

## Required next links

The adapter decodes the computed cval result through proved round trips and
returns an assumption-free ordinary HOL equality for the complete aggregate.
The generic real theorem layer now proves, without assumptions, that each
nonnegative natural-weighted inequality preserves `<=`, that the list fold
preserves it, and that a fold from `(0,0)` yields a valid aggregate inequality.
This closes the abstract inequality-combination argument independently of cval
evaluation.

The first Flyspeck-facing bridge now accepts authenticated `lhs <= rhs`
theorems paired with natural multipliers, constructs the corresponding row
list, and derives one fold inequality through that soundness theorem. It
preserves all input hypotheses and performs no unchecked theorem synthesis.
This removes theorem-per-addition construction from the combination boundary;
the conclusion is intentionally still an unnormalized fold expression, so no
end-to-end speedup is claimed yet.

The realization layer now proves that signed natural pairs denote integer
differences over the reals, that vector addition and scaling preserve this
denotation, and that the complete exact accumulator fold denotes exactly the
same real fold used by the inequality theorem. Every theorem is
assumption-free. Together with the existing cval representation theorem, this
closes the generic equality bridge from evaluator output to the real
linear-combination result.

The strict theorem-producing reifier now accepts a caller-supplied normalized
linear-function definition, exact integer decoder, sorted variable basis, and
linear-function term. It constructs a dense signed-pair coefficient vector and
returns a kernel theorem equating that vector's real denotation to the source
term. Untrusted ML parsing never authorizes the equality: both sides are
normalized by conversions, and the bridge is constructed only when their HOL
terms agree. Duplicate or unsorted variables, variables outside the basis, and
normalization mismatches fail closed. This generic layer has passed its full
core test, but the actual Flyspeck adapter and public-conclusion normalization
remain pending.

It is not yet a Flyspeck checker. Before integration it must add:

1. a Flyspeck wrapper selecting `Linear_function.lin_f`,
   `Arith_int.my_dest_realintconst`, and the exact arithmetic rewrites required
   by the loaded checker;
2. a normalized-conclusion adapter connecting the reifier, the proved
   realization equality, and the existing theorem interface;
3. conclusion, hypothesis, and axiom-fingerprint equality against the existing
   `transform_le_ineq`/`add_step'` oracle; and
4. inclusive benchmarks on `hard_2` terminals 15, 5, and 17 before any broader
   integration.

The existing theorem path remains the fail-closed fallback. No certificate,
source theorem, hypothesis, public interface, or allowed axiom is changed.
