# Reflected exact linear-combination prototype

Status: DEVELOPMENT / NON-RELEASE; measured local benefit, but no Flyspeck
theorem replacement or end-to-end speedup claim

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
core test.

The computed adapter now connects those pieces end to end for normalized
generic rows. For each authenticated source inequality it requires
assumption-free lhs/rhs reification theorems, proves that the resulting exact
row denotes that source row, applies the bulk soundness theorem once, evaluates
the complete exact fold with `Kernel.compute`, and rewrites the soundness
result to the computed coefficient vector and integer. Its regression test
combines two assumed inequalities with distinct signed coefficients and checks
the exact accumulator, conclusion, and complete hypothesis set. The adapter
does not invoke an oracle or trust its ML-produced row data.

The result is now canonicalized by a second verified computation. The fold's
subtraction-free `(positive,negative)` pairs are reduced to pairs with one zero
component; HOL proofs establish preservation of both scalar and vector real
denotations before the inequality is rewritten. The test deliberately produces
an unreduced right side `(21,4)` and checks that the public adapter receives the
proved canonical result `(17,0)` with unchanged hypotheses.

The Flyspeck instantiation now selects `Linear_function.lin_f`, converts the
checker’s base-200 numeral syntax to ordinary numerals by a kernel conversion,
and renders a canonical result back through `Arith_int.my_mk_realintconst`.
Its focused fresh-state test passes for a normalized source aggregate and
checks the exact result, public conclusion, and complete hypothesis set.
The source-facing entry point additionally requires an assumption-free
normalization equality from its caller. Its test converts raw checker-shaped
linear expressions through such equalities and checks the exact result,
public conclusion, complete raw hypothesis set, and unchanged global axiom
state. The production post-action-181 caller will supply
`Prove_lp.lin_f_conv`; the adapter does not trust or duplicate that parser.

The adapter now also closes the cancellation/refutation boundary. It accepts
the same weighted source inequalities, requires the verified computation to
produce an all-zero coefficient vector and a strictly negative canonical
right-hand side, re-renders and reifies that exact result, and derives `F`
through an ordinary HOL theorem. Its focused test combines `x <= 0` and
`--x <= --1`, obtains the exact computed result `([(0,0)],(0,1))`, preserves
both assumptions, and leaves the global axiom set unchanged. This establishes
the machinery needed to replace the old per-variable `add_cancel_step` fold;
it is not yet a real-terminal or timing result.

The terminal-shaped entry point separately applies the positive
`10^precision` multiplier to every ordinary constraint coefficient while
leaving target-variable, variable-bound, and optional global-inequality rows
at their certificate weights. It then invokes the same verified bulk
refutation. A focused cancellation uses multiplier 10 on the constraint side
and weight 10 on the bound side, computes `([(0,0)],(0,10))`, and derives `F`
with the exact two hypotheses. Negative row weights and a nonpositive precision
multiplier fail closed. The real-checkpoint caller still owns authenticated
row selection and optional global-inequality construction.

## Real-certificate measurement

The generic bulk-soundness path has run on terminals 15, 5, and 17 from the
authenticated `hard_2.dat` certificate in three successive fresh checkpoint
attempts. The accepted 50 ms externally sampled attempt used 402/480/382 real
rows, preserved 68/78/65 hypotheses, and measured:

| Terminal | Selection + bulk proof | Legacy construction + combination | Local ratio |
|---:|---:|---:|---:|
| 15 | 2.641 s | 26.077 s | 9.87x |
| 5 | 3.960 s | 16.449 s | 4.15x |
| 17 | 2.841 s | 10.407 s | 3.66x |

This clears the feasibility response's 3x continuation threshold on all three
selected slices. It is deliberately not an inclusive terminal benchmark: the
measured prototype did not yet include the exact reifier, `Kernel.compute`,
canonicalization, public rendering, variable-bound construction,
cancellation, or final discharge. The retained evidence is
`/project/flyspeck-candle-runs/cv-lp-bulk-hard2-v11`.

The corrected complete old/new comparison harness is prepared, but its latest
fresh checkpoint restore was stopped by the swap-out resource guard before any
proof byte was emitted. That partial state is rejected and is not reused.

It is not yet a Flyspeck checker replacement. Before integration it must add:

1. conclusion, hypothesis, and axiom-fingerprint equality against the existing
   `transform_le_ineq`/`add_step'` oracle; and
2. an inclusive complete-adapter benchmark on `hard_2` terminals 15, 5, and 17,
   followed by reflection of variable bounds/cancellation if they remain
   material.

The existing theorem path remains the fail-closed fallback. No certificate,
source theorem, hypothesis, public interface, or allowed axiom is changed.
