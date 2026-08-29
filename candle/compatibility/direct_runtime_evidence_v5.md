# Direct runtime semantic evidence v5

Schema 5 supersedes schema 4 for newly generated cumulative Flyspeck attempts.
It adds direct semantic observations, but remains diagnostic and
nonpromotable. The exact schema-4 contract remains accepted by its validator;
a schema-4 artifact cannot pass the schema-5 validator, and a partial upgrade
cannot pass either exact envelope.

## Dependency-history observations

`text_formalization/general/serialization.hl` defines
`Serialization.full_digest_thm` only after selected action 295. Accordingly,
dependency history is requested only at the exact final boundary, after the L2
target has been loaded. The requested identities, in order, are:

1. `Linear_programming_results.linear_programming_results_th`;
2. `Mk_all_ineq.the_nonlinear_inequalities`;
3. `The_kepler_conjecture.tame_nonlinear_imp_kepler_conjecture`; and
4. `Candle_flyspeck_l2.tame_imp_kepler_conjecture`.

Each compiled-runtime record binds the attempt nonce, consecutive integer
index, hex-encoded identity, and a 32-character lowercase digest. A terminal
record binds the nonce, exact boundary, count, and canonical SHA-256 of the
ordered request list. Missing, duplicate, extra, reordered, wrong-nonce,
wrong-boundary, malformed, or tampered records fail validation. The immutable
receipt retains the ordered records and their canonical SHA-256, and the
validator rederives them from the read-only bound log bytes.

These values are honestly labelled dependency-history observations.
`full_digest_thm` sorts and deduplicates the theorem history's source labels and
MD5-digests that string. It is not a retained kernel proof trace, theorem
serialization, or approval identity. Boundaries 05 and 06 retain their existing
LP structural fingerprint, but do not claim that Serialization was available;
their dependency-history state is exactly `not_requested`.

## Authenticated semantic coverage projection

The immutable schema-5 attempt adds an exact semantic-evidence plan. It binds:

- the plan, host-materialization, and manifest SHA-256 identities;
- completed action count and exact logical-source closure count/digest;
- loader-owned physical-trace required-key count/digest;
- the boundary's ordered structural and dependency-history requests; and
- all 39 ordered LP-certificate runtime inputs with exact paths, byte counts,
  SHA-256 values, and MD5 values.

The completed receipt's coverage object is not trusted as a set of booleans.
The validator deterministically rederives it from that immutable plan, the
exact logical closure, closed loader-owned trace, structural fingerprint
records, and dependency-history records. It retains canonical hashes of every
input observation and reports source, LP, nonlinear, and final-implication
coverage separately.

Source coverage means exact loader observation against the authenticated
source plan. LP, nonlinear, and final-implication coverage means only that the
requested fingerprints were observed but not compared. The 39 certificates
are authenticated runtime inputs; individual certificate file reads are not
traced, and the artifact says so explicitly.

## Claim limit and remaining release gates

Every schema-5 contract and completed observation requires:

- `approved_reference_present: false` and `approval_sha256: null`;
- `pft_used: false`;
- `s2_eligible: false` and `s3_eligible: false`; and
- `s2_s3_evidence: false`.

A failed receipt may lack semantic observations, but a completed receipt must
contain both exact dependency-history and semantic-coverage objects. Schema 5
does not contain an approval record or finalizer and cannot self-promote.

Promotion still requires a pristine non-PFT reference collector, two agreeing
clean reference sweeps, independent reviewed approval, clean repeated compiled
direct runs, certificate-consumption justification, and the other release
gates. No compiled full Flyspeck run was launched while implementing this
source-only slice, so actual end-to-end `full_digest_thm` compatibility remains
to be demonstrated by the next proof-linked direct run.
