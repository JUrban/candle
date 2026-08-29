# Direct nonlinear fatal guards

The direct route applies two exact, hash-bound normalization entries to the
pinned nonlinear reconstruction:

- `PROJECT-NONLINEAR-S3-RECONSTRUCTION-COVERAGE-001` makes the 23,242-parameter
  partition-shape comparison fatal and counts each recursive `Iarg_leaf`
  traversal in `break_case_exec.hl`;
- `PROJECT-NONLINEAR-S3-FINAL-COVERAGE-GATES-001` makes both theorem-surface
  digests (`1f0547...` and `e607b9...`) fatal, rejects every `TRUTH` sentinel
  from both caught reconstruction paths, and requires exactly 7,479 serialized
  `Iarg_leaf` visits before accepting the final theorem.

Each accepted comparison still runs once, has type `bool`, and returns `true`.
A false comparison raises `Failure`, preventing the containing source action,
neutralization, later action, or checkpoint from being treated as complete.

These are necessary coverage and regression guards, not standalone nonlinear
closure evidence.  The 23,242 value remains a pre-`setify` diagnostic list.
The 7,479 value binds complete traversal of the pinned serialized `Iarg` leaf
corpus only in combination with the authenticated case-log source and the
fatal `TRUTH` gates; a count-preserving source mutation can still evade it.
The two `Serialization.simple_digest_thm` values hash theorem surface data but
do not bind definition or proof history, generated-input provenance, or the
permitted axiom identities.

S3 therefore still requires a provenance-bound compiled run that authenticates
all inputs, attempts and succeeds on the complete nonlinear workload without a
`TRUTH` sentinel, reaches the final theorem, records exact structural theorem,
hypothesis, axiom/history, and coverage artifacts, and reproduces them from a
second clean state.  PFT replay cannot satisfy these gates.
