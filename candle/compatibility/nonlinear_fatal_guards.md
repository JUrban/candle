# Direct nonlinear fatal guards

Three pinned Flyspeck nonlinear checks originally evaluated booleans without
aborting when false.  The direct route now applies two exact, hash-bound
normalizations using the source corpus's existing
`comparison || failwith message` idiom:

- `PROJECT-NONLINEAR-S3-PARAMETER-COUNT-001` makes the 23,242-parameter
  comparison fatal in `break_case_exec.hl`;
- `PROJECT-NONLINEAR-S3-DIGEST-GATES-001` makes both the cheap assumed-theorem
  surface digest (`1f0547...`) and final theorem surface digest (`e607b9...`)
  fatal in `mk_all_ineq.hl`.

Each accepted comparison still runs once, has type `bool`, and returns `true`.
A false comparison raises `Failure`, preventing the containing source action,
neutralization, later action, or checkpoint from being treated as complete.

These are regression guards, not nonlinear closure evidence.  The 23,242
value counts a pre-`setify` diagnostic work-unit list used by `get_nth`; it
does not prove category disjointness, multiplicity, or reconstructed-leaf
coverage, and a count-preserving mutation can evade it.  Both digests come
from `Serialization.simple_digest_thm`, which hashes theorem surface data and
filters deserialization hypotheses; it does not bind definition or proof
history, input coverage, generated-input provenance, or the permitted axiom
set.

S3 therefore still requires a provenance-bound compiled run that authenticates
all inputs, attempts and succeeds on the complete nonlinear workload without a
`TRUTH` sentinel, reaches the final theorem, records exact structural theorem,
hypothesis, axiom/history, and coverage artifacts, and reproduces them from a
second clean state.  PFT replay cannot satisfy these gates.
