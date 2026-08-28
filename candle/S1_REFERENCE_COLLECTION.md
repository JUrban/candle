# S1 reference identity collection

`reference_fingerprints.py` collects review-only theorem identities from one
fresh pinned HOL Light/OCaml process. It does not approve identities and cannot
write `top100_manifest.EXPECTED_IDENTITIES`.

## Trust and provenance contract

Before execution, the tool requires and records:

- a clean reference git tree and full commit ID;
- exact SHA-256 pins for the collector, launcher, OCaml/HOL runtime executable,
  `ocamlc`, `hol.ml`, the manifest, and `candle/fingerprint.ml`;
- the probed OCaml compiler version;
- manifest-equal hashes for every ordered target load file;
- audited mapping status and ordered requested theorem value paths;
- a 256-bit session nonce embedded in both start and completion markers;
- fresh-process execution, with checkpoints/preloaded theorem state forbidden.

Execution uses a recorded allowlist environment (`HOME`, `PATH`, `LC_ALL`, and
`LINE_EDITOR`) rather than inheriting arbitrary caller variables. In particular,
`HOL_ML_PATH`, `HOLLIGHT_DIR`, and OCaml preload variables cannot silently
replace pinned inputs.

The collector launches the pinned reference launcher itself, supplies the
generated request on standard input, captures combined output, and rechecks all
pins and git cleanliness after exit. The target file(s), serializer, and
theorem requests run in that order. Missing/duplicate session markers, a
nonzero exit, missing/extra fingerprint records, inconsistent global axioms,
or any changed pin fails collection.

## Commands

Generate and inspect a plan without starting HOL Light:

```sh
python3 candle/reference_fingerprints.py plan \
  --target 100/gcd \
  --reference-root /project/repos/hol-light \
  --launcher /project/repos/hol-light/hol.sh \
  --runtime /project/repos/hol-light/ocaml-hol \
  --ocamlc /usr/bin/ocamlc \
  --plan /tmp/gcd-reference-plan.json \
  --request /tmp/gcd-reference-request.ml
```

After review and only when heavy workloads permit, collect in one fresh
process with an explicit total wall deadline:

```sh
python3 candle/reference_fingerprints.py collect \
  --target 100/gcd \
  --reference-root /project/repos/hol-light \
  --launcher /project/repos/hol-light/hol.sh \
  --runtime /project/repos/hol-light/ocaml-hol \
  --ocamlc /usr/bin/ocamlc \
  --plan /tmp/gcd-reference-plan.json \
  --request /tmp/gcd-reference-request.ml \
  --transcript /tmp/gcd-reference.log \
  --candidate /tmp/gcd-reference-candidate.json \
  --wall-timeout 3600
```

Validate the review-only shape later with:

```sh
python3 candle/reference_fingerprints.py validate \
  /tmp/gcd-reference-candidate.json
```

## Deliberate promotion barrier

The candidate schema is `candle-s1-reference-candidate-v1`, its approval status
is always `candidate_unapproved`, `promotion_allowed` is always false, and
observations remain `observed_uncompared`. Identities are nested under
`candidate_identities`; the object has a different shape from the exact
two-field `EXPECTED_IDENTITIES` value. Manifest generation and the runner both
reject the candidate object as malformed if it is pasted into the expected
identity table.

There is intentionally no candidate-to-expected conversion command. An
independent review must establish reference suitability, inspect theorem and
global-axiom identities, preserve provenance separately, and explicitly enter
only the approved expected object in a reviewed commit.

## Current limitations

- Fresh-process isolation is enforced by spawning a new launcher, but it is not
  a proof that the pinned launcher/runtime implementation is trustworthy.
- The launcher pin and runtime pin are recorded separately; a reviewer must
  confirm that the launcher actually invokes that runtime.
- Direct target files are hash-equal to the manifest. Transitive dependencies
  are pinned collectively by the clean reference git commit, not enumerated in
  the candidate.
- Reference and Candle `hol.ml` may differ. The candidate records reference
  `hol.ml` and global axioms so that difference is visible; suitability still
  requires review.
- Source-normalized compatibility targets may intentionally differ from the
  reference target file and will fail planning until that difference receives
  an explicit, separately reviewed policy. The tool has no bypass flag.
- The structural serializer preserves free and type-variable names. Its
  cross-runtime canonicality remains an acceptance assumption to validate on
  reference/Candle differential samples before approving all 65 identities.
- No reference workload was executed as part of implementing this path.
