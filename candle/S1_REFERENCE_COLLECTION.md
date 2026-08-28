# S1 reference identity collection

`reference_fingerprints.py` collects review-only theorem identities from one
fresh pinned HOL Light/OCaml process. It does not approve identities and cannot
write `top100_manifest.EXPECTED_IDENTITIES`.

## Trust and provenance contract

Before execution, the tool requires and records:

- a clean reference git tree and full commit ID;
- exact SHA-256 pins for the collector, OCaml/HOL runtime executable, required
  runtime stub library, the bytecode interpreter selected by the runtime
  shebang, `ocamlc`, `hol.ml`, the manifest, and `candle/fingerprint.ml`;
- exact pins for `hol_loader.cmo`, `pa_j.cmo`, and
  `load_camlp5_topfind.ml`, including the ignored generated objects that a
  clean reference Git status does not cover;
- deterministic whole-tree inventory digests for the OCaml library tree
  selected by `ocamlc -where` (therefore including topfind, findlib, and
  Camlp5) and the runtime-stub directory;
- exact pins for the recursively resolved ELF dependency closure of the
  bytecode interpreter and runtime stub, including the dynamic loader, libc,
  libm, and GMP on the current host;
- the collector repository commit, status, committed collector hash, and an
  assertion that the executing collector equals that committed file;
- the probed OCaml compiler version;
- manifest-equal hashes for every ordered target load file;
- audited mapping status and ordered requested theorem value paths;
- a 256-bit session nonce embedded in both start and completion markers;
- fresh-process execution, with checkpoints/preloaded theorem state forbidden.

Execution invokes the pinned runtime directly with the pinned `hol.ml`, exact
reference include path, and `-noprompt`. It uses a recorded allowlist
environment, including exact HOL root, runtime-library directory, and OCaml
toplevel directory, rather than inheriting arbitrary caller variables.

The collector refuses execution unless its own repository is clean and the
collector file equals the recorded HEAD version. It then launches the pinned
reference runtime itself, supplies the
generated request on standard input, captures combined output, and rechecks all
pins and git cleanliness after exit. The target file(s), serializer, and
theorem requests run in that order. Fingerprint records are accepted only
between the nonce-bound start and completion markers. Missing/duplicate markers,
a record outside that interval, a nonzero exit, missing/extra fingerprint
records, inconsistent global axioms, or any changed pin fails collection.

## Commands

Generate and inspect a plan without starting HOL Light:

```sh
python3 candle/reference_fingerprints.py plan \
  --target 100/gcd \
  --reference-root /project/repos/hol-light \
  --runtime /project/repos/hol-light/ocaml-hol \
  --runtime-stublib /project/repos/hol-light/_opam/lib/stublibs/dllzarith.so \
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
  --runtime /project/repos/hol-light/ocaml-hol \
  --runtime-stublib /project/repos/hol-light/_opam/lib/stublibs/dllzarith.so \
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
  /tmp/gcd-reference-candidate.json \
  --plan /tmp/gcd-reference-plan.json \
  --request /tmp/gcd-reference-request.ml \
  --transcript /tmp/gcd-reference.log
```

## Deliberate promotion barrier

The candidate schema is `candle-s1-reference-candidate-v3`, its approval status
is always `candidate_unapproved`, `promotion_allowed` is always false, and
observations remain `observed_uncompared`. Identities are nested under
`candidate_identities`; the object has a different shape from the exact
two-field `EXPECTED_IDENTITIES` value. Manifest generation and the runner both
reject the candidate object as malformed if it is pasted into the expected
identity table.

The candidate binds the canonical JSON plan, exact request, and complete
transcript by SHA-256. Offline validation now requires all three artifacts and
reconstructs the complete candidate from them; a changed plan, request,
transcript, nonce, or fingerprint record fails validation. It also recomputes
the reference, runtime, library-tree, dynamic-library, and collector pins from
the current filesystem, so validation fails if the recorded execution closure
is no longer present exactly.

There is intentionally no candidate-to-expected conversion command. An
independent review must establish reference suitability, inspect theorem and
global-axiom identities, preserve provenance separately, and explicitly enter
only the approved expected object in a reviewed commit.

## Current limitations

- Fresh-process isolation is enforced by spawning the pinned runtime directly,
  but it is not a proof that the runtime implementation is trustworthy.
- Direct target files are hash-equal to the manifest. Transitive dependencies
  are pinned collectively by the clean reference git commit, not enumerated in
  the candidate.
- The OCaml and runtime-stub closures use deterministic whole-tree digests
  rather than embedding thousands of individual file hashes in the plan. The
  inventory algorithm is versioned in the plan and any name, kind, mode,
  symlink target, resolved symlink content, or regular-file content change
  changes the digest.
- Reference and Candle `hol.ml` may differ. The candidate records reference
  `hol.ml` and global axioms so that difference is visible; suitability still
  requires review.
- Source-normalized compatibility targets may intentionally differ from the
  reference target file and will fail planning until that difference receives
  an explicit, separately reviewed policy. The tool has no bypass flag.
- The structural serializer preserves free and type-variable names. Its
  cross-runtime canonicality remains an acceptance assumption to validate on
  reference/Candle differential samples before approving all 65 identities.
- The first wrapper-based GCD attempt failed closed before HOL initialization;
  a direct-runtime initialization smoke and one schema-v2 GCD collection then
  passed. Independent review found its identity coherent but rejected it for
  promotion because its runtime closure was incomplete, it used the
  PFT-instrumented kernel, and no Candle differential sample existed. That
  historical candidate remains review-only. A schema-v3 candidate must still
  be repeated on pristine upstream HOL Light and matched against Candle before
  any identity can be considered for approval.
