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
- an exact pin for the findlib executable and configuration plus versioned
  whole-tree inventories for every configured package-search root; the runtime
  receives the exact recorded `OCAMLFIND_CONF` and no inherited `OCAMLPATH`;
- exact pins for the recursively resolved ELF dependency closure of the
  bytecode interpreter and every `.so` in the selected local and system OCaml
  stub directories, including the dynamic loader, libc, libm, GMP, and any
  transitive native libraries those candidate stubs can select on the current
  host;
- the collector repository commit, status, committed collector hash, and an
  assertion that the executing collector equals that committed file;
- the probed OCaml compiler version;
- manifest-equal hashes for every ordered target load file, or the historical
  side of exactly one of the three hash-pinned, review-required deltas in
  `reference_source_contracts.json`;
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
  --ocamlfind /usr/bin/ocamlfind \
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
  --ocamlfind /usr/bin/ocamlfind \
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

Pass `--source-mode historical-original` only with the reference tree at exact
upstream commit `3170739521d88d04580f61385c95b497690b7002`.  That mode accepts
only the historical side of the three recorded deltas; it is not a generic
source-hash bypass.  The selected sides coexist at exact reference commit
`1258c129c3ddf0b239b649ba7024eab677cd953b`. That audit commit has the pinned
historical upstream commit as its sole parent, and its complete Great-100 diff
is exactly the three recorded paths. Keeping the reference runtime and all
transitive sources at the historical upstream tree avoids using Candle's
deliberately reduced compiled-runtime loader as an OCaml reference loader. The
default is `manifest-exact`. An approval may use only reference runs at that
exact-source commit and must reproduce the committed source-contract policy
field for field.

## Deliberate promotion barrier

The candidate schema is `candle-s1-reference-candidate-v6`, its approval status
is always `candidate_unapproved`, `promotion_allowed` is always false, and
observations remain `observed_uncompared`. Identities are nested under
`candidate_identities`; the object has a different shape from the exact
approved identity object. Manifest generation and the runner both
reject the candidate object as malformed if it is pasted into the expected
identity table.

The candidate binds the canonical JSON plan, exact request, and complete
transcript by SHA-256. Offline validation now requires all three artifacts and
reconstructs the complete candidate from them; a changed plan, request,
transcript, nonce, or fingerprint record fails validation. It also recomputes
the reference, runtime, library-tree, dynamic-library, and collector pins from
the current filesystem, so validation fails if the recorded execution closure
is no longer present exactly.

There is intentionally no candidate-to-expected conversion command. Two
fresh, nonce-distinct reference candidates must agree for every target. An
independent reviewer must establish reference suitability, inspect the exact
three source deltas, and create `top100_identity_approval.json`. An approved
artifact must retain ordinary-file path/byte/SHA records for both candidates,
plans, requests, transcripts, and source contracts; manifest regeneration
rehashes every attachment. It also parses every exact schema-v6 plan and
candidate, mechanically calls `validate_candidate` with the retained request
and transcript bytes, regenerates the nonce-bound request, and requires the
replayed identity projection to equal the independently approved theorem and
post-state identity. Target, selected-source list, reference HEAD, session
nonce, serializer, collector, and exact source-contract policy are
cross-bound. Arbitrary hash-consistent attachment text therefore cannot become
an approval. The unapproved committed template contains no identity data and
keeps the 65-target runtime gate disabled.

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
- The historical source mode recognizes exactly three compatibility deltas.
  Equivalence remains an independent review obligation; a matching hash is not
  a proof that a source rewrite preserves theorem behavior.
- The structural serializer preserves free and type-variable names. Its
  cross-runtime canonicality remains an acceptance assumption to validate on
  reference/Candle differential samples before approving all 65 identities.
- The first wrapper-based GCD attempt failed closed before HOL initialization;
  a direct-runtime initialization smoke and one schema-v2 GCD collection then
  passed. Independent review found its identity coherent but rejected it for
  promotion because its runtime closure was incomplete, it used the
  PFT-instrumented kernel, and no Candle differential sample existed. That
  historical candidate remains review-only. A later schema-v3 pristine run
  matched the earlier identity exactly, but a critical re-review found that
  findlib's configuration and first package-search root were not pinned. It too
  remains review-only. A schema-v4 plan then pinned findlib selection but was
  not executed; a final critical pass observed that system OCaml stub files
  were tree-pinned while their ELF dependencies were not enumerated. A
  schema-v6 candidate must repeat the pristine run, include the full structural
  post-state identity, and still match an independent second reference run
  before any identity can be considered for approval.
