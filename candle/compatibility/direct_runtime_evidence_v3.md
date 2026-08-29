# Direct runtime evidence v3

This contract strengthens the compiled cumulative Flyspeck runner without
promoting an attempt to S2 or S3.  Schema-2 attempt and receipt artifacts remain
permanently non-promotable; the changed action and source-closure protocols are
emitted only by schema 3.

## Action outcomes

Every completed outer action emits its exact index, authenticated original
source SHA-256, and one outcome:

- `load`: the original logical identity was absent and became the unique new
  head of the logical ledger; or
- `skip-ledger`: the directive performed no evaluation because that exact
  logical identity was already present.

The former `skip-loader-cache` case is rejected inside the compiled process. It
meant that the private physical-path cache skipped a file while its original
logical identity was absent, so it could not establish the required source
execution.

## Selected logical source closure

The runtime independently reconstructs a path-independent ordered closure from
the authenticated manifest.  It contains:

1. the two bootstrap roots and their resolved nested dependencies;
2. the four reviewed dynamic sources loaded by pinned `strictbuild.hl`;
3. every completed outer action and its resolved nested dependencies;
4. the source-integrity harness and the authenticated full-build driver; and
5. at the final boundary, the direct L2 target loaded by the postlude.

The executing `flyspeck_loader.ml` is excluded because the stratum runner uses
`flyspeck_stratum_setup.ml`, not that full-loader entry point.  Records retain
manifest order and bind the source key, original SHA-256/MD5, and optional
normalization id and output SHA-256/MD5.  The compiled process emits every
record in order followed by a nonce- and boundary-bound terminal marker.  The
host reparses the exact records and independently recomputes their canonical
SHA-256.

This is a **manifest-derived logical reachability closure**, justified by the
authenticated source graph and successful outer-action ledger.  It is not a
loader-owned trace of Candle's private physical-path cache.  That distinction
remains an explicit assurance boundary until the verified boot exports such a
trace.

## Generated theorem-digest output

The selected run uses `Serialization` only for in-memory canonical identities.
Its historical `Filename.temp_file` allocation and deferred `save_all` /
`load_digest_file` route are not selected build actions.  The exact normalized
source therefore performs no temporary-file allocation at module load and
makes both deferred output operations fail closed.  Reintroducing theorem-
digest output requires a separately versioned, attempt-local, atomic generated-
output contract.

No evidence-v3 artifact approves a semantic identity.  Independent reference
approval, two clean full runs, checkpoint/resume qualification, nonlinear/LP
coverage finalization, and an external authorization remain separate gates.
