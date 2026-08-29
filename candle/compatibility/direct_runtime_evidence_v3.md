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

`test_exact_setup_action_transition_runs_in_compiled_ocaml_fixture` extracts
the exact production transition definition from `flyspeck_stratum_setup.ml`,
compiles it with pinned OCaml 4.14.1, and exercises `load`, `skip-ledger`, and
the physical-cache/logical-ledger mismatch failure.  This is an exact unit
fixture for the transition function, not a claim that a linked CakeML run has
yet emitted nested loader events.

## Selected logical source closure

The runtime independently reconstructs a path-independent ordered closure from
the authenticated manifest.  It contains:

1. the two bootstrap roots and their selected resolved nested dependencies,
   including the three selected standalone `strictbuild.hl` `loadt` actions;
2. every completed outer action and its selected resolved nested dependencies;
3. the generated controls actually consumed by setup/bootstrap,
   `candle/build/insulate.ml` and `candle/flyspeck_source_digests.ml`;
4. the source-integrity harness and, as a derivation-only input, the
   authenticated `flyspeck_full_build.ml`; and
5. at the final boundary, the direct L2 target loaded by the postlude.

`strictbuild.hl`'s `build/use_serialization.hl` dependency is not a selected
execution edge.  `general/serialization.hl` enters only after outer action 295,
and its pinned OCaml 4.14.1 branch selects `update_database_400.ml`, never
`update_database_310.ml`.

The executing `flyspeck_loader.ml` is excluded because the stratum runner uses
`flyspeck_stratum_setup.ml`, not that full-loader entry point.  Records use the
declared `canonical-source-key-lexicographic-v1` order and bind the source key,
one of `observed-outer-source`, `expected-nested-source`,
`generated-executed-control`, or `derivation-only-input`, original
SHA-256/MD5, and optional normalization id and output SHA-256/MD5.  The
instrumented cumulative prefix, not `flyspeck_full_build.ml`, is executed; its
own digest is bound separately as an attempt control input.  The
compiled process emits every record in that order followed by a nonce- and
boundary-bound terminal marker.  The host reparses the exact records and
independently recomputes their canonical SHA-256.

This is a **manifest-derived logical reachability closure**, justified by the
authenticated source graph and successful outer-action ledger.  It is not a
loader-owned observation of nested source execution and cannot self-certify
that execution.  The verified boot's ordinary `needs` / `loads` cache is a
closure-local string list; only the custom outer actions update the exported
logical-identity ledger.  Closing this hard promotion blocker therefore
requires a newly built verified boot to export nonce-bound, authenticated
nested load events (or equivalent exact evidence).  Re-emitting this expected
closure is deliberately marked nonpromotable until then.

That future trace also needs a single lexical-to-canonical identity resolver.
The first `..` outer target occurs at action 126
(`../jHOLLight/caml/ssreflect.hl`), and action 145 begins the
`../formal_lp/...` targets, some of whose selected sources use normalization
overlays.  The current logical-identity and overlay tables are canonical-path
based; comparing those lexical spellings directly would create false misses.
Until aliases and overlays converge through an authenticated canonical
resolver, nested execution remains a hard blocker.

## Generated theorem-digest output

The selected run uses `Serialization` only for in-memory canonical identities.
Its historical `Filename.temp_file` allocation and deferred `save_all` /
`load_digest_file` route are not selected build actions.  The exact normalized
source therefore performs no temporary-file allocation at module load and
makes both deferred output operations fail closed.  Reintroducing theorem-
digest output requires a separately versioned, attempt-local, atomic generated-
output contract.

This source normalization intentionally changes diagnostic stdout by removing
exactly the two lines emitted by Candle's `Filename.temp_file` implementation:
`TODO Filename.temp_file (just concats temp dir, prefix, suffix)` and
`TODO Filename.get_temp_dir_name (always returns /tmp)`.  It does not claim
byte-for-byte stdout preservation.  The preservation claim is limited to the
selected proof state, source-action semantics, and semantic fingerprints; any
consumer of those diagnostics is outside the declared scope.

No evidence-v3 artifact approves a semantic identity.  Independent reference
approval, two clean full runs, checkpoint/resume qualification, nonlinear/LP
coverage finalization, and an external authorization remain separate gates.
