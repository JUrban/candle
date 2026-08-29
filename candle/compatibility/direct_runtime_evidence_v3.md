# Direct runtime evidence v3

This is the historical schema-3 contract. Newly generated attempts use
[direct runtime evidence v4](direct_runtime_evidence_v4.md), which adds the
loader-owned physical source trace needed to close the nested-execution gap.

This contract strengthens the compiled cumulative Flyspeck runner without
promoting an attempt to S2 or S3.  Schema-2 attempt and receipt artifacts remain
permanently non-promotable; the changed action and source-closure protocols are
emitted only by schema 3.

## Action outcomes

Every completed outer action emits its exact index, authenticated original
source SHA-256, the canonical SHA-256 of its exact logical-ledger delta, and one
outcome.  The delta is written in final list-prefix order: normally `[outer]`;
for action 295 it is exactly `[serialization, update_database_400]`.

- `load`: the original logical identity was absent and became the unique new
  head of the logical ledger; or
- `skip-ledger`: the directive performed no evaluation because that exact
  logical identity was already present.

The former `skip-loader-cache` case is rejected inside the compiled process. It
meant that the private physical-path cache skipped a file while its original
logical identity was absent, so it could not establish the required source
execution.

The CakeML boot dependency `0e97a1ab8` keeps pending logical identities on a
LIFO stack parallel to nested source evaluation.  Thus the selected nested
`#flyspeck_loadt "general/update_database_400.ml"` commits first and the outer
serialization identity commits second, producing the declared final prefix.
Evaluator failure clears the whole pending stack.  The setup transition then
accepts only the complete authenticated prefix; a reordered, missing, extra,
or skipped nested delta fails before its action marker.

`test_exact_setup_action_transition_runs_in_compiled_ocaml_fixture` extracts
the exact production transition definition from `flyspeck_stratum_setup.ml`,
compiles it with pinned OCaml 4.14.1, and exercises `load`, `skip-ledger`, the
two-record serialization/update400 prefix, and the physical-cache/logical-
ledger mismatch failure.  CakeML's separate exact-source fixture compiles the
production identity-stack functions and proves nested push/commit order,
complete drain, and underflow rejection.  These are exact unit fixtures; a new
linked CakeML build and full attempt are still required for runtime evidence.

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
one of `observed-outer-source`, `observed-nested-source`, `expected-nested-source`,
`generated-executed-control`, or `derivation-only-input`, original
SHA-256/MD5, and optional normalization id and output SHA-256/MD5.  The
instrumented cumulative prefix, not `flyspeck_full_build.ml`, is executed; its
own digest is bound separately as an attempt control input.  The
compiled process emits every record in that order followed by a nonce- and
boundary-bound terminal marker.  The host reparses the exact records and
independently recomputes their canonical SHA-256.

This is a **manifest-derived logical reachability closure** with ledger
observation for outer actions and selected nested `#flyspeck_loadt` actions.
In particular, `update_database_400.ml` becomes `observed-nested-source` only
after action 295.  Ordinary nested `needs` / `loads` remain expected graph
reachability: their private physical cache does not export logical identities.
The closure therefore still cannot self-certify complete nested execution and
remains deliberately nonpromotable.  Closing that hard blocker requires a
newly built verified boot to export nonce-bound authenticated events for every
selected nested load (or equivalent exact evidence), not merely the selected
`loadt` subset.

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
