# Direct runtime evidence v4

Schema 4 supersedes direct runtime evidence v3 for newly generated cumulative
Flyspeck attempts. It remains diagnostic and nonpromotable: it does not itself
grant S2 or S3 approval.

The v3 logical closure described selected reachability but could not prove that
every ordinary nested `needs` or `loads` edge executed. Schema 4 adds one
loader-owned, nonce-bound physical source-trace session. The authenticated
runtime configuration is the sole pre-trace enabler; every later source
directive, beginning with setup and ending with the postlude, must appear in
the trace.

## Exact source bindings

Before execution, the host derives a sorted table for every allowed resolved
path. Each row has a canonical-JSON SHA-256 binding id and binds:

- the resolved, canonical, and selected absolute paths;
- the logical source key and canonical basename;
- the original MD5 and SHA-256;
- the selected SHA-256; and
- the normalization id, or `-` for unchanged input.

Lexical aliases for one logical key must agree on every field except their
resolved path and binding id. The required logical-key set is exactly the v3
closure minus derivation-only inputs, plus setup, the instrumented prefix, the
stratum check, the postlude, and the fingerprint serializer when requested.
The trace contract cannot omit a selected logical source or add a different
logical key.

## Loader-owned events

The linked CakeML loader emits one request before it selects a source action,
then one outcome after that action completes. Requests carry a consecutive
integer id, their exact active parent, directive kind, binding id, logical key,
bound metadata, and whether the canonical physical path was already cached.
Outcomes are `evaluated` or `cache-skip`. Only `needs` and
`#flyspeck_needs` may skip, and only when the canonical path was already in the
loader cache; `loads` and `#flyspeck_loadt` always evaluate. `#use` always
evaluates and does not add its path to the needs/loads cache.

The host independently replays the LIFO request tree and canonical cache. It
requires the exact top-level order `setup`, `instrumented-prefix`,
`stratum-check`, `postlude`; exact coverage of every required logical key; and
one final terminal event after the stack is empty. Missing, extra, reordered,
cross-parent, duplicate, metadata-forged, cache-forged, failed, or unterminated
sessions are rejected. The validated event list and its canonical SHA-256 are
retained in the receipt.

## Compatibility and claim limit

Schema-3 and partially upgraded artifacts do not satisfy the schema-4
validator. The v3 action markers and logical-closure records remain in v4 so
the physical observation is checked against both the authenticated action
projection and the path-independent logical model.

Even a successful evidence-v4 receipt remains explicitly `s2_s3_evidence:
false`. Promotion still requires a freshly linked CakeML binary containing the
trace implementation, semantic comparison against independently approved
reference sweeps, clean repeated runs, and the remaining release gates.
