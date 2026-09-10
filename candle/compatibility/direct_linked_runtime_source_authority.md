# Direct linked-runtime source authority

This is a development-only correction to the schema-5 cumulative Flyspeck
runner.  It does not alter the qualified S1 Candle source, runtime, reports, or
evidence, and it does not make an S2/S3 or release claim.

## Actual-run failure

The first run at Candle commit
`5b5a955f9077e8680fdbedc2afdb299b7e3a07b7` accepted the relocated logical
request for `hol.ml`, then failed before action zero when `hol_lib.ml` issued:

```text
loads "candle/build/insulate.ml";;
```

The trace table bound the authenticated snapshot copy only by its absolute
path, so the loader rejected the lexical request with
`unauthenticated Candle source trace path: candle/build/insulate.ml`.  The
immutable failed receipt is
`/project/flyspeck-candle-runs/v14-stratum-base-5b5a955-attempt-001/receipt.json`
(SHA-256
`ce6f52563b055d43eeb6d966743eee630803ca3a5f127456804e1a8760ff026e`).
It reports zero validated action markers and a postflight-authenticated failed
state.  Later missing-source and undefined-value messages are cascades after
the interactive loop continued past the first exception.

## Bounded correction

The runner now derives the complete linked-build loader-source class instead
of adding a special-case spelling for `insulate.ml`.  A member must be:

- a standalone `generated-contract` source action in the authenticated
  manifest;
- present exactly once in its authenticated parent source dependency list;
- under the canonical repository-relative `candle/build/` namespace;
- an exact ordinary, single-link file named by the already validated linked
  provenance output set; and
- byte-identical to that output's recorded length and SHA-256.

The derived runtime authority binds artifact role, source key, repository,
logical relative request/canonical/selected paths, MD5, and SHA-256.  The
attempt separately binds the linked-provenance record, and the logical source
closure must still contain the exact generated executed-control set.  Path or
parent substitution, missing linked outputs, changed bytes, symlinks, and
hard-link aliases fail closed.

The real-plan relocation dry-run was tightened at the same boundary.  It now
invokes the runner's complete `validate_plan`, compares its reconstructed
trace contract with `attempt.expected_physical_source_trace`, rederives the
observed trace from the receipt-bound log and compares it with
`receipt.physical_source_trace`, and includes the boundary's actual structural
fingerprint requests when rebuilding both contracts.

Focused development tests cover the valid linked-runtime derivation and the
adversarial cases above, plus relocated logical identity stability.  The
source-trace, direct-runtime, stratum-plan, and LP-consumption suites pass 69
tests in total.  A fresh schema-5 actual run remains required to locate the
next functional boundary.
