# Great 100 S1 evidence closure checklist

Snapshot: 2026-08-28, before any fingerprint closure rerun.

## Current evidence boundary

- The audited inventory has 65 clean-process targets over 66 source files and
  requests 97 named theorem values.
- 63 mappings are source-audited. Two remain manual review and cannot be S1
  accepted yet: `100/cantor` and `100/fourier`. `100/piseries` is pinned to the
  explicitly labeled “most famous special case,” `EULER_HARMONIC_SUM`.
  `100/quartic` is pinned to the final `QUARTIC_CASES`; its statement is
  identical to the preceding iff-form binding, so the last rebinding changes
  only the proof.
- All 65 `fingerprint_request.expected_identities` values are null. Therefore
  all theorem identities are missing as acceptance evidence. The two isolated
  observations for `CUBIC` and `Finale.TRANSCENDENTAL_E` are correctly
  `observed_uncompared`, not matches.
- The long live baseline runs runner commit
  `110a18d485557ae877d0cb47bb9172e6558ddf61`. That runner has no fingerprint
  helper/request plumbing. Its final report can establish load, timing, and
  resource observations only; fingerprints cannot be recovered from those
  completed processes.
- The live report is written only at suite exit. While the suite is active,
  the per-target logs are the result frontier and no partial JSON report exists.
  At this snapshot the live runner is on target 50, `100/pnt`; therefore its
  final aggregate and result table are not yet available for S1 ingestion.

## Reference identity gate

Before rerunning Candle, produce and review expected records from an approved,
pinned HOL Light reference environment using the exact
`candle/fingerprint.ml` serializer. For each target:

1. Approve the named theorem boundary. Resolve both manual-review mappings.
2. Pin the reference source commit, clean/dirty status, load-file hashes,
   ordered load files, executable/runtime identity, and serializer SHA-256.
3. Load `hol.ml` and the target files in a fresh process with no theorem-state
   reuse, then request every named result in manifest order.
4. Capture, for every theorem, the theorem, sorted hypotheses, conclusion, and
   sorted global-axiom SHA-256 identities plus both counts.
5. Review reference records before adding them to
   `top100_manifest.EXPECTED_IDENTITIES`. Never promote hashes observed first
   from the Candle-under-test run into their own expected values.

The expected object for one target has exactly this shape:

```json
{
  "serializer_sha256": "<64 lowercase hexadecimal characters>",
  "theorems": [
    {
      "name": "<manifest value path>",
      "theorem_sha256": "<sha256>",
      "hypotheses_sha256": "<sha256>",
      "conclusion_sha256": "<sha256>",
      "global_axioms_sha256": "<sha256>",
      "hypothesis_count": 0,
      "global_axiom_count": 3
    }
  ]
}
```

## Candle rerun scope

The load-only baseline itself need not be repeated solely to obtain timing.
Every target does need a fresh-process Candle run after its compatibility fixes
are integrated, because a theorem fingerprint must be captured in the same
process and state that loaded the theorem.

- Rerun the 63 audited targets individually or as one sequential suite with
  fingerprint capture enabled. A targeted run is sufficient evidence if it
  pins the same source/executable/serializer contract and preserves fresh
  process isolation.
- Defer the two manual-review targets until their result boundary is approved;
  an identity match is rejected while their mapping status is `manual_review`.
- Failed baseline targets require their narrow compatibility fix, focused
  differential tests, and then the same clean load-plus-fingerprint run.
- If a source file, direct/transitive dependency, serializer, executable, or
  global axiom set changes, invalidate and rerun every affected target. A
  serializer change invalidates all 65 expected comparisons.
- Do not parallelize a closure rerun with the current heavy baseline/bootstrap
  processes. Use the existing memory cap and an explicit total wall policy in
  addition to the inactivity deadline.

## Per-target acceptance invariants

A target is S1-accepted only when all of the following are true:

- target status is `PASS`, all requested files reach their exact finished-load
  markers, and the process is a clean isolated session;
- source commit/status, load-file hashes, executable SHA-256, serializer
  SHA-256, timeout policy, and resource evidence are present in the report;
- mapping status is `audited`, every requested theorem appears exactly once,
  and no unexpected theorem record appears;
- observed theorem order and all seven record fields exactly equal the approved
  expected records;
- every theorem request in the target sees the same global-axiom identity and
  count;
- fingerprint report status is `matched` and
  `expected_identities_present` is true;
- no load-only pass, `observed_uncompared` record, missing fingerprint, timeout,
  manual-review mapping, or self-derived expected hash is counted as S1.

## Suite closure report

The final S1 report must contain all 65 ordered targets and state separately:

- load results and compatibility failures;
- mapping readiness (63 audited today, two unresolved today);
- expected identity coverage (0/65 today);
- observed fingerprint coverage and exact matches;
- invalidated/stale targets caused by identity changes;
- exclusions (`100/sqrt.ml` remains unreviewed for Great-100/Flyspeck scope).

Suite S1 closes only at 65/65 load passes, 65/65 approved mappings, 65/65
expected identity sets, and 65/65 exact matches, with zero skips, mismatches,
timeouts, stale identities, or unexplained global axioms.
