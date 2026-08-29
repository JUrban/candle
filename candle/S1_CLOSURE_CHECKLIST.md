# Great 100 S1 evidence closure checklist

Snapshot: 2026-08-28, before any fingerprint closure rerun.

## Current evidence boundary

- The audited inventory has 65 clean-process targets over 66 source files and
  requests 97 named theorem values.
- All 65 mappings are source-audited. `100/cantor` uses the final visible
  post-load binding, and broad `100/fourier` conservatively requires all four
  independently headlined culmination results. `100/piseries` is pinned to the
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

Use `candle/reference_fingerprints.py` as documented in
`candle/S1_REFERENCE_COLLECTION.md`; its output is deliberately an unapproved
candidate and cannot be consumed as an expected identity object.

1. Recheck the approved named theorem boundaries against the pinned sources.
2. Pin the reference source commit, clean/dirty status, load-file hashes,
   ordered load files, executable/runtime identity, and serializer SHA-256.
3. Load `hol.ml` and the target files in a fresh process with no theorem-state
   reuse, then request every named result in manifest order.
4. Capture, for every theorem, the theorem, sorted hypotheses, conclusion, and
   sorted global-axiom SHA-256 identities plus both counts.
5. Repeat collection with a distinct 256-bit nonce and require exact identity
   equality. Preserve both linked evidence sets and have an independent
   reviewer create `top100_identity_approval.json`. Never promote hashes
   observed first from the Candle-under-test run into their own expectations.

The expected object for one target has exactly this shape:

```json
{
  "approval_sha256": "<exact independent approval artifact sha256>",
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
  ],
  "post_state": {
    "kernel_state_sha256": "<sha256>",
    "type_constants_sha256": "<sha256>",
    "type_constant_count": 0,
    "term_constants_sha256": "<sha256>",
    "term_constant_count": 0,
    "definitions_sha256": "<sha256>",
    "definition_count": 0,
    "global_axioms_sha256": "<sha256>",
    "global_axiom_count": 3
  }
}
```

The approval artifact itself omits `approval_sha256` from each
`expected_identity`; manifest generation injects the artifact hash after
validation, avoiding a circular self-hash.

## Candle rerun scope

The load-only baseline itself need not be repeated solely to obtain timing.
Every target does need a fresh-process Candle run after its compatibility fixes
are integrated, because a theorem fingerprint must be captured in the same
process and state that loaded the theorem.

- Rerun the 65 audited targets individually or as one sequential suite with
  fingerprint capture enabled. A targeted run is sufficient evidence if it
  pins the same source/executable/serializer contract and preserves fresh
  process isolation.
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
- schema-6 linked provenance, clean pre/post Git and runtime state, exact
  65/66/97 source closure, executable/manifest/runner/launcher/serializer
  identities, transcript byte identity, timeout policy, and complete resource
  sampling are present in the report;
- mapping status is `audited`, every requested theorem appears exactly once,
  and no unexpected theorem record appears;
- observed theorem order and all seven record fields exactly equal the approved
  expected records;
- every theorem request in the target sees the same global-axiom identity and
  count;
- the post-load type, constant, primitive-definition, and global-axiom tables
  exactly match the independently approved structural state identity;
- fingerprint report status is `matched` and
  `expected_identities_present` is true;
- no load-only pass, `observed_uncompared` record, missing fingerprint, timeout,
  manual-review mapping, or self-derived expected hash is counted as S1.

## Suite closure report

The final S1 report must contain all 65 ordered targets and state separately:

- load results and compatibility failures;
- mapping readiness (65/65 audited today);
- expected identity coverage (0/65 today);
- observed fingerprint coverage and exact matches;
- invalidated/stale targets caused by identity changes;
- exclusions (`100/sqrt.ml` remains unreviewed for Great-100/Flyspeck scope).

The schema-4 runner also requires nonce-bound ordered suite/start/linked/
complete markers, an ordinary zero process exit, a persistent report/log
directory, and a positive total wall deadline. It exits nonzero unless
`suite_closed` is true.

After approval and a schema-6 linked build, a canonical low-parallelism launch
is:

```sh
python3 -I candle/regression.py --top100 -j 1 \
  --inactivity-timeout 1800 --wall-timeout 14400 \
  --json-report /absolute/new/great100-run.json \
  --log-dir /absolute/new/great100-run-logs
```

The report path must not exist. The committed approval template is currently
unapproved, so this command intentionally fails before starting Candle today.

The controller rehashes the clean source/runtime contract before and after
every process and rehashes each retained transcript again while writing the
report. It does not provide OS-level isolation from a hostile same-UID process
that transiently replaces a source after the precheck and restores it before
the postcheck; excluding such interference is an explicit host trust
assumption. Kernel-state fingerprints make an accidental semantic substitution
observable but are not a substitute for sealed filesystem execution.

The Candle source wrapper retains the primitive definition theorem returned by
each `new_basic_definition` call solely to reproduce HOL Light's
`definitions()` audit view. Definition construction remains in the verified
CakeML kernel. This observational registry and the structural serializer have
not yet been exercised by a compiled 65-target run, so this work does not by
itself establish S1, S2, or S3.

Suite S1 closes only at 65/65 load passes, 65/65 approved mappings, 65/65
expected identity sets, and 65/65 exact matches, with zero skips, mismatches,
timeouts, stale identities, or unexplained global axioms.
