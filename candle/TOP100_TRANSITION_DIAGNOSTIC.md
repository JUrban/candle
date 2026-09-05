# Great 100 transition diagnostic

`regression.py --top100-transition-diagnostic` runs the complete ordered
65-target / 66-source / 97-theorem fingerprint comparison against an
authenticated schema-7 transition-linked Candle runtime.  Its purpose is to
find compatibility or identity failures before paying for a new canonical
bootstrap at the final Candle commit.

This mode is not S1 evidence.  Its report uses the distinct suite name
`top100-transition-diagnostic`, records `promotion.eligible` and
`promotion.s1_evidence` as false, and leaves `s1_evidence.suite_closed` false
even if every target and fingerprint matches.  Only `--top100` with an exact
schema-6 link at the clean final Candle commit can close S1.

The diagnostic retains the full-suite safeguards: a clean committed Candle
tree, independently approved identities, the exact execution and source
closures, fresh unaliased report/log destinations, nonce-bound process
markers, linked-record observation, runtime revalidation, transcript rehashes,
resource sampling, and per-target wall limits.  It additionally requires the
schema-7 record to carry the exact diagnostic-only promotion status and
byte-identical bootstrap-transition mode.  Schema 6 and schema 7 are rejected
when supplied to the other mode.

After creating and checking a schema-7 transition link, run from the clean
candidate checkout with fresh evidence paths outside that checkout:

```sh
python3 -I candle/regression.py --top100-transition-diagnostic -j 1 \
  --inactivity-timeout 1800 --wall-timeout 14400 \
  --json-report /absolute/fresh/attempt/report.json \
  --log-dir /absolute/fresh/attempt/logs
```

A zero exit status means that the diagnostic execution and all expected
fingerprints matched.  It does not change the promotion status.  The next
required step remains a canonical bootstrap rooted at the final Candle commit,
an exact schema-6 link, and a fresh `--top100` run.
