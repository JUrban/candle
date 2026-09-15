# Direct boundary 04: cumulative actions 000--151

Status: DEVELOPMENT / NON-RELEASE cumulative pass. This is functional direct-
Flyspeck evidence, not S1 archival evidence or an S2/S3 release claim.

## Result

A fresh action-zero replay completed every cumulative action from 000 through
151: 152 authenticated `CANDLE_FLYSPECK_STRATUM_ACTION_OK` records with no
missing or duplicate index. The final source was
`text_formalization/local/lp_details.hl`; its terminal
`Lp_details.quad_3862621143_revised` theorem was bound, the action-151 record
was emitted, and the instrumented prefix reported that it had finished
loading. A scan of the complete log found no error, exception, failure,
stack-overflow, too-deep, or timeout diagnostic.

The run exited 0 after 1:38:29 wall time, with 17,095,680 KiB maximum resident
set size. Its immutable development artifacts are under:

```text
/project/flyspeck-candle-runs/v81-dev-direct-boundary04-d6f7162-attempt-001
```

The attempt nonce is `d78e1fb19ed93fce16898f5e5fecf9a3`. The run used
Candle project commit `d6f71626063f5baeb515e2fa85707f55730cd7f8` and the
unchanged Flyspeck source commit
`1ce0353008eba83d3c76ae9a25c3c242e4802d53`.

Artifact SHA-256 identities:

- complete log: `ba4f791a5d6b49b283279058eae20a0ed49c443dfc1a6aee83c75ffe841d4006`
- instrumented prefix: `ae491c1f2585300388c5bd7a1209107a40c3f846ee4146e2ce5952b7a6790375`
- stdin launcher: `096b485c5c64642a374f393c0cae16c06e8f58f6f36a4bda3a6d88bf8fe4b560`
- preparation receipt: `cb84f3da96b90c23b19ebad77a23a2c2aa037f44fd0d883f26acf528e87b1eb0`
- runtime configuration: `c12f865baffda8574412396b79445285edc9fa9ea90c33160a629294942a3bf9`

## Consequence

The cumulative geometry boundary is green. This replay includes the repaired
GRUTOTI native set-tactic binding scope and therefore independently confirms
that the earlier local proof workaround is unnecessary. The demonstrated
GRUTOTI cause remains transitive-open name resolution; no comparator-ordering
or pointer-equality diagnosis is carried forward for that incident.

The next direct action is 152, `formal_lp/hypermap/arith_link.hl`. Subsequent
focused development has loaded its complete source from a separately copied
clean predecessor and is documented in
`direct_boundary_05_v49_action152_arithmetic.md`. That focused pass is
explicitly non-release and does not alter this cumulative result or confer an
action-152 marker.
