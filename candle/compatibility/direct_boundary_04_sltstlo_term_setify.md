# Direct Flyspeck boundary 04: SLTSTLO term `setify`

Date: 2026-09-12 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct progress

The completed v33 exact cumulative run reached 80 actions and passed 79.
Actions 000--078 are exact-green, including this batch's action-072
`SLTSTLO.hl` normalization. The run emitted one authenticated preflight marker
and 79 unique nonce-bound success-marker bases exactly equal to the first 79
markers in its instrumented prefix. Its immutable DEVELOPMENT / NON-RELEASE
failure receipt has SHA-256
`e0b1507d883e6c088143d6d8d31220bfe407ccd65ee668d5fae40336ad0e52e1`.

Action 079, `text_formalization/local/WRGCVDR.hl`, is the first genuine
failure. Candle reports the independently reproduced bare-structure-effect
mismatch at diagnostic line 67. Action 080 was not reached. Cumulative
boundary 04, full direct S2, and nonlinear/LP S3 remain open.

## Complete shared-class review and bounded normalization

Neither `origin/fix-top100` nor `upstream/fix-top100` contains SLTSTLO source
or a patch for this helper, and relevant historical direct branches contain
no normalization for it. The Flyspeck history contains the same unary call
from the file's initial 2011 addition, with no later compatibility repair.

The exact corpus has four textual `setify (flat vss)` occurrences. Three are
active copies of the same `seans_fn` helper: `EMNWUUS.hl`, `OXLZLEZ2.hl`, and
`SLTSTLO.hl`. The fourth is inside a block comment in `trig2.hl`; its action
031 already passed exactly. The live shared failure class is therefore fully
enumerated, and v33 adds the missing third active site.

`map frees (tm::tms)` produces `term list list`, so `flat vss` is a
`term list`. Native Flyspeck's unary `setify` uses OCaml structural ordering;
Candle's verified HOL library requires the comparator explicitly. The v33
contract supplies its canonical HOL-term strict order at exactly line 27:

```text
let vs = setify (flat vss) in
let vs = setify Term.(<) (flat vss) in
```

The existing independent native/Candle ordering oracle covers every HOL-term
constructor and duplicate removal. The exact-shape packing fixture reproduces
Candle's original mismatch and verifies that the normalized form returns the
expected ordered, deduplicated `dest_var` list. No theorem statement,
hypothesis, proof, tactic, geometric definition, proof intent, or axiom is
changed.

The exact source/output identities are:

- source SHA-256
  `f3d683fb2d3d8b2f49cfea798f7cb66b8d20f23efb530bd1b86519727b70e346`,
  MD5 `fe92d9638666ccb6e6b8ec82d8c5bf86`, 137,457 bytes;
- normalized SHA-256
  `c2acbede83d2b6d5e8bec9cff266bba4394883be3c3de8ff2545b52c8b4c56f2`,
  MD5 `78e1641aace383531357719f10fa90cb`, 137,466 bytes.

## Focused validation

- focused Candle original rejection and normalized acceptance: PASS;
- existing exact native/Candle term-order and duplicate-removal oracle: PASS;
- normalization unit tests: PASS, 18/18;
- manifest unit tests: PASS, 28/28;
- parser descriptor identities: PASS, pilot 20/20 and all-inventory 400/400;
- normalization contract check: PASS, 53 unique-path entries;
- manifest fixed point: PASS, 297 roots, 400 source nodes, 43 generated
  inputs;
- exact cumulative replay: PASS at action 072 and through action 078;
- JSON parsing and `git diff --check`: PASS.

The v33 derived authority identities are:

- normalization contract SHA-256:
  `dd76673b0abb8a10532c56cc21687b78531a4961e613c9d670ada2a38d37eb85`;
- manifest SHA-256:
  `43d23beaff01aedad5c47384b44fbc7f049b95555c10e468e4356f26a853b588`;
- pilot descriptor SHA-256:
  `5c64298def0c12cc5ac5988e02977f88a400a2383fa4cb1e7649449ff281e906`;
- all-inventory descriptor SHA-256:
  `589f0432006a300d15571be5366f1b8c4ca1a052a66f7f7fd45d67b994351485`;
- ordered effective/prepared SHA-256:
  `15db349e1ad4e7cde16c06395665196840457f24f8e5544840ac1241d1cca980`
  / `60d9fd05337e3eebe3af61977de06be5c82db37a93f0e4d7ec69886527cf82d8`;
- effective loader action-site SHA-256:
  `64b0eeae41dc5722db0993a3a83b49879decc3ff4c60476d70c9eb73186a0c63`;
- generated source-digest/full-build MD5:
  `e5e86981343d83b8c7e2bd375070d240` /
  `56625dea3db477659e01cb302a8a9e95`.

## Next exact boundary work

The exact replay validates v33 and independently exposes action 079. The
action-079, action-083, and action-126 repairs are integrated with this batch
on committed v34 head
`8b8095c58929887c550108d785a6aa9f3776d3a9`. A fresh cumulative v34 replay
is now running from action zero; it alone can credit those later repairs.
