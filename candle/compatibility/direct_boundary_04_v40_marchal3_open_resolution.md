# Direct Flyspeck boundary 04: v40 Marchal3 open resolution

Date: 2026-09-12 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 runtime,
source, report, transcript, or semantic-evidence byte was changed.

## Actual direct action progress

The exact cumulative frontier remains 92 actions reached and 91 passed at
boundary 04 (`00-base-through-151`): actions 000--090 are exact-green, and
action 091 is `packing/marchal3.hl`. The first 30-action boundary remains
30/30 exact-green. Full direct S2 and nonlinear/LP S3 remain open.

The v39 exact replay passed preflight and emitted all 91 ordered nonce-bound
success markers for actions 000--090. Action 091 emitted no success marker. It
reproduced the exact distinctive v38 MESON growth sequence through 9,536,057
nodes, so it was intentionally interrupted after 1:29:25 rather than repeat
the prior 181,964,983-node run. Maximum RSS was 4,484,480 KiB. The frozen v39
log SHA-256 is
`4a1cdbf42eef933c6b1452c3a2f98b183bdccb2684f0ab4a703c091afaff8814`;
the complete bounded-interruption record is stored beside that log.

## Corrected root cause

The v39 result falsified the isolated final-tactic diagnosis. Its exact
transcript shows that many modules opened before Marchal3 leak an imported
`prove_by_refinement` member under Candle, including the late `Qzyzmjc`
module. Candle currently makes an `open`-imported member visible as an export
of the importing module. Native OCaml does not re-export a name merely
imported by `open`, so native Marchal3 retains Strictbuild's top-level
`Prove_by_refinement.prove_by_refinement` instead.

This explains both previous symptoms: the original refinement step failed in
the wrong implementation, and the later theorem wrapper never ran because the
transitive-open leak shadowed it inside `Marchal_cells_3`. The seven v38/v39
theorem-body edits were compensating at the wrong layer.

Before making this repair, `fix-top100` and the relevant historical Candle
branches were searched for Marchal3 and this construct. They contained no
Marchal3 compatibility patch. Those branches were treated only as leads; the
actual mismatch and repair were reproduced independently.

## Bounded compatibility repair

All seven v38/v39 edits to `LEFT_ACTION_LIST_3_EXISTS` are removed. The
original theorem term and tactic body are restored byte-for-byte. The sole
normalization is a 69-byte lexical binding after the complete open sequence at
the unique line-40 anchor:

```ocaml
open Upfzbzm_support_lemmas;;

let prove_by_refinement = Prove_by_refinement.prove_by_refinement;;
```

This explicitly selects the same qualified function selected by native OCaml.
It changes no theorem statement, hypothesis, tactic list, proof step, proof
intent, definition, or axiom.

The pinned upstream source remains 254,482 bytes, MD5
`ad1052eeb7d9979e8fd3069d2eb4a35c`, SHA-256
`191528d2c1dc3542751507d2b44880f3b4f07efe00ea9267b66bc10e28d21926`.
The v40 normalized source is 254,551 bytes, MD5
`75d4e4000ddf71bc004102b9c28326f1`, SHA-256
`0b7c87e5f08bd9dba862ee6b2da624e2530964ae21f22e960e45ea2f6618960a`.
An in-memory mechanical reversal of the one operation recovers the original
source exactly, and the entire source suffix beginning at
`LEFT_ACTION_LIST_3_EXISTS` is unchanged.

## Independent oracle and validation

The focused native/Candle oracle models the actual transitive-open chain.
Native OCaml selects Strictbuild; unmodified Candle selects the leaked
refinement binding; Candle with the qualified binding selects Strictbuild.
The tracked gate and its v40 runtime-root execution pass. The diagnostic-only
oracle artifacts are frozen under
`/project/flyspeck-candle-runs/marchal3-open-resolution-focused-001`; their
original/normalized SHA-256 identities are respectively
`1d8d00920f62e7ae0a367fc3a69cab4063fe035ef97a80c59116ec55619ba200`
and
`25ef36f85a2df617cca448c82d06d873cabbf3df046cd470fda29a9835038122`.

Pre-replay gates:

- Marchal3 native/original/normalized open-resolution gate: PASS;
- normalization contract check: PASS, 58 entries and 226 unique operations;
- normalization tests: PASS, 18/18;
- manifest tests: PASS, 28/28;
- manifest write/check fixed point: PASS, 297 roots, 400 source nodes, 43
  generated inputs;
- normalized full Marchal3 artifact identity and theorem-body restoration:
  PASS;
- JSON parse, shell syntax, and `git diff --check`: PASS.

The frozen implementation commit is
`6e015e37e2e43ca67f528ffae774fc2a11f7e35e`. Derived identities are:

- normalization contract SHA-256:
  `7ba583ca2958352304ea670e09e05262c9d8a34ad540c47e18602d302e5f2348`;
- manifest SHA-256:
  `ee9fab620860e70bc97750128b583a45083d0efd43b91a507bad186c5b7d1872`;
- loader SHA-256:
  `356276e7ca4c5b55f7edeb035d3f440c9b7bff1c207c2fb632eeb497714447bb`;
- generated source-digest/full-build MD5:
  `6f25df5cf05e0c09938395dda8e12d0d` /
  `0a1b7d74a9d4ee0697672e46a985398e`.

## Next work

Materialize a fresh overlay and boundary-04 plan from the final report head,
then launch a fresh exact DEVELOPMENT / NON-RELEASE cumulative replay. Action
091 receives no pass credit until normalized `marchal3.hl` completes and emits
its nonce-bound marker. If it passes, continue through actions 092--101; only
after exact action 102 is actually reached should the separately isolated
`YSSKQOY.hl` open-resolution candidate be integrated.
