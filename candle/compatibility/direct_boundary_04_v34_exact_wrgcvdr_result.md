# Direct Flyspeck boundary 04: v34 exact WRGCVDR result

Date: 2026-09-12 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim. No qualified Great100 byte was
changed.

## Exact action result

The fresh cumulative v34 replay at Candle source commit
`8b8095c58929887c550108d785a6aa9f3776d3a9` emitted exactly one authenticated
preflight marker and exactly 79 unique nonce-bound action-success markers for
indices 000--078, in order. Their identities equal the first 79 actions in the
exact instrumented prefix. Action 079, `local/WRGCVDR.hl`, was reached and
failed before its success marker; no later action was reached.

The exact DEVELOPMENT / NON-RELEASE headline is therefore:

```text
actions reached: 80
actions passed:  79
passed indices:  000--078
current boundary: 04-geometry-through-151
```

The process exited zero under the development REPL's source-error behavior
after 1:10:38 and used a maximum 4,468,352 KiB RSS. No boundary-success marker
was emitted.

## First genuine failure

Candle selected the authenticated v34 normalized WRGCVDR source and reported a
`thm` versus theorem-producing function type mismatch while underlining the
following `X_IN_HYP_ORBITS` binding. With the earlier line-75/76 parser effects
already normalized, the remaining source item is the unbound theorem-valued
`prove(...)` expression at original line 238. The independent v35 fixture
reproduces this exact module-structure class and validates the explicit
wildcard-binding repair without changing the theorem or proof.

The immutable exact failure receipt is:

```text
/project/flyspeck-candle-runs/v34-dev-direct-boundary04-8b8095c-attempt-001/development-failure-receipt.json
SHA-256 75eaf13f1aea18e831fd522b26d8fbcb6ccf3f8669cdc200106f0a20c44f29f5
```

Key preserved artifacts are:

- preparation receipt SHA-256
  `89ba4bbf4d85bd45f5ef01a771a5648ae25b4cedefa4d80ec506d9c1bb30f35a`;
- exact instrumented prefix SHA-256
  `ab574250806c794ad2cc0bf70b12a31cc1d01f05ebe2d964d4411af24ec959e2`;
- runtime configuration SHA-256
  `5fc39db1cfe6a7b24c399fdbd8eded4ade2ebe0a1a643a41c5dd077a33ed02a7`;
- transcript SHA-256
  `e6c79d3565168387d059c93a9b91898d5b15f43750b944eba0ed1415f888cb1a`;
- usage report SHA-256
  `32e72122b9e34f083ba33149ae971c37bfa097301800eb3e65e5e332918629b8`.

## Consequence

The v34 integration independently validates the action-070 EMNWUUS and
action-072 SLTSTLO term-order fixes through action 078. It does not validate
the later action-083, action-126, or any dirty-run candidate. The next exact
cumulative replay must start at action zero on the committed v35 source that
combines the independently validated WRG theorem-effect and ssreflect
term-`setify` compatibility repairs.
