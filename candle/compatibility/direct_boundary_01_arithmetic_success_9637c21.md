# Direct Flyspeck boundary 01 arithmetic: 38/38 action success

Date: 2026-09-11 UTC

Status: DEVELOPMENT / NON-RELEASE. This report makes no S1, S2, S3,
qualification, promotion, or release claim.

## Headline progress

- Direct Flyspeck actions reached / passed: **38 / 38**.
- Current cumulative boundary: `01-arithmetic-through-037`.
- Remaining compatibility failure classes at this boundary: **0**.
- Full direct S2: open.
- Nonlinear + LP / S3: open.

This advances the preceding exact result from 31 reached / 30 passed. The
five-expression `trig1.hl`/`trig2.hl` module-structure normalization batch is
green not only at its two directly affected actions, but through all remaining
arithmetic actions 032--037.

## Exact cumulative result

The frozen run is:

`/project/flyspeck-candle-runs/v16-dev-direct-boundary01-9637c21-attempt-002`

It used:

- Candle `9637c21bb28dac93e43ba15c96d5bd14f609b985`;
- Flyspeck `1ce0353008eba83d3c76ae9a25c3c242e4802d53`;
- the checked DEVELOPMENT / NON-RELEASE runtime built from CakeML
  `cea7c49d441c749bed4c8a987bee6d321816fbde`, binary SHA-256
  `dd8a693bc88b75b5599a91777b93629417993cdb5338bb7cb0f40d38d246190f`;
- plan SHA-256
  `a268c6185323f61cde9a87f7cecaa246e6694d73df9223f6ffc5b57fffec6b17`;
- normalization receipt SHA-256
  `26928f7dbe384a7d235b1c39b41d9fd1eec2e387399e8ded68b58d34ce2d2418`.

The transcript contains one exact nonce-bound preflight marker and 38 exact,
ordered nonce-bound action-success markers for indices 000--037. It contains
no top-level `ERROR:` or `EXCEPTION:` line. The process exited zero at EOF.
The manual harness does not execute the formal boundary-check postlude, so no
formal boundary-success marker or S2/S3 claim is inferred.

Run measurements and frozen identities:

- wall time: 48:26.49;
- maximum RSS: 4,339,328 KiB;
- result receipt SHA-256:
  `0467e5994252616d4d10bfd18dd37d572807174f13c701d06aa09854ea835daa`;
- transcript SHA-256:
  `2b5dc3322fab28a2a29d9d823ced9600dac676c9a4a4fae34ee40dd351cb0469`;
- timing SHA-256:
  `bb30536995cb7e89734072f8b53a085a9a12bf184ba22d92febd91617522a2b8`;
- preparation receipt SHA-256:
  `1e4b6ab4b20d69922eb3f8ad47da8805a50f56bca318dd8cf55928c653ed8403`.

## Preserved pre-action harness failure

Attempt 001 is separately frozen at
`/project/flyspeck-candle-runs/v16-dev-direct-boundary01-9637c21-attempt-001`.
It reached no action: its generated config carried all 38 authenticated
normalization rows but retained a historical declared count of 35. Setup
failed closed before preflight. The narrow correction mechanically derives the
declared count from the authenticated generated table; it does not alter any
runtime, Flyspeck source, normalization, theorem, proof, or qualified evidence
byte. The preserved failure receipt has SHA-256
`cca900b735cc34b69be62d0b99ee555e7edf51d871f5fe137760886aacc97daa`.

## Next boundary

The next cumulative gate is `02-nonlinear_support-through-049`, actions
000--049. It must replay from action zero and report the first genuine
Candle/Flyspeck failure if it does not produce all 50 exact action-success
markers.
