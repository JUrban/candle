# Direct boundary 00--029 development attempt at cf97a2cd5

This DEVELOPMENT / NON-RELEASE attempt reached two direct Flyspeck actions and
passed one. Action 000, `general/hol_pervasives.hl`, emitted its exact
nonce-bound authenticated success marker. Action 001, `general/lib.hl`, was
invoked and failed at its next expansive polymorphic binding, `let length =`,
before its success marker. This is not schema-5 or schema-6 evidence and makes
no S1, S2, S3, qualification, promotion, or release claim. No qualified
Great100/S1 runtime, source, report, transcript, or semantic-evidence byte was
changed.

## Inputs and execution

The exact Candle source head was
`cf97a2cd530954b9cd8d17e6bae96304b570c6d2`; the CakeML runtime source head
was `cea7c49d441c749bed4c8a987bee6d321816fbde`; and the pinned Flyspeck commit
was `1ce0353008eba83d3c76ae9a25c3c242e4802d53`. The fresh 297-action plan at
`/project/flyspeck-candle-runs/v14-stratum-plan-cf97a2c-dev-001` has SHA-256
`59c6bc3a449a17699bf083b491a09ea958a378aba45ca9266d2cdb89851b2ab3`.
Its first cumulative boundary contains 30 actions. The accompanying overlay
contains the exact `rev` eta-expansion independently validated after the prior
attempt.

The attempt root is
`/project/flyspeck-candle-runs/v14-dev-direct-boundary-cf97a2c-attempt-001`.
It used the checked DEVELOPMENT / NONPROMOTABLE Cake binary with SHA-256
`dd8a693bc88b75b5599a91777b93629417993cdb5338bb7cb0f40d38d246190f`.
An independent prelaunch reconstruction matched the runtime config, 399
executed identities for 400 plan nodes, 47 aliases, 25 normalizations, 43
generated inputs, 39 LP inputs, two process inputs, and all 30 action deltas.
Trace, check, postlude, archive, publication, and fingerprint consumers were
absent, and every promotion/release claim remained false.

## Actual progress and failure

The complete strictbuild setup and authenticated `Library/rstc.ml` load passed.
The exact nonce-bound preflight appeared at log line 184121. Action 000 emitted
its exact authenticated success marker at line 184127 with disposition
`skip-ledger`. Action 001 selected and began loading the authenticated
normalized `general/lib.hl` at line 184130. The prior `rev` failure was gone;
CakeML next reported at lines 184131--184133:

```text
ERROR: Value restriction violated at line 206

let length =
```

No action-001 success marker and no later action invocation appeared. Exact
progress is therefore **2 actions reached / 1 passed**, with one authenticated
action success marker. This is the next instance of the same CakeML
value-restriction compatibility class, not a Flyspeck theorem, proof, or
mathematical semantic failure.

The run consumed 42:01.84 wall time at 99% of one CPU and reached a maximum RSS
of 4,335,744 KiB. The interactive REPL exited zero at EOF after reporting the
compile-time compatibility error; that exit does not override the missing
action-001 marker. The immutable log and timing SHA-256 identities are
`9dd4930d36c15a720cbca93255b3d6fb55ecc7e4f4eb77f8ffe73acf0c27b63e`
and `16163ed461f2a2eb6c83ca429f6f279ab6d7d875ea7ff2c387bdafe34bd6ece7`.
The attempt-local result receipt has SHA-256
`f5c6e8c5eeec38721703d2938679cb396129f976e60986d95289ffe03ad8513e`.
The frozen attempt must never be promoted.
