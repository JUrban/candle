# Direct boundary 00--029 development attempt at e1a8cd89

This DEVELOPMENT / NON-RELEASE attempt reached and passed zero direct boundary
actions. It emitted no nonce-bound preflight or action-success marker. It is
not schema-5 or schema-6 evidence and makes no S1, S2, S3, qualification,
promotion, or release claim. No qualified Great100/S1 runtime, source, report,
transcript, or evidence byte was changed.

## Inputs and execution

The exact Candle source head was
`e1a8cd89d275099335f7f7a53ef5063cc0e94c69`; the CakeML runtime source head
was `cea7c49d441c749bed4c8a987bee6d321816fbde`; and the pinned Flyspeck commit
was `1ce0353008eba83d3c76ae9a25c3c242e4802d53`. The fresh 297-action plan at
`/project/flyspeck-candle-runs/v14-stratum-plan-e1a8cd8-dev-001` has SHA-256
`314f48a78b1d38ac4b083daa77b9b4244eda036d00613c2f7d5bc3d1230624d8`.
Its first cumulative boundary contains 30 actions. The accompanying overlay
and generated-input projection contain 24 normalized outputs and 43 bindings.

The attempt root is
`/project/flyspeck-candle-runs/v14-dev-direct-boundary-e1a8cd8-attempt-001`.
It used the checked DEVELOPMENT / NONPROMOTABLE Cake binary with SHA-256
`dd8a693bc88b75b5599a91777b93629417993cdb5338bb7cb0f40d38d246190f`.
The stdin contained only the minimal no-trace runtime config, current setup,
and current instrumented prefix. Check, postlude, archive, publication, and
source-trace observation were deliberately absent.

## Actual progress and failure

The corrected parser compatibility path did execute successfully during
strictbuild setup: normalized `general/parser_verbose.hl` and
`general/debug.hl` completed at log lines 19865 and 19892. Setup then issued
ordinary `needs "Library/rstc.ml"` and failed closed at lines 19896--19897:

```text
Failure "unauthenticated Candle source action: Library/rstc.ml"
```

The runtime identity table represented this manifest source under the absolute
Candle repository root, while the loader retained `.` as its only matching
search-path entry and consequently produced the relative cache key
`Library/rstc.ml`. Exact identity lookup correctly rejected that unmatched
path before reading or evaluating `rstc.ml`. This is an authenticated-loader
search-path canonicalization defect, not a parser, theorem, proof, or Flyspeck
source-semantic failure.

Because strictbuild did not complete, the exact nonce-bound preflight never
appeared. The later undefined `State_manager.neutralize_state` message and
apparent action-zero load are cascades from continuing the REPL after failed
setup and do not count as an action invocation. Exact progress for this attempt
is therefore 0 actions reached, 0 passed, and 0 authenticated success markers.

The run consumed 6:08.68 wall time at 99% of one CPU and reached a maximum RSS
of 4,235,392 KiB. The interactive REPL exited zero at EOF after reporting the
caught exception; that process exit does not override the missing preflight.
The immutable log and timing SHA-256 identities are respectively
`30507ad3977ea3b85ca66b73fb7182ece11565864917dbb7f9328a47f89ed593`
and `4ceb3c4b6d718ba3e5c78665ee8a13064ab9c92ad50d62f0b38b468ae22b8f1d`.
The attempt-local result receipt records the complete classification. This
attempt must never be promoted.
