# Direct boundary 00--029 development attempt at 9e078a737

This DEVELOPMENT / NON-RELEASE attempt reached two direct Flyspeck actions and
passed one. Action 000, `general/hol_pervasives.hl`, emitted its exact
nonce-bound authenticated success marker. Action 001, `general/lib.hl`, was
invoked and failed with a CakeML value-restriction diagnostic before its
success marker. This is not schema-5 or schema-6 evidence and makes no S1, S2,
S3, qualification, promotion, or release claim. No qualified Great100/S1
runtime, source, report, transcript, or evidence byte was changed.

## Inputs and execution

The exact Candle source head was
`9e078a737229e6c8ba87bb4fbb516baf977079cc`; the CakeML runtime source head
was `cea7c49d441c749bed4c8a987bee6d321816fbde`; and the pinned Flyspeck commit
was `1ce0353008eba83d3c76ae9a25c3c242e4802d53`. The fresh 297-action plan at
`/project/flyspeck-candle-runs/v14-stratum-plan-9e078a7-dev-001` has SHA-256
`777ede7410a6a53c80b66a350c3d8ec95011217bb1d752a84489383253fd6b60`.
Its first cumulative boundary contains 30 actions. The accompanying overlay
and generated-input projection contain 25 normalized outputs and 43 bindings.

The attempt root is
`/project/flyspeck-candle-runs/v14-dev-direct-boundary-9e078a7-attempt-002`.
It used the checked DEVELOPMENT / NONPROMOTABLE Cake binary with SHA-256
`dd8a693bc88b75b5599a91777b93629417993cdb5338bb7cb0f40d38d246190f`.
The stdin contained only the minimal no-trace runtime config, current setup,
and current instrumented prefix. Check, postlude, archive, publication, and
source-trace observation were deliberately absent.

## Actual progress and failure

The logical-path setup correction passed its prior blocker: authenticated
`Library/rstc.ml` loaded and completed at log lines 19896--20489. The entire
strictbuild setup then completed, and the exact nonce-bound preflight appeared
at line 184121. Action 000 selected the normalized
`general/hol_pervasives.hl` identity and emitted its exact authenticated
success marker at line 184127 with disposition `skip-ledger`.

Action 001 then selected and began loading the authenticated normalized source
for `general/lib.hl` at lines 184129--184130. CakeML rejected the file at lines
184131--184133:

```text
ERROR: Value restriction violated at line 72

let rev =
```

No action-001 success marker and no later action invocation appeared. Exact
progress is therefore 2 actions reached, 1 passed, and 1 authenticated action
success marker. This is a language-compatibility failure in a polymorphic
top-level function binding, not a Flyspeck theorem, proof, or mathematical
semantic failure.

Post-run historical inspection found that Candle `fix-top100`, `master`,
`pft`, `ptr-eq`, and `merge/jrh13-master-20260825` all use an eta-expanded
`let rev l = ... rev_append [] l` implementation in `lib.ml`. That is only a
lead: the project normalization must still minimize and independently validate
the corresponding Flyspeck compatibility rewrite before rerunning the
boundary.

The run consumed 41:18.22 wall time at 99% of one CPU and reached a maximum
RSS of 4,342,016 KiB. The interactive REPL exited zero at EOF after reporting
the compile-time compatibility error; that exit does not override the missing
action-001 marker. The immutable log and timing SHA-256 identities are
`0a9fa8ad91476e905e0248966cba65c84cb00a758347b5355124a17a4abf6324`
and `bf5d43b5990700cc12f6a595c0b92d36595fdf563010e2e4b07257b55e99d7d7`.
The attempt-local result receipt has SHA-256
`1a20048255aebfedca50f402ab9256cce3306a1a6f5bede8bebf975b828295b2`.
This attempt must never be promoted.
