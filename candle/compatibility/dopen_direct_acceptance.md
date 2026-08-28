# Direct Flyspeck Dopen prefix acceptance

This gate is the first real selected-source workload that depends on verified
declaration `open`.  It executes the authenticated normalized strictbuild
prefix through these two existing loader actions, in order:

1. `#flyspeck_loadt "general/parser_verbose.hl";;`
2. `#flyspeck_loadt "general/debug.hl";;`

The second source contains `open Parser_verbose` inside `module Debug`.  Its
later unqualified uses of `parse_pretype_verbose`, `parse_preterm_verbose`, and
`string_of_lexcodel` make successful parsing and inference genuinely depend on
Dopen; this is not a synthetic module smoke test.

## Exact pins and roots

- CakeML integration: `936219bbc3021fa20418d62e85155f2d0092b9f9`;
- HOL4 proof build: `a390cbabd3a4521bab4ee20281e3e42933a8a3ae`;
- direct Flyspeck: `1ce0353008eba83d3c76ae9a25c3c242e4802d53`;
- normalization contract SHA-256:
  `46499f442c741cf9d2c8e4adfeb442b0c4d8fdeb705c6cea8afffbced2e450b8`;
- current authenticated overlay root:
  `/project/flyspeck-candle-runs/v13-normalized-overlay-46499f442c741cf9`;
- prepared `hard_7.dat` SHA-256:
  `0ca1b5b6ceba53537ac5d95ffddd883bb297e7d48c30ac241de4f3ec71ab5526`;
- current authenticated generated-input root:
  `/project/flyspeck-candle-runs/v13-generated-lp-0ca1b5b6`.

The preparation tool re-derives these facts from
`flyspeck_manifest.json`, both contract files, both receipts, the clean
Flyspeck Git root, and the bytes on disk.  It authenticates all normalized
overlay outputs and the generated input, plus the original strictbuild,
Parser_verbose, and Debug sources.  The compiled process independently checks
the original and normalized source MD5 identities before source evaluation.

## Reproduction

After the pinned CakeML bootstrap has produced the x64/64 inputs, build a
fresh integrated Candle executable and run the bounded gate:

```sh
cd /project/worktrees/candle-dopen-acceptance-v13
CANDLE_BUILD_JOBS=2 ./build-local-cakeml.sh \
  /project/worktrees/cakeml-flyspeck-v13-integration
CANDLE_FLYSPECK_DOPEN_LOG=/project/flyspeck-candle-runs/v13-dopen-direct-prefix.log \
  candle/test_flyspeck_dopen_prefix.sh \
  ./candle.sh \
  /project/worktrees/flyspeck-v13-source \
  /project/flyspeck-candle-runs/v13-normalized-overlay-46499f442c741cf9 \
  /project/flyspeck-candle-runs/v13-generated-lp-0ca1b5b6
```

Do not run this command concurrently with a build or another compiled Candle
workload in the same worktree.

## Acceptance and failure semantics

Success requires exactly one, correctly ordered preflight marker, normalized
selection/loading/completion triple for Parser_verbose, normalized
selection/loading/completion triple for Debug, and final
`CANDLE_FLYSPECK_DOPEN_PREFIX_OK`.  The final checked phrase also requires both
logical source identities to have committed exactly once, no pending source
identity, the Parser_verbose export, and `Debug.parse_type_verbose "bool" =
bool_ty`.

Any source, contract, receipt, Git pin, digest, action-order, parser, inference,
evaluation, or logical-identity mismatch fails closed.  A failed Debug action
must emit neither its completion marker nor the final marker.  Any parse/error
marker also rejects the gate even if the REPL itself returns zero.

The prepared prefix is exact bytes from the normalized strictbuild source and
ends immediately after the Debug action.  Preparation rejects a prefix that
contains `#flyspeck_needs`, so this workload cannot enter the remaining
strictbuild dependencies or the generated 297-entry full run.

Host-side preparation and unit tests are not G2 evidence.  Even a green
compiled run covers one real Dopen site out of the manifest's 3,180 sites; it
does not establish the complete direct source corpus, the full-build target,
or S2/S3.  The generated LP root is authenticated to bind the same production
root tuple but is not consumed by this prefix.
