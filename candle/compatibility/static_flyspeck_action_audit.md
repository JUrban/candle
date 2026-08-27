# Static Flyspeck source-action audit

This is direct-source frontier evidence for roadmap v1.3.  It is not S2 or S3
acceptance, and it does not use PFT to close a source-execution gate.

## Selected architecture

The manifest-generated `flyspeck_full_build.ml` contains 297 ordered
`#flyspeck_needs` actions.  Candle recognizes only a complete standalone
directive with one string literal and `;;`.  Before the driver is loaded, the
direct loader:

1. authenticates 399 selected source files with OCaml-compatible MD5 values;
2. installs their exact original-path to `(basename, MD5)` identities once;
3. authenticates five normalized outputs independently and installs an exact
   original-path to output-path overlay once; and
4. authenticates the generated driver's MD5.

For a new action, the boot loader resolves an existing original under the
declared load path, selects only its registered overlay (if any), reads and
evaluates that source once, commits the authenticated logical identity, and
evaluates `State_manager.neutralize_state ();;` once.  The completion marker is
emitted only after the evaluator has accepted all three phrases.  A duplicate
performs none of those steps.  An unknown identity, malformed directive,
evaluation failure, or neutralization failure flushes the loaded driver before
later phrases or a success marker.

The source-visible `loaded_files` reference aliases the action identity list.
The physical normalized path is deliberately not its identity: this preserves
the pinned HOL Light basename/digest contract while still making physical
selection explicit in the log.

## Narrow Toploop decision

`PROJECT-TOPLOOP-S3-USE-FILE-B-001` replaces strictbuild's legacy
`Toploop.use_file` wrapper and dynamic helper bindings with explicit failures,
and converts its three standalone `loadt` phrases to exact authenticated
actions.  The selected production route is the authenticated static driver
above.  No `Toploop` module, dummy return value, or swallowed source error is
introduced.  Any missed runtime call to a disabled helper therefore aborts.

This is narrower than a general transactional `Toploop.use_file` compatibility
engine.  Such an engine remains a fallback only if a selected source use cannot
be represented by an exact manifest action or documented normalization.

## Exact tested pins

- CakeML action branch: `0e749990546e2c8108851360585667a8e173f48c`;
- CakeML `candle_boot.ml` SHA-256:
  `ec202123865b131038b7038dc2c8191f67d816146b8d063b9590f346c317b8b3`;
- runtime boot artifact: the exact 37,472-byte source prefix plus the existing
  615-byte Candle working-directory suffix, SHA-256
  `c19c392bc76e969b3a34a59932f2ee67f4b781ab707b75259c57a8b551ded675`;
- normalization contract SHA-256:
  `f356deaafcaf066eb8060f1475dd8a1ab51d2b500f99b2679622c03cd24682c1`;
- generated static driver SHA-256:
  `44ae6acc8b43e9408694f64457e0c1fe8b481865abc9afdd2921fcf981094b4a`.

The compiled gates are:

```sh
candle/test_filename_compat.sh
candle/test_static_load_directive.sh ./candle.sh
candle/test_flyspeck_needs_directive.sh
```

They cover OCaml 4.14.1 filename edge cases; accepted and duplicate source
actions; always-evaluate/no-neutralize loadt actions; ordinary phrase and
loaded-file EOF boundaries; once-only source-identity configuration; rejection before evaluation
when identities are absent; evaluation and neutralization failure; malformed
mid-phrase actions; exact overlay selection; and overlay reconfiguration
rejection.

## Direct frontier

The clean direct run log has SHA-256
`3fcb0af0578513fe030e66fa162abc0fcbbc8bcada97a91d4a05aca7873aa6b0`.
It proves selection of the normalized strictbuild, both static libraries, exact
metadata, fail-closed legacy helpers, corrected phrase/EOF boundaries, and
activation of the first loadt action.  It stops inside
`general/parser_verbose.hl` at the selected let-binding or-pattern; the failed
action has no logical-identity commit or completion marker.

Open gates include the parser or-pattern and all later source frontiers,
theorem/assumption
fingerprints, performance, checkpoints, mutation tests for every materialized
output, and two clean matching full runs plus a resume run.  Consequently no S
milestone advances here.
