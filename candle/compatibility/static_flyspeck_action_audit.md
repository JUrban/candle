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

`PROJECT-TOPLOOP-S3-USE-FILE-B-001` replaces only strictbuild's legacy
`Toploop.use_file` wrapper with an explicit failure.  The selected production
route is the authenticated static driver above.  No `Toploop` module, dummy
return value, or swallowed source error is introduced.  Any missed runtime
call to `use_file_b` therefore aborts.

This is narrower than a general transactional `Toploop.use_file` compatibility
engine.  Such an engine remains a fallback only if a selected source use cannot
be represented by an exact manifest action or documented normalization.

## Exact tested pins

- CakeML action branch: `a0303d78e230a4d1fe8615f4571abd1235be677e`;
- CakeML `candle_boot.ml` SHA-256:
  `2ffea9afb9d3fefb5039be313da1929b191d720fb15c1fcbbd41c26d9293f2e8`;
- runtime boot artifact: the exact 33,875-byte source prefix plus the existing
  615-byte Candle working-directory suffix, SHA-256
  `1584a0019586bc7be33df844dcaa76a61c85e3efa860da8b73581932cee68270`;
- normalization contract SHA-256:
  `8ab1778d840f8d3a3c9a03257c88306ae7e440a9786059c669ce7af9ae026ad7`;
- generated static driver SHA-256:
  `44ae6acc8b43e9408694f64457e0c1fe8b481865abc9afdd2921fcf981094b4a`.

The compiled gates are:

```sh
candle/test_filename_compat.sh
candle/test_static_load_directive.sh ./candle.sh
candle/test_flyspeck_needs_directive.sh
```

They cover OCaml 4.14.1 filename edge cases; accepted and duplicate source
actions; once-only source-identity configuration; rejection before evaluation
when identities are absent; evaluation and neutralization failure; malformed
mid-phrase actions; exact overlay selection; and overlay reconfiguration
rejection.

## Direct frontier

The clean direct run log has SHA-256
`6c98ef4f7bb41ee9857ab69074a5a8aae3ac970f11291e4e8d043cdff041e922`.
It proves selection of the normalized strictbuild, both static libraries, exact
metadata, the fail-closed legacy `use_file_b`, and working
`loaded_files`/`file_on_path`/`load_on_path_b` definitions.  It stops at the
first selected standalone dynamic-argument `loadt` phrase at original
strictbuild line 103.

Open gates include the exact `loadt` normalization, all later source
frontiers, ordinary directive phrase-start repair, theorem/assumption
fingerprints, performance, checkpoints, mutation tests for every materialized
output, and two clean matching full runs plus a resume run.  Consequently no S
milestone advances here.
