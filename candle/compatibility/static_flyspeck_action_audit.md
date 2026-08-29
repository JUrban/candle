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
3. authenticates seven normalized outputs independently and installs an exact
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

- CakeML action branch: `1b17732f902fde2efd985905d277a972da73ae0f`;
- CakeML `candle_boot.ml` SHA-256:
  `55a0e08b515a06e9b047ccedb62eb98eb4808f3b45e9c4b11e13eac7f7abba94`;
- runtime boot artifact: the exact 38,504-byte source prefix plus the existing
  615-byte Candle working-directory suffix, SHA-256
  `ecd0da6408863d140cff3988ccc111e5b6677ebc48a4b1f91f5f05698643e705`;
- normalization contract SHA-256:
  `dfe12cb8171e8f8d63330bf4c5f647072ffda5a5676f4d70f005ce8cccaf46e3`;
- generated static driver SHA-256:
  `44ae6acc8b43e9408694f64457e0c1fe8b481865abc9afdd2921fcf981094b4a`.

The compiled gates are:

```sh
candle/test_filename_compat.sh
candle/test_static_load_directive.sh ./candle.sh
candle/test_flyspeck_needs_directive.sh
candle/test_flyspeck_parser_orpattern_normalization.sh ./candle.sh
```

They cover OCaml 4.14.1 filename edge cases; accepted and duplicate source
actions; always-evaluate/no-neutralize loadt actions; ordinary phrase,
module-item separator, and loaded-file EOF boundaries; exact parser
normalization behavior; once-only source-identity configuration; rejection before evaluation
when identities are absent; evaluation and neutralization failure; malformed
mid-phrase actions; exact overlay selection; and overlay reconfiguration
rejection.

## Direct frontier

The clean direct run log has SHA-256
`cc75153644c72a85bd0ee6acb88e66288e903f08a5aa3cd28f462d29d4b3b5c7`.
It proves selection of the normalized strictbuild, both static libraries, exact
metadata, fail-closed legacy helpers, corrected phrase/EOF boundaries, and
activation of the first loadt action.  It completes normalized
`general/parser_verbose.hl`, selects normalized `general/debug.hl`, and stops
at the exact `open Parser_verbose` Dopen boundary on original line 16; the
failed debug action has no logical-identity commit or completion marker.

Open gates include Dopen integration and all later source frontiers,
theorem/assumption
fingerprints, performance, checkpoints, mutation tests for every materialized
output, and two clean matching full runs plus a resume run.  Consequently no S
milestone advances here.
