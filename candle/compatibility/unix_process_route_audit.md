# Selected Unix process/filesystem route audit

This audit is scoped to the manifest-selected direct Flyspeck graph at pinned
Flyspeck commit `1ce0353008eba83d3c76ae9a25c3c242e4802d53`.  It is static
non-use evidence plus fail-closed runtime behavior, not an S3 completion claim.

The selected route has three distinct Unix/process cases:

1. Strictbuild executes `Unix.open_process_in` for exactly `date` and `whoami`.
   Candle substitutes manifest-hashed ordinary files and exposes no shell.
2. The LP certificate source originally contains `Unix.mkdir`, `Sys.chdir`,
   `Sys.command`, directory enumeration, `tar`, and `rm`.  Exact normalization
   `PROJECT-FFI-S3-LP-SHELL-ELIMINATION-001` replaces that lane with prepared,
   authenticated ordinary certificate files and rejects compressed input.
3. `glpk_link.ml` and `lpproc.ml` retain historical GLPK generator/debug helper
   definitions.  A comment/string/HOL-quotation-aware scan freezes all 32
   occurrences in their internal call chain.  The selected graph has zero
   qualified external `Glpk_link.*` or `Lpproc.*` consumers and its only open is
   `open Glpk_link` inside `Lpproc` itself.  The route root `Lpproc.execute` and
   six direct GLPK utility entrypoints occur only as definitions.

`Sys.chdir`, `Sys.command`, `Unix.open_process`, `Unix.close_process`, and
`Unix.mkdir` therefore remain explicit failures.  Adding `Sys.chdir` as a
fail-closed binding is necessary because CakeML still typechecks deferred
function bodies; it does not grant directory-changing behavior.  Any accidental
entry into the generator lane aborts the one-shot process.

The generator validates every reviewed source/line/identifier tuple, the exact
module open, and the absence of selected qualified external consumers.  Source
drift fails manifest generation.  `test_unix_metadata.sh` confirms in compiled
Candle that deterministic metadata and zero-only telemetry work while arbitrary
commands, process creation, `mkdir`, and `chdir` fail.

This evidence cannot exclude reflection, a constructed identifier, or an
external caller.  The complete compiled route and final theorem statement and
fingerprint agreement remain mandatory promotion gates.
