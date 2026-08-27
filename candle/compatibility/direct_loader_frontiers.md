# Direct Flyspeck loader compatibility frontiers

This report records clean compiled-Candle evidence for the v1.3 direct-source
loader.  It is not S1/S2/S3 acceptance evidence.

## Pins and invocation

- direct Flyspeck source: `1ce0353008eba83d3c76ae9a25c3c242e4802d53`;
- compiled Candle executable SHA-256:
  `d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3`;
- the loader is invoked once in a clean process with explicit Candle root,
  Flyspeck root, authenticated normalization-overlay root, and `full` build
  mode;
- ambient `HOLLIGHT_DIR`, `FLYSPECK_DIR`, and serialization variables are not
  read.

## Closed startup frontiers

1. Non-`full` mode fails before loading HOL or touching the source tree.
2. The loader starts the pinned Candle/HOL stack itself.
3. `Sys.configure_manifest_environment` exposes only the two manifest paths;
   absent serialization retains `Not_found` behavior.
4. `Sys.file_exists` checks required ordinary marker files through CakeML's
   TextIO-backed predicate.  Directory semantics are explicitly not claimed.
5. The OCaml `Filename` compatibility module preserves Candle boot's verified
   `concat`, `basename`, and `dirname` functions and supplies the two additional
   operations found in the direct corpus.
6. HOL Light's standard `load_path` name aliases `Cakeml.loadPath`; there is one
   reference and no copied loader state.
7. The manifest-authenticated original path/basename/MD5 table is installed
   once; an unknown action or reconfiguration fails before source evaluation.
8. HOL Light's logical `loaded_files`, `hol_expand_directory`, and
   `file_on_path` names are bound before the rest of HOL loads.  Resolution uses
   only ordinary files below explicit load roots; ambient `.` resolution fails
   closed.
9. The seven authenticated normalization outputs are checked independently by
   MD5, registered as exact original-to-output mappings, and never added as a
   shadowing load root.

## Closed strictbuild loading frontiers

The clean full-mode run selects the authenticated normalized output for pinned
`text_formalization/build/strictbuild.hl`.  Exact `#flyspeck_loadt` actions now
replace the three selected standalone dynamic-argument phrases.  Unlike
`#flyspeck_needs`, each occurrence evaluates even when repeated, commits the
authenticated logical identity after success, and does not neutralize state.
The legacy dynamic `needs` and `reneeds` bindings fail explicitly if called.

The ordinary `needs`/`loads`/`#use` scanner now recognizes a directive only at
an exact phrase start.  A compiled fixture proves identifiers inside a
definition and false conditional remain ordinary source syntax, while a
phrase-start directive still loads.  Loaded-file EOF also terminates a final
declaration without requiring `;;`; the parent action resumes at a fresh phrase
boundary.  The scanner treats `;;` inside `struct` and `sig` as module-item
separators while retaining separators inside `begin` expressions, and a
compiled nested-module fixture plus a negative `begin 1;; 2 end` case freezes
that distinction.

## Current exact frontier

After passing the former `loadt` and parser boundaries, the direct run reports:

```text
- Flyspeck source action complete: general/parser_verbose.hl
- Selecting normalized source .../text_formalization/general/debug.hl -> .../text_formalization/general/debug.hl
- Loading .../text_formalization/general/debug.hl
open-declarations are not supported (yet)
Parsing failed at line 16

  open Parser_verbose
```

The authenticated parser overlay replaces its single let-binding or-pattern
by an ordinary match and its single `%s`-only `sprintf` call by concatenation;
the compiled loader exports all `Parser_verbose` bindings and commits that
action.  The authenticated debug overlay removes an OCaml-valid trailing
sequence separator that Candle cannot parse.  Its next exact unsupported form
is the module-opening declaration at original `general/debug.hl:16`.
Because evaluation fails, the debug action reaches neither its logical-identity
commit nor its completion marker.  Before the failure, strictbuild evaluates
its exact Unix metadata path and binds `load_date` to the manifest input
`1970-01-01T00:00:00Z\n`.  No dummy or no-op `Toploop` or `loadt` binding is
installed.

The repository contains 17 standalone directives: ten `unix.cma`, five
`str.cma`, and two `nums.cma`.  The enforcing loader graph contains only five:
two `unix.cma` and three `str.cma`; neither `nums.cma` directive is reachable.
The preceding graph incorrectly counted the convenience entry
`load_flyspeck.ml`, although the enforcing loader enters `strictbuild.hl`
directly.  Removing that false root also removes its two placeholder
`Unix.putenv` uses from execution claims.

The generated manifest now freezes the five actual directive locations and 42
capability occurrences: 39 qualified plus three reviewed lexical candidates
under `open Str`.  The two `Str` opens and absence of `Unix` opens are recorded
separately.  The boot accepts only complete standalone directives for the two
listed libraries and selects their fixed static modules.  Embedded, malformed,
and unknown loads fail closed.  This exact activation is not full member
compatibility; every member remains governed by the partial evidence below.

The five selected `Str` members now have a pure source implementation.  A
compiled gate matches OCaml 4.14.1 on all selected literal regex forms and
fails explicitly on unimplemented advanced syntax; it introduces no dynamic
loader or FFI.  This is partial evidence because one source definition builds a
regex from an argument.

The immediate strictbuild metadata dependency also has a narrow pure-source
binding.  Its exact `date` and `whoami` commands read two manifest-hashed text
inputs through TextIO; no shell or ambient clock/user state is exposed.  The
source compatibility layer also shadows Candle REPL's token queue with the
small OCaml `Buffer` subset used by strictbuild and serialization.  A compiled
gate exercises strictbuild's byte-at-a-time reader, including channel close,
and verifies rejection of arbitrary commands and clock access.
This does not cover indirect command helpers elsewhere in the source graph or
general Unix process, clock, and directory semantics.  Those paths remain
explicitly fail-closed.

The separate OCaml-compatibility ledger records 21 selected `Digest` uses over
`file`, `string`, `to_hex`, and type `t`, with no `open Digest`.  A pure
source implementation matches OCaml 4.14.1 on binary and padding-boundary
vectors at every length from 0 through 130, multi-block input, file hashing,
and invalid hexadecimal conversion;
it adds no host hashing FFI.  The differential result is not yet a formal link
to CakeML's existing verified `md5Theory`/`md5Prog`, so that assurance boundary
remains explicit.  A single informational probe of the largest selected source
file (9,099,782 bytes) matches the host MD5 in 9.12 seconds including Candle
preload and 1,216,768 KiB maximum RSS.

## Open boundaries exposed by this slice

- verified Dopen integration against the generated 3,180-site, 234-file
  declaration-open corpus contract rather than only a synthetic fixture;
- directory existence, directory enumeration, and directory-type queries;
- a formal link between the source `Digest` binding and CakeML's verified MD5
  theory/program;
- sandbox/refinement contracts for non-metadata process calls, clock access,
  and directory creation;
- verified Dopen integration for `open Parser_verbose` and all later
  source-language frontiers;
- dynamic non-use proof for strictbuild's fail-closed legacy loader helpers;
- complete direct sequence execution, checkpoints, and semantic fingerprints.

Reproduce the two current compiled gates with:

```sh
candle/test_flyspeck_loader_guard.sh ./candle.sh /path/to/flyspeck
candle/test_static_load_directive.sh ./candle.sh
candle/test_flyspeck_needs_directive.sh
candle/test_flyspeck_parser_orpattern_normalization.sh ./candle.sh
candle/test_filename_compat.sh
candle/test_flyspeck_loader_frontier.sh \
  ./candle.sh /path/to/flyspeck /path/to/materialized-overlay
candle/test_str_compat.sh
candle/test_unix_metadata.sh
candle/test_digest_compat.sh
```
