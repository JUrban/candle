# Direct Flyspeck loader compatibility frontiers

This report records clean compiled-Candle evidence for the v1.3 direct-source
loader.  It is not S1/S2/S3 acceptance evidence.

## Pins and invocation

- direct Flyspeck source: `1ce0353008eba83d3c76ae9a25c3c242e4802d53`;
- compiled Candle executable SHA-256:
  `d361be3839f31811328d5a0da1ecea15a8a73f369c77e34a288355f16bb930d3`;
- the loader is invoked once in a clean process with explicit Candle root,
  Flyspeck root, and `full` build mode;
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

## Current exact frontier

The clean full-mode run reaches the original pinned
`text_formalization/build/strictbuild.hl` and reports:

```text
Parsing failed at line 23

#load "unix.cma";;
^
```

The source line is 21; the loader's diagnostic line includes its input-stack
offset.  The repository contains 17 standalone directives: ten `unix.cma`,
five `str.cma`, and two `nums.cma`.  The enforcing loader graph contains only
five: two `unix.cma` and three `str.cma`; neither `nums.cma` directive is
reachable.  The preceding graph incorrectly counted the convenience entry
`load_flyspeck.ml`, although the enforcing loader enters `strictbuild.hl`
directly.  Removing that false root also removes its two placeholder
`Unix.putenv` uses from execution claims.

The generated manifest now freezes the five actual directive locations and 42
capability occurrences: 39 qualified plus three reviewed lexical candidates
under `open Str`.  The two `Str` opens and absence of `Unix` opens are recorded
separately.  Its library contract remains inactive pending static-binding
evidence, blocks every unknown library/member, and forbids directive erasure or
a generic no-op.

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
explicitly fail-closed, and the library contract remains inactive.

## Open boundaries exposed by this slice

- directory existence, directory enumeration, and directory-type queries;
- exact `Digest`/MD5 behavior used by duplicate tracking, serialization, and
  LP output checks;
- sandbox/refinement contracts for non-metadata process calls, clock access,
  and directory creation;
- complete source-library resolution and manifest digest enforcement.

Reproduce the two current compiled gates with:

```sh
candle/test_flyspeck_loader_guard.sh ./candle.sh /path/to/flyspeck
candle/test_flyspeck_loader_frontier.sh ./candle.sh /path/to/flyspeck
candle/test_str_compat.sh
candle/test_unix_metadata.sh
```
