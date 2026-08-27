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
five `str.cma`, and two `nums.cma`.  The reachable full-build graph contains
only six: three `unix.cma` and three `str.cma`; neither `nums.cma` directive is
reachable.  The generated manifest now freezes those six source locations and
41 qualified capability uses.  Its library contract remains inactive pending
static-binding evidence, blocks every unknown library, and forbids directive
erasure or a generic no-op.  The next remedy must provide semantics for the
seven used `Unix` members and five used `Str` members before activating it.

## Open boundaries exposed by this slice

- directory existence, directory enumeration, and directory-type queries;
- exact `Digest`/MD5 behavior used by duplicate tracking, serialization, and
  LP output checks;
- reproducible substitutes for strictbuild's `date` and `whoami` process
  probes (the release path may not invoke a shell for these);
- complete source-library resolution and manifest digest enforcement.

Reproduce the two current compiled gates with:

```sh
candle/test_flyspeck_loader_guard.sh ./candle.sh /path/to/flyspeck
candle/test_flyspeck_loader_frontier.sh ./candle.sh /path/to/flyspeck
```
