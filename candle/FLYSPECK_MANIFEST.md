# Direct Flyspeck source manifest (G6 inventory slice)

`flyspeck_manifest.py` generates `flyspeck_manifest.json` from a clean pinned
Flyspeck checkout.  The manifest extracts the literal
`Build.build_sequence_full` list, resolves it under Flyspeck's declared load
path, recursively follows literal source-loading calls, and records source and
mathematical-input hashes without embedding checkout locations.

Generate or verify it with:

```sh
python3 candle/flyspeck_manifest.py \
  --flyspeck-root /path/to/pinned/flyspeck --write
python3 candle/flyspeck_manifest.py \
  --flyspeck-root /path/to/pinned/flyspeck --check
(cd candle && python3 -m unittest -v test_flyspeck_manifest.py)
```

The current pinned inventory contains 297 ordered build entries (287 unique),
399 recursively reached source nodes, 418 selected dependency edges, and 42
hashed LP/archive/nonlinear inputs.  There are no unresolved build roots,
unreviewed dynamic loads, missing ordinary sources, path escapes, ambiguous
loads, or detected cycles.  Fifteen non-literal call sites have explicit
source-and-line reviews; the selected OCaml-version branch is pinned to 4.14.
The manifest also pins `flyspeck_l2_target.ml`, the direct Candle theorem glue
for `Candle_flyspeck_l2.tame_imp_kepler_conjecture`; that file has no trace
producer or theorem-import shortcut.

The 297 entries are also partitioned into eight contiguous operational
checkpoint strata: base, arithmetic, nonlinear support, analysis, geometry,
LP support, text formalization, and final assembly.  Each stratum records its
exact inclusive indexes, boundary paths, entry count, and a digest over the
ordered resolved roots and their source hashes.  Stratum membership is
propagated through every selected dependency edge; all 399 source nodes must
have at least one membership.  These are load/checkpoint labels, not a claim
that a shared dependency belongs to only one mathematical subject.

`flyspeck_full_build.ml` is generated from the same 297-entry sequence.  Each
entry carries its index, stratum, manifest-selected source key, and source
SHA-256 beside an explicit `#flyspeck_needs` directive.  Build entry 182 also
records the exact normalization id and output SHA-256 described below.  The directive is
intentionally fail-closed today.  Its required future loader action is atomic:
evaluate a newly selected source at that exact point and call
`State_manager.neutralize_state` once only after success; an already-loaded
duplicate does neither.  Unknown, malformed, reordered, unresolved, or
hash-mismatched entries abort.  This separates the static load-order contract
from Flyspeck's `Toploop.use_file` implementation without pretending that a
successful no-op loaded anything.  The direct loader authenticates the
generated program's MD5 before `strictbuild`; its SHA-256 remains an outer
release-manifest pin.  Authentication does not activate the directive.

`flyspeck_normalizations.json` and `flyspeck_normalize.py` implement the first
mechanical source normalization.  The sole entry is
`PROJECT-POINTER-S3-IMMEDIATE-001`: after authenticating the pinned upstream
`formal_lp/hypermap/main/prove_flyspeck_lp.hl`, it replaces the unique exact
line `if n == 1 then [] else` with `if n = 1 then [] else` and authenticates
the normalized size, MD5, and SHA-256.  Commit, path, input hash, anchor count,
or output drift aborts.  The manifest annotates exactly that source node and no
other.  This rule is confined to the `int` returned by `count_terminals`; it
does not rewrite or discharge any identity-sensitive comparison over allocated
lists.  The host test and pinned-source gate are:

```sh
(cd candle && python3 -m unittest -v test_flyspeck_normalize.py)
python3 candle/flyspeck_normalize.py \
  --flyspeck-root /path/to/pinned/flyspeck --check
CANDLE_BINARY=/path/to/candle.sh \
  candle/test_flyspeck_immediate_normalization.sh
```

The pinned OCaml 4.14.1 implementation binds `==` through `%eq` directly to
integer comparison, specializes structural `=` on `int` to the same
`Pintcomp Ceq`, and encodes every OCaml `int` injectively as a tagged immediate
word.  Thus the branch predicate is equal for every representable `int`, not
only the oracle samples.  The compiled Candle oracle separately confirms that
the normalized branch is accepted and selects the expected cases.  Runtime
application of the recorded patch is still pending integration with the exact
compiled source loader, so the manifest status remains
`ready-pending-compiled-loader-integration` and this work alone advances no S
milestone.

The top-level interface contract also inventories the small set of Flyspeck
identifiers that could consume compiler reflection.  The selected graph has
only the definitions of `test_id_thm`, `use_arg_then`, and `eval_command`; it
has no other lexical reference to those bindings.  In contrast, the explicit
theorem-fallback helper `use_arg_then2`, which does not call `Toploop`, occurs
23,810 times in 22 selected files.  The pinned OCaml-4 route has one active
compiler-environment consumer: the load-time `update_database ()` call in
`update_database_400.ml`.  All 20 relevant identifier sites are source/line
reviewed, and any site drift aborts manifest generation.  This supports a
narrow fail-closed normalization design, but lexical non-use is not proof
against reflection or external invocation; compiled reference and final
fingerprint gates remain mandatory.

The loader action contract separately freezes all 434 loading-syntax sites.
There are 422 complete standalone phrases and 12 embedded occurrences.  The
standalone set includes 144 literal `flyspeck_needs` calls, whose post-success
state neutralization is observably different from ordinary `needs`; the
embedded set contains the version conditional, optional serialization path,
generated digest loader, and loader-function definitions/drivers.  Only a
complete standalone top-level phrase can be handled as a boot action.  A token
at the start of a physical line can still be inside a conditional or function,
so executing it lexically can select both branches.  Embedded calls require
ordinary verified evaluation or an exact hash-bound normalization.

`flyspeck_source_digests.ml` is generated alongside the JSON manifest and is a
known generated dependency rather than a self-hashed graph node.  It carries
OCaml `Digest.file`-compatible MD5 values for 398 selected source nodes: every
node except the executing loader.  The loader embeds and checks the generated
program's MD5 before executing it, while the JSON manifest and generated
program remain SHA-256-pinned externally.  `flyspeck_loader.ml` executes the
in-process preflight before loading `strictbuild.hl`, rejecting a missing file,
unknown repository, entry-count drift, or digest mismatch.  This detects
on-disk source corruption before the Flyspeck build, but `hol.ml` and the
loader necessarily begin executing before the preflight and remain
launcher/authentication obligations.

`flyspeck_loader.ml` is the initial enforcing loader slice.  In a clean Candle
process it first fails closed unless the mode is `full`, then loads the pinned
Candle/HOL source stack itself.  The launcher supplies the Candle and Flyspeck
roots as explicit source-level inputs.  `Sys.configure_manifest_environment`
turns those into the exact `HOLLIGHT_DIR`/`FLYSPECK_DIR` allowlist used by the
source build; ambient host variables are not inherited.  The loader checks
ordinary marker files, installs only the manifest load paths, runs the complete
authoritative build sequence, and then loads the direct target.  It does not
yet execute the generated static sequence or implement versioned checkpoints,
so it is not execution acceptance evidence.  Its current source preflight
checks all selected source nodes except the already-executing loader; the
outer release lock authenticates that loader and the generated contracts.

The fail-closed ordering is exercised against a compiled Candle executable by
`test_flyspeck_loader_guard.sh`; the negative test must reach the exact mode
exception without reaching filesystem compatibility or the success marker.
With `full` selected, `test_flyspeck_loader_frontier.sh` now proves that the
compiled path passes the former manifest-environment, ordinary-file,
`Filename.concat`, and standard `load_path` frontiers.  It reaches the exact
direct source file and stops at `build/strictbuild.hl:21`, where Candle does not
yet recognize `#load "unix.cma";;`.  The pinned repository has exactly 17
standalone directives: ten `unix.cma`, five `str.cma`, and two `nums.cma`.
Only five are in the enforcing loader's recursively reached full-build graph:
two `unix.cma` and three `str.cma`; no `nums.cma` site is reachable.  The
repository convenience entry `load_flyspeck.ml` is not executed by this loader:
it hard-codes `/home/user` paths and was incorrectly included as an extra root
in the preceding manifest.  Removing that false root removes its directive and
two `Unix.putenv` occurrences from execution-route claims.

The manifest contract records the five actual sites plus 42 source-located
capability uses: 39 qualified uses and three conservative, manually reviewed
candidates under `open Str`.  There are 17 `Unix` uses over six members and 25
`Str` uses over five members.  The two reachable `open Str` sites and absence of `open Unix`
are frozen separately; open-based attribution is explicitly not represented as
a compiler name-resolution proof.  Unknown libraries or members are
promotion-blocking diagnostics, and directive erasure or a generic no-op is
forbidden.

`ocaml.ml` now provides the five selected `Str` members as pure Candle source,
so `str.cma` does not imply host dynamic loading or an FFI.  The compiled
`test_str_compat.sh` gate matches an OCaml 4.14.1 oracle for every literal
regular-expression form in the selected graph, offset matching, character
ranges, splitting, replacement, and `first_chars`.  Unsupported escaped
grouping, alternation, back-references, and empty-match replacement fail
explicitly.  This is partial binding evidence rather than activation of the
library contract: arbitrary dynamic regex input remains open.

The immediate strictbuild process dependency is now source-bound without a
shell.  `Unix.open_process_in` accepts only the exact commands `date` and
`whoami`, returning TextIO channels over two manifest-hashed repository inputs;
`Unix.close_process_in` closes those channels (the selected Flyspeck source
discards its return value).  The same source slice supplies the small pure
OCaml `Buffer` subset used by strictbuild's byte-at-a-time reader and Flyspeck's
serializer, rather than exposing Candle REPL's unrelated token-queue module.
`test_unix_metadata.sh` exercises the original byte-at-a-time
`process_to_string` pattern against a compiled Candle and proves that an
arbitrary command and the clock operation fail closed.  This covers only
strictbuild's load/build-report metadata.  It does not authorize the indirect
command helpers defined elsewhere in Flyspeck, nor implement general process,
clock, or directory behavior.  The other selected operations fail explicitly,
so the overall library status is still
`blocked-pending-static-binding-evidence`.

The selected graph also has 17 executable qualified `Digest` occurrences:
eight `file`, three type `t`, two `string`, and four `to_hex`; it has no
`open Digest`.  `ocaml.ml` supplies these operations with a pure MD5
implementation and no hashing FFI.  `test_digest_compat.sh` differentially
checks OCaml 4.14.1 across deterministic binary inputs of every length from 0
through 130 bytes, explicit 55/56/64/65-byte padding boundaries, a 1,000-byte
multi-block string, a file, and invalid `to_hex` input.  CakeML
already contains a verified `md5Theory`/`md5Prog`, but this source binding is
not yet formally linked to it; the manifest records that assurance limit.  An
informational largest-selected-file probe hashes the 9,099,782-byte
`archive_all.ml` correctly in 9.12 seconds including Candle preload, at
1,216,768 KiB maximum RSS on the development machine.

`Sys.file_exists` in this slice deliberately forwards to CakeML's verified
TextIO-backed ordinary-file predicate.  OCaml-compatible directory existence,
`Sys.is_directory`, and `Sys.readdir` remain open and require the versioned,
sandboxed filesystem contract.  No directory behavior is claimed by the
marker-file checks.

This artifact is deliberately not loader-execution evidence.  In particular,
two generated-runtime contracts remain visible:

- `candle/build/insulate.ml` must be generated from the pinned compiler's
  `types.txt` by the pinned `insulate.py` recipe.  It remains a generated
  contract even when an ignored local build happens to contain the file, so
  the source manifest is independent of worktree build state; and
- Flyspeck serialization writes and reloads a temporary theorem-digest module,
  which needs a versioned, atomic generated-input/checkpoint lifecycle.

The next G6 slices must turn this inventory into the loader's enforced input
contract, reject manifest/source reorder and corruption, add relocation and
clean/resume tests, and prove that generated inputs are linked to the theorem
artifacts consumed in the direct run.  Until those gates pass, the manifest
does not advance S1, S2, or S3.
