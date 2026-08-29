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
400 recursively reached source nodes, 706 selected dependency edges, and 42
hashed LP/archive/nonlinear inputs.  There are no unresolved build roots,
unreviewed dynamic loads, missing ordinary sources, path escapes, ambiguous
loads, or detected cycles.  Fourteen non-literal call sites have explicit
source-and-line reviews; the selected OCaml-version branch is pinned to 4.14.
The manifest also pins `flyspeck_l2_target.ml`, the direct Candle theorem glue
for `Candle_flyspeck_l2.tame_imp_kepler_conjecture`; that file has no trace
producer or theorem-import shortcut.

The 297 entries are also partitioned into eight contiguous operational
checkpoint strata: base, arithmetic, nonlinear support, analysis, geometry,
LP support, text formalization, and final assembly.  Each stratum records its
exact inclusive indexes, boundary paths, entry count, and a digest over the
ordered resolved roots and their source hashes.  Stratum membership is
propagated through every selected dependency edge; all 400 source nodes must
have at least one membership.  These are load/checkpoint labels, not a claim
that a shared dependency belongs to only one mathematical subject.

The generated `dopen_corpus_contract` separately freezes every declaration
open in that exact graph.  It contains 3,180 occurrences across 234 Flyspeck
files and 193 module names; all selected paths are simple, none use `open!`,
and a canonical site digest binds source, line, module path, path form, and
warning-suppression flag.  Earliest-stratum counts are recorded for all eight
strata.  Local let-open and parenthesized local-open expressions are explicitly
outside this Dopen declaration contract.  This is inventory for the G2 gate,
not proof that a synthetic open test closes the corpus.

`flyspeck_full_build.ml` is generated from the same 297-entry sequence.  Each
entry carries its index, stratum, manifest-selected source key, and source
SHA-256 beside an explicit `#flyspeck_needs` directive.  Entries whose source
is normalized also record the exact normalization id and output SHA-256.  The
directive is now an exact boot action.  The loader installs a once-only table
of manifest-authenticated original paths and their standard HOL Light
basename/MD5 identities.  A new source resolves through the original load
path, selects only an exactly registered normalization, evaluates once,
commits its logical source identity, and calls
`State_manager.neutralize_state` once.  The completion marker is reached only
after all of those steps return normally; an already-loaded duplicate performs
neither evaluation nor neutralization.  An unauthenticated source, evaluator
failure, or neutralization exception flushes the loaded driver before any
later target or success marker.  This is exact for accepted and duplicate
observations and intentionally stronger than the pinned helper's unsafe
failure recovery.  Unknown, malformed, reordered, unresolved, or
hash-mismatched entries also abort.  The direct loader authenticates the
generated program's MD5 before `strictbuild`; its SHA-256 remains an outer
release-manifest pin.

`flyspeck_normalizations.json` and `flyspeck_normalize.py` implement eighteen
site-specific, hash-bound source overlays.  `PROJECT-POINTER-S3-IMMEDIATE-001` replaces the
unique integer branch `if n == 1 then [] else` with `if n = 1 then [] else`.
`PROJECT-POINTER-S3-ALLOCATED-LIB-001` replaces five exact blocks containing
the ten physical-sharing tests in `general/lib.hl`: explicit change flags
preserve the original unchanged objects for `filter`, `partition`, `uniq`, and
`undefine`.  The selected graph contains no call of either `qmap` or
`Print_types.unsuppress`, so both normalized bindings fail explicitly if a
missed dynamic or future call reaches them; no general compatibility is
claimed.  Accordingly,
`PROJECT-POINTER-S3-UNSUPPRESS-001` replaces its identity-sensitive binding by
an explicit failure.  `PROJECT-POINTER-S3-RELABEL-001` confines structural
comparison to Jordan's binder exclusion used by `mk_primed_var`; final exact
fingerprints must still validate its selected calls.
`PROJECT-TOPLOOP-S3-USE-FILE-B-001` replaces strictbuild's dynamic
`Toploop.use_file`, `needs`, and `reneeds` helper bindings with explicit
failures and converts its three standalone `loadt` phrases to exact
`#flyspeck_loadt` actions.  Each action evaluates on every occurrence, commits
the authenticated logical identity only after success, and never neutralizes
state.  The authenticated `#flyspeck_needs` driver remains the selected
production loader, and any missed runtime helper call therefore aborts rather
than silently succeeding.  `PROJECT-PARSER-S3-LET-OR-PATTERN-001` rewrites the
single selected let-binding or-pattern in `general/parser_verbose.hl` as an
ordinary match over the same two constructor alternatives; it also replaces
one `%s`-only `sprintf` call by concatenation with the same rendered number.
`PROJECT-PARSER-S3-TRAILING-SEMI-001` removes the single trailing sequence
separator immediately before the closing parenthesis of `Debug.print_m` in
`general/debug.hl`; expression order, effects, and result are unchanged.  Each
original file,
each ordered unique anchor, and each final output size/MD5/SHA-256 is
authenticated.  Commit, path, input hash, anchor count, order, or output drift
aborts; no blanket rewrite is authorized.  The host tests and pinned-source
gate are:

```sh
(cd candle && python3 -m unittest -v test_flyspeck_normalize.py)
python3 candle/flyspeck_normalize.py \
  --flyspeck-root /path/to/pinned/flyspeck --check
CANDLE_BINARY=/path/to/candle.sh \
  candle/test_flyspeck_immediate_normalization.sh
CANDLE_BINARY=/path/to/candle.sh FLYSPECK_ROOT=/path/to/pinned/flyspeck \
  candle/test_flyspeck_identity_normalization.sh
candle/test_flyspeck_parser_orpattern_normalization.sh ./candle.sh
```

For the immediate-integer entry, pinned OCaml 4.14.1 binds `==` through `%eq` directly to
integer comparison, specializes structural `=` on `int` to the same
`Pintcomp Ceq`, and encodes every OCaml `int` injectively as a tagged immediate
word.  Thus the branch predicate is equal for every representable `int`, not
only the oracle samples.  The compiled Candle oracle separately confirms that
the normalized branch is accepted and selects the expected cases.  The
allocation refinements retain compiled, performance, and final-fingerprint
gates.  Runtime application is wired
through the authenticated static source action: the manifest and compiled boot
select the exact seven-file overlay, but the complete-run status remains
`exact-overlay-selection-active-pending-full-run`; this work alone advances no
S milestone.

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

The loader action contract separately freezes all 731 loading-syntax sites.
It distinguishes 297 generated standalone `#flyspeck_needs` actions from the
434 source-language loading sites.  The source set has 423 complete standalone
phrases and 11 embedded occurrences, including 144 literal `flyspeck_needs`
calls, whose post-success
state neutralization is observably different from ordinary `needs`; the
embedded set contains the version conditional, optional serialization path,
generated digest loader, and loader-function definitions/drivers.  Only a
complete standalone top-level phrase can be handled as a boot action.  The
compiled boot now enforces that exact boundary for ordinary `needs`, `loads`,
and `#use` as well as the two Flyspeck-specific actions; its EOF regression also
preserves a final declaration without trailing `;;`.  Embedded calls require
ordinary verified evaluation or an exact hash-bound normalization.

`flyspeck_source_digests.ml` is generated alongside the JSON manifest and is a
known generated dependency rather than a self-hashed graph node.  It carries
OCaml `Digest.file`-compatible MD5 values for 399 selected source nodes: every
node except the executing loader.  The loader embeds and checks the generated
program's MD5 before executing it, while the JSON manifest and generated
program remain SHA-256-pinned externally.  `flyspeck_loader.ml` executes the
in-process preflight before loading `strictbuild.hl`, rejecting a missing file,
unknown repository, entry-count drift, or digest mismatch.  This detects
on-disk source corruption before the Flyspeck build, but `hol.ml` and the
loader necessarily begin executing before the preflight and remain
launcher/authentication obligations.

`flyspeck_loader.ml` is the enforcing static-source loader slice.  In a clean Candle
process it first fails closed unless the mode is `full`, then loads the pinned
Candle/HOL source stack itself.  The launcher supplies the Candle and Flyspeck
roots as explicit source-level inputs.  `Sys.configure_manifest_environment`
turns those into the exact `HOLLIGHT_DIR`/`FLYSPECK_DIR` allowlist used by the
source build; ambient host variables are not inherited.  The loader checks
ordinary marker files, installs only the manifest load paths, authenticates and
registers the eighteen exact normalization outputs, authenticates a host-prepared
`hard_7.dat`, installs the fixed 39-file LP certificate table, executes the generated static
sequence through `#flyspeck_needs`, and then loads the direct target.  It does
not yet complete that sequence or implement versioned checkpoints, so it is
frontier evidence rather than S2/S3 acceptance.  Its current source preflight
checks all selected source nodes except the already-executing loader; the
outer release lock authenticates that loader and the generated contracts.

The LP assembly normalization's exact-set argument and remaining S3 gates are
documented in `compatibility/lp_exact_result_coverage.md`.

The fail-closed ordering is exercised against a compiled Candle executable by
`test_flyspeck_loader_guard.sh`; the negative test must reach the exact mode
exception without reaching filesystem compatibility or the success marker.
With `full` selected, `test_flyspeck_loader_frontier.sh` now proves that the
compiled path passes the former manifest-environment, ordinary-file,
`Filename`, standard `load_path`, logical source-identity, digest-preflight,
overlay-selection, static-library, metadata, `Toploop`, `loaded_files`, and
`file_on_path`, phrase-boundary, loaded-file EOF, strictbuild `loadt`, parser
or-pattern, `%s` formatting, module-item separator, and trailing-sequence
frontiers.  It selects and completes the normalized `parser_verbose.hl`, then
selects normalized `general/debug.hl` and stops at its line 16
`open Parser_verbose` declaration.  The failed debug action commits no
identity and emits no completion marker.  The pinned repository has exactly 17
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
a compiler name-resolution proof.  The compiled boot now accepts only complete
standalone `#load "unix.cma";;` and `#load "str.cma";;` phrases and selects the
corresponding fixed static module.  Every other library and every embedded or
malformed use fails closed.  This exact selection is not full member
compatibility; the per-member evidence and failures below remain authoritative.

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
`process_to_string` pattern against a compiled Candle, checks deterministic
zero-only load-report telemetry, and proves that arbitrary commands, process
creation, `mkdir`, and `chdir` fail closed.  The manifest also freezes the full
32-site call chain through the historical `Glpk_link`/`Lpproc` generator
helpers.  There is no selected external qualified consumer, and the only
selected `open Glpk_link` is inside `Lpproc`; `Lpproc.execute` itself is
definition-only.  The LP certificate path separately removes its original
mkdir/chdir/command/extraction block through the authenticated ordinary-file
normalization.  This is static non-use evidence, not proof against reflection
or an S3 claim; complete execution and final fingerprints remain mandatory.
General process, mutable-directory, and directory-creation behavior remains
unimplemented and fails explicitly.
The overall directive status is therefore
`exact-static-link-selection-active-member-compatibility-partial`, not a claim
of complete `unix.cma` behavior.

The selected graph also has 23 executable qualified `Digest` occurrences:
11 `file`, three type `t`, two `string`, and seven `to_hex`; it has no
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
TextIO-backed ordinary-file predicate.  The selected LP path no longer needs
directory enumeration: the manifest supplies 39 exact filenames.  The sole
compressed member is authenticated and expanded before Candle starts under
`flyspeck_lp_archive_contract.json`; the runtime rejects `.gz` and invokes no
shell, `tar`, `rm`, temporary-directory, or custom FFI operation.  Container
preparation is not proof evidence: Candle still unmarshals and verifies the
resulting certificate bytes.  OCaml-compatible directory operations used by
other unresolved source paths remain open.

The compiled executable now starts from the repository root through relative
links to its generated boot/config inputs.  The obsolete `chdir` boot suffix,
unrestricted `system` bridge, custom-FFI C patch, and their call sites are not
part of the source tree or build recipe.  Relocation of the complete checkout
therefore preserves startup without granting an ambient process capability.

Schema-4 direct evidence supplies loader-execution evidence while retaining
the original-source generated dependencies explicitly:

- `candle/build/insulate.ml` must be generated from the pinned compiler's
  `types.txt` by the pinned `insulate.py` recipe.  It remains a generated
  contract even when an ignored local build happens to contain the file, so
  the source manifest is independent of worktree build state.  Direct
  evidence-v4 classifies the exact linked output and the manifest-pinned
  `candle/flyspeck_source_digests.ml` as generated executed controls; and
- upstream Flyspeck serialization writes and reloads a temporary theorem-digest
  module.  The exact selected normalization now removes the load-time
  `Filename.temp_file` allocation and makes both deferred output and reload
  fail closed.  Thus the selected direct run creates no such generated runtime;
  re-enabling theorem-digest output would require a separately versioned,
  attempt-local atomic lifecycle.

Removing `Filename.temp_file` also removes exactly its two Candle diagnostic
stdout lines, one for `Filename.temp_file` and one for
`Filename.get_temp_dir_name`.  No byte-for-byte stdout equivalence is claimed:
the preservation scope is the selected proof state, source-action semantics,
and semantic fingerprints, and excludes consumers of those diagnostics.

The evidence-v4 closure separately classifies completed outer roots, selected
nested `#flyspeck_loadt` sources observed through the logical ledger, other
expected nested sources, generated executed controls, and derivation-only
inputs.  `flyspeck_full_build.ml` is derivation-only; the authenticated
instrumented prefix derived from it is the executed attempt control.  The
closure follows three selected standalone strictbuild actions, excludes
`build/use_serialization.hl`, and adds `serialization.hl` plus its selected
`update_database_400.ml` branch only after action 295.  The pinned CakeML boot
uses a pending-identity stack for nested actions, and the runtime validates the
exact final ledger prefix `[serialization, update_database_400]` before
emitting action 295's delta-bound marker.  Schema 4 adds the exact nonce-bound,
loader-owned physical trace for ordinary nested directives and the host replays
its parent stack and canonical cache.  Exact lexical aliases are preserved in
the source bindings while sharing one canonical logical identity: action 126's
`Filename.concat` spelling includes the repeated separator before `..`, and
action 145 begins `../formal_lp/...`.

New direct attempts use disjoint evidence schema 5. At the exact final
boundary, after selected `serialization.hl` is available, the postlude observes
`Serialization.full_digest_thm` for the LP result, nonlinear inventory,
Flyspeck implication, and Candle L2 implication in fixed order. These are
nonce-bound sorted dependency-history MD5 values, not retained kernel traces or
approved identities. The immutable attempt also binds an exact semantic
coverage plan: source closure/physical-trace identities, the plan/manifest/
materialization hashes, ordered fingerprint requests, and all 39 authenticated
LP-certificate inputs. The receipt coverage is deterministically rederived
from the bound observations and keeps source, LP, nonlinear, and final-
implication status separate. Certificate inputs are authenticated but their
individual reads are not traced.

Schema 5 contains no semantic approval or finalizer. It requires PFT use,
approval presence, S2 eligibility, S3 eligibility, and S2/S3 evidence all to be
false. Schema 4 remains valid only under its own permanently nonpromotable
validator; partial schema upgrades fail closed.

Promotion still requires the proof-built and exactly linked CakeML binary,
clean and repeated direct strata, approved semantic fingerprints, and the
remaining release gates.  Until those gates pass, the manifest does not
advance S1, S2, or S3.
