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

- CakeML integration: `36e2245f42d4759063615c97fec51865798ca894`;
- HOL4 proof build: `a390cbabd3a4521bab4ee20281e3e42933a8a3ae`;
- direct Flyspeck: `1ce0353008eba83d3c76ae9a25c3c242e4802d53`;
- normalization contract SHA-256:
  `ac925270aa6a8605a8f70ab170ff965c3e4a4d6410623e3d3a6d51976ff1da08`;
- current authenticated overlay root:
  `/project/flyspeck-candle-runs/v13-normalized-overlay-f7dac3a-ac925270`;
- prepared `hard_7.dat` SHA-256:
  `0ca1b5b6ceba53537ac5d95ffddd883bb297e7d48c30ac241de4f3ec71ab5526`;
- current authenticated generated-input root:
  `/project/flyspeck-candle-runs/v13-generated-lp-0ca1b5b6`.

The preparation tool re-derives these facts from
`flyspeck_manifest.json`, both contract files, both receipts, the clean
Flyspeck Git root, and the bytes on disk.  It authenticates all normalized
overlay outputs and the generated input, plus the original strictbuild,
Parser_verbose, and Debug sources.  The compiled process independently checks
the original and normalized source MD5 identities and the two deterministic
strictbuild metadata inputs before source evaluation.

## Reproduction

Produce the pinned x64/64 bootstrap with the canonical controller, build a
fresh integrated Candle executable, and run the bounded gate:

```sh
cd /project/worktrees/candle-integration-v13
/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
  /project/worktrees/candle-integration-v13/build-local-cakeml-bootstrap.sh \
  /project/worktrees/cakeml-flyspeck-v13-integration \
  /project/worktrees/HOL-cakeml-dopen-v13 \
  /project/flyspeck-candle-runs/v13-dopen-bootstrap-canonical.log \
  /project/flyspeck-candle-runs/v13-dopen-bootstrap-preflight.json \
  /project/flyspeck-candle-runs/v13-dopen-bootstrap-provenance.json
./build-local-cakeml.sh \
  /project/worktrees/cakeml-flyspeck-v13-integration \
  /project/flyspeck-candle-runs/v13-dopen-bootstrap-provenance.json
CANDLE_FLYSPECK_DOPEN_LOG=/project/flyspeck-candle-runs/v13-dopen-direct-prefix.log \
  candle/test_flyspeck_dopen_prefix.sh \
  ./candle.sh \
  /project/worktrees/flyspeck-v13-source \
  /project/flyspeck-candle-runs/v13-normalized-overlay-f7dac3a-ac925270 \
  /project/flyspeck-candle-runs/v13-generated-lp-0ca1b5b6
```

Do not run this command concurrently with a build or another compiled Candle
workload in the same worktree.

The first command refuses a dirty or mismatched Candle/CakeML/HOL worktree,
wrong cwd, stale receipt, unexpected controller/build environment, a failed
bootstrap transcript, a missing output, or any pin drift. Its immutable
preflight binds the single controller process's direct `-I -S` Python
execution, fixed tools,
launch/runtime ELF closures, exact roots and commits, checkout lock inode, and
the mechanically derived generated-output inventory before the build. It
archives and removes only `cake.S`, `config_enc_str.txt`, the exact 18-target
`.hol/objs` output set, their exact make-dependency files, and retry-only
`*Script.ui`/`*Script.uo` transients, plus both relevant `.hol/make-deps/lastmaker`
files. The two `lastmaker` postimages must freshly name only the pinned absolute
`HOL_ROOT/bin/Holmake` path. The tracked `candle_boot.ml`, `basis_ffi.c`,
and `Makefile` links are preserved and bound to their exact commit blobs and
in-root ordinary targets. Failure retains the archive, log, and partial outputs;
there is no automatic restore mutation. The schema-5 final bootstrap record
authenticates the ordinary bytes of `bin/Holmake`, `bin/hol`, and
`bin/hol.state`, the exact resolved ELF closures of both launchers (including
their fixed absolute RUNPATH), and exactly one complete trailing GNU `time -v`
footer for the pinned build command with final status zero and ordered
x64Bootstrap completion evidence, including the exact ordered `[1/18]` through
`[18/18]` target sequence.
Every other pre-existing CakeML `.hol/objs` ordinary file is content-inventoried
before and after. Its bytes are authenticated, but its derivation is expressly
not claimed to have been replayed and remains in the documented boundary.
The controller likewise inventories all ordinary files recursively under every
pinned HOL4 `.hol/objs` directory, all 2,407 direct `sigobj` entries (including
exact link text and each symlink's resolved in-root ordinary payload), and the
seven generated HOL sources used outside those sets. This conservative HOL
proof-artifact closure is validated before and after and retained with the
receipt, but is explicitly content-bound rather than independently rederived.
All ordinary HOL4 `.hol/make-deps` files and all non-transitioned CakeML
ancestor `.hol/make-deps` files are also inventoried before and after. Every
retained `lastmaker` must contain exactly the pinned absolute Holmake path;
these dependency artifacts are content-bound inputs, not claimed source
derivations. The ignored HOL4 `.kernelidstr` read by Holmake is also bound
exactly through the launch-runtime record.
The requested `/bin/sh` link, resolved executable bytes, and ELF closure are
authenticated because Holmake builders invoke it with `-c`. The CakeML
`cv_translator/cake_compile_heap` selected through the pinned final
x64Bootstrap Holmakefile's HMF `POLY` branch is content-bound before and after
as a non-rederived input, together with that Holmakefile's committed bytes.

The local build revalidates that record before copying ignored generated files,
then links with a fixed single-job GNU make and C-compiler command.  Before its
schema-6 `candle/build/cakeml-build-provenance.json` is accepted, it copies the
authenticated patched `cake.S`, `basis_ffi.c`, and `Makefile` to a fresh private
directory, forcibly relinks them, captures and re-derives the exact make, CC,
cc1, assembler, collect2, and linker argv, binds the corresponding tool files,
GCC query/specification identities, fixed environment and flags, and compares
the fresh candidate ELF byte-for-byte with the installed `cake`.  Both Dopen
runners require that record to match the clean Candle checkout, the exact
linked executable and other build outputs, assembly patch derivation, retained
bootstrap evidence, runtime ELF closure, and the compiler's embedded CakeML/HOL
revision lines before starting Candle.

This gate explicitly leaves the semantics of the exact host toolchain and
system inputs in the trusted boundary.  In particular, kernel/process/filesystem
semantics, dynamic libraries used by the build tools, system headers, compiler
internal data, linker scripts, startup objects, and archives are not promoted
to verified evidence merely because their selected tool executables, command
plan, final runtime closure, and output bytes are authenticated.  This boundary
is also an exact machine-checked object in the linked provenance record.
The outer `/usr/bin/env -i` is required, but its own pre-start loader environment
cannot be checked retrospectively by the controller. That interval, kernel and
same-UID mutation semantics remain explicitly trusted.

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
