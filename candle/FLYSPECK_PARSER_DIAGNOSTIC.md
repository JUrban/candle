# Flyspeck translated-parser diagnostic

## Claim boundary

`flyspeck_parser_diagnostic.py` prepares an authenticated, parser-only smoke
test for the translated Candle OCaml parser, `caml_parser$run`. It is
categorically non-promotable: it is not an inference run, a source execution,
a theorem check, a semantic fingerprint, a checkpoint, or S1/S2/S3 evidence.

The controller never uses the generic CakeML `parse_prog` language (including
`--print_sexp`) and never treats the `--candle` REPL as a parser oracle. The
REPL proceeds from parsing into inference and evaluation and is therefore not
a safe implementation of this gate.

## Exact profiles

`flyspeck_parser_diagnostic_pilot.json` predeclares 20 nodes. Its order is the
first-discovery preorder obtained from manifest bootstrap roots, then build
action roots, recursively following only `status=resolved` selected source
dependencies in manifest list order. This first pilot is intentionally a
bootstrap/core smoke test, not representative Flyspeck corpus coverage. It
does include the original `candle/kernel.ml` bytes and their
`Kernel.EQ_MP` parser-regression trigger.

That traversal reaches 392 of the manifest's 400 nodes. The pilot binds the
other eight by source identity and reason rather than silently calling 392
"all 400": four Candle-generated/control nodes are not reachable through the
runtime source graph, and four Flyspeck nodes are reached only by
`resolved-dynamic` actions. Do not describe the 20-input core pilot as corpus
coverage.

`flyspeck_parser_diagnostic_all_inventory.json` defines the separate
`all-inventory` profile. It contains the 392 first-discovery
nodes followed by the eight exclusions in lexicographic source-key order, so
its 400 inputs are an exact set-equal partition of the authenticated manifest.
`check-all-inventory` independently regenerates and compares it. Both
`materialize --profile all-inventory` and `run --profile all-inventory` require
all 400 inputs to be ready and launch exactly one fresh parser process per
input; there is no accepted partial profile. Materialization of the committed
authorities produces 382 byte-identical inputs and 18 normalized inputs. The
normalization contract accounts for all 727 classified loader sites.

For each selected source, the generator:

- authenticates the exact Git blob and manifest byte/MD5/SHA-256 identity;
- replaces only manifest-classified standalone loader lines with equal-length
  spaces, preserving newlines and byte offsets, because Candle consumes those
  phrases before calling the OCaml parser;
- retains embedded loading expressions as parser input but records that the
  gate never executes them;
- refuses to launch a source with an unknown/dynamic standalone action or an
  unmodeled normalization; and
- binds the complete generated-input inventory while stating that no generated
  input is consumed and none of its semantics is checked.

## Runtime protocol and current blocker

The linked compiler must first accept an empty-stdin capability request:

```text
cake --candle-parser-diagnostic-capability-v1
```

and emit exactly:

```text
CANDLE_CAMLPARSER_DIAGNOSTIC_CAPABILITY_V1	caml_parser$run	stdin-exact-bytes	parser-only	no-inference	no-evaluation
```

The capability process must exit 0, write that one line to stdout, write no
stderr, and must not read stdin. Only then may the controller send one prepared
source per fresh process using
`cake --candle-parser-diagnostic-v1 NONCE`, where `NONCE` is exactly 64
lowercase hexadecimal characters. The only accepted replies are:

```text
CANDLE_CAMLPARSER_DIAGNOSTIC_V1	NONCE	OK
CANDLE_CAMLPARSER_DIAGNOSTIC_V1	NONCE	PARSE_ERROR
```

`OK` requires exit code 0 and empty stderr. `PARSE_ERROR` requires exit code
**exactly 65**, not merely a nonzero code. Its stderr must be well-formed UTF-8
(the protocol does not perform Unicode normalization).
The runtime does not compute or emit an error digest. After validating the
exact runtime line, exit status, and UTF-8 stderr, the controller records the
lowercase 64-hex encoding of:

```text
SHA256(ASCII("CANDLE_CAMLPARSER_ERROR_V1") || byte(0x00) || STDERR_BYTES)
```

`STDERR_BYTES` is the exact UTF-8 byte stream emitted on stderr, including any
newlines; there is no decoding, newline conversion, length prefix, or terminal
NUL in the digest preimage. The newline terminating the stdout protocol record
is not part of the preimage. This is controller receipt metadata, not a runtime
wire field. Any other exit code, output byte, nonce, or encoding is rejected;
a runtime-supplied digest field is therefore also rejected.

This three-field error wire format plus controller-side stderr digest is
`parser_runtime_protocol.schema = 2`. Schema 1 described the superseded
runtime-supplied digest contract and must not be used for the CakeML migration.

A generic compiler, old compiler, REPL, or protocol variation is rejected
during the empty handshake before any corpus bytes are sent. Both the
capability process and every parser process run with fixed environment and
CPU, address-space, process-count, core-file, and output-file resource limits.
Stdout and stderr are never connected to unbounded controller pipes. Each goes
to a fresh ordinary file below a private mode-0700 staging directory, with
`RLIMIT_FSIZE` set to the recorded effective per-stream cap (1 MiB by default,
configurable only from 1 through 16 MiB). Every child starts a fresh session;
Linux pidfd supervision keeps the leader unreaped while the controller kills
the entire process group on normal exit or timeout. The no-fork child limit is
an additional defense against escaped descendants.

The manifest pins CakeML integration commit
`964406486a52e1a53a94eade4cf86a666dc8055a`, which implements the dedicated
protocol and its proof obligations. Its clean x64 proof replay and canonical
bootstrap/link qualification are still in progress, so the pin alone does not
qualify a runtime. Therefore the exact blocking condition is:

> No pilot or all-inventory process may be launched until the protocol commit's
> proof replay succeeds, that commit is pinned by the Candle manifest, and the
> resulting compiler is canonically bootstrapped and linked to the exact Candle
> controller commit under validated provenance.

No parser pilot was launched while implementing this controller.

## Smallest CakeML entrypoint change

The smallest entrypoint compatible with this controller can be confined at
source level to
`compiler/bootstrap/translation/compiler64ProgScript.sml`, where
`parse_ocaml_syntax` already directly calls `caml_parser$run` and `main` already
owns stdin and command-line dispatch:

1. Translate exact-list argument predicates: the capability form is the sole
   argument, and the run form is exactly the option plus one validated 64-hex
   nonce. A `MEM`-style flag test is insufficient.
2. Add a pure parser-diagnostic function whose only semantic parser call is
   `caml_parser$run (explode input)`. Format its success or parser failure using
   the exact wire bytes above. Do not route through `parse_ocaml_syntax` if that
   would obscure the direct call in its specification.
3. Put the two branches before REPL/general compilation dispatch. The
   capability branch must not open stdin; the run branch reads stdin exactly
   once and parses exactly those bytes.
4. On parser error, emit the exact three-field `PARSE_ERROR` stdout line and
   canonical UTF-8 diagnostic, then invoke an exact exit FFI path carrying byte
   value 65. Digesting is deliberately a controller operation. The existing
   `nonzero_exit_code_for_error_msg` helper is insufficient because it does not
   promise exit status 65.
5. Do not invoke `infertype_prog`, `check_and_tweak`, `eval`, `compile_64`, or
   `parse_prog` in either diagnostic branch.
6. Prove the translated parser-diagnostic functions and both new `main`
   branches. Add separate capability and run-mode STDIO/COMMANDLINE/exit-event
   specifications that establish empty-stdin behavior, exact parser input,
   output bytes, and absence of inference/evaluation by construction.
   Strengthen the existing ordinary-compiler `main_spec`,
   `main_whole_prog_spec`, and `semantics_compiler64_prog` assumptions to
   exclude both exact diagnostic modes.

No parser grammar or parser translation theory needs a new API:
`caml_parserProgTheory` already translates `caml_parser$run`, and
`compiler64ProgScript.sml` already consumes it. The directly affected build
frontier is `compiler64ProgTheory.uo`, then the x64 bootstrap evaluation
`compiler/bootstrap/compilation/x64/64/x64BootstrapTheory.uo` and its `cake.S`;
the end-to-end compiler proof in
`compiler/bootstrap/compilation/x64/64/proofs/x64BootstrapProofScript.sml`
consumes `semantics_compiler64_prog` and must also be replayed or extended for
the new mode. Other architecture bootstraps that consume `compiler64ProgTheory`
are downstream too, although they are not needed for this x64 pilot. An
incremental development checkout may reuse unchanged predecessors, but the
project's canonical bootstrap controller qualifies `cake.S` by rebuilding its
exact forced 18-target closure, so release qualification still requires
another full canonical bootstrap.

This change necessarily creates a new CakeML commit, changes the manifest's
pinned CakeML identity, changes the Candle manifest/pilot digest, and requires
a new exact-head linked-provenance record. An old linked compiler cannot
validate the new parser or satisfy the capability handshake.

## Invocation and release order

From the exact committed Candle checkout, using fresh destination paths:

```sh
/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
  /usr/bin/python3 -I -S candle/flyspeck_parser_diagnostic.py check-pilot \
  --candle-root /absolute/candle

/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
  /usr/bin/python3 -I -S candle/flyspeck_parser_diagnostic.py materialize \
  --profile pilot \
  --candle-root /absolute/candle \
  --flyspeck-root /absolute/flyspeck \
  --output-root /fresh/parser-pilot-plan

/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
  /usr/bin/python3 -I -S candle/flyspeck_parser_diagnostic.py run \
  --profile pilot \
  --plan-root /fresh/parser-pilot-plan \
  --candle-root /absolute/candle \
  --candle-head CANDLE_40_HEX_COMMIT \
  --flyspeck-root /absolute/flyspeck \
  --flyspeck-head FLYSPECK_40_HEX_COMMIT \
  --output-root /fresh/parser-pilot-result
```

After the 20-input pilot succeeds, materialize and run the exact 400-input
profile with new destinations:

```sh
/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
  /usr/bin/python3 -I -S candle/flyspeck_parser_diagnostic.py check-all-inventory \
  --candle-root /absolute/candle

/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
  /usr/bin/python3 -I -S candle/flyspeck_parser_diagnostic.py materialize \
  --profile all-inventory \
  --candle-root /absolute/candle \
  --flyspeck-root /absolute/flyspeck \
  --output-root /fresh/parser-all-inventory-plan

/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
  /usr/bin/python3 -I -S candle/flyspeck_parser_diagnostic.py run \
  --profile all-inventory \
  --plan-root /fresh/parser-all-inventory-plan \
  --candle-root /absolute/candle \
  --candle-head CANDLE_40_HEX_COMMIT \
  --flyspeck-root /absolute/flyspeck \
  --flyspeck-head FLYSPECK_40_HEX_COMMIT \
  --output-root /fresh/parser-all-inventory-result
```

The controller rejects any other Python flags or environment, any system-wide
`/etc/ld.so.preload`, symlinked authority/output path component, or changed
authenticated Python/runtime dependency. It binds `/proc/self/exe`, the Python
ELF closure and controller tools using the established direct-runner policy.

`materialize` requires the controller, selected profile descriptor, manifest,
policy helpers, preparation authorities, and every selected source to be exact
committed blobs. At run time, the supplied
Candle and Flyspeck roots and heads independently reconstruct the canonical
plan, every prepared input, every promotion flag/claim, and the host receipt;
the published tree must match byte for byte. Fully rehashing a forged tree is
therefore not authority. Both plan and result destinations must be fresh and
outside the Candle and Flyspeck authority roots.

The run exact-loads the commit-bound transition/provenance/runtime-lock policy
from captured source bytes without import or bytecode lookup. It holds a shared
lock on the authenticated `candle/build` inode across linked-provenance
validation, the empty capability handshake, all parser attempts, postflight
runtime validation, evidence capture, and result publication. A result embeds
read-only snapshots of the exact plan and inputs, manifest, selected profile,
normalization authorities when applicable, host
receipt, linked provenance, controller/policy sources, every `linked.outputs`
member, every selected source's original Git blob alongside its prepared input,
the patch plus patch/native-link inputs, the CakeML runtime ELF closure, the
controller Python executable/ELF closure and host tools, and the schema-7
transition record when applicable. This makes the exact masking transformation
auditable offline. Large objects are streamed into independent ordinary
copies—never mutable hardlinks. A closed inventory is rehashed before
publication, so an omitted, extra, symlinked, writable, or tampered snapshot
member rejects the result. This can intentionally cost multiple GiB once a
linked compiler exists.

Publication retains stable descriptors for the staging directory and both
parents, uses descriptor-relative `renameat2(RENAME_NOREPLACE)`, verifies the
published inode identity, and rehashes the complete opened tree after the
rename before reporting success. Modes 0555/0444 are an audit and accidental-
mutation barrier, not immutability against another process with the same UID;
every later consumer must therefore revalidate the closed receipt inventory.

The published pilot receipt is schema 4. The all-inventory receipt is schema 5
and additionally closes its profile and source-preparation fields, its exact
authority directory, and all 400 prepared plan inputs. Both schemas close the
top-level field set over the sealed `runtime_execution` record, require that
record's byte count and SHA-256 to equal the archived linked runtime, and
require exactly one original-source record for every selected input. Older
receipt schemas are not compatible.

While the shared build lock is held, the controller opens the authenticated
linked runtime with `O_NOFOLLOW`, verifies one stable ordinary inode, and
copies those exact bytes into an anonymous mode-0500 memfd sealed against
write, growth, shrinkage, and further seal changes. The capability handshake
and every parser attempt execute that same inherited descriptor via
`/proc/self/fd`; they never reopen the mutable runtime pathname. Postflight and
pre-publication checks revalidate both the named linked runtime and the sealed
executed image. None of these measures changes the categorically
non-promotable claim boundary.
