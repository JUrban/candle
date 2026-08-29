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

## Exact pilot

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
`resolved-dynamic` actions. A future all-inventory plan must select all 400
explicitly. Before that expansion, use a separate deterministic Flyspeck-heavy
pilot: the first 20 `repository=flyspeck` entries in the same authenticated
first-discovery order, followed by the eight bound exclusions under explicit
handling rules. Do not describe the current core pilot as corpus coverage.

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

Only then may the controller send one prepared source per fresh process using
`cake --candle-parser-diagnostic-v1 NONCE`. Success and parser-error replies
bind that nonce and are fail-closed. A generic compiler, old compiler, REPL, or
protocol variation is rejected during the empty handshake before any corpus
bytes are sent.

The CakeML integration commit currently pinned by the manifest does **not**
implement these two options. Therefore the exact blocking condition is:

> No pilot process may be launched until a new, proof-built CakeML commit
> exposes the dedicated protocol directly around `caml_parser$run`, that commit
> is pinned by the Candle manifest, and the resulting compiler is bootstrapped
> and linked to the exact Candle controller commit under validated provenance.

No parser pilot was launched while implementing this controller.

## Smallest CakeML entrypoint change

The smallest entrypoint compatible with this controller is confined at source
level to
`compiler/bootstrap/translation/compiler64ProgScript.sml`, where
`parse_ocaml_syntax` already directly calls `caml_parser$run` and `main` already
owns stdin and command-line dispatch:

1. translate exact-argument predicates for the capability form and the run
   form (the latter carries one 64-hex nonce);
2. add a pure parser-diagnostic function whose only semantic call is
   `caml_parser$run (explode input)` and whose result is an OK or parser-error
   protocol record;
3. put those two branches before REPL/general compilation dispatch; the
   capability branch must not open stdin, and the run branch reads stdin once;
4. on a parser error, write diagnostics and use a dedicated nonzero-exit path;
   do not invoke `infertype_prog`, `check_and_tweak`, `eval`, `compile_64`, or
   `parse_prog`; and
5. prove the translated parser-diagnostic function and new `main` branches,
   while strengthening the existing ordinary-compiler `main_spec`,
   `main_whole_prog_spec`, and `semantics_compiler64_prog` assumptions to
   exclude the two diagnostic modes. Add a diagnostic-mode STDIO/COMMANDLINE
   specification so the capability's no-inference/no-evaluation claim is not
   based only on its output string.

No parser grammar or parser translation theory needs a new API:
`caml_parserProgTheory` already translates `caml_parser$run`, and
`compiler64ProgScript.sml` already consumes it. The directly affected build
frontier is `compiler64ProgTheory.uo`, then
`compiler/bootstrap/compilation/x64/64/x64BootstrapTheory.uo`/`cake.S`; the
end-to-end compiler proof in
`compiler/bootstrap/compilation/x64/64/proofs/x64BootstrapProofScript.sml`
must also be replayed or extended for the new mode. An incremental development
checkout may reuse unchanged predecessors, but the project's canonical
bootstrap controller qualifies `cake.S` by rebuilding its exact forced
18-target closure, so release qualification still requires another full
canonical bootstrap.

This change necessarily creates a new CakeML commit, changes the manifest's
pinned CakeML identity, changes the Candle manifest/pilot digest, and requires
a new exact-head linked-provenance record. An old linked compiler cannot
validate the new parser or satisfy the capability handshake.

## Invocation after the blocker is closed

From the exact committed Candle checkout, using fresh destination paths:

```sh
/usr/bin/python3 -I -S candle/flyspeck_parser_diagnostic.py check-pilot \
  --candle-root /absolute/candle

/usr/bin/python3 -I -S candle/flyspeck_parser_diagnostic.py materialize \
  --candle-root /absolute/candle \
  --flyspeck-root /absolute/flyspeck \
  --output-root /fresh/parser-pilot-plan

/usr/bin/python3 -I -S candle/flyspeck_parser_diagnostic.py run \
  --plan-root /fresh/parser-pilot-plan \
  --candle-root /absolute/candle \
  --output-root /fresh/parser-pilot-result
```

`materialize` requires the controller, pilot, manifest, and every selected
source to be exact committed blobs. `run` revalidates the immutable plan and
linked compiler provenance before the empty capability handshake.
