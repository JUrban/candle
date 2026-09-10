# Direct boundary 00--029 development attempt at 67be95d

This records DEVELOPMENT / NON-RELEASE evidence only. It is not qualified or
promotable evidence and makes no S1, S2, S3, or release claim. No qualified S1
runtime, source, report, transcript, or evidence byte was changed.

## Print_types compatibility batch

The immutable predecessor attempt at
`/project/flyspeck-candle-runs/v14-dev-direct-boundary-93a5310-attempt-001`
failed before all boundary actions in pinned
`text_formalization/general/print_types.hl` at the original line 64 phrase:

```text
let setify_types tm = ((sort (<)) o setify o get_term_types) tm
```

Candle reported `Type mismatch between (_6 -> int list) -> _6 -> int list and
((_10 -> _10 -> bool) -> _10 list -> _10 list) -> _11`. That predecessor log
has SHA-256 `f9438f1c22ee26d24696867a43bba1587efc81d460299b25da4528d195d5c76e`;
its development receipt has SHA-256
`94a58be803306293a6e4560bd7d757de2a6762796f325bdf392795f493414f87`.

Commit `67be95dc5f4f65cf5468908c48ebb21d9a43df5d` adds the one hash-pinned
`PROJECT-PRINT-TYPES-S3-COMPATIBILITY-001` normalization. It retains the
existing fail-closed selected-graph `unsuppress` rule, defines the exact
atom-type comparator
`Pair.compare String.compare Type.compare x y < 0`, and supplies that
comparator to every one of the file's four unary `setify` sites and their
adjacent sorts. The local comparator does not shadow the numeric `<` used later
in the file. A first whole-file probe showed that Candle's compatibility List
module does not expose OCaml's `List.flatten` alias; the same exact line-85
operation therefore spells that one call as the available, semantically
identical `List.concat`.

The normalized file is 3,318 bytes, SHA-256
`5135cd5b24a837a94ba49fab5eb54e3bbd8c2ed47c9198dc80e9bd6e73c886dd`,
and MD5 `937774e3558ecfe48afda2f7f54dc5b9`. The complete normalized file loaded
after the real `hol.ml`; duplicate removal, same-name/different-type
distinctness, lexicographic order, numeric `<`, and concatenation order all
passed focused Candle oracles. The final static gates passed: normalizer 17/17,
manifest 28/28, parser diagnostic 56/56, all-inventory 17/17, pilot selection
20 exact nodes, and all-inventory selection 400 exact nodes. Manifest,
normalization, and prior Debug compatibility checks also passed.

The regenerated authorities are:

- manifest SHA-256
  `ed352c40e1addecc25dd158eefc1cb5ad954533378c4ad495fdd4ce98c58c6ba`;
- normalization contract SHA-256
  `c80a8cc917fc59be9c0228bc8bd92ce150dc839474debfb94813d16bd1dae030`;
- pilot descriptor SHA-256
  `e3f6694078ff5ce5a0d1c914553248454b76b73f64cac788f60bb5cdda8ac192`;
- all-inventory descriptor SHA-256
  `5f08d153dc1f716ccc19d0676924ec9169ef2cc6c359f389c229cf7176d71b94`;
- all-400 ordered effective/prepared roots
  `be3d25080be18b7c1579bc4004f92ad83d7be7674fc9af5c88c220533edbac9c`
  and
  `02aba41ec2dd8fe28ee351493560c74136c18d083f739185d85afc4b461b07d7`.

## Fresh development run

Fresh exact-head roots were materialized at:

- `/project/flyspeck-candle-runs/v14-normalized-overlay-67be95d-dev-001`;
- `/project/flyspeck-candle-runs/v14-generated-inputs-67be95d-dev-001`;
- `/project/flyspeck-candle-runs/v14-stratum-plan-67be95d-dev-001`.

Independent reconstruction matched all 297 plan actions and all 10 prefixes.
The plan SHA-256 is
`8c686d1082a12a7673b8597d4a6baa77588da5e4b6e07adb388c1f17b24c4fb6`.
The attempt root is
`/project/flyspeck-candle-runs/v14-dev-direct-boundary-67be95d-attempt-001`.
Its exact launch is recorded in `launch-command.txt`. It used the existing
development Candle binary (SHA-256
`7c6705199dae8ecf79a72a85d65ab6a4727b411cdfd34f86f999151a2d292ced`),
not a source-head-qualified rebuild. The source-trace observer and release
check/postlude were deliberately omitted.

Before launch, one nonce was verified across the nonce file, both runtime
configuration fields, and all 30 action markers. The current plan/root and
Print_types identities were bound, and no predecessor root, ID, or normalized
hash remained. The instrumented prefix has SHA-256
`88f5483446e01d1058884ce08a766f7589b6c9a9809b559f735114822a42ac2e`
and MD5 `87bcbe86e0417d6c9273cd6b7fe9f284`.

## Result and next genuine failure

Normalized `parser_verbose.hl`, `debug.hl`, and `print_types.hl` all completed.
`Print_types.atom_type_lt`, `Print_types.setify_types`, and both relevant print
functions were exported. This closes the observed Print_types incompatibility
for this functional run.

The next genuine compatibility failure is in unnormalized
`text_formalization/general/hol_pervasives.hl`. Candle reports at line 24 while
compiling the `needs` definition whose pinned source call is line 25:

```text
ERROR: Undefined variable: loadt at line 24

let needs s =
^^^^^^^^^^^^^^
```

No line beginning with the exact nonce-bound action-success marker was
emitted, so 0 actions were reached and 0 passed. The later prefix diagnostic
`Undefined variable: candle_flyspeck_stratum_commit_action` is a cascade:
strictbuild setup failed before it defined that ledger helper. The action-0
directive's later `Already loaded` message is not an action-success marker and
does not upgrade the 0/0 result.

The run took 6:07.93 at 99% of one CPU, with maximum RSS 4,235,392 KiB. The
interactive runtime exited zero despite the source errors. The immutable
`candle.log` has SHA-256
`246685eda25eb901ca0853a77ae4d5268ebc28dd1a60cb5a39e53961498f2f36`.
The fail-closed development receipt has SHA-256
`c769119680e26649f8b923d3efaf9ad5e8011ddfeb447698aee6e21450376076`.

Before changing this new boundary, inspect historical `fix-top100` and all
relevant Candle history for `hol_pervasives`/`loadt`, the normalized
strictbuild tail that should establish the legacy loading helpers, and the
current loader API. This attempt itself must remain immutable and must never
be promoted.
