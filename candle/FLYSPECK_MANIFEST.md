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
398 recursively reached source nodes, 417 selected dependency edges, and 42
hashed LP/archive/nonlinear inputs.  There are no unresolved build roots,
unreviewed dynamic loads, missing ordinary sources, path escapes, ambiguous
loads, or detected cycles.  Sixteen non-literal call sites have explicit
source-and-line reviews; the selected OCaml-version branch is pinned to 4.14.
The manifest also pins `flyspeck_l2_target.ml`, the direct Candle theorem glue
for `Candle_flyspeck_l2.tame_imp_kepler_conjecture`; that file has no trace
producer or theorem-import shortcut.

This artifact is deliberately not loader-execution evidence.  In particular,
two generated-runtime contracts remain visible:

- `candle/build/insulate.ml` must be generated from the pinned compiler's
  `types.txt` by the pinned `insulate.py` recipe; and
- Flyspeck serialization writes and reloads a temporary theorem-digest module,
  which needs a versioned, atomic generated-input/checkpoint lifecycle.

The next G6 slices must turn this inventory into the loader's enforced input
contract, reject manifest/source reorder and corruption, add relocation and
clean/resume tests, and prove that generated inputs are linked to the theorem
artifacts consumed in the direct run.  Until those gates pass, the manifest
does not advance S1, S2, or S3.
