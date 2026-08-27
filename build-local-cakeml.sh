#!/usr/bin/env bash
set -euo pipefail

usage() {
  printf 'usage: %s <CakeML checkout>\n' "$0" >&2
  exit 2
}

[[ $# -eq 1 ]] || usage

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cakeml_dir=$(realpath -- "$1")
manifest=$script_dir/candle/flyspeck_manifest.json
bootstrap_dir=$cakeml_dir/compiler/bootstrap/compilation/x64/64
build_dir=$script_dir/candle/build

[[ -d $cakeml_dir/.git || -f $cakeml_dir/.git ]] || {
  printf 'not a CakeML Git checkout: %s\n' "$cakeml_dir" >&2
  exit 2
}
[[ -r $manifest ]] || {
  printf 'missing Flyspeck manifest: %s\n' "$manifest" >&2
  exit 2
}

expected_head=$(
  python3 - "$manifest" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as source:
    manifest = json.load(source)
print(manifest["dopen_corpus_contract"]["verified_cakeml_integration"]["commit"])
PY
)
actual_head=$(git -C "$cakeml_dir" rev-parse HEAD)
[[ $actual_head == "$expected_head" ]] || {
  printf 'CakeML revision mismatch: expected %s, found %s\n' \
    "$expected_head" "$actual_head" >&2
  exit 1
}
git -C "$cakeml_dir" diff --quiet
git -C "$cakeml_dir" diff --cached --quiet

required=(cake.S config_enc_str.txt candle_boot.ml basis_ffi.c Makefile)
for input in "${required[@]}"; do
  [[ -r $bootstrap_dir/$input ]] || {
    printf 'missing bootstrapped CakeML input: %s\n' \
      "$bootstrap_dir/$input" >&2
    exit 1
  }
done

mkdir -p "$build_dir"
for input in "${required[@]}"; do
  cp -L -- "$bootstrap_dir/$input" "$build_dir/$input"
done

(
  cd "$build_dir"
  patch --batch --forward cake.S ../cake.S.patch
  make -j"${CANDLE_BUILD_JOBS:-2}" cake
  ./cake --types </dev/null >types.txt 2>&1
  python3 ../insulate.py types.txt insulate.ml
)

ln -sfn candle/build/config_enc_str.txt "$script_dir/config_enc_str.txt"
ln -sfn candle/build/candle_boot.ml "$script_dir/candle_boot.ml"

printf 'CakeML head: %s\n' "$actual_head"
sha256sum \
  "$build_dir/cake.S" \
  "$build_dir/cake" \
  "$build_dir/config_enc_str.txt" \
  "$build_dir/candle_boot.ml" \
  "$build_dir/types.txt" \
  "$build_dir/insulate.ml"
