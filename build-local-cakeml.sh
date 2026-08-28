#!/bin/bash -p
set -euo pipefail
export PATH=/usr/bin:/bin
export LC_ALL=C

for variable in ${!LD_@} GLIBC_TUNABLES BASH_ENV ENV; do
  if [[ -v $variable ]]; then
    printf 'forbidden build environment: %s\n' "$variable" >&2
    exit 1
  fi
done

usage() {
  printf 'usage: %s <CakeML checkout> <bootstrap-provenance.json>\n' "$0" >&2
  exit 2
}

[[ $# -eq 2 ]] || usage

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cakeml_dir=$(realpath -- "$1")
bootstrap_record=$(/usr/bin/realpath -- "$2")
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
  /usr/bin/python3 -I - "$manifest" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as source:
    manifest = json.load(source)
print(manifest["dopen_corpus_contract"]["verified_cakeml_integration"]["commit"])
PY
)
actual_head=$(/usr/bin/git -C "$cakeml_dir" rev-parse HEAD)
[[ $actual_head == "$expected_head" ]] || {
  printf 'CakeML revision mismatch: expected %s, found %s\n' \
    "$expected_head" "$actual_head" >&2
  exit 1
}
/usr/bin/git -C "$cakeml_dir" diff --quiet
/usr/bin/git -C "$cakeml_dir" diff --cached --quiet

/usr/bin/python3 -I "$script_dir/candle/cakeml_artifact_provenance.py" \
  check-bootstrap \
  --candle-root "$script_dir" \
  --cakeml-root "$cakeml_dir" \
  --record "$bootstrap_record"

required=(cake.S config_enc_str.txt candle_boot.ml basis_ffi.c Makefile)
for input in "${required[@]}"; do
  [[ -r $bootstrap_dir/$input ]] || {
    printf 'missing bootstrapped CakeML input: %s\n' \
      "$bootstrap_dir/$input" >&2
    exit 1
  }
done

build_jobs=${CANDLE_BUILD_JOBS:-2}
[[ $build_jobs =~ ^[1-9][0-9]*$ ]] || {
  printf 'CANDLE_BUILD_JOBS must be a positive decimal integer\n' >&2
  exit 2
}

mkdir -p "$build_dir"
for input in "${required[@]}"; do
  cp -L -- "$bootstrap_dir/$input" "$build_dir/$input"
done

(
  cd "$build_dir"
  /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
    /usr/bin/patch --batch --forward cake.S ../cake.S.patch
  /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
    /usr/bin/make -j"$build_jobs" cake
  /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
    ./cake --types </dev/null >types.txt 2>&1
  /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
    /usr/bin/python3 -I ../insulate.py types.txt insulate.ml
)

/usr/bin/python3 -I "$script_dir/candle/cakeml_artifact_provenance.py" \
  record-linked \
  --candle-root "$script_dir" \
  --cakeml-root "$cakeml_dir" \
  --bootstrap-record "$bootstrap_record" \
  --write "$build_dir/cakeml-build-provenance.json"

ln -sfn candle/build/config_enc_str.txt "$script_dir/config_enc_str.txt"
ln -sfn candle/build/candle_boot.ml "$script_dir/candle_boot.ml"

printf 'CakeML head: %s\n' "$actual_head"
/usr/bin/sha256sum \
  "$build_dir/cake.S" \
  "$build_dir/cake" \
  "$build_dir/config_enc_str.txt" \
  "$build_dir/candle_boot.ml" \
  "$build_dir/types.txt" \
  "$build_dir/insulate.ml" \
  "$build_dir/cakeml-build-provenance.json"
