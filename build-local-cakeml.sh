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
[[ ! -e /etc/ld.so.preload && ! -L /etc/ld.so.preload ]] || {
  printf 'system-wide dynamic-loader preload is outside the build model\n' >&2
  exit 1
}

usage() {
  printf 'usage: %s <CakeML checkout> <bootstrap-provenance.json> [<source Candle checkout> <source Candle head> <bootstrap-transition.json>]\n' "$0" >&2
  exit 2
}

[[ $# -eq 2 || $# -eq 5 ]] || usage

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
cakeml_dir=$(realpath -- "$1")
bootstrap_record=$(/usr/bin/realpath -- "$2")
transition_mode=false
source_candle_dir=
source_candle_head=
transition_record=
if [[ $# -eq 5 ]]; then
  transition_mode=true
  source_candle_dir=$(/usr/bin/realpath -- "$3")
  source_candle_head=$4
  transition_record=$(/usr/bin/realpath -- "$5")
fi
manifest=$script_dir/candle/flyspeck_manifest.json
bootstrap_dir=$cakeml_dir/compiler/bootstrap/compilation/x64/64
build_dir=$script_dir/candle/build
mkdir -p "$build_dir"
[[ -d $script_dir/candle && ! -L $script_dir/candle &&
   -d $build_dir && ! -L $build_dir ]] || {
  printf 'Candle build directory must be an ordinary directory: %s\n' \
    "$build_dir" >&2
  exit 1
}
exec 9<"$build_dir"
/usr/bin/flock -x 9
lock_fd_identity=$(/usr/bin/stat -Lc '%d:%i' "/proc/$$/fd/9")
lock_path_identity=$(/usr/bin/stat -Lc '%d:%i' "$build_dir")
[[ $lock_fd_identity == "$lock_path_identity" ]] || {
  printf 'Candle build directory changed while acquiring its lock\n' >&2
  exit 1
}
managed_outputs=(
  cake.S cake.S.bootstrap cake config_enc_str.txt candle_boot.ml basis_ffi.c
  Makefile types.txt insulate.ml bootstrap-preflight.json
  bootstrap-provenance.json bootstrap.log
  cakeml-build-provenance.json
)
for output in "${managed_outputs[@]}"; do
  [[ ! -L $build_dir/$output ]] || {
    printf 'refusing symlink build output: %s\n' "$build_dir/$output" >&2
    exit 1
  }
done

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

if $transition_mode; then
  final_candle_head=$(/usr/bin/git -C "$script_dir" rev-parse HEAD)
  /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
    /usr/bin/python3 -I -S \
      "$script_dir/candle/cakeml_bootstrap_transition.py" \
    check-transition \
    --source-candle-root "$source_candle_dir" \
    --source-candle-head "$source_candle_head" \
    --final-candle-root "$script_dir" \
    --final-candle-head "$final_candle_head" \
    --cakeml-root "$cakeml_dir" \
    --bootstrap-record "$bootstrap_record" \
    --record "$transition_record"
else
  /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
    /usr/bin/python3 -I -S "$script_dir/candle/cakeml_artifact_provenance.py" \
    check-bootstrap \
    --candle-root "$script_dir" \
    --cakeml-root "$cakeml_dir" \
    --record "$bootstrap_record"
fi

required=(cake.S config_enc_str.txt candle_boot.ml basis_ffi.c Makefile)
for input in "${required[@]}"; do
  [[ -r $bootstrap_dir/$input ]] || {
    printf 'missing bootstrapped CakeML input: %s\n' \
      "$bootstrap_dir/$input" >&2
    exit 1
  }
done

for input in "${required[@]}"; do
  cp -L -- "$bootstrap_dir/$input" "$build_dir/$input"
done
cp -- "$build_dir/cake.S" "$build_dir/cake.S.bootstrap"

(
  cd "$build_dir"
  /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
    /usr/bin/patch --batch --forward cake.S ../cake.S.patch
  /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
    /usr/bin/make --no-builtin-rules --no-builtin-variables \
      -B -j1 -f Makefile \
      OS=Linux CC=/usr/bin/cc CFLAGS=-O2 LOADLIBES= EVALFLAG=-DEVAL \
      LDFLAGS= LDLIBS=-lm cake
  /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
    ./cake --types </dev/null >types.txt 2>&1
  /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
    /usr/bin/python3 -I ../insulate.py types.txt insulate.ml
)

if $transition_mode; then
  /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
    /usr/bin/python3 -I -S \
      "$script_dir/candle/cakeml_bootstrap_transition.py" \
    record-linked-transition \
    --source-candle-root "$source_candle_dir" \
    --source-candle-head "$source_candle_head" \
    --final-candle-root "$script_dir" \
    --final-candle-head "$final_candle_head" \
    --cakeml-root "$cakeml_dir" \
    --bootstrap-record "$bootstrap_record" \
    --transition-record "$transition_record" \
    --write "$build_dir/cakeml-build-provenance.json"
else
  /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
    /usr/bin/python3 -I -S "$script_dir/candle/cakeml_artifact_provenance.py" \
    record-linked \
    --candle-root "$script_dir" \
    --cakeml-root "$cakeml_dir" \
    --bootstrap-record "$bootstrap_record" \
    --write "$build_dir/cakeml-build-provenance.json"
fi

ln -sfn candle/build/config_enc_str.txt "$script_dir/config_enc_str.txt"
ln -sfn candle/build/candle_boot.ml "$script_dir/candle_boot.ml"

# Exercise the same complete provenance and root-alias preflight used by every
# interactive session.  A linked record is not a successful installation until
# this post-alias check passes.
/usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
  /usr/bin/python3 -I -S "$script_dir/candle/cakeml_artifact_provenance.py" \
  check-linked --candle-root "$script_dir"

printf 'CakeML head: %s\n' "$actual_head"
/usr/bin/sha256sum \
  "$build_dir/cake.S" \
  "$build_dir/cake" \
  "$build_dir/config_enc_str.txt" \
  "$build_dir/candle_boot.ml" \
  "$build_dir/types.txt" \
  "$build_dir/insulate.ml" \
  "$build_dir/cakeml-build-provenance.json"
