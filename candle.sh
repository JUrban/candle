#!/bin/bash -p
# Set up "strict mode" for bash
set -euo pipefail
export PATH=/usr/bin:/bin

# Promotable runtime provenance models a fixed dynamic-loader environment.
# Refuse ambient loader injection rather than silently blessing it into a run.
for variable in ${!LD_@} GLIBC_TUNABLES BASH_ENV ENV; do
  if [[ -v $variable ]]; then
    printf 'forbidden dynamic-loader environment: %s\n' "$variable" >&2
    exit 1
  fi
done
export LC_ALL=C

# The CakeML bootstrap reads these generated files from its current directory.
# The build installs relative links at the repository root so Candle can start
# in the same authenticated source tree that it subsequently loads.  This
# avoids a boot-time custom chdir FFI and keeps relocation explicit.
script_path=$(/usr/bin/readlink -f -- "${BASH_SOURCE[0]}")
script_dir=${script_path%/*}
if [[ ! -d $script_dir/candle/build || -L $script_dir/candle/build ]]; then
  echo "Candle build directory must be an ordinary directory" >&2
  exit 1
fi
exec 9>>"$script_dir/candle/build/runtime.lock"
/usr/bin/flock -s 9
/usr/bin/python3 -I "$script_dir/candle/cakeml_artifact_provenance.py" \
  check-linked --candle-root "$script_dir"
for generated in config_enc_str.txt candle_boot.ml; do
  expected_link="candle/build/$generated"
  if [[ ! -L "$script_dir/$generated" ]]; then
    echo "mismatched generated Candle runtime alias: $script_dir/$generated" >&2
    exit 1
  fi
  observed_link=$(/usr/bin/readlink -- "$script_dir/$generated")
  observed_resolved=$(/usr/bin/readlink -f -- "$script_dir/$generated")
  if [[ $observed_link != "$expected_link" ||
        $observed_resolved != "$script_dir/$expected_link" ]]; then
    echo "mismatched generated Candle runtime alias: $script_dir/$generated" >&2
    exit 1
  fi
done
cd "$script_dir"

# Start Candle
runtime_sizes=()
for variable in CML_HEAP_SIZE CML_STACK_SIZE; do
  if [[ -v $variable ]]; then
    runtime_sizes+=("$variable=${!variable}")
  fi
done
exec /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
  "${runtime_sizes[@]}" ./candle/build/cake --candle
