#!/bin/bash
# Set up "strict mode" for bash
set -euo pipefail

# Promotable runtime provenance models a fixed dynamic-loader environment.
# Refuse ambient loader injection rather than silently blessing it into a run.
for variable in ${!LD_@} GLIBC_TUNABLES; do
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
script_dir=$(dirname -- "$(readlink -f -- "${BASH_SOURCE[0]}")")
python3 "$script_dir/candle/cakeml_artifact_provenance.py" \
  check-linked --candle-root "$script_dir"
for generated in config_enc_str.txt candle_boot.ml; do
  if [[ ! -r "$script_dir/$generated" ]]; then
    echo "missing generated Candle runtime input: $script_dir/$generated" >&2
    exit 1
  fi
done
cd "$script_dir"

# Start Candle
exec ./candle/build/cake --candle
