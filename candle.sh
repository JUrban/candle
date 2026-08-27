#!/bin/bash
# Set up "strict mode" for bash
set -euo pipefail

# The CakeML bootstrap reads these generated files from its current directory.
# The build installs relative links at the repository root so Candle can start
# in the same authenticated source tree that it subsequently loads.  This
# avoids a boot-time custom chdir FFI and keeps relocation explicit.
script_dir=$(dirname -- "$(readlink -f -- "${BASH_SOURCE[0]}")")
for generated in config_enc_str.txt candle_boot.ml; do
  if [[ ! -r "$script_dir/$generated" ]]; then
    echo "missing generated Candle runtime input: $script_dir/$generated" >&2
    exit 1
  fi
done
cd "$script_dir"

# Start Candle
exec ./candle/build/cake --candle
