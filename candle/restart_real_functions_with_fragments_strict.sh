#!/usr/bin/env bash
set -euo pipefail

# The base runner watches the live log, but a final exception can race process
# exit and be followed by a marker from the remaining input.  Preserve the
# authenticated base runner byte-for-byte and add the complete-log check here.

if [[ $# -lt 3 ]]; then
  printf 'usage: %s OUTPUT_DIR EXPECTED_MARKER FRAGMENT...\n' "$0" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
output_dir=$1
runner="$repo_root/candle/restart_real_functions_with_fragments.sh"

set +e
"$runner" "$@"
runner_status=$?
set -e

if [[ -f "$output_dir/candle.log" ]] &&
   rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$output_dir/candle.log"; then
  first_error_line=$(
    rg -n -m1 'ERROR:|EXCEPTION:|Parsing failed' "$output_dir/candle.log" |
      cut -d: -f1
  )
  printf 'strict restored-input check found a source error at line %s\n' \
    "$first_error_line" >&2
  head -n "$first_error_line" "$output_dir/candle.log" | tail -300 >&2
  exit 1
fi

exit "$runner_status"
