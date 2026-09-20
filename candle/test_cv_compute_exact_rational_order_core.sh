#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
binary=${CANDLE_BINARY:-/project/flyspeck-candle-runs/nonpromotable-dev-link-cc36ecadd-1109fdf-attempt-001/cake}
runtime_cwd=${CANDLE_RUNTIME_CWD:-/project/flyspeck-candle-runs/nonpromotable-dev-link-cc36ecadd-1109fdf-attempt-001}
log_file=$(mktemp)
trap 'rm -f "$log_file"' EXIT

(
  cd "$runtime_cwd"
  timeout 1800 "$binary" --candle >"$log_file" 2>&1 <<EOF
Cakeml.loadPath := ["$repo_root"; "/project/worktrees/candle-action165-invf-v61"; Filename.currentDir];;
#use "hol.ml";;
#use "$repo_root/candle/test_cv_compute_exact_rational_order_core.ml";;
EOF
)

if ! rg -Fq 'CANDLE_CV_EXACT_RATIONAL_ORDER_CORE_OK' "$log_file"; then
  tail -220 "$log_file" >&2
  exit 1
fi
if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$log_file"; then
  tail -140 "$log_file" >&2
  exit 1
fi

printf '%s\n' 'CANDLE_CV_EXACT_RATIONAL_ORDER_CORE_OK'
