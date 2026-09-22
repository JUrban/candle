#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
binary=${CANDLE_BINARY:-/project/flyspeck-candle-runs/nonpromotable-dev-link-cc36ecadd-1109fdf-attempt-001/cake}
runtime_cwd=${CANDLE_RUNTIME_CWD:-/project/flyspeck-candle-runs/nonpromotable-dev-link-cc36ecadd-1109fdf-attempt-001}
log_file=$(mktemp)
trap 'rm -f "$log_file"' EXIT

set +e
(
  cd "$runtime_cwd"
  timeout 1800 "$binary" --candle >"$log_file" 2>&1 <<EOF
Cakeml.loadPath := ["$repo_root"; "/project/worktrees/candle-action165-invf-v61"; Filename.currentDir];;
#use "hol.ml";;
#use "$repo_root/candle/test_cv_compute_linear_combination_sparse_verdict.ml";;
EOF
)
runtime_status=$?
set -e

if (( runtime_status != 0 )); then
  rg -n 'ERROR:|EXCEPTION:|LEXER ERROR|No such file' "$log_file" >&2 || true
  tail -120 "$log_file" >&2
  exit "$runtime_status"
fi
if ! rg -Fq 'CANDLE_CV_LINEAR_COMBINATION_SPARSE_VERDICT_OK' "$log_file"; then
  rg -n 'ERROR:|EXCEPTION:|LEXER ERROR|No such file' "$log_file" >&2 || true
  tail -160 "$log_file" >&2
  exit 1
fi
if rg -q 'Error|Exception|Failure' "$log_file"; then
  tail -120 "$log_file" >&2
  exit 1
fi

printf '%s\n' 'CANDLE_CV_LINEAR_COMBINATION_SPARSE_VERDICT_OK'
