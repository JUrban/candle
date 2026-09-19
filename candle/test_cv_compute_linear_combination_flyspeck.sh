#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
binary=${CANDLE_BINARY:-/project/flyspeck-candle-runs/nonpromotable-dev-link-cc36ecadd-1109fdf-attempt-001/cake}
runtime_cwd=${CANDLE_RUNTIME_CWD:-/project/flyspeck-candle-runs/nonpromotable-dev-link-cc36ecadd-1109fdf-attempt-001}
flyspeck_root=${FLYSPECK_ROOT:-/project/worktrees/flyspeck-v13-source}
overlay_root=${FLYSPECK_OVERLAY_ROOT:-/project/flyspeck-candle-runs/v260-focused-action292-through295-pre296-v66-001/overlay}
hol_root=${CANDLE_HOL_ROOT:-/project/worktrees/candle-action165-invf-v61}
log_file=$(mktemp)
trap 'rm -f "$log_file"' EXIT

set +e
(
  cd "$runtime_cwd"
  timeout 1800 "$binary" --candle >"$log_file" 2>&1 <<EOF
Cakeml.loadPath := ["$repo_root"; "$hol_root"; "$overlay_root/text_formalization"; "$overlay_root/formal_lp"; "$overlay_root"; "$flyspeck_root/text_formalization"; "$flyspeck_root/formal_lp"; "$flyspeck_root"; Filename.currentDir];;
#use "hol.ml";;
let flyspeck_dir = "$overlay_root/text_formalization";;
load_path := "$flyspeck_root/formal_ineqs" :: !load_path;;
#use "$flyspeck_root/formal_lp/more_arith/lin_f.hl";;
#use "$flyspeck_root/formal_lp/hypermap/arith_link.hl";;
load_path := "$overlay_root/formal_ineqs" :: !load_path;;
#use "$flyspeck_root/formal_lp/more_arith/arith_int.hl";;
#use "$repo_root/candle/test_cv_compute_linear_combination_flyspeck.ml";;
EOF
)
runtime_status=$?
set -e

if (( runtime_status != 0 )); then
  rg -n 'ERROR:|EXCEPTION:|LEXER ERROR|No such file' "$log_file" >&2 || true
  tail -30 "$log_file" >&2
  exit "$runtime_status"
fi

if ! rg -Fq 'CANDLE_CV_LINEAR_COMBINATION_FLYSPECK_OK' "$log_file"; then
  rg -n 'ERROR:|EXCEPTION:|LEXER ERROR|No such file' "$log_file" >&2 || true
  tail -30 "$log_file" >&2
  exit 1
fi
if rg -q 'Error|Exception|Failure' "$log_file"; then
  tail -100 "$log_file" >&2
  exit 1
fi

printf '%s\n' 'CANDLE_CV_LINEAR_COMBINATION_FLYSPECK_OK'
