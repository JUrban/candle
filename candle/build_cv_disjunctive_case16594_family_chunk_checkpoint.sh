#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  printf 'usage: %s BASE_DIR RUN_DIR\n' "$0" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
base_dir=$1
run_dir=$2
ready_marker=CANDLE_CV_DISJUNCTIVE_CASE16594_FAMILY_CHUNK_CHECKPOINT_READY

exec "$repo_root/candle/build_cv_fragment_checkpoint.sh" \
  "$base_dir" "$run_dir" "$ready_marker" \
  "$repo_root/candle/cv_compute_analytic_expr_disjunctive_case16594_family_next.ml"
