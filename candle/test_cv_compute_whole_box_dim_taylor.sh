#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
output_dir=${1:-/project/flyspeck-candle-runs/cv-whole-box-dim-taylor-v1-run-001}
base_dir=/project/flyspeck-candle-runs/cv-polynomial-calculus-predecessor-checkpoint-v2

exec "$base_dir/restart-with-driver.sh" \
  "$output_dir" \
  "$repo_dir/candle/test_cv_compute_whole_box_dim_taylor.ml" \
  CANDLE_CV_WHOLE_BOX_DIM_TAYLOR_OK
