#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
output_dir=${1:-/project/flyspeck-candle-runs/cv-nonlinear-real-leaf-batch-capture-v1-run-001}
checkpoint_dir=/project/flyspeck-candle-runs/cv-nonlinear-real-functions-checkpoint-v1

exec "$checkpoint_dir/restart-with-continuation.sh" \
  "$output_dir" \
  "$repo_dir/candle/capture_flyspeck_nonlinear_leaf_batch_finish.ml" \
  CANDLE_NL_REAL_LEAF_BATCH_CAPTURE_OK
