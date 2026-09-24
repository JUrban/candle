#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
flyspeck_dir=${CANDLE_ACTION296_FLYSPECK_DIR:-/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6}
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-nonlinear-reflected-driver-checkpoint-v2}
output_dir=${1:-/project/flyspeck-candle-runs/cv-polynomial-expression-action296-source-inventory-v1-run-001}

python3 "$repo_dir/candle/flyspeck_nonlinear_action296_leaf_target.py" \
  --flyspeck-root "$flyspeck_dir" --check
python3 - \
  "$repo_dir/candle/test_cv_compute_polynomial_expr_action296_source_inventory.ml" \
  "$repo_dir/candle/flyspeck_nonlinear_action296_leaf_target.json" <<'PY'
import json
import re
import sys
from pathlib import Path

source = Path(sys.argv[1]).read_text(encoding="utf-8")
target = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
match = re.search(
    r"let candle_action296_inventory_target =\s*`(?P<term>.*?)`;;",
    source,
    flags=re.DOTALL,
)
if match is None:
    raise SystemExit("action-296 inventory target quotation is absent")
normalize = lambda text: re.sub(r"\s+", "", text)
if normalize(match.group("term")) != normalize(
    target["target"]["legacy_ineqm_text"]
):
    raise SystemExit("action-296 inventory target differs from authority")
PY

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$repo_dir/candle/restart_real_functions_with_fragments.sh" \
  "$output_dir" CANDLE_CV_ACTION296_SOURCE_INVENTORY_OK \
  "$repo_dir/candle/cv_compute_polynomial_expr_dim_jet_prove.ml" \
  "$repo_dir/candle/cv_compute_flyspeck_nonlinear_driver.ml" \
  "$repo_dir/candle/test_cv_compute_polynomial_expr_action296_source_inventory.ml"

printf 'CANDLE_CV_ACTION296_SOURCE_INVENTORY_WRAPPER_OK output=%s\n' \
  "$output_dir"
