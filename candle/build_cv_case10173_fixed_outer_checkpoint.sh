#!/usr/bin/env bash
set -euo pipefail

if [[ $# -gt 1 ]]; then
  printf 'usage: %s [RUN_DIR]\n' "$0" >&2
  exit 2
fi

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
flyspeck_dir=${CANDLE_CASE10173_FLYSPECK_DIR:-/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6}
base_dir=${CANDLE_CASE10173_FIXED_OUTER_BASE_DIR:-/project/flyspeck-candle-runs/cv-case10173-plan-support-checkpoint-v1}
run_dir=${1:-/project/flyspeck-candle-runs/cv-case10173-fixed-outer-support-checkpoint-v1}
ready_marker=CANDLE_CV_CASE10173_FIXED_OUTER_CHECKPOINT_READY
fixture="$repo_dir/candle/cv_compute_analytic_expr_case10173_fixture.ml"
target="$repo_dir/candle/flyspeck_nonlinear_case10173_target.json"

python3 "$repo_dir/candle/flyspeck_nonlinear_case10173_target.py" \
  --flyspeck-root "$flyspeck_dir" --check
python3 - "$fixture" "$target" <<'PY'
import json
import re
import sys
from pathlib import Path

source = Path(sys.argv[1]).read_text(encoding="utf-8")
target = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
match = re.search(
    r"let candle_case10173_analytic_target =\s*`(?P<term>.*?)`;;",
    source,
    flags=re.DOTALL,
)
if match is None:
    raise SystemExit("case-10173 fixture target quotation is absent")
normalize = lambda text: re.sub(r"\s+", "", text)
if normalize(match.group("term")) != normalize(
    target["target"]["legacy_ineqm_text"]
):
    raise SystemExit("case-10173 fixture differs from target authority")
PY

fragments=(
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_invariant.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_item_invariant.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_program_sound.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_compile_sound.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_compile_sound.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_algebraic_certified_sound.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_certified_sound.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_stable_batch_sound.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_taylor_model_program_fixed_outer_stable_batch_prove.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_box_certificate_prepare.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_action296_adaptive_forest_prove.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_action296_bounded_grouped_forest_prove.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_action296_stable_grouped_forest_prove.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_action296_fixed_outer_grouped_forest_prove.ml"
  "$repo_dir/candle/test_cv_compute_analytic_expr_case10173_adapter_setup.ml"
)

exec "$repo_dir/candle/build_cv_fragment_checkpoint.sh" \
  "$base_dir" "$run_dir" "$ready_marker" "${fragments[@]}"
