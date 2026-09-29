#!/usr/bin/env bash
set -euo pipefail

if [[ $# -gt 1 ]]; then
  printf 'usage: %s [RUN_DIR]\n' "$0" >&2
  exit 2
fi

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
flyspeck_dir=${CANDLE_CASE10173_FLYSPECK_DIR:-/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6}
base_dir=${CANDLE_CASE10173_PLAN_BASE_DIR:-/project/flyspeck-candle-runs/cv-action296-box-plan-support-checkpoint-v1-case10173-copy-001}
run_dir=${1:-/project/flyspeck-candle-runs/cv-case10173-plan-support-checkpoint-v1}
ready_marker=CANDLE_CV_CASE10173_PLAN_CHECKPOINT_READY
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
  "$fixture"
  "$repo_dir/candle/cv_compute_analytic_expr_case10173_reused_plan.ml"
  "$repo_dir/candle/cv_compute_analytic_expr_case10173_leaf_grouping_fixture.ml"
)

exec "$repo_dir/candle/build_cv_fragment_checkpoint.sh" \
  "$base_dir" "$run_dir" "$ready_marker" "${fragments[@]}"
