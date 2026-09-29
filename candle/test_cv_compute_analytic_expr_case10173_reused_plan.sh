#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd "$(dirname "$0")/.." && pwd)
flyspeck_dir=${CANDLE_CASE10173_FLYSPECK_DIR:-/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6}
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-action296-box-plan-support-checkpoint-v1-schedule-copy-001}
output_dir=${1:-/project/flyspeck-candle-runs/cv-case10173-reused-plan-v1-dev-001}
fixture="$repo_dir/candle/cv_compute_analytic_expr_case10173_fixture.ml"
plan="$repo_dir/candle/cv_compute_analytic_expr_case10173_reused_plan.ml"
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

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$repo_dir/candle/restart_real_functions_with_fragments.sh" \
  "$output_dir" CANDLE_CV_CASE10173_REUSED_PLAN_OK \
  "$fixture" "$plan"

printf 'CANDLE_CV_CASE10173_REUSED_PLAN_WRAPPER_OK output=%s\n' \
  "$output_dir"
