#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
flyspeck_dir=${CANDLE_DISJUNCTIVE_FLYSPECK_DIR:-/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6}
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-action296-box-plan-support-checkpoint-v1-schedule-copy-001}
output_dir=${1:-/project/flyspeck-candle-runs/cv-disjunctive-plan-v1-dev-001}
target="$repo_root/candle/flyspeck_nonlinear_disjunctive_target.json"
fixture="$repo_root/candle/cv_compute_analytic_expr_disjunctive_fixture.ml"
started_epoch=$(date +%s)

python3 "$repo_root/candle/flyspeck_nonlinear_disjunctive_target.py" \
  --flyspeck-root "$flyspeck_dir" --check
python3 - "$fixture" "$target" <<'PY'
import json
import re
import sys
from pathlib import Path

source = Path(sys.argv[1]).read_text(encoding="utf-8")
target = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
match = re.search(
    r"let candle_disjunctive_analytic_target =\s*`(?P<term>.*?)`;;",
    source,
    flags=re.DOTALL,
)
if match is None:
    raise SystemExit("disjunctive fixture target quotation is absent")
normalize = lambda text: re.sub(r"\s+", "", text)
if normalize(match.group("term")) != normalize(
    target["target"]["legacy_ineqm_text"]
):
    raise SystemExit("disjunctive fixture differs from target authority")
PY

CANDLE_FRAGMENT_BASE_DIR="$base_dir" CANDLE_FRAGMENT_SKIP_ALL_NEEDS=1 \
  "$repo_root/candle/restart_real_functions_with_fragments.sh" \
  "$output_dir" CANDLE_CV_DISJUNCTIVE_PLAN_OK \
  "$repo_root/candle/cv_compute_analytic_expr_reify.ml" \
  "$repo_root/candle/cv_compute_analytic_expr_jet_prove.ml" \
  "$fixture" \
  "$repo_root/candle/cv_compute_analytic_expr_disjunctive_plan.ml"

printf 'CANDLE_CV_DISJUNCTIVE_PLAN_WRAPPER_OK output=%s wall_seconds=%s\n' \
  "$output_dir" "$(( $(date +%s) - started_epoch ))"
