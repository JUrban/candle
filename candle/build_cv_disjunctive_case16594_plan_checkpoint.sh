#!/usr/bin/env bash
set -euo pipefail

if [[ $# -gt 1 ]]; then
  printf 'usage: %s [RUN_DIR]\n' "$0" >&2
  exit 2
fi

repo_root=$(cd "$(dirname "$0")/.." && pwd)
flyspeck_root=${CANDLE_DISJUNCTIVE_FLYSPECK_DIR:-/project/worktrees/flyspeck-cv-nonlinear-closure-v11-manifest-d6}
base_dir=${CANDLE_FRAGMENT_BASE_DIR:-/project/flyspeck-candle-runs/cv-disjunctive-complete-range-v3-dev-001}
run_dir=${1:-/project/flyspeck-candle-runs/cv-disjunctive-case16594-plan-checkpoint-v1-dev-001}
target="$repo_root/candle/flyspeck_nonlinear_disjunctive_case16594_target.json"
fixture="$repo_root/candle/cv_compute_analytic_expr_disjunctive_case16594_fixture.ml"
plan="$repo_root/candle/cv_compute_analytic_expr_disjunctive_case16594_plan.ml"
ready_marker=CANDLE_CV_DISJUNCTIVE_CASE16594_PLAN_CHECKPOINT_READY

python3 "$repo_root/candle/flyspeck_nonlinear_disjunctive_target.py" \
  --flyspeck-root "$flyspeck_root" --global-case 16594 \
  --output candle/flyspeck_nonlinear_disjunctive_case16594_target.json \
  --check

python3 - "$fixture" "$target" <<'PY'
import json
import re
import sys
from pathlib import Path

source = Path(sys.argv[1]).read_text(encoding="utf-8")
target = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
match = re.search(
    r"let candle_disjunctive_case16594_target =\s*`(?P<term>.*?)`;;",
    source,
    flags=re.DOTALL,
)
if match is None:
    raise SystemExit("case16594 fixture target quotation is absent")
normalize = lambda text: re.sub(r"\s+", "", text)
if normalize(match.group("term")) != normalize(
    target["target"]["legacy_ineqm_text"]
):
    raise SystemExit("case16594 fixture differs from target authority")
PY

exec "$repo_root/candle/build_cv_fragment_checkpoint.sh" \
  "$base_dir" "$run_dir" "$ready_marker" "$fixture" "$plan"
