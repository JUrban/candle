#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 4 ]]; then
  printf 'usage: %s /path/to/candle.sh /path/to/flyspeck /path/to/overlay /path/to/generated-inputs\n' "$0" >&2
  exit 2
fi

loader_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
candle_script=$(realpath -- "$1")
flyspeck_root=$(realpath -- "$2")
overlay_root=$(realpath -- "$3")
generated_root=$(realpath -- "$4")
candle_root=$(cd -- "$(dirname -- "$candle_script")" && pwd)
[[ -x $candle_script ]] || {
  printf 'Candle launcher is not executable: %s\n' "$candle_script" >&2
  exit 2
}
python3 "$loader_dir/cakeml_artifact_provenance.py" \
  check-linked --candle-root "$candle_root"

work=$(mktemp -d /tmp/candle-flyspeck-dopen-prefix.XXXXXX)
log=$work/candle.log
prepared=$work/prepared
preserved_log=${CANDLE_FLYSPECK_DOPEN_LOG:-}
cleanup() {
  result=$?
  if [[ $result -ne 0 && -f $log ]]; then
    tail -n 100 "$log" >&2
  fi
  if [[ -n $preserved_log && -f $log ]]; then
    cp -- "$log" "$preserved_log"
  fi
  find "$work" -depth -type f -delete 2>/dev/null || true
  find "$work" -depth -type d -empty -delete 2>/dev/null || true
}
trap cleanup EXIT

python3 "$loader_dir/flyspeck_dopen_prefix.py" \
  --candle-root "$candle_root" \
  --flyspeck-root "$flyspeck_root" \
  --overlay-root "$overlay_root" \
  --generated-root "$generated_root" \
  --write "$prepared"

(
  cd -- "$candle_root"
  timeout 300 "$candle_script" >"$log" 2>&1 <<EOF
#use "$prepared/dopen-prefix-config.ml";;
#use "$loader_dir/flyspeck_dopen_prefix_setup.ml";;
#use "$prepared/strictbuild-dopen-prefix.hl";;
#use "$loader_dir/flyspeck_dopen_prefix_check.ml";;
EOF
)

python3 - "$log" "$flyspeck_root" "$overlay_root" <<'PY'
import sys
from pathlib import Path

log = Path(sys.argv[1]).read_text(encoding="utf-8", errors="replace")
source = sys.argv[2]
overlay = sys.argv[3]
markers = [
    "CANDLE_FLYSPECK_DOPEN_PREFIX_PREFLIGHT_OK",
    f"- Selecting normalized source {source}/text_formalization/general/parser_verbose.hl -> {overlay}/text_formalization/general/parser_verbose.hl",
    f"- Loading {overlay}/text_formalization/general/parser_verbose.hl",
    "- Flyspeck source action complete: general/parser_verbose.hl",
    f"- Selecting normalized source {source}/text_formalization/general/debug.hl -> {overlay}/text_formalization/general/debug.hl",
    f"- Loading {overlay}/text_formalization/general/debug.hl",
    "- Flyspeck source action complete: general/debug.hl",
    "CANDLE_FLYSPECK_DOPEN_PREFIX_OK",
]
positions = []
for marker in markers:
    if log.count(marker) != 1:
        raise SystemExit(f"expected exactly one log marker: {marker}")
    positions.append(log.index(marker))
if positions != sorted(positions):
    raise SystemExit("Dopen prefix marker order mismatch")
PY

if rg -q 'open-declarations are not supported|Parsing failed|^ERROR:|^EXCEPTION:|Static #flyspeck_(loadt|needs) rejected|CANDLE_FLYSPECK_DIRECT_FULL_OK' "$log"; then
  tail -n 100 "$log" >&2
  exit 1
fi

printf 'Dopen direct-source prefix PASS\n'
