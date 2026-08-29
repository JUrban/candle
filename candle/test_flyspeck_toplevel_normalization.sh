#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
: "${FLYSPECK_ROOT:?set FLYSPECK_ROOT to the pinned Flyspeck checkout}"
temporary=$(mktemp -d /tmp/candle-flyspeck-toplevel.XXXXXX)
cleanup() {
  find "$temporary" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

python3 "$candle_root/candle/flyspeck_normalize.py" \
  --flyspeck-root "$FLYSPECK_ROOT" --write "$temporary/overlay"
python3 "$candle_root/candle/check_flyspeck_normalized_toplevel.py" \
  --flyspeck-root "$FLYSPECK_ROOT"

printf 'PASS: exact selected toplevel non-use normalizations\n'
