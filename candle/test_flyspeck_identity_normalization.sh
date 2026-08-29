#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd "$(dirname "$0")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle.sh"}
: "${FLYSPECK_ROOT:?set FLYSPECK_ROOT to the pinned Flyspeck checkout}"
flyspeck_root=$FLYSPECK_ROOT

python3 "$candle_root/candle/flyspeck_normalize.py" \
  --flyspeck-root "$flyspeck_root" --check
python3 "$candle_root/candle/check_flyspeck_normalized_identity.py" \
  --flyspeck-root "$flyspeck_root"

ocaml -noinit -noprompt \
  "$candle_root/candle/flyspeck_identity_ocaml_oracle.ml"

timeout 90s "$candle_binary" \
  < "$candle_root/candle/flyspeck_identity_normalized_oracle.ml" \
  | grep -F "val candle_flyspeck_identity_normalized_oracle_ok = true"
