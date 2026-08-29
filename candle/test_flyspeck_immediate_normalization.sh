#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd "$(dirname "$0")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle.sh"}

ocaml -noinit -noprompt \
  "$candle_root/candle/flyspeck_immediate_ocaml_oracle.ml"

timeout 45s "$candle_binary" \
  < "$candle_root/candle/flyspeck_immediate_normalized_oracle.ml" \
  | grep -F "val candle_flyspeck_immediate_normalized_oracle_ok = true"
