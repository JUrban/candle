#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
fixture="$candle_root/candle/compatibility/fixtures/serialization_string_order_ocaml_oracle.ml"
test_dir=$(mktemp -d /tmp/candle-serialization-string-order.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

ocaml "$fixture" >"$test_dir/oracle.log" 2>&1
rg -Fq 'CANDLE_SERIALIZATION_STRING_ORDER_OCAML_OK' "$test_dir/oracle.log"

printf '%s\n' 'PASS: native Serialization string-order equivalence oracle'
