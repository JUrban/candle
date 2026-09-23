#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
candle_bootstrap_root=${CANDLE_BOOTSTRAP_ROOT:-"$candle_root"}
fixtures="$candle_root/candle/compatibility/fixtures"
test_dir=$(mktemp -d /tmp/candle-certificate-float-subdomain.XXXXXX)
cleanup() {
  local status=$?
  trap - EXIT
  if [[ $status != 0 ]]; then
    for log in "$test_dir"/*.log; do
      [[ -f $log ]] || continue
      printf '%s\n' "--- ${log##*/}" >&2
      tail -n 100 "$log" >&2 || true
    done
  fi
  find "$test_dir" -depth -delete 2>/dev/null || true
  exit "$status"
}
trap cleanup EXIT

(
  cd "$candle_runtime_cwd"
  printf 'Cakeml.loadPath := ["%s"; "%s"; Filename.currentDir];;\n#use "hol.ml";;\nlet float_ieee_le left right = Cake.Double.(<=) left right;;\n#use "%s";;\n#use "%s";;\n' \
    "$candle_bootstrap_root" "$candle_root" \
    "$fixtures/certificate_float_subdomain_raw.ml" \
    "$fixtures/certificate_float_subdomain_normalized.ml" |
    timeout 300 "$candle_binary" --candle
) >"$test_dir/candle.log" 2>&1

rg -Fq 'Type mismatch between int list -> int list -> bool and Double.double list ->' \
  "$test_dir/candle.log"
test "$(rg -c '^ERROR:' "$test_dir/candle.log")" -eq 1
rg -Fq 'val candle_certificate_float_subdomain_ok = true: bool' \
  "$test_dir/candle.log"
rg -Fq 'CANDLE_CERTIFICATE_FLOAT_SUBDOMAIN_OK' "$test_dir/candle.log"
if rg -q 'EXCEPTION:|Parsing failed|Undefined variable:' "$test_dir/candle.log"; then
  exit 1
fi

printf 'PASS: explicit certificate float order preserves subdomain checks\n'
