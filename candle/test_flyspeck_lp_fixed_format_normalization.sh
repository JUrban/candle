#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
flyspeck_root=${FLYSPECK_ROOT:-/project/worktrees/flyspeck-v13-source}
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
fixture_root="$candle_root/candle/compatibility/fixtures"
test_dir=$(mktemp -d /tmp/candle-flyspeck-lp-fixed-format.XXXXXX)
cleanup() {
  chmod -R u+w "$test_dir" 2>/dev/null || true
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

python3 "$candle_root/candle/flyspeck_normalize.py" \
  --flyspeck-root "$flyspeck_root" --write "$test_dir/overlay"

declare -A expected_sha256=(
  [formal_lp/glpk/lpproc.ml]=e520d885811bf32bcfeeff876ec182163505df7703393de59d3b7c7878354166
  [text_formalization/tame/good_list_archive.hl]=5b6de7d78ec8a8aef2fc86976e5d61c6f21097a37b41cd48101b86b554a46f8d
  [formal_lp/hypermap/ineqs/lp_ineqs.hl]=5a10de553316284be1a5e179e6d539bb925e96ca34e0a3b147bba8657472ac12
  [formal_lp/hypermap/ineqs/lp_body_ineqs.hl]=34371472bd4910bfa1bc4af9cf73b07eb420eb94b7028d35464ba953debd7aaf
  [formal_lp/hypermap/main/prove_flyspeck_lp.hl]=f640fc6dc381f67887c84eca68ab3de2a0f138369f1b40a62de588120ae5193e
  [formal_lp/hypermap/verify_all.hl]=49e01e67d0ae506d261ac82f77a0f5359e8875331042617100632bb1d4317bed
  [text_formalization/tame/linear_programming_results.hl]=a2d009759d2fa9bd555922cca3f78cf98366e912311cdb7a778487aafa2086ec
)

for relative in "${!expected_sha256[@]}"; do
  normalized="$test_dir/overlay/$relative"
  test -f "$normalized"
  test "$(sha256sum -- "$normalized" | cut -d' ' -f1)" = \
    "${expected_sha256[$relative]}"
done

lpproc="$test_dir/overlay/formal_lp/glpk/lpproc.ml"
good_list="$test_dir/overlay/text_formalization/tame/good_list_archive.hl"
lp_ineqs="$test_dir/overlay/formal_lp/hypermap/ineqs/lp_ineqs.hl"
lp_body="$test_dir/overlay/formal_lp/hypermap/ineqs/lp_body_ineqs.hl"
prove_lp="$test_dir/overlay/formal_lp/hypermap/main/prove_flyspeck_lp.hl"
verify_all="$test_dir/overlay/formal_lp/hypermap/verify_all.hl"
results="$test_dir/overlay/text_formalization/tame/linear_programming_results.hl"

rg -Fq 'output_string outs j' "$lpproc"
rg -Fxq 'needs "../formal_lp/glpk/glpk_link.ml";;' "$lpproc"
rg -Fxq 'needs "../formal_graph/archive/archive_all.ml";;' "$lpproc"
if rg -Fq 'needs (Filename.concat' "$lpproc"; then
  echo 'normalized lpproc retained computed needs expression' >&2
  exit 1
fi
test "$(realpath -- "$flyspeck_root/text_formalization/../formal_lp/glpk/glpk_link.ml")" = \
  "$(realpath -- "$flyspeck_root/formal_lp/glpk/glpk_link.ml")"
test "$(realpath -- "$flyspeck_root/text_formalization/../formal_graph/archive/archive_all.ml")" = \
  "$(realpath -- "$flyspeck_root/formal_graph/archive/archive_all.ml")"
if rg -Fq 'Printf.fprintf outs "%s" j' "$lpproc"; then
  echo 'normalized lpproc retained unavailable Printf.fprintf' >&2
  exit 1
fi
for normalized in "$good_list" "$lp_ineqs" "$lp_body" "$verify_all" "$results"; do
  if rg -q 'Printf\.|Format\.sprintf|\bsprintf\b' "$normalized"; then
    echo "normalized LP source retained fixed-format call: $normalized" >&2
    exit 1
  fi
done
test "$(rg -c '\bsprintf\b' "$prove_lp")" -eq 1
rg -Fq 'Candle S3: total verification time is recorded by the outer runner' \
  "$results"

ocaml -noinit -noprompt <"$fixture_root/lp_fixed_format_ocaml_oracle.ml" \
  >"$test_dir/ocaml.log" 2>&1
rg -Fq 'LP_FIXED_FORMAT_OCAML_ORACLE_OK' "$test_dir/ocaml.log"

(
  cd "$candle_runtime_cwd"
  timeout 300 "$candle_binary" --candle \
    <"$fixture_root/lp_fixed_format_normalized.ml" \
    >"$test_dir/candle.log" 2>&1
)
rg -Fq 'val candle_lp_fixed_format_normalized_ok = true: bool' \
  "$test_dir/candle.log"
if rg -q 'Parsing failed|^ERROR:|^EXCEPTION:' "$test_dir/candle.log"; then
  tail -n 100 "$test_dir/candle.log" >&2
  exit 1
fi

printf 'PASS: LP fixed-format compatibility normalizations\n'
