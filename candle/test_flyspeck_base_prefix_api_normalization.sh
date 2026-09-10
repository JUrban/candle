#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle/build/cake"}
candle_runtime_cwd=${CANDLE_RUNTIME_CWD:-"$candle_root"}
flyspeck_root=${FLYSPECK_ROOT:-${1:-}}
if [[ -z "$flyspeck_root" || ! -d "$flyspeck_root" ]]; then
  echo "usage: FLYSPECK_ROOT=/exact/source/root $0" >&2
  exit 1
fi
flyspeck_root=$(realpath -- "$flyspeck_root")
fixture_root="$candle_root/candle/compatibility/fixtures"
test_dir=$(mktemp -d /tmp/candle-flyspeck-base-prefix-api.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT
overlay="$test_dir/overlay"
cd "$candle_root"

python3 candle/flyspeck_normalize.py \
  --flyspeck-root "$flyspeck_root" --write "$overlay" \
  >"$test_dir/normalization.log"

strictbuild="$overlay/text_formalization/build/strictbuild.hl"
lib="$overlay/text_formalization/general/lib.hl"
flyspeck_lib="$overlay/text_formalization/general/flyspeck_lib.hl"
sphere="$overlay/text_formalization/general/sphere.hl"
hales="$overlay/text_formalization/general/hales_tactic.hl"
truong="$overlay/text_formalization/general/truong_tactic.hl"

rg -Fq 'dynamic strictbuild build_and_report is disabled by the static manifest' \
  "$strictbuild"
if rg -Fq 'open_out_gen' "$strictbuild"; then
  echo 'normalized strictbuild retained unsupported open_out_gen' >&2
  exit 1
fi
[[ $(rg -Fc 'let rev l =' "$lib") -eq 1 ]]
if rg -Fq 'let rev =' "$lib"; then
  echo 'normalized lib retained value-restricted rev binding' >&2
  exit 1
fi
for binding in length mapf foldl foldr applyd; do
  if rg -Fq "let $binding =" "$lib"; then
    echo "normalized lib retained value-restricted $binding binding" >&2
    exit 1
  fi
done
if rg -Fq 'let undefine =' "$lib"; then
  echo 'normalized lib retained value-restricted undefine binding' >&2
  exit 1
fi
if rg -Fq 'let (|->),combine =' "$lib"; then
  echo 'normalized lib retained value-restricted update/combine pair' >&2
  exit 1
fi
rg -Fq 'let undefine x t =' "$lib"
rg -Fq 'let (|->) x y t =' "$lib"
rg -Fq 'let combine op z t1 t2 =' "$lib"
[[ $(rg -Fc 'output_string outs a' "$flyspeck_lib") -eq 1 ]]
[[ $(rg -Fc 'needs "general/flyspeck_eval_4.14.hl";;' "$flyspeck_lib") -eq 1 ]]
if rg -Fq 'needs (String.concat "/"' "$flyspeck_lib"; then
  echo 'normalized flyspeck_lib retained dynamic needs expression' >&2
  exit 1
fi
if rg -Fq 'Printf.fprintf outs "%s" a' "$flyspeck_lib"; then
  echo 'normalized flyspeck_lib retained unavailable Printf.fprintf' >&2
  exit 1
fi
[[ $(rg -Fc 'sort Term.(<) (frees bod)' "$sphere") -eq 1 ]]
if rg -Fq 'sort (<) (frees bod)' "$sphere"; then
  echo 'normalized sphere retained implicit term comparison' >&2
  exit 1
fi
[[ $(rg -Fc 'List.concat' "$hales") -eq 2 ]]
[[ $(rg -Fc 'List.concat' "$truong") -eq 2 ]]
if rg -Fq 'List.flatten' "$hales" "$truong"; then
  echo 'normalized tactic source retained unavailable List.flatten' >&2
  exit 1
fi

if ! command -v ocaml >/dev/null; then
  echo 'OCaml is required for the update/combine structural oracle' >&2
  exit 1
fi
original_pair_oracle=$(
  {
    sed -n '518,521p' "$flyspeck_root/text_formalization/general/lib.hl"
    sed -n '657,746p' "$flyspeck_root/text_formalization/general/lib.hl"
    sed -n '1,200p' "$fixture_root/lib_pair_split_oracle_driver.ml"
  } | ocaml -noinit -noprompt 2>&1 | rg '^PAIR_SPLIT_ORACLE '
)
normalized_pair_oracle=$(
  {
    sed -n '518,521p' "$flyspeck_root/text_formalization/general/lib.hl"
    sed -n '1,300p' "$fixture_root/lib_pair_split_replacement.ml"
    sed -n '1,200p' "$fixture_root/lib_pair_split_oracle_driver.ml"
  } | ocaml -noinit -noprompt 2>&1 | rg '^PAIR_SPLIT_ORACLE '
)
if [[ "$original_pair_oracle" != "$normalized_pair_oracle" ]]; then
  echo 'original/split update/combine structural oracles differ' >&2
  exit 1
fi

(
  cd "$candle_runtime_cwd"
  printf '#use "hol.ml";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n#use "%s";;\n' \
      "$fixture_root/base_prefix_api_original_sphere.ml" \
      "$fixture_root/base_prefix_api_original_flatten.ml" \
      "$fixture_root/base_prefix_api_original_printf.ml" \
      "$fixture_root/base_prefix_api_original_rev.ml" \
      "$fixture_root/base_prefix_api_normalized.ml" \
      "$lib" |
    timeout 300 "$candle_binary" --candle \
      >"$test_dir/candle.log" 2>&1
)

rg -Fq 'Type mismatch between int list -> int list and term list' \
  "$test_dir/candle.log"
rg -Fq 'Undefined variable: List.flatten' "$test_dir/candle.log"
rg -Fq 'Undefined variable: Printf.fprintf' "$test_dir/candle.log"
rg -Fq 'Value restriction violated' "$test_dir/candle.log"
rg -Fq 'val candle_flyspeck_normalized_all_forall = <fun>: term -> term' \
  "$test_dir/candle.log"
rg -Fq 'val candle_flyspeck_normalized_flatten_frees = <fun>: term list -> term list' \
  "$test_dir/candle.log"
rg -Fq 'val candle_flyspeck_normalized_output_filestring = <fun>: string -> string -> unit' \
  "$test_dir/candle.log"
rg -Fq 'val candle_flyspeck_build_and_report_fail_closed = true: bool' \
  "$test_dir/candle.log"
rg -Fq 'val candle_flyspeck_base_prefix_api_oracle_ok = true: bool' \
  "$test_dir/candle.log"
rg -Fq -- "- Finished loading $lib" "$test_dir/candle.log"
if [[ $(rg -c '^ERROR:' "$test_dir/candle.log") -ne 4 ]]; then
  tail -n 80 "$test_dir/candle.log" >&2
  exit 1
fi

printf 'PASS: exact Flyspeck base-prefix API normalizations\n'
