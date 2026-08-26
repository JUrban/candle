#!/usr/bin/env bash
set -euo pipefail

repo_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
test_dir="$repo_dir/candle/pft/tests"
fixture_dir="$test_dir/fixtures"
core_fixture="$fixture_dir/core.pft.bin"
axiom_fixture="$fixture_dir/unauthorized-axiom.pft.bin"
impostor_fixture="$fixture_dir/impostor-standard-axiom.pft.bin"
preamble_fixture="$fixture_dir/preamble.pft.bin"
hol_light_bootstrap_fixture="$fixture_dir/hol-light-bootstrap.pft.bin"

if [[ ! -f "$core_fixture" || ! -f "$axiom_fixture" ||
      ! -f "$impostor_fixture" || ! -f "$preamble_fixture" ||
      ! -f "$hol_light_bootstrap_fixture" ]]; then
  printf 'missing generated fixtures under %s\n' "$fixture_dir" >&2
  exit 2
fi

tmp_dir=$(mktemp -d)
trap 'rm -rf -- "$tmp_dir"' EXIT
python3 "$test_dir/mutate_fixtures.py" "$core_fixture" "$tmp_dir/malformed"

run_replay() {
  local expected=$1
  local trace=$2
  local label=$3
  local setup=${4:-}
  local assertion=${5:-}
  local log="$tmp_dir/$label.log"
  timeout 180 "$repo_dir/candle.sh" >"$log" 2>&1 <<EOF
#use "candle/pft/replay.ml";;
$setup
let evidence = replay "$trace";;
$assertion
EOF
  if [[ "$expected" == pass ]]; then
    if ! rg -q '^Success!$' "$log" || rg -q '^EXCEPTION:' "$log"; then
      printf 'FAIL (expected success): %s\n' "$label" >&2
      tail -n 30 "$log" >&2
      return 1
    fi
  else
    if ! rg -q '^EXCEPTION:' "$log" || rg -q '^Success!$' "$log"; then
      printf 'FAIL (expected rejection): %s\n' "$label" >&2
      tail -n 30 "$log" >&2
      return 1
    fi
  fi
  printf 'PASS: %s (%s)\n' "$label" "$expected"
}

run_replay pass "$core_fixture" core '' \
  'if pft_result_command_count evidence = 18 &&
      pft_result_table_limits evidence = (3,4,3) &&
      pft_result_peak_live evidence = (3,4,3) &&
      length (pft_result_saved_theorems evidence) = 2 &&
      pft_result_axioms evidence = []
   then print_endline "Evidence OK"
   else failwith "unexpected core replay evidence";;'
run_replay reject "$axiom_fixture" unauthorized-axiom
run_replay reject "$impostor_fixture" impostor-standard-axiom \
  'allow_standard_pft_axioms ();;'
run_replay pass "$preamble_fixture" standard-preamble \
  'allow_standard_pft_axioms ();;' \
  'if pft_result_command_count evidence = 1181 &&
      pft_result_table_limits evidence = (31,329,775) &&
      pft_result_peak_live evidence = (31,329,775) &&
      length (pft_result_saved_theorems evidence) = 42 &&
      length (pft_result_axioms evidence) = 3
   then print_endline "Evidence OK"
   else failwith "unexpected preamble replay evidence";;'
run_replay pass "$hol_light_bootstrap_fixture" hol-light-bootstrap \
  'allow_standard_pft_axioms ();;' \
  'if pft_result_command_count evidence = 8817 &&
      pft_result_table_limits evidence = (1148,2735,4919) &&
      pft_result_peak_live evidence = (1148,2735,4919) &&
      length (pft_result_saved_theorems evidence) = 6 &&
      length (pft_result_axioms evidence) = 3
   then print_endline "Evidence OK"
   else failwith "unexpected HOL Light bootstrap replay evidence";;'
for trace in "$tmp_dir"/malformed/*.pft.bin; do
  label=$(basename "$trace" .pft.bin)
  run_replay reject "$trace" "$label"
done
