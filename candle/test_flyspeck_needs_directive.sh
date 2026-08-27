#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle.sh"}
fixture_prefix=candle/compatibility/fixtures
action_ok_md5=$(md5sum "$candle_root/$fixture_prefix/flyspeck_needs_action_ok.ml" | cut -d' ' -f1)
action_eval_fail_md5=$(md5sum "$candle_root/$fixture_prefix/flyspeck_needs_action_eval_fail.ml" | cut -d' ' -f1)
loadt_action_md5=$(md5sum "$candle_root/$fixture_prefix/flyspeck_loadt_action.ml" | cut -d' ' -f1)
test_dir=$(mktemp -d /tmp/candle-flyspeck-needs.XXXXXX)
cleanup() {
  find "$test_dir" -depth -delete 2>/dev/null || true
}
trap cleanup EXIT

run_candle() {
  local name=$1
  shift
  (
    cd "$candle_root"
    timeout 90 "$candle_binary" >"$test_dir/$name.log" 2>&1 "$@"
  )
}

run_candle accepted <<EOF
let flyspeck_action_value = ref 0;;
let flyspeck_neutralize_count = ref 0;;
module State_manager = struct
  let neutralize_state () =
    flyspeck_neutralize_count := !flyspeck_neutralize_count + 1
end;;
Cakeml.configureSourceIdentities
  [(Filename.concat Filename.currentDir "$fixture_prefix/flyspeck_needs_action_ok.ml",
    ("flyspeck_needs_action_ok.ml","$action_ok_md5"))];;
#flyspeck_needs "$fixture_prefix/flyspeck_needs_action_ok.ml";;
#flyspeck_needs "$fixture_prefix/flyspeck_needs_action_ok.ml";;
let flyspeck_identity_reconfigure_rejected =
  try Cakeml.configureSourceIdentities []; false
  with Failure _ -> true;;
let flyspeck_action_source_id =
  ("flyspeck_needs_action_ok.ml","$action_ok_md5");;
if !flyspeck_action_value = 1 && !flyspeck_neutralize_count = 1 &&
   !Cakeml.loadedSourceIds = [flyspeck_action_source_id] &&
   flyspeck_identity_reconfigure_rejected then
  print "FLYSPECK_NEEDS_ACCEPTED_OK\n"
else failwith "Flyspeck source action count mismatch";;
EOF
rg -Fq 'FLYSPECK_NEEDS_ACCEPTED_OK' "$test_dir/accepted.log"
[[ $(rg -c -- '- Flyspeck source action complete:' "$test_dir/accepted.log") == 1 ]]
rg -Fq -- '- Already loaded:' "$test_dir/accepted.log"

run_candle loadt <<EOF
let flyspeck_loadt_value = ref 0;;
let flyspeck_loadt_neutralize_count = ref 0;;
module State_manager = struct
  let neutralize_state () =
    flyspeck_loadt_neutralize_count := !flyspeck_loadt_neutralize_count + 1
end;;
Cakeml.configureSourceIdentities
  [(Filename.concat Filename.currentDir "$fixture_prefix/flyspeck_loadt_action.ml",
    ("flyspeck_loadt_action.ml","$loadt_action_md5"))];;
#flyspeck_loadt "$fixture_prefix/flyspeck_loadt_action.ml";;
#flyspeck_loadt "$fixture_prefix/flyspeck_loadt_action.ml";;
let flyspeck_loadt_source_id =
  ("flyspeck_loadt_action.ml","$loadt_action_md5");;
if !flyspeck_loadt_value = 2 && !flyspeck_loadt_neutralize_count = 0 &&
   !Cakeml.loadedSourceIds =
     [flyspeck_loadt_source_id;flyspeck_loadt_source_id] then
  print "FLYSPECK_LOADT_ACCEPTED_OK\n"
else failwith "Flyspeck loadt action mismatch";;
EOF
rg -Fq 'FLYSPECK_LOADT_ACCEPTED_OK' "$test_dir/loadt.log"
[[ $(rg -c -- '- Flyspeck source action complete:' "$test_dir/loadt.log") == 2 ]]
if rg -q 'Already loaded|EXCEPTION:|Parsing failed' "$test_dir/loadt.log"; then
  tail -n 50 "$test_dir/loadt.log" >&2
  exit 1
fi

run_candle ordinary-boundary <<EOF
let flyspeck_action_value = ref 0;;
let needs (_:string) = flyspeck_action_value := 100;;
let loads (_:string) = flyspeck_action_value := 200;;
if false then needs "$fixture_prefix/flyspeck_needs_action_ok.ml";;
if false then loads "$fixture_prefix/flyspeck_needs_action_ok.ml";;
loads "$fixture_prefix/source_action_boundary_module.ml";;
needs "$fixture_prefix/flyspeck_needs_action_ok.ml";;
if !flyspeck_action_value = 1 && Source_action_boundary_module.value = 7 then
  print "ORDINARY_SOURCE_ACTION_BOUNDARY_OK\n"
else failwith "ordinary source action escaped its phrase boundary";;
EOF
rg -Fq 'ORDINARY_SOURCE_ACTION_BOUNDARY_OK' "$test_dir/ordinary-boundary.log"
if rg -q 'EXCEPTION:|Parsing failed' "$test_dir/ordinary-boundary.log"; then
  tail -n 50 "$test_dir/ordinary-boundary.log" >&2
  exit 1
fi

run_candle overlay <<EOF
let flyspeck_overlay_value = ref 0;;
let flyspeck_overlay_original =
  Filename.concat Filename.currentDir "$fixture_prefix/flyspeck_overlay_original.ml";;
let flyspeck_overlay_normalized =
  "$fixture_prefix/flyspeck_overlay_normalized.ml";;
Cakeml.configureNormalizationOverlay
  [flyspeck_overlay_original,flyspeck_overlay_normalized];;
needs "$fixture_prefix/flyspeck_overlay_original.ml";;
let flyspeck_overlay_reconfigure_rejected =
  try Cakeml.configureNormalizationOverlay []; false
  with Failure _ -> true;;
if !flyspeck_overlay_value = 2 && flyspeck_overlay_reconfigure_rejected then
  print "FLYSPECK_NORMALIZATION_OVERLAY_OK\n"
else failwith "Flyspeck normalization overlay mismatch";;
EOF
rg -Fq 'FLYSPECK_NORMALIZATION_OVERLAY_OK' "$test_dir/overlay.log"
rg -Fq -- '- Selecting normalized source' "$test_dir/overlay.log"

run_candle identity-rejected <<EOF
let flyspeck_action_value = ref 0;;
module State_manager = struct
  let neutralize_state () = print "UNEXPECTED_FLYSPECK_IDENTITY_REJECTION_NEUTRALIZE\n"
end;;
#use "$fixture_prefix/flyspeck_needs_identity_reject_driver.ml";;
EOF
rg -Fq 'Candle source identities are not configured' \
  "$test_dir/identity-rejected.log"
if rg -q 'Flyspeck source action complete|UNEXPECTED_FLYSPECK_IDENTITY_REJECTION_(CONTINUATION|NEUTRALIZE)' \
  "$test_dir/identity-rejected.log"
then
  tail -n 40 "$test_dir/identity-rejected.log" >&2
  exit 1
fi

run_candle eval-fail <<EOF
let flyspeck_action_value = ref 0;;
module State_manager = struct
  let neutralize_state () = print "UNEXPECTED_FLYSPECK_EVAL_FAILURE_NEUTRALIZE\n"
end;;
Cakeml.configureSourceIdentities
  [(Filename.concat Filename.currentDir "$fixture_prefix/flyspeck_needs_action_eval_fail.ml",
    ("flyspeck_needs_action_eval_fail.ml","$action_eval_fail_md5"))];;
#use "$fixture_prefix/flyspeck_needs_eval_fail_driver.ml";;
EOF
rg -Fq 'injected Flyspeck source evaluation failure' "$test_dir/eval-fail.log"
if rg -q 'Flyspeck source action complete|UNEXPECTED_FLYSPECK_EVAL_FAILURE_(CONTINUATION|NEUTRALIZE)' \
  "$test_dir/eval-fail.log"
then
  tail -n 40 "$test_dir/eval-fail.log" >&2
  exit 1
fi

run_candle neutralize-fail <<EOF
let flyspeck_action_value = ref 0;;
module State_manager = struct
  let neutralize_state () : unit =
    failwith "injected Flyspeck neutralization failure"
end;;
Cakeml.configureSourceIdentities
  [(Filename.concat Filename.currentDir "$fixture_prefix/flyspeck_needs_action_ok.ml",
    ("flyspeck_needs_action_ok.ml","$action_ok_md5"))];;
#use "$fixture_prefix/flyspeck_needs_neutralize_fail_driver.ml";;
EOF
rg -Fq 'injected Flyspeck neutralization failure' \
  "$test_dir/neutralize-fail.log"
if rg -q 'Flyspeck source action complete|UNEXPECTED_FLYSPECK_NEUTRALIZE_FAILURE_CONTINUATION' \
  "$test_dir/neutralize-fail.log"
then
  tail -n 40 "$test_dir/neutralize-fail.log" >&2
  exit 1
fi

run_candle malformed <<'EOF'
let malformed_prefix = 1 #flyspeck_needs "candle/compatibility/fixtures/flyspeck_needs_action_ok.ml";;
EOF
rg -Fq '#flyspeck_needs must be a standalone top-level phrase' \
  "$test_dir/malformed.log"
if rg -q 'Flyspeck source action complete' "$test_dir/malformed.log"; then
  tail -n 30 "$test_dir/malformed.log" >&2
  exit 1
fi

run_candle malformed-loadt <<'EOF'
let malformed_prefix = 1 #flyspeck_loadt "candle/compatibility/fixtures/flyspeck_loadt_action.ml";;
EOF
rg -Fq '#flyspeck_loadt must be a standalone top-level phrase' \
  "$test_dir/malformed-loadt.log"
if rg -q 'Flyspeck source action complete' "$test_dir/malformed-loadt.log"; then
  tail -n 30 "$test_dir/malformed-loadt.log" >&2
  exit 1
fi

printf 'PASS: exact Flyspeck source actions and ordinary phrase boundaries\n'
