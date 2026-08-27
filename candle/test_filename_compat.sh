#!/usr/bin/env bash
set -euo pipefail

candle_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
candle_binary=${CANDLE_BINARY:-"$candle_root/candle.sh"}
log=$(mktemp /tmp/candle-filename-compat.XXXXXX.log)
cleanup() {
  find "$log" -maxdepth 0 -type f -delete 2>/dev/null || true
}
trap cleanup EXIT

(
  cd "$candle_root"
  timeout 90 "$candle_binary" >"$log" 2>&1 <<'EOF'
let filename_cases =
  [("",".","."); (".",".","."); ("..","..",".");
   ("/","/","/"); ("//","/","/"); ("a","a",".");
   ("a/","a","."); ("a/b","b","a"); ("/a/b","b","/a");
   ("/a/b/","b","/a"); ("./a","a","."); ("../a","a","..");
   ("///a///","a","/")];;
let filename_case_ok (path,base,dir) =
  Filename.basename path = base && Filename.dirname path = dir;;
if List.all filename_case_ok filename_cases then
  print "CANDLE_FILENAME_COMPAT_OK\n"
else failwith "Filename.basename/dirname differs from OCaml 4.14.1";;
EOF
)

rg -Fq 'CANDLE_FILENAME_COMPAT_OK' "$log"
if rg -q 'ERROR:|EXCEPTION:|Parsing failed' "$log"; then
  tail -n 60 "$log" >&2
  exit 1
fi
printf 'PASS: Filename basename/dirname OCaml 4.14.1 edge cases\n'
