#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  printf 'usage: %s /path/to/candle.sh\n' "$0" >&2
  exit 2
fi

candle_script=$(realpath -- "$1")
test_tmp=$(mktemp -d /tmp/candle-static-load.XXXXXX)
cleanup() {
  find "$test_tmp" -maxdepth 1 -type f -delete 2>/dev/null || true
  rmdir "$test_tmp" 2>/dev/null || true
}
trap cleanup EXIT

accept_log="$test_tmp/accept.log"
(
  cd -- "$(dirname -- "$candle_script")"
  timeout 120 "$candle_script" >"$accept_log" 2>&1 <<'EOF'
#load "unix.cma";;
#load "str.cma";;
print "STATIC_LOAD_ACCEPT_OK\n";;
EOF
)
rg -Fq -- '- Selecting statically linked library unix.cma (module Unix)' "$accept_log"
rg -Fq -- '- Selecting statically linked library str.cma (module Str)' "$accept_log"
rg -Fq 'STATIC_LOAD_ACCEPT_OK' "$accept_log"
if rg -q 'No such file: .*\.cma|Static #load rejected' "$accept_log"; then
  tail -n 40 "$accept_log" >&2
  exit 1
fi

unknown_log="$test_tmp/unknown.log"
(
  cd -- "$(dirname -- "$candle_script")"
  timeout 120 "$candle_script" >"$unknown_log" 2>&1 <<'EOF'
#load "dynlink.cma";;
EOF
)
rg -Fq -- '- Static #load rejected: unsupported library dynlink.cma' "$unknown_log"
if rg -q 'Selecting statically linked library .*dynlink' "$unknown_log"; then
  tail -n 40 "$unknown_log" >&2
  exit 1
fi

embedded_log="$test_tmp/embedded.log"
(
  cd -- "$(dirname -- "$candle_script")"
  timeout 120 "$candle_script" >"$embedded_log" 2>&1 <<'EOF'
print "BEFORE" #load "unix.cma" print "SHOULD_NOT_RUN";;
print "AFTER_REJECTION\n";;
EOF
)
rg -Fq -- '- Static #load rejected: #load must be a standalone top-level phrase' "$embedded_log"
rg -Fq 'AFTER_REJECTION' "$embedded_log"
if rg -q 'BEFORE|SHOULD_NOT_RUN|Selecting statically linked library' "$embedded_log"; then
  tail -n 40 "$embedded_log" >&2
  exit 1
fi

malformed_log="$test_tmp/malformed.log"
(
  cd -- "$(dirname -- "$candle_script")"
  timeout 120 "$candle_script" >"$malformed_log" 2>&1 <<'EOF'
#load unix.cma;;
EOF
)
rg -Fq -- '- Static #load rejected: #load requires one string literal and double semicolon [;;]' "$malformed_log"

printf 'CANDLE_STATIC_LOAD_DIRECTIVE_OK cases=4\n'
