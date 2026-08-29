#!/bin/bash -p
# Canonical CakeML bootstrap entry point. Invoke this exact absolute path via:
#   /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C /absolute/path/... <five args>
# The first env/interpreter loader startup precedes these checks and remains an
# explicit trusted boundary; the script immediately execs one isolated Python
# controller which holds the lock and owns every subsequent phase.
set -euo pipefail

usage() {
  printf 'usage: %s <CakeML checkout> <HOL4 checkout> <bootstrap.log> <bootstrap-preflight.json> <bootstrap-provenance.json>\n' "$0" >&2
  exit 2
}

[[ $# -eq 5 ]] || usage
[[ ${PATH-} == /usr/bin:/bin && ${LC_ALL-} == C ]] || {
  printf 'controller must be launched with exact PATH=/usr/bin:/bin and LC_ALL=C\n' >&2
  exit 1
}
while IFS= read -r variable; do
  case $variable in
    PATH|LC_ALL|PWD|SHLVL|_) ;;
    *)
      printf 'unexpected controller launch environment: %s\n' "$variable" >&2
      exit 1
      ;;
  esac
done < <(compgen -e)
[[ ${SHLVL-} == 1 && ${PWD-} == "$(pwd -P)" ]] || {
  printf 'controller was not launched through the exact outer env -i boundary\n' >&2
  exit 1
}
[[ ! -e /etc/ld.so.preload && ! -L /etc/ld.so.preload ]] || {
  printf 'system-wide dynamic-loader preload is outside the bootstrap model\n' >&2
  exit 1
}
[[ ${BASH_SOURCE[0]} == /* && ${BASH_SOURCE[0]} == */* ]] || {
  printf 'controller must be invoked by its exact absolute path\n' >&2
  exit 1
}
script_dir=${BASH_SOURCE[0]%/*}
[[ ${BASH_SOURCE[0]} == "$script_dir/build-local-cakeml-bootstrap.sh" ]] || {
  printf 'controller must be invoked by its exact absolute path\n' >&2
  exit 1
}

exec /usr/bin/env -i PATH=/usr/bin:/bin LC_ALL=C \
  /usr/bin/python3 -I -S "$script_dir/candle/cakeml_artifact_provenance.py" \
  run-bootstrap \
  --candle-root "$script_dir" \
  --cakeml-root "$1" \
  --hol-root "$2" \
  --bootstrap-log "$3" \
  --preflight "$4" \
  --write "$5"
