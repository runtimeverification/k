#!/bin/bash
# This script is designed to provide a common bash library of functions for
# scripts that are written primarily in bash. Right now, that consists of
# kore-print, kparse, kparse-gen, and krun. There is probably some code
# shared among those files that could be factored out further into this
# script, but this is an initial effort to factor out some of the most obvious
# cases.
#
# You can use this script by adding the following line (minus the comment) to
# your script:
#
# ktool=TOOL_NAME
# source "$(dirname "$0")/../lib/kframework/k-util.sh"

# initialize flags
fold_lines='fold -s'
profile=false
verbose=false

# initialize state
result=0

error () {
  local result
  result="$1" ; shift
  printf "[Error] ${ktool}: $*\n" | ${fold_lines} 1>&2
  exit ${result}
}

k_util_usage() {
    cat <<HERE
  --no-exc-wrap     Do not wrap messages to 80 chars (keep long lines).
  --profile         Print coarse process timing information. Format printed:
                    exit-code wall-time user-time system-time command args*
  -v, --verbose     Print significant sub-commands executed.
HERE
}

args=()
literal=false
while [[ "$#" -gt 0 ]]
do
  arg="$1" ; shift
  if ${literal}; then
    args+=("${arg}")
  else
    case "${arg}" in
      --no-exc-wrap)
      fold_lines='cat -'
      ;;

      --profile)
      profile=true
      ;;

      --verbose)
      verbose=true
      ;;

      --)
      literal=true
      ;;

      *)
      args+=("${arg}")
      ;;
    esac
  fi
done
if [[ "${#args[@]}" -gt 0 ]]; then
  set -- "${args[@]}"
fi

execute () {
  (
  if ${verbose}; then
    set -x
  fi
  if ${profile}; then
    time --format '%x %Es %Us %Ss %C' -- "$@"
  else
    "$@"
  fi
  )
}

output () {
  target="$1"
  shift
  if [ "$target" = "/dev/stdout" ]; then
    "$@"
  elif [ "$target" = "/dev/stderr" ]; then
    "$@" 1>&2
  else
    "$@" > "$target"
  fi
}

catNewline () {
  cat "$@"
  echo
}
