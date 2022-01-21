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
# source "$(dirname "$0")/../lib/kframework/k-util.sh"

time_millis () {
  # Using this solution to support MacOS
  # https://superuser.com/questions/599072/how-to-get-bash-execution-time-in-milliseconds-under-mac-os-x
  # TODO: Is it worth the extra dependency on perl? Should we find a different way.
  perl -MTime::HiRes -e 'printf("%.0f\n",Time::HiRes::time()*1000)'
}

# initialize flags
fold_lines='fold -s'
profile=false
verbose=false

# initialize state
old_millis="$(time_millis)"
result=0

error () {
  local result
  result="$1" ; shift
  printf "[Error] Critical: $*\n" | ${fold_lines} 1>&2
  exit ${result}
}

time_diff () {
  local time1 time2
  time2="$1" ; shift
  time1="$1" ; shift
  echo "$((${time2} - ${time1}))"
}

profile_line () {
  local new_millis diff_millis
  new_millis="$(time_millis)"
  diff_millis="$((${new_millis} - ${old_millis}))"
  old_millis="${new_millis}"
  printf "[Timing ${diff_millis} ms] $*\n" | ${fold_lines} 1>&2
}

k_util_usage() {
    cat <<HERE
  --no-exc-wrap     Do not wrap messages to 80 chars (keep long lines).
  --profile         Print coarse process timing information
  -v, --verbose     Print significant sub-commands executed
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
    profile_line "Starting: $*"
  fi
  "$@"
  if ${profile}; then
    profile_line "Finished: $*"
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
