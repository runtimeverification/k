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

execute () {
  (
  if $verbose; then
    set -x
  fi
  "$@"
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
