#!/bin/bash

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
