#!/bin/bash

for sha in $(git rev-list origin/master); do
  if tag=$(git describe --tags --exact-match $sha 2>/dev/null); then
    echo $tag
    break
  fi
done
