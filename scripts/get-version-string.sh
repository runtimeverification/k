#!/bin/bash

MERGE_BASE=$(git merge-base master HEAD)
VERSION_TAG=$(git describe --contains --always "$MERGE_BASE" | sed 's/~.*//')

VERSION_STRING=$VERSION_TAG

DISTANCE=$(git rev-list --count "$MERGE_BASE"..HEAD)
VERSION_STRING+="-$DISTANCE"

SHA=$(git rev-parse --short HEAD)
VERSION_STRING+="-g$SHA"

DIRTY=$(git diff HEAD)
if [ -n "$DIRTY" ]; then
  VERSION_STRING+=-dirty
fi

echo $VERSION_STRING
