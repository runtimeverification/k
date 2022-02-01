#!/bin/bash

SCRIPTS_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
RELEASE_TAG=$("$SCRIPTS_DIR/newest-release-tag.sh")

MERGE_BASE=$(git merge-base "$RELEASE_TAG" HEAD)
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
