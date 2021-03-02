#!/usr/bin/env bash

set -euo pipefail

UPSTREAM="${UPSTREAM:-origin}"

notif() { echo "== $@" >&2 ; }
fatal() { echo "[FATAL] $@" ; exit 1 ; }

command="$1" ; shift

git fetch --all
current_commit="$(git rev-parse HEAD)"
master_commit="$(git rev-parse ${UPSTREAM}/master)"
release_commit="$(git rev-parse ${UPSTREAM}/release)"
common_commit="$(git merge-base ${UPSTREAM}/master ${UPSTREAM}/release)"

major_version_file="package/version.major"
minor_version_file="package/version.minor"
patch_version_file="package/version.patch"
version_file="package/version"

version_fill() {
    local major minor patch version
    major="$(cat $major_version_file)"
    minor="$(cat $minor_version_file)"
    [[ -f "$patch_version_file" ]] || echo '0' > "$patch_version_file"
    patch="$(cat $patch_version_file)"

    version="$major.$minor.$patch"

    notif "Version: $version"
    echo "$version" > "$version_file"
}
