#!/usr/bin/env bash

set -euo pipefail

UPSTREAM="${UPSTREAM:-origin}"
MASTER="${MASTER:-master}"
RELEASE="${RELEASE:-release}"

notif() { echo "== $@" >&2 ; }
fatal() { echo "[FATAL] $@" ; exit 1 ; }

git fetch --all
current_commit="$(git rev-parse HEAD)"
master_commit="$(git rev-parse ${UPSTREAM}/${MASTER})"
release_commit="$(git rev-parse ${UPSTREAM}/${RELEASE})"

major_version_file="package/version.major"
minor_version_file="package/version.minor"
patch_version_file="package/version.patch"
version_file="package/version"

version_bump() {
    local master_major master_minor master_patch
    local release_patch release_minor release_major
    master_major="$(git show $master_commit:$major_version_file)"
    master_minor="$(git show $master_commit:$minor_version_file)"
    master_patch="$(git show $master_commit:$patch_version_file)"
    release_major="$(git show $release_commit:$major_version_file)"
    release_minor="$(git show $release_commit:$minor_version_file)"
    release_patch="$(git show $release_commit:$patch_version_file)"
    if [[ "$master_major" -gt "$release_major" ]]; then
        echo 0 > $minor_version_file
        echo 0 > $patch_version_file
    elif [[ "$master_minor" -gt "$release_minor" ]]; then
        echo 0 > $patch_version_file
    else
        echo $(($release_patch + 1)) > $patch_version_file
    fi
}

version_fill() {
    local major minor patch version
    major="$(cat $major_version_file)"
    minor="$(cat $minor_version_file)"
    [[ -f "$patch_version_file" ]] || echo 0 > "$patch_version_file"
    patch="$(cat $patch_version_file)"
    version="$major.$minor.$patch"
    notif "Version: $version"
    echo "$version" > "$version_file"
}

version_command="$1"

case "$version_command" in
    bump) version_bump "$@"                    ;;
    fill) version_fill "$@"                    ;;
    *)    fatal "No command: $version_command" ;;
esac
