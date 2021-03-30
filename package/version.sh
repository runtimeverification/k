#!/usr/bin/env bash

set -xeuo pipefail

UPSTREAM="${UPSTREAM:-origin}"
MASTER="${MASTER:-master}"
RELEASE="${RELEASE:-release}"

notif() { echo "== $@" >&2 ; }
fatal() { echo "[FATAL] $@" ; exit 1 ; }

major_version_file="package/version.major"
minor_version_file="package/version.minor"
patch_version_file="package/version.patch"
version_file="package/version"

version_set_major_minor_patch() {
    local version_commit

    version_commit="$1" ; shift

    version_major="$(git show $version_commit:$version_file | cut --delimiter '.' --field 1)"
    version_minor="$(git show $version_commit:$version_file | cut --delimiter '.' --field 2)"
    version_patch="$(git show $version_commit:$version_file | cut --delimiter '.' --field 3)"
}

version_bump() {
    local master_commit master_major master_minor master_patch
    local release_commit release_patch release_minor release_major

    master_commit="$(git rev-parse --short=7 ${UPSTREAM}/${MASTER})"
    release_commit="$(git rev-parse --short=7 ${UPSTREAM}/${RELEASE})"

    version_set_major_minor_patch "$master_commit"
    master_major="$version_major"
    master_minor="$version_minor"
    master_patch="$version_patch"

    version_set_major_minor_patch "$release_commit"
    release_major="$version_major"
    release_minor="$version_minor"
    release_patch="$version_patch"

    echo $master_major $master_minor $master_patch
    echo $release_major $release_minor $release_patch

    major="$release_major"
    minor="$release_minor"
    patch="$release_patch"
    if [[ "$master_major" -gt "$release_major" ]]; then
        minor='0'
        patch='0'
    elif [[ "$master_minor" -gt "$release_minor" ]]; then
        patch='0'
    else
        patch=$(($patch + 1))
    fi

    version="${major}.${minor}.${patch}"
    echo "$version" > $version_file

    notif "Version: ${version}"
}

version_sub() {
    local version
    version="$(cat $version_file)"
    sed --in-place 's/K_VERSION=5.0.0/K_VERSION='${version}'/'                                                         install-k
    sed --in-place 's/name = "k-5.0.0";/name = "k-'${version}'";/'                                                     nix/k.nix
    sed --in-place 's/pkgver=5.0.0/pkgver='${version}'/'                                                               package/arch/PKGBUILD
    sed --in-place 's/kframework (5.0.0) unstable; urgency=medium/kframework ('${version}') unstable; urgency=medium/' package/debian/changelog
    sed --in-place 's/K_VERSION=5.0.0/K_VERSION='${version}'/'                                                         src/main/scripts/test-in-container-debian
}

version_command="$1"

case "$version_command" in
    bump) version_bump "$@"                    ;;
    sub)  version_sub  "$@"                    ;;
    *)    fatal "No command: $version_command" ;;
esac
