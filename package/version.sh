#!/usr/bin/env bash

set -xeuo pipefail

notif() { echo "== $@" >&2 ; }
fatal() { echo "[FATAL] $@" ; exit 1 ; }

version_file="package/version"

version_bump() {
    local version release_commit version_major version_minor version_patch new_version
    version="$(cat ${version_file})"
    version_major="$(echo ${current_version} | cut --delimiter '.' --field 1)"
    version_minor="$(echo ${current_version} | cut --delimiter '.' --field 2)"
    version_patch="$(echo ${current_version} | cut --delimiter '.' --field 3)"
    new_version="${version}"
    new_version="${version_major}.${version_minor}.$((version_patch + 1))"
    echo "${new_version}" > "${version_file}"
    notif "Version: ${new_version}"
}

version_sub() {
    local version
    version="$(cat $version_file)"
    sed --in-place 's/^K_VERSION=.*$/K_VERSION='${version}'/'                                                         install-k
    sed --in-place 's/^pkgver=.*$/pkgver='${version}'/'                                                               package/arch/PKGBUILD
    sed --in-place 's/^kframework (.*) unstable; urgency=medium$/kframework ('${version}') unstable; urgency=medium/' package/debian/changelog
    sed --in-place 's/^K_VERSION=.*$/K_VERSION='${version}'/'                                                         src/main/scripts/test-in-container-debian
}

version_command="$1" ; shift

case "${version_command}" in
    bump) version_bump "$@"                      ;;
    sub)  version_sub  "$@"                      ;;
    *)    fatal "No command: ${version_command}" ;;
esac
