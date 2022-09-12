#!/usr/bin/env bash

set -xeuo pipefail

notif() { echo "== $@" >&2 ; }
fatal() { echo "[FATAL] $@" ; exit 1 ; }

version_file="package/version"

version_bump() {
    local version release_commit version_major version_minor version_patch new_version current_version_major current_version_minor current_version_patch
    version="$1"
    version_major="$(echo ${version} | cut --delimiter '.' --field 1)"
    version_minor="$(echo ${version} | cut --delimiter '.' --field 2)"
    version_patch="$(echo ${version} | cut --delimiter '.' --field 3)"
    current_version="$(cat ${version_file})"
    current_version_major="$(echo ${current_version} | cut --delimiter '.' --field 1)"
    current_version_minor="$(echo ${current_version} | cut --delimiter '.' --field 2)"
    current_version_patch="$(echo ${current_version} | cut --delimiter '.' --field 3)"
    new_version="${current_version}"
    if [[ "${version_major}" == "${current_version_major}" ]] && [[ "${version_minor}" == "${current_version_minor}" ]]; then
        new_version="${version_major}.${version_minor}.$((version_patch + 1))"
    fi
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

version_command="$1"

case "${version_command}" in
    bump) version_bump "$@"                      ;;
    sub)  version_sub  "$@"                      ;;
    *)    fatal "No command: ${version_command}" ;;
esac
