#!/usr/bin/env bash

set -xeuo pipefail

notif() { echo "== $@" >&2 ; }
fatal() { echo "[FATAL] $@" ; exit 1 ; }

version_file="package/version"

version_bump() {
    local version release_commit version_major version_minor version_patch new_version
    version="$(cat ${version_file})"
    version_major="$(echo ${version} | cut --delimiter '.' --field 1)"
    version_minor="$(echo ${version} | cut --delimiter '.' --field 2)"
    version_patch="$(echo ${version} | cut --delimiter '.' --field 3)"
    new_version="${version}"
    new_version="${version_major}.${version_minor}.$((version_patch + 1))"
    echo "${new_version}" > "${version_file}"
    notif "Version: ${new_version}"
}

version_sub() {
    local version
    version="$(cat $version_file)"
    sed --in-place 's/^K_VERSION=.*$/K_VERSION='${version}'/'                                                         install-k
    sed --in-place 's/^kframework (.*) unstable; urgency=medium$/kframework ('${version}') unstable; urgency=medium/' package/debian/kframework/changelog
    sed --in-place 's/^version = ".*"$/version = "'${version}'"/'                                                     pyk/pyproject.toml
    sed --in-place "s/^version = '.*'$/version = '${version}'/"                                                       pyk/docs/conf.py
    sed --in-place "s/^release = '.*'$/release = '${version}'/"                                                       pyk/docs/conf.py
}

version_command="$1" ; shift

case "${version_command}" in
    bump) version_bump "$@"                      ;;
    sub)  version_sub  "$@"                      ;;
    *)    fatal "No command: ${version_command}" ;;
esac
