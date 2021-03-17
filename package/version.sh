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
commit_version_file="package/version.commit"
version_file="package/version"
release_tag_file="package/version.release-tag"
version_date_file="package/version.date"

version_bump() {
    local master_commit master_major master_minor master_patch master_commit
    local release_commit release_patch release_minor release_major
    local release_tag version_date

    master_commit="$(git rev-parse --short=7 ${UPSTREAM}/${MASTER})"
    release_commit="$(git rev-parse --short=7 ${UPSTREAM}/${RELEASE})"

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
    echo "$master_commit" > $commit_version_file

    major="$(cat $major_version_file)"
    minor="$(cat $minor_version_file)"
    patch="$(cat $patch_version_file)"
    commit="$(cat $commit_version_file)"
    version="${major}.${minor}.${patch}"
    echo "$version" > $version_file

    release_tag="${version}-${commit}"
    echo "$release_tag" > $release_tag_file

    version_date="$(date)"
    echo "$version_date" > $version_date_file

    notif "Version: ${release_tag}"
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
