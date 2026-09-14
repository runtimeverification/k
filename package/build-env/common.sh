# Shared by build-deb and test-deb. Source it; it is not executable.

# The one table. The LLVM and JDK versions are properties of the Ubuntu
# release, not free choices: each release carries one clang/lld/llvm-tools set
# and one JDK that K is built and tested against. Adding a release means
# editing here and in the CI matrix, and nowhere else.
#
# JDK in particular is worth having written down: the Dockerfile declares
# JDK_VERSION with NO default, so a caller that forgets it installs the package
# `openjdk--jdk` and the build fails several minutes in, on an apt error that
# does not mention the build arg.
llvm_version_for() {
    case "${1}" in
        jammy) echo 15 ;;
        noble) echo 17 ;;
        *)     return 1 ;;
    esac
}

jdk_version_for() {
    case "${1}" in
        jammy) echo 17 ;;
        noble) echo 21 ;;
        *)     return 1 ;;
    esac
}

SUPPORTED_DISTROS='jammy noble'

# k builds two debs from one tree, each with its own recipe directory under
# package/debian/ and its own test script. Keeping the pairing here means
# test-deb cannot be pointed at the wrong test for a package.
SUPPORTED_PACKAGES='kframework kframework-frontend'

test_script_for() {
    case "${1}" in
        kframework)          echo 'package/debian/test-package' ;;
        kframework-frontend) echo 'package/debian/test-frontend-package' ;;
        *)                   return 1 ;;
    esac
}

require_distro() {
    if [ -z "${1}" ]; then
        echo "${0##*/}: usage: ${0##*/} <${SUPPORTED_DISTROS// /|}> [package] [output.deb]" >&2
        exit 2
    fi
    if ! llvm_version_for "${1}" > /dev/null; then
        echo "${0##*/}: unknown distro '${1}' (expected: ${SUPPORTED_DISTROS})" >&2
        exit 2
    fi
}

require_package() {
    if ! test_script_for "${1}" > /dev/null; then
        echo "${0##*/}: unknown package '${1}' (expected: ${SUPPORTED_PACKAGES})" >&2
        exit 2
    fi
}

default_pkg_name() {
    echo "${2}_amd64_ubuntu_${1}.deb"
}

# podman is what RV uses; docker is accepted so this still runs on a machine
# that only has that. CONTAINER_ENGINE overrides both.
container_engine() {
    if [ -n "${CONTAINER_ENGINE:-}" ]; then
        echo "${CONTAINER_ENGINE}"
    elif command -v podman > /dev/null 2>&1; then
        echo podman
    elif command -v docker > /dev/null 2>&1; then
        echo docker
    else
        echo "${0##*/}: no container engine found (looked for podman, docker)" >&2
        exit 1
    fi
}
