ARG BASE_OS
ARG BASE_DISTRO
ARG K_VERSION

ARG Z3_VERSION
FROM runtimeverificationinc/z3:${BASE_OS}-${BASE_DISTRO}-${Z3_VERSION} as Z3

ARG BASE_OS
ARG BASE_DISTRO
ARG K_VERSION
FROM stack:${BASE_DISTRO}-${K_VERSION} as STACK

ARG BASE_OS
ARG BASE_DISTRO
ARG K_VERSION
FROM maven:${BASE_DISTRO}-${K_VERSION} as MAVEN

ARG BASE_OS
ARG BASE_DISTRO
FROM ${BASE_OS}:${BASE_DISTRO}

ENV TZ America/Chicago
ENV DEBIAN_FRONTEND=noninteractive

ARG LLVM_VERSION
ARG JDK_VERSION

RUN    apt-get update              \
    && apt-get install --yes       \
        bison                      \
        build-essential            \
        clang-${LLVM_VERSION}      \
        cmake                      \
        curl                       \
        debhelper                  \
        flex                       \
        gcc                        \
        git                        \
        libboost-test-dev          \
        libbz2-dev                 \
        libffi-dev                 \
        libfmt-dev                 \
        libgdbm-dev                \
        libgmp-dev                 \
        libjemalloc-dev            \
        libmpfr-dev                \
        libncurses5-dev            \
        libnss3-dev                \
        libreadline-dev            \
        libsecp256k1-dev           \
        libsqlite3-dev             \
        libssl-dev                 \
        libunwind-dev              \
        libyaml-dev                \
        libz3-dev                  \
        lld-${LLVM_VERSION}        \
        llvm-${LLVM_VERSION}-tools \
        locales                    \
        lsof                       \
        maven                      \
        openjdk-${JDK_VERSION}-jdk \
        parallel                   \
        pkg-config                 \
        python3                    \
        python3-dev                \
        python3-pip                \
        xxd                        \
        zlib1g-dev

COPY --from=Z3 /usr/bin/z3 /usr/bin/z3
COPY --from=STACK /usr/local/bin/stack /usr/local/bin/stack

RUN locale-gen en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

# The build runs as an account whose uid/gid match the CALLER's, so that files
# written to the bind-mounted checkout are owned by whoever invoked the build.
# Only the ids matter for that; the name is ours to pick, and picking it here
# rather than taking it from the caller is what keeps the three images in this
# directory agreeing -- the main Dockerfile COPYs /home/$USER/.stack and
# /home/$USER/.m2 out of the other two, so a caller that passed a different
# name to one build than another would produce an image missing its caches.
#
# It also stops the image colliding with the base: ubuntu:noble ships an
# `ubuntu` account at uid/gid 1000, and `users` (gid 100) is the primary group
# of many developer accounts. Either makes groupadd/useradd fail minutes into
# the build with a message that never mentions a build arg. -o permits the ids
# to be shared with an existing account rather than deleting a system account
# that something else already uses.
ARG USER=builder
ARG GROUP=$USER
ARG USER_ID=1000
ARG GROUP_ID=$USER_ID
RUN groupadd -o -g $GROUP_ID $GROUP && useradd -o -m -u $USER_ID -s /bin/sh -g $GROUP $USER


# dpkg-buildpackage writes its output to the PARENT of the directory it builds
# in, and package/debian/build-package globs ../<pkg>_*_amd64.deb to find it.
# So the build needs a writable parent: build-deb mounts the checkout at
# /opt/workspace/source, and this is the directory that has to exist and be
# owned by the build user for that to work.
#
# Mounting the checkout directly at /opt/workspace instead makes the parent `/`,
# which the build user cannot write, and the failure surfaces from inside
# dpkg-buildpackage rather than from the mount that caused it.
RUN mkdir -p /opt/workspace && chown $USER_ID:$GROUP_ID /opt/workspace

USER $USER:$GROUP

COPY --from=STACK --chown=$USER:$GROUP /home/$USER/.stack /home/$USER/.stack
COPY --from=MAVEN --chown=$USER:$GROUP /home/$USER/.m2 /home/$USER/.m2
