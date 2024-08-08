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
        python3-distutils          \
        python3-pip                \
        xxd                        \
        zlib1g-dev

COPY --from=Z3 /usr/bin/z3 /usr/bin/z3
COPY --from=STACK /usr/local/bin/stack /usr/local/bin/stack

RUN locale-gen en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

# The image is built specifically for an environment with this user/group
ARG USER=github-user
ARG GROUP=$USER
ARG USER_ID=1000
ARG GROUP_ID=$USER_ID
RUN groupadd -g $GROUP_ID $GROUP && useradd -m -u $USER_ID -s /bin/sh -g $GROUP $USER

USER $USER:$GROUP

COPY --from=STACK --chown=$USER:$GROUP /home/$USER/.stack /home/$USER/.stack
COPY --from=MAVEN --chown=$USER:$GROUP /home/$USER/.m2 /home/$USER/.m2
