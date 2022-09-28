ARG K_VERSION
ARG Z3_VERSION
FROM z3:${Z3_VERSION} as Z3

ARG K_VERSION
FROM stack:${K_VERSION} as STACK

ARG K_VERSION
FROM maven:${K_VERSION} as MAVEN

FROM ubuntu:jammy

COPY --from=Z3 /usr/bin/z3 /usr/bin/z3
COPY --from=STACK /usr/local/bin/stack /usr/local/bin/stack

ARG LLVM_VERSION=14

ENV TZ America/Chicago
ENV DEBIAN_FRONTEND=noninteractive

RUN    apt-get update            \
    && apt-get install --yes     \
        curl

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN groupadd -g $GROUP_ID user && useradd -m -u $USER_ID -s /bin/sh -g user user

USER user:user

COPY --from=STACK --chown=user:user /home/user/.stack /home/user/.stack
COPY --from=MAVEN --chown=user:user /home/user/.m2 /home/user/.m2

user root:root

ENV TZ America/Chicago
ENV DEBIAN_FRONTEND=noninteractive

RUN    apt-get update            \
    && apt-get install --yes     \
        maven

RUN apt-get install --yes git
RUN apt-get install --yes gcc
RUN apt-get install --yes lld-$LLVM_VERSION

#        bison                    \
#        build-essential          \
#        clang-$LLVM_VERSION      \
#        cmake                    \
#        curl                     \
#        debhelper                \
#        flex                     \
#        gcc                      \
#        libboost-test-dev        \
#        libbz2-dev               \
#        libffi-dev               \
#        libgdbm-dev              \
#        libgmp-dev               \
#        libjemalloc-dev          \
#        libmpfr-dev              \
#        libncurses5-dev          \
#        libnss3-dev              \
#        libreadline-dev          \
#        libsqlite3-dev           \
#        libssl-dev               \
#        libyaml-dev              \
#        libz3-dev                \
#        llvm-$LLVM_VERSION-tools \
#        openjdk-11-jdk           \
#        parallel                 \
#        pkg-config               \
#        python3                  \
#        python3-dev              \
#        python3-distutils        \
#        python3-pip              \
#        zlib1g-dev

USER user:user
