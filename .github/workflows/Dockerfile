ARG BASE_IMAGE=ubuntu:jammy
FROM ${BASE_IMAGE}
ARG BASE_IMAGE

ARG LLVM_VERSION=14

ENV TZ America/Chicago
ENV DEBIAN_FRONTEND=noninteractive

# RUN if [ "$BASE_IMAGE" = "debian:bullseye" ]; then echo "Enabling backports..."; echo "deb http://deb.debian.org/debian bullseye-backports main" > /etc/apt/sources.list.d/bullseye-backports.list; fi
RUN    apt-get update            \
    && apt-get install --yes     \
        bison                    \
        build-essential          \
        clang-$LLVM_VERSION      \
        cmake                    \
        curl                     \
        debhelper                \
        flex                     \
        gcc                      \
        git                      \
        libboost-test-dev        \
        libgdbm-dev              \
        libgmp-dev               \
        libjemalloc-dev          \
        libffi-dev               \
        libmpfr-dev              \
        libncurses5-dev          \
        libnss3-dev              \
        libreadline-dev          \
        libsqlite3-dev           \
        libssl-dev               \
        libyaml-dev              \
        libbz2-dev               \
        libz3-dev                \
        lld-$LLVM_VERSION        \
        llvm-$LLVM_VERSION-tools \
        maven                    \
        openjdk-11-jdk           \
        parallel                 \
        pkg-config               \
        python3                  \
        python3-dev              \
        python3-distutils        \
        python3-pip              \
        zlib1g-dev

RUN curl -sSL https://get.haskellstack.org/ | sh

RUN    git clone 'https://github.com/z3prover/z3' --branch=z3-4.8.15 \
    && cd z3                                                         \
    && python3 scripts/mk_make.py                                    \
    && cd build                                                      \
    && make -j8                                                      \
    && make install                                                  \
    && cd ../..                                                      \
    && rm -rf z3

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd -g $GROUP_ID user                     \
    && useradd -m -u $USER_ID -s /bin/sh -g user user

USER user:user
WORKDIR /home/user

ENV LC_ALL=C.UTF-8
ADD --chown=user:user haskell-backend/src/main/native/haskell-backend/stack.yaml      .tmp-haskell/
ADD --chown=user:user haskell-backend/src/main/native/haskell-backend/kore/kore.cabal .tmp-haskell/kore/
RUN cd .tmp-haskell && stack build --only-snapshot

ADD pom.xml                                                    .tmp-maven/
ADD ktree/pom.xml                                              .tmp-maven/ktree/
ADD llvm-backend/pom.xml                                       .tmp-maven/llvm-backend/
ADD llvm-backend/src/main/native/llvm-backend/matching/pom.xml .tmp-maven/llvm-backend/src/main/native/llvm-backend/matching/
ADD haskell-backend/pom.xml                                    .tmp-maven/haskell-backend/
ADD kernel/pom.xml                                             .tmp-maven/kernel/
ADD java-backend/pom.xml                                       .tmp-maven/java-backend/
ADD k-distribution/pom.xml                                     .tmp-maven/k-distribution/
ADD kore/pom.xml                                               .tmp-maven/kore/
RUN    cd .tmp-maven                          \
    && mvn --batch-mode dependency:go-offline
