ARG BASE_IMAGE=ubuntu:bionic
FROM ${BASE_IMAGE}
ARG BASE_IMAGE

ARG LLVM_VERSION=10

ENV TZ America/Chicago
ENV DEBIAN_FRONTEND=noninteractive

# RUN if [ "$BASE_IMAGE" = "debian:bullseye" ]; then echo "Enabling backports..."; echo "deb http://deb.debian.org/debian bullseye-backports main" > /etc/apt/sources.list.d/bullseye-backports.list; fi
RUN    apt-get update            \
    && apt-get install --yes     \
        bison                    \
        clang-$LLVM_VERSION      \
        cmake                    \
        curl                     \
        debhelper                \
        flex                     \
        gcc                      \
        git                      \
        libboost-test-dev        \
        libgmp-dev               \
        libjemalloc-dev          \
        libmpfr-dev              \
        libyaml-dev              \
        libz3-dev                \
        lld-$LLVM_VERSION        \
        llvm-$LLVM_VERSION-tools \
        maven                    \
        opam                     \
        openjdk-11-jdk           \
        parallel                 \
        pkg-config               \
        python3                  \
        python3-graphviz         \
        zlib1g-dev

RUN curl -sSL https://get.haskellstack.org/ | sh

RUN    git clone 'https://github.com/z3prover/z3' --branch=z3-4.8.12 \
    && cd z3                                                         \
    && python scripts/mk_make.py                                     \
    && cd build                                                      \
    && make -j8                                                      \
    && make install                                                  \
    && cd ../..                                                      \
    && rm -rf z3

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd -g $GROUP_ID user                     \
    && useradd -m -u $USER_ID -s /bin/sh -g user user

USER $USER_ID:$GROUP_ID

ADD k-distribution/src/main/scripts/bin/k-configure-opam-dev k-distribution/src/main/scripts/bin/k-configure-opam-common /home/user/.tmp-opam/bin/
ADD k-distribution/src/main/scripts/lib/opam                                                                             /home/user/.tmp-opam/lib/kframework/opam/
RUN    cd /home/user                        \
    && ./.tmp-opam/bin/k-configure-opam-dev

ENV LC_ALL=C.UTF-8
ADD --chown=user:user haskell-backend/src/main/native/haskell-backend/stack.yaml        /home/user/.tmp-haskell/
ADD --chown=user:user haskell-backend/src/main/native/haskell-backend/kore/kore.cabal /home/user/.tmp-haskell/kore/
RUN    cd /home/user/.tmp-haskell  \
    && stack build --only-snapshot

ADD pom.xml                                                    /home/user/.tmp-maven/
ADD ktree/pom.xml                                              /home/user/.tmp-maven/ktree/
ADD llvm-backend/pom.xml                                       /home/user/.tmp-maven/llvm-backend/
ADD llvm-backend/src/main/native/llvm-backend/matching/pom.xml /home/user/.tmp-maven/llvm-backend/src/main/native/llvm-backend/matching/
ADD haskell-backend/pom.xml                                    /home/user/.tmp-maven/haskell-backend/
ADD ocaml-backend/pom.xml                                      /home/user/.tmp-maven/ocaml-backend/
ADD kernel/pom.xml                                             /home/user/.tmp-maven/kernel/
ADD java-backend/pom.xml                                       /home/user/.tmp-maven/java-backend/
ADD k-distribution/pom.xml                                     /home/user/.tmp-maven/k-distribution/
ADD kore/pom.xml                                               /home/user/.tmp-maven/kore/
RUN    cd /home/user/.tmp-maven               \
    && mvn --batch-mode dependency:go-offline
