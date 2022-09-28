ARG Z3_VERSION
FROM z3:${Z3_VERSION} as Z3

FROM ubuntu:jammy

COPY --from=Z3 /usr/bin/z3 /usr/bin/z3

ARG LLVM_VERSION=14

ENV TZ America/Chicago
ENV DEBIAN_FRONTEND=noninteractive

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
        libbz2-dev               \
        libffi-dev               \
        libgdbm-dev              \
        libgmp-dev               \
        libjemalloc-dev          \
        libmpfr-dev              \
        libncurses5-dev          \
        libnss3-dev              \
        libreadline-dev          \
        libsqlite3-dev           \
        libssl-dev               \
        libyaml-dev              \
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

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN groupadd -g $GROUP_ID user && useradd -m -u $USER_ID -s /bin/sh -g user user

USER user:user

ENV LC_ALL=C.UTF-8
ADD --chown=user:user haskell-backend/src/main/native/haskell-backend/stack.yaml      /home/user/.tmp-haskell/
ADD --chown=user:user haskell-backend/src/main/native/haskell-backend/kore/kore.cabal /home/user/.tmp-haskell/kore/
RUN cd /home/user/.tmp-haskell && stack build --only-snapshot

ADD pom.xml                                                    /home/user/.tmp-maven/
ADD ktree/pom.xml                                              /home/user/.tmp-maven/ktree/
ADD llvm-backend/pom.xml                                       /home/user/.tmp-maven/llvm-backend/
ADD llvm-backend/src/main/native/llvm-backend/matching/pom.xml /home/user/.tmp-maven/llvm-backend/src/main/native/llvm-backend/matching/
ADD haskell-backend/pom.xml                                    /home/user/.tmp-maven/haskell-backend/
ADD kernel/pom.xml                                             /home/user/.tmp-maven/kernel/
ADD java-backend/pom.xml                                       /home/user/.tmp-maven/java-backend/
ADD k-distribution/pom.xml                                     /home/user/.tmp-maven/k-distribution/
ADD kore/pom.xml                                               /home/user/.tmp-maven/kore/
RUN cd /home/user/.tmp-maven && mvn --batch-mode dependency:go-offline
