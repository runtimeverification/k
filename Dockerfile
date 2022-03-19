FROM ubuntu:bionic

RUN    apt-get update        \
    && apt-get install --yes \
        bison                \
        clang-10             \
        cmake                \
        curl                 \
        debhelper            \
        flex                 \
        gcc                  \
        git                  \
        libboost-test-dev    \
        libgmp-dev           \
        libjemalloc-dev      \
        libmpfr-dev          \
        libyaml-dev          \
        libz3-dev            \
        lld-10               \
        llvm-10-tools        \
        maven                \
        openjdk-11-jdk       \
        parallel             \
        pkg-config           \
        python               \
        python3              \
        python3-graphviz     \
        zlib1g-dev

RUN    git clone 'https://github.com/z3prover/z3' --branch=z3-4.8.11 \
    && cd z3                                                         \
    && python scripts/mk_make.py                                     \
    && cd build                                                      \
    && make -j8                                                      \
    && make install                                                  \
    && cd ../..                                                      \
    && rm -rf z3

RUN curl -sL https://deb.nodesource.com/setup_14.x | bash -
RUN    apt-get update               \
    && apt-get upgrade --yes        \
    && apt-get install --yes nodejs

RUN curl -sSL https://get.haskellstack.org/ | sh

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd -g $GROUP_ID user                     \
    && useradd -m -u $USER_ID -s /bin/sh -g user user

USER user:user

RUN curl -L https://github.com/github/hub/releases/download/v2.14.0/hub-linux-amd64-2.14.0.tgz -o /home/user/hub.tgz
RUN cd /home/user && tar xzf hub.tgz

ENV LD_LIBRARY_PATH=/usr/local/lib
ENV PATH=/home/user/hub-linux-amd64-2.14.0/bin:$PATH

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
ADD kernel/pom.xml                                             /home/user/.tmp-maven/kernel/
ADD java-backend/pom.xml                                       /home/user/.tmp-maven/java-backend/
ADD k-distribution/pom.xml                                     /home/user/.tmp-maven/k-distribution/
ADD kore/pom.xml                                               /home/user/.tmp-maven/kore/
RUN    cd /home/user/.tmp-maven               \
    && mvn --batch-mode dependency:go-offline

RUN    curl -L https://bootstrap.pypa.io/get-pip.py -o get-pip.py \
    && python3 get-pip.py                                         \
    && pip install --upgrade pip virtualenv

RUN    git config --global user.email 'admin@runtimeverification.com' \
    && git config --global user.name  'RV Jenkins'                    \
    && mkdir -p ~/.ssh                                                \
    && echo 'host github.com'                       > ~/.ssh/config   \
    && echo '    hostname github.com'              >> ~/.ssh/config   \
    && echo '    user git'                         >> ~/.ssh/config   \
    && echo '    identityagent SSH_AUTH_SOCK'      >> ~/.ssh/config   \
    && echo '    stricthostkeychecking accept-new' >> ~/.ssh/config   \
    && chmod go-rwx -R ~/.ssh
