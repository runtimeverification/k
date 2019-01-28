FROM ubuntu:bionic

ENV TZ=America/Chicago
RUN    ln --symbolic --no-dereference --force /usr/share/zoneinfo/$TZ /etc/localtime \
    && echo $TZ > /etc/timezone

RUN apt update && apt upgrade --yes

RUN apt-get install --yes \
            bison clang-6.0 cmake curl debhelper flex gcc git libboost-test-dev \
            libgmp-dev libjemalloc-dev libmpfr-dev libyaml-cpp-dev libz3-dev    \
            maven opam openjdk-8-jdk pkg-config z3 zlib1g-dev

RUN update-alternatives --set java /usr/lib/jvm/java-8-openjdk-amd64/jre/bin/java

RUN curl -sSL https://get.haskellstack.org/ | sh

RUN    git clone 'https://github.com/z3prover/z3' --branch=z3-4.8.4 \
    && cd z3                                                        \
    && python scripts/mk_make.py                                    \
    && cd build                                                     \
    && make -j8                                                     \
    && make install                                                 \
    && cd ../..                                                     \
    && rm -rf z3

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd --gid $GROUP_ID user                                        \
    && useradd --create-home --uid $USER_ID --shell /bin/sh --gid user user

USER $USER_ID:$GROUP_ID

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain 1.28.0

RUN    cd /home/user                                                          \
    && git clone 'https://github.com/kframework/k' --branch=nightly-0f3835d3a \
    && ./k/k-distribution/src/main/scripts/bin/k-configure-opam-dev           \
    && rm -rf k
