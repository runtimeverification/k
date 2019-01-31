FROM ubuntu:bionic

RUN apt-get update
RUN apt-get install -y git debhelper maven openjdk-8-jdk cmake libboost-test-dev libyaml-cpp-dev libjemalloc-dev flex bison clang-6.0 zlib1g-dev libgmp-dev libmpfr-dev gcc z3 libz3-dev opam pkg-config curl
RUN update-alternatives --set java /usr/lib/jvm/java-8-openjdk-amd64/jre/bin/java
RUN curl -sSL https://get.haskellstack.org/ | sh      

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN groupadd -g $GROUP_ID user && \
    useradd -m -u $USER_ID -s /bin/sh -g user user

USER $USER_ID:$GROUP_ID
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain 1.28.0

RUN mkdir -p /home/user/.tmp-opam/lib && mkdir -p /home/user/.tmp-opam/bin
ADD k-distribution/src/main/scripts/bin/k-configure-opam-dev k-distribution/src/main/scripts/bin/k-configure-opam-common /home/user/.tmp-opam/bin/
ADD k-distribution/src/main/scripts/lib/opam  /home/user/.tmp-opam/lib/opam/
RUN    cd /home/user \
    && ./.tmp-opam/bin/k-configure-opam-dev
