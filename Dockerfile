ARG BASE_IMAGE=ubuntu:bionic
FROM ${BASE_IMAGE}
ARG BASE_IMAGE

RUN if [ "$BASE_IMAGE" = "debian:stretch" ]; then echo "Enabling backports..."; echo "deb http://ftp.debian.org/debian stretch-backports main" > /etc/apt/sources.list.d/stretch-backports.list; fi
RUN apt-get update
RUN apt-get install -y git debhelper maven openjdk-8-jdk cmake libboost-test-dev libyaml-cpp-dev libjemalloc-dev flex bison clang-6.0 zlib1g-dev libgmp-dev libmpfr-dev gcc z3 libz3-dev opam pkg-config curl
RUN update-alternatives --set java /usr/lib/jvm/java-8-openjdk-amd64/jre/bin/java
ENV JAVA_HOME=/usr/lib/jvm/java-8-openjdk-amd64/
RUN curl -sSL https://get.haskellstack.org/ | sh      

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN groupadd -g $GROUP_ID user && \
    useradd -m -u $USER_ID -s /bin/sh -g user user

USER $USER_ID:$GROUP_ID
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain 1.28.0

ADD k-distribution/src/main/scripts/bin/k-configure-opam-dev k-distribution/src/main/scripts/bin/k-configure-opam-common /home/user/.tmp-opam/bin/
ADD k-distribution/src/main/scripts/lib/opam  /home/user/.tmp-opam/lib/opam/
RUN    cd /home/user \
    && ./.tmp-opam/bin/k-configure-opam-dev

ENV LC_ALL=C.UTF-8
ADD --chown=user:user haskell-backend/src/main/native/haskell-backend/stack.yaml /home/user/.tmp-haskell/
ADD --chown=user:user haskell-backend/src/main/native/haskell-backend/kore/package.yaml /home/user/.tmp-haskell/kore/
RUN    cd /home/user/.tmp-haskell \
    && stack build --only-snapshot --test --bench --haddock --library-profiling

ADD --chown=user:user llvm-backend/src/main/native/llvm-backend/matching/stack.yaml /home/user/.tmp-haskell2/
ADD --chown=user:user llvm-backend/src/main/native/llvm-backend/matching/package.yaml /home/user/.tmp-haskell2/
ADD --chown=user:user llvm-backend/src/main/native/llvm-backend/matching/submodules/kore/stack.yaml /home/user/.tmp-haskell2/submodules/kore/
ADD --chown=user:user llvm-backend/src/main/native/llvm-backend/matching/submodules/kore/src/main/haskell/kore/package.yaml /home/user/.tmp-haskell2/submodules/kore/src/main/haskell/kore/
RUN    cd /home/user/.tmp-haskell2 \
    && stack build --only-snapshot --test

ADD pom.xml /home/user/.tmp-maven/
ADD ktree/pom.xml /home/user/.tmp-maven/ktree/
ADD llvm-backend/pom.xml /home/user/.tmp-maven/llvm-backend/
ADD haskell-backend/pom.xml /home/user/.tmp-maven/haskell-backend/
ADD ocaml-backend/pom.xml /home/user/.tmp-maven/ocaml-backend/
ADD kernel/pom.xml /home/user/.tmp-maven/kernel/
ADD java-backend/pom.xml /home/user/.tmp-maven/java-backend/
ADD k-distribution/pom.xml /home/user/.tmp-maven/k-distribution/
ADD kore/pom.xml /home/user/.tmp-maven/kore/
RUN    cd /home/user/.tmp-maven \
    && mvn dependency:go-offline 
