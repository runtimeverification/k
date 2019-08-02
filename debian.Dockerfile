ARG OS=ubuntu
ARG FLAVOR=bionic

FROM runtimeverificationinc/${OS}:${FLAVOR}

ARG OS=ubuntu
ARG FLAVOR=bionic

RUN apt-get update && \
    apt-get install -y \
      git debhelper maven openjdk-11-jdk cmake libboost-test-dev \
      libyaml-dev libjemalloc-dev flex bison \
      `[ "$OS:$FLAVOR" = "debian:buster" ] && echo clang-7 llvm-7-tools lld-7 || echo clang-8 llvm-8-tools lld-8` \
      zlib1g-dev libgmp-dev libmpfr-dev gcc z3 libz3-dev opam pkg-config curl python3

RUN curl -sSL https://get.haskellstack.org/ | sh

USER user:user

ADD llvm-backend/src/main/native/llvm-backend/install-rust llvm-backend/src/main/native/llvm-backend/rust-checksum /home/user/
RUN cd /home/user/ && ./install-rust

ADD k-distribution/src/main/scripts/bin/k-configure-opam-dev k-distribution/src/main/scripts/bin/k-configure-opam-common /home/user/.tmp-opam/bin/
ADD k-distribution/src/main/scripts/lib/opam  /home/user/.tmp-opam/lib/opam/
RUN    cd /home/user \
    && ./.tmp-opam/bin/k-configure-opam-dev

ADD --chown=user:user haskell-backend/src/main/native/haskell-backend/stack.yaml /home/user/.tmp-haskell/
ADD --chown=user:user haskell-backend/src/main/native/haskell-backend/kore/package.yaml /home/user/.tmp-haskell/kore/
RUN    cd /home/user/.tmp-haskell \
    && stack build --only-snapshot

ADD pom.xml /home/user/.tmp-maven/
ADD ktree/pom.xml /home/user/.tmp-maven/ktree/
ADD llvm-backend/pom.xml /home/user/.tmp-maven/llvm-backend/
ADD llvm-backend/src/main/native/llvm-backend/matching/pom.xml /home/user/.tmp-maven/llvm-backend/src/main/native/llvm-backend/matching/
ADD haskell-backend/pom.xml /home/user/.tmp-maven/haskell-backend/
ADD ocaml-backend/pom.xml /home/user/.tmp-maven/ocaml-backend/
ADD kernel/pom.xml /home/user/.tmp-maven/kernel/
ADD java-backend/pom.xml /home/user/.tmp-maven/java-backend/
ADD k-distribution/pom.xml /home/user/.tmp-maven/k-distribution/
ADD kore/pom.xml /home/user/.tmp-maven/kore/
RUN    cd /home/user/.tmp-maven \
    && mvn dependency:go-offline 
