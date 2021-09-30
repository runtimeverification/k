FROM archlinux:base

RUN    pacman -Sy   --noconfirm archlinux-keyring \
    && pacman -Syyu --noconfirm                   \
    && pacman -S    --noconfirm                   \
                       base                       \
                       base-devel                 \
                       boost                      \
                       clang                      \
                       cmake                      \
                       curl                       \
                       git                        \
                       gmp                        \
                       hub                        \
                       jdk-openjdk                \
                       jemalloc                   \
                       libunwind                  \
                       libyaml                    \
                       lld                        \
                       llvm                       \
                       maven                      \
                       mpfr                       \
                       opam                       \
                       openssh                    \
                       python                     \
                       python-pip                 \
                       stack                      \
                       z3                         \
                       zlib

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd -g $GROUP_ID user                     \
    && useradd -m -u $USER_ID -s /bin/sh -g user user

USER $USER_ID:$GROUP_ID

ENV PATH="${PATH}:/usr/bin/core_perl"

ADD k-distribution/src/main/scripts/bin/k-configure-opam-dev k-distribution/src/main/scripts/bin/k-configure-opam-common /home/user/.tmp-opam/bin/
ADD k-distribution/src/main/scripts/lib/opam                                                                             /home/user/.tmp-opam/lib/kframework/opam/
RUN    cd /home/user                        \
    && ./.tmp-opam/bin/k-configure-opam-dev

ADD --chown=user:user haskell-backend/src/main/native/haskell-backend/stack.yaml        /home/user/.tmp-haskell/
ADD --chown=user:user haskell-backend/src/main/native/haskell-backend/kore/kore.cabal /home/user/.tmp-haskell/kore/
RUN    cd /home/user/.tmp-haskell \
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

RUN pip3 install --user graphviz
