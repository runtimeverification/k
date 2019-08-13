ARG OS=ubuntu
ARG FLAVOR=bionic

FROM runtimeverificationinc/kframework:${OS}-${FLAVOR}

RUN    apt-get update -q \
    && apt-get install -y z3 libz3-dev

USER user:user

# Copy rust's .cargo, .rustup, and build-in-source directories.
COPY --chown=user:user \
     --from=runtimeverificationinc/rust:1.34.0-llvm-8-ubuntu-bionic \
     /root/.cargo \
     /home/user/.cargo

COPY --chown=user:user \
     --from=runtimeverificationinc/rust:1.34.0-llvm-8-ubuntu-bionic \
     /root/.rustup \
     /home/user/.rustup

COPY --chown=user:user \
     --from=runtimeverificationinc/rust:1.34.0-llvm-8-ubuntu-bionic \
     /rustc-1.34.0-src \
     /home/user/rustc-1.34.0-src

# Use rustup.
RUN    cd /home/user/rustc-1.34.0-src \
    && /home/user/.cargo/bin/rustup \
         toolchain \
         link \
         rust-1.34.0-llvm-8 \
         build/x86_64-unknown-linux-gnu/stage2


# Copy OCaml.
COPY --chown=user:user \
     --from=runtimeverificationinc/ocaml:ubuntu-bionic \
     /home/user/.opam \
     /home/user/.opam

# Copy haskell.
COPY --from=runtimeverificationinc/haskell:ubuntu-bionic \
     --chown=user:user \
     /home/user/.stack \
     /home/user/.stack

COPY --from=runtimeverificationinc/haskell:ubuntu-bionic \
     --chown=user:user \
     /usr/local/bin/stack \
     /usr/local/bin/stack

# K submodules and other dependencies.
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
