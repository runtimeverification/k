ARG BASE_OS
ARG BASE_DISTRO
ARG K_VERSION
FROM stack:${BASE_DISTRO}-${K_VERSION} as STACK

ARG BASE_OS
ARG BASE_DISTRO
ARG K_VERSION
FROM maven:${BASE_DISTRO}-${K_VERSION} as MAVEN

ARG BASE_OS
ARG BASE_DISTRO
FROM ${BASE_OS}:${BASE_DISTRO}

RUN    pacman -Sy   --noconfirm archlinux-keyring \
    && pacman -Syyu --noconfirm                   \
    && pacman -S    --noconfirm                   \
                       base                       \
                       base-devel                 \
                       boost                      \
                       clang                      \
                       cmake                      \
                       curl                       \
                       fmt                        \
                       git                        \
                       gmp                        \
                       hub                        \
                       jdk-openjdk                \
                       jemalloc                   \
                       libsecp256k1               \
                       libyaml                    \
                       lld                        \
                       llvm                       \
                       maven                      \
                       mpfr                       \
                       openssh                    \
                       python                     \
                       python-pip                 \
                       stack                      \
                       z3                         \
                       zlib

# The image is built specifically for an environment with this user/group
ARG USER=github-user
ARG GROUP=${USER}
ARG USER_ID=1000
ARG GROUP_ID=${USER_ID}
RUN groupadd -g $GROUP_ID ${GROUP} && useradd -m -u ${USER_ID} -s /bin/sh -g ${GROUP} ${USER}

USER ${USER_ID}:${GROUP_ID}

ENV PATH="${PATH}:/usr/bin/core_perl"

COPY --from=STACK --chown=$USER:$GROUP /home/$USER/.stack /home/$USER/.stack
COPY --from=MAVEN --chown=$USER:$GROUP /home/$USER/.m2 /home/$USER/.m2
