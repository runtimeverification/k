ARG BASE_DISTRO
ARG BASE_OS
FROM ${BASE_OS}:${BASE_DISTRO}

RUN    pacman -Sy   --noconfirm archlinux-keyring \
    && pacman -Syyu --noconfirm                   \
    && pacman -S    --noconfirm                   \
                       z3
