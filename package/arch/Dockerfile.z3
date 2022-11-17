ARG BASE_DISTRO
ARG BASE_OS
FROM ${BASE_OS}:${BASE_DISTRO}

ENV TZ=America/Chicago
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone

ARG BASE_OS
ARG BASE_DISTRO
FROM ${BASE_OS}:${BASE_DISTRO}

RUN    pacman -Sy   --noconfirm archlinux-keyring \
    && pacman -Syyu --noconfirm                   \
    && pacman -S    --noconfirm                   \
                       z3
