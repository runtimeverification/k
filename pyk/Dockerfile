ARG K_DISTRO=focal
ARG K_VERSION
FROM runtimeverificationinc/kframework-k:ubuntu-${K_DISTRO}-${K_VERSION}

RUN    apt-get update     \
    && apt-get install -y \
         curl

RUN    curl -sSL https://install.python-poetry.org | POETRY_HOME=/usr python3 - \
    && poetry --version

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd -g $GROUP_ID user                     \
    && useradd -m -u $USER_ID -s /bin/sh -g user user
WORKDIR /home/user
