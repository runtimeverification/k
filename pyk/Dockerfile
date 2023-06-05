ARG K_DISTRO=jammy
ARG K_VERSION
FROM runtimeverificationinc/kframework-k:ubuntu-${K_DISTRO}-${K_VERSION}

ARG PYTHON_VERSION=3.10

RUN    apt-get -y update             \
    && apt-get -y install            \
         curl                        \
         graphviz                    \
         python${PYTHON_VERSION}     \
         python${PYTHON_VERSION}-dev \
    && apt-get -y clean

RUN    curl -sSL https://install.python-poetry.org | POETRY_HOME=/usr python3 - \
    && poetry --version

ARG USER_ID=9876
ARG GROUP_ID=9876
RUN    groupadd -g $GROUP_ID user                     \
    && useradd -m -u $USER_ID -s /bin/sh -g user user
