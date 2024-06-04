ARG BASE_OS
ARG BASE_DISTRO

FROM ${BASE_OS}:${BASE_DISTRO}

ARG K_DEB_PATH
ARG LLVM_BACKEND_DEB_PATH

COPY ${K_DEB_PATH} /kframework.deb
COPY ${LLVM_BACKEND_DEB_PATH} /llvm-backend.deb

RUN    apt-get -y update    \
    && apt-get -y install   \
         curl               \
         graphviz           \
         make               \
         python3.10-dev     \
         /llvm-backend.deb  \
         /kframework.deb    \
    && apt-get -y clean

RUN rm /llvm-backend.deb
RUN rm /kframework.deb

ARG USER_ID=9876
ARG GROUP_ID=9876
RUN    groupadd -g ${GROUP_ID} user                     \
    && useradd -m -u ${USER_ID} -s /bin/sh -g user user

USER user
WORKDIR /home/user

ENV PATH=/home/user/.local/bin:${PATH}
RUN    curl -sSL https://install.python-poetry.org | python3 - \
    && poetry --version
