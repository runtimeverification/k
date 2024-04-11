ARG K_DISTRO=jammy
ARG K_VERSION

FROM runtimeverificationinc/kframework-k:ubuntu-${K_DISTRO}-${K_VERSION}

ARG K_VERSION
ARG PYK_VERSION

# create non-root user and adjust UID:GID on start-up
# see https://github.com/boxboat/fixuid
RUN addgroup --gid 1000 k-group && \
    adduser -uid 1000 --ingroup k-group --home /home/k-user --shell /bin/sh --disabled-password --gecos "" k-user
RUN apt install -y curl graphviz && \
    USER=k-user && \
    GROUP=k-group && \
    curl -SsL https://github.com/boxboat/fixuid/releases/download/v0.6.0/fixuid-0.6.0-linux-amd64.tar.gz | tar -C /usr/local/bin -xzf - && \
    chown root:root /usr/local/bin/fixuid && \
    chmod 4755 /usr/local/bin/fixuid && \
    mkdir -p /etc/fixuid && \
    printf "user: $USER\ngroup: $GROUP\n" > /etc/fixuid/config.yml
USER k-user:k-group
WORKDIR /home/k-user

# remember K and pyk versions in environment
ENV K_VERSION=${K_VERSION} \
    PYK_VERSION=${PYK_VERSION} \
    PATH=/home/k-user/.local/bin:$PATH \
    force_color_prompt=yes

# install poetry and pyk
COPY --chown=1000:1000 LICENSE.md Makefile README.md deps docs poetry.lock pyproject.toml src pyk-${PYK_VERSION}/
RUN pip install poetry && \
    cd pyk-${PYK_VERSION} && \
    make build && \
    pip install dist/*.whl && \
    make clean


ENTRYPOINT ["fixuid", "-q"]

CMD printf "%s\n" \
    "Welcome to the K Framework" \
    "" \
    "This Docker image provides a K Framework installation with the following programs:" \
    " * kompile" \
    " * krun" \
    " * kprove" \
    " * kast" \
    " * K backend tools (kore-*)" \
    "" \
    "as well as a pre-installed pyk library to interact with K programmatically." \
    "" \
    "To use this Docker image, start a container with an interactive shell and" \
    "a working directory with your K definition mounted into it, like so:" \
    "" \
    'user@host$ docker run --rm -it -v "$PWD":/home/k-user/workspace -u $(id -u):$(id -g) <docker-image> /bin/bash' \
    ""
