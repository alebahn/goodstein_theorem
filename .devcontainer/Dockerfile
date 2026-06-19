FROM ghcr.io/alebahn/idris-2-docker/devcontainer:v0.7.0

USER root

RUN apt-get update && apt-get install -y --no-install-recommends \
    bash-completion \
    build-essential \
    bubblewrap \
    ca-certificates \
    cmake \
    curl \
    git \
    gettext \
    ninja-build \
    stow \
    sudo \
    unzip \
    xz-utils \
    && rm -rf /var/lib/apt/lists/*

# Node 22 for Codex
RUN curl -fsSL https://deb.nodesource.com/setup_22.x | bash - \
    && apt-get update \
    && apt-get install -y --no-install-recommends nodejs \
    && rm -rf /var/lib/apt/lists/*

# Newer Neovim, built against this image's libc.
RUN git clone --branch stable --depth 1 https://github.com/neovim/neovim.git /tmp/neovim \
    && make -C /tmp/neovim CMAKE_BUILD_TYPE=RelWithDebInfo CMAKE_INSTALL_PREFIX=/usr/local \
    && make -C /tmp/neovim install \
    && rm -rf /tmp/neovim

RUN npm install -g @openai/codex

# Match Android/host: 1000:100
RUN usermod -g users vscode \
    && chgrp -R users /home/vscode \
    && find /home/vscode -type d -exec chmod g+s {} +

USER vscode

WORKDIR /workspace

CMD ["/bin/bash"]
