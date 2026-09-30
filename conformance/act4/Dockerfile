# The environment that generates the ACT4 ELF files (generate.sh builds and runs it):
# riscv-arch-test, its RISC-V GCC, the Sail reference model and the tools of its
# framework, every one pinned by version and checksum. The configuration is mounted
# at run time, so a change to it does not rebuild the image.
FROM ubuntu:24.04@sha256:008173c23f95b170204355c12626cb5a965d779a7e1283b09e9cffbb1bf33ca3

ARG DEBIAN_FRONTEND=noninteractive
# build-essential builds the native gems of the unified database (UDB).
RUN apt-get update && apt-get install -y --no-install-recommends \
        build-essential ca-certificates curl git xz-utils \
    && rm -rf /var/lib/apt/lists/*

# GCC 15.1 and binutils 2.45: ACT4 4.1.0 needs GCC 15 or later.
ARG TOOLCHAIN=2025.08.08
ARG TOOLCHAIN_SHA256=2aaa09d5eb768d4874b85cba152b994f49605b13035fc8d6a71f14c51db5276e
RUN curl -fsSL -o /tmp/toolchain.tar.xz \
        "https://github.com/riscv-collab/riscv-gnu-toolchain/releases/download/${TOOLCHAIN}/riscv64-elf-ubuntu-24.04-gcc-nightly-${TOOLCHAIN}-nightly.tar.xz" \
    && echo "${TOOLCHAIN_SHA256}  /tmp/toolchain.tar.xz" | sha256sum -c - \
    && tar -xJf /tmp/toolchain.tar.xz -C /opt \
    && rm /tmp/toolchain.tar.xz

# ACT4 4.1.0 requires exactly Sail 0.13.1.
ARG SAIL=0.13.1
ARG SAIL_SHA256=ee052f64494a2f5f071afd9c2cb4aa5eaae4ba84753e4f77e442b4f83f2e9469
RUN curl -fsSL -o /tmp/sail.tar.gz \
        "https://github.com/riscv/sail-riscv/releases/download/${SAIL}/sail-riscv-Linux-x86_64.tar.gz" \
    && echo "${SAIL_SHA256}  /tmp/sail.tar.gz" | sha256sum -c - \
    && mkdir /opt/sail \
    && tar -xzf /tmp/sail.tar.gz -C /opt/sail --strip-components=1 \
    && rm /tmp/sail.tar.gz

# mise installs the uv, Ruby and Bundler versions riscv-arch-test's .mise.toml pins.
ARG MISE=2026.9.17
ARG MISE_SHA256=63049bc35fb9065e8dc35ac8b25fdae53e9bd6f1885a843aedeba398e046a1ee
RUN curl -fsSL -o /usr/local/bin/mise \
        "https://github.com/jdx/mise/releases/download/v${MISE}/mise-v${MISE}-linux-x64" \
    && echo "${MISE_SHA256}  /usr/local/bin/mise" | sha256sum -c - \
    && chmod +x /usr/local/bin/mise

ENV PATH="/opt/riscv/bin:/opt/sail/bin:/root/.local/share/mise/shims:${PATH}" \
    MISE_YES=1

# riscv-arch-test 4.1.0, and its Ruby and Python dependencies (locked by its
# Gemfile.lock and uv.lock), so that generating needs no network.
ARG ARCH_TEST=6e8a45123f14cebfb3df151a0e7b849b4389b33b
WORKDIR /act4
RUN git init -q . \
    && git fetch -q --depth 1 https://github.com/riscv/riscv-arch-test.git "${ARCH_TEST}" \
    && git checkout -q FETCH_HEAD \
    && mise trust \
    && mise install ruby gem:bundler uv \
    && BUNDLE_GEMFILE=/act4/framework/src/act/data/Gemfile bundle install \
    && uv sync --frozen \
    && riscv64-unknown-elf-gcc --version && sail_riscv_sim --version
