#!/bin/sh
# Generate ACT4's self-checking I and M tests for leanVM into elf/ (elf/I, elf/M; not
# checked in), which leanvm_core/tests/verifiers/act4/mod.rs loads. `generate.sh DIR` writes them to DIR
# instead. Needs Docker, and network access to build the image (Dockerfile) that
# pins every tool; ACT4_IMAGE names an image already built from it instead.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
out=${1:-$here/elf}
image=${ACT4_IMAGE:-}
if [ -z "$image" ]; then
  image=leanvm-act4
  docker build -t "$image" - <"$here/Dockerfile"
fi

mkdir -p "$out"
out=$(cd "$out" && pwd)
rm -rf "$out/I" "$out/M"
docker run --rm -v "$here:/config:ro" -v "$out:/out" -e OWNER="$(id -u):$(id -g)" "$image" sh /config/in-docker.sh
