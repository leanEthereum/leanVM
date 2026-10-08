#!/bin/bash
set -euo pipefail
repo_root=$(pwd)
mkdir -p /tmp/leanvm-profile-tools /tmp/leanvm-profiles /tmp/leanvm-profile-binaries
cd /tmp/leanvm-profile-tools
apt-get download google-perftools libgoogle-perftools4t64 libunwind8
for package in *.deb; do dpkg -x "$package" root; done
cd "$repo_root"
export RUSTFLAGS='-C target-cpu=native -C force-frame-pointers=yes'
export CARGO_NET_GIT_FETCH_WITH_CLI=true
profile_lib=/tmp/leanvm-profile-tools/root/usr/lib/aarch64-linux-gnu
profiler=/tmp/leanvm-profile-tools/root/usr/bin/google-pprof
for spec in 'before:a956c82ac711b2f4dbb3793ef2679fa47f3d6435' 'after:ee8267e6d1a939cf5c5789608a8cd27fd5ffd1d0'; do
 IFS=: read -r label revision <<< "$spec"
 git checkout -f "$revision"
 cargo build --release --locked -p leanvm-cli
 cp target/release/leanvm "/tmp/leanvm-profile-binaries/$label"
 LD_PRELOAD="$profile_lib/libprofiler.so.0" LD_LIBRARY_PATH="$profile_lib" CPUPROFILE="/tmp/leanvm-profiles/$label.prof" CPUPROFILE_FREQUENCY=1000 LEANVM_NUM_THREADS=1 "/tmp/leanvm-profile-binaries/$label" --cooldown 0 leanxmss --n 100 --repeat 1 --tracing > "/tmp/leanvm-profiles/$label-trace.log"
 LD_LIBRARY_PATH="$profile_lib" "$profiler" --text --no_strip_temp --focus='::prove$' "/tmp/leanvm-profile-binaries/$label" "/tmp/leanvm-profiles/$label.prof" > "/tmp/leanvm-profiles/$label-text.txt"
 LD_LIBRARY_PATH="$profile_lib" "$profiler" --callgrind --no_strip_temp --focus='::prove$' "/tmp/leanvm-profile-binaries/$label" "/tmp/leanvm-profiles/$label.prof" > "/tmp/leanvm-profiles/$label-callgrind.txt"
 printf '\nPROFILE %s\n' "$label"
 sed -n '1,65p' "/tmp/leanvm-profiles/$label-text.txt"
done
