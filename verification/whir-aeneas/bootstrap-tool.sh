#!/usr/bin/env bash
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
opam="$here/.tools/opam-2.5.2"
source="$here/.tools/aeneas-source"
export OPAMROOT="$here/.tools/opam" OPAMJOBS=2
run_heavy() {
    flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 "$@"
}
if [[ ! -x "$opam" ]]; then
    mkdir -p "$here/.tools"
    curl -fL https://github.com/ocaml/opam/releases/download/2.5.2/opam-2.5.2-x86_64-linux -o "$opam"
    chmod +x "$opam"
fi
printf '%s  %s\n' edfca2630c373b44b7ee1c2f81cd8dcf67468d0db57d6c02158de553ac63dbd4 "$opam" | sha256sum -c -
if [[ ! -f "$OPAMROOT/config" ]]; then
    run_heavy "$opam" init --bare --no-setup --disable-sandboxing --yes
fi
if [[ ! -d "$OPAMROOT/aeneas-5.3" ]]; then
    run_heavy "$opam" switch create aeneas-5.3 --empty --yes
    run_heavy "$opam" switch import --switch=aeneas-5.3 --jobs=2 --yes "$here/toolchain/aeneas.opam.export"
fi
if [[ ! -d "$source/.git" ]]; then
    git clone --no-checkout https://github.com/AeneasVerif/aeneas "$source"
    git -C "$source" checkout --detach d119a474f852781f8ae88a85424f2f8ba8407b82
fi
[[ $(git -C "$source" rev-parse HEAD) == d119a474f852781f8ae88a85424f2f8ba8407b82 ]]
for patch in aeneas-parent-trait-fields.patch aeneas-unreferenced-impl-metadata.patch; do
    if ! git -C "$source" apply --reverse --check "$here/$patch" 2>/dev/null; then
        git -C "$source" apply --check "$here/$patch"
        git -C "$source" apply "$here/$patch"
    fi
done
if [[ ! -d "$source/charon/.git" ]]; then
    git clone --no-checkout https://github.com/AeneasVerif/charon "$source/charon"
    git -C "$source/charon" checkout --detach 798016509139eb51f0d764645f76d068d34ba5f6
fi
[[ $(git -C "$source/charon" rev-parse HEAD) == 798016509139eb51f0d764645f76d068d34ba5f6 ]]
cd "$source/src"
run_heavy "$opam" exec --switch=aeneas-5.3 -- dune build main.exe -j 2
"$source/src/_build/default/main.exe" -version
