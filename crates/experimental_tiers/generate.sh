#!/bin/sh
# Writes one copy of the experimental prover's crates per CPU tier: manifests over the same sources, which
# scripts/tier-rustc compiles with the tier's target features. experimental_dispatch's `tiers!` lists the same tiers.
set -eu
cd "$(dirname "$0")"

x86v3=+avx2,+bmi1,+bmi2,+fma,+lzcnt,+movbe,+f16c,+popcnt,+pclmulqdq
x86v4=$x86v3,+avx512f,+avx512bw,+avx512cd,+avx512dq,+avx512vl
tiers="
x86v3clmul $x86v3,+vpclmulqdq
x86v3gfni $x86v3,+vpclmulqdq,+gfni
x86v4 $x86v4
x86v4gfni $x86v4,+vpclmulqdq,+gfni,+avx512vbmi
armaes +aes
armsha3 +aes,+sha3
"
copied="keccak256 fiat_shamir_prover experimental_primitives experimental_pcs experimental_keccak_gkr experimental_lean_vm_core"

# A crate, its sources under crates/, and its dependencies as `alias=crate`, or `crate` for a workspace one.
crates="
keccak256 keccak256
fiat_shamir_prover fiat_shamir_prover verifier keccak256
experimental_primitives experimental_prover/primitives keccak256 parallel=experimental_parallel fiat_shamir_prover
experimental_pcs experimental_prover/pcs parallel=experimental_parallel primitives=experimental_primitives fiat_shamir=fiat_shamir_prover tracing verifier
experimental_keccak_gkr experimental_prover/keccak_gkr parallel=experimental_parallel primitives=experimental_primitives fiat_shamir=fiat_shamir_prover pcs=experimental_pcs tracing verifier
experimental_lean_vm_core experimental_prover/lean_vm_core isa parallel=experimental_parallel primitives=experimental_primitives fiat_shamir=fiat_shamir_prover pcs=experimental_pcs keccak_gkr=experimental_keccak_gkr verifier tracing
"

dependency() { # tier, alias, crate
    case " $copied " in
    *" $3 "*) echo "$2 = { package = \"$3_$1\", path = \"../$3\" }" ;;
    *)
        case "$3" in
        experimental_parallel) echo "$2 = { package = \"$3\", path = \"../../../experimental_prover/parallel\" }" ;;
        *) echo "$2.workspace = true" ;;
        esac
        ;;
    esac
}

find . -mindepth 1 -maxdepth 1 -type d -exec rm -r {} +
echo "$tiers" | while read -r tier features; do
    [ -n "$tier" ] || continue
    echo "$crates" | while read -r name src deps; do
        [ -n "$name" ] || continue
        mkdir -p "$tier/$name"
        {
            printf '# Written by ../../generate.sh.\n[package]\nname = "%s_%s"\n' "$name" "$tier"
            printf 'version.workspace = true\nedition.workspace = true\npublish = false\n'
            printf 'autobins = false\nautotests = false\nautobenches = false\nautoexamples = false\n\n'
            printf '[package.metadata.tier]\ntarget-features = "%s"\n\n' "$features"
            printf '[lib]\npath = "../../../%s/src/lib.rs"\ntest = false\ndoctest = false\nbench = false\ndoc = false\n\n' "$src"
            printf '[lints]\nworkspace = true\n'
            [ -z "$deps" ] || printf '\n[dependencies]\n'
            for dep in $deps; do
                dependency "$tier" "${dep%%=*}" "${dep#*=}"
            done
            # Features the sources gate code on, never enabled in a copy.
            case "$name" in
            experimental_primitives) printf '\n[features]\ntest-util = []\n' ;;
            experimental_keccak_gkr) printf '\n[features]\nbench = []\n' ;;
            esac
        } > "$tier/$name/Cargo.toml"
    done
done
