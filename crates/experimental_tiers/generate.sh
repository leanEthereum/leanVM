#!/bin/sh
# Writes one copy of the experimental prover's crates per CPU tier: manifests over the same sources, which
# scripts/tier-rustc compiles with the tier's target features. experimental_dispatch's TIERS lists the same features.
set -eu
cd "$(dirname "$0")"
X86V3=+avx2,+bmi1,+bmi2,+fma,+lzcnt,+movbe,+f16c,+popcnt,+pclmulqdq
X86V4=$X86V3,+avx512f,+avx512bw,+avx512cd,+avx512dq,+avx512vl
tiers="
x86v3 $X86V3
x86v3clmul $X86V3,+vpclmulqdq
x86v3gfni $X86V3,+vpclmulqdq,+gfni
x86v4 $X86V4
x86v4gfni $X86V4,+vpclmulqdq,+gfni,+avx512vbmi
armaes +aes
armsha3 +aes,+sha3
"
# crate, its source, its dependencies on the other copies or on shared crates.
crates="
keccak256|keccak256|
fiat_shamir_prover|fiat_shamir_prover|verifier.workspace = true;keccak256 = { package = \"keccak256_TIER\", path = \"../keccak256\" }
experimental_primitives|experimental_prover/primitives|keccak256 = { package = \"keccak256_TIER\", path = \"../keccak256\" };parallel = { package = \"experimental_parallel\", path = \"../../../experimental_prover/parallel\" };fiat_shamir_prover = { package = \"fiat_shamir_prover_TIER\", path = \"../fiat_shamir_prover\" }
experimental_pcs|experimental_prover/pcs|parallel = { package = \"experimental_parallel\", path = \"../../../experimental_prover/parallel\" };primitives = { package = \"experimental_primitives_TIER\", path = \"../experimental_primitives\" };fiat_shamir = { package = \"fiat_shamir_prover_TIER\", path = \"../fiat_shamir_prover\" };tracing.workspace = true;verifier.workspace = true
experimental_keccak_gkr|experimental_prover/keccak_gkr|parallel = { package = \"experimental_parallel\", path = \"../../../experimental_prover/parallel\" };primitives = { package = \"experimental_primitives_TIER\", path = \"../experimental_primitives\" };fiat_shamir = { package = \"fiat_shamir_prover_TIER\", path = \"../fiat_shamir_prover\" };pcs = { package = \"experimental_pcs_TIER\", path = \"../experimental_pcs\" };tracing.workspace = true;verifier.workspace = true
experimental_lean_vm_core|experimental_prover/lean_vm_core|isa.workspace = true;parallel = { package = \"experimental_parallel\", path = \"../../../experimental_prover/parallel\" };primitives = { package = \"experimental_primitives_TIER\", path = \"../experimental_primitives\" };fiat_shamir = { package = \"fiat_shamir_prover_TIER\", path = \"../fiat_shamir_prover\" };pcs = { package = \"experimental_pcs_TIER\", path = \"../experimental_pcs\" };keccak_gkr = { package = \"experimental_keccak_gkr_TIER\", path = \"../experimental_keccak_gkr\" };verifier.workspace = true;tracing.workspace = true
"
find . -mindepth 1 -maxdepth 1 -type d -exec rm -rf {} +
echo "$tiers" | while read -r tier features; do
    [ -n "$tier" ] || continue
    echo "$crates" | while IFS='|' read -r name src deps; do
        [ -n "$name" ] || continue
        mkdir -p "$tier/$name"
        {
            printf '# Written by ../../generate.sh.\n[package]\nname = "%s_%s"\n' "$name" "$tier"
            printf 'version.workspace = true\nedition.workspace = true\npublish = false\n'
            printf 'autobins = false\nautotests = false\nautobenches = false\nautoexamples = false\n\n'
            printf '[package.metadata.tier]\ntarget-features = "%s"\n\n' "$features"
            printf '[lib]\npath = "../../../%s/src/lib.rs"\ntest = false\ndoctest = false\nbench = false\ndoc = false\n\n' "$src"
            printf '[lints]\nworkspace = true\n'
            if [ -n "$deps" ]; then
                printf '\n[dependencies]\n'
                echo "$deps" | tr ';' '\n' | sed "s/TIER/$tier/g"
            fi
            # Features the sources gate code on, never enabled here.
            case "$name" in
            experimental_primitives) printf '\n[features]\ntest-util = []\n' ;;
            experimental_keccak_gkr) printf '\n[features]\nbench = []\n' ;;
            esac
        } > "$tier/$name/Cargo.toml"
    done
done
