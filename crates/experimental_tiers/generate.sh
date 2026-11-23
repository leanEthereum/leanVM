#!/bin/sh
# Writes the CPU tiers: per tier, a copy of the experimental prover's crates over the same sources, which
# scripts/tier-rustc compiles with the tier's target features, and experimental_dispatch's manifest and tiers.rs,
# behind its `cpu_tiers` feature.
set -eu
cd "$(dirname "$0")"

x86v3=+avx2,+bmi1,+bmi2,+fma,+lzcnt,+movbe,+f16c,+popcnt,+pclmulqdq
x86v4=$x86v3,+avx512f,+avx512bw,+avx512cd,+avx512dq,+avx512vl
# Fastest first: dispatch takes the first the CPU runs.
tiers="
x86v4gfni x86_64 $x86v4,+vpclmulqdq,+gfni,+avx512vbmi
x86v3gfni x86_64 $x86v3,+vpclmulqdq,+gfni
x86v3clmul x86_64 $x86v3,+vpclmulqdq
x86v4 x86_64 $x86v4
armsha3 aarch64 +aes,+sha3
armaes aarch64 +aes
"
# A copied crate, its sources under crates/, and its dependencies as `alias=crate`, or `crate`.
crates="
keccak256 keccak256
fiat_shamir_prover fiat_shamir_prover verifier keccak256
experimental_primitives experimental_prover/primitives keccak256 parallel=experimental_parallel fiat_shamir_prover
experimental_pcs experimental_prover/pcs parallel=experimental_parallel primitives=experimental_primitives fiat_shamir=fiat_shamir_prover tracing verifier
experimental_keccak_gkr experimental_prover/keccak_gkr parallel=experimental_parallel primitives=experimental_primitives fiat_shamir=fiat_shamir_prover pcs=experimental_pcs tracing verifier
experimental_lean_vm_core experimental_prover/lean_vm_core isa parallel=experimental_parallel primitives=experimental_primitives fiat_shamir=fiat_shamir_prover pcs=experimental_pcs keccak_gkr=experimental_keccak_gkr verifier tracing
"
copied=$(echo "$crates" | cut -d' ' -f1)
# The copies sit outside the workspace, so they take its settings literally.
workspace() { sed -n "s/^$1 = \"\(.*\)\"$/\1/p" ../../Cargo.toml | head -n 1; }

dependency() { # tier, alias, crate
    case "$3" in
    experimental_parallel) echo "$2 = { package = \"$3\", path = \"../../../experimental_prover/parallel\" }" ;;
    tracing) echo "$2 = \"$(workspace tracing)\"" ;;
    *)
        if echo "$copied" | grep -qx "$3"; then
            echo "$2 = { package = \"$3_$1\", path = \"../$3\" }"
        else
            echo "$2 = { path = \"../../../$3\" }"
        fi
        ;;
    esac
}

# A build on the architecture that lacks some of the tier's features.
lacking() { # arch, features
    echo "target_arch = \"$1\", not(all($(echo "$2" | sed 's/+\([a-z0-9_.]*\)/target_feature = "\1"/g; s/,/, /g')))"
}

find . -mindepth 1 -maxdepth 1 -type d -exec rm -r {} +
dispatch=../experimental_dispatch
{
    printf '# Written by ../experimental_tiers/generate.sh.\n[package]\nname = "experimental_dispatch"\n'
    printf 'version.workspace = true\nedition.workspace = true\npublish = false\n\n[lints]\nworkspace = true\n\n'
    printf '[dependencies]\nisa.workspace = true\nverifier.workspace = true\n'
    printf 'base = { package = "experimental_lean_vm_core", path = "../experimental_prover/lean_vm_core" }\n'
} > "$dispatch/Cargo.toml"
printf '// Written by ../../experimental_tiers/generate.sh.\ntiers! {\n' > "$dispatch/src/tiers.rs"
echo "$tiers" | while read -r tier arch features; do
    [ -n "$tier" ] || continue
    echo "$crates" | while read -r name src deps; do
        [ -n "$name" ] || continue
        mkdir -p "$tier/$name"
        {
            printf '# Written by ../../generate.sh.\n[package]\nname = "%s_%s"\n' "$name" "$tier"
            printf 'version = "%s"\nedition = "%s"\npublish = false\n' "$(workspace version)" "$(workspace edition)"
            printf 'autobins = false\nautotests = false\nautobenches = false\nautoexamples = false\n\n'
            printf '[package.metadata.tier]\ntarget-features = "%s"\n\n' "$features"
            printf '[lib]\npath = "../../../%s/src/lib.rs"\ntest = false\ndoctest = false\nbench = false\ndoc = false\n\n' "$src"
            printf '[lints.rust]\nunexpected_cfgs = { level = "warn", check-cfg = ["cfg(leanvm_tier)"] }\n'
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
        # Cargo tracks neither RUSTC_WRAPPER nor the wrapper and features it applies.
        printf '%s\n' '// Written by ../../generate.sh.' 'fn main() {' \
            '    println!("cargo::rerun-if-env-changed=RUSTC_WRAPPER");' \
            '    println!("cargo::rerun-if-changed=Cargo.toml");' \
            '    println!("cargo::rerun-if-changed=../../../../scripts/tier-rustc");' '}' > "$tier/$name/build.rs"
    done
    lacks=$(lacking "$arch" "$features")
    printf "\n[target.'cfg(all(%s))'.dependencies]\n" "$lacks" >> "$dispatch/Cargo.toml"
    printf '%s = { package = "experimental_lean_vm_core_%s", path = "../experimental_tiers/%s/experimental_lean_vm_core", optional = true }\n' \
        "$tier" "$tier" "$tier" >> "$dispatch/Cargo.toml"
    cfg="cfg(all(feature = \"cpu_tiers\", $lacks))"
    detect=is_x86_feature_detected
    [ "$arch" = x86_64 ] || detect=is_${arch}_feature_detected
    printf '    #[%s]\n    %s => %s,\n' "$cfg" "$tier" \
        "$(echo "$features" | sed "s/+\([a-z0-9_.]*\)/std::arch::$detect!(\"\1\")/g; s/,/ \&\& /g")" >> "$dispatch/src/tiers.rs"
done
printf '}\n' >> "$dispatch/src/tiers.rs"
names=$(echo "$tiers" | awk 'NF { printf "%s\"%s\"", (n++ ? ", " : ""), $1 }')
deps=$(echo "$tiers" | awk 'NF { printf "%s\"dep:%s\"", (n++ ? ", " : ""), $1 }')
{
    printf '\n[features]\n# The CPU tiers, which only a build with scripts/tier-rustc makes faster.\ncpu_tiers = [%s]\n' "$deps"
    printf '\n# Named by tiers.rs, which machete does not read.\n[package.metadata.cargo-machete]\nignored = [%s]\n' "$names"
} >> "$dispatch/Cargo.toml"
