#!/bin/sh
# Writes the CPU tiers: per tier, a copy of the experimental prover's crates over the same sources, which
# scripts/tier-rustc compiles with the tier's target features, and experimental_dispatch's manifest and tiers.rs,
# behind its `cpu_tiers` feature.
set -eu
cd "$(dirname "$0")"
# It deletes the directories next to it: refuse to run anywhere else.
[ "${PWD##*/}" = experimental_tiers ] && [ -f generate.sh ] || { echo "run it as sh crates/experimental_tiers/generate.sh" >&2; exit 1; }

x86v3=+avx2,+bmi1,+bmi2,+fma,+lzcnt,+movbe,+f16c,+popcnt,+pclmulqdq
x86v4=$x86v3,+avx512f,+avx512bw,+avx512cd,+avx512dq,+avx512vl
# Fastest first: dispatch takes the first the CPU runs.
tiers="
x86v4gfni x86_64 $x86v4,+vpclmulqdq,+gfni,+avx512vbmi
x86v3gfni x86_64 $x86v3,+vpclmulqdq,+gfni
x86v3clmul x86_64 $x86v3,+vpclmulqdq
x86v4 x86_64 $x86v4
x86avx2 x86_64 +avx2,+pclmulqdq
armsha3 aarch64 +aes,+sha3
armaes aarch64 +aes
"
# The features the copied sources gate code on, per architecture; `avx` and `ssse3` come with `avx2`.
gated="
x86_64 avx2 pclmulqdq bmi2 vpclmulqdq gfni avx512f avx512bw avx512vbmi
aarch64 aes sha3
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

# The sources gate on exactly the gated features, and a tier of its architecture enables each one.
sources=$(echo "$crates" | awk 'NF { print "../" $2 "/src" }')
found=$(grep -rhoE 'target_feature *= *"[a-z0-9_.]+"' $sources | sed 's/.*"\(.*\)"/\1/' | sort -u)
for feature in $found; do
    case " avx ssse3 $(echo $gated) " in
    *" $feature "*) ;;
    *) echo "the sources gate on $feature: add it to a tier and to \$gated" >&2 && exit 1 ;;
    esac
done
echo "$gated" | while read -r arch features; do
    for feature in $features; do
        echo "$found" | grep -qx "$feature" || { echo "no source gates on $feature: drop it from \$gated" >&2 && exit 1; }
        echo "$tiers" | awk -v arch="$arch" '$2 == arch { print $3 }' | grep -q "+$feature\b" ||
            { echo "no $arch tier enables $feature" >&2 && exit 1; }
    done
done
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
            '    let wrapper = "../../../../scripts/tier-rustc";' \
            '    if std::path::Path::new(wrapper).exists() {' \
            '        println!("cargo::rerun-if-changed={wrapper}");' '    }' '}' > "$tier/$name/build.rs"
    done
    lacks=$(lacking "$arch" "$features")
    printf "\n[target.'cfg(all(%s))'.dependencies]\n" "$lacks" >> "$dispatch/Cargo.toml"
    printf '%s = { package = "experimental_lean_vm_core_%s", path = "../experimental_tiers/%s/experimental_lean_vm_core", optional = true }\n' \
        "$tier" "$tier" "$tier" >> "$dispatch/Cargo.toml"
    cfg="cfg(all(feature = \"cpu_tiers\", $lacks))"
    detect=is_x86_feature_detected
    [ "$arch" = x86_64 ] || detect=is_${arch}_feature_detected
    printf '    #[%s]\n    %s => %s, [%s],\n' "$cfg" "$tier" \
        "$(echo "$features" | sed "s/+\([a-z0-9_.]*\)/std::arch::$detect!(\"\1\")/g; s/,/ \&\& /g")" \
        "$(echo "$features" | sed 's/+\([a-z0-9_.]*\)/"\1"/g; s/,/, /g')" >> "$dispatch/src/tiers.rs"
done
printf '}\n' >> "$dispatch/src/tiers.rs"
# Per architecture, for the warning: every tier and its features, and per feature whether the CPU has it and
# whether the build's own code does.
echo "$gated" | while read -r arch gates; do
    [ -n "$arch" ] || continue
    detect=is_x86_feature_detected
    [ "$arch" = x86_64 ] || detect=is_${arch}_feature_detected
    all=$(echo "$tiers" | awk -v arch="$arch" '$2 == arch { print $3 }' | tr ',+' '\n\n' | awk 'NF && !seen[$0]++')
    printf '\n#[cfg(target_arch = "%s")]\nconst TABLE: &[(&str, &[&str])] = &[\n' "$arch"
    echo "$tiers" | awk -v arch="$arch" '$2 == arch { print $1, $3 }' | while read -r tier features; do
        printf '    ("%s", &[%s]),\n' "$tier" "$(echo "$features" | sed 's/+\([a-z0-9_.]*\)/"\1"/g; s/,/, /g')"
    done
    printf '];\n\n#[cfg(target_arch = "%s")]\nconst GATED: &[&str] = &[%s];\n' "$arch" \
        "$(for f in $gates; do printf '"%s", ' "$f"; done | sed 's/, $//')"
    printf '\n#[cfg(target_arch = "%s")]\nfn on_cpu(feature: &str) -> bool {\n    match feature {\n' "$arch"
    for f in $all; do
        printf '        "%s" => std::arch::%s!("%s"),\n' "$f" "$detect" "$f"
    done
    printf '        _ => false,\n    }\n}\n\n#[cfg(target_arch = "%s")]\nconst IN_BUILD: &[(&str, bool)] = &[\n' "$arch"
    for f in $all; do
        printf '    ("%s", cfg!(target_feature = "%s")),\n' "$f" "$f"
    done
    printf '];\n'
done >> "$dispatch/src/tiers.rs"
others="not(any($(echo "$gated" | awk 'NF { printf "%starget_arch = \"%s\"", (n++ ? ", " : ""), $1 }')))"
printf '\n#[cfg(%s)]\nconst TABLE: &[(&str, &[&str])] = &[];\n\n#[cfg(%s)]\nconst GATED: &[&str] = &[];\n' "$others" "$others" >> "$dispatch/src/tiers.rs"
printf '\n#[cfg(%s)]\nfn on_cpu(_: &str) -> bool {\n    false\n}\n\n#[cfg(%s)]\nconst IN_BUILD: &[(&str, bool)] = &[];\n' "$others" "$others" >> "$dispatch/src/tiers.rs"
names=$(echo "$tiers" | awk 'NF { printf "%s\"%s\"", (n++ ? ", " : ""), $1 }')
deps=$(echo "$tiers" | awk 'NF { printf "%s\"dep:%s\"", (n++ ? ", " : ""), $1 }')
{
    printf '\n[features]\n# The CPU tiers, which only a build with scripts/tier-rustc makes faster.\ncpu_tiers = [%s]\n' "$deps"
    printf '\n# Named by tiers.rs, which machete does not read.\n[package.metadata.cargo-machete]\nignored = [%s]\n' "$names"
} >> "$dispatch/Cargo.toml"
