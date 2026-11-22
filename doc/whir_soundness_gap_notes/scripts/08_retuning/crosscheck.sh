#!/bin/sh
# Cross-check of whir_model.py against the Rust search at non-deployed constants (researcher 08).
#
# Copies crates/experimental_prover/pcs/src/whir_config.rs and whir_config/affine_mca.rs, unmodified but for their
# imports, into a scratch crate in DIR (outside the repository; default: a fresh temporary directory), builds it once
# per variant with a stub `verifier` module carrying that variant's constants, and compares every admitted shape
# (rates 1..4, stacked sizes 16..30) with the model. Nothing in the repository is modified.
#
# Usage: sh crosscheck.sh [DIR]
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../../.." && pwd)
DIR=${1:-$(mktemp -d)}
mkdir -p "$DIR/src/whir_config"
cd "$DIR"
cat > Cargo.toml <<'TOML'
[package]
name = "whircheck"
version = "0.0.0"
edition = "2024"

[workspace]
TOML
sed -e 's/^use verifier::{/use crate::verifier::{/' -e 's/fiat_shamir::SECURITY_BITS/crate::fiat_shamir::SECURITY_BITS/g' \
    -e 's/fiat_shamir::grinding_bits/crate::fiat_shamir::grinding_bits/g' \
    "$REPO/crates/experimental_prover/pcs/src/whir_config.rs" > src/whir_config.rs
cp "$REPO/crates/experimental_prover/pcs/src/whir_config/affine_mca.rs" src/whir_config/affine_mca.rs
cat > main.rs.tmpl <<'RUST'
#![allow(dead_code, unused_imports)]
mod verifier {
    pub const MIN_LOG_INV_RATE: usize = 1;
    pub const MAX_LOG_INV_RATE: usize = 4;
    pub const INITIAL_FOLDING_FACTOR: usize = @K0@;
    pub const SUBSEQUENT_FOLDING_FACTOR: usize = @KS@;
    pub const RS_DOMAIN_INITIAL_REDUCTION_FACTOR: usize = @R0@;
    pub const RS_DOMAIN_SUBSEQUENT_REDUCTION_FACTOR: usize = @RS@;
    pub const RESIDUAL_MAX_LOG: usize = @RES@;
    pub const QUERY_GRINDING_BITS: u32 = @GQ@;
    pub const FOLD_GRINDING_BITS: u32 = @GF@;
    pub const BATCH_GRINDING_BITS: u32 = @GB@;
    pub const OOD_GRINDING_BITS: u32 = @GO@;
}
mod fiat_shamir {
    pub const SECURITY_BITS: u32 = 125;
    pub const fn grinding_bits(numerator: u128) -> u32 {
        let log = if numerator <= 1 { 0 } else { u128::BITS - (numerator - 1).leading_zeros() };
        log.saturating_sub(128 - SECURITY_BITS)
    }
}
mod ring_switch {
    pub(crate) const RING_SWITCH_ERROR_NUMERATOR: usize = 2;
}
const LOG_PACKING: usize = 0;
mod whir_config;

fn main() {
    for rate in 1..=4usize {
        for log_n in 16..=30usize {
            match whir_config::WhirSecurityConfig::derive_config_with_log_inv_rate(log_n, rate) {
                Ok(cfg) => {
                    let q: Vec<usize> = cfg.levels.iter().map(|lv| lv.queries).collect();
                    let l: Vec<u128> = cfg.levels.iter().map(|lv| lv.list_bound().unwrap()).collect();
                    println!("{rate} {log_n} {q:?} {l:?}");
                }
                Err(_) => println!("{rate} {log_n} None"),
            }
        }
    }
}
RUST
# k0 ks r0 rs residual_max g_query g_fold g_batch g_ood
variant() {
    sed -e "s/@K0@/$1/" -e "s/@KS@/$2/" -e "s/@R0@/$3/" -e "s/@RS@/$4/" -e "s/@RES@/$5/" -e "s/@GQ@/$6/" \
        -e "s/@GF@/$7/" -e "s/@GB@/$8/" -e "s/@GO@/$9/" main.rs.tmpl > src/main.rs
    cargo run -j4 --release --offline 2>/dev/null | grep -E "^[1-4] [0-9]+ " > "out_$1_$2_$3_$4_$5_$6_$7_$8_$9.txt"
}
variant 6 4 3 1 5 17 7 13 15
variant 5 4 3 1 5 17 7 13 15
variant 6 4 3 1 5 24 7 14 16
variant 5 4 3 1 5 22 7 14 16
variant 5 5 2 2 5 17 7 13 15
variant 4 3 2 1 4 20 9 14 19
variant 6 4 4 1 5 17 7 13 15
variant 7 5 3 0 5 17 5 12 15
variant 6 4 3 1 5 28 12 16 27
variant 5 4 2 1 5 19 6 13 17
variant 6 4 3 1 6 17 7 13 15
variant 6 4 3 1 6 22 7 14 16
python3 "$HERE/crosscheck.py" "$DIR"
