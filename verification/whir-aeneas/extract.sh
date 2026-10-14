#!/usr/bin/env bash
set -euo pipefail
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$here/../.." && pwd)
tools="$here/.tools/aeneas"
"$here/bootstrap.sh"
generator="$here/.tools/aeneas-source/src/_build/default/main.exe"
frontend="$here/.tools/aeneas-source/charon/charon/target/release/charon"
if [[ ! -x "$generator" || ! -x "$frontend" || ! -f "$here/.tools/charon-build.sha256" ]] ||
    ! sha256sum -c "$here/.tools/charon-build.sha256" >/dev/null; then
    "$here/bootstrap-tool.sh"
fi
export PATH="$tools:$PATH"
export CARGO_BUILD_JOBS=2 LEAN_NUM_THREADS=2
export RUSTFLAGS='-C target-cpu=x86-64'
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$here/.tools/target}"
surface=${1:-statement}
aeneas_args=(-backend lean -namespace PcsSource -emit-json -no-progress-bar -abort-on-error)
crate="$root/crates/pcs"
llbc_name=pcs
case "$surface" in
    statement)
        dest="$here/llbc/statement"
        generated="$here"
        args=(--start-from pcs::stack::Statement::check --include primitives)
        cargo_args=(--lib --release)
        aeneas_args=(-backend lean -namespace StatementSource -no-progress-bar
                     -abort-on-error -all-computable -split-files -subdir WhirAeneas/Generated/Statement)
        ;;
    replay)
        dest="$here/llbc/replay"
        generated="$here"
        args=(--start-from pcs::whir::verify::verify --start-from pcs::whir::query::sample_queries
              --start-from pcs::ring_switch::RingMap::close
              --start-from pcs::merkle::PrunedMerklePaths::open --start-from pcs::merkle::PrunedMerklePaths::from_hint
              --start-from pcs::verifier::open_rows_native
              --start-from '{impl pcs::verifier::OpeningVerifier for fiat_shamir::verifier::VerifierState<_>}'
              --include primitives --include fiat_shamir
              --opaque pcs::merkle::hash_pairs --opaque pcs::merkle::hash_rows --opaque pcs::merkle::sorted_unique
              --opaque primitives::hash::hash --opaque 'fiat_shamir::codec::_::encode'
              --opaque 'fiat_shamir::duplex::_::context'
              --opaque 'fiat_shamir::duplex::_::absorb' --opaque 'fiat_shamir::duplex::_::squeeze')
        cargo_args=(--lib --release)
        aeneas_args=(-backend lean -namespace ReplaySource -no-progress-bar
                     -abort-on-error -all-computable -split-files -subdir WhirAeneas/Generated/Replay)
        ;;
    verifier)
        dest="$here/llbc/verifier"
        generated="$here"
        args=(--start-from pcs::whir::verify::verify_with_basis --include primitives --include fiat_shamir)
        cargo_args=(--lib --release)
        aeneas_args+=(-subdir WhirAeneas/Generated/Verifier -split-files -all-computable)
        ;;
    native)
        dest="$here/failures/native"
        generated="$dest/generated"
        args=(--start-from-if-exists pcs::stack::tests::verify_instance --include primitives --include fiat_shamir)
        cargo_args=(--lib --tests --release)
        ;;
    native-hash-interface|native-hash-interface-mono)
        dest="$here/failures/$surface"
        generated="$dest/generated"
        args=(--start-from-if-exists pcs::stack::tests::verify_instance --include primitives --include fiat_shamir
              --opaque primitives::hash::compress
              --opaque pcs::merkle::hash_pairs
              --opaque 'pcs::merkle::_::hash'
              --opaque primitives::hash::hash
              --opaque primitives::hash::hash_many
              --opaque primitives::hash::hash_many_dyn_from_state
              --opaque primitives::hash::hash_from_state
              --opaque primitives::hash::zero_prefix_state)
        if [[ "$surface" == native-hash-interface-mono ]]; then
            args+=(--monomorphize)
        fi
        cargo_args=(--lib --tests --release)
        ;;
    portable)
        crate="$root/crates/primitives"
        llbc_name=primitives
        dest="$here/llbc/portable"
        generated="$here/WhirAeneas/Generated/Portable"
        args=(--start-from primitives::hash::compress_portable)
        cargo_args=(--lib --release)
        aeneas_args=(-backend lean -namespace PortableSource -emit-json -no-progress-bar -all-computable)
        ;;
    *) printf 'unknown extraction surface: %s\n' "$surface" >&2; exit 2 ;;
esac
mkdir -p "$dest" "$generated"
cd "$crate"
flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 "$frontend" cargo --preset=aeneas "${args[@]}" --dest-file "$dest/$llbc_name.llbc" -- "${cargo_args[@]}"
if [[ "$surface" == native || "$surface" == native-hash-interface* ]]; then
    python3 "$here/toolchain/check-extracted-root.py" "$dest/$llbc_name.llbc" pcs::stack::tests::verify_instance
fi
if [[ "$surface" == statement ]]; then
    python3 "$here/toolchain/check-extracted-root.py" "$dest/$llbc_name.llbc" pcs::stack::Statement::check
fi
if [[ "$surface" == replay ]]; then
    for root in pcs::whir::verify::verify pcs::whir::query::sample_queries pcs::whir::query::Stratum::batch \
        pcs::ring_switch::RingMap::close pcs::whir::sumcheck::RoundQuad::read \
        fiat_shamir::arith::Verifier::read_round fiat_shamir::arith::RoundWeight::fixed_index \
        pcs::merkle::PrunedMerklePaths::open pcs::merkle::PrunedMerklePaths::from_hint \
        pcs::verifier::open_rows_native pcs::verifier::authenticate pcs::merkle::Openings::rows \
        pcs::ntt::basis::NovelBasis::new pcs::whir::query::Padding::share \
        fiat_shamir::verifier::VerifierState::prover_hint_with fiat_shamir::verifier::VerifierState::prover_hint \
        fiat_shamir::verifier::VerifierState::prover_message fiat_shamir::verifier::VerifierState::verifier_message \
        fiat_shamir::verifier::VerifierState::check_pow fiat_shamir::pow::ProofOfWork::verify; do
        python3 "$here/toolchain/check-extracted-root.py" "$dest/$llbc_name.llbc" "$root"
    done
fi
flock /tmp/leanvm-heavy.lock systemd-run --user --scope -q -p MemoryMax=20G -p MemorySwapMax=0 "$generator" "${aeneas_args[@]}" -dest "$generated" "$dest/$llbc_name.llbc"
