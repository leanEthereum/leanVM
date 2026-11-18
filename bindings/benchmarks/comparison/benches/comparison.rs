use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use lean_pq::xmss;
use lean_pq_comparison::{lean_full_key_seed, FixtureSet};

/// The leaf index the full key signs at in the single-operation benchmarks.
const LEAN_LEAF_INDEX: xmss::LeafIndex = 0;

const INDEPENDENT_SIGNATURE_SIZES: [usize; 3] = [1, 8, 16];

fn verify_lean_independent_signatures(fixtures: &FixtureSet) -> bool {
    fixtures
        .lean_signatures()
        .iter()
        .zip(fixtures.lean_public_keys())
        .zip(fixtures.lean_messages())
        .all(|((signature, public_key), message)| public_key.verify(message, signature).is_ok())
}

fn single_operations(criterion: &mut Criterion) {
    let fixtures = FixtureSet::same_claim(1).expect("single-signer fixture should be valid");
    let lean_message = &fixtures.lean_messages()[0];
    let lean_key = &xmss::SecretKey::from_seed(
        lean_full_key_seed(0).expect("the full-key seed should be derivable"),
    );
    let lean_signature = &lean_key.sign(lean_message, LEAN_LEAF_INDEX);
    let lean_public_key = &lean_key.public_key();
    let bls_message = fixtures.bls_messages()[0];
    let bls_key = &fixtures.bls_keys()[0];
    let bls_signature = &fixtures.bls_signatures()[0];
    let bls_public_key = &fixtures.bls_public_keys()[0];

    assert!(lean_public_key.verify(lean_message, lean_signature).is_ok());
    assert!(bls_signature.verify(bls_public_key, bls_message));

    let artifact_sizes = [
        ("public_key/lean", lean_public_key.to_bytes().len()),
        ("public_key/lighthouse", bls_public_key.serialize().len()),
        ("raw_signature/lean", lean_signature.to_bytes().len()),
        ("raw_signature/lighthouse", bls_signature.serialize().len()),
    ];
    for (artifact, size) in artifact_sizes {
        println!("artifact-size {artifact} {size}");
    }

    let mut group = criterion.benchmark_group("sign");
    group.bench_function("lean", |bencher| {
        bencher.iter(|| {
            black_box(black_box(lean_key).sign(black_box(lean_message), black_box(LEAN_LEAF_INDEX)))
        });
    });
    group.bench_function("lighthouse", |bencher| {
        bencher.iter(|| black_box(black_box(bls_key).sign(black_box(bls_message))));
    });
    group.finish();

    let lean_signature_bytes = lean_signature.to_bytes();
    let bls_signature_bytes = bls_signature.serialize();
    let decoded_lean_signature = xmss::Signature::from_bytes(&lean_signature_bytes)
        .expect("fixture XMSS signature deserialization should succeed");
    let decoded_bls_signature = lighthouse_bls::Signature::deserialize(&bls_signature_bytes)
        .expect("fixture BLS signature deserialization should succeed");
    assert!(lean_public_key
        .verify(lean_message, &decoded_lean_signature)
        .is_ok());
    assert!(decoded_bls_signature.verify(bls_public_key, bls_message));

    let mut group = criterion.benchmark_group("raw_signature_serialize");
    group.bench_function("lean", |bencher| {
        bencher.iter(|| black_box(black_box(lean_signature).to_bytes()));
    });
    group.bench_function("lighthouse", |bencher| {
        bencher.iter(|| black_box(black_box(bls_signature).serialize()));
    });
    group.finish();

    let mut group = criterion.benchmark_group("raw_signature_deserialize");
    group.bench_function("lean", |bencher| {
        bencher.iter(|| {
            black_box(
                xmss::Signature::from_bytes(black_box(&lean_signature_bytes))
                    .expect("fixture XMSS signature deserialization should succeed"),
            )
        });
    });
    group.bench_function("lighthouse", |bencher| {
        bencher.iter(|| {
            black_box(
                lighthouse_bls::Signature::deserialize(black_box(&bls_signature_bytes))
                    .expect("fixture BLS signature deserialization should succeed"),
            )
        });
    });
    group.finish();

    let mut group = criterion.benchmark_group("single_verify");
    group.bench_function("lean", |bencher| {
        bencher.iter(|| {
            black_box(
                black_box(lean_public_key)
                    .verify(black_box(lean_message), black_box(lean_signature)),
            )
        });
    });
    group.bench_function("lighthouse", |bencher| {
        bencher.iter(|| {
            black_box(
                black_box(bls_signature).verify(black_box(bls_public_key), black_box(bls_message)),
            )
        });
    });
    group.finish();
}

fn independent_signature_verification(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("independent_signatures_verify");

    for size in INDEPENDENT_SIGNATURE_SIZES {
        let fixtures = FixtureSet::distinct_claims(size)
            .expect("independent-signature fixtures should be valid");
        let bls_signature_sets = fixtures.bls_signature_sets();
        assert!(verify_lean_independent_signatures(&fixtures));
        assert!(lighthouse_bls::verify_signature_sets(
            bls_signature_sets.iter()
        ));

        group.bench_with_input(
            BenchmarkId::new("lean", size),
            &fixtures,
            |bencher, fixtures| {
                bencher.iter(|| black_box(verify_lean_independent_signatures(black_box(fixtures))));
            },
        );
        group.bench_with_input(
            BenchmarkId::new("lighthouse", size),
            &bls_signature_sets,
            |bencher, signature_sets| {
                bencher.iter(|| {
                    black_box(lighthouse_bls::verify_signature_sets(black_box(
                        signature_sets.iter(),
                    )))
                });
            },
        );
    }

    group.finish();
}

criterion_group!(
    benches,
    single_operations,
    independent_signature_verification
);
criterion_main!(benches);
