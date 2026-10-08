//! The memory helpers of the x86-64 NTT butterfly kernels (`intrinsics::x86_nttsimd`) against their
//! specifications: each load returns the words (or bytes) at its offset, read through `transmute` as the views
//! are, and each store writes exactly its words and leaves the rest of the row as it was. Each helper is compiled
//! where its target feature is, so each test runs in the builds that have it.
use core::arch::x86_64::*;
use core::mem::transmute;
use leanvm_verus::gf2_64::F64;
use leanvm_verus::intrinsics::x86_nttsimd as helpers;
use primitives::test_util::Rng;

const N: usize = 2_000;

fn random_row(rng: &mut Rng, n: usize) -> Vec<F64> {
    (0..n).map(|_| F64(rng.next_u64())).collect()
}

/// Every offset of a row of `W + 7` words: the load gives words `at .. at + W`; the store of random words
/// changes exactly those.
macro_rules! check_load_store {
    ($w:literal, $reg:ty, $load:ident, $store:ident) => {{
        let mut rng = Rng::new(0x10AD + $w);
        for _ in 0..N {
            let row = random_row(&mut rng, $w + 7);
            for at in 0..=7 {
                let got = unsafe { transmute::<$reg, [u64; $w]>(helpers::$load(&row, at)) };
                let want: [u64; $w] = std::array::from_fn(|j| row[at + j].0);
                assert_eq!(got, want, "{} at {at}", stringify!($load));
                let words: [u64; $w] = std::array::from_fn(|_| rng.next_u64());
                let mut stored = row.clone();
                unsafe { helpers::$store(&mut stored, at, transmute::<[u64; $w], $reg>(words)) };
                for j in 0..row.len() {
                    let want = if (at..at + $w).contains(&j) {
                        words[j - at]
                    } else {
                        row[j].0
                    };
                    assert_eq!(stored[j].0, want, "{} at {at} word {j}", stringify!($store));
                }
            }
        }
    }};
}

#[cfg(target_feature = "avx512f")]
#[test]
fn avx512_row_loads_and_stores() {
    check_load_store!(8, __m512i, loadu512_at, storeu512_at);
}

#[cfg(target_feature = "avx")]
#[test]
fn avx_row_loads_and_stores() {
    check_load_store!(4, __m256i, loadu256_at, storeu256_at);
}

#[test]
fn byte_table_load() {
    let mut rng = Rng::new(0x128);
    for _ in 0..N {
        let bytes: [u8; 16] = std::array::from_fn(|_| rng.next_u64() as u8);
        assert_eq!(
            unsafe { transmute::<__m128i, [u8; 16]>(helpers::loadu128_bytes(&bytes)) },
            bytes
        );
    }
}
