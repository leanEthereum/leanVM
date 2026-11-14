//! The `kernels` group: differential tests of the prover's kernels against plain references written here, and
//! against the `verifier` crate's own scalar code where it is public. A disagreement is High: two implementations of
//! one function differ, and a proof built on the wrong one fails (or, worse, verifies something else).

use crate::{Cost, Source, Target};
use primitives::field::{F64, F128};

mod bits;
mod field;
mod hash;
mod merkle;
mod multilinear;
mod ntt;
mod parallel;
mod sponge;

pub static TARGETS: &[&Target] = &[
    &Target {
        name: "kernel-field",
        about: "K and E arithmetic, the batched and unreduced kernels, g-powers and inverses against a schoolbook reference and the verifier's field",
        cost: Cost::Cheap,
        run: field::run,
    },
    &Target {
        name: "kernel-hash",
        about: "Keccak-256 one-shot, streaming, batched and from-state, and the permutation, against sha3 and a reference Keccak-f",
        cost: Cost::Cheap,
        run: hash::run,
    },
    &Target {
        name: "kernel-sponge",
        about: "the Fiat-Shamir duplex, compress and the DA membership challenge against a sponge built here from the permutation",
        cost: Cost::Cheap,
        run: sponge::run,
    },
    &Target {
        name: "kernel-ntt",
        about: "the additive NTT: encode against naive novel-basis evaluation, forward then inverse, twiddles against subspace polynomials",
        cost: Cost::Cheap,
        run: ntt::run,
    },
    &Target {
        name: "kernel-merkle",
        about: "the WHIR commitment root against an encode-and-hash reference, openings authenticated as the verifier does, mutated ones refused",
        cost: Cost::Cheap,
        run: merkle::run,
    },
    &Target {
        name: "kernel-multilinear",
        about: "eq tables, MLE evaluation, packed dot products and the verifier's bytecode evaluation against naive sums",
        cost: Cost::Cheap,
        run: multilinear::run,
    },
    &Target {
        name: "kernel-bits",
        about: "bit transposes, the bit fold and streaming copies against naive loops",
        cost: Cost::Cheap,
        run: bits::run,
    },
    &Target {
        name: "kernel-parallel",
        about: "every thread-pool primitive on random counts and chunk sizes against a sequential loop",
        cost: Cost::Cheap,
        run: parallel::run,
    },
];

/// Plain references: bit loops with nothing shared with the code under test.
pub mod reference {
    use super::*;

    /// The modulus of `K` past `x^64`: `x^4 + x^3 + x + 1`.
    const R: u128 = 0x1B;

    pub fn clmul(a: u64, b: u64) -> u128 {
        (0..64)
            .filter(|i| a >> i & 1 == 1)
            .fold(0u128, |acc, i| acc ^ (u128::from(b) << i))
    }

    /// Long division by `x^64 + x^4 + x^3 + x + 1`, one bit at a time.
    pub fn reduce(mut p: u128) -> u64 {
        for i in (64..128).rev() {
            if p >> i & 1 == 1 {
                p ^= (1u128 << i) | (R << (i - 64));
            }
        }
        p as u64
    }

    pub fn mul_k(a: u64, b: u64) -> u64 {
        reduce(clmul(a, b))
    }

    pub fn pow_k(a: u64, mut e: u128) -> u64 {
        let (mut acc, mut base) = (1u64, a);
        while e > 0 {
            if e & 1 == 1 {
                acc = mul_k(acc, base);
            }
            base = mul_k(base, base);
            e >>= 1;
        }
        acc
    }

    /// Schoolbook over `K[y]/(y² + xy + 1)`: three coefficients, then `y² = xy + 1`, so the
    /// high-limb product lands on the constant and, times `x`, on the `y` coefficient.
    pub fn mul_e(a: F128, b: F128) -> F128 {
        let (a0, a1) = (a.c0, a.c1);
        let (b0, b1) = (b.c0, b.c1);
        let p = mul_k(a1, b1);
        F128::new(mul_k(a0, b0) ^ p, mul_k(a0, b1) ^ mul_k(a1, b0) ^ mul_k(2, p))
    }

    pub fn pow_e(a: F128, mut e: u128) -> F128 {
        let (mut acc, mut base) = (F128::ONE, a);
        while e > 0 {
            if e & 1 == 1 {
                acc = mul_e(acc, base);
            }
            base = mul_e(base, base);
            e >>= 1;
        }
        acc
    }

    pub fn add_e(a: F128, b: F128) -> F128 {
        F128::new(a.c0 ^ b.c0, a.c1 ^ b.c1)
    }

    pub fn mul_base(a: F128, k: u64) -> F128 {
        F128::new(mul_k(a.c0, k), mul_k(a.c1, k))
    }

    /// Keccak-f\[1600\] from the specification: round constants from the LFSR, rotation offsets from the `(x, y)`
    /// walk, nothing taken from the crates under test. Lane `x + 5y` is `A[x, y]`.
    pub fn keccak_f(a: &mut [u64; 25]) {
        static TABLES: std::sync::OnceLock<([u64; 24], [u32; 25])> = std::sync::OnceLock::new();
        let (rc, rho) = TABLES.get_or_init(|| {
            let rc_bit = |t: usize| {
                let mut r: u16 = 1;
                for _ in 0..t % 255 {
                    r <<= 1;
                    if r & 0x100 != 0 {
                        r ^= 0x171;
                    }
                }
                r & 1 == 1
            };
            let rc = std::array::from_fn(|i| {
                (0..7)
                    .filter(|&j| rc_bit(j + 7 * i))
                    .fold(0u64, |acc, j| acc | 1 << ((1 << j) - 1))
            });
            let mut rho = [0u32; 25];
            let (mut x, mut y) = (1usize, 0usize);
            for t in 0..24 {
                rho[x + 5 * y] = (((t + 1) * (t + 2) / 2) % 64) as u32;
                (x, y) = (y, (2 * x + 3 * y) % 5);
            }
            (rc, rho)
        });
        for &round in rc {
            let c: [u64; 5] = std::array::from_fn(|x| (0..5).fold(0, |acc, y| acc ^ a[x + 5 * y]));
            for x in 0..5 {
                let d = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
                for y in 0..5 {
                    a[x + 5 * y] ^= d;
                }
            }
            let mut b = [0u64; 25];
            for x in 0..5 {
                for y in 0..5 {
                    b[y + 5 * ((2 * x + 3 * y) % 5)] = a[x + 5 * y].rotate_left(rho[x + 5 * y]);
                }
            }
            for x in 0..5 {
                for y in 0..5 {
                    a[x + 5 * y] = b[x + 5 * y] ^ (!b[(x + 1) % 5 + 5 * y] & b[(x + 2) % 5 + 5 * y]);
                }
            }
            a[0] ^= round;
        }
    }

    /// Ethereum's Keccak-256, from the `sha3` crate.
    pub fn keccak256(data: &[u8]) -> [u8; 32] {
        use sha3::Digest;
        sha3::Keccak256::digest(data)[..].try_into().unwrap()
    }

    pub fn hash_pair(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
        keccak256(&[&a[..], &b[..]].concat())
    }

    /// The root of a binary tree over `leaves`, pairs hashed left to right.
    pub fn merkle_root(mut level: Vec<[u8; 32]>) -> [u8; 32] {
        assert!(level.len().is_power_of_two());
        while level.len() > 1 {
            level = level.chunks(2).map(|p| hash_pair(&p[0], &p[1])).collect();
        }
        level[0]
    }

    pub fn words_le(words: &[u64]) -> Vec<u8> {
        words.iter().flat_map(|w| w.to_le_bytes()).collect()
    }
}

/// A `K` element biased to the edges a carry-less kernel gets wrong: high bits, single bits, all ones.
pub fn edge_k(src: &mut Source) -> F64 {
    match src.below(10) {
        0 => F64(u64::MAX),
        1 => F64(1 << 63),
        2 => F64(u64::MAX << src.below(64)),
        3 => F64(u64::MAX >> src.below(64)),
        4 => F64(0x1B),
        _ => src.f64(),
    }
}

/// An `E` element biased like [`edge_k`], limb by limb.
pub fn edge_e(src: &mut Source) -> F128 {
    match src.below(6) {
        0 => F128::new(edge_k(src).0, edge_k(src).0),
        1 => F128::new(0, edge_k(src).0),
        2 => F128::new(edge_k(src).0, 0),
        _ => src.f128(),
    }
}

/// `n` random `E` elements expanded from one draw, a few of them replaced by edges.
pub fn bulk_e(src: &mut Source, n: usize) -> Vec<F128> {
    let words = src.bulk_u64(2 * n);
    let mut out: Vec<F128> = words
        .as_chunks::<2>()
        .0
        .iter()
        .map(|w| F128::new(w[0], w[1]))
        .collect();
    for _ in 0..src.below(4) {
        if n > 0 {
            let i = src.below(n);
            out[i] = edge_e(src);
        }
    }
    out
}

/// `n` random `K` elements, a few replaced by edges.
pub fn bulk_k(src: &mut Source, n: usize) -> Vec<F64> {
    let mut out: Vec<F64> = src.bulk_u64(n).into_iter().map(F64).collect();
    for _ in 0..src.below(4) {
        if n > 0 {
            let i = src.below(n);
            out[i] = edge_k(src);
        }
    }
    out
}

/// A High finding for a kernel that disagrees with its reference, keyed by the kernel alone.
pub fn mismatch(kernel: &str, detail: impl std::fmt::Display) -> crate::Finding {
    crate::Finding::high(format!("{kernel} disagrees with its reference"), detail.to_string())
}

/// `ensure!` for kernels: `check!(cond, "kernel", "detail {}", args)`.
macro_rules! check {
    ($cond:expr, $kernel:expr, $($detail:tt)+) => {
        if !$cond {
            return Err($crate::targets::kernels::mismatch($kernel, format!($($detail)+)));
        }
    };
}
pub(crate) use check;
