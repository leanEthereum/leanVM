//! Groth16 verification over BN254, as Ethereum's pairing precompile (EIP-197) and a Solidity
//! verifier check it, for one verification key ([`vk`]).
//!
//! A proof is three points, `A` and `C` in G1 and `B` in G2, and it is valid for public inputs
//! `x` below `r` when
//!
//! ```text
//!   L = IC[0] + sum_i x_i IC[i + 1]
//!   e(A, B) e(C, -delta) e(alpha, -beta) e(L, -gamma) = 1
//! ```
//!
//! which is one Miller loop over the four pairs and one final exponentiation. The pair
//! `(alpha, -beta)` is fixed, so its Miller loop is a constant, and so are the lines of `-gamma`
//! and `-delta`: only `B`'s are computed as the loop goes.
//!
//! The field is `F_p` in Montgomery form over four 64-bit limbs; a value the advice holds is
//! canonical, little-endian limbs.
#![no_std]
use thiserror::Error;

mod curve;
mod fp;
mod fp12;
mod fp2;
mod fp6;
mod pairing;
pub mod vk;

pub use curve::{G1Point, G2Point};
pub use vk::N_INPUTS;

use curve::{G1Affine, G2Affine};
use fp::Fp;
use fp12::Fp12;
use pairing::{Scaled, multi_miller_loop};

/// A proof as the advice holds it.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Proof {
    pub a: G1Point,
    pub b: G2Point,
    pub c: G1Point,
}

/// The public inputs, each canonical, little-endian limbs.
pub type Inputs = [[u64; 4]; N_INPUTS];

/// Why a proof is refused.
#[derive(Debug, Error, PartialEq, Eq, Clone, Copy)]
pub enum Error {
    #[error("a coordinate is not below p")]
    NotInField,
    #[error("a point is not on its curve")]
    NotOnCurve,
    #[error("B is not in G2")]
    NotInSubgroup,
    #[error("a public input is not below r")]
    InputNotInField,
    #[error("the pairing check fails")]
    Rejected,
}

/// Verify `proof` for `inputs`.
///
/// # Errors
///
/// Refuses a point not on its curve (the point at infinity included), `B` outside G2, a value
/// out of its field, and a proof the pairing check rejects.
pub fn verify(proof: &Proof, inputs: &Inputs) -> Result<(), Error> {
    let a = G1Affine::from_point(&proof.a)?;
    let b = G2Affine::from_point(&proof.b)?;
    let c = G1Affine::from_point(&proof.c)?;
    let l = vk::public_input_point(inputs)?;

    // At infinity, L's pair is one and leaves the loop. No point of G1 has y = 0, G1 having odd
    // order, so the y's have inverses.
    let scaled = |p: &G1Affine, y_inv: Fp| Scaled {
        x_over_y: p.x.mul(&y_inv),
        y_inv,
    };
    let f = l
        .map_or_else(
            || {
                let fixed = [(scaled(&c, c.y.inverse().expect("y is not zero")), &vk::DELTA_NEG_LINES)];
                multi_miller_loop(&a, &b, &fixed)
            },
            |l| {
                let inverse = c.y.mul(&l.y).inverse().expect("y is not zero");
                let fixed = [
                    (scaled(&c, inverse.mul(&l.y)), &vk::DELTA_NEG_LINES),
                    (scaled(&l, inverse.mul(&c.y)), &vk::GAMMA_NEG_LINES),
                ];
                multi_miller_loop(&a, &b, &fixed)
            },
        )
        .mul(&vk::ALPHA_BETA_NEG);
    match f.final_exponentiation() {
        Some(e) if e == Fp12::ONE => Ok(()),
        _ => Err(Error::Rejected),
    }
}
