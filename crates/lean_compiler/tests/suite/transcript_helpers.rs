//! The recursion guest's Fiat-Shamir step, written as it is there: a scalar packed into
//! the rate, a `keccak(.., cap=)` duplex step, and a challenge read off the output,
//! against the duplex sponge of `fiat_shamir::FiatShamirState`.

use lean_compiler::{compile, parse};
use primitives::field::F192;
use primitives::hash::{STATE_LANES, keccak_f};

use crate::common::f192_lit;

const SRC: &str = r#"
from snark_lib import *

Y = f192(0, 1, 0)
Y_INV = Y_INV_LIT

@inline
def challenge_from_state(state):
    d2 = StackBuf(1)
    hint_f192_limbs(d2, state[1])
    d3 = (state[1] + d2[0]) * Y_INV
    assert_in_k(d2[0], d3)
    return state[0] + Y * Y * d2[0]

@inline
def fs_pack(rate, k: Const, x, tag):
    limbs = StackBuf(3)
    hint_f192_limbs(limbs, x)
    assert_in_k(limbs[2], tag)
    rate[2 * k] = x + Y * Y * limbs[2]
    rate[2 * k + 1] = limbs[2] + Y * tag
    return

def main():
    seed = [CAP_0, CAP_1, CAP_2, CAP_3, CAP_4]
    rate = StackBuf(2)
    fs_pack(rate, 0, f192(5, 6, 7), 1)
    sp = StackBuf(13)
    keccak(rate[0:2], [0, 0], sp, cap=seed)
    first = challenge_from_state(sp)
    nxt = StackBuf(13)
    keccak([0, 0], [0, 0], nxt, cap=sp)
    second = challenge_from_state(nxt)
    p = GEN ** 0
    p[1] = first
    p[GEN] = second
    return
"#;

/// One overwrite-mode duplex step: lanes `0..16` are `rate` then zeros, lanes `16..25`
/// carry over. Returns the challenge, the output's first three lanes.
fn duplex(state: &mut [u64; STATE_LANES], rate: &[u64]) -> F192 {
    state[..16].fill(0);
    state[..rate.len()].copy_from_slice(rate);
    keccak_f(state);
    F192::new(state[0], state[1], state[2])
}

#[test]
fn guest_transcript_step_matches_the_native_duplex() {
    let mut state: [u64; STATE_LANES] = std::array::from_fn(|i| 0x9e37_79b9_7f4a_7c15u64.wrapping_mul(i as u64 + 1));
    keccak_f(&mut state);
    // The capacity cells as the VM reads them: lane 16 alone, then lanes 17..25 two a cell.
    let cap: [F192; 5] = std::array::from_fn(|c| match c {
        0 => F192::new(state[16], 0, 0),
        _ => F192::new(state[15 + 2 * c], state[16 + 2 * c], 0),
    });
    let mut src = SRC.replace("Y_INV_LIT", &f192_lit(F192::new(0, 1, 0).inv()));
    for (c, x) in cap.into_iter().enumerate() {
        src = src.replace(&format!("CAP_{c}"), &f192_lit(x));
    }
    let first = duplex(&mut state, &[5, 6, 7, 1]);
    let second = duplex(&mut state, &[]);

    let program = compile(&parse(&src).expect("parse"));
    program
        .execute([first, second])
        .expect("the guest's step is the native duplex");
    let wrong = second + F192::new(1, 0, 0);
    assert!(program.execute([first, wrong]).is_err());
}
