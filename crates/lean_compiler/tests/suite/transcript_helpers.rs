//! The recursion guest's Fiat-Shamir step, written as it is there: a scalar packed into
//! the rate, a `keccak(.., cap=)` duplex step, and a challenge read off the output,
//! against the duplex sponge of `fiat_shamir::FiatShamirState`.

use lean_compiler::{compile, f128_literal, parse};
use primitives::field::F128;
use primitives::hash::{STATE_LANES, keccak_f};

const SRC: &str = r#"
from snark_lib import *

Y = 18446744073709551616

@inline
def challenge_from_state(state):
    return state[0]

@inline
def fs_pack(rate, k: Const, x, tag):
    rate[2 * k] = x
    rate[2 * k + 1] = Y * tag
    return

def main():
    seed = [CAP_0, CAP_1, CAP_2, CAP_3, CAP_4]
    rate = StackBuf(2)
    fs_pack(rate, 0, X_LIT, 1)
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
/// carry over. Returns the challenge, the output's first two lanes.
fn duplex(state: &mut [u64; STATE_LANES], rate: &[u64]) -> F128 {
    state[..16].fill(0);
    state[..rate.len()].copy_from_slice(rate);
    keccak_f(state);
    F128::new(state[0], state[1])
}

#[test]
fn guest_transcript_step_matches_the_native_duplex() {
    let mut state: [u64; STATE_LANES] = std::array::from_fn(|i| 0x9e37_79b9_7f4a_7c15u64.wrapping_mul(i as u64 + 1));
    keccak_f(&mut state);
    // The capacity cells as the VM reads them: lane 16 alone, then lanes 17..25 two a cell.
    let cap: [F128; 5] = std::array::from_fn(|c| match c {
        0 => F128::new(state[16], 0),
        _ => F128::new(state[15 + 2 * c], state[16 + 2 * c]),
    });
    // A scalar rides its four lanes as `[c0, c1, 0, tag]`.
    let mut src = SRC.replace("X_LIT", &f128_literal(F128::new(5, 6)));
    for (c, x) in cap.into_iter().enumerate() {
        src = src.replace(&format!("CAP_{c}"), &f128_literal(x));
    }
    let first = duplex(&mut state, &[5, 6, 0, 1]);
    let second = duplex(&mut state, &[]);

    let program = compile(&parse(&src).expect("parse"));
    program
        .execute([first, second])
        .expect("the guest's step is the native duplex");
    let wrong = second + F128::new(1, 0);
    assert!(program.execute([first, wrong]).is_err());
}
