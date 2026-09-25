use lean_compiler::{compile, parse};
use primitives::field::F192;

#[test]
fn transcript_helpers_are_ordinary_nested_inline_zkdsl() {
    let src = r#"
from snark_lib import *

Y = f192(0, 1, 0)

@inline
def pack64x2(a, b):
    assert_in_k(a, b)
    return a + Y * b

@inline
def challenge_from_state(state):
    lo = StackBuf(2)
    hi = StackBuf(2)
    hint_f192_limbs(lo, state[0])
    hint_f192_limbs(hi, state[1])
    state[0] = pack64x2(lo[0], lo[1])
    state[1] = pack64x2(hi[0], hi[1])
    return lo[0] + Y * (lo[1] + Y * hi[0])

@inline
def fs_compress(state, scalar, tail, out):
    limbs = StackBuf(3)
    hint_f192_limbs(limbs, scalar)
    block = StackBuf(2)
    block[0] = pack64x2(limbs[0], limbs[1])
    block[1] = pack64x2(limbs[2], tail)
    assert scalar == limbs[0] + Y * (limbs[1] + Y * limbs[2])
    blake2s(state, block, out)
    return

@inline
def observe(state, scalar):
    out = StackBuf(2)
    fs_compress(state, scalar, 13, out)
    return out

def main():
    state = StackBuf(2)
    state[0] = f192(1, 2, 0)
    state[1] = f192(3, 4, 0)
    out = observe(state, f192(5, 6, 7))
    challenge = challenge_from_state(out)
    assert challenge == challenge
    return
"#;
    // `assert challenge == challenge` is the zkDSL keep-alive idiom: it forces
    // the value to be materialized. The assertion under test is that `execute`
    // runs the lowered helpers without a write-once memory conflict.
    let program = compile(&parse(src).expect("parse transcript helpers"));
    program.execute([F192::ZERO; 2]);
}
