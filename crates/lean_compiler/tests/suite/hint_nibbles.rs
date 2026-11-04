//! `hint_decompose_nibbles_exponent(digits, x, shift, ndigits, rev)`: computed advice writing the
//! base-16 digits of `n >> s` (`x = g^n`, `shift = g^s`) as g-powers. The recursion guest's
//! selectors read a nibble's eq factor and its share of `g^offset` through such a digit, so the
//! advice is unconstrained and the caller's checks are what make it sound: each digit
//! range-checked below its table size, and the shares' product pinned to `x`.

use lean_compiler::{compile, parse};
use leanvm_core::cpu::{prove, verify};
use primitives::field::{F64, F192, g_pow};

/// The digits the advice writes, low first, each published as `g^d`: plain and bit-reversed,
/// with and without a shift.
#[test]
fn nibble_advice_writes_the_digits() {
    let src = "\
def main():
    x = hint_witness(\"x\")
    s = hint_witness(\"s\")
    digits = StackBuf(3)
    hint_decompose_nibbles_exponent(digits, x, s, 3, REV)
    p = 1
    p[1] = digits[0]
    p[GEN] = digits[1] * digits[2] ** 17
    return
";
    let rev4 = |d: usize| (0..4).fold(0, |r, t| r | ((d >> t) & 1) << (3 - t));
    for (n, s, rev) in [
        (0x2b7usize, 0usize, 0usize),
        (0x2b7, 0, 1),
        (0x5c3 << 3, 3, 0),
        (0x5c3 << 3, 3, 1),
        (0, 0, 0),
    ] {
        let mut program = compile(&parse(&src.replace("REV", &rev.to_string())).expect("parse"));
        program.set_witness("x", vec![vec![F192::from(g_pow(n))]]);
        program.set_witness("s", vec![vec![F192::from(g_pow(s))]]);
        let d: Vec<usize> = (0..3)
            .map(|j| ((n >> s) >> (4 * j)) & 15)
            .map(|d| if rev == 1 { rev4(d) } else { d })
            .collect();
        // digits[1] · digits[2]^17
        let want = [F192::from(g_pow(d[0])), F192::from(g_pow(d[1] + 17 * d[2]))];
        let (proof, _) = prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE).unwrap();
        verify(&program, &want, &proof).unwrap_or_else(|_| panic!("n={n:#x} s={s} rev={rev}"));
    }
}

/// The checks a selector runs on the digits, here on digits a dishonest prover supplies through
/// a witness stream: every digit range-checked below 16, and `Π g^(d_j·16^j) = x`.
const CHECKED: &str = "\
def main():
    x = hint_witness(\"x\")
    digits = StackBuf(2)
    hint_witness(digits[0:2], \"digits\")
    RANGE
    hi = digits[1] ** 16
    assert digits[0] * hi == x
    p = 1
    p[1] = x
    p[GEN] = 1
    return
";

fn run(range: bool, digits: [usize; 2]) -> bool {
    let range = if range {
        "assert log(digits[0]) < 16\n    assert log(digits[1]) < 16"
    } else {
        ""
    };
    let mut program = compile(&parse(&CHECKED.replace("RANGE", range)).expect("parse"));
    let x = F192::from(g_pow(0x21));
    program.set_witness("x", vec![vec![x]]);
    program.set_witness("digits", vec![digits.iter().map(|&d| F192::from(g_pow(d))).collect()]);
    let want = [x, F192::from(F64::ONE)];
    match prove(&program, want, leanvm_core::pcs::TEST_LOG_INV_RATE) {
        Ok((proof, _)) => verify(&program, &want, &proof).is_ok(),
        Err(_) => false,
    }
}

/// `0x21` is `1 + 16·2`, and also `17 + 16·1`: the product alone accepts the second split, whose
/// low digit would read past its nibble's table; the range check refuses it.
#[test]
fn an_out_of_range_digit_is_refused() {
    assert!(run(true, [1, 2]), "the honest digits pass");
    assert!(
        run(false, [17, 1]),
        "without the range check the forged split passes the product"
    );
    assert!(!run(true, [17, 1]), "the range check refuses the forged split");
    assert!(!run(true, [2, 2]), "a wrong digit fails the product");
}
