//! The optimal ate pairing's Miller loop, its lines taken as arkworks' `ark-bn254` takes them
//! (homogeneous projective steps on the D-type twist, Costello, Lange and Naehrig's formulas).
//!
//! A fixed point of G2 has its lines computed once, at compile time ([`prepare`]), and divided
//! by their first coefficient ([`normalize`]); the proof's point has its own computed as the
//! loop goes.
//!
//! A line's value may be scaled by any element of `F_p2`: the final exponentiation sends it to
//! one, since `p^2 - 1` divides `(p^12 - 1) / r`.

use crate::curve::{B2, G1Affine, G2Affine};
use crate::fp::Fp;
use crate::fp2::Fp2;
use crate::fp12::Fp12;

/// `6 x + 2` in signed binary, least significant digit first: the loop's count.
const ATE_LOOP_COUNT: [i8; 65] = [
    0, 0, 0, 1, 0, 1, 0, -1, 0, 0, -1, 0, 0, 0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 1, 0, -1, 0, 0, 0, 0, -1, 0, 0, 1, 0, -1,
    0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 1, 0, -1, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1, 0, 1, 1,
];

/// The lines of one point: a doubling per digit below the top, an addition per non-zero one,
/// and the two additions of `psi(Q)` and `-psi^2(Q)`.
pub const N_LINES: usize = {
    let mut n = ATE_LOOP_COUNT.len() - 1 + 2;
    let mut i = 0;
    while i < ATE_LOOP_COUNT.len() - 1 {
        if ATE_LOOP_COUNT[i] != 0 {
            n += 1;
        }
        i += 1;
    }
    n
};

/// A line through points of the twist, which at a point `(x, y)` of G1 is `c0 y + (c1 x + c2 v) w`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Line {
    pub c0: Fp2,
    pub c1: Fp2,
    pub c2: Fp2,
}

impl Line {
    const ZERO: Self = Self {
        c0: Fp2::ZERO,
        c1: Fp2::ZERO,
        c2: Fp2::ZERO,
    };

    /// `f` times this line's value at `p`.
    #[inline(always)]
    const fn evaluate(&self, f: &Fp12, p: &G1Affine) -> Fp12 {
        f.mul_by_034(&self.c0.mul_by_fp(&p.y), &self.c1.mul_by_fp(&p.x), &self.c2)
    }
}

/// A line divided by its `c0`: at `(x, y)` it is `1 + (c1 x / y + c2 / y v) w`, its value
/// divided by `c0 y`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NormalizedLine {
    pub c1: Fp2,
    pub c2: Fp2,
}

impl NormalizedLine {
    const ZERO: Self = Self {
        c1: Fp2::ZERO,
        c2: Fp2::ZERO,
    };

    /// `f` times this line's value at the point `p` stands for.
    #[inline(always)]
    const fn evaluate(&self, f: &Fp12, p: &Scaled) -> Fp12 {
        f.mul_by_34(&self.c1.mul_by_fp(&p.x_over_y), &self.c2.mul_by_fp(&p.y_inv))
    }
}

/// A point `(x, y)` of G1 as normalized lines take it: `x / y` and `1 / y`.
#[derive(Clone, Copy, Debug)]
pub struct Scaled {
    pub x_over_y: Fp,
    pub y_inv: Fp,
}

/// The loop's running point, `(X / Z, Y / Z)`.
struct Projective {
    x: Fp2,
    y: Fp2,
    z: Fp2,
}

impl Projective {
    const fn new(q: &G2Affine) -> Self {
        Self {
            x: q.x,
            y: q.y,
            z: Fp2::ONE,
        }
    }

    /// Double the point, and give the tangent: arkworks' formulas with the new point's
    /// coordinates scaled by 4, which spares the halvings.
    const fn double(&mut self) -> Line {
        let b = self.y.square();
        let c = self.z.square();
        let e = B2.mul(&c.double().add(&c));
        let f = e.double().add(&e);
        let h = self.y.add(&self.z).square().sub(&b.add(&c));
        let i = e.sub(&b);
        let j = self.x.square();
        let e_square = e.square();
        self.x = self.x.mul(&self.y).mul(&b.sub(&f)).double();
        self.y = b
            .add(&f)
            .square()
            .sub(&e_square.double().add(&e_square).double().double());
        self.z = b.mul(&h).double().double();
        Line {
            c0: h.neg(),
            c1: j.double().add(&j),
            c2: i,
        }
    }

    /// Add `q`, and give the line through both.
    const fn add(&mut self, q: &G2Affine) -> Line {
        let theta = self.y.sub(&q.y.mul(&self.z));
        let lambda = self.x.sub(&q.x.mul(&self.z));
        let c = theta.square();
        let d = lambda.square();
        let e = lambda.mul(&d);
        let f = self.z.mul(&c);
        let g = self.x.mul(&d);
        let h = e.add(&f).sub(&g.double());
        self.x = lambda.mul(&h);
        self.y = theta.mul(&g.sub(&h)).sub(&e.mul(&self.y));
        self.z = self.z.mul(&e);
        Line {
            c0: lambda,
            c1: theta.neg(),
            c2: theta.mul(&q.x).sub(&lambda.mul(&q.y)),
        }
    }
}

/// The lines of `q`, in the order the Miller loop takes them.
pub const fn prepare(q: &G2Affine) -> [Line; N_LINES] {
    let mut lines = [Line::ZERO; N_LINES];
    let mut n = 0;
    let mut r = Projective::new(q);
    let neg_q = q.neg();
    let mut i = ATE_LOOP_COUNT.len() - 1;
    while i > 0 {
        i -= 1;
        lines[n] = r.double();
        n += 1;
        match ATE_LOOP_COUNT[i] {
            1 => {
                lines[n] = r.add(q);
                n += 1;
            }
            -1 => {
                lines[n] = r.add(&neg_q);
                n += 1;
            }
            _ => {}
        }
    }
    let q1 = q.psi();
    let q2 = q1.psi().neg();
    lines[n] = r.add(&q1);
    lines[n + 1] = r.add(&q2);
    lines
}

/// Each line divided by its `c0`, with one inversion for all, by Montgomery's trick.
pub const fn normalize(lines: &[Line; N_LINES]) -> [NormalizedLine; N_LINES] {
    // prefix[n] is the product of the c0's before n.
    let mut prefix = [Fp2::ONE; N_LINES];
    let mut acc = Fp2::ONE;
    let mut n = 0;
    while n < N_LINES {
        prefix[n] = acc;
        acc = acc.mul(&lines[n].c0);
        n += 1;
    }
    let mut inverse = match acc.inverse() {
        Some(inverse) => inverse,
        None => panic!("no line has c0 = 0"),
    };
    let mut out = [NormalizedLine::ZERO; N_LINES];
    while n > 0 {
        n -= 1;
        let c0_inv = inverse.mul(&prefix[n]);
        inverse = inverse.mul(&lines[n].c0);
        out[n] = NormalizedLine {
            c1: lines[n].c1.mul(&c0_inv),
            c2: lines[n].c2.mul(&c0_inv),
        };
    }
    out
}

/// The Miller loop of one point of G1 and a prepared point of G2.
pub const fn miller_loop_prepared(p: &G1Affine, lines: &[Line; N_LINES]) -> Fp12 {
    let mut f = Fp12::ONE;
    let mut n = 0;
    let mut i = ATE_LOOP_COUNT.len() - 1;
    while i > 0 {
        i -= 1;
        if i != ATE_LOOP_COUNT.len() - 2 {
            f = f.square();
        }
        f = lines[n].evaluate(&f, p);
        n += 1;
        if ATE_LOOP_COUNT[i] != 0 {
            f = lines[n].evaluate(&f, p);
            n += 1;
        }
    }
    f = lines[n].evaluate(&f, p);
    lines[n + 1].evaluate(&f, p)
}

/// The product of the Miller loops of `(a, b)` and of each fixed pair, a point of G1 and the
/// normalized lines of a point of G2: one square of `f` per step for all of them.
pub fn multi_miller_loop(a: &G1Affine, b: &G2Affine, fixed: &[(Scaled, &[NormalizedLine; N_LINES])]) -> Fp12 {
    let mut f = Fp12::ONE;
    let mut n = 0;
    let mut r = Projective::new(b);
    let neg_b = b.neg();
    let mut step = |f: &mut Fp12, line: Line| {
        *f = line.evaluate(f, a);
        for (p, lines) in fixed {
            *f = lines[n].evaluate(f, p);
        }
        n += 1;
    };
    let mut i = ATE_LOOP_COUNT.len() - 1;
    while i > 0 {
        i -= 1;
        if i != ATE_LOOP_COUNT.len() - 2 {
            f = f.square();
        }
        step(&mut f, r.double());
        match ATE_LOOP_COUNT[i] {
            1 => step(&mut f, r.add(b)),
            -1 => step(&mut f, r.add(&neg_b)),
            _ => {}
        }
    }
    let b1 = b.psi();
    let b2 = b1.psi().neg();
    step(&mut f, r.add(&b1));
    step(&mut f, r.add(&b2));
    f
}
