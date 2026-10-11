//! The claims a node reduces: on the dense polynomials, and on the flock circuits' matrices.
//!
//! Every claim is generic over its elements: values for the prover, wires for the rows.

use crate::class_flock::FlockId;
use crate::cpu::Claim;
use flock::lincheck::MatrixForm;

/// The polynomials the leaves and the tree's circuits fix, on which tree proofs carry claims.
///
/// A tree whose leaves fix no such polynomial has none: no claim is ever made on it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DensePoly {
    /// The leaves' program's stacked bytecode table, if RISC-V proofs are leaves.
    Bytecode,
    /// That program's RAM image, zero padded to a power of two.
    Image,
    /// The leaves' fixed polynomial `W_leaf`, if proofs of recursion circuits are leaves: each such circuit's fixed columns, stacked.
    Leaf,
    /// The nodes' fixed polynomial `W_node`: each kind's circuit's fixed columns, stacked in the order of the kinds' codes.
    Fixed,
}

/// Public coordinates of a point: `len` bits, lowest first.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Bits {
    /// The bits, as an integer.
    pub(crate) value: usize,
    /// How many there are.
    pub(crate) len: usize,
}

/// One claim on a dense polynomial `P`, at the shared prefix, then public bits, then the kind's bits: `s P(low, bits, top) = s v`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DenseTerm<E> {
    /// How many of the shared prefix's coordinates the point starts with.
    pub(crate) n_low: usize,
    /// The public coordinates after them.
    pub(crate) bits: Bits,
    /// The last coordinates, a child's kind's bits lowest first, if any.
    pub(crate) top: Vec<E>,
    /// A factor both sides carry, one when absent: a zero scale makes the claim vacuous.
    pub(crate) scale: Option<E>,
    /// The claimed value.
    pub(crate) value: E,
}

/// Claims on one dense polynomial at points sharing a prefix, each batched as a claim of its own.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DenseClaim<E> {
    /// The polynomial.
    pub(crate) poly: DensePoly,
    /// The prefix every claim's point starts with a part of.
    pub(crate) low: Vec<E>,
    /// The claims.
    pub(crate) terms: Vec<DenseTerm<E>>,
}

/// A matrix's coefficient in a matrix claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Coefficient<E> {
    /// The matrix is not in the claim.
    Zero,
    /// The matrix itself.
    One,
    /// The matrix scaled by this element.
    Of(E),
}

/// A matrix claim's row weight `u`: flock's skip weight at a zerocheck point, or `eq(p, .)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RowWeight<E> {
    /// Lagrange weights at `z` over the skip domain, then an eq weight over the other variables.
    Skip { z: E, rest: Vec<E> },
    /// The eq weight at a point.
    Point(Vec<E>),
}

/// A matrix claim's column weight `w`: the lincheck's slices, then an eq weight, or `eq(p, .)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ColWeight<E> {
    /// The slices on the low variables, then an eq weight over the other variables.
    Slices { slices: Vec<E>, rest: Vec<E> },
    /// The eq weight at a point.
    Point(Vec<E>),
}

/// `u^T (a A + b B) w = v` on a flock circuit's matrices: `u` and `w` its weights, `a` and `b` its coefficients.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MatrixClaim<E> {
    /// The flock circuit.
    pub(crate) circuit: FlockId,
    /// The row weight `u`.
    pub(crate) row: RowWeight<E>,
    /// The column weight `w`.
    pub(crate) col: ColWeight<E>,
    /// The coefficients `a` and `b`.
    pub(crate) coefficients: [Coefficient<E>; 2],
    /// The claimed value.
    pub(crate) value: E,
}

/// What a node reduces: the values its transcript binds first, then its dense and matrix claims.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NodeClaims<E> {
    /// Each verified proof's final state and every hint its claims rest on, which every challenge follows.
    pub(crate) bound: Vec<E>,
    /// The claims on the dense polynomials.
    pub(crate) dense: Vec<DenseClaim<E>>,
    /// The claims on the flock circuits' matrices.
    pub(crate) matrices: Vec<MatrixClaim<E>>,
}

impl DensePoly {
    /// How many dense polynomials there are.
    pub const COUNT: usize = 4;

    /// Every dense polynomial, in statement order.
    pub const ALL: [Self; Self::COUNT] = [Self::Bytecode, Self::Image, Self::Leaf, Self::Fixed];
}

impl Bits {
    /// No coordinates.
    pub(crate) const NONE: Self = Self { value: 0, len: 0 };
}

impl<E: Copy> DenseTerm<E> {
    /// The same claim, each element mapped by `f`.
    fn map<T>(&self, f: &mut impl FnMut(E) -> T) -> DenseTerm<T> {
        DenseTerm {
            n_low: self.n_low,
            bits: self.bits,
            top: self.top.iter().map(|&x| f(x)).collect(),
            scale: self.scale.map(&mut *f),
            value: f(self.value),
        }
    }
}

impl<E: Copy> DenseClaim<E> {
    /// `s P(point) = s v`, the scale `s` one when absent.
    pub(crate) fn at(poly: DensePoly, point: Vec<E>, scale: Option<E>, value: E) -> Self {
        let n_low = point.len();
        Self {
            poly,
            low: point,
            terms: vec![DenseTerm {
                n_low,
                bits: Bits::NONE,
                top: Vec::new(),
                scale,
                value,
            }],
        }
    }

    /// The same claims, each element mapped by `f`.
    fn map<T>(&self, f: &mut impl FnMut(E) -> T) -> DenseClaim<T> {
        DenseClaim {
            poly: self.poly,
            low: self.low.iter().map(|&x| f(x)).collect(),
            terms: self.terms.iter().map(|t| t.map(f)).collect(),
        }
    }
}

impl<E: Copy> Coefficient<E> {
    /// The same coefficient, its element mapped by `f`.
    fn map<T>(self, f: &mut impl FnMut(E) -> T) -> Coefficient<T> {
        match self {
            Self::Zero => Coefficient::Zero,
            Self::One => Coefficient::One,
            Self::Of(x) => Coefficient::Of(f(x)),
        }
    }
}

impl<E: Copy> RowWeight<E> {
    /// The same weight, each element mapped by `f`.
    fn map<T>(&self, f: &mut impl FnMut(E) -> T) -> RowWeight<T> {
        match self {
            Self::Skip { z, rest } => RowWeight::Skip {
                z: f(*z),
                rest: rest.iter().map(|&x| f(x)).collect(),
            },
            Self::Point(p) => RowWeight::Point(p.iter().map(|&x| f(x)).collect()),
        }
    }
}

impl<E: Copy> ColWeight<E> {
    /// The same weight, each element mapped by `f`.
    fn map<T>(&self, f: &mut impl FnMut(E) -> T) -> ColWeight<T> {
        match self {
            Self::Slices { slices, rest } => ColWeight::Slices {
                slices: slices.iter().map(|&x| f(x)).collect(),
                rest: rest.iter().map(|&x| f(x)).collect(),
            },
            Self::Point(p) => ColWeight::Point(p.iter().map(|&x| f(x)).collect()),
        }
    }
}

impl<E: Copy> MatrixClaim<E> {
    /// The claim a lincheck leaves: `u^T (A + alpha B) w`, at the zerocheck's skip point and the lincheck's sliced point.
    pub(crate) fn fresh(circuit: FlockId, claim: &Claim<MatrixForm<E>, E>) -> Self {
        let form = &claim.point;
        Self {
            circuit,
            row: RowWeight::Skip {
                z: form.z_skip,
                rest: form.x_inner_rest.clone(),
            },
            col: ColWeight::Slices {
                slices: form.s_hat_v.clone(),
                rest: form.r_inner_rest.clone(),
            },
            coefficients: [Coefficient::One, Coefficient::Of(form.alpha)],
            value: claim.value,
        }
    }

    /// A child's claims on both matrices of a circuit of `k` variables, at its prefixes of the child's points.
    pub(crate) fn carried(circuit: FlockId, k: usize, rows: &[E], cols: &[E], values: [E; 2]) -> [Self; 2] {
        let claim = |coefficients, value| Self {
            circuit,
            row: RowWeight::Point(rows[..k].to_vec()),
            col: ColWeight::Point(cols[..k].to_vec()),
            coefficients,
            value,
        };
        [
            claim([Coefficient::One, Coefficient::Zero], values[0]),
            claim([Coefficient::Zero, Coefficient::One], values[1]),
        ]
    }

    /// The same claim, each element mapped by `f`.
    fn map<T>(&self, f: &mut impl FnMut(E) -> T) -> MatrixClaim<T> {
        MatrixClaim {
            circuit: self.circuit,
            row: self.row.map(f),
            col: self.col.map(f),
            coefficients: self.coefficients.map(|c| c.map(f)),
            value: f(self.value),
        }
    }
}

impl<E> Default for NodeClaims<E> {
    fn default() -> Self {
        Self {
            bound: Vec::new(),
            dense: Vec::new(),
            matrices: Vec::new(),
        }
    }
}

impl<E: Copy> NodeClaims<E> {
    /// The same claims, each element mapped by `f`.
    pub(crate) fn map<T>(&self, mut f: impl FnMut(E) -> T) -> NodeClaims<T> {
        NodeClaims {
            bound: self.bound.iter().map(|&x| f(x)).collect(),
            dense: self.dense.iter().map(|c| c.map(&mut f)).collect(),
            matrices: self.matrices.iter().map(|c| c.map(&mut f)).collect(),
        }
    }
}
