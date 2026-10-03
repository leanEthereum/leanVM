//! The leanVM verifier's core (`cpu::Program::verify_core`) as a circuit: every check that depends on the
//! proof, leaving the claims on the program's and the circuits' fixed polynomials as wires the statement
//! exposes.

pub(crate) mod bus;
pub mod core;
pub mod flock;
pub mod math;
pub mod pcs;

use super::circuit::Ew;

/// `pcs::stack_open::StackClaim` with its point and value as wires.
#[derive(Clone, Debug)]
pub enum StackClaim {
    Point {
        offset: usize,
        low_point: Vec<Ew>,
        value: Ew,
    },
    Strided {
        offset: usize,
        slot: usize,
        stride_log: usize,
        point: Vec<Ew>,
        value: Ew,
    },
}

impl StackClaim {
    pub const fn value(&self) -> Ew {
        match self {
            Self::Point { value, .. } | Self::Strided { value, .. } => *value,
        }
    }
}

/// `flock::reduction::SliceClaim`: the `2^k_skip` slices of a packed witness at a point.
#[derive(Clone, Debug)]
pub struct SliceClaim {
    pub suffix_point: Vec<Ew>,
    pub s_hat_v: Vec<Ew>,
}

/// `pcs::stack_open::RingSwitchVerify`: one ring-switched region and its claims.
#[derive(Clone, Debug)]
pub struct RingRegion {
    pub offset: usize,
    pub qflock_vars: usize,
    pub claims: Vec<SliceClaim>,
}

/// `flock::lincheck::MatrixForm` and the value the core needs it to take.
#[derive(Clone, Debug)]
pub struct MatrixClaim {
    pub alpha: Ew,
    pub z_skip: Ew,
    pub x_inner_rest: Vec<Ew>,
    pub r_inner_rest: Vec<Ew>,
    pub s_hat_v: Vec<Ew>,
    pub value: Ew,
}

/// `cpu::deferred::ProgramPoint` and the value the core needs it to take.
#[derive(Clone, Debug)]
pub struct ProgramClaim {
    pub bytecode: Vec<Ew>,
    pub twist: Vec<Ew>,
    pub image_weight: Ew,
    pub image_point: Vec<Ew>,
    pub value: Ew,
}
