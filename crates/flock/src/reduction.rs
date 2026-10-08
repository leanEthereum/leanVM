//! The circuit-agnostic half of flock: zerocheck then lincheck over batches of `2^k_log`-bit blocks.
//!
//! Every circuit of a batch shares every challenge.
//! Each circuit's R1CS validity reduces to one claim on its packed witness, ready for ring switching.
//! A circuit supplies only its block: its shape, and the walks behind its matrices.

use fiat_shamir::arith::Verifier;
use fiat_shamir::transcript::ProverState;
use pcs::ring_switch::SliceClaim;
use primitives::field::F192;

use crate::error::FlockError;
use crate::lincheck::{self, LincheckCircuit, LincheckInput, MatrixClaim, MatrixForm, QuirkyPoint};
use crate::witness::{Tables, Witness, packed_bytes};
use crate::zerocheck::multilinear::PackedWitness;
use crate::zerocheck::{self, K_SKIP, Padding, SkipDomain, ZerocheckInput};

#[cfg(test)]
mod tests;

// A claim's `2^K_SKIP` slices are a ring-switch claim on the packed witness only if they are one word's bits.
const _: () = assert!(
    K_SKIP == u64::BITS.ilog2() as usize,
    "the univariate skip must match the PCS packing width"
);

/// The fewest instances, as a base-two logarithm, that prove `n_blocks` of them.
///
/// The lincheck reads its witness in stripes of eight instances, so a batch holds at least eight.
///
/// # Panics
///
/// When `n_blocks` is zero.
pub const fn min_n_blocks_log(n_blocks: usize) -> usize {
    assert!(n_blocks >= 1, "a batch proves at least one instance");
    let n = if n_blocks > 8 { n_blocks } else { 8 };
    n.next_power_of_two().trailing_zeros() as usize
}

/// The instances before a packed witness's identical tail.
///
/// From the returned index on, every instance's `z` is the last one's, and so are its `A z` and `B z`.
///
/// # Panics
///
/// When an instance is not whole words.
pub fn live_instances(z: &[u64], k_log: usize) -> usize {
    assert!(k_log >= 6, "an instance is whole words");
    let words = 1usize << (k_log - 6);
    let Some(last) = z.rchunks_exact(words).next() else {
        return 0;
    };
    // Count the copies of the last instance just before it.
    let copies = z.rchunks_exact(words).skip(1).take_while(|w| *w == last).count();
    z.len() / words - 1 - copies
}

/// A circuit as the reduction sees it.
#[derive(Clone, Copy)]
pub struct Block<'a> {
    /// The base-two logarithm of the bits per instance.
    pub k_log: usize,

    /// The bits of an instance before its zero padding, which the prover skips.
    pub useful_bits: usize,

    /// The circuit's matrices, reached only by walking it.
    pub circuit: &'a dyn LincheckCircuit,
}

impl Block<'_> {
    /// What the verifier's replay reads of the circuit short of its matrices.
    pub fn shape(&self) -> Shape {
        Shape {
            k_log: self.k_log,
            const_pin_col: self.circuit.const_pin_col(),
        }
    }
}

/// What the verifier's replay reads of a circuit short of its matrices.
///
/// The matrices are left to the claim the replay returns, so the replay needs no built circuit.
/// Whoever settles that claim against the circuit holds the circuit to this shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    /// The base-two logarithm of the bits per instance.
    pub k_log: usize,

    /// The column of the constant wire, which the lincheck pins to one.
    pub const_pin_col: usize,
}

impl Shape {
    /// Whether a matrix form has the lengths a replay of a circuit of this shape gives.
    pub const fn fits(&self, form: &MatrixForm) -> bool {
        let rest = self.k_log - K_SKIP;
        form.s_hat_v.len() == 1 << K_SKIP && form.x_inner_rest.len() == rest && form.r_inner_rest.len() == rest
    }
}

/// What the verifier's replay leaves of one circuit.
///
/// Its elements are values, or whatever a verifier holds them as.
#[derive(Clone, Debug)]
pub struct ReductionReplay<E = F192> {
    /// The claim on the circuit's packed witness, which the commitment's opening settles.
    pub claim: SliceClaim<E>,

    /// The claim on the circuit's matrices, which whoever holds the circuit settles.
    pub matrices: MatrixClaim<E>,
}

/// One circuit's batch as the prover holds it: `2^n_blocks_log` instances of its block, and their witness.
///
/// The bits are borrowed apart from the factor tables.
/// A committed batch's bits are its column of the commitment, which the generators write in place.
#[derive(Clone, Copy)]
pub struct Instance<'a> {
    /// The circuit.
    pub block: Block<'a>,

    /// The base-two logarithm of the instance count.
    pub n_blocks_log: usize,

    /// The instances before the identical tail.
    ///
    /// The zerocheck sums the tail once while it binds variables inside an instance.
    /// Nothing of the proof depends on it: claiming no tail changes no word.
    pub live: usize,

    /// The witness bits.
    pub z: &'a [u64],

    /// `A z`.
    pub az: &'a [u64],

    /// `B z`.
    pub bz: &'a [u64],
}

impl<'a> Instance<'a> {
    /// A batch whose bits the caller holds apart from its factor tables.
    ///
    /// Its identical tail is read off its bits.
    pub fn new(block: Block<'a>, n_blocks_log: usize, z: &'a [u64], tables: &'a Tables) -> Self {
        Self {
            block,
            n_blocks_log,
            live: live_instances(z, block.k_log),
            z,
            az: &tables.az,
            bz: &tables.bz,
        }
    }

    /// A batch whose whole witness is `witness`.
    ///
    /// Its identical tail is read off its bits.
    pub fn of(block: Block<'a>, n_blocks_log: usize, witness: &'a Witness) -> Self {
        Self {
            block,
            n_blocks_log,
            live: live_instances(&witness.z, block.k_log),
            z: &witness.z,
            az: &witness.az,
            bz: &witness.bz,
        }
    }

    /// The base-two logarithm of the batch's bits.
    const fn m(&self) -> usize {
        self.block.k_log + self.n_blocks_log
    }

    /// The batch as the zerocheck reads it: the factor tables' bits, and where their padding lies.
    fn zerocheck_input(&self) -> ZerocheckInput<'a> {
        // Each table packs the batch's `2^m` bits 64 a word.
        let words = 1usize << (self.m() - 6);
        assert_eq!(self.z.len(), words, "wrong packed witness length");
        assert_eq!(self.az.len(), words, "wrong packed A z length");
        assert_eq!(self.bz.len(), words, "wrong packed B z length");
        ZerocheckInput {
            bits: PackedWitness {
                a: packed_bytes(self.az),
                b: packed_bytes(self.bz),
            },
            m: self.m(),
            padding: Padding {
                k_log: self.block.k_log,
                useful_bits: self.block.useful_bits,
                live_blocks: self.live,
            },
        }
    }

    /// The batch as the lincheck reads it, at the point its zerocheck claims are at.
    fn lincheck_input<'p>(&self, point: &'p QuirkyPoint) -> LincheckInput<'p>
    where
        'a: 'p,
    {
        LincheckInput {
            z: self.z,
            m: self.m(),
            k_log: self.block.k_log,
            k_skip: K_SKIP,
            useful_bits: self.block.useful_bits,
            circuit: self.block.circuit,
            x_ab: point,
        }
    }
}

/// The batched zerocheck then lincheck, leaving one claim on each circuit's packed witness.
///
/// - The zerocheck reduces `a b + c = 0` over every circuit's cube to claims on its `(a, b, c)` at one point.
/// - The lincheck reduces those, against the circuit's matrices, to the bit slices of its `z` at one point.
///
/// Every circuit shares every challenge.
/// No statement is bound here: the embedding protocol binds the circuits, the instance counts and the commitment first.
pub fn prove(instances: &[Instance<'_>], ps: &mut ProverState) -> Vec<SliceClaim> {
    // Phase 1: the zerocheck, each circuit's claims at its share of one point.
    let points: Vec<QuirkyPoint> = {
        let _span = tracing::info_span!("Zerocheck").entered();
        let inputs: Vec<ZerocheckInput<'_>> = instances.iter().map(Instance::zerocheck_input).collect();
        let claims = zerocheck::prove(&inputs, ps);
        (instances.iter().zip(&claims))
            .map(|(i, claim)| claim.point(i.block.k_log - K_SKIP))
            .collect()
    };

    // Phase 2: the lincheck at those points, each circuit's claim moving onto its witness.
    let _span = tracing::info_span!("Lincheck").entered();
    let inputs: Vec<LincheckInput<'_>> = (instances.iter().zip(&points))
        .map(|(i, point)| i.lincheck_input(point))
        .collect();
    let claims = lincheck::prove(&inputs, ps);

    // The witness's point: the lincheck's inner coordinates, then the zerocheck's outer ones.
    (claims.into_iter().zip(&points))
        .map(|(claim, point)| claim.slice_claim(&point.x_outer))
        .collect()
}

/// Replay the batched zerocheck and lincheck over circuits of `2^n` instances each, straight off the transcript.
///
/// Each circuit is its shape and `n`, and leaves two claims:
///
/// - one on its packed witness, which the commitment's opening settles;
/// - one on its matrices, which the built circuit settles.
///
/// The verifier's arithmetic is the native one or the recursion machine's rows, which run the same steps.
///
/// # Errors
///
/// The first stage that refuses the proof.
pub fn verify<V: Verifier>(circuits: &[(Shape, usize)], v: &mut V) -> Result<Vec<ReductionReplay<V::E>>, FlockError> {
    // Phase 1: the zerocheck's point and evaluations.
    let log_ns: Vec<usize> = circuits.iter().map(|(shape, n)| shape.k_log + n).collect();
    let zc = v
        .scope("zerocheck", |v| zerocheck::verify(&log_ns, v))
        .map_err(FlockError::Zerocheck)?;

    // Phase 2: the lincheck, each circuit's matrices left as a claim.
    let shapes: Vec<Shape> = circuits.iter().map(|&(shape, _)| shape).collect();
    let matrices = v
        .scope("lincheck", |v| {
            lincheck::verify_deferred(SkipDomain::FLOCK, &zc, &shapes, v)
        })
        .map_err(FlockError::Lincheck)?;

    // Each witness claim: the lincheck's inner coordinates, then the zerocheck's outer ones.
    Ok((matrices.into_iter().zip(&log_ns))
        .map(|(matrices, &m)| {
            let rest = matrices.form.r_inner_rest.len();
            let mut suffix_point = matrices.form.r_inner_rest.clone();
            suffix_point.extend_from_slice(&zc.mlv_challenges[rest..m - K_SKIP]);
            let claim = SliceClaim {
                suffix_point,
                s_hat_v: matrices.form.s_hat_v.clone(),
            };
            ReductionReplay { claim, matrices }
        })
        .collect())
}
