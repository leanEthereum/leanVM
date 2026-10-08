//! The circuit-agnostic half of Flock: zerocheck then lincheck over batches of
//! `2^k_log`-bit blocks, one batch per circuit and every circuit under shared
//! challenges, reducing each circuit's R1CS validity to ONE claim on its packed
//! witness, packaged for ring switching. A circuit supplies only its [`Block`]:
//! the shape, and the walks behind its [`LincheckCircuit`].

use crate::lincheck::{self, LincheckCircuit, LincheckClaim, LincheckInput, MatrixClaim, MatrixForm, QuirkyPoint};
use crate::verifier::FlockError;
use crate::witness::{Tables, Witness, packed_bytes};
use crate::zerocheck::multilinear::PackedWitness;
use crate::zerocheck::{self, K_SKIP, PaddingSpec, SkipDomain, ZerocheckClaim, ZerocheckInput};
use fiat_shamir::arith::Verifier;
use fiat_shamir::transcript::ProverState;
use pcs::ring_switch::SliceClaim;
use primitives::field::{F64, F192};

// A claim's `2^K_SKIP` slices are a ring-switch claim on `q_flock` only if that
// matches the packing width.
const _: () = assert!(
    K_SKIP == F64::DEGREE.ilog2() as usize,
    "the univariate skip must match the PCS packing width"
);

/// Minimum `n_blocks_log` needed to prove `n_blocks` instances, subject to the
/// lincheck floor of `n_blocks_log ≥ 3` (`n_outer ≥ 8`).
pub const fn min_n_blocks_log(n_blocks: usize) -> usize {
    assert!(n_blocks >= 1, "n_blocks must be ≥ 1");
    let n = if n_blocks > 8 { n_blocks } else { 8 };
    n.next_power_of_two().trailing_zeros() as usize
}

/// The instances before a packed witness's identical tail: from the returned index on, every
/// instance's `z` is the last one's, and so are its `A·z` and `B·z`.
pub fn live_instances(z: &[u64], k_log: usize) -> usize {
    assert!(k_log >= 6, "an instance is whole words");
    let words = 1usize << (k_log - 6);
    let Some(last) = z.rchunks_exact(words).next() else {
        return 0;
    };
    let copies = z.rchunks_exact(words).skip(1).take_while(|w| *w == last).count();
    z.len() / words - 1 - copies
}

/// A circuit as the reduction sees it: `2^k_log` witness bits per instance, of
/// which `[useful_bits, 2^k_log)` are zero padding the prover skips.
#[derive(Clone, Copy)]
pub struct Block<'a> {
    pub k_log: usize,
    pub useful_bits: usize,
    pub circuit: &'a dyn LincheckCircuit,
}

/// What the verifier's replay reads of a circuit short of its matrices.
///
/// The matrices are left to the claim the replay returns, so the replay needs no built circuit.
/// Whoever settles that claim against the circuit holds the circuit to this shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Shape {
    /// The base-two logarithm of the witness bits per instance.
    pub k_log: usize,
    /// The column of the constant wire, which lincheck pins to one.
    pub const_pin_col: usize,
}

/// What the verifier's replay leaves of one circuit.
///
/// Its elements are values, or whatever a verifier holds them as.
#[derive(Clone, Debug)]
pub struct ReductionReplay<E = F192> {
    /// The claim on the circuit's packed witness, which the PCS discharges.
    pub claim: SliceClaim<E>,
    /// The claim on the circuit's matrices, which whoever holds the circuit settles.
    pub matrices: MatrixClaim<E>,
}

/// One circuit's batch as the prover holds it: `2^n_blocks_log` instances of its block, and their witness.
///
/// `z` is borrowed apart from the rest: a committed batch's `z` is its committed column, which the `_into` generators
/// write in place.
///
/// The instances from `live` on are copies of one instance, which the zerocheck sums once while it binds bits inside an instance.
/// Nothing of the proof depends on `live`: `1 << n_blocks_log` claims no such tail.
#[derive(Clone, Copy)]
pub struct Instance<'a> {
    pub block: Block<'a>,
    pub n_blocks_log: usize,
    pub live: usize,
    /// The witness bits.
    pub z: &'a [u64],
    /// `A·z`.
    pub az: &'a [u64],
    /// `B·z`.
    pub bz: &'a [u64],
    /// `z` again in lincheck's byte stripes.
    pub stripes: &'a [u8],
}

impl<'a> Instance<'a> {
    /// A batch whose `z` the caller holds apart, the rest in `tables`; its identical tail is read off `z`.
    pub fn new(block: Block<'a>, n_blocks_log: usize, z: &'a [u64], tables: &'a Tables) -> Self {
        Self {
            block,
            n_blocks_log,
            live: live_instances(z, block.k_log),
            z,
            az: &tables.az,
            bz: &tables.bz,
            stripes: &tables.stripes,
        }
    }

    /// A batch whose whole witness is `witness`; its identical tail is read off its `z`.
    pub fn of(block: Block<'a>, n_blocks_log: usize, witness: &'a Witness) -> Self {
        Self {
            block,
            n_blocks_log,
            live: live_instances(&witness.z, block.k_log),
            z: &witness.z,
            az: &witness.az,
            bz: &witness.bz,
            stripes: &witness.stripes,
        }
    }
}

/// The lincheck input point carried over from the zerocheck claim: the
/// univariate-skip coordinate, then the multilinear challenges split at
/// `inner_rest_len` into the inner-rest and outer halves.
fn x_ab_of(zc: &ZerocheckClaim, inner_rest_len: usize) -> QuirkyPoint {
    QuirkyPoint {
        z_skip: zc.z,
        x_inner_rest: zc.mlv_challenges[..inner_rest_len].to_vec(),
        x_outer: zc.mlv_challenges[inner_rest_len..].to_vec(),
    }
}

/// The claim the reduction leaves for the PCS: lincheck's output point, whose
/// 64 slice values are `lc.s_hat_v`. Prover and verifier must derive it
/// identically, so they share this one derivation.
fn reduction_claim(lc: &LincheckClaim, x_outer: &[F192]) -> SliceClaim {
    let mut suffix_point = lc.r_inner_rest.clone();
    suffix_point.extend_from_slice(x_outer);
    SliceClaim {
        suffix_point,
        s_hat_v: lc.s_hat_v.clone(),
    }
}

/// The batched zerocheck then lincheck, leaving one claim on each circuit's committed witness.
///
/// - The zerocheck reduces `a·b ⊕ c = 0` over every circuit's cube to claims on its `(â, b̂, ĉ)` at one point.
/// - The lincheck reduces those to the `2^k_skip` bit slices of each circuit's `z` at one point, against its matrices.
///
/// Every circuit shares every challenge.
pub fn prove(instances: &[Instance<'_>], ps: &mut ProverState) -> Vec<SliceClaim> {
    // No statement is bound here: the embedding protocol binds the circuits, the instance counts and the commitment
    // before any challenge.
    let x_abs: Vec<QuirkyPoint> = {
        let _span = tracing::info_span!("Zerocheck").entered();
        let inputs: Vec<ZerocheckInput<'_>> = instances
            .iter()
            .map(|i| {
                let m = i.block.k_log + i.n_blocks_log;
                // The fused generator packs 64 Boolean coordinates per word.
                let packed_len = 1usize << (m - 6);
                assert_eq!(i.z.len(), packed_len, "wrong packed witness length");
                assert_eq!(i.az.len(), packed_len, "wrong packed A·z length");
                assert_eq!(i.bz.len(), packed_len, "wrong packed B·z length");
                ZerocheckInput {
                    bits: PackedWitness {
                        a: packed_bytes(i.az),
                        b: packed_bytes(i.bz),
                    },
                    // `C = I`, so `c = z`.
                    c: packed_bytes(i.z),
                    m,
                    padding: PaddingSpec {
                        k_log: i.block.k_log,
                        useful_bits_per_block: i.block.useful_bits,
                        live_blocks: i.live,
                    },
                }
            })
            .collect();
        let claims = zerocheck::prove(&inputs, ps);
        (instances.iter().zip(&claims))
            .map(|(i, zc)| x_ab_of(zc, i.block.k_log - K_SKIP))
            .collect()
    };

    let _span = tracing::info_span!("Lincheck").entered();
    let inputs: Vec<LincheckInput<'_>> = (instances.iter().zip(&x_abs))
        .map(|(i, x_ab)| {
            let m = i.block.k_log + i.n_blocks_log;
            assert_eq!(i.stripes.len(), (1usize << m) / 8, "wrong lincheck stripe length");
            LincheckInput {
                z_packed: i.stripes,
                m,
                k_log: i.block.k_log,
                k_skip: K_SKIP,
                useful_bits: i.block.useful_bits,
                circuit: i.block.circuit,
                x_ab,
            }
        })
        .collect();
    let claims = lincheck::prove(&inputs, ps);
    (claims.iter().zip(&x_abs))
        .map(|(lc, x_ab)| reduction_claim(lc, &x_ab.x_outer))
        .collect()
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

impl Shape {
    /// Whether a matrix form has the lengths a replay of a circuit of this shape gives.
    pub const fn fits(&self, form: &MatrixForm) -> bool {
        let rest = self.k_log - K_SKIP;
        form.s_hat_v.len() == 1 << K_SKIP && form.x_inner_rest.len() == rest && form.r_inner_rest.len() == rest
    }
}

/// **Verifier.** Replay the batched zerocheck and lincheck over circuits of
/// `2^n_blocks_log` instances each straight off the shared transcript stream,
/// recovering one evaluation claim on each circuit's committed witness, which
/// the PCS then discharges, and each circuit's claim on its matrices.
///
/// It reads only the circuits' shapes: their matrices' forms are left as claims
/// for the built circuits to settle.
///
/// The verifier's arithmetic is the native one or the recorder of a verifier program, which run the same steps.
///
/// # Errors
///
/// Returns the first stage that refuses the proof.
pub fn verify<V: Verifier>(circuits: &[(Shape, usize)], v: &mut V) -> Result<Vec<ReductionReplay<V::E>>, FlockError> {
    let log_ns: Vec<usize> = circuits.iter().map(|(shape, n)| shape.k_log + n).collect();
    let zc = v
        .scope("zerocheck", |v| zerocheck::verify(&log_ns, v))
        .map_err(FlockError::Zerocheck)?;
    let shapes: Vec<Shape> = circuits.iter().map(|&(shape, _)| shape).collect();
    let matrices = v
        .scope("lincheck", |v| {
            lincheck::verify_deferred(SkipDomain::FLOCK, &zc, &shapes, v)
        })
        .map_err(FlockError::Lincheck)?;
    Ok((matrices.into_iter().zip(&log_ns))
        .map(|(matrices, &m)| {
            // The witness's point: the lincheck's inner coordinates, then the zerocheck's outer ones.
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
