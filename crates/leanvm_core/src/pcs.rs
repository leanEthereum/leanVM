//! Base-field witness commitments with one shared opening for point and circuit-validity claims.
//!
//! Witness words lie in K = GF(2^64), and challenges lie in E = GF(2^192).
//! The opening proves an inner product against a weight the verifier reconstructs.
//!
//! The immutable commitment includes the root, shape, original transcript context, and one out-of-domain point/value anchor.
//! Each opening binds that complete record before batching the point and circuit-validity claims.
//! The security-bit constant is a parameter-selection target, not a proved concrete security level for the deployed hash and Fiat-Shamir composition (doc/leanvm, Annex B).

use crate::witness::StackShape;
use fiat_shamir::transcript::ProverState;
use pcs::stack::{CommittedStack, StackCommitment, Statement};
use pcs::verifier::OpeningVerifier;
use pcs::whir::WhirError;
use pcs::whir::config::ConfigError;
use primitives::field::F64;
use thiserror::Error;

pub(crate) use pcs::ring_switch::{RingSwitch, SliceClaim};
pub(crate) use pcs::stack::StackClaim;
pub(crate) use pcs::whir::INITIAL_FOLDING_FACTOR as LOG_BATCH;
pub use pcs::whir::{MAX_LOG_N as MAX_MU, MIN_LOG_N as MIN_MU};

/// The proof's parameter-selection target, in bits.
///
/// WHIR parameters and the bus soundness check share this design target.
pub const SECURITY_BITS: u32 = pcs::whir::SECURITY_BITS as u32;

/// A supported commitment rate, represented by the base-two logarithm of its inverse.
///
/// A lower rate trades more prover work for a smaller proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Rate(u8);

// Every supported inverse-rate logarithm fits in the public representation.
const _: () = assert!(pcs::whir::MAX_LOG_INV_RATE <= u8::MAX as usize);

impl Rate {
    /// The highest supported rate, favoring prover speed.
    pub const MIN: Self = Self(pcs::whir::MIN_LOG_INV_RATE as u8);

    /// The lowest supported rate, favoring proof size.
    pub const MAX: Self = Self(pcs::whir::MAX_LOG_INV_RATE as u8);

    /// Constructs a supported rate from its inverse's base-two logarithm.
    ///
    /// # Errors
    ///
    /// Returns the rejected logarithm when the rate is unsupported.
    pub const fn new(log_inv_rate: u8) -> Result<Self, InvalidRate> {
        // The tabulated security profile supports one contiguous range of rates.
        if Self::MIN.0 <= log_inv_rate && log_inv_rate <= Self::MAX.0 {
            Ok(Self(log_inv_rate))
        } else {
            Err(InvalidRate { log_inv_rate })
        }
    }

    /// The base-two logarithm of the inverse rate.
    #[must_use]
    pub const fn log_inv_rate(self) -> u8 {
        self.0
    }
}

/// An unsupported commitment rate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Error)]
#[error("log_inv_rate {log_inv_rate} is not in {min}..={max}", min = Rate::MIN.0, max = Rate::MAX.0)]
pub struct InvalidRate {
    /// The rejected inverse-rate logarithm.
    pub log_inv_rate: u8,
}

/// A witness whose dimensions or length cannot be committed or opened.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub(crate) enum WitnessError {
    /// A witness dimension outside the supported opening profile.
    #[error(transparent)]
    Config(#[from] ConfigError),
    /// A lane count outside the initial commitment's leaf width.
    #[error("{n_lanes} committed lanes, expected 1..={max}")]
    LaneCount {
        /// The supplied lane count.
        n_lanes: usize,
        /// The largest supported lane count.
        max: usize,
    },
    /// A word count different from the committed shape.
    #[error("witness has {got} words, expected {expected}")]
    Length {
        /// The word count required by the committed shape.
        expected: usize,
        /// The supplied word count.
        got: usize,
    },
}

/// The encoded witness and authentication tree retained for opening.
///
/// The caller retains the witness words, avoiding a second full-witness allocation.
pub(crate) struct Committed {
    /// The codeword, tree, immutable anchored record and opening parameters.
    stack: CommittedStack,
    /// The full witness dimension and the number of lanes actually encoded.
    shape: StackShape,
}

impl Committed {
    /// Encodes the witness and binds its Merkle root before any dependent challenge.
    ///
    /// Only whole lanes containing data are supplied.
    /// Omitted lanes are zero, giving the same root as a full padded witness.
    ///
    /// # Errors
    ///
    /// Returns an error for an unsupported dimension, an invalid lane count, or a mismatched word count.
    pub(crate) fn new(
        ps: &mut ProverState,
        witness: &[F64],
        shape: StackShape,
        rate: Rate,
    ) -> Result<Self, WitnessError> {
        // Validate the dimension before shifting lengths or allocating the codeword.
        let log_inv_rate = usize::from(rate.log_inv_rate());
        let config = pcs::whir::config_for_rate(shape.mu, log_inv_rate)?;
        let max = 1usize << config.initial_k();
        if !(1..=max).contains(&shape.n_lanes) {
            return Err(WitnessError::LaneCount {
                n_lanes: shape.n_lanes,
                max,
            });
        }
        let expected = shape.committed_len();
        if witness.len() != expected {
            return Err(WitnessError::Length {
                expected,
                got: witness.len(),
            });
        }

        // The codeword and tree use the same parameters retained for opening.
        let stack = CommittedStack::new(ps, witness, shape.mu, config);
        Ok(Self { stack, shape })
    }

    /// Proves the point evaluations and ring-switched circuit-validity claims together.
    ///
    /// Claim values must already be bound by the transcript or the public statement.
    /// The witness must contain the same words supplied at commitment.
    ///
    /// # Errors
    ///
    /// Returns the expected and supplied word counts if the witness length differs from the commitment.
    ///
    /// # Panics
    ///
    /// Panics if the claims are malformed.
    pub(crate) fn open(
        &self,
        ps: &mut ProverState,
        witness: &[F64],
        points: &[StackClaim],
        rings: &[RingSwitch],
    ) -> Result<(), WitnessError> {
        // A different lane count would change both the encoded rows and their authentication paths.
        let expected = self.shape.committed_len();
        if witness.len() != expected {
            return Err(WitnessError::Length {
                expected,
                got: witness.len(),
            });
        }

        // Values are transcript-bound or public, points are challenges or constants, and offsets are public.
        // The opening samples batching challenges without observing those claims again.
        self.stack.open(ps, witness, Statement { points, rings });
        Ok(())
    }
}

/// An immutable anchored commitment and its validated opening configuration.
pub(crate) struct Commitment<E, R, K> {
    stack: StackCommitment<E, R, K>,
}

impl<E: Copy, R: Copy, K: Copy> Commitment<E, R, K> {
    /// Reads and binds the complete commitment before any opening statement.
    ///
    /// # Errors
    ///
    /// Returns an invalid public shape, incompatible commitment context, or malformed stream.
    pub(crate) fn read<V: OpeningVerifier<E = E, Root = R, K = K>>(
        v: &mut V,
        shape: StackShape,
        rate: Rate,
    ) -> Result<Self, WhirError> {
        let log_inv_rate = usize::from(rate.log_inv_rate());
        let config = pcs::whir::config_for_rate(shape.mu, log_inv_rate)?;
        let stack = StackCommitment::receive(v, shape.mu, shape.n_lanes, config)?;
        Ok(Self { stack })
    }

    /// Checks the shared opening of point evaluations and circuit-validity claims.
    ///
    /// The same arithmetic runs natively and in recursion rows.
    /// Claim values must already be bound by the transcript or the public statement.
    ///
    /// # Errors
    ///
    /// Returns an error for an unsupported witness size, malformed claims, or an invalid opening.
    pub(crate) fn verify<V: OpeningVerifier<E = E, Root = R, K = K>>(
        &self,
        v: &mut V,
        points: &[StackClaim<V::E>],
        rings: &[RingSwitch<V::E>],
    ) -> Result<(), WhirError>
    where
        E: PartialEq,
    {
        self.stack.verify(v, Statement { points, rings })
    }
}

#[cfg(test)]
mod tests {
    use super::{Committed, InvalidRate, LOG_BATCH, MAX_MU, MIN_MU, Rate, WitnessError};
    use crate::witness::StackShape;
    use fiat_shamir::transcript::ProverState;
    use pcs::whir::config::ConfigError;
    use primitives::field::F64;

    #[test]
    fn only_supported_rates_can_be_constructed() {
        // Exhaust all 256 representations, including both supported endpoints and their neighbors.
        for log_inv_rate in u8::MIN..=u8::MAX {
            let rate = Rate::new(log_inv_rate);
            if (Rate::MIN.log_inv_rate()..=Rate::MAX.log_inv_rate()).contains(&log_inv_rate) {
                assert_eq!(rate.expect("a supported rate").log_inv_rate(), log_inv_rate);
            } else {
                // The caller receives the exact rejected value for diagnostics.
                assert_eq!(rate, Err(InvalidRate { log_inv_rate }));
            }
        }
    }

    #[test]
    fn malformed_witnesses_are_refused_before_root_binding() {
        let lane_words = 1usize << (MIN_MU - LOG_BATCH);
        let max_lanes = 1usize << LOG_BATCH;

        // Mutation: dimensions outside the configured window, before any shift or codeword allocation.
        let sizes = [MIN_MU - 1, MAX_MU + 1, usize::MAX].map(|mu| {
            (
                StackShape { mu, n_lanes: 1 },
                0,
                WitnessError::Config(ConfigError::SizeOutOfRange { log_n: mu }),
            )
        });
        // Mutation: lane counts outside a leaf and incomplete lane buffers.
        let lanes = [0, max_lanes + 1, usize::MAX].map(|n_lanes| {
            (
                StackShape { mu: MIN_MU, n_lanes },
                0,
                WitnessError::LaneCount {
                    n_lanes,
                    max: max_lanes,
                },
            )
        });
        let lengths = [0, lane_words - 1, lane_words + 1].map(|got| {
            (
                StackShape { mu: MIN_MU, n_lanes: 1 },
                got,
                WitnessError::Length {
                    expected: lane_words,
                    got,
                },
            )
        });
        for (shape, words, error) in sizes.into_iter().chain(lanes).chain(lengths) {
            let witness = vec![F64::ZERO; words];
            let mut ps = ProverState::from_label(b"invalid commitment");

            // Refusal reports the invalid parameter and leaves the proof stream untouched.
            assert_eq!(Committed::new(&mut ps, &witness, shape, Rate::MIN).err(), Some(error));
            assert_eq!(
                ps.into_proof(),
                ProverState::from_label(b"invalid commitment").into_proof()
            );
        }
    }

    #[test]
    fn opening_requires_the_original_committed_length() {
        // Fixture state: one committed lane, with space for two lanes in the supplied buffer.
        let shape = StackShape { mu: MIN_MU, n_lanes: 1 };
        let lane_words = shape.committed_len();
        let witness = vec![F64::ZERO; 2 * lane_words];
        let committed = Committed::new(
            &mut ProverState::from_label(b"committed length"),
            &witness[..lane_words],
            shape,
            Rate::MIN,
        )
        .expect("a supported witness");

        // Mutation: omit the lane, cut it short, or supply a second whole lane.
        for words in [0, lane_words - 1, 2 * lane_words] {
            let mut ps = ProverState::from_label(b"invalid opening");
            assert_eq!(
                committed.open(&mut ps, &witness[..words], &[], &[]),
                Err(WitnessError::Length {
                    expected: lane_words,
                    got: words
                }),
            );

            // Length refusal precedes claim validation and all opening transcript writes.
            assert_eq!(
                ps.into_proof(),
                ProverState::from_label(b"invalid opening").into_proof()
            );
        }
    }
}
