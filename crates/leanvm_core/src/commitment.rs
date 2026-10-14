//! Base-field witness commitments with one shared opening for point and circuit-validity claims.
//!
//! Witness words lie in K = GF(2^64), and challenges lie in E = GF(2^192).
//! The opening proves an inner product against a weight the verifier reconstructs.
//!
//! The immutable commitment includes the root, shape, original transcript context, and one out-of-domain point/value anchor.
//! Each opening binds that complete record before batching the point and circuit-validity claims.
//! A hiding commitment, a zero-knowledge proof's, has no anchor: its value would publish an evaluation of the hidden witness.
//! The security-bit constant is a parameter-selection target, not a proved concrete security level for the deployed hash and Fiat-Shamir composition (doc/leanvm, Annex B).

use crate::stacking::StackShape;
use fiat_shamir::ProverState;
use pcs::stack::{CommittedStack, StackCommitment, Statement};
use pcs::verifier::OpeningVerifier;
use pcs::whir::{Config, ConfigError, WhirError};
use primitives::field::F64;
use rand_core::CryptoRng;
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

/// The opening's profile: the hiding one for a hiding stack.
fn config(shape: StackShape, rate: Rate) -> Result<Config, ConfigError> {
    let log_inv_rate = usize::from(rate.log_inv_rate());
    if shape.hiding {
        Config::hiding(shape.mu, log_inv_rate)
    } else {
        Config::for_rate(shape.mu, log_inv_rate)
    }
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
        let config = Self::config(witness.len(), shape, rate)?;
        // The codeword and tree use the same parameters retained for opening.
        let stack = CommittedStack::new(ps, witness, shape.mu, config);
        Ok(Self { stack, shape })
    }

    /// Encodes a hiding stack and binds its root: the data lanes, then the zero lanes and the random group.
    ///
    /// The random group and every lane's padding are drawn from `rng`.
    ///
    /// # Errors
    ///
    /// As the plain commitment.
    pub(crate) fn new_hiding(
        ps: &mut ProverState,
        witness: &mut [F64],
        shape: StackShape,
        rate: Rate,
        rng: &mut impl CryptoRng,
    ) -> Result<Self, WitnessError> {
        assert!(shape.hiding, "a hiding commitment takes a hiding stack");
        let config = Self::config(witness.len(), shape, rate)?;
        let stack = CommittedStack::new_hiding(witness, shape.mu, config, rng);
        ps.prover_message(&stack.root());
        Ok(Self { stack, shape })
    }

    /// The opening's configuration, once the shape and the witness's length are checked.
    fn config(len: usize, shape: StackShape, rate: Rate) -> Result<Config, WitnessError> {
        // Validate the dimension before shifting lengths or allocating the codeword.
        let config = config(shape, rate)?;
        let max = 1usize << config.initial_k();
        if !(1..=max).contains(&shape.committed_lanes()) {
            return Err(WitnessError::LaneCount {
                n_lanes: shape.committed_lanes(),
                max,
            });
        }
        let expected = shape.committed_len();
        if len != expected {
            return Err(WitnessError::Length { expected, got: len });
        }
        Ok(config)
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
    #[expect(
        clippy::disallowed_methods,
        reason = "cpu::Program::prove_witness and rec's Circuit::prove_with send each value as a prover message or take it from the instance first"
    )]
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

/// A commitment as its verifier holds it, with its validated opening configuration: an immutable anchored record, or a hiding stack's root.
pub(crate) struct Commitment<E, R, K> {
    stack: StackCommitment<E, R, K>,
}

impl<E: Copy, R: Copy, K: Copy> Commitment<E, R, K> {
    /// Reads and binds the complete commitment before any opening statement.
    ///
    /// A plain stack's commitment is its anchored record; a hiding stack's is its root alone, since its anchor would publish an evaluation of the hidden witness.
    ///
    /// # Errors
    ///
    /// Returns an invalid public shape, incompatible commitment context, or malformed stream.
    pub(crate) fn read<V: OpeningVerifier<E = E, Root = R, K = K>>(
        v: &mut V,
        shape: StackShape,
        rate: Rate,
    ) -> Result<Self, WhirError> {
        let config = config(shape, rate)?;
        let stack = if shape.hiding {
            // Reading the root binds it into the transcript without drawing a challenge.
            let root = v.next_root()?;
            StackCommitment::hiding(root, shape.mu, shape.committed_lanes(), config)?
        } else {
            StackCommitment::receive(v, shape.mu, shape.committed_lanes(), config)?
        };
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
    #[expect(
        clippy::disallowed_methods,
        reason = "cpu::Layout::verify_core and rec's TableArgument::verify_core read each value as a prover message or take it from the instance first"
    )]
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
    use crate::stacking::StackShape;
    use fiat_shamir::{ProverState, SessionId};
    use pcs::whir::ConfigError;
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
                StackShape {
                    mu,
                    n_lanes: 1,
                    hiding: false,
                },
                0,
                WitnessError::Config(ConfigError::SizeOutOfRange { log_n: mu }),
            )
        });
        // Mutation: lane counts outside a leaf and incomplete lane buffers.
        let lanes = [0, max_lanes + 1, usize::MAX].map(|n_lanes| {
            (
                StackShape {
                    mu: MIN_MU,
                    n_lanes,
                    hiding: false,
                },
                0,
                WitnessError::LaneCount {
                    n_lanes,
                    max: max_lanes,
                },
            )
        });
        let lengths = [0, lane_words - 1, lane_words + 1].map(|got| {
            (
                StackShape {
                    mu: MIN_MU,
                    n_lanes: 1,
                    hiding: false,
                },
                got,
                WitnessError::Length {
                    expected: lane_words,
                    got,
                },
            )
        });
        for (shape, words, error) in sizes.into_iter().chain(lanes).chain(lengths) {
            let witness = vec![F64::ZERO; words];
            let mut ps = ProverState::new(&SessionId::new(b"invalid commitment"), &0u64);

            // Refusal reports the invalid parameter and leaves the proof stream untouched.
            assert_eq!(Committed::new(&mut ps, &witness, shape, Rate::MIN).err(), Some(error));
            assert_eq!(
                ps.into_proof(),
                ProverState::new(&SessionId::new(b"invalid commitment"), &0u64).into_proof()
            );
        }
    }

    #[test]
    fn opening_requires_the_original_committed_length() {
        // Fixture state: one committed lane, with space for two lanes in the supplied buffer.
        let shape = StackShape {
            mu: MIN_MU,
            n_lanes: 1,
            hiding: false,
        };
        let lane_words = shape.committed_len();
        let witness = vec![F64::ZERO; 2 * lane_words];
        let committed = Committed::new(
            &mut ProverState::new(&SessionId::new(b"committed length"), &0u64),
            &witness[..lane_words],
            shape,
            Rate::MIN,
        )
        .expect("a supported witness");

        // Mutation: omit the lane, cut it short, or supply a second whole lane.
        for words in [0, lane_words - 1, 2 * lane_words] {
            let mut ps = ProverState::new(&SessionId::new(b"invalid opening"), &0u64);
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
                ProverState::new(&SessionId::new(b"invalid opening"), &0u64).into_proof()
            );
        }
    }
}
