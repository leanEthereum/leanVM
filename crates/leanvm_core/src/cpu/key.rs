//! A program's verifying key: the commitment to its decoded table, and everything else public about it.
//!
//! Key generation ([`super::Program::new`]) is a deterministic function of the program, so anyone can regenerate a key and compare it.

use super::batch::{Batch, FormPowers};
use super::error::CpuError;
use super::layout::{Announcement, Schema, Sizes};
use crate::rv::{self, Region};
use crate::{class_flock, constraints, leaf, pcs, tables};
use ::pcs::pack::PACKING_WIDTH;
use fiat_shamir::transcript::{Challenger, Proof, RawProof, VerifierState};
use primitives::field::{F64, F192};

/// What a verifier needs of a program: the Merkle root of its committed table, its sizes, its entry point and its image.
///
/// The table itself is no part of it: every proof opens the commitment at the points it needs (§sec:e2e-bc).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifyingKey {
    /// The root of the commitment to the program's stacked table.
    root: [u8; 32],
    /// The table's, RAM's and the advice's sizes.
    sizes: Sizes,
    /// The address of the first instruction run.
    entry_pc: u64,
    /// RAM's first words; the rest are zero.
    image: Vec<u64>,
    /// The digest of the key, which seeds the transcript.
    digest: [u8; 32],
}

/// The most entries a program's table has, as a base-two logarithm: what the text region holds, and what the commitment takes once the table is stacked.
pub(super) const MAX_LOG_BYTECODE: usize = {
    let committed = pcs::MAX_MU - leaf::N_BYTECODE_SELECTORS;
    if Region::TEXT.max_log_words() < committed {
        Region::TEXT.max_log_words()
    } else {
        committed
    }
};

impl VerifyingKey {
    /// The domain separator of the digest, versioned with the statement's format.
    const DIGEST_DOMAIN: &'static [u8] = b"leanvm-rv64im-7";

    /// The key of a program whose table commits to `root`.
    pub(super) fn new(root: [u8; 32], sizes: Sizes, entry_pc: u64, image: Vec<u64>) -> Self {
        let mut key = Self {
            root,
            sizes,
            entry_pc,
            image,
            digest: [0; 32],
        };
        let mut h = primitives::hash::Hasher::new();
        h.update(Self::DIGEST_DOMAIN);
        h.update(&key.to_bytes());
        key.digest = h.finalize();
        key
    }

    /// The key's bytes, every word little-endian.
    ///
    /// ```text
    /// | root: 32 bytes | log_bytecode | entry_pc | log_ram | log_advice | image length | image words |
    /// ```
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        let words = [
            self.sizes.log_bytecode as u64,
            self.entry_pc,
            self.sizes.log_ram as u64,
            self.sizes.log_advice as u64,
            self.image.len() as u64,
        ];
        let words = words.iter().chain(&self.image).flat_map(|w| w.to_le_bytes());
        self.root.iter().copied().chain(words).collect()
    }

    /// The key these bytes encode.
    ///
    /// Returns `None` for bytes that are no key, or a key whose sizes or entry point no program has.
    #[must_use]
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let (root, rest) = bytes.split_first_chunk::<32>()?;
        let (words, tail) = rest.as_chunks::<8>();
        if !tail.is_empty() {
            return None;
        }
        let words: Vec<u64> = words.iter().map(|&w| u64::from_le_bytes(w)).collect();
        let (&[log_bytecode, entry_pc, log_ram, log_advice, image_len], image) = words.split_first_chunk::<5>()?;
        let size = |word: u64| usize::try_from(word).ok();
        let (log_bytecode, log_ram, log_advice) = (size(log_bytecode)?, size(log_ram)?, size(log_advice)?);
        if image.len() as u64 != image_len {
            return None;
        }

        // A table some text gives: at least the halt slot and a slot before it.
        if !(1..=MAX_LOG_BYTECODE).contains(&log_bytecode) {
            return None;
        }
        rv::Program::validate((1 << log_bytecode) - 1, entry_pc, image.len(), log_ram, log_advice).ok()?;
        let sizes = Sizes {
            log_bytecode,
            log_ram,
            log_advice,
        };
        Some(Self::new(*root, sizes, entry_pc, image.to_vec()))
    }

    /// BLAKE2s over a domain separator and the key's bytes: the table's commitment, its size, the entry point, the region sizes and the initial RAM image.
    ///
    /// ELF metadata is no part of it, and every illegal encoding decodes to the same entry.
    pub const fn digest(&self) -> &[u8; 32] {
        &self.digest
    }

    /// The root of the commitment to the program's stacked table.
    pub const fn root(&self) -> &[u8; 32] {
        &self.root
    }

    /// The transcript's seed: the digest, as words.
    ///
    /// Every challenge depends on it, and the run's public output seeds the transcript beside it.
    pub fn fs_seed(&self) -> [F64; 4] {
        fiat_shamir::digest_words(&self.digest)
    }

    /// The table's, RAM's and the advice's sizes.
    pub(crate) const fn sizes(&self) -> Sizes {
        self.sizes
    }

    /// The address of the first instruction run.
    pub(crate) const fn entry_pc(&self) -> u64 {
        self.entry_pc
    }

    /// Where a run ends: the table's last slot, which is never executed.
    pub(crate) const fn halt_pc(&self) -> u64 {
        Region::TEXT.address((1 << self.sizes.log_bytecode) - 1)
    }

    /// RAM's initialized words.
    pub(crate) fn image(&self) -> &[u64] {
        &self.image
    }

    /// The stack the program's table is committed in.
    pub(crate) fn program_shape(&self) -> crate::witness::StackShape {
        pcs::program_shape(self.sizes.log_bytecode + leaf::N_BYTECODE_SELECTORS)
    }

    /// Verify a proof that the program exits returning `output`.
    ///
    /// It takes only public inputs, never the prover's witness.
    ///
    /// # Errors
    ///
    /// Returns the first stage that refuses the proof.
    pub fn verify(&self, output: &[u64; 4], proof: &Proof) -> Result<(), CpuError> {
        self.verify_to_raw(output, proof).map(|_| ())
    }

    /// Verify a proof, and return it with every query's Merkle path written out, the form the Python verifier reads.
    ///
    /// # Errors
    ///
    /// Returns the first stage that refuses the proof.
    #[tracing::instrument(name = "Verify", skip_all)]
    pub fn verify_to_raw(&self, output: &[u64; 4], proof: &Proof) -> Result<RawProof, CpuError> {
        // The public statement seeds the transcript, as on the prover's side.
        let mut vs = VerifierState::new(self.fs_seed(), proof, output.map(F64));

        // The announced sizes, then the layout they describe, then the commitment.
        let announcement = Announcement::read(&mut vs)?;
        let l = announcement.layout(self)?;
        let root = pcs::read_commitment(&mut vs)?;

        let bus = leaf::verify_balance(&l.push, &l.pull, &l.producers, &Schema::get().spans, &mut vs)
            .map_err(CpuError::Bus)?;

        // The tie between the batch and the bus, and why the batch's target is never sent.
        //
        // Each side's leaf claim, less its framework blocks, is the tables' and producers' share `R_s`.
        //
        // The verifier just derived those, and the batch must sum to `sum_s xi^s * R_s`.
        //
        // The challenge `xi` comes after the `R_s` are fixed, so hitting that one number forces each side's share.
        let powers = FormPowers::new(vs.sample());
        let target = powers.combine(bus.totals);
        let batch = Batch::new(&l, &bus.forms, &bus.producers, powers);
        let table_claims =
            constraints::verify(batch.airs(), &bus.point, target, &mut vs).map_err(CpuError::Constraint)?;
        let slots = l.opening_claims(bus.claims, &table_claims, output);
        let producer_claims = &table_claims[tables::N_TABLES..];
        let program_slots = l.program_claims(&bus.alphas, bus.beta, producer_claims);

        // Replay each circuit's flock reduction off the stream, to recover its validity claim on its packed witness.
        let mut replays = Vec::with_capacity(class_flock::N_FLOCKS);
        for f in 0..class_flock::N_FLOCKS {
            let (t, part) = class_flock::flock(f);
            let replay = class_flock::verify_reduction(f, l.taus[t], &mut vs).map_err(|error| CpuError::Flock {
                table: tables::CLASSES[t].name,
                part,
                error,
            })?;
            replays.push(replay);
        }

        // The ring-switched regions: each packed witness, then each producer's multiplicity column, from its bits' values.
        let slices: Vec<[F192; PACKING_WIDTH]> = l
            .producers
            .iter()
            .zip(producer_claims)
            .map(|(p, claims)| claims.evals_padded(p.bits))
            .collect();
        let witnesses = replays.iter().enumerate().map(|(f, replay)| {
            let window = l.witness_window(f);
            flock::reduction::ring_switch_verify(window.n_vars, window.offset, &replay.claim)
        });
        let producers = l
            .producers
            .iter()
            .zip(producer_claims)
            .zip(&slices)
            .map(|((p, claims), slices)| {
                let window = l.multiplicity_window(p);
                ::pcs::stack_open::RingSwitchVerify {
                    offset: window.offset,
                    qflock_vars: window.n_vars,
                    claims: vec![::pcs::stack_open::RingSwitchVerifyClaim {
                        suffix_point: &claims.chi,
                        s_hat_v: slices,
                    }],
                }
            });
        let rings: Vec<_> = witnesses.chain(producers).collect();

        // The witness's opening, then the program's, then nothing may be left on the stream.
        pcs::verify(&mut vs, &slots, &rings, l.shape, announcement.log_inv_rate, &root).map_err(CpuError::Open)?;
        pcs::verify_program(&mut vs, &program_slots, self.program_shape(), &self.root)
            .map_err(CpuError::ProgramOpen)?;
        vs.finish()?;
        Ok(vs.into_raw_proof())
    }
}
