use crate::challenger::Challenger;
use crate::{
    MerkleOpening, MerklePaths, PrunedMerklePaths, RawProof,
    transcript::{DIGEST_LEN_FE, Proof},
    *,
};
use field::PrimeCharacteristicRing;
use field::{ExtensionField, PrimeField64};
use koala_bear::symmetric::Permutation;
use koala_bear::{KoalaBear, default_koalabear_poseidon1_16};
use std::any::TypeId;
use std::collections::VecDeque;
use std::iter::repeat_n;
use symetric::CAPACITY;
use symetric::RATE;
use symetric::WIDTH;

pub struct VerifierState<EF: ExtensionField<PF<EF>>, P> {
    challenger: Challenger<PF<EF>, P>,
    transcript: Vec<PF<EF>>,
    transcript_offset: usize,
    pending_merkle_paths: VecDeque<PrunedMerklePaths<PF<EF>, PF<EF>>>,
    merkle_openings: Vec<MerkleOpening<PF<EF>>>,
    merkle_opening_index: usize,
    raw_transcript: Vec<PF<EF>>, // reconstructed during the proof verification, it's the format that the zkVM recursion program expects (no Merkle pruning, no sumcheck optimization to send less data, etc)
}

impl<EF: ExtensionField<PF<EF>>, P: Permutation<[PF<EF>; WIDTH]>> VerifierState<EF, P>
where
    PF<EF>: PrimeField64,
{
    pub fn new(proof: Proof<PF<EF>>, permutation: P, capacity: [PF<EF>; CAPACITY]) -> Result<Self, ProofError> {
        Ok(Self {
            challenger: Challenger::new(permutation, capacity),
            transcript: proof.transcript,
            transcript_offset: 0,
            pending_merkle_paths: proof.merkle_paths.into(),
            merkle_openings: Vec::new(),
            merkle_opening_index: 0,
            raw_transcript: Vec::new(),
        })
    }

    pub fn into_raw_proof(self) -> RawProof<PF<EF>> {
        RawProof {
            transcript: self.raw_transcript,
            merkle_openings: self.merkle_openings,
        }
    }

    pub fn check_fully_consumed(&self) -> Result<(), ProofError> {
        if self.transcript_offset != self.transcript.len()
            || self.merkle_opening_index != self.merkle_openings.len()
            || !self.pending_merkle_paths.is_empty()
        {
            return Err(ProofError::InvalidProof);
        }
        Ok(())
    }

    fn absorb_and_record(&mut self, scalars: &[PF<EF>]) {
        self.challenger.observe_many(scalars);
        let total_padded = scalars.len().next_multiple_of(RATE);
        self.raw_transcript.extend_from_slice(scalars);
        self.raw_transcript
            .extend(repeat_n(PF::<EF>::ZERO, total_padded - scalars.len()));
    }

    fn read_transcript(&mut self, n: usize) -> Result<Vec<PF<EF>>, ProofError> {
        if self.transcript_offset + n > self.transcript.len() {
            return Err(ProofError::ExceededTranscript);
        }
        let scalars = self.transcript[self.transcript_offset..self.transcript_offset + n].to_vec();
        self.transcript_offset += n;
        Ok(scalars)
    }

    #[allow(clippy::missing_transmute_annotations)]
    fn restore_merkle_paths(paths: PrunedMerklePaths<PF<EF>, PF<EF>>) -> Option<Vec<MerkleOpening<PF<EF>>>> {
        assert_eq!(TypeId::of::<PF<EF>>(), TypeId::of::<KoalaBear>());
        // SAFETY: We've confirmed PF<EF> == KoalaBear
        let paths: PrunedMerklePaths<KoalaBear, KoalaBear> = unsafe { std::mem::transmute(paths) };
        let perm = default_koalabear_poseidon1_16();
        let hash_fn = |data: &[KoalaBear]| symetric::hash_slice_rtl::<_, _, 16, 8, DIGEST_LEN_FE>(&perm, data);
        let combine_fn = |left: &[KoalaBear; DIGEST_LEN_FE], right: &[KoalaBear; DIGEST_LEN_FE]| {
            symetric::compress(&perm, [*left, *right])
        };
        let restored: MerklePaths<KoalaBear, KoalaBear> = paths.restore(&hash_fn, &combine_fn)?;
        let openings: Vec<MerkleOpening<KoalaBear>> = restored
            .0
            .into_iter()
            .map(|path| MerkleOpening {
                leaf_data: path.leaf_data,
                path: path.sibling_hashes,
            })
            .collect();
        // SAFETY: PF<EF> == KoalaBear
        Some(unsafe { std::mem::transmute(openings) })
    }
}

impl<EF: ExtensionField<PF<EF>>, P: Permutation<[PF<EF>; WIDTH]>> ChallengeSampler<EF> for VerifierState<EF, P>
where
    PF<EF>: PrimeField64,
{
    fn sample_vec(&mut self, len: usize) -> Vec<EF> {
        sample_vec(&mut self.challenger, len)
    }
    fn sample_in_range(&mut self, bits: usize, n_samples: usize) -> Vec<usize> {
        self.challenger.sample_in_range(bits, n_samples)
    }
}

impl<EF: ExtensionField<PF<EF>>, P: Permutation<[PF<EF>; WIDTH]>> FSVerifier<EF> for VerifierState<EF, P>
where
    PF<EF>: PrimeField64,
{
    fn state(&self) -> String {
        format!(
            "state {} (offset: {}, merkle_idx: {})",
            self.challenger
                .state
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.transcript_offset,
            self.merkle_opening_index,
        )
    }

    fn observe_scalars(&mut self, scalars: &[PF<EF>]) {
        self.challenger.observe_many(scalars);
    }

    fn duplex(&mut self) {
        self.challenger.duplex();
    }

    fn next_base_scalars_vec(&mut self, n: usize) -> Result<Vec<PF<EF>>, ProofError> {
        let scalars = self.read_transcript(n)?;
        self.absorb_and_record(&scalars);
        Ok(scalars)
    }

    fn begin_merkle_opening_batch(&mut self, n: usize) -> Result<(), ProofError> {
        if self.merkle_opening_index != self.merkle_openings.len() {
            return Err(ProofError::InvalidProof); // Previous batch must have been fully drained
        }
        let paths = self
            .pending_merkle_paths
            .pop_front()
            .ok_or(ProofError::ExceededTranscript)?;
        if paths.original_order.len() != n {
            return Err(ProofError::InvalidProof);
        }
        let restored = Self::restore_merkle_paths(paths).ok_or(ProofError::InvalidProof)?;
        self.merkle_openings.extend(restored);
        Ok(())
    }

    fn next_merkle_opening(&mut self) -> Result<MerkleOpening<PF<EF>>, ProofError> {
        if self.merkle_opening_index >= self.merkle_openings.len() {
            return Err(ProofError::ExceededTranscript);
        }
        let opening = self.merkle_openings[self.merkle_opening_index].clone();
        self.merkle_opening_index += 1;
        Ok(opening)
    }

    fn check_pow_grinding(&mut self, bits: usize) -> Result<(), ProofError> {
        if bits == 0 {
            return Ok(());
        }
        let witness = self.read_transcript(1)?[0];
        self.challenger.observe_many(&[witness]);
        if self.challenger.state[CAPACITY].as_canonical_u64() & ((1 << bits) - 1) != 0 {
            return Err(ProofError::InvalidGrindingWitness);
        }
        // On "compressed" proofs (in Rust), we assume only the first field element is pow-grinded (the RATE-1 others are zero) -> saves a bit of proof size
        // On "raw" proofs (without Prunned merkle paths, the one used in recursion program (fiat_shamir.py) / python verifier (verifier.py) -> what's actually specified), we assume all 8 field elements are pow-grinded
        self.raw_transcript.push(witness);
        self.raw_transcript.extend(repeat_n(PF::<EF>::ZERO, RATE - 1));
        Ok(())
    }

    fn next_sumcheck_polynomial(
        &mut self,
        n_coeffs: usize,
        claimed_sum: EF,
        eq_alpha: Option<EF>,
    ) -> ProofResult<Vec<EF>> {
        match eq_alpha {
            None => {
                let rest_scalars = self.read_transcript((n_coeffs - 1) * EF::DIMENSION)?;
                let rest_coeffs: Vec<EF> = pack_scalars_to_extension(&rest_scalars);
                // we use h(0) + h(1) = claimed_sum to recover the missing c0
                let c0 = (claimed_sum - rest_coeffs.iter().copied().sum::<EF>()).halve();

                let mut full_coeffs = Vec::with_capacity(n_coeffs);
                full_coeffs.push(c0);
                full_coeffs.extend_from_slice(&rest_coeffs);

                let mut all_scalars = flatten_scalars_to_base(&[c0]);
                all_scalars.extend_from_slice(&rest_scalars);
                self.absorb_and_record(&all_scalars);
                Ok(full_coeffs)
            }
            Some(alpha) => {
                let rest_scalars = self.read_transcript((n_coeffs - 2) * EF::DIMENSION)?;
                let rest_bare: Vec<EF> = pack_scalars_to_extension(&rest_scalars);
                let h0 = claimed_sum - alpha * rest_bare.iter().copied().sum::<EF>();

                let mut bare = Vec::with_capacity(n_coeffs - 1);
                bare.push(h0);
                bare.extend_from_slice(&rest_bare);

                let full_coeffs = expand_bare_to_full(&bare, alpha);
                self.absorb_and_record(&flatten_scalars_to_base(&full_coeffs));
                Ok(full_coeffs)
            }
        }
    }
}
