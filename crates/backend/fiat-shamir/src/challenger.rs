use field::PrimeField64;
use koala_bear::symmetric::Permutation;
use symetric::{CAPACITY, RATE, WIDTH};

#[derive(Clone, Debug)]
pub struct Challenger<F, P> {
    pub permutation: P,
    pub state: [F; WIDTH],
    rate_fresh: bool,
}

impl<F: PrimeField64, P: Permutation<[F; WIDTH]>> Challenger<F, P> {
    pub fn new(permutation: P, initial_capacity: [F; CAPACITY]) -> Self
    where
        F: Default,
    {
        let mut state = [F::ZERO; WIDTH];
        state[..CAPACITY].copy_from_slice(&initial_capacity);
        Self {
            permutation,
            state,
            rate_fresh: false,
        }
    }

    pub fn observe(&mut self, value: [F; RATE]) {
        self.state[CAPACITY..].copy_from_slice(&value);
        self.permutation.permute_mut(&mut self.state);
        self.rate_fresh = true;
    }

    pub fn observe_many(&mut self, scalars: &[F]) {
        for chunk in scalars.chunks(RATE) {
            let mut buffer = [F::ZERO; RATE];
            buffer[..chunk.len()].copy_from_slice(chunk);
            self.observe(buffer);
        }
    }

    pub fn duplex(&mut self) {
        self.observe([F::ZERO; RATE]);
    }

    pub fn sample(&mut self) -> [F; RATE] {
        assert!(self.rate_fresh, "stale rate. insert a duplex() before.");
        let out: [F; RATE] = self.state[CAPACITY..].try_into().unwrap();
        self.rate_fresh = false;
        out
    }

    pub fn sample_many(&mut self, n: usize) -> Vec<[F; RATE]> {
        if n == 0 {
            return Vec::new();
        }
        let mut out = Vec::with_capacity(n);
        out.push(self.sample());
        for _ in 1..n {
            self.duplex();
            out.push(self.sample());
        }
        out
    }

    /// Warning: not perfectly uniform
    pub fn sample_in_range(&mut self, bits: usize, n_samples: usize) -> Vec<usize> {
        assert!(bits < F::bits());

        let range: u64 = 1u64 << bits;
        // Valori >= threshold vengono scartati: tenerli darebbe alle residue
        // basse (0..F::ORDER_U64 % range) massa di probabilita' extra.
        let threshold: u64 = F::ORDER_U64 - (F::ORDER_U64 % range);

        let mut res = Vec::with_capacity(n_samples);
        while res.len() < n_samples {
            let remaining = n_samples - res.len();
            let batch = self.sample_many(remaining.div_ceil(RATE));
            for fe in batch.into_iter().flatten() {
                let candidate = fe.as_canonical_u64();
                if candidate >= threshold {
                    continue;
                }
                res.push((candidate & (range - 1)) as usize);
                if res.len() == n_samples {
                    break;
                }
            }
        }
        res
    }
}

#[cfg(test)]
mod bias_regression_tests {
    use super::*;
    use koala_bear::{KoalaBear, default_koalabear_poseidon1_16};

    #[test]
    fn sample_in_range_is_not_biased_toward_low_residues() {
        let bits = 4;
        let n = 1usize << bits;
        let samples = 200_000;

        let perm = default_koalabear_poseidon1_16();
        let mut challenger: Challenger<KoalaBear, _> = Challenger::new(perm, Default::default());
        challenger.duplex();
        let out = challenger.sample_in_range(bits, samples);

        let mut counts = vec![0usize; n];
        for v in out {
            assert!(v < n);
            counts[v] += 1;
        }

        let expected = samples as f64 / n as f64;
        for (i, &c) in counts.iter().enumerate() {
            let deviation = (c as f64 - expected).abs() / expected;
            assert!(
                deviation < 0.05,
                "residue {i} deviates {deviation:.3} from uniform (count={c}, expected={expected})"
            );
        }
    }
}
