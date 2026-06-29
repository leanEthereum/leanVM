use std::fmt::{Display, Formatter};

use backend::PrimeCharacteristicRing;
use lean_vm::F;

pub const DIGEST_LEN: usize = 8;
pub const EXT_DEGREE: usize = 5;
/// Matches LeanVM's current default WHIR security target.
pub const SAMPLING_SOUNDNESS_BITS: usize = lean_prover::SECURITY_BITS;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParameterProfile {
    pub name: &'static str,
    pub n: usize,
    pub m: usize,
    pub k: usize,
    pub c: usize,
    pub whir_log_inv_rate: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProfileError(pub String);

impl Display for ProfileError {
    /// Formats a parameter-validation failure.
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for ProfileError {}

impl ParameterProfile {
    pub const TINY: Self = Self {
        name: "tiny",
        n: 2,
        m: 16,
        k: 8,
        c: 8,
        whir_log_inv_rate: 1,
    };

    pub const MEDIUM: Self = Self {
        name: "medium",
        n: 8,
        m: 256,
        k: 128,
        c: 8,
        whir_log_inv_rate: 1,
    };

    pub const LARGE: Self = Self {
        name: "large",
        n: 16,
        m: 1024,
        k: 512,
        c: 8,
        whir_log_inv_rate: 1,
    };

    pub const STRESS: Self = Self {
        name: "stress",
        n: 32,
        m: 4096,
        k: 2048,
        c: 8,
        whir_log_inv_rate: 1,
    };

    pub const BLOB_128K_1: Self = Self {
        name: "blob-128k-1",
        n: 1,
        m: 65536,
        k: 32768,
        c: 64,
        whir_log_inv_rate: 1,
    };

    pub const BLOB_128K_4: Self = Self {
        name: "blob-128k-4",
        n: 4,
        m: 65536,
        k: 32768,
        c: 64,
        whir_log_inv_rate: 1,
    };

    pub const BLOB_128K_16: Self = Self {
        name: "blob-128k-16",
        n: 16,
        m: 65536,
        k: 32768,
        c: 64,
        whir_log_inv_rate: 1,
    };

    /// Constructs a custom half-rate profile and validates it before use.
    pub fn custom(n: usize, m: usize, k: usize, c: usize, whir_log_inv_rate: usize) -> Result<Self, ProfileError> {
        let profile = Self {
            name: "custom",
            n,
            m,
            k,
            c,
            whir_log_inv_rate,
        };
        profile.validate()?;
        Ok(profile)
    }

    /// Returns the number of cell columns in each encoded row.
    pub const fn n_cells(self) -> usize {
        self.m / self.c
    }

    /// Returns the number of distinct cells required for reconstruction.
    pub const fn reconstruction_threshold_cells(self) -> usize {
        self.k.div_ceil(self.c)
    }

    /// Returns the minimum number of distinct samples needed for the requested availability soundness.
    pub fn sampling_count(self, soundness_bits: usize) -> usize {
        let n_cells = self.n_cells();
        let max_available_without_reconstruction = self.reconstruction_threshold_cells() - 1;
        let mut log2_failure = 0.0;

        for sample_count in 1..=n_cells {
            if sample_count > max_available_without_reconstruction {
                return sample_count;
            }
            let offset = sample_count - 1;
            log2_failure +=
                ((max_available_without_reconstruction - offset) as f64).log2() - ((n_cells - offset) as f64).log2();
            if log2_failure <= -(soundness_bits as f64) {
                return sample_count;
            }
        }
        n_cells
    }

    /// Returns the log2 false-accept probability for distinct sampling in the worst unreconstructable case.
    pub fn sampling_log2_failure(self, sample_count: usize) -> f64 {
        let n_cells = self.n_cells();
        let max_available_without_reconstruction = self.reconstruction_threshold_cells() - 1;
        if sample_count > max_available_without_reconstruction {
            return f64::NEG_INFINITY;
        }
        (0..sample_count)
            .map(|offset| {
                ((max_available_without_reconstruction - offset) as f64).log2() - ((n_cells - offset) as f64).log2()
            })
            .sum()
    }

    /// Returns the spacing between systematic subgroup evaluations.
    pub const fn systematic_stride(self) -> usize {
        self.m / self.k
    }

    /// Returns the binary Merkle-tree depth.
    pub const fn merkle_depth(self) -> usize {
        self.n_cells().ilog2() as usize
    }

    /// Checks all field, FFT, hashing, Merkle, and current membership constraints.
    pub fn validate(self) -> Result<(), ProfileError> {
        if self.n == 0 || self.k == 0 || self.m == 0 || self.c == 0 {
            return Err(ProfileError("n, m, k, and c must be non-zero".to_string()));
        }
        if !self.m.is_power_of_two() || !self.k.is_power_of_two() {
            return Err(ProfileError("m and k must be powers of two".to_string()));
        }
        if self.m != 2 * self.k {
            return Err(ProfileError(
                "the current special-barycentric implementation requires m = 2k".to_string(),
            ));
        }
        if !self.m.is_multiple_of(self.c) {
            return Err(ProfileError("c must divide m".to_string()));
        }
        if !self.n_cells().is_power_of_two() {
            return Err(ProfileError("m/c must be a power of two".to_string()));
        }
        if !self.k.is_multiple_of(DIGEST_LEN) || !(self.n * self.c).is_multiple_of(DIGEST_LEN) {
            return Err(ProfileError(
                "k and n*c must be multiples of the Poseidon rate 8".to_string(),
            ));
        }
        if !(1..=4).contains(&self.whir_log_inv_rate) {
            return Err(ProfileError("WHIR log inverse rate must be in 1..=4".to_string()));
        }
        if self.m.ilog2() > 24 {
            return Err(ProfileError("m exceeds KoalaBear two-adicity".to_string()));
        }
        Ok(())
    }

    /// Encodes this profile into one field-element block for public Fiat-Shamir preprocessing.
    pub fn profile_block(self) -> [F; DIGEST_LEN] {
        [
            F::from_u32(0x5051_4441),
            F::ONE,
            F::from_usize(self.n),
            F::from_usize(self.m),
            F::from_usize(self.k),
            F::from_usize(self.c),
            F::from_usize(self.n_cells()),
            F::from_usize(self.whir_log_inv_rate),
        ]
    }
}

/// Encodes the RS Fiat-Shamir domain separator into one Poseidon-rate block.
pub fn fs_block() -> [F; DIGEST_LEN] {
    [
        F::from_u32(0x5253_4348),
        F::ONE,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
        F::ZERO,
    ]
}
