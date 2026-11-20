//! ML-DSA (FIPS 204) verification in leanVM: the host side of `guests/ml_dsa.py`.
//!
//! The guest runs ML-DSA.Verify_internal on claims `(pk, mu, sig)`. It computes `tr = H(pk, 64)` itself and
//! publishes the claims as one digest ([`public_input`]): `c_s = Keccak-256(tr_s || mu_s)` for each claim, chained as
//! `d_1 = c_0`, `d_{s+1} = Keccak-256(d_s || c_s)`. Whoever checks a claim on a message computes its `mu` as
//! ML-DSA.Verify does ([`fips::mu`]), so the guest never reads a message, whatever its length.
//!
//! [`witness`] decodes each claim and replays the guest's arithmetic to produce its advice. A signature whose
//! encoding is malformed has no decoding, so no witness ([`Rejected`]); any other invalid signature gets one, and the
//! guest's run fails on it.

pub mod fips;
mod witness;

use std::collections::BTreeMap;

pub use fips::{ML_DSA_44, ML_DSA_65, ML_DSA_87, Params};
use verifier::E;

/// The guest's source.
pub const GUEST: &str = include_str!("../../../guests/ml_dsa.py");

/// One claim: a public key, the message representative `mu` and a signature, each as FIPS 204 encodes it.
#[derive(Clone, Debug)]
pub struct Claim {
    pub pk: Vec<u8>,
    pub mu: [u8; 64],
    pub sig: Vec<u8>,
}

/// Why a claim has no witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Rejected {
    /// `pkDecode` takes no key of this length.
    MalformedKey,
    /// `sigDecode` returns ⊥: a wrong length or a malformed hint.
    MalformedSignature,
    /// A valid signature the guest cannot take: it squeezes five SHAKE128 blocks a polynomial of `A` and one
    /// SHAKE256 block for `c`, which every key and signature but a vanishing fraction fit.
    Unsupported(&'static str),
}

/// The guest compiled for `n_sigs` claims under parameter set `p`.
pub fn program(p: &Params, n_sigs: usize) -> isa::Program {
    __program_from(GUEST, p, n_sigs)
}

#[doc(hidden)]
pub fn __program_from(src: &str, p: &Params, n_sigs: usize) -> isa::Program {
    let ast = zkdsl_compiler::parse_with_replacements(src, &replacements(p, n_sigs))
        .unwrap_or_else(|e| panic!("the ML-DSA guest parses: {e}"));
    isa::Program::from(zkdsl_compiler::compile(&ast))
}

fn replacements(p: &Params, n_sigs: usize) -> BTreeMap<String, String> {
    assert!(n_sigs >= 1, "the guest takes at least one claim");
    let list = |v: &[u64]| format!("[{}]", v.iter().map(u64::to_string).collect::<Vec<_>>().join(", "));
    let [d, h, w1] = witness::use_hint_columns(p);
    [
        ("K_PLACEHOLDER", p.k.to_string()),
        ("L_PLACEHOLDER", p.l.to_string()),
        ("TAU_PLACEHOLDER", p.tau.to_string()),
        ("OMEGA_PLACEHOLDER", p.omega.to_string()),
        ("GAMMA2_PLACEHOLDER", p.gamma2.to_string()),
        ("W1_BITS_PLACEHOLDER", p.w1_bits().to_string()),
        ("ZB_PLACEHOLDER", p.z_bound().to_string()),
        ("CHW_PLACEHOLDER", (64 >> p.w1_bits().trailing_zeros()).to_string()),
        ("CT_LANES_PLACEHOLDER", (p.ctilde_bytes() / 8).to_string()),
        ("N_SIGS_PLACEHOLDER", n_sigs.to_string()),
        ("UH_D_PLACEHOLDER", list(&d)),
        ("UH_H_PLACEHOLDER", list(&h)),
        ("UH_W1_PLACEHOLDER", list(&w1)),
    ]
    .into_iter()
    .map(|(k, v)| (k.to_string(), v))
    .collect()
}

/// Hint streams by name, each with one entry a `hint_witness` call pops, as `isa::Prover::prove` takes them.
pub type Streams = Vec<(String, Vec<Vec<E>>)>;

/// The guest's advice for `claims`.
pub fn witness(p: &Params, claims: &[Claim]) -> Result<Streams, Rejected> {
    witness::streams(p, claims)
}

/// The public input the guest publishes for `claims`.
pub fn public_input(claims: &[Claim]) -> [E; 2] {
    let claim_digest = |c: &Claim| {
        let mut data = fips::tr(&c.pk).to_vec();
        data.extend(c.mu);
        keccak256::hash(&data)
    };
    let mut d = claim_digest(&claims[0]);
    for c in &claims[1..] {
        d = keccak256::hash_pair(&d, &claim_digest(c));
    }
    let (lo, hi) = verifier::Digest(d).halves();
    [lo, hi]
}
