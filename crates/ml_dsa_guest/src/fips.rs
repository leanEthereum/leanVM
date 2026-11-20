//! What the guest takes from FIPS 204: the parameter sets, the encodings it decodes, and the sponges.

/// The modulus `q`.
pub const Q: u64 = 8_380_417;
/// Bits dropped from `t`.
pub const D: u32 = 13;

/// An ML-DSA parameter set (FIPS 204, Table 1).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    pub name: &'static str,
    pub k: usize,
    pub l: usize,
    pub tau: usize,
    pub lambda: usize,
    pub gamma1_bits: u32,
    pub gamma2: u64,
    pub beta: u64,
    pub omega: usize,
}

pub const ML_DSA_44: Params = Params {
    name: "ML-DSA-44",
    k: 4,
    l: 4,
    tau: 39,
    lambda: 128,
    gamma1_bits: 17,
    gamma2: (Q - 1) / 88,
    beta: 78,
    omega: 80,
};

pub const ML_DSA_65: Params = Params {
    name: "ML-DSA-65",
    k: 6,
    l: 5,
    tau: 49,
    lambda: 192,
    gamma1_bits: 19,
    gamma2: (Q - 1) / 32,
    beta: 196,
    omega: 55,
};

pub const ML_DSA_87: Params = Params {
    name: "ML-DSA-87",
    k: 8,
    l: 7,
    tau: 60,
    lambda: 256,
    gamma1_bits: 19,
    gamma2: (Q - 1) / 32,
    beta: 120,
    omega: 75,
};

impl Params {
    /// `(q - 1) / (2 gamma2)`, the number of values `HighBits` takes.
    pub const fn m(&self) -> u64 {
        (Q - 1) / (2 * self.gamma2)
    }

    /// Bits a coefficient of `w1` takes in `w1Encode`.
    pub const fn w1_bits(&self) -> u32 {
        (self.m() - 1).ilog2() + 1
    }

    /// Bytes of `c~`.
    pub const fn ctilde_bytes(&self) -> usize {
        self.lambda / 4
    }

    /// The largest `|z_i|` a valid signature has, `gamma1 - beta - 1`.
    pub const fn z_bound(&self) -> u64 {
        (1 << self.gamma1_bits) - self.beta - 1
    }

    pub const fn pk_bytes(&self) -> usize {
        32 + 320 * self.k
    }

    pub const fn sig_bytes(&self) -> usize {
        self.ctilde_bytes() + 32 * self.l * (self.gamma1_bits as usize + 1) + self.omega + self.k
    }
}

/// A decoded public key.
pub struct PublicKey {
    pub rho: [u8; 32],
    /// `t1`, one row of ten-bit coefficients a polynomial.
    pub t1: Vec<[u64; 256]>,
}

/// A decoded signature.
pub struct Signature {
    pub ctilde: Vec<u8>,
    /// `z`, as integers in `[gamma1 - 2^(gamma1_bits + 1) + 1, gamma1]`.
    pub z: Vec<[i64; 256]>,
    pub h: Vec<[bool; 256]>,
}

/// `pkDecode`.
pub fn decode_pk(p: &Params, pk: &[u8]) -> Option<PublicKey> {
    if pk.len() != p.pk_bytes() {
        return None;
    }
    let rho = pk[..32].try_into().unwrap();
    let t1 = (0..p.k)
        .map(|i| {
            let bytes = &pk[32 + 320 * i..][..320];
            std::array::from_fn(|n| bits_at(bytes, 10 * n, 10))
        })
        .collect();
    Some(PublicKey { rho, t1 })
}

/// `sigDecode`, `None` where it returns ⊥ (a malformed hint).
pub fn decode_sig(p: &Params, sig: &[u8]) -> Option<Signature> {
    if sig.len() != p.sig_bytes() {
        return None;
    }
    let (ctilde, rest) = sig.split_at(p.ctilde_bytes());
    let zb = p.gamma1_bits as usize + 1;
    let (zs, y) = rest.split_at(32 * p.l * zb);
    let gamma1 = 1i64 << p.gamma1_bits;
    let z = (0..p.l)
        .map(|j| {
            let bytes = &zs[32 * zb * j..][..32 * zb];
            std::array::from_fn(|n| gamma1 - bits_at(bytes, zb * n, zb) as i64)
        })
        .collect();
    // HintBitUnpack.
    let mut h = vec![[false; 256]; p.k];
    let mut index = 0usize;
    for (i, row) in h.iter_mut().enumerate() {
        let end = y[p.omega + i] as usize;
        if end < index || end > p.omega {
            return None;
        }
        let first = index;
        while index < end {
            if index > first && y[index - 1] >= y[index] {
                return None;
            }
            row[y[index] as usize] = true;
            index += 1;
        }
    }
    if y[index..p.omega].iter().any(|&b| b != 0) {
        return None;
    }
    Some(Signature {
        ctilde: ctilde.to_vec(),
        z,
        h,
    })
}

/// The `width` bits of the little-endian bit string `bytes` from bit `at`.
fn bits_at(bytes: &[u8], at: usize, width: usize) -> u64 {
    (0..width).fold(0, |v, b| {
        v | (u64::from(bytes[(at + b) / 8] >> ((at + b) % 8) & 1) << b)
    })
}

/// SHAKE128 (rate 168) or SHAKE256 (rate 136) of `data`, `out` bytes.
pub fn shake(rate: usize, data: &[u8], out: usize) -> Vec<u8> {
    let mut st = [0u64; 25];
    let mut block = vec![0u8; rate];
    let mut chunks = data.chunks_exact(rate);
    for chunk in &mut chunks {
        xor_into(&mut st, chunk);
        keccak256::keccak_f(&mut st);
    }
    let tail = chunks.remainder();
    block[..tail.len()].copy_from_slice(tail);
    block[tail.len()] ^= 0x1F;
    block[rate - 1] ^= 0x80;
    xor_into(&mut st, &block);
    keccak256::keccak_f(&mut st);
    let mut squeezed = Vec::with_capacity(out.next_multiple_of(rate));
    loop {
        squeezed.extend(st.iter().flat_map(|lane| lane.to_le_bytes()).take(rate));
        if squeezed.len() >= out {
            squeezed.truncate(out);
            return squeezed;
        }
        keccak256::keccak_f(&mut st);
    }
}

fn xor_into(st: &mut [u64; 25], block: &[u8]) {
    for (lane, word) in st.iter_mut().zip(block.chunks(8)) {
        let mut w = [0u8; 8];
        w[..word.len()].copy_from_slice(word);
        *lane ^= u64::from_le_bytes(w);
    }
}

pub fn shake256(data: &[u8], out: usize) -> Vec<u8> {
    shake(136, data, out)
}

/// `tr = H(pk, 64)`.
pub fn tr(pk: &[u8]) -> [u8; 64] {
    shake256(pk, 64).try_into().unwrap()
}

/// `mu = H(tr || M', 64)` for `M'` as ML-DSA.Verify forms it from a message and a context string.
pub fn mu(pk: &[u8], message: &[u8], ctx: &[u8]) -> [u8; 64] {
    assert!(ctx.len() < 256, "a context string is at most 255 bytes");
    let mut data = tr(pk).to_vec();
    data.extend([0, ctx.len() as u8]);
    data.extend(ctx);
    data.extend(message);
    shake256(&data, 64).try_into().unwrap()
}

/// `zetas[k] = zeta^BitRev8(k) mod q`, `zeta = 1753`.
pub fn zetas() -> [u64; 256] {
    std::array::from_fn(|k| pow_mod(1753, (k as u8).reverse_bits() as u64))
}

fn pow_mod(b: u64, e: u64) -> u64 {
    (0..64).rev().fold(1, |acc, bit| {
        let sq = acc * acc % Q;
        if e >> bit & 1 == 1 { sq * b % Q } else { sq }
    })
}
