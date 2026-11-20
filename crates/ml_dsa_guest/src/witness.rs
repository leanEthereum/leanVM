//! The guest's advice: the run of `guests/ml_dsa.py` replayed on integers, each hint stream in the order the guest
//! pops it.

use verifier::E;

use crate::fips::{self, D, Params, Q};
use crate::{Claim, Rejected, Streams};

/// `g^v` for an integer `v` the exponent holds, `v` taken mod `2^64 - 1` (a negative `v` wraps, and no range check
/// passes it).
fn g(v: i128) -> E {
    E::new(2, 0).pow(v.rem_euclid((1 << 64) - 1) as u64)
}

fn lane(bytes: &[u8]) -> E {
    E::new(u64::from_le_bytes(bytes.try_into().unwrap()), 0)
}

/// The hint streams as they fill.
#[derive(Default)]
struct Builder(Streams);

impl Builder {
    fn push(&mut self, name: &str, entry: Vec<E>) {
        match self.0.iter_mut().find(|(n, _)| n == name) {
            Some((_, entries)) => entries.push(entry),
            None => self.0.push((name.to_string(), vec![entry])),
        }
    }

    /// A reduction `x = r + q t` as `reduce_mul` reads it: `r`, `r < 2^23`, in limbs of 12 and 11 bits, then `t`,
    /// `t < 2^33`, in limbs of 12, 12 and 9.
    fn red(&mut self, x: i128) {
        let (r, t) = (x.rem_euclid(Q as i128), x.div_euclid(Q as i128));
        assert!(
            (0..1 << 33).contains(&t),
            "a reduction's quotient {t} is past its limbs"
        );
        self.push(
            "red",
            vec![g(r & 4095), g(r >> 12), g(t & 4095), g(t >> 12 & 4095), g(t >> 24)],
        );
    }
}

/// The UseHint columns: for each index `k' = r1 + (m + 1) s + (2m + 1) h`, `r1 2 gamma2 + s gamma2`, `h` and
/// UseHint's result, where `s` says `r0 > 0`.
pub fn use_hint_columns(p: &Params) -> [Vec<u64>; 3] {
    let m = p.m();
    let (mut d, mut h, mut w1) = (vec![], vec![], vec![]);
    for kp in 0..4 * m + 2 {
        let (hb, k) = (kp / (2 * m + 1), kp % (2 * m + 1));
        let (s, r1) = (k / (m + 1), k % (m + 1));
        d.push(r1 * 2 * p.gamma2 + s * p.gamma2);
        h.push(hb);
        w1.push(match (hb, s) {
            (0, _) => r1 % m,
            (_, 1) => (r1 + 1) % m,
            _ => (r1 + m - 1) % m,
        });
    }
    [d, h, w1]
}

/// The streams of the claims in order, or why the guest cannot accept one.
pub fn streams(p: &Params, claims: &[Claim]) -> Result<Streams, Rejected> {
    let mut s = Builder::default();
    for claim in claims {
        claim_streams(p, claim, &mut s)?;
    }
    Ok(s.0)
}

fn claim_streams(p: &Params, claim: &Claim, s: &mut Builder) -> Result<(), Rejected> {
    let pk = fips::decode_pk(p, &claim.pk).ok_or(Rejected::MalformedKey)?;
    let sig = fips::decode_sig(p, &claim.sig).ok_or(Rejected::MalformedSignature)?;
    let (k, l, tau) = (p.k, p.l, p.tau);

    s.push("rho", claim.pk[..32].chunks(8).map(lane).collect());
    for i in 0..k {
        for u in 0..8 {
            let bytes = &claim.pk[32 + 320 * i + 40 * u..][..40];
            s.push("t1", bytes.iter().map(|&b| g(b.into())).collect());
        }
    }
    s.push("mu", claim.mu.chunks(8).map(lane).collect());

    // ExpandA: five SHAKE128 blocks a polynomial, the accepted candidates' values.
    let mut a_hat = vec![vec![[0i128; 256]; l]; k];
    for (i, row) in a_hat.iter_mut().enumerate() {
        for (j, poly) in row.iter_mut().enumerate() {
            let mut seed = pk.rho.to_vec();
            seed.extend([j as u8, i as u8]);
            let bytes = fips::shake(168, &seed, 5 * 168);
            let mut n = 0;
            for block in bytes.chunks(168) {
                s.push("exa", block.iter().map(|&b| g(b.into())).collect());
                for c in block.chunks(3) {
                    let v = u64::from(c[0]) | u64::from(c[1]) << 8 | u64::from(c[2] & 127) << 16;
                    if c[2] & 127 == 127 {
                        s.push("exr", vec![E::new(u64::from(v >= Q), 0)]);
                    }
                    if v < Q {
                        if n < 256 {
                            poly[n] = v.into();
                        }
                        n += 1;
                    }
                }
            }
            if n < 256 {
                return Err(Rejected::Unsupported("ExpandA needs a sixth block"));
            }
        }
    }

    // SampleInBall: one SHAKE256 block, its first lane the signs.
    s.push("ct", sig.ctilde.chunks(8).map(lane).collect());
    let block = fips::shake256(&sig.ctilde, 136);
    s.push("sib", block.iter().map(|&b| g(b.into())).collect());
    let signs = u64::from_le_bytes(block[..8].try_into().unwrap());
    let mut js = vec![];
    for &j in &block[8..] {
        if js.len() == tau {
            break;
        }
        let i = 256 - tau + js.len();
        let accept = usize::from(j) <= i;
        s.push("sibf", vec![E::new(u64::from(!accept), 0)]);
        if accept {
            js.push(usize::from(j));
        }
    }
    if js.len() < tau {
        return Err(Rejected::Unsupported("SampleInBall needs a second block"));
    }
    let mut c = [0i128; 256];
    for (kk, &j) in js.iter().enumerate() {
        let i = 256 - tau + kk;
        c[i] = c[j];
        c[j] = if signs >> kk & 1 == 1 { -1 } else { 1 };
    }

    // NTT(z), z lifted by q.
    let zetas = fips::zetas();
    let mut z_hat = vec![[0i128; 256]; l];
    for (j, zj) in sig.z.iter().enumerate() {
        s.push(
            "z",
            zj.iter().map(|&z| g(i128::from(z) + p.z_bound() as i128)).collect(),
        );
        let mut w: [i128; 256] = std::array::from_fn(|n| i128::from(zj[n]) + Q as i128);
        for lay in 0..8 {
            let len = 128 >> lay;
            let mut nw = [0i128; 256];
            for jj in 0..len {
                for blk in 0..1 << lay {
                    let st = 2 * len * blk + jj;
                    let (a, b) = (w[st], w[st + len]);
                    let x = i128::from(zetas[(1 << lay) + blk]) * b;
                    s.red(x);
                    let r = x.rem_euclid(Q as i128);
                    nw[st] = a + r;
                    nw[st + len] = a + Q as i128 - r;
                }
            }
            w = nw;
        }
        for (m, &x) in w.iter().enumerate() {
            let (r, t) = (x.rem_euclid(Q as i128), x.div_euclid(Q as i128));
            s.push("zr", vec![g(r & 4095), g(r >> 12), g(t)]);
            z_hat[j][m] = r;
        }
    }

    // A NTT(z), then NTT^-1 without its factor 256^-1.
    let mut w_hat = vec![[0i128; 256]; k];
    for m in 0..256 {
        for i in 0..k {
            let x: i128 = (0..l).map(|j| a_hat[i][j][m] * z_hat[j][m]).sum();
            s.red(x);
            w_hat[i][m] = x.rem_euclid(Q as i128);
        }
    }
    let mut o = vec![[0i128; 256]; k];
    for i in 0..k {
        let mut w = w_hat[i];
        for lay in 0..8 {
            let len = 1 << lay;
            let mut nw = [0i128; 256];
            for jj in 0..len {
                for blk in 0..128 >> lay {
                    let st = 2 * len * blk + jj;
                    let (a, b) = (w[st], w[st + len]);
                    nw[st] = a + b;
                    let d = a + (2 << lay) * Q as i128 - b;
                    assert!(d >= 0);
                    let x = d * (Q - zetas[(256 >> lay) - 1 - blk]) as i128;
                    s.red(x);
                    nw[st + len] = x.rem_euclid(Q as i128);
                }
            }
            w = nw;
        }
        o[i] = w;
    }

    // w' = 256^-1 o - c t1 2^d, UseHint, the hint bits counted.
    let m_w1 = p.m() as i128;
    let gamma2 = p.gamma2 as i128;
    let k1 = (32736i128 * (1 << 31) + 64 * 1023 * 8192) / Q as i128 + 1;
    for i in 0..k {
        let ct1: [i128; 256] = std::array::from_fn(|m| {
            (0..256)
                .map(|n| {
                    let t = i128::from(pk.t1[i][(m + 256 - n) % 256]);
                    if n <= m { c[n] * t } else { -c[n] * t }
                })
                .sum()
        });
        for m in 0..256 {
            let x = -32736 * o[i][m] - (ct1[m] << D) + k1 * Q as i128;
            let rr = x.rem_euclid(Q as i128);
            // Decompose, the r1 = m case kept as r1 = m, r0 <= 0.
            let mut r0 = rr.rem_euclid(2 * gamma2);
            if r0 > gamma2 {
                r0 -= 2 * gamma2;
            }
            let r1 = (rr - r0) / (2 * gamma2);
            let sb = i128::from(r0 > 0);
            let h = i128::from(sig.h[i][m]);
            let kp = r1 + (m_w1 + 1) * sb + (2 * m_w1 + 1) * h;
            let u = r0 + gamma2 - 1 - sb * gamma2;
            let t = (x + gamma2 - 1 - (r1 * 2 * gamma2 + sb * gamma2) - u) / Q as i128;
            assert_eq!(x + gamma2 - 1, r1 * 2 * gamma2 + sb * gamma2 + u + t * Q as i128);
            assert!((0..1 << 33).contains(&t));
            s.push("fin", vec![g(kp), g(u), g(t & 4095), g(t >> 12 & 4095), g(t >> 24)]);
        }
    }
    Ok(())
}
