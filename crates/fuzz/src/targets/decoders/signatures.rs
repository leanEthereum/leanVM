//! `decode-signatures`: leanXMSS and leanSPHINCS public keys and signatures from bytes.
//!
//! Oracles: the fixed-size decoders are bijections (decode then encode is the identity, both ways); verifying garbage
//! never panics and never accepts; an honest signature verifies; and one changed bit or byte of a real signature, its
//! key or its message is refused (Critical otherwise). Keys and signatures are made once per process: leanXMSS keys
//! whose prepared bottom tree holds their fixture leaves, one range ending at the last leaf index, and a leanSPHINCS key.

use crate::{Ctx, Finding, Outcome, Source, catch};
use signatures::lean_sphincs::{self, LeanSphincsPublicKey, LeanSphincsSignature};
use signatures::lean_xmss::{self, LeanXmssPublicKey, LeanXmssSecretKey, LeanXmssSignature};
use std::sync::OnceLock;

struct Fixtures {
    lean_xmss: Vec<(LeanXmssPublicKey, [u8; 32], LeanXmssSignature)>,
    xmss_keys: Vec<(LeanXmssSecretKey, LeanXmssPublicKey, u32, u32)>,
    sphincs: Vec<(LeanSphincsPublicKey, [u8; 32], LeanSphincsSignature)>,
    sphincs_key: (lean_sphincs::LeanSphincsSecretKey, LeanSphincsPublicKey),
}

fn fixtures() -> &'static Fixtures {
    static F: OnceLock<Fixtures> = OnceLock::new();
    F.get_or_init(|| {
        // Ranges inside one bottom tree each, so the prepared tree serves every fresh sign.
        let ranges = [(0u32, 2u32), (0xfffe, 0xffff), (u32::MAX - 1, u32::MAX)];
        let mut lean_xmss = Vec::new();
        let mut xmss_keys = Vec::new();
        for (k, &(first, last)) in ranges.iter().enumerate() {
            let mut seed = [0x5au8; 32];
            seed[0] = k as u8;
            let (sk, pk) = lean_xmss::key_gen_from_seed(seed);
            sk.prepare(first).expect("prepare");
            for (j, leaf) in [first, last].into_iter().enumerate() {
                let msg: [u8; 32] = std::array::from_fn(|i| (i * 7 + k * 3 + j) as u8);
                let sig = lean_xmss::sign(&sk, &msg, leaf).expect("signs");
                lean_xmss.push((pk, msg, sig));
            }
            xmss_keys.push((sk, pk, first, last));
        }
        let (sk, pk) = lean_sphincs::key_gen_from_seed([0x3c; 32]);
        let sphincs = (0..2u8)
            .map(|j| {
                let msg = [j.wrapping_mul(91); 32];
                (pk, msg, lean_sphincs::sign(&sk, &msg).expect("sign"))
            })
            .collect();
        Fixtures {
            lean_xmss,
            xmss_keys,
            sphincs,
            sphincs_key: (sk, pk),
        }
    })
}

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let f = fixtures();
    match src.below(8) {
        0 => garbage(src, ctx),
        1 => digest_fields(src, ctx),
        2 => fresh(src, ctx, f),
        3 | 4 => xmss_tamper(src, ctx, f),
        _ => sphincs_tamper(src, ctx, f),
    }
}

fn flip(bytes: &mut [u8], src: &mut Source) -> &'static str {
    let n = bytes.len();
    match src.below(5) {
        0 | 1 => {
            bytes[src.below(n)] ^= 1 << src.below(8);
            "bit"
        }
        2 => {
            let i = src.below(n);
            bytes[i] = bytes[i].wrapping_add(src.range(1, 255) as u8);
            "byte"
        }
        3 => {
            // A whole 16-byte digest zeroed or set.
            let i = src.below(n / 16) * 16;
            let v = if src.bool() { 0 } else { 0xff };
            bytes[i..(i + 16).min(n)].fill(v);
            "digest"
        }
        _ => {
            // Two digests swapped.
            let (i, j) = (src.below(n / 16) * 16, src.below(n / 16) * 16);
            for k in 0..16.min(n - i.max(j)) {
                bytes.swap(i + k, j + k);
            }
            "swap"
        }
    }
}

fn verdict<T>(what: &str, f: impl FnOnce() -> T) -> Result<T, Finding> {
    catch(f).map_err(|(m, l)| Finding::panic(&m, &l).in_context(what))
}

fn xmss_tamper(src: &mut Source, ctx: &Ctx, f: &Fixtures) -> Outcome {
    let (pk, msg, sig) = &f.lean_xmss[src.below(f.lean_xmss.len())];
    let (mut pkb, mut m, mut sb) = (pk.to_bytes(), *msg, sig.to_bytes());
    let part = src.below(4);
    let how = match part {
        0 => flip(&mut pkb, src),
        1 => flip(&mut m, src),
        _ => flip(&mut sb, src),
    };
    if (pkb, m, sb) == (pk.to_bytes(), *msg, sig.to_bytes()) {
        return Ok(());
    }
    ctx.note(format!(
        "lean_xmss {} {how}",
        ["key", "message", "signature", "signature"][part]
    ));
    let (pk2, sig2) = (LeanXmssPublicKey::from_bytes(&pkb), LeanXmssSignature::from_bytes(&sb));
    let accepted = verdict("lean_xmss::verify", || lean_xmss::verify(&pk2, &m, &sig2))?;
    if accepted.is_ok()
        && !f
            .lean_xmss
            .iter()
            .any(|(p, mm, s)| (p.to_bytes(), *mm, s.to_bytes()) == (pkb, m, sb))
    {
        return Err(Finding::critical(
            format!(
                "lean_xmss::verify accepted a tampered {}",
                ["key", "message", "signature", "signature"][part]
            ),
            format!("{how} edit, leaf index {}", sig.leaf_index()),
        ));
    }
    // The untouched triple still verifies.
    let honest = verdict("lean_xmss::verify", || lean_xmss::verify(pk, msg, sig))?;
    if honest.is_err() {
        return Err(Finding::high(
            "lean_xmss::verify refused an honest signature",
            format!("{honest:?}"),
        ));
    }
    Ok(())
}

fn sphincs_tamper(src: &mut Source, ctx: &Ctx, f: &Fixtures) -> Outcome {
    let (pk, msg, sig) = &f.sphincs[src.below(f.sphincs.len())];
    let (mut pkb, mut m, mut sb) = (pk.to_bytes(), *msg, sig.to_bytes());
    let part = src.below(4);
    let how = match part {
        0 => flip(&mut pkb, src),
        1 => flip(&mut m, src),
        _ => flip(&mut sb, src),
    };
    if (pkb, m) == (pk.to_bytes(), *msg) && sb == sig.to_bytes() {
        return Ok(());
    }
    ctx.note(format!(
        "sphincs {} {how}",
        ["key", "message", "signature", "signature"][part]
    ));
    let (pk2, sig2) = (
        LeanSphincsPublicKey::from_bytes(&pkb),
        LeanSphincsSignature::from_bytes(&sb),
    );
    let accepted = verdict("lean_sphincs::verify", || lean_sphincs::verify(&pk2, &m, &sig2))?;
    if accepted.is_ok() {
        let known = f
            .sphincs
            .iter()
            .any(|(p, mm, s)| p.to_bytes() == pkb && *mm == m && s.to_bytes() == sb);
        if !known {
            return Err(Finding::critical(
                format!(
                    "lean_sphincs::verify accepted a tampered {}",
                    ["key", "message", "signature", "signature"][part]
                ),
                format!("{how} edit"),
            ));
        }
    }
    let honest = verdict("lean_sphincs::verify", || lean_sphincs::verify(pk, msg, sig))?;
    if honest.is_err() {
        return Err(Finding::high(
            "lean_sphincs::verify refused an honest signature",
            format!("{honest:?}"),
        ));
    }
    Ok(())
}

/// Random bytes as keys and signatures: decode is a bijection, and verification refuses without panicking.
fn garbage(src: &mut Source, ctx: &Ctx) -> Outcome {
    let f = fixtures();
    if src.bool() {
        ctx.note("lean_xmss garbage");
        let pkb: [u8; lean_xmss::PUB_KEY_SIZE] = src.bulk(lean_xmss::PUB_KEY_SIZE).try_into().unwrap();
        let mut sb: [u8; lean_xmss::SIG_SIZE] = src.bulk(lean_xmss::SIG_SIZE).try_into().unwrap();
        if src.bool() {
            // A real key, a signature with garbage after a real leaf index.
            sb[..4].copy_from_slice(&f.lean_xmss[0].2.leaf_index().to_le_bytes());
        }
        let msg: [u8; 32] = src.bulk(32).try_into().unwrap();
        let (pk, sig) = (LeanXmssPublicKey::from_bytes(&pkb), LeanXmssSignature::from_bytes(&sb));
        if pk.to_bytes() != pkb || sig.to_bytes() != sb {
            return Err(Finding::high("leanXMSS from_bytes is not the inverse of to_bytes", ""));
        }
        let key = if src.bool() {
            pk
        } else {
            f.lean_xmss[src.below(f.lean_xmss.len())].0
        };
        if verdict("lean_xmss::verify", || lean_xmss::verify(&key, &msg, &sig))?.is_ok() {
            return Err(Finding::critical("lean_xmss::verify accepted a random signature", ""));
        }
    } else {
        ctx.note("sphincs garbage");
        let pkb: [u8; lean_sphincs::PUB_KEY_SIZE] = src.bulk(lean_sphincs::PUB_KEY_SIZE).try_into().unwrap();
        let sb: [u8; lean_sphincs::SIG_SIZE] = src.bulk(lean_sphincs::SIG_SIZE).try_into().unwrap();
        let msg: [u8; 32] = src.bulk(32).try_into().unwrap();
        let (pk, sig) = (
            LeanSphincsPublicKey::from_bytes(&pkb),
            LeanSphincsSignature::from_bytes(&sb),
        );
        if pk.to_bytes() != pkb || sig.to_bytes() != sb {
            return Err(Finding::high(
                "leanSPHINCS from_bytes is not the inverse of to_bytes",
                "",
            ));
        }
        let key = if src.bool() { pk } else { f.sphincs_key.1 };
        if verdict("lean_sphincs::verify", || lean_sphincs::verify(&key, &msg, &sig))?.is_ok() {
            return Err(Finding::critical(
                "lean_sphincs::verify accepted a random signature",
                "",
            ));
        }
        let seed: [u8; 32] = src.bulk(32).try_into().unwrap();
        if lean_sphincs::LeanSphincsSecretKey::from_bytes(&seed).to_bytes() != seed {
            return Err(Finding::high(
                "leanSPHINCS secret key from_bytes is not the inverse of to_bytes",
                "",
            ));
        }
    }
    Ok(())
}

/// `digest_fields` (FIPS 205 Algorithm 19's split of the message digest) against a bit-by-bit reading.
fn digest_fields(src: &mut Source, ctx: &Ctx) -> Outcome {
    use lean_sphincs::{DIGEST_CALLS, FORS_HEIGHT, FORS_TREES, H, LAYER_HEIGHTS, MD_BYTES, TREE_INDEX_BYTES};
    ctx.note("digest fields");
    let d: [u8; 32 * DIGEST_CALLS] = src.bulk(32 * DIGEST_CALLS).try_into().unwrap();
    let bit = |p: usize| (d[p / 8] >> (7 - p % 8) & 1) as usize;
    let leaves: Vec<usize> = (0..FORS_TREES)
        .map(|c| (0..FORS_HEIGHT).fold(0, |v, j| 2 * v + bit(FORS_HEIGHT * c + j)))
        .collect();
    // The tree index's low `H - h0` bits, then the leaf's low `h0`, each a big-endian integer.
    let be = |bytes: &[u8]| bytes.iter().fold(0u128, |v, &b| v << 8 | u128::from(b));
    let tree = be(&d[MD_BYTES..MD_BYTES + TREE_INDEX_BYTES]) % (1 << (H - LAYER_HEIGHTS[0]));
    let leaf = be(&d[MD_BYTES + TREE_INDEX_BYTES..lean_sphincs::DIGEST_BYTES]) % (1 << LAYER_HEIGHTS[0]);
    let want = ((tree << LAYER_HEIGHTS[0] | leaf) as u64, leaves);
    let (idx, got) = lean_sphincs::digest_fields(&d);
    if (idx, got.to_vec()) != want {
        return Err(Finding::high(
            "lean_sphincs::digest_fields disagrees with its reference",
            format!("got index {idx}, want {}", want.0),
        ));
    }
    Ok(())
}

/// A fresh signature on a random message: leanXMSS at any leaf of a key's range, leanSPHINCS rarely (it builds its
/// FORS and lower trees per message). Both verify, and only for their message.
fn fresh(src: &mut Source, ctx: &Ctx, f: &Fixtures) -> Outcome {
    let msg: [u8; 32] = src.bulk(32).try_into().unwrap();
    let mut other = msg;
    other[src.below(32)] ^= 1 << src.below(8);
    if src.chance(1, 16) {
        ctx.note("sphincs fresh");
        let (sk, pk) = &f.sphincs_key;
        let sig = verdict("lean_sphincs::sign", || lean_sphincs::sign(sk, &msg))?
            .map_err(|e| Finding::high("lean_sphincs::sign failed", format!("{e}")))?;
        let back = LeanSphincsSignature::from_bytes(&sig.to_bytes());
        if back != sig {
            return Err(Finding::high("leanSPHINCS signature does not round-trip its bytes", ""));
        }
        if lean_sphincs::verify(pk, &msg, &back).is_err() {
            return Err(Finding::high(
                "lean_sphincs::verify refused a fresh honest signature",
                "",
            ));
        }
        if lean_sphincs::verify(pk, &other, &back).is_ok() {
            return Err(Finding::critical(
                "lean_sphincs::verify accepted a signature for another message",
                "",
            ));
        }
        return Ok(());
    }
    let (sk, pk, first, last) = &f.xmss_keys[src.below(f.xmss_keys.len())];
    let leaf = first + src.below((last - first) as usize + 1) as u32;
    ctx.note("lean_xmss fresh");
    let sig = verdict("lean_xmss::sign", || lean_xmss::sign(sk, &msg, leaf))?
        .map_err(|e| Finding::high("lean_xmss::sign failed on a prepared key", format!("{e}")))?;
    if sig.leaf_index() != leaf || LeanXmssSignature::from_bytes(&sig.to_bytes()) != sig {
        return Err(Finding::high("leanXMSS signature does not round-trip its bytes", ""));
    }
    if lean_xmss::verify(pk, &msg, &sig).is_err() {
        return Err(Finding::high(
            "lean_xmss::verify refused a fresh honest signature",
            format!("leaf index {leaf}"),
        ));
    }
    if lean_xmss::verify(pk, &other, &sig).is_ok() {
        return Err(Finding::critical(
            "lean_xmss::verify accepted a signature for another message",
            "",
        ));
    }
    // Another key's signature under this key.
    let (_, opk, ..) = &f.xmss_keys[(f.xmss_keys.iter().position(|k| k.1 == *pk).unwrap() + 1) % f.xmss_keys.len()];
    if lean_xmss::verify(opk, &msg, &sig).is_ok() {
        return Err(Finding::critical(
            "lean_xmss::verify accepted another key's signature",
            "",
        ));
    }
    Ok(())
}
