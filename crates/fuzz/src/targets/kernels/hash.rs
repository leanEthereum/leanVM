//! `kernel-hash`: every public entry of `primitives::hash` against `sha3`'s Keccak-256 and a reference permutation.

use super::reference as r;
use super::{check, mismatch};
use crate::{Ctx, Outcome, Source};
use primitives::hash::{
    self, Hasher, LANES, OUT_LEN, PAD_FIRST, PAD_LAST, RATE, STATE_LANES, digest_halves_from, digest_of, final_state,
    hash_many, hash_many_from_state, keccak_f, keccak_f_many, permutations, zero_prefix_state,
};

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    match src.below(6) {
        0 => one_shot(src, ctx),
        1 => streaming(src, ctx),
        2 => batched(src, ctx),
        3 => permutation(src, ctx),
        4 => halves(src, ctx),
        _ => from_state(src, ctx),
    }
}

/// A message length near a block boundary, or anywhere up to a few blocks, or rarely huge.
fn length(src: &mut Source) -> usize {
    match src.below(10) {
        0 => src.below(3),
        1..=4 => boundary(src),
        5 => src.below(64) + 1,
        6 => 64,
        7 => src.below(1 << 20),
        _ => src.below(4 * RATE),
    }
    .min(1 << 20)
}

/// Lengths that land on the padding's edges: a block boundary minus 2 to plus 2.
fn boundary(src: &mut Source) -> usize {
    (RATE * src.below(5) + src.below(5)).saturating_sub(2)
}

fn one_shot(src: &mut Source, ctx: &Ctx) -> Outcome {
    let len = if src.bool() { boundary(src) } else { length(src) };
    ctx.note(format!("one-shot blocks {}", (len / RATE).min(3)));
    let data = src.bulk(len);
    let want = r::keccak256(&data);
    let got = hash::hash(&data);
    check!(got == want, "hash", "{len} bytes: got {got:02x?}, want {want:02x?}");
    check!(
        fiat_shamir::merkle::hash_leaf(&data) == want,
        "fiat_shamir::merkle::hash_leaf",
        "{len} bytes"
    );
    check!(permutations(len) == len / RATE + 1, "permutations", "{len} bytes");
    // final_state: one permutation away from the digest.
    let mut state = final_state(&data);
    keccak_f(&mut state);
    check!(digest_of(&state) == want, "final_state", "{len} bytes");
    Ok(())
}

fn streaming(src: &mut Source, ctx: &Ctx) -> Outcome {
    let len = length(src).min(1 << 14);
    let data = src.bulk(len);
    let mut hasher = Hasher::new();
    let mut at = 0;
    let mut chunks = 0;
    while at < len {
        let take = match src.below(5) {
            0 => 0,
            1 => 1,
            2 => RATE - (at % RATE),
            3 => src.below(2 * RATE),
            _ => src.below(len - at + 1),
        }
        .min(len - at);
        hasher.update(&data[at..at + take]);
        at += take;
        chunks += 1;
        if chunks > 4 * len + 8 {
            hasher.update(&data[at..]);
            at = len;
        }
        if src.chance(1, 16) {
            // `finalize` takes `&self`: the hasher keeps absorbing after it.
            let mid = hasher.finalize();
            check!(
                mid == r::keccak256(&data[..at]),
                "Hasher finalize mid-stream",
                "{at} of {len} bytes"
            );
        }
    }
    let cloned = hasher.clone();
    hasher.update(&[]);
    ctx.note(format!("streaming chunks {}", chunks.min(8)));
    let want = r::keccak256(&data);
    check!(hasher.finalize() == want, "Hasher", "{len} bytes in {chunks} chunks");
    check!(cloned.finalize() == want, "Hasher clone", "{len} bytes");
    check!(Hasher::default().finalize() == r::keccak256(&[]), "Hasher default", "");
    Ok(())
}

fn batched(src: &mut Source, ctx: &Ctx) -> Outcome {
    let len = if src.bool() {
        boundary(src)
    } else {
        length(src).min(1 << 12)
    };
    let n = match src.below(4) {
        0 => src.below(LANES + 1),
        1 => LANES * src.range(1, 3) + src.below(2),
        _ => src.below(4 * LANES + 3),
    };
    ctx.note(format!("hash_many lanes {}", n % LANES));
    let data = src.bulk(n * len);
    let mut out = vec![0u8; n * OUT_LEN];
    hash_many(&data, len, &mut out);
    for i in 0..n {
        let want = r::keccak256(&data[i * len..(i + 1) * len]);
        check!(
            out[i * OUT_LEN..(i + 1) * OUT_LEN] == want,
            "hash_many",
            "input {i} of {n}, {len} bytes each"
        );
    }
    // From a shared zero prefix, as the PCS leaves are hashed.
    let blocks = src.below(4);
    let state = zero_prefix_state(blocks);
    let mut want_state = [0u64; STATE_LANES];
    for _ in 0..blocks {
        r::keccak_f(&mut want_state);
    }
    check!(state == want_state, "zero_prefix_state", "{blocks} blocks");
    let mut out = vec![0u8; n * OUT_LEN];
    hash_many_from_state(&data, len, &state, &mut out);
    for i in 0..n {
        let image = [vec![0u8; blocks * RATE], data[i * len..(i + 1) * len].to_vec()].concat();
        check!(
            out[i * OUT_LEN..(i + 1) * OUT_LEN] == r::keccak256(&image),
            "hash_many_from_state",
            "input {i} of {n}, {len} bytes after {blocks} zero blocks"
        );
    }
    Ok(())
}

fn random_state(src: &mut Source) -> [u64; STATE_LANES] {
    let mut s: [u64; STATE_LANES] = src.bulk_u64(STATE_LANES).try_into().unwrap();
    for _ in 0..src.below(3) {
        let i = src.below(STATE_LANES);
        s[i] = src.edgy_u64();
    }
    s
}

fn permutation(src: &mut Source, ctx: &Ctx) -> Outcome {
    let s = random_state(src);
    let mut want = s;
    r::keccak_f(&mut want);
    let mut got = s;
    keccak_f(&mut got);
    check!(got == want, "keccak_f", "state {s:x?}");
    let n = match src.below(3) {
        0 => src.below(LANES + 1),
        1 => LANES * src.range(1, 4) + src.below(LANES),
        _ => src.below(40),
    };
    ctx.note(format!("keccak_f_many tail {}", n % LANES));
    let states: Vec<[u64; STATE_LANES]> = (0..n).map(|_| random_state(src)).collect();
    let mut many = states.clone();
    keccak_f_many(&mut many);
    for (i, (before, after)) in states.iter().zip(&many).enumerate() {
        let mut want = *before;
        r::keccak_f(&mut want);
        check!(*after == want, "keccak_f_many", "state {i} of {n}");
    }
    Ok(())
}

/// `digest_halves_from`: a template final state with 16 bytes left zero, each value XORed in.
fn halves(src: &mut Source, ctx: &Ctx) -> Outcome {
    // One block, the value's 16 bytes inside the message, its lanes before the padding's last one.
    let len = src.range(16, RATE - 1);
    let at = src.below(((len - 16) / 8).min(RATE / 8 - 3) + 1);
    let mut data = src.bulk(len);
    data[8 * at..8 * at + 16].fill(0);
    let template = final_state(&data);
    let n = src.below(3 * LANES + 2);
    ctx.note(format!("digest_halves lanes {}", n % LANES));
    let values: Vec<u128> = (0..n)
        .map(|_| u128::from(src.edgy_u64()) | u128::from(src.u64()) << 64)
        .collect();
    let mut out = vec![0u128; n];
    digest_halves_from(&template, at, &values, &mut out);
    for (i, &v) in values.iter().enumerate() {
        let mut image = data.clone();
        image[8 * at..8 * at + 16].copy_from_slice(&v.to_le_bytes());
        let d = r::keccak256(&image);
        let want = u128::from_le_bytes(d[..16].try_into().unwrap());
        check!(
            out[i] == want,
            "digest_halves_from",
            "value {i} of {n} at lane {at}, {len}-byte input"
        );
    }
    Ok(())
}

/// The padding constants and the final-block layout, through `final_state` on a message that fills a block to the
/// last byte (where `PAD_FIRST` and `PAD_LAST` share a byte).
fn from_state(src: &mut Source, ctx: &Ctx) -> Outcome {
    ctx.note("padding");
    check!(
        PAD_FIRST == 0x01 && PAD_LAST == 0x80,
        "padding constants",
        "Ethereum's Keccak-256"
    );
    let len = RATE * src.below(3) + RATE - 1;
    let data = src.bulk(len);
    let state = final_state(&data);
    let mut want = [0u64; STATE_LANES];
    let mut padded = data.clone();
    padded.push(PAD_FIRST | PAD_LAST);
    let blocks = padded.len() / RATE;
    for (b, block) in padded.chunks(RATE).enumerate() {
        for (i, w) in block.chunks(8).enumerate() {
            want[i] ^= u64::from_le_bytes(w.try_into().unwrap());
        }
        if b + 1 < blocks {
            r::keccak_f(&mut want);
        }
    }
    if state != want {
        return Err(mismatch(
            "final_state",
            format!("{len}-byte message whose padding shares a byte"),
        ));
    }
    Ok(())
}
