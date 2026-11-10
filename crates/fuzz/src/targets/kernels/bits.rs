//! `kernel-bits`: the 64-byte bit transpose, the bit fold (subset-sum tables, GFNI byte matrices, nibble shuffles)
//! and the streaming copy against naive loops.

use super::reference as r;
use super::{bulk_e, check};
use crate::{Ctx, Outcome, Source};
use primitives::bit_fold::{BLOCK, BitFold};
use primitives::bits::bit_transpose_64bytes;
use primitives::field::{F64, F192};
use primitives::stream::Stream;

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    match src.below(4) {
        0 => transpose(src, ctx),
        1 => fold_pair(src, ctx),
        2 => fold_columns(src, ctx),
        _ => stream(src, ctx),
    }
}

fn transpose(src: &mut Source, ctx: &Ctx) -> Outcome {
    ctx.note("transpose");
    let input: [u8; 64] = src.bulk(64).try_into().unwrap();
    let mut out = [0u8; 64];
    bit_transpose_64bytes(&input, &mut out);
    for b in 0..8 {
        for t in 0..8 {
            for x in 0..8 {
                let want = input[x * 8 + b] >> t & 1;
                check!(
                    out[b * 8 + t] >> x & 1 == want,
                    "bit_transpose_64bytes",
                    "output byte {}, bit {x} of input {input:02x?}",
                    b * 8 + t
                );
            }
        }
    }
    Ok(())
}

/// `sum_(bit s of row set) w_s`, bit `b` of byte `j` being bit `8j + b`.
fn fold_ref(weights: &[F192], row: &[u8]) -> F192 {
    let mut acc = F192::ZERO;
    for (j, &byte) in row.iter().enumerate() {
        for b in 0..8 {
            if byte >> b & 1 == 1 {
                acc = r::add_e(acc, weights[8 * j + b]);
            }
        }
    }
    acc
}

/// Rows biased to all-zero, all-one and single-bit bytes.
fn rows<const N: usize>(src: &mut Source, n: usize) -> Vec<[u8; N]> {
    let bytes = src.bulk(n * N);
    let mut out: Vec<[u8; N]> = bytes.as_chunks::<N>().0.to_vec();
    if src.chance(1, 4) {
        for row in &mut out {
            for b in row.iter_mut() {
                *b = match *b % 4 {
                    0 => 0,
                    1 => 0xff,
                    2 => 1 << (*b >> 5),
                    _ => *b,
                };
            }
        }
    }
    out
}

fn pair<const A: usize, const B: usize>(src: &mut Source) -> Outcome {
    let (wa, wb) = (bulk_e(src, 8 * A), bulk_e(src, 8 * B));
    let (fa, fb) = (BitFold::new(&wa), BitFold::new(&wb));
    let n = match src.below(3) {
        0 => BLOCK,
        1 => src.below(4),
        _ => src.below(BLOCK + 1),
    };
    let (head, tail) = (rows::<A>(src, n), rows::<B>(src, n));
    let mut out = [F192::new(9, 9, 9); BLOCK];
    fa.fold_block_pair(&fb, &head, &tail, &mut out);
    for p in 0..BLOCK {
        let want = if p < n {
            r::add_e(fold_ref(&wa, &head[p]), fold_ref(&wb, &tail[p]))
        } else {
            F192::ZERO
        };
        check!(
            out[p] == want,
            "BitFold::fold_block_pair",
            "{A}+{B} bytes, {n} rows: row {p}"
        );
    }
    Ok(())
}

fn fold_pair(src: &mut Source, ctx: &Ctx) -> Outcome {
    let shape = src.below(8);
    ctx.note(format!("fold pair shape {shape}"));
    match shape {
        0 => pair::<8, 8>(src),
        1 => pair::<16, 8>(src),
        2 => pair::<8, 16>(src),
        3 => pair::<16, 16>(src),
        4 => pair::<32, 8>(src),
        5 => pair::<64, 16>(src),
        6 => pair::<128, 8>(src),
        _ => pair::<32, 32>(src),
    }
}

fn columns<const C: usize>(src: &mut Source) -> Outcome {
    let w = bulk_e(src, 8 * C);
    let fold = BitFold::new(&w);
    let rows = rows::<C>(src, BLOCK);
    let cols: [[u8; BLOCK]; C] = std::array::from_fn(|j| std::array::from_fn(|p| rows[p][j]));
    let mut out = [F192::ZERO; BLOCK];
    fold.fold_columns(&cols, &mut out);
    for (p, row) in rows.iter().enumerate() {
        check!(
            out[p] == fold_ref(&w, row),
            "BitFold::fold_columns",
            "{C} bytes: row {p}"
        );
    }
    Ok(())
}

fn fold_columns(src: &mut Source, ctx: &Ctx) -> Outcome {
    let c = src.below(5);
    ctx.note(format!("fold columns {c}"));
    match c {
        0 => columns::<8>(src),
        1 => columns::<16>(src),
        2 => columns::<32>(src),
        3 => columns::<64>(src),
        _ => columns::<128>(src),
    }
}

/// Streaming copies at every alignment: whole lines stream, ragged heads and tails do not.
fn stream(src: &mut Source, ctx: &Ctx) -> Outcome {
    let s = Stream::new();
    let len = match src.below(3) {
        0 => src.below(8),
        1 => src.below(300),
        _ => src.below(1 << 16),
    };
    let (from, to) = (src.below(16), src.below(16));
    ctx.note(format!("stream offsets {} {}", from % 8, to % 8));
    let data = src.bulk(len + from);
    let mut dst = vec![0xa5u8; len + to + 3];
    s.copy(&mut dst[to..to + len], &data[from..from + len]);
    check!(
        dst[to..to + len] == data[from..from + len],
        "Stream::copy",
        "{len} bytes, offsets {from} {to}"
    );
    check!(
        dst[..to].iter().chain(&dst[to + len..]).all(|&b| b == 0xa5),
        "Stream::copy",
        "{len} bytes wrote outside the destination"
    );
    let words = src.bulk_u64(len / 8 + 1);
    let mut wdst = vec![0u64; words.len()];
    s.copy(&mut wdst, &words);
    check!(wdst == words, "Stream::copy", "{} words", words.len());
    let elems: Vec<F192> = words
        .chunks(3)
        .map(|c| F192::new(c[0], *c.get(1).unwrap_or(&0), 0))
        .collect();
    let mut edst = vec![F192::ZERO; elems.len()];
    s.copy(&mut edst, &elems);
    check!(edst == elems, "Stream::copy", "{} F192", elems.len());
    let k: Vec<F64> = words.iter().map(|&w| F64(w)).collect();
    let mut kdst = vec![F64::ZERO; k.len()];
    Stream::default().copy(&mut kdst, &k);
    check!(kdst == k, "Stream::copy", "{} F64", k.len());
    drop(s);
    Ok(())
}
