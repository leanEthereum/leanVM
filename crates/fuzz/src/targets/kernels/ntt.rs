//! `kernel-ntt`: `pcs::ntt::AdditiveNttF64`, whose plans (gathered passes, deep passes, streaming stores) depend on
//! the shape, against one butterfly at a time, against naive evaluation of the novel-basis polynomial at the domain
//! points, and against its own inverse.

use super::reference as r;
use super::{bulk_k, check};
use crate::{Ctx, Outcome, Source};
use pcs::ntt::AdditiveNttF64;
use primitives::field::F64;

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    match src.below(4) {
        0 => twiddles(src, ctx),
        1 => naive(src, ctx),
        2 => planned(src, ctx),
        _ => round_trip(src, ctx),
    }
}

/// `W_i(x)`, the subspace polynomial of `span(1, x, .., x^(i-1))`, by its definition: a product over the span.
fn subspace_naive(i: usize, x: u64) -> u64 {
    (0..1u64 << i).fold(1, |acc, u| r::mul_k(acc, x ^ u))
}

/// `W_i(x)` by `W_(k+1)(x) = W_k(x)^2 + W_k(x^k) W_k(x)`, for the sizes the product is too slow for.
fn subspace(i: usize, x: u64) -> u64 {
    if i <= 6 {
        return subspace_naive(i, x);
    }
    let (mut w, mut b) = (x, Vec::new());
    // `b[k] = W_k(x^k)`, by the same recurrence on the basis.
    let mut basis: Vec<u64> = (0..i).map(|k| 1u64 << k).collect();
    for k in 0..i {
        b.push(basis[k]);
        for v in basis.iter_mut().skip(k + 1) {
            *v = r::mul_k(*v, *v) ^ r::mul_k(b[k], *v);
        }
        w = r::mul_k(w, w) ^ r::mul_k(b[k], w);
    }
    w
}

/// The normalized `W_i(x) / W_i(x^i)`.
fn normalized(i: usize, x: u64) -> u64 {
    r::mul_k(subspace(i, x), r::pow_k(subspace(i, 1 << i), u128::from(u64::MAX) - 1))
}

fn twiddles(src: &mut Source, ctx: &Ctx) -> Outcome {
    let dim = src.range(1, 24);
    ctx.note(format!("twiddles dim {}", dim.min(12)));
    let ntt = AdditiveNttF64::standard(dim);
    for _ in 0..4 {
        let layer = src.below(dim);
        let i = dim - layer - 1;
        let block = match src.below(3) {
            0 => 0,
            1 => (1 << layer) - 1,
            _ => src.below(1 << layer),
        };
        // `s_i` at `sum_j bit_j(block) x^(i+1+j)`.
        let point = (0..layer)
            .filter(|j| block >> j & 1 == 1)
            .fold(0u64, |p, j| p ^ 1 << (i + 1 + j));
        let want = normalized(i, point);
        let got = ntt.twiddle(layer, block);
        check!(
            got.0 == want,
            "AdditiveNttF64::twiddle",
            "dim {dim}, layer {layer}, block {block}: got {got:?}, want {want:#x}"
        );
    }
    if dim <= 7 {
        for i in 0..dim {
            let x = src.u64();
            check!(
                subspace(i, x) == subspace_naive(i, x),
                "reference subspace recurrence",
                "i {i}"
            );
        }
    }
    Ok(())
}

/// The codeword at row `q` is the message's novel-basis polynomial at the domain point `q`, the integer under its
/// natural encoding: `sum_m msg[m] prod_(k in bits(m)) W-hat_k(q)`.
fn naive(src: &mut Source, ctx: &Ctx) -> Outcome {
    let log_msg = src.range(0, 5);
    let rate = src.range(0, 3);
    let log_d = log_msg + rate;
    let lanes = *src.pick(&[1usize, 1, 2, 3]);
    ctx.note(format!("naive rate {rate}"));
    let ntt = AdditiveNttF64::standard(log_d);
    let msg = bulk_k(src, lanes << log_msg);
    let mut data = vec![F64::ZERO; lanes << log_d];
    data[..msg.len()].copy_from_slice(&msg);
    ntt.encode_interleaved_in_place(&mut data, lanes, rate);
    let what: Vec<Vec<u64>> = (0..1usize << log_d)
        .map(|q| (0..log_msg).map(|k| normalized(k, q as u64)).collect())
        .collect();
    for q in 0..1usize << log_d {
        for l in 0..lanes {
            let want = (0..1usize << log_msg).fold(0u64, |acc, m| {
                let x = (0..log_msg)
                    .filter(|k| m >> k & 1 == 1)
                    .fold(1u64, |p, k| r::mul_k(p, what[q][k]));
                acc ^ r::mul_k(msg[m * lanes + l].0, x)
            });
            check!(
                data[q * lanes + l].0 == want,
                "encode_interleaved_in_place",
                "row {q}, lane {l} of a 2^{log_msg} message at rate {rate}: got {:?}, want {want:#x}",
                data[q * lanes + l]
            );
        }
    }
    Ok(())
}

/// One butterfly at a time over `lanes` interleaved transforms, layers `start..log_d`, the public twiddles.
fn forward_scalar(ntt: &AdditiveNttF64, data: &mut [F64], lanes: usize, start: usize) {
    let log_d = (data.len() / lanes).trailing_zeros() as usize;
    for layer in start..log_d {
        let half = 1usize << (log_d - layer - 1);
        for block in 0..1usize << layer {
            let t = ntt.twiddle(layer, block);
            let base = block * 2 * half * lanes;
            for row in 0..half {
                for l in 0..lanes {
                    let (top, bot) = (base + row * lanes + l, base + (row + half) * lanes + l);
                    let u = data[top] + data[bot] * t;
                    data[top] = u;
                    data[bot] += u;
                }
            }
        }
    }
}

/// Shapes that pick each plan: wide rows, deep transforms, ragged lane counts.
fn planned(src: &mut Source, ctx: &Ctx) -> Outcome {
    let (log_d, lanes) = match src.below(6) {
        0 => (src.range(1, 8), src.range(1, 40)),
        1 => (src.range(9, 14), *src.pick(&[1usize, 3, 8, 9, 16, 17, 24, 48, 64])),
        2 => (src.range(8, 11), *src.pick(&[256usize, 512, 1000, 2048])),
        3 => (src.range(15, 18), *src.pick(&[1usize, 2, 3, 8])),
        4 => (src.range(18, 20), 1),
        _ => (src.range(1, 12), src.range(1, 128)),
    };
    // At most 2^20 words, so the scalar reference stays well inside a cheap case.
    let log_d = log_d.min(20 - lanes.ilog2() as usize);
    let rate = src.below(log_d.min(4) + 1);
    ctx.note(format!(
        "planned log_d {} lanes {} rate {rate}",
        log_d.min(16),
        lanes.min(64)
    ));
    let ntt = AdditiveNttF64::standard(log_d);
    let msg = bulk_k(src, lanes << (log_d - rate));
    let mut want = vec![F64::ZERO; lanes << log_d];
    for replica in want.chunks_mut(msg.len()) {
        replica.copy_from_slice(&msg);
    }
    forward_scalar(&ntt, &mut want, lanes, rate);
    let mut got = vec![F64::ZERO; lanes << log_d];
    if src.chance(1, 4) {
        // Garbage past the message: the in-place encode must overwrite the replicas, not read them.
        let n = got.len();
        got.copy_from_slice(&bulk_k(src, n));
    }
    got[..msg.len()].copy_from_slice(&msg);
    ntt.encode_interleaved_in_place(&mut got, lanes, rate);
    if got != want {
        let i = got.iter().zip(&want).position(|(a, b)| a != b).unwrap();
        return Err(super::mismatch(
            "encode_interleaved_in_place",
            format!(
                "log_d {log_d}, {lanes} lanes, rate {rate}: first difference at word {i} (row {}, lane {})",
                i / lanes,
                i % lanes
            ),
        ));
    }
    Ok(())
}

/// Forward then inverse is the identity, and the inverse of a rate-`r` codeword has zeros above the message.
fn round_trip(src: &mut Source, ctx: &Ctx) -> Outcome {
    let log_d = src.range(0, 16);
    let extra = if src.chance(1, 4) { src.below(4) } else { 0 };
    let dim = (log_d + extra).min(63);
    let rate = src.below(log_d.min(3) + 1);
    ctx.note(format!("round trip rate {rate} extra {}", extra.min(1)));
    let ntt = AdditiveNttF64::standard(dim);
    let msg = bulk_k(src, 1 << (log_d - rate));
    let mut data = vec![F64::ZERO; 1 << log_d];
    data[..msg.len()].copy_from_slice(&msg);
    if dim == log_d {
        ntt.encode_interleaved_in_place(&mut data, 1, rate);
    } else {
        for replica in data.chunks_mut(msg.len()) {
            replica.copy_from_slice(&msg);
        }
        forward_scalar(&ntt, &mut data, 1, rate);
    }
    ntt.inverse_transform(&mut data);
    check!(
        data[..msg.len()] == msg[..],
        "inverse_transform",
        "2^{log_d} words, dim {dim}, rate {rate}: the message is not recovered"
    );
    check!(
        data[msg.len()..].iter().all(|w| w.0 == 0),
        "inverse_transform",
        "2^{log_d} words, dim {dim}, rate {rate}: a codeword has coefficients above its degree bound"
    );
    Ok(())
}
