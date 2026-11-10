//! `kernel-parallel`: the claim-counter pool. Every primitive on item counts and chunk sizes at the edges (zero, one,
//! primes, many items of no work) against a sequential loop; a panicking task and a nested dispatch surface on the
//! dispatcher and leave the pool usable.

use super::check;
use crate::{Ctx, Outcome, Source, catch};
use std::sync::atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering};

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let n = count(src);
    let op = src.below(12);
    ctx.note(format!("parallel op {op} size {}", bucket(n)));
    match op {
        0 => each(src, n),
        1 => each_chunk(src, n),
        2 => chunks(src, n),
        3 => zip(src, n),
        4 => each_mut_fill(src, n),
        5 => collect(src, n),
        6 => first(src, n),
        7 => reductions(src, n),
        8 => chunk_reductions(src, n),
        9 => recommended(src, n),
        10 => panics(src, n, ctx),
        _ => nested(src, n, ctx),
    }
}

fn count(src: &mut Source) -> usize {
    match src.below(8) {
        0 => src.below(3),
        1 => *src.pick(&[61usize, 63, 64, 65, 127, 4093, 4096, 4097]),
        2 => src.below(1 << 18),
        3 => (1 << src.below(17)) + src.below(3),
        _ => src.below(5000),
    }
}

fn bucket(n: usize) -> &'static str {
    match n {
        0 => "0",
        1 => "1",
        2..=64 => "small",
        65..=4096 => "medium",
        _ => "large",
    }
}

fn chunk(src: &mut Source, n: usize) -> usize {
    match src.below(5) {
        0 => 1,
        1 => n.max(1),
        2 => n + 1 + src.below(5),
        3 => *src.pick(&[2usize, 3, 7, 64, 97]),
        _ => src.range(1, n.max(1)),
    }
}

/// Each index exactly once.
fn each(_src: &mut Source, n: usize) -> Outcome {
    let hits: Vec<AtomicU32> = (0..n).map(|_| AtomicU32::new(0)).collect();
    parallel::for_each(n, |i| {
        hits[i].fetch_add(1, Ordering::Relaxed);
    });
    let bad = hits.iter().position(|h| h.load(Ordering::Relaxed) != 1);
    check!(
        bad.is_none(),
        "parallel::for_each",
        "{n} tasks: index {bad:?} not run exactly once"
    );
    Ok(())
}

fn each_chunk(_src: &mut Source, n: usize) -> Outcome {
    let hits: Vec<AtomicU32> = (0..n).map(|_| AtomicU32::new(0)).collect();
    let bad_range = AtomicUsize::new(0);
    parallel::for_each_chunk(n, |start, end| {
        if start >= end || end > n {
            bad_range.fetch_add(1, Ordering::Relaxed);
            return;
        }
        for h in &hits[start..end] {
            h.fetch_add(1, Ordering::Relaxed);
        }
    });
    check!(
        bad_range.load(Ordering::Relaxed) == 0,
        "parallel::for_each_chunk",
        "{n} tasks: an empty or out-of-range claim"
    );
    let bad = hits.iter().position(|h| h.load(Ordering::Relaxed) != 1);
    check!(
        bad.is_none(),
        "parallel::for_each_chunk",
        "{n} tasks: index {bad:?} not covered exactly once"
    );
    Ok(())
}

fn chunks(src: &mut Source, n: usize) -> Outcome {
    let c = chunk(src, n);
    let mut data = vec![u64::MAX; n];
    let calls = AtomicUsize::new(0);
    parallel::chunks_mut(&mut data, c, |i, sub| {
        calls.fetch_add(1, Ordering::Relaxed);
        for (k, x) in sub.iter_mut().enumerate() {
            *x = ((i as u64) << 32) | k as u64;
        }
    });
    let want: Vec<u64> = (0..n).map(|j| (((j / c) as u64) << 32) | (j % c) as u64).collect();
    check!(data == want, "parallel::chunks_mut", "{n} items in chunks of {c}");
    check!(
        calls.load(Ordering::Relaxed) == n.div_ceil(c),
        "parallel::chunks_mut",
        "{n} items in chunks of {c}: {} calls",
        calls.load(Ordering::Relaxed)
    );
    Ok(())
}

fn zip(src: &mut Source, n: usize) -> Outcome {
    let c = chunk(src, n);
    let input: Vec<u32> = (0..n as u32).map(|x| x.wrapping_mul(2_654_435_761)).collect();
    let mut out = vec![0u64; n];
    parallel::chunks_mut_zip(&mut out, &input, c, |i, dst, from| {
        for (k, (d, s)) in dst.iter_mut().zip(from).enumerate() {
            *d = u64::from(*s) ^ ((i * c + k) as u64) << 32;
        }
    });
    let want: Vec<u64> = input
        .iter()
        .enumerate()
        .map(|(j, &s)| u64::from(s) ^ (j as u64) << 32)
        .collect();
    check!(out == want, "parallel::chunks_mut_zip", "{n} items in chunks of {c}");
    Ok(())
}

fn each_mut_fill(_src: &mut Source, n: usize) -> Outcome {
    let mut data = vec![0usize; n];
    parallel::for_each_mut(&mut data, |i, x| *x = i ^ 0x5555);
    check!(
        data.iter().enumerate().all(|(i, &x)| x == i ^ 0x5555),
        "parallel::for_each_mut",
        "{n} items"
    );
    let mut data = vec![0u64; n];
    parallel::fill(&mut data, |i| (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15));
    check!(
        data.iter()
            .enumerate()
            .all(|(i, &x)| x == (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15)),
        "parallel::fill",
        "{n} items"
    );
    Ok(())
}

fn collect(_src: &mut Source, n: usize) -> Outcome {
    // A heap-owning item: a slot written twice or never would leak or double-free.
    let got = parallel::map_collect(n, |i| vec![i as u32; i % 3]);
    let want: Vec<Vec<u32>> = (0..n).map(|i| vec![i as u32; i % 3]).collect();
    check!(got == want, "parallel::map_collect", "{n} items");
    Ok(())
}

fn first(src: &mut Source, n: usize) -> Outcome {
    let hits: Vec<usize> = match src.below(4) {
        0 => Vec::new(),
        1 => vec![n.saturating_sub(1)],
        2 => vec![0],
        _ => (0..src.range(1, 8)).map(|_| src.below(n.max(1))).collect(),
    };
    let want = hits.iter().copied().filter(|&h| h < n).min();
    let got = parallel::find_first(n, |i| hits.contains(&i));
    check!(
        got == want,
        "parallel::find_first",
        "{n} items, hits {hits:?}: got {got:?}"
    );
    Ok(())
}

fn item(i: usize) -> u64 {
    (i as u64 ^ 0xdead_beef)
        .wrapping_mul(0x9e37_79b9_7f4a_7c15)
        .rotate_left(i as u32 % 64)
}

fn reductions(src: &mut Source, n: usize) -> Outcome {
    let sum = (0..n).fold(0u64, |s, i| s.wrapping_add(item(i)));
    let xor = (0..n).fold(0u64, |s, i| s ^ item(i));
    let max = (0..n).map(item).max().unwrap_or(0);
    let got = parallel::map_reduce(n, || 0u64, item, u64::wrapping_add);
    check!(got == sum, "parallel::map_reduce", "{n} items: sum");
    let got = parallel::map_reduce(n, || (0u64, 0u64), |i| (item(i), 1), |a, b| (a.0 ^ b.0, a.1 + b.1));
    check!(
        got == (xor, n as u64),
        "parallel::map_reduce",
        "{n} items: xor and count {got:?}"
    );
    let got = parallel::fold_reduce(n, || 0u64, |acc, i| *acc = (*acc).max(item(i)), u64::max);
    check!(got == max, "parallel::fold_reduce", "{n} items: max");
    let inits = AtomicUsize::new(0);
    let got = parallel::map_reduce_with_state(
        n,
        || {
            inits.fetch_add(1, Ordering::Relaxed);
            vec![0u8; 16]
        },
        || (0u64, 0u64),
        |scratch, acc, i| {
            scratch[i % 16] = scratch[i % 16].wrapping_add(1);
            acc.0 = acc.0.wrapping_add(item(i));
            acc.1 += 1;
        },
        |a, b| (a.0.wrapping_add(b.0), a.1 + b.1),
    );
    check!(
        got == (sum, n as u64),
        "parallel::map_reduce_with_state",
        "{n} items: {got:?}"
    );
    check!(
        inits.load(Ordering::Relaxed) <= parallel::num_threads(),
        "parallel::map_reduce_with_state",
        "{} states for {} workers",
        inits.load(Ordering::Relaxed),
        parallel::num_threads()
    );
    let _ = src;
    Ok(())
}

fn chunk_reductions(src: &mut Source, n: usize) -> Outcome {
    let (wa, wb) = (chunk(src, n), chunk(src, n / 2 + 1));
    let (na, nb) = (n, n / 2 + src.below(3));
    let mut a = vec![0u64; na];
    let mut b = vec![0u64; nb];
    let tasks = na.div_ceil(wa).max(nb.div_ceil(wb));
    let got = parallel::map_reduce_chunks_mut(
        [&mut a, &mut b],
        [wa, wb],
        || (),
        || 0u64,
        |_, acc, i, [ca, cb]| {
            for (k, x) in ca.iter_mut().enumerate() {
                *x = (i * wa + k) as u64;
            }
            for (k, x) in cb.iter_mut().enumerate() {
                *x = (i * wb + k) as u64 | 1 << 40;
            }
            *acc += 1;
        },
        |x, y| x + y,
    );
    check!(
        got == tasks as u64,
        "parallel::map_reduce_chunks_mut",
        "{got} tasks, want {tasks}"
    );
    check!(
        a.iter().enumerate().all(|(j, &x)| x == j as u64),
        "parallel::map_reduce_chunks_mut",
        "first buffer, {na} in chunks of {wa}"
    );
    check!(
        b.iter().enumerate().all(|(j, &x)| x == j as u64 | 1 << 40),
        "parallel::map_reduce_chunks_mut",
        "second buffer, {nb} in chunks of {wb}"
    );
    Ok(())
}

fn recommended(_src: &mut Source, n: usize) -> Outcome {
    let c = parallel::recommended_chunk_size(n);
    check!(
        c >= 1 && c <= n.max(1),
        "parallel::recommended_chunk_size",
        "{n} items: {c}"
    );
    check!(parallel::num_threads() >= 1, "parallel::num_threads", "no thread");
    Ok(())
}

/// A task that panics: the dispatch re-raises it on the caller, and the next dispatch runs normally.
fn panics(src: &mut Source, n: usize, ctx: &Ctx) -> Outcome {
    let n = n.max(1);
    let at = src.below(n);
    let ran = AtomicU64::new(0);
    let result = catch(|| {
        parallel::for_each(n, |i| {
            ran.fetch_add(1, Ordering::Relaxed);
            if i == at {
                panic!("fuzz: a task panics on purpose");
            }
        })
    });
    check!(
        result.is_err(),
        "parallel::for_each",
        "a task panicked at {at} of {n} and the dispatch returned normally"
    );
    ctx.note("task panic surfaced");
    each(src, n)
}

/// A dispatch from inside a task panics rather than deadlocking, and the pool stays usable.
fn nested(src: &mut Source, n: usize, ctx: &Ctx) -> Outcome {
    let n = n.clamp(2, 4096);
    let inner_ran = AtomicUsize::new(0);
    let result = catch(|| {
        parallel::for_each(n, |_| {
            parallel::for_each(2, |_| {
                inner_ran.fetch_add(1, Ordering::Relaxed);
            });
        })
    });
    check!(
        result.is_err(),
        "parallel nested dispatch",
        "a dispatch inside a task of {n} returned normally, running {} inner tasks",
        inner_ran.load(Ordering::Relaxed)
    );
    ctx.note("nested dispatch refused");
    each(src, n)
}
