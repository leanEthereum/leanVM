//! `decode-proof`: `leanvm_core::cpu::Proof::from_bytes` on honest encodings edited field by field and byte by byte,
//! on structurally mutated proofs re-encoded, on synthetic phases, and on garbage.
//!
//! Oracles: decoding never panics; whatever decodes re-encodes to exactly its input (the wire format promises one
//! encoding per proof, so anything that dedupes on bytes depends on it); `to_bytes` never panics on a decoded proof;
//! and a decoded proof that differs from the honest one does not verify for the honest statement.

use super::honest;
use crate::source::{Rng, mutate};
use crate::{Ctx, Finding, Outcome, Source, catch};
use fiat_shamir::merkle::{hash_pair, hash_words, open};
use leanvm_core::cpu::Proof;
use primitives::field::{F64, F128};

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let fixtures = honest();
    let (bytes, origin) = match src.below(10) {
        0..=2 if !fixtures.is_empty() => {
            let h = &fixtures[src.below(fixtures.len())];
            (edit_field(&h.bytes, src, ctx), Some(h))
        }
        3 | 4 if !fixtures.is_empty() => {
            let h = &fixtures[src.below(fixtures.len())];
            let mut rng = Rng::new(src.u64());
            let other = &fixtures[src.below(fixtures.len())].bytes;
            ctx.note("havoc");
            (mutate(&h.bytes, &mut rng, Some(other)), Some(h))
        }
        5 if !fixtures.is_empty() => {
            let h = &fixtures[src.below(fixtures.len())];
            let other = &fixtures[src.below(fixtures.len())].proof;
            let mut proof = h.proof.clone();
            let what = crate::mutate_proof::mutate(&mut proof, src, Some(other));
            ctx.note(format!("structured {}", what.split('/').next().unwrap_or(what)));
            match catch(|| proof.to_bytes()) {
                Ok(bytes) => (bytes, Some(h)),
                // The encoder asserts the wire bounds: a proof outside them has no encoding to decode.
                Err(_) => return Ok(()),
            }
        }
        6 | 7 => {
            let bytes = synthetic(src);
            let mut rng = Rng::new(src.u64());
            ctx.note("synthetic");
            if src.bool() {
                (mutate(&bytes, &mut rng, None), None)
            } else {
                (edit_field(&bytes, src, ctx), None)
            }
        }
        _ => (garbage(src, ctx), None),
    };
    check(
        &bytes,
        origin.map(|h| (h.name, &h.program, &h.public_input, &h.proof)),
        ctx,
    )
}

pub fn check(
    bytes: &[u8],
    origin: Option<(&str, &leanvm_core::cpu::Program, &[F128; 2], &Proof)>,
    ctx: &Ctx,
) -> Outcome {
    let decoded =
        catch(|| Proof::from_bytes(bytes)).map_err(|(m, l)| Finding::panic(&m, &l).in_context("Proof::from_bytes"))?;
    let Some(proof) = decoded else {
        ctx.note("refused");
        return Ok(());
    };
    ctx.note("decoded");
    let again = catch(|| proof.to_bytes())
        .map_err(|(m, l)| Finding::panic(&m, &l).in_context("Proof::to_bytes on a decoded proof"))?;
    if again != bytes {
        let at = again
            .iter()
            .zip(bytes)
            .position(|(a, b)| a != b)
            .unwrap_or(again.len().min(bytes.len()));
        return Err(Finding::high(
            "Proof::from_bytes accepted a non-canonical encoding",
            format!(
                "{} input bytes decode to a proof whose encoding is {} bytes, first difference at byte {at}",
                bytes.len(),
                again.len()
            ),
        ));
    }
    let Some((name, program, pi, honest)) = origin else {
        return Ok(());
    };
    if proof == *honest {
        ctx.note("decoded the honest proof");
        return Ok(());
    }
    let verdict = catch(|| leanvm_core::cpu::verify(program, pi, &proof))
        .map_err(|(m, l)| Finding::panic(&m, &l).in_context("cpu::verify on a decoded proof"))?;
    match verdict {
        Ok(_) => Err(Finding::high(
            "a decoded proof that differs from the honest one verifies",
            format!("program {name}: the encoding changed, the proof changed, and the verifier did not notice"),
        )),
        Err(e) => {
            ctx.note(format!(
                "verify refused {}",
                format!("{e:?}").split('(').next().unwrap_or("")
            ));
            Ok(())
        }
    }
}

/// Where each field of an encoding sits, read as the decoder reads it: `(offset, width, what)`.
fn fields(bytes: &[u8]) -> Vec<(usize, usize, &'static str)> {
    let mut out = Vec::new();
    let u32_at = |at: usize| {
        bytes
            .get(at..at + 4)
            .map(|b| u32::from_le_bytes(b.try_into().unwrap()) as usize)
    };
    let Some(len) = u32_at(0) else { return out };
    out.push((0, 4, "stream length"));
    let mut at = 4;
    for i in 0..len.min(64) {
        out.push((at + 16 * i, 8, "stream word"));
    }
    at += 16 * len;
    let Some(phases) = u32_at(at) else { return out };
    out.push((at, 4, "phase count"));
    at += 4;
    for _ in 0..phases.min(8) {
        let Some(count) = u32_at(at) else { return out };
        out.push((at, 4, "query count"));
        at += 4;
        let mut positions = Vec::new();
        for _ in 0..count.min(256) {
            positions.push(u32_at(at).unwrap_or(0));
            out.push((at, 4, "query position"));
            at += 4;
        }
        let (Some(height), Some(_), Some(row_words)) = (u32_at(at), u32_at(at + 4), u32_at(at + 8)) else {
            return out;
        };
        out.extend([(at, 4, "height"), (at + 4, 4, "leaf words"), (at + 8, 4, "row words")]);
        at += 12;
        positions.sort_unstable();
        positions.dedup();
        for _ in 0..positions.len() {
            for w in 0..row_words.min(64) {
                out.push((at + 8 * w, 8, "leaf word"));
            }
            at += 8 * row_words.min(64);
        }
        // Siblings: as many as the octopus needs, which the positions determine.
        let mut nodes: Vec<usize> = positions.clone();
        for _ in 0..height.min(32) {
            let mut parents = Vec::new();
            for &p in &nodes {
                if !nodes.contains(&(p ^ 1)) {
                    out.push((at, 32, "sibling"));
                    at += 32;
                }
                if parents.last() != Some(&(p >> 1)) {
                    parents.push(p >> 1);
                }
            }
            nodes = parents;
        }
    }
    out
}

/// One field of the encoding set to an edge value, grown or shrunk.
fn edit_field(bytes: &[u8], src: &mut Source, ctx: &Ctx) -> Vec<u8> {
    let fields = fields(bytes);
    let mut out = bytes.to_vec();
    if fields.is_empty() {
        return out;
    }
    let (at, width, what) = fields[src.below(fields.len())];
    if at + width > out.len() {
        return out;
    }
    let old = u64::from_le_bytes({
        let mut w = [0u8; 8];
        w[..width.min(8)].copy_from_slice(&out[at..at + width.min(8)]);
        w
    });
    let edit = src.below(9);
    ctx.note(format!("field {what} edit {edit}"));
    let value = match edit {
        0 => 0,
        1 => old.wrapping_add(1),
        2 => old.wrapping_sub(1),
        3 => u64::MAX,
        4 => 1 << src.below(8 * width.min(8)),
        5 => old ^ 1 << src.below(8 * width.min(8)),
        6 => old.wrapping_mul(2),
        7 => {
            // Drop or duplicate the field's bytes, shifting everything after it.
            if src.bool() {
                out.drain(at..at + width);
            } else {
                let copy = out[at..at + width].to_vec();
                out.splice(at..at, copy);
            }
            return out;
        }
        _ => src.edgy_u64(),
    };
    let le = value.to_le_bytes();
    out[at..at + width.min(8)].copy_from_slice(&le[..width.min(8)]);
    if width == 32 {
        out[at + src.below(32)] ^= 1 << src.below(8);
    }
    out
}

/// A well-formed encoding of a random proof: a stream and phases opened from random trees, some leaves sharing
/// leading zeros, some queries repeated.
fn synthetic(src: &mut Source) -> Vec<u8> {
    let stream: Vec<F128> = (0..src.below(20)).map(|_| src.f128()).collect();
    let phases = (0..src.range(0, 3))
        .map(|_| {
            let height = src.range(0, 6);
            let n = 1usize << height;
            let leaf_words = src.range(0, 8);
            let row_words = src.range(0, leaf_words);
            let zeros = src.below(row_words + 1);
            let rows: Vec<Vec<F64>> = (0..n)
                .map(|_| {
                    let mut row: Vec<F64> = src.bulk_u64(row_words).into_iter().map(F64).collect();
                    row.iter_mut().take(zeros).for_each(|w| *w = F64::ZERO);
                    row
                })
                .collect();
            let images: Vec<Vec<F64>> = rows
                .iter()
                .map(|r| [vec![F64::ZERO; leaf_words - row_words], r.clone()].concat())
                .collect();
            let mut levels = vec![images.iter().map(|i| hash_words(i)).collect::<Vec<_>>()];
            while levels.last().unwrap().len() > 1 {
                let up = levels
                    .last()
                    .unwrap()
                    .chunks(2)
                    .map(|p| hash_pair(&p[0], &p[1]))
                    .collect();
                levels.push(up);
            }
            let count = src.range(1, 12);
            let queries: Vec<usize> = (0..count).map(|_| src.below(n)).collect();
            open(n, &queries, leaf_words, |l, i| levels[l][i], |q| &rows[q])
        })
        .collect();
    Proof { stream, merkle: phases }.to_bytes()
}

fn garbage(src: &mut Source, ctx: &Ctx) -> Vec<u8> {
    match src.below(4) {
        0 => {
            ctx.note("garbage random");
            let n = src.below(512);
            src.bulk(n)
        }
        1 => {
            // A header that claims a lot and delivers nothing: the decoder must not allocate for it.
            ctx.note("garbage huge counts");
            let mut out = u32::MAX.to_le_bytes().to_vec();
            let n = src.below(64);
            out.extend(src.bulk(n));
            out
        }
        2 => {
            ctx.note("garbage phases");
            let mut out = 0u32.to_le_bytes().to_vec();
            out.extend((src.range(0, 9) as u32).to_le_bytes());
            for _ in 0..src.range(1, 4) {
                out.extend((src.range(0, 300) as u32).to_le_bytes());
                for _ in 0..src.below(8) {
                    out.extend(src.u32().to_le_bytes());
                }
                out.extend((src.range(0, 40) as u32).to_le_bytes());
                out.extend((src.range(0, 70) as u32).to_le_bytes());
                out.extend((src.range(0, 70) as u32).to_le_bytes());
                let n = src.below(256);
                out.extend(src.bulk(n));
            }
            out
        }
        _ => {
            ctx.note("garbage empty");
            Vec::new()
        }
    }
}
