//! Structured edits of a VM proof: what a malicious prover sends instead of an honest proof, one edit at a time, aimed
//! at each part a verifier reads (the announced sizes, the commitment root, the sumcheck and GKR messages, the WHIR
//! openings, the nonces and the Merkle paths).
//!
//! An edit made after the fact breaks Fiat-Shamir from that point on, so it mostly tests that the verifier reads
//! everything and that it fails cleanly. `soundness::transcript_tamper` forges messages the prover then stays
//! consistent with, which is the stronger attack.

use crate::Source;
use fiat_shamir::merkle::MerklePath;
use leanvm_core::cpu::Proof;
use primitives::field::{F64, F128};

/// The scalars every execution proof starts with: `log_memory`, six table row counts, `log_inv_rate`.
pub const ANNOUNCED: usize = 8;

/// One edit of `proof`, its name returned for the case's notes. `other` is another honest proof to splice from.
pub fn mutate(proof: &mut Proof, src: &mut Source, other: Option<&Proof>) -> &'static str {
    let in_stream = proof.merkle.is_empty() || src.chance(2, 3);
    if in_stream {
        mutate_stream(proof, src, other)
    } else {
        mutate_merkle(proof, src, other)
    }
}

/// A position in the stream, biased toward its landmarks: the announcement, the root, the start and the end.
pub fn stream_position(len: usize, src: &mut Source) -> usize {
    if len == 0 {
        return 0;
    }
    match src.below(6) {
        0 => src.below(ANNOUNCED.min(len)),
        1 => (ANNOUNCED + src.below(2)).min(len - 1),
        2 => len - 1 - src.below(len.min(32)),
        _ => src.below(len),
    }
}

/// Replace `x` by a value close to it or on an edge.
pub fn perturb(x: F128, src: &mut Source) -> F128 {
    match src.below(9) {
        0 => {
            let limb = src.below(3);
            let bit = 1u64 << src.below(64);
            let mut limbs = x.to_limbs();
            limbs[limb] ^= bit;
            F128::new(limbs[0], limbs[1])
        }
        1 => x + F128::ONE,
        2 => F128::ZERO,
        3 => F128::ONE,
        4 => x * F128::new(2, 0),
        5 => F128::new(x.c0, x.c1 ^ src.edgy_u64().max(1)),
        6 => src.f128(),
        7 => F128::new(x.c0.wrapping_add(1), x.c1),
        _ => F128::new(src.edgy_u64(), 0),
    }
}

fn mutate_stream(proof: &mut Proof, src: &mut Source, other: Option<&Proof>) -> &'static str {
    let len = proof.stream.len();
    if len == 0 {
        proof.stream.push(src.f128());
        return "stream/fill-empty";
    }
    let i = stream_position(len, src);
    match src.below(12) {
        0..=3 => {
            proof.stream[i] = perturb(proof.stream[i], src);
            if i < ANNOUNCED {
                "stream/perturb-announced"
            } else {
                "stream/perturb"
            }
        }
        4 => {
            // An announced size on an edge: zero, huge, a high limb, one past a cap.
            let j = src.below(ANNOUNCED.min(len));
            let v = match src.below(5) {
                0 => 0,
                1 => u64::MAX,
                2 => 1 << src.below(64),
                3 => src.below(70) as u64,
                _ => (1u64 << src.below(40)) + 1,
            };
            proof.stream[j] = F128::new(v, if src.chance(1, 4) { 1 } else { 0 });
            "stream/announced-edge"
        }
        5 => {
            let j = src.below(len);
            proof.stream.swap(i, j);
            "stream/swap"
        }
        6 => {
            proof.stream.insert(i, src.f128());
            "stream/insert"
        }
        7 => {
            proof.stream.remove(i);
            "stream/delete"
        }
        8 => {
            proof.stream.truncate(i);
            "stream/truncate"
        }
        9 => {
            for _ in 0..src.range(1, 64) {
                proof.stream.push(src.f128());
            }
            "stream/append"
        }
        10 => match other.filter(|o| !o.stream.is_empty()) {
            Some(other) => {
                let j = src.below(other.stream.len());
                let n = src.range(1, 64).min(other.stream.len() - j).min(len - i);
                proof.stream[i..i + n].copy_from_slice(&other.stream[j..j + n]);
                "stream/splice-other"
            }
            None => {
                proof.stream[i] += F128::new(2, 0);
                "stream/perturb"
            }
        },
        _ => {
            // A run of consecutive scalars, as a forged round polynomial would be.
            let n = src.range(2, 8).min(len - i);
            for x in &mut proof.stream[i..i + n] {
                *x = perturb(*x, src);
            }
            "stream/perturb-run"
        }
    }
}

fn path_mut<'a>(proof: &'a mut Proof, src: &mut Source) -> Option<&'a mut MerklePath> {
    let phases: Vec<usize> = (0..proof.merkle.len())
        .filter(|&p| !proof.merkle[p].is_empty())
        .collect();
    let &phase = phases.get(src.below(phases.len().max(1)))?;
    let paths = &mut proof.merkle[phase];
    let i = src.below(paths.len());
    Some(&mut paths[i])
}

fn mutate_merkle(proof: &mut Proof, src: &mut Source, other: Option<&Proof>) -> &'static str {
    match src.below(14) {
        0 => {
            let Some(path) = path_mut(proof, src) else {
                return "merkle/none";
            };
            path.leaf_index = match src.below(4) {
                0 => path.leaf_index ^ 1,
                1 => path.leaf_index.wrapping_add(1),
                2 => src.edgy_u64(),
                _ => path.leaf_index ^ (1 << src.below(32)),
            };
            "merkle/leaf-index"
        }
        1 | 2 => {
            let Some(path) = path_mut(proof, src) else {
                return "merkle/none";
            };
            if path.leaf.is_empty() {
                path.leaf.push(src.f64());
                return "merkle/leaf-grow";
            }
            let i = src.below(path.leaf.len());
            path.leaf[i] = F64(path.leaf[i].0 ^ (1 << src.below(64)));
            "merkle/leaf-word"
        }
        3 => {
            let Some(path) = path_mut(proof, src) else {
                return "merkle/none";
            };
            if src.bool() {
                path.leaf.push(src.f64());
                "merkle/leaf-grow"
            } else {
                path.leaf.pop();
                "merkle/leaf-shrink"
            }
        }
        4 | 5 => {
            let Some(path) = path_mut(proof, src) else {
                return "merkle/none";
            };
            if path.siblings.is_empty() {
                path.siblings.push(src.array());
                return "merkle/sibling-grow";
            }
            let i = src.below(path.siblings.len());
            path.siblings[i][src.below(32)] ^= 1 << src.below(8);
            "merkle/sibling-byte"
        }
        6 => {
            let Some(path) = path_mut(proof, src) else {
                return "merkle/none";
            };
            match src.below(3) {
                0 => {
                    path.siblings.pop();
                    "merkle/sibling-drop"
                }
                1 => {
                    path.siblings.push(src.array());
                    "merkle/sibling-grow"
                }
                _ if path.siblings.len() > 1 => {
                    let n = path.siblings.len();
                    path.siblings.swap(src.below(n), src.below(n));
                    "merkle/sibling-swap"
                }
                _ => "merkle/none",
            }
        }
        7 => {
            let Some(phase) = proof.merkle.iter_mut().filter(|p| p.len() > 1).nth(src.below(4)) else {
                return "merkle/none";
            };
            let n = phase.len();
            phase.swap(src.below(n), src.below(n));
            "merkle/path-swap"
        }
        8 => {
            let Some(phase) = proof.merkle.iter_mut().find(|p| !p.is_empty()) else {
                return "merkle/none";
            };
            let i = src.below(phase.len());
            if src.bool() {
                let path = phase[i].clone();
                phase.insert(i, path);
                "merkle/path-duplicate"
            } else {
                phase.remove(i);
                "merkle/path-remove"
            }
        }
        9 => {
            let i = src.below(proof.merkle.len() + 1);
            match src.below(3) {
                0 if !proof.merkle.is_empty() => {
                    proof.merkle.remove(i.min(proof.merkle.len() - 1));
                    "merkle/phase-remove"
                }
                1 => {
                    proof.merkle.insert(i, Vec::new());
                    "merkle/phase-empty"
                }
                _ if proof.merkle.len() > 1 => {
                    let n = proof.merkle.len();
                    proof.merkle.swap(src.below(n), src.below(n));
                    "merkle/phase-swap"
                }
                _ => "merkle/none",
            }
        }
        10 => {
            // One path at another's position: the leaf a verifier did not ask for, authenticated.
            let Some(phase) = proof.merkle.iter_mut().find(|p| p.len() > 1) else {
                return "merkle/none";
            };
            let n = phase.len();
            let (a, b) = (src.below(n), src.below(n));
            phase[a] = phase[b].clone();
            "merkle/path-copy"
        }
        11 => match other {
            Some(other) if !other.merkle.is_empty() => {
                let p = src.below(other.merkle.len().min(proof.merkle.len()).max(1));
                if let (Some(dst), Some(from)) = (proof.merkle.get_mut(p), other.merkle.get(p))
                    && !dst.is_empty()
                    && !from.is_empty()
                {
                    let i = src.below(dst.len());
                    dst[i] = from[src.below(from.len())].clone();
                    "merkle/splice-other"
                } else {
                    "merkle/none"
                }
            }
            _ => "merkle/none",
        },
        12 => {
            // The zero leaf the pruned encoding drops: a verifier that trusted the width would read it.
            let Some(path) = path_mut(proof, src) else {
                return "merkle/none";
            };
            path.leaf.iter_mut().for_each(|w| *w = F64(0));
            "merkle/leaf-zero"
        }
        _ => {
            let Some(path) = path_mut(proof, src) else {
                return "merkle/none";
            };
            path.siblings.iter_mut().for_each(|s| *s = [0; 32]);
            "merkle/siblings-zero"
        }
    }
}
