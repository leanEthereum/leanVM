//! `kernel-merkle`: `pcs::whir::commit` (the lane-major encode, the cut Merkle builder, the shared zero-prefix leaf
//! hashing) against encoding each lane and hashing each leaf image here; openings from `fiat_shamir::merkle::open`
//! authenticated the way `verifier`'s `MerklePath::root` does, and refused once mutated; and the proof wire format
//! round-tripping those openings.

use super::reference as r;
use super::{bulk_k, check};
use crate::{Ctx, Finding, Outcome, Source};
use fiat_shamir::merkle::{MerklePath, hash_pair, hash_words, open};
use fiat_shamir::transcript::Proof;
use pcs::ntt::AdditiveNttF64;
use primitives::field::{F64, F192};

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    if src.chance(1, 2) {
        commit(src, ctx)
    } else {
        openings(src, ctx)
    }
}

/// The leaf digest and the climb of `verifier::merkle::MerklePath::root`, transcribed.
fn verifier_root(path: &MerklePath) -> [u8; 32] {
    let mut node = r::keccak256(&r::words_le(&path.leaf.iter().map(|w| w.0).collect::<Vec<_>>()));
    for (level, sibling) in path.siblings.iter().enumerate() {
        node = if path.leaf_index >> level & 1 == 0 {
            r::hash_pair(&node, sibling)
        } else {
            r::hash_pair(sibling, &node)
        };
    }
    node
}

/// The tree's levels, leaves first.
fn levels(leaves: Vec<[u8; 32]>) -> Vec<Vec<[u8; 32]>> {
    let mut out = vec![leaves];
    while out.last().unwrap().len() > 1 {
        let up = out
            .last()
            .unwrap()
            .chunks(2)
            .map(|p| r::hash_pair(&p[0], &p[1]))
            .collect();
        out.push(up);
    }
    out
}

fn commit(src: &mut Source, ctx: &Ctx) -> Outcome {
    let log_batch = match src.below(4) {
        0 => 6,
        1 => src.range(1, 4),
        2 => src.range(5, 8),
        _ => src.range(9, 11),
    };
    let log_rows = src.range(1, 12usize.saturating_sub(log_batch / 2).max(2));
    let rate = src.range(1, 4);
    let lanes = match src.below(4) {
        0 => 1usize << log_batch,
        1 => 1,
        _ => src.range(1, 1 << log_batch),
    };
    // Keep the codeword below 2^22 words.
    let rate = rate.min(22usize.saturating_sub(log_rows + log_batch).max(1));
    let log_n = log_rows + log_batch;
    ctx.note(format!(
        "commit batch {} lanes {} rate {rate} cut {}",
        log_batch.min(8),
        if lanes == 1 << log_batch {
            "full"
        } else if lanes == 1 {
            "one"
        } else {
            "some"
        },
        log_rows + rate >= 12
    ));
    let message = bulk_k(src, lanes << log_rows);
    let (commitment, _) = pcs::whir::commit(&message, log_n, log_batch, rate);

    // Each lane encoded alone, the leaf image its lanes in reverse, the absent ones leading as zeros.
    let k_code = log_rows + rate;
    let ntt = AdditiveNttF64::standard(k_code);
    let codewords: Vec<Vec<F64>> = message
        .chunks(1 << log_rows)
        .map(|block| {
            let mut cw = vec![F64::ZERO; 1 << k_code];
            cw[..block.len()].copy_from_slice(block);
            ntt.encode_interleaved_in_place(&mut cw, 1, rate);
            cw
        })
        .collect();
    let width = 1usize << log_batch;
    let leaves: Vec<[u8; 32]> = (0..1usize << k_code)
        .map(|q| {
            let image: Vec<u64> = (0..width)
                .map(|j| width - 1 - j)
                .map(|t| codewords.get(t).map_or(0, |cw| cw[q].0))
                .collect();
            r::keccak256(&r::words_le(&image))
        })
        .collect();
    let want = r::merkle_root(leaves);
    check!(
        commitment.root == want,
        "pcs::whir::commit",
        "2^{log_rows} rows, {lanes} of 2^{log_batch} lanes, rate {rate}: root {:02x?}, want {want:02x?}",
        commitment.root
    );
    Ok(())
}

fn openings(src: &mut Source, ctx: &Ctx) -> Outcome {
    let height = src.range(0, 10);
    let n = 1usize << height;
    let leaf_words = src.range(0, 12);
    let row_words = src.range(0, leaf_words);
    let rows: Vec<Vec<F64>> = (0..n)
        .map(|_| {
            let mut row = bulk_k(src, row_words);
            if src.chance(1, 4) {
                row.iter_mut()
                    .take(src.below(row_words + 1))
                    .for_each(|w| *w = F64::ZERO);
            }
            row
        })
        .collect();
    let images: Vec<Vec<F64>> = rows
        .iter()
        .map(|row| [vec![F64::ZERO; leaf_words - row_words], row.clone()].concat())
        .collect();
    let tree = levels(images.iter().map(|img| hash_words(img)).collect());
    let root = tree[height][0];
    // The same leaf digests from the fiat_shamir helpers and from sha3.
    for (q, img) in images.iter().enumerate().take(4) {
        let want = r::keccak256(&r::words_le(&img.iter().map(|w| w.0).collect::<Vec<_>>()));
        check!(tree[0][q] == want, "fiat_shamir::merkle::hash_words", "leaf {q}");
    }
    check!(
        tree.get(1).is_none_or(
            |l| l[0] == hash_pair(&tree[0][0], &tree[0][1]) && l[0] == r::hash_pair(&tree[0][0], &tree[0][1])
        ),
        "fiat_shamir::merkle::hash_pair",
        ""
    );
    let count = src.range(1, 40);
    let queries: Vec<usize> = (0..count).map(|_| src.below(n)).collect();
    ctx.note(format!("open height {} queries {}", height.min(4), count.min(8)));
    let paths = open(n, &queries, leaf_words, |level, i| tree[level][i], |q| &rows[q]);
    for (path, &q) in paths.iter().zip(&queries) {
        check!(path.leaf_index == q as u64, "fiat_shamir::merkle::open", "position {q}");
        check!(path.leaf == images[q], "fiat_shamir::merkle::open", "leaf image at {q}");
        check!(path.siblings.len() == height, "fiat_shamir::merkle::open", "height");
        check!(
            verifier_root(path) == root,
            "fiat_shamir::merkle::open",
            "path {q} does not authenticate"
        );
    }

    // A mutated path reaches another root.
    let mut bad = paths[src.below(paths.len())].clone();
    let what = match src.below(4) {
        0 if !bad.leaf.is_empty() => {
            let i = src.below(bad.leaf.len());
            bad.leaf[i] = F64(bad.leaf[i].0 ^ 1 << src.below(64));
            "leaf"
        }
        1 if height > 0 => {
            let i = src.below(height);
            bad.siblings[i][src.below(32)] ^= 1 << src.below(8);
            "sibling"
        }
        2 if height > 0 => {
            bad.leaf_index ^= 1 << src.below(height);
            "index"
        }
        _ => {
            bad.leaf.push(F64(src.u64()));
            "leaf length"
        }
    };
    if verifier_root(&bad) == root && bad.leaf_index < n as u64 {
        let same_image = images.get(bad.leaf_index as usize) == Some(&bad.leaf);
        if !same_image {
            return Err(Finding::critical(
                format!("kernel-merkle: a mutated {what} still authenticates"),
                format!("height {height}, leaf words {leaf_words}"),
            ));
        }
    }

    // The proof's wire format: one encoding, which decodes back to the same paths.
    if leaf_words <= 64 && count <= 256 {
        let stream: Vec<F192> = (0..src.below(5)).map(|_| src.f192()).collect();
        let proof = Proof {
            stream,
            merkle: vec![paths.clone(); src.range(1, 3)],
        };
        let bytes = proof.to_bytes();
        let back = Proof::from_bytes(&bytes);
        check!(
            back.as_ref() == Some(&proof),
            "Proof wire round trip",
            "height {height}, {leaf_words} leaf words, {row_words} row words, {count} queries"
        );
        ctx.note("wire round trip");
    }
    Ok(())
}
