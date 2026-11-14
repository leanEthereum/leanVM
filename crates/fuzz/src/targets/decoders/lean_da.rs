//! `lean-da`: `lean_da::commit` on payloads of every edge size, and what it promises: a size error rather than a
//! panic, a deterministic root, a systematic code (the payload is the codeword's first half), rows that are codewords
//! (degree below `k` after the inverse NTT, orthogonal to the membership vector the verifier's challenge builds), the
//! tree a plain rebuild with `sha3` gives, and padding rows that are indistinguishable from zero rows.

use crate::targets::kernels::reference as r;
use crate::{Ctx, Finding, Outcome, Source, catch};
use lean_da::{BLOB_SYMBOLS, CELL_SYMBOLS, CELLS_PER_ROW, CODEWORD_SYMBOLS, DA_LOG_K, DA_MAX_ROWS};
use pcs::ntt::AdditiveNttF64;
use primitives::field::{F64, F128};

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    // Mostly a handful of rows; the full 1024 only at depth 2, being seconds of encoding.
    let max_rows = if ctx.depth >= 2 { DA_MAX_ROWS } else { 8 };
    let symbols = match src.below(12) {
        0 => 0,
        1 => BLOB_SYMBOLS - 1,
        2 => BLOB_SYMBOLS + 1,
        3 => BLOB_SYMBOLS * src.range(1, 3) + src.range(1, BLOB_SYMBOLS - 1),
        4 => (DA_MAX_ROWS + 1) * BLOB_SYMBOLS,
        5 => src.below(64),
        6 if ctx.depth >= 2 => DA_MAX_ROWS * BLOB_SYMBOLS,
        _ => BLOB_SYMBOLS * src.range(1, max_rows.min(5)),
    };
    let valid = symbols.is_multiple_of(BLOB_SYMBOLS) && (1..=DA_MAX_ROWS).contains(&(symbols / BLOB_SYMBOLS));
    ctx.note(format!(
        "rows {}",
        if valid {
            (symbols / BLOB_SYMBOLS).min(5).to_string()
        } else {
            "invalid".into()
        }
    ));
    let rows: Vec<u64> = if valid || symbols < (4 << 20) {
        payload(src, symbols)
    } else {
        // Too many rows by one: zeros, which the allocator hands over without touching.
        vec![0; symbols]
    };
    let result =
        catch(|| lean_da::commit(&rows)).map_err(|(m, l)| Finding::panic(&m, &l).in_context("lean_da::commit"))?;
    let (root, witness) = match (result, valid) {
        (Err(e), false) => {
            if e.symbols != symbols {
                return Err(Finding::medium(
                    "lean_da::commit reports the wrong size",
                    format!("{e} for {symbols}"),
                ));
            }
            return Ok(());
        }
        (Err(e), true) => return Err(Finding::high("lean_da::commit refused a valid payload", format!("{e}"))),
        (Ok(_), false) => {
            return Err(Finding::high(
                "lean_da::commit accepted a payload that is not whole blobs",
                format!("{symbols} symbols"),
            ));
        }
        (Ok(ok), true) => ok,
    };
    let n_rows = symbols / BLOB_SYMBOLS;
    let codewords = &witness.codewords;
    if codewords.len() != n_rows * CODEWORD_SYMBOLS {
        return Err(Finding::high(
            "lean_da::commit codewords have the wrong length",
            format!("{}", codewords.len()),
        ));
    }
    // Systematic, and a codeword: the inverse NTT leaves no coefficient at or above k.
    let ntt = AdditiveNttF64::standard(DA_LOG_K + 1);
    for (i, cw) in codewords.chunks(CODEWORD_SYMBOLS).enumerate() {
        if cw[..BLOB_SYMBOLS] != rows[i * BLOB_SYMBOLS..(i + 1) * BLOB_SYMBOLS] {
            return Err(Finding::high("lean_da encoding is not systematic", format!("row {i}")));
        }
        if i < 2 {
            let mut c: Vec<F64> = cw.iter().map(|&w| F64(w)).collect();
            ntt.inverse_transform(&mut c);
            if c[BLOB_SYMBOLS..].iter().any(|w| w.0 != 0) {
                return Err(Finding::high(
                    "lean_da encoding is not a Reed-Solomon codeword",
                    format!("row {i}"),
                ));
            }
        }
    }
    // The tree, rebuilt: each blob's root over its cells' digests, the commitment over the blob roots padded with
    // the zero codeword's.
    let padded = n_rows.next_power_of_two();
    let zero_cell = r::keccak256(&vec![0u8; 8 * CELL_SYMBOLS]);
    let padding_root = r::merkle_root(vec![zero_cell; CELLS_PER_ROW]);
    if lean_da::padding_root() != padding_root {
        return Err(Finding::high("lean_da::padding_root disagrees with its reference", ""));
    }
    let blob_roots: Vec<[u8; 32]> = (0..padded)
        .map(|i| match codewords.chunks(CODEWORD_SYMBOLS).nth(i) {
            Some(cw) => r::merkle_root(
                cw.chunks(CELL_SYMBOLS)
                    .map(|cell| r::keccak256(&r::words_le(cell)))
                    .collect(),
            ),
            None => padding_root,
        })
        .collect();
    if witness.blob_roots() != blob_roots {
        return Err(Finding::high(
            "lean_da blob roots disagree with a plain rebuild",
            format!("{n_rows} rows"),
        ));
    }
    let i = src.below(padded);
    let tree = witness.blob_tree(i);
    let cells: Vec<[u8; 32]> = match codewords.chunks(CODEWORD_SYMBOLS).nth(i) {
        Some(cw) => cw
            .chunks(CELL_SYMBOLS)
            .map(|cell| r::keccak256(&r::words_le(cell)))
            .collect(),
        None => vec![zero_cell; CELLS_PER_ROW],
    };
    if tree[..CELLS_PER_ROW] != cells[..] || *tree.last().unwrap() != blob_roots[i] {
        return Err(Finding::high(
            "lean_da blob tree disagrees with a plain rebuild",
            format!("blob {i} of {padded}"),
        ));
    }
    if root != r::merkle_root(blob_roots.clone()) {
        return Err(Finding::high(
            "lean_da commitment disagrees with a plain rebuild",
            format!("{n_rows} rows"),
        ));
    }

    // Deterministic, and linear: a second payload's codewords XOR to the codewords of the XOR.
    if src.chance(1, 4) {
        let again = lean_da::commit(&rows).map(|(root, _)| root);
        if again != Ok(root) {
            return Err(Finding::high("lean_da::commit is not deterministic", ""));
        }
        let other = payload(src, symbols);
        let sum: Vec<u64> = rows.iter().zip(&other).map(|(a, b)| a ^ b).collect();
        let (eo, es) = (lean_da::encode_rows(&other), lean_da::encode_rows(&sum));
        if codewords.iter().zip(&eo).zip(&es).any(|((a, b), c)| a ^ b != *c) {
            return Err(Finding::high("lean_da::encode_rows is not linear", ""));
        }
        let (re_root, _) = lean_da::commit_codewords(codewords.clone());
        if re_root != root {
            return Err(Finding::high("lean_da::commit_codewords disagrees with commit", ""));
        }
    }

    // A trailing zero row within the same padded height commits like padding (documented).
    if n_rows < padded && src.chance(1, 4) {
        let mut longer = rows.clone();
        longer.extend(std::iter::repeat_n(0, BLOB_SYMBOLS));
        if lean_da::commit(&longer).map(|(r, _)| r) != Ok(root) {
            return Err(Finding::high(
                "lean_da: a trailing zero row changed the root within its padded height",
                "",
            ));
        }
        ctx.note("zero row as padding");
    }

    membership(src, ctx, &root, codewords)
}

/// Rows of the payload: random, all zero, all ones, or one symbol set.
fn payload(src: &mut Source, symbols: usize) -> Vec<u64> {
    match src.below(6) {
        0 => vec![0; symbols],
        1 => vec![u64::MAX; symbols],
        2 => {
            let mut v = vec![0; symbols];
            if symbols > 0 {
                v[src.below(symbols)] = src.edgy_u64().max(1);
            }
            v
        }
        _ => src.bulk_u64(symbols),
    }
}

/// The membership check the guest runs: `L = prod_j (1 + z^(2^j) Vhat_j)` from `lean_da::subspace_above`, `z` from
/// `verifier::da::membership_challenge`; every committed row is orthogonal to it, and a row with one symbol changed is
/// not.
fn membership(src: &mut Source, ctx: &Ctx, root: &[u8; 32], codewords: &[u64]) -> Outcome {
    if !src.chance(1, 3) {
        return Ok(());
    }
    ctx.note("membership");
    let z = verifier::da::membership_challenge(root);
    let z = F128::new(z.c0, z.c1);
    let vhat = lean_da::subspace_above();
    let mut z_pow = vec![z];
    for j in 1..DA_LOG_K {
        z_pow.push(r::mul_e(z_pow[j - 1], z_pow[j - 1]));
    }
    let dual: Vec<F128> = (0..CODEWORD_SYMBOLS)
        .map(|i| {
            (0..DA_LOG_K).fold(F128::ONE, |acc, j| {
                let at = ((i >> j) & 1) as u64 ^ vhat(j, i >> (j + 1)).0;
                acc * (F128::ONE + z_pow[j].mul_base(F64(at)))
            })
        })
        .collect();
    let residual = |row: &[u64]| {
        row.iter()
            .zip(&dual)
            .fold(F128::ZERO, |s, (&w, &l)| s + l.mul_base(F64(w)))
    };
    let i = src.below(codewords.len() / CODEWORD_SYMBOLS);
    let row = &codewords[i * CODEWORD_SYMBOLS..(i + 1) * CODEWORD_SYMBOLS];
    if !residual(row).is_zero() {
        return Err(Finding::high(
            "a committed LeanDA row fails the membership check",
            format!("row {i}"),
        ));
    }
    let mut bad = row.to_vec();
    let at = src.below(CODEWORD_SYMBOLS);
    bad[at] ^= src.edgy_u64().max(1);
    if residual(&bad).is_zero() {
        return Err(Finding::critical(
            "a LeanDA row with a changed symbol passes the membership check",
            format!("row {i}, symbol {at}"),
        ));
    }
    Ok(())
}
