//! `lean-da`: `BlobMatrix::build` on payloads of every edge size, and what it promises: a size error rather than
//! a panic on a payload that is not whole blobs, the commitment against a plain rebuild, determinism and the
//! linearity of the encoding, `verify_cell` and `root_of_padding_blob`.

use crate::{Ctx, Finding, Outcome, Source, catch};
use lean_da::{
    BLOB_SYMBOLS, CELLS_PER_ROW, CELL_SYMBOLS, CODEWORD_SYMBOLS, DA_MAX_ROWS, Blob, BlobMatrix, Symbol,
    root_of_padding_blob, verify_cell,
};
use lean_da::encode::encode_rows;

fn payload(src: &mut Source, symbols: usize) -> Vec<Symbol> {
    (0..symbols).map(|_| src.u64() as u128).collect()
}

/// A `K`-element XORed over the payload's symbols: any 128-bit word is one.
fn xor_sum(rows: &[Symbol]) -> Symbol {
    rows.iter().fold(0, |acc, s| acc ^ s)
}

pub fn run(src: &mut Source, ctx: &Ctx) -> Outcome {
    let symbols = match src.below(10) {
        0 => 0,
        1 => 1,
        2 => BLOB_SYMBOLS,
        3 => BLOB_SYMBOLS - 1,
        4 => BLOB_SYMBOLS + 1,
        5 => 4 * BLOB_SYMBOLS,
        6 => DA_MAX_ROWS as usize * BLOB_SYMBOLS,
        7 => (DA_MAX_ROWS as usize + 1) * BLOB_SYMBOLS,
        _ => src.below(9 * BLOB_SYMBOLS),
    };
    let valid = symbols.is_multiple_of(BLOB_SYMBOLS) && symbols / BLOB_SYMBOLS <= DA_MAX_ROWS as usize && symbols > 0;
    ctx.note(format!("lean_da {} symbols", symbols));
    let rows = if valid || symbols < (4 << 20) { payload(src, symbols) } else { vec![0; symbols] };
    let blobs: Vec<Blob> = rows
        .chunks(BLOB_SYMBOLS)
        .map(|chunk| chunk.try_into().unwrap_or([0; BLOB_SYMBOLS]))
        .collect();
    let result = catch(|| BlobMatrix::build(&blobs))
        .map_err(|(m, l)| Finding::panic(&m, &l).in_context("BlobMatrix::build"))?;
    let matrix = match (result, valid) {
        (Err(e), false) => {
            if e.blobs != symbols.div_ceil(BLOB_SYMBOLS) {
                return Err(Finding::medium(
                    "BlobMatrix::build reports the wrong blob count",
                    format!("{e} for {symbols} symbols"),
                ));
            }
            return Ok(());
        }
        (Err(e), true) => {
            return Err(Finding::high("BlobMatrix::build refused a valid payload", format!("{e}")));
        }
        (Ok(_), false) => {
            return Err(Finding::high(
                "BlobMatrix::build accepted a payload that is not whole blobs",
                format!("{symbols} symbols"),
            ));
        }
        (Ok(matrix), true) => matrix,
    };
    // The codewords: the first `BLOB_SYMBOLS` symbols are the blob (systematic), every row a codeword.
    for blob_idx in 0..matrix.n_blobs() {
        let Some(row) = matrix.row(blob_idx) else {
            return Err(Finding::high("BlobMatrix::row misses a blob", format!("blob {blob_idx}")));
        };
        if row.len() != CODEWORD_SYMBOLS {
            return Err(Finding::high("lean_da codewords have the wrong length", format!("blob {blob_idx}")));
        }
        if row[..BLOB_SYMBOLS] != blobs[blob_idx] {
            return Err(Finding::high(
                "lean_da encoding is not systematic",
                format!("blob {blob_idx}"),
            ));
        }
    }
    // The root against a plain rebuild: each blob's flat tree over its cells' digests, the top tree over the
    // blob roots padded with the zero codeword's.
    let zero_cell = lean_da_hash(&[0u8; 16 * CELL_SYMBOLS]);
    let padding_root = merkle_root(&vec![zero_cell; CELLS_PER_ROW]);
    if root_of_padding_blob() != padding_root {
        return Err(Finding::high("lean_da::root_of_padding_blob disagrees with its reference", ""));
    }
    let blob_roots: Vec<_> = (0..matrix.n_blobs())
        .map(|i| {
            let cells: Vec<_> = (0..CELLS_PER_ROW)
                .map(|j| {
                    let cell = matrix.cell(i, j).expect("a cell below CELLS_PER_ROW");
                    lean_da_hash(&cell.iter().flat_map(|s| s.to_le_bytes()).collect::<Vec<u8>>())
                })
                .collect();
            merkle_root(&cells)
        })
        .collect();
    if matrix.n_blobs() > 0 {
        let expected = merkle_root_padded(&blob_roots, DA_MAX_ROWS as usize);
        if matrix.top_root() != expected {
            return Err(Finding::high(
                "lean_da commitment disagrees with a plain rebuild",
                format!("{} blobs", matrix.n_blobs()),
            ));
        }
    }
    // Every cell verifies against the root, at its own place; a flipped symbol or a wrong place does not.
    if src.chance(2, 3) {
        let root = matrix.top_root();
        for (blob_idx, col_idx) in [(0usize, 0usize), (0, CELLS_PER_ROW / 2), (matrix.n_blobs() - 1, CELLS_PER_ROW - 1)]
        {
            let cell = matrix.cell(blob_idx, col_idx).expect("an in-range cell").to_owned();
            let path = matrix
                .merkle_path_for_cell(blob_idx, col_idx)
                .expect("a path for an in-range cell");
            if !verify_cell(&root, blob_idx, col_idx, &cell, &path) {
                return Err(Finding::high(
                    "lean_da::verify_cell refuses an honest cell",
                    format!("blob {blob_idx}, column {col_idx}"),
                ));
            }
            let mut flipped = cell;
            flipped[0] ^= 1;
            if verify_cell(&root, blob_idx, col_idx, &flipped, &path) {
                return Err(Finding::high(
                    "lean_da::verify_cell accepts a flipped symbol",
                    format!("blob {blob_idx}, column {col_idx}"),
                ));
            }
        }
    }
    // Deterministic, and linear: a second payload's codewords XOR to the codewords of the XOR.
    if src.chance(1, 4) {
        let other_rows = payload(src, symbols);
        let other_blobs: Vec<Blob> = other_rows
            .chunks(BLOB_SYMBOLS)
            .map(|chunk| chunk.try_into().unwrap_or([0; BLOB_SYMBOLS]))
            .collect();
        let sum: Vec<Symbol> = rows.iter().zip(&other_rows).map(|(a, b)| a ^ b).collect();
        let sum_blobs: Vec<Blob> =
            sum.chunks(BLOB_SYMBOLS).map(|chunk| chunk.try_into().unwrap_or([0; BLOB_SYMBOLS])).collect();
        let (eo, es) = (encode_rows(&other_blobs), encode_rows(&sum_blobs));
        let first = matrix.row(0).expect("a blob").to_owned();
        let (eo, es) = (eo.chunks(CODEWORD_SYMBOLS), es.chunks(CODEWORD_SYMBOLS));
        let (eo, es) = (eo.collect::<Vec<_>>(), es.collect::<Vec<_>>());
        if first.chunks(CODEWORD_SYMBOLS).zip(&eo).zip(&es).any(|((a, b), c)| {
            a.iter().zip(b.iter()).zip(c.iter()).any(|((x1, y1), z)| *x1 ^ *y1 != *z)
        }) {
            return Err(Finding::high("lean_da::encode_rows is not linear", ""));
        }
        let again = catch(|| BlobMatrix::build(&blobs))
            .map_err(|(m, l)| Finding::panic(&m, &l).in_context("BlobMatrix::build"))?;
        if again.map(|m| m.top_root()) != Ok(matrix.top_root()) {
            return Err(Finding::high("BlobMatrix::build is not deterministic", ""));
        }
    }
    // The payload's XOR survives: the systematic encoding keeps the blob symbols.
    let left: Vec<_> = rows[..BLOB_SYMBOLS.min(rows.len())].to_vec();
    let from_row = matrix.row(0).map(|row| xor_sum(&row[..BLOB_SYMBOLS.min(row.len())]));
    if from_row != Some(xor_sum(&left)) && !left.is_empty() {
        return Err(Finding::high("lean_da row does not hold the payload's symbols", ""));
    }
    Ok(())
}

/// Keccak-256 of bytes, as the `[u8; 32]` the trees hash.
fn lean_da_hash(bytes: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    out.copy_from_slice(&keccak256::hash(bytes));
    out
}

/// A flat binary Merkle root over `leaves`.
fn merkle_root(leaves: &[[u8; 32]]) -> [u8; 32] {
    let mut level: Vec<[u8; 32]> = leaves.to_vec();
    if level.is_empty() {
        return [0; 32];
    }
    while level.len() > 1 {
        level = level
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| {
                let mut pair_bytes = [0u8; 64];
                pair_bytes[..32].copy_from_slice(&pair[0]);
                pair_bytes[32..].copy_from_slice(&pair[1]);
                lean_da_hash(&pair_bytes)
            })
            .collect();
    }
    level[0]
}

/// A Merkle root over `leaves` padded with zeros to `n`.
fn merkle_root_padded(leaves: &[[u8; 32]], n: usize) -> [u8; 32] {
    let mut padded = leaves.to_vec();
    padded.resize(n, [0; 32]);
    merkle_root(&padded)
}