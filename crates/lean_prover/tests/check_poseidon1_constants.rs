//! Ensure the Poseidon1 (width-16) constants hardcoded in
//! `crates/lean_prover/verifier.py` match the Rust constants used by the AIR.
//! The test prints the expected line (so you can paste it back if anything
//! drifts) and asserts that `verifier.py` contains that exact string up to
//! whitespace.
//!
//! Run:
//!     cargo test -p lean_prover --test check_poseidon1_constants -- --nocapture

use std::fmt::Write as _;
use std::fs;
use std::path::PathBuf;

use backend::{
    KoalaBear, POSEIDON1_HALF_FULL_ROUNDS, POSEIDON1_PARTIAL_ROUNDS, PrimeCharacteristicRing, PrimeField32,
    mds_circ_16, poseidon1_final_constants, poseidon1_initial_constants, poseidon1_sparse_first_round_constants,
    poseidon1_sparse_first_row, poseidon1_sparse_m_i, poseidon1_sparse_scalar_round_constants, poseidon1_sparse_v,
};

fn k(x: KoalaBear) -> u32 {
    x.as_canonical_u32()
}

/// Reconstruct the dense MDS matrix the way `mds_dense_16` does in
/// `lean_vm::tables::poseidon_16::mod.rs` — run `mds_circ_16` on each standard
/// basis vector and stack the columns into a row-major matrix.
fn dense_mds_matrix() -> [[KoalaBear; 16]; 16] {
    let mut cols = [[KoalaBear::ZERO; 16]; 16];
    for j in 0..16 {
        let mut e = [KoalaBear::ZERO; 16];
        e[j] = KoalaBear::ONE;
        mds_circ_16::<KoalaBear>(&mut e);
        cols[j] = e;
    }
    let mut rows = [[KoalaBear::ZERO; 16]; 16];
    for i in 0..16 {
        for j in 0..16 {
            rows[i][j] = cols[j][i];
        }
    }
    rows
}

fn fmt_vec(v: &[KoalaBear]) -> String {
    let mut s = String::from("(");
    for (i, &x) in v.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        write!(s, "{}", k(x)).unwrap();
    }
    s.push(')');
    s
}

fn fmt_mat<R: AsRef<[KoalaBear]>>(rows: &[R]) -> String {
    let mut s = String::from("(");
    for (i, row) in rows.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        s.push_str(&fmt_vec(row.as_ref()));
    }
    s.push(')');
    s
}

fn expected_poseidon1_constants_line() -> String {
    let initial = poseidon1_initial_constants();
    let final_ = poseidon1_final_constants();
    let m_i = poseidon1_sparse_m_i();
    let first_row = poseidon1_sparse_first_row();
    let sparse_v = poseidon1_sparse_v();
    let first_rc = poseidon1_sparse_first_round_constants();
    let scalar_rc = poseidon1_sparse_scalar_round_constants();
    let mds = dense_mds_matrix();

    let initial: Vec<Vec<KoalaBear>> = initial.iter().map(|r| r.to_vec()).collect();
    let final_: Vec<Vec<KoalaBear>> = final_.iter().map(|r| r.to_vec()).collect();
    let m_i: Vec<Vec<KoalaBear>> = m_i.iter().map(|r| r.to_vec()).collect();
    let first_row: Vec<Vec<KoalaBear>> = first_row.iter().map(|r| r.to_vec()).collect();
    let sparse_v: Vec<Vec<KoalaBear>> = sparse_v.iter().map(|r| r.to_vec()).collect();
    let mds: Vec<Vec<KoalaBear>> = mds.iter().map(|r| r.to_vec()).collect();

    format!(
        "POSEIDON1_CONSTANTS = {{\
'half_full_rounds':{hf},\
'partial_rounds':{pr},\
'initial_constants':{ic},\
'final_constants':{fc},\
'sparse_m_i':{smi},\
'sparse_first_row':{sfr},\
'sparse_v':{sv},\
'sparse_first_round_constants':{sfrc},\
'sparse_scalar_round_constants':{ssrc},\
'mds_dense':{mds}\
}}",
        hf = POSEIDON1_HALF_FULL_ROUNDS,
        pr = POSEIDON1_PARTIAL_ROUNDS,
        ic = fmt_mat(&initial),
        fc = fmt_mat(&final_),
        smi = fmt_mat(&m_i),
        sfr = fmt_mat(&first_row),
        sv = fmt_mat(&sparse_v),
        sfrc = fmt_vec(first_rc),
        ssrc = fmt_vec(scalar_rc),
        mds = fmt_mat(&mds),
    )
}

fn strip_ws(s: &str) -> String {
    s.chars().filter(|c| !c.is_whitespace()).collect()
}

#[test]
fn check_poseidon1_constants() {
    let expected = expected_poseidon1_constants_line();
    println!("{expected}");

    let verifier_py = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("verifier.py");
    let src =
        fs::read_to_string(&verifier_py).unwrap_or_else(|e| panic!("failed to read {}: {e}", verifier_py.display()));

    assert!(
        strip_ws(&src).contains(&strip_ws(&expected)),
        "POSEIDON1_CONSTANTS in {} is out of sync with Rust. Replace the line with the one printed above.",
        verifier_py.display(),
    );
}
