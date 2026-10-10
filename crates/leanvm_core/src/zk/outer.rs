//! The outer constraint system: what the recording verifier recorded, over the key stack's slots.
//!
//! Column 0 is the constant one and column `1 + s` the key stack's slot `s`. A key is its slot; an auxiliary variable is the scalar the prover sent for it plus its own key, so every column is a slot and the assignment is the key stack.
//!
//! Its rows, in order:
//!
//! ```text
//!     one per auxiliary variable, by digest    a·b = v  (a product),  a·v = 1  (an inverse),  (a + v)·1 = 0  (a bound value)
//!     one per linear constraint, by digest     l·1 = 0
//!     one per bit, by digest                   b·b = b
//!     the two dummies
//! ```

use super::keys::{DUMMY_SLOT, KEY_SLOT, N_SLOTS};
use super::r1cs::{R1cs, Row as SparseRow};
use super::sym::{Form, Kind, Record, Var};
use primitives::field::F192;

/// The constraint system the record states, the auxiliary variable of rank `r` (by digest) being the form `sent[r]`: the scalar sent for it plus its key.
pub(crate) fn constraint_system(record: &Record, sent: &[Form]) -> R1cs {
    let order = record.aux_order();
    assert_eq!(sent.len(), order.len(), "a sent scalar per auxiliary variable");
    let mut rank = vec![0u32; order.len()];
    for (r, &j) in order.iter().enumerate() {
        rank[j as usize] = u32::try_from(r).expect("fewer than 2^32 variables");
    }
    let row = |f: &Form| sparse(f, &rank, sent);
    let constant = |c: F192| vec![(0, c)];
    let mut r1cs = R1cs {
        n_cols: 1 + N_SLOTS,
        ..R1cs::default()
    };
    for &j in &order {
        let aux = &record.aux[j as usize];
        let v = Form {
            constant: F192::ZERO,
            terms: vec![(Var::Aux(j), F192::ONE)],
        };
        let (a, b, c) = match aux.kind {
            Kind::Product => (row(&aux.a), row(&aux.b), row(&v)),
            Kind::Inverse => (row(&aux.a), row(&v), constant(F192::ONE)),
            Kind::Bind => {
                let mut terms = aux.a.terms.clone();
                terms.push((Var::Aux(j), F192::ONE));
                let sum = Form {
                    constant: aux.a.constant,
                    terms,
                };
                (row(&sum), constant(F192::ONE), Vec::new())
            }
        };
        r1cs.a.push(a);
        r1cs.b.push(b);
        r1cs.c.push(c);
    }
    let mut linear: Vec<&([u8; 32], Form)> = record.linear.iter().collect();
    linear.sort_unstable_by_key(|(d, _)| *d);
    for (_, l) in linear {
        r1cs.a.push(row(l));
        r1cs.b.push(constant(F192::ONE));
        r1cs.c.push(Vec::new());
    }
    let mut booleans: Vec<&([u8; 32], Form)> = record.booleans.iter().collect();
    booleans.sort_unstable_by_key(|(d, _)| *d);
    for (_, b) in booleans {
        let b = row(b);
        r1cs.a.push(b.clone());
        r1cs.b.push(b.clone());
        r1cs.c.push(b);
    }
    r1cs.push_dummies(1 + DUMMY_SLOT);
    r1cs
}

/// The column of a key.
fn key_column(i: u32) -> u32 {
    u32::try_from(1 + KEY_SLOT).expect("a column fits a u32") + i
}

/// A form as a sparse row, its auxiliary variables expanded to what was sent for them, its columns in order and merged.
fn sparse(form: &Form, rank: &[u32], sent: &[Form]) -> SparseRow {
    let mut out: Vec<(u32, F192)> = vec![(0, form.constant)];
    for &(v, coefficient) in &form.terms {
        match v {
            Var::Key(i) => out.push((key_column(i), coefficient)),
            Var::Aux(j) => {
                let a = &sent[rank[j as usize] as usize];
                out.push((0, coefficient * a.constant));
                for &(w, c) in &a.terms {
                    let Var::Key(i) = w else {
                        unreachable!("an auxiliary variable is a sent scalar plus its key")
                    };
                    out.push((key_column(i), coefficient * c));
                }
            }
        }
    }
    out.sort_unstable_by_key(|&(col, _)| col);
    let mut merged: SparseRow = Vec::with_capacity(out.len());
    for (col, c) in out {
        match merged.last_mut() {
            Some((last, acc)) if *last == col => *acc += c,
            _ => merged.push((col, c)),
        }
    }
    merged.retain(|&(_, c)| c != F192::ZERO);
    merged
}
