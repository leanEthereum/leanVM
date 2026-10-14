//! What both sides derive from a circuit alone: each table's height, the tables the proof has, and where every column
//! sits in the stack.

use super::RecError;
use super::circuit::Circuit;
use super::hash;
use super::table::{Heights, Table};
use crate::bus::ColumnClaim;
use crate::commitment::StackClaim;
use crate::constraints::{Air, BitColumns, Claims};
use crate::stacking;
use crate::stacking::{Placement, Source, StackShape, Window};
use std::ops::Range;

/// Each table's height, the owned tables the proof has, and every column's place in the stack.
///
/// The stack holds the hash table's packed witness, then every present owned table's columns in table order.
/// The hash table's first columns are ports of that witness and take no place of their own.
///
/// A table with no height is absent: nothing of it is committed, it has no bus block and no summand, and no claim names
/// it. The heights are the verifier's, from the circuit, so a proof has no rows where the verifier expects none.
#[derive(Clone, Debug)]
pub(crate) struct RecLayout {
    /// Each table's base-two logarithm of rows, the public table's included, none for an absent table.
    pub(crate) taus: Heights,
    /// The owned tables the proof has, in table order: a table's index here is its index on the bus and in the table
    /// sumcheck.
    pub(crate) present: Vec<Table>,
    pub(crate) placements: Vec<Placement>,
    pub(crate) shape: StackShape,
}

impl RecLayout {
    /// The global column of the hash table's packed witness, the one committed column before the owned tables'.
    pub(crate) const HASH_WITNESS: usize = 0;

    /// The most rows a table holds, as a base-two logarithm: a slot's key keeps the row in its low 32 bits.
    pub(crate) const MAX_TAU: usize = 32;

    /// Each owned table's first global column and its number of columns, in table order.
    pub(crate) const TABLE_COLUMNS: [(usize, usize); Table::OWNED.len()] = {
        let mut spans = [(0, 0); Table::OWNED.len()];
        let mut next = Self::HASH_WITNESS + 1;
        let mut t = 0;
        while t < spans.len() {
            spans[t] = (next, Table::OWNED[t].n_cols());
            next += spans[t].1;
            t += 1;
        }
        spans
    };

    /// The layout of a circuit: each table at the least power of two holding its rows, and at least its floor.
    ///
    /// # Errors
    ///
    /// Returns an error if a table has more rows than its keys name, or the witness exceeds one commitment.
    pub(crate) fn new(circuit: &Circuit) -> Result<Self, RecError> {
        Self::from_taus(circuit.heights())
    }

    /// The layout of a circuit of the given heights.
    ///
    /// # Errors
    ///
    /// Returns an error if a table has more rows than its keys name, or the witness exceeds one commitment.
    ///
    /// # Panics
    ///
    /// Panics if the hash table or the public table has no height: every circuit has both.
    pub(crate) fn from_taus(taus: Heights) -> Result<Self, RecError> {
        assert!(
            taus[Table::Hash].is_some() && taus[Table::Pub].is_some(),
            "every proof has the hash and public tables"
        );
        let too_many =
            (taus.iter()).find_map(|(table, &tau)| tau.filter(|&tau| tau > Self::MAX_TAU).map(|tau| (table, tau)));
        if let Some((table, tau)) = too_many {
            return Err(RecError::TooManyRows { table, tau });
        }
        let (placements, shape) = stacking::placements_of(&Self::sources(&taus));
        if shape.mu > crate::commitment::MAX_MU {
            return Err(RecError::TooLong { mu: shape.mu });
        }
        Ok(Self {
            present: Table::OWNED.into_iter().filter(|&t| taus[t].is_some()).collect(),
            taus,
            placements,
            shape,
        })
    }

    /// Every global column's source: the packed witness, then each owned table's ports and committed columns, none of an
    /// absent table's in the stack.
    fn sources(taus: &Heights) -> Vec<Source> {
        let stride_log = hash::CIRCUIT.stride_log();
        let mut sources = vec![Source::Committed(Self::tau_of(taus, Table::Hash) + stride_log)];
        for table in Table::OWNED {
            debug_assert_eq!(sources.len(), Self::columns(table).start);
            sources.extend((0..table.n_cols()).map(|c| match taus[table] {
                None => Source::Absent,
                Some(_) if c < table.n_ports() => Source::Port {
                    column: Self::HASH_WITNESS,
                    port: c,
                    stride_log,
                },
                Some(tau) => Source::Committed(tau),
            }));
        }
        sources
    }

    /// An owned table's global columns.
    pub(crate) const fn columns(table: Table) -> Range<usize> {
        let (base, n) = Self::TABLE_COLUMNS[table as usize];
        base..base + n
    }

    /// A table's base-two logarithm of rows.
    ///
    /// # Panics
    ///
    /// Panics if the proof leaves the table out.
    pub(crate) fn tau(&self, table: Table) -> usize {
        Self::tau_of(&self.taus, table)
    }

    /// A table's base-two logarithm of rows among the heights, which have the table.
    fn tau_of(taus: &Heights, table: Table) -> usize {
        taus[table].unwrap_or_else(|| panic!("the proof leaves {table:?} out"))
    }

    /// Each present owned table's first global column and its number of columns, in table order: the tables the bus
    /// and the table sumcheck see.
    pub(crate) fn spans(&self) -> Vec<(usize, usize)> {
        self.present.iter().map(|&t| Self::TABLE_COLUMNS[t as usize]).collect()
    }

    /// The packed witness's window in the stack.
    pub(crate) fn hash_window(&self) -> Window {
        self.placements[Self::HASH_WITNESS]
            .window()
            .expect("the packed witness is committed")
    }

    /// The constraint batch's airs, one per present owned table, each with its summand in table order.
    pub(crate) fn airs<S>(&self, summands: Vec<S>) -> Vec<Air<S>> {
        (self.present.iter().zip(summands))
            .map(|(&table, summand)| Air {
                tau: self.tau(table),
                n_cols: table.n_cols(),
                n_public: 0,
                bits: BitColumns::default(),
                summand,
            })
            .collect()
    }

    /// Every column claim the opening discharges, the bus's then each present owned table's, located in the stack.
    ///
    /// A port's claim is a strided evaluation of its packed witness.
    pub(crate) fn opening_claims<E: Copy>(&self, bus: Vec<ColumnClaim<E>>, tables: &[Claims<E>]) -> Vec<StackClaim<E>> {
        let mut claims = bus;
        for (&table, claimed) in self.present.iter().zip(tables) {
            let base = Self::columns(table).start;
            claims.extend(claimed.evals.iter().enumerate().map(|(c, &value)| ColumnClaim {
                col: base + c,
                point: claimed.chi.clone(),
                value,
            }));
        }
        (claims.into_iter())
            .filter_map(|c| self.placements[c.col].claim(c.point, c.value))
            .collect()
    }
}
