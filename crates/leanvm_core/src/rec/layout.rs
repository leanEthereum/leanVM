//! What both sides derive from a circuit alone: each table's height and where every column sits in the stack.

use super::RecError;
use super::circuit::Circuit;
use super::table::{HashFlock, Table};
use crate::constraints::{Air, Claims};
use crate::leaf::ColumnClaim;
use crate::pcs::StackClaim;
use crate::witness::{Placement, Source, StackShape, Window};
use crate::{pcs, witness};
use std::ops::Range;

/// Each table's height and every column's place in the stack.
///
/// The stack holds the hash table's packed witness, then every owned table's columns in table order.
/// The hash table's first columns are ports of that witness and take no place of their own.
#[derive(Clone, Debug)]
pub(crate) struct RecLayout {
    /// Each table's base-two logarithm of rows, the public table's included.
    pub(crate) taus: [usize; Table::COUNT],
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
    pub(crate) fn from_taus(taus: [usize; Table::COUNT]) -> Result<Self, RecError> {
        if let Some(table) = Table::ALL.into_iter().find(|&t| taus[t as usize] > Self::MAX_TAU) {
            return Err(RecError::TooManyRows {
                table,
                tau: taus[table as usize],
            });
        }
        let (placements, shape) = witness::placements_of(&Self::sources(&taus));
        if shape.mu > pcs::MAX_MU {
            return Err(RecError::TooLong { mu: shape.mu });
        }
        Ok(Self {
            taus,
            placements,
            shape,
        })
    }

    /// Every global column's source: the packed witness, then each owned table's ports and committed columns.
    fn sources(taus: &[usize; Table::COUNT]) -> Vec<Source> {
        let stride_log = HashFlock::stride_log();
        let mut sources = vec![Source::Committed(taus[Table::Hash as usize] + stride_log)];
        for table in Table::OWNED {
            debug_assert_eq!(sources.len(), Self::columns(table).start);
            sources.extend((0..table.n_cols()).map(|c| {
                if c < table.n_ports() {
                    Source::Port {
                        column: Self::HASH_WITNESS,
                        port: c,
                        stride_log,
                    }
                } else {
                    Source::Committed(taus[table as usize])
                }
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
    pub(crate) const fn tau(&self, table: Table) -> usize {
        self.taus[table as usize]
    }

    /// The packed witness's window in the stack.
    pub(crate) fn hash_window(&self) -> Window {
        self.placements[Self::HASH_WITNESS]
            .window()
            .expect("the packed witness is committed")
    }

    /// The constraint batch's airs, one per owned table, each with its summand in table order.
    pub(crate) fn airs<S>(&self, summands: Vec<S>) -> Vec<Air<S>> {
        (Table::OWNED.into_iter().zip(summands))
            .map(|(table, summand)| Air {
                tau: self.tau(table),
                n_cols: table.n_cols(),
                n_public: 0,
                summand,
            })
            .collect()
    }

    /// Every column claim the opening discharges, the bus's then each owned table's, located in the stack.
    ///
    /// A port's claim is a strided evaluation of its packed witness.
    pub(crate) fn opening_claims<E: Copy>(&self, bus: Vec<ColumnClaim<E>>, tables: &[Claims<E>]) -> Vec<StackClaim<E>> {
        let mut claims = bus;
        for (&(base, _), table) in Self::TABLE_COLUMNS.iter().zip(tables) {
            claims.extend(table.evals.iter().enumerate().map(|(c, &value)| ColumnClaim {
                col: base + c,
                point: table.chi.clone(),
                value,
            }));
        }
        (claims.into_iter())
            .map(|c| match self.placements[c.col] {
                Placement::Committed(window) => StackClaim::Point {
                    offset: window.offset,
                    low_point: c.point,
                    value: c.value,
                },
                Placement::Port {
                    offset,
                    port,
                    stride_log,
                } => StackClaim::Strided {
                    offset,
                    slot: port,
                    stride_log,
                    point: c.point,
                    value: c.value,
                },
            })
            .collect()
    }
}
