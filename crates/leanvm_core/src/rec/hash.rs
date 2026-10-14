//! The hash table's rows as flock proves them: one packed BLAKE2s witness per row, its first words the table's ports.
//!
//! The ports are the compression circuit's own:
//!
//! ```text
//!     word    0   1   2..6     6..14    14..18
//!     port    t   f   h0..h3   m0..m7   o0..o3
//! ```

use super::circuit::Compression;
use super::layout::RecLayout;
use crate::commitment::RingSwitch;
use crate::rv::circuits::blake2s_witness;
use crate::tables::{CircuitId, TableId};
use fiat_shamir::ProverState;
use flock::reduction::{self, Instance};
use flock::{BatchRows, Tables};
use parallel::SendPtr;
use primitives::field::F64;
use std::mem::MaybeUninit;

/// The BLAKE2s class circuit, whose packed witness proves every hash row.
pub(crate) const CIRCUIT: CircuitId = CircuitId::class(TableId::HASH).expect("the HASH class has a circuit");

/// How many ports the hash table reads.
pub(crate) const N_PORTS: usize = 18;

/// The hash table's flock batch, one instance per row, but its `z`, which is the stack's packed-witness window.
pub(super) struct HashBatch {
    /// The base-two logarithm of the table's height.
    tau: usize,
    /// The rows, before the padding rows: every instance from here on is the padding compression's.
    live: usize,
    /// The batch's products, which the reduction reads beside `z`.
    tables: Tables,
}

impl HashBatch {
    /// The batch of the hash rows at height `2^tau`.
    ///
    /// - Every row's packed witness is written into `z`.
    /// - Every row's ports are written into `ports`, one buffer a port, each slot of which is written.
    pub(super) fn new(rows: &[Compression], tau: usize, z: &mut [F64], ports: &mut [Box<[MaybeUninit<F64>]>]) -> Self {
        let z = F64::as_bits_mut(z);
        let port_ptrs: Vec<SendPtr<F64>> = ports.iter_mut().map(|p| SendPtr(p.as_mut_ptr().cast())).collect();
        // A live row's ports are copied while its words are in cache; the padding rows' after.
        let ports_of = |j: usize, _: &Compression, z: &[u64]| {
            if j < rows.len() {
                for (ptr, &word) in port_ptrs.iter().zip(z) {
                    // SAFETY: row `j` is visited once, and each port buffer holds every row.
                    unsafe { ptr.0.add(j).write(F64(word)) };
                }
            }
        };
        let tables = CIRCUIT.circuit().witness_by_instance(
            z,
            BatchRows::new(rows, &Compression::PADDING, tau),
            |row, z, az, bz| blake2s_witness(row.inputs(), z, az, bz),
            ports_of,
        );
        // The padding rows share one witness, whose ports fill the buffers' tails.
        if rows.len() < 1 << tau {
            let padding = &z[rows.len() << CIRCUIT.stride_log()..];
            for (port, &word) in ports.iter_mut().zip(padding) {
                port[rows.len()..].fill(MaybeUninit::new(F64(word)));
            }
        }
        Self {
            tau,
            live: rows.len(),
            tables,
        }
    }

    /// Prove every hash row: zerocheck, then lincheck, a batch of one circuit, to one ring-switched claim on the packed witness.
    pub(super) fn prove(self, layout: &RecLayout, q: &[F64], ps: &mut ProverState) -> RingSwitch {
        let window = layout.hash_window();
        let z = F64::as_bits(&q[window.offset..window.offset + (1 << window.n_vars)]);
        let instance = Instance {
            block: CIRCUIT.circuit().block(),
            n_blocks_log: self.tau,
            live: self.live,
            z,
            az: &self.tables.az,
            bz: &self.tables.bz,
        };
        let [reduced] = <[_; 1]>::try_from(reduction::prove(&[instance], ps)).expect("one circuit");
        window.ring(reduced)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bus::Coord;
    use crate::rec::table::Table;
    use crate::tables::{ClassSpec, Word};

    #[test]
    fn the_hash_ports_are_the_precompile_ports() {
        // The generated slot forms name the ports by column: `h` is slot 0, `(t, f)` slot 1, the message words slots
        // 8 to 15, the output slot 6, and the mux bit slot 3, the one committed column after the ports.
        let ports: Vec<Word> = ClassSpec::HASH.ports().collect();
        assert_eq!(ports.len(), N_PORTS);
        let col = |s: usize, limb: usize| match Table::Hash.slot(s).0[limb] {
            Coord::Col(c) => c,
            ref other => panic!("slot {s} limb {limb} is {other:?}"),
        };
        assert_eq!((ports[col(1, 0)], ports[col(1, 1)]), (Word::V2, Word::Flags));
        assert!((0..4).all(|i| ports[col(0, i)] == Word::Cell(i as u8)));
        assert!((0..8).all(|i| ports[col(8 + i, 0)] == Word::Cell(8 + i as u8)));
        assert!((0..4).all(|i| ports[col(6, i)] == Word::CellNew(4 + i as u8)));
        assert_eq!(col(3, 0), N_PORTS);
    }
}
