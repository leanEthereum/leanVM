//! RAM boundaries whose zero-filled tail commits only the cells accessed.

use super::*;
use flock::circuit::{Builder, Circuit, Wire};
use primitives::field::mul_by_g;

/// A separate channel links the ascending address chain.
pub(crate) const SEP_ORDER: F64 = mul_by_g(tables::SEP_REG);
/// The circuit's ports: previous address, address, final timestamp, final word, seed timestamp, failure bit.
pub(crate) const WIDTH: usize = 6;
/// A power-of-two circuit cube covering all ports and comparison gates.
pub(crate) const K_LOG: usize = 10;
/// Each packed word holds 64 bits, so an instance occupies 2^(k - 6) words.
pub(crate) const STRIDE_LOG: usize = K_LOG - 6;
/// The batch must fill the zerocheck minimum cube.
pub(crate) const MIN_TAU: usize = crate::class_flock::MIN_CUBE_LOG - K_LOG;

/// The sparse table height and its final address, bound before the commitment.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Boundary {
    /// The power-of-two row count, including cancelling padding.
    pub tau: usize,
    /// The ascending chain ends at this aligned RAM address.
    pub end: u64,
}

/// The public image occupies one dense, aligned block.
pub(crate) fn image_log(p: &rv::Program) -> usize {
    // Round up the image so every remaining cell has public initial value zero.
    crate::log2_ceil_usize(p.image().len().max(1))
}

/// The last address of the dense image block starts the ascending chain.
pub(crate) fn start(p: &rv::Program) -> u64 {
    rv::RAM_BASE + ((1u64 << image_log(p)) - 1) * 8
}

/// Select the representation by the exact number of committed words.
pub(crate) fn boundary(p: &rv::Program, tr: &Trace) -> Option<Boundary> {
    // Every live timestamp identifies a touched cell, including reads of zero.
    let low = 1usize << image_log(p);
    let count = tr.ram_ts[low..].iter().filter(|t| t.0 != tables::SEED_CLOCK).count();
    let tau = crate::log2_ceil_usize(count.max(1)).max(MIN_TAU);
    let sparse_words = 2 * low + (1usize << (tau + STRIDE_LOG));
    let dense_words = 2usize << p.log_ram();
    // A tie retains the dense boundary and avoids another reduction.
    (sparse_words < dense_words).then(|| Boundary {
        tau,
        end: tr.ram_ts[low..]
            .iter()
            .rposition(|t| t.0 != tables::SEED_CLOCK)
            .map_or_else(|| start(p), |i| rv::RAM_BASE + ((low + i) as u64) * 8),
    })
}

/// Carry out of a + !b proves the strict unsigned comparison b < a.
fn less(c: &mut Builder, b: &[Wire], a: &[Wire]) -> Wire {
    // The final carry is one precisely when the left operand is strictly smaller.
    let mut carry = None;
    for (&b, &a) in b.iter().zip(a) {
        let not_b = c.not(b);
        let x = c.xor(a, carry);
        let y = c.xor(not_b, carry);
        let product = c.and(x, y);
        carry = c.xor(product, carry);
    }
    carry
}

/// A live cell is word aligned, inside RAM and strictly after its predecessor, and a padding row is zero.
///
/// - Every address is above the image: a pulled predecessor is the public start or a pushed address, so the chain descends to the start.
/// - A live row is one whose final timestamp has the live bit, which every access sets and padding clears.
pub(crate) fn circuit(p: &rv::Program) -> Circuit {
    // Inputs: previous address, current address, final timestamp, final word.
    let mut c = Builder::new(&[31, 31, tables::CLOCK_BITS, 64], &[tables::CLOCK_BITS, 1]);
    let (previous, address, timestamp, value) = (c.input(0), c.input(1), c.input(2), c.input(3));
    let live = timestamp[tables::LIVE_BIT as usize];
    let mut bad = None;
    // A live address has RAM's base above the region and zero alignment bits; a padding one is zero.
    for bit in (0..3).chain(p.log_ram() + 3..31) {
        let expected = if rv::RAM_BASE >> bit & 1 == 1 { live } else { None };
        let mismatch = c.xor(address[bit], expected);
        bad = c.or(bad, mismatch);
    }
    // Strict increase rules out a duplicate address and a cycle on the order channel.
    let ordered = less(&mut c, &previous, &address);
    let unordered = c.not(ordered);
    let mismatch = c.and(live, unordered);
    bad = c.or(bad, mismatch);
    // A padding row is zero, so its tuples cancel on both channels and seed nothing.
    let mut nonzero = None;
    let free_address = &address[3..p.log_ram() + 3];
    let free_timestamp = &timestamp[..tables::LIVE_BIT as usize];
    for &wire in previous.iter().chain(free_address).chain(free_timestamp).chain(&value) {
        nonzero = c.or(nonzero, wire);
    }
    let padding = c.not(live);
    let mismatch = c.and(padding, nonzero);
    bad = c.or(bad, mismatch);
    c.output(0, tables::LIVE_BIT as usize, live);
    c.output(1, 0, bad);
    let circuit = c.finish();
    assert_eq!(circuit.k_log(), K_LOG, "the sparse boundary circuit size moved");
    circuit
}

/// Native circuit tables retained until the one shared opening.
pub(crate) struct Prepared {
    /// The public gate list fixes the region bounds and port order.
    circuit: Circuit,
    /// The instance cube shared by the packed witness and native tables.
    tau: usize,
    /// Packed bits of every circuit instance.
    z: zk_alloc::ArenaVec<u64>,
    /// The left side of every circuit product.
    a: zk_alloc::ArenaVec<u64>,
    /// The right side of every circuit product.
    b: zk_alloc::ArenaVec<u64>,
    /// The byte stripes consumed by the linear reduction.
    stripe: zk_alloc::ArenaVec<u8>,
}

impl Prepared {
    /// Build the ascending chain and pad with rows cancelling on both channels.
    pub(crate) fn build(p: &rv::Program, tr: &Trace, boundary: Boundary, window: &mut [F64]) -> Self {
        let mut previous = start(p);
        let mut rows = Vec::new();
        // Only the zero tail is private: public image cells keep their dense boundary.
        for i in 1usize << image_log(p)..tr.ram_ts.len() {
            if tr.ram_ts[i].0 != tables::SEED_CLOCK {
                let address = rv::RAM_BASE + i as u64 * 8;
                rows.push([previous, address, tr.ram_ts[i].0, tr.ram_fin[i].0]);
                previous = address;
            }
        }
        assert_eq!(previous, boundary.end);
        let circuit = circuit(p);
        let (z, a, b, stripe) = circuit.generate_witness_from(&rows, &[0; 4], boundary.tau, |row, words| {
            words.copy_from_slice(row);
        });
        assert_eq!(window.len(), z.len(), "the sparse witness fills its committed window");
        // Ports remain the sole committed copy of each boundary word.
        for (dst, &src) in window.iter_mut().zip(z.iter()) {
            *dst = F64(src);
        }
        Self {
            circuit,
            tau: boundary.tau,
            z,
            a,
            b,
            stripe,
        }
    }

    /// Reduce circuit validity against the same commitment as the machine.
    pub(crate) fn prove(&self, ps: &mut ProverState) -> flock::reduction::SliceClaim {
        let block = self.circuit.block();
        let stage = block.prove_zerocheck(self.tau, &self.z, &self.a, &self.b, ps);
        block.prove_lincheck(self.tau, stage, &self.stripe, ps)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::asm::*;
    use proptest::prelude::*;

    fn program() -> Program {
        // The first image word is public and a distant zero cell is read, then written.
        let text = Asm::new()
            .li(Reg::T0, rv::RAM_BASE + 2048)
            .load(Ld, Reg::T1, 0, Reg::T0)
            .i(Addi, Reg::T1, Reg::T1, 7)
            .store(Sd, Reg::T1, 0, Reg::T0)
            .load(Ld, Reg::A0, 0, Reg::T0)
            .exit()
            .finish();
        Program::new(&text, rv::TEXT_BASE, vec![19], 10, 0).expect("valid sparse RAM program")
    }

    #[test]
    fn sparse_boundary_proves_read_then_write() {
        let program = program();
        let exec = program.execute(&[]).unwrap();
        // A zero-valued first read must still cause a boundary row to be committed.
        let boundary = boundary(&program.rv, &exec.trace).expect("one touched cell is cheaper than dense RAM");
        assert_eq!(boundary.end, rv::RAM_BASE + 2048);
        let witness = program.build(&exec);
        assert!(
            crate::leaf::unmatched_leaves(
                &witness.layout.push,
                &witness.layout.pull,
                &witness.layout.producers,
                &witness.columns()
            )
            .is_empty()
        );
        let (proof, _) = super::super::prove_execution(&program, &exec, pcs::Rate::MIN);
        verify(&program, &exec.output, &proof).expect("the sparse boundary verifies");
        assert_eq!(exec.output[0], 7);
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(256))]

        #[test]
        fn sparse_rows_match_integer_bounds(
            log_ram in 3usize..=rv::MAX_LOG_RAM,
            previous in 0u64..16,
            current in 0u64..16,
            misalignment in 0u64..2,
            timestamp in 0u64..1 << tables::CLOCK_BITS,
            value in any::<u64>(),
            dirty_padding in any::<bool>(),
        ) {
            // Declared capacities vary without allocating their memory regions.
            let text = Asm::new().exit().finish();
            let p = Program::new(&text, rv::TEXT_BASE, vec![19], log_ram, 0).unwrap();
            let circuit = circuit(&p.rv);
            let live = timestamp >> tables::LIVE_BIT == 1;
            let row = if live {
                // Small offsets make duplicates, descents and cells past a small RAM likely.
                [rv::RAM_BASE + 8 * previous, rv::RAM_BASE + 8 * current + misalignment, timestamp, value]
            } else {
                // Padding may try to carry a private word.
                [0, 0, 0, if dirty_padding { value } else { 0 }]
            };

            // Integer comparisons are the reference for the gate list.
            let valid = if live {
                row[0] < row[1] && row[1] < rv::RAM_BASE + (8u64 << log_ram) && row[1].is_multiple_of(8)
            } else {
                row[3] == 0
            };
            let mut z = vec![0; 1 << STRIDE_LOG];
            let mut a = z.clone();
            let mut b = z.clone();
            circuit.witness_instance(&row, &mut z, &mut a, &mut b);
            prop_assert_eq!(z[4], u64::from(live) * tables::SEED_CLOCK);
            prop_assert_eq!(z[5], u64::from(!valid));
        }
    }

    #[test]
    fn sparse_boundary_bus_rejects_omission_duplication_and_false_seeds() {
        let p = program();
        let exec = p.execute(&[]).unwrap();
        let assert_unbalanced = |w: Witness| {
            // A forged boundary leaves tuples unmatched, whatever the bus challenge.
            assert!(
                !crate::leaf::unmatched_leaves(&w.layout.push, &w.layout.pull, &w.layout.producers, &w.columns())
                    .is_empty()
            );
        };
        // Omission: a real load/store chain loses its final boundary tuple.
        let mut omitted = p.execute(&[]).unwrap();
        omitted.trace.ram_ts[256] = F64(tables::SEED_CLOCK);
        assert_unbalanced(p.build(&omitted));
        for mutation in 0..4 {
            let mut w = p.build(&exec);
            let base = schema().n + 1;
            let ports: Vec<_> = w
                .virt
                .iter()
                .filter(|(col, _)| *col >= base)
                .map(|(_, values)| values[0])
                .collect();
            // Mutation: duplicate the first row, move a cell into the image, disconnect the chain, or seed at a later clock.
            for (col, values) in &mut w.virt {
                if *col >= base {
                    let port = *col - base;
                    match mutation {
                        0 => values[1] = ports[port],
                        1 if port == 1 => values[0] = F64(rv::RAM_BASE),
                        2 if port == 0 => values[0] = F64(rv::RAM_BASE + 8),
                        3 if port == 4 => values[0] = F64(tables::SEED_CLOCK | 1),
                        _ => {}
                    }
                }
            }
            assert_unbalanced(w);
        }
        // A forged first load reads nine from the zero tail, every other column agreeing with it.
        let text = Asm::new()
            .li(Reg::T0, rv::RAM_BASE + 2048)
            .load(Ld, Reg::A0, 0, Reg::T0)
            .exit()
            .finish();
        let p = Program::new(&text, rv::TEXT_BASE, vec![19], 10, 0).unwrap();
        let mut exec = p.execute(&[]).unwrap();
        let load = tables::table_of(rv::Class::Load).unwrap();
        let row = exec.trace.rows[load].iter_mut().find(|r| r.ts != 0).unwrap();
        (row.ram.old, row.ram.new, row.out) = (9, 9, 9);
        exec.trace.ram_fin[256] = F64(9);
        exec.trace.reg_fin[Reg::A0.index()] = F64(9);
        exec.output[0] = 9;
        assert_unbalanced(p.build(&exec));
    }
}
