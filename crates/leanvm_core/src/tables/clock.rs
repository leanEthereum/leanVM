//! Timestamp encoding and the circuit that orders a row's memory accesses.

use crate::rv::circuits::Products;
use flock::circuit::{Builder, Circuit, Wire};
use flock::clean;
use std::ops::Range;

/// A row timestamp, including its live bit and access slot.
///
/// Seeds and executed rows carry the live bit; padding rows have clock zero.
///
/// An ordering failure marks the next clock, preventing a matching successor or final state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Clock {
    /// Encoded timestamp supplied to the clock circuit.
    pub timestamp: u64,
}

impl Clock {
    /// The bit every real timestamp has.
    pub const LIVE_BIT: u32 = 40;

    /// The bits a row's clock circuit reads of a timestamp: up to the live bit.
    pub const CLOCK_BITS: usize = Self::LIVE_BIT as usize + 1;

    /// The low bits of a timestamp, which number a row's access slots.
    pub const SLOT_BITS: u32 = 5;

    /// One cycle of the clock.
    pub const CYCLE: u64 = 1 << Self::SLOT_BITS;

    /// The bit of a row's next clock that says one of its accesses is out of order.
    pub const FAIL_BIT: u32 = Self::LIVE_BIT + 1;

    /// The timestamp every cell is seeded at: cycle zero.
    pub const SEED_CLOCK: u64 = 1 << Self::LIVE_BIT;

    /// The clock the run starts on: cycle 1, so that every access is strictly after the seeds.
    pub const CLOCK_START: u64 = Self::SEED_CLOCK | Self::CYCLE;

    /// The cycles a run may take: past them the cycle count would carry into the live bit.
    pub const MAX_CYCLES: u64 = (1 << (Self::LIVE_BIT - Self::SLOT_BITS)) - 1;

    /// A row's clock slots: `rs1`, `rs2`, then `rd` last, after the RAM access if there is one.
    ///
    /// A row that skips an access leaves its slot unused.
    pub const REG_SLOTS: [u32; 3] = [0, 1, 3];

    /// Clock slot reserved for a single load or store.
    pub const RAM_SLOT: u32 = 2;

    /// A hash row reads its two registers, then accesses its block's words in order.
    pub const fn block_slot(k: usize) -> u32 {
        2 + k as u32
    }

    /// An extension-field row reads its three registers, then accesses its limbs in order: `a`'s, `b`'s, then `c`'s.
    pub const fn limb_slot(k: usize) -> u32 {
        Self::REG_SLOTS[2] + 1 + k as u32
    }

    /// Circuit checking that each access follows its cell's previous timestamp.
    ///
    /// - Inputs: row clock, its slot bits forced zero, then one previous timestamp per access.
    /// - Output: XOR mask for the next clock, with bit 41 recording an ordering failure.
    /// - Live accesses must be strictly ordered; padding accesses must remain non-live.
    ///
    /// # Panics
    ///
    /// Panics if `slots` are not a production table's clock slots ([`Self::builder`]).
    pub(crate) fn circuit(slots: &[u32]) -> Circuit {
        Self::builder(slots, &[], &[]).finish()
    }

    /// [`Self::circuit`] before it is finished, with more input and output ports of these widths past its own, for
    /// the caller to compute: a table with no class circuit checks what it needs of its operands there.
    ///
    /// Its gates are the Clean clock circuit of `verification/circuits/LeanVMCircuits/ClockStep.lean`, exported for
    /// each production table's slots (`ClockExport.lean`), whose rows Lean proves compute [`Self::step`]'s reference
    /// (`Clock.Holds`): per access the carry out of bit 39 of `(ts | slot) + !prev`, products before the slot's
    /// lowest set bit skipped as structural zeros, and the OR of its live-bit disagreement; then the AND of the
    /// in-order bits, `late` and `fail`; the step's carries go straight to its bits 6 to 40.
    ///
    /// Crate-internal: its only callers are the tables' clock circuits (`ClassSpec::clock_circuit` and
    /// `Ext::clock_circuit`), whose slot lists are exactly the five exported ones.
    ///
    /// # Panics
    ///
    /// Panics if `slots` are not a production table's clock slots.
    pub(crate) fn builder(slots: &[u32], inputs: &[usize], outputs: &[usize]) -> Builder {
        // Invariant: the clock's slot bits are structural zeros.
        // So the timestamp an access is ordered at, its slot ORed in, is the one its tuple carries, its slot XORed in.
        let input_bits: Vec<Range<usize>> = std::iter::once(Self::SLOT_BITS as usize..Self::CLOCK_BITS)
            .chain(std::iter::repeat_n(0..Self::CLOCK_BITS, slots.len()))
            .chain(inputs.iter().map(|&bits| 0..bits))
            .collect();
        let output_bits: Vec<usize> = std::iter::once(Self::CLOCK_BITS + 1)
            .chain(outputs.iter().copied())
            .collect();
        let mut c = Builder::with_input_ranges(&input_bits, &output_bits);
        let ts = c.input::<{ Self::CLOCK_BITS }>(0);
        let prev: Vec<[Wire; Self::CLOCK_BITS]> = (1..=slots.len()).map(|i| c.input(i)).collect();
        fn accesses<const N: usize>(prev: &[[Wire; Clock::CLOCK_BITS]]) -> &[[Wire; Clock::CLOCK_BITS]; N] {
            prev.try_into().expect("one previous timestamp per slot")
        }
        let [live, fail] = match slots {
            [0, 1, 3] => clean::clock_registers(&mut c, &ts, accesses(&prev)),
            [0, 3, 2] => clean::clock_load(&mut c, &ts, accesses(&prev)),
            [0, 1, 2] => clean::clock_store(&mut c, &ts, accesses(&prev)),
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] => {
                clean::clock_hash(&mut c, &ts, accesses(&prev))
            }
            [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] => clean::clock_ext(&mut c, &ts, accesses(&prev)),
            _ => panic!("slots {slots:?} are no production table's: no Clean clock circuit is exported for them"),
        };
        // The live bit advances the cycle; padding rows keep their clock unchanged.
        c.output(0, Self::SLOT_BITS as usize, live);
        c.output(0, Self::FAIL_BIT as usize, fail);
        c
    }

    /// Reference clock transition as an XOR mask, with bit 41 set on an ordering failure.
    pub fn step(self, prev: &[u64], slots: &[u32]) -> u64 {
        let ts = self.timestamp;
        // The circuit reads 41 input bits, the clock's above its slot bits, and requires matching live bits.
        let read = |t: u64| t & ((1 << Self::CLOCK_BITS) - 1);
        let (ts, live) = (read(ts) & !(Self::CYCLE - 1), ts >> Self::LIVE_BIT & 1);
        let low = (1u64 << Self::LIVE_BIT) - 1;
        let fail = prev.iter().zip(slots).any(|(&p, &slot)| {
            let p = read(p);
            let late = p & low >= (ts & low) | u64::from(slot);
            p >> Self::LIVE_BIT != live || live == 1 && late
        });
        // A carry can flip several cycle bits, so the step is an XOR mask rather than an increment.
        let cycles = ts >> Self::SLOT_BITS;
        let carries = ((cycles + live) ^ cycles) & ((1 << (Self::CLOCK_BITS - Self::SLOT_BITS as usize)) - 1);
        carries << Self::SLOT_BITS | u64::from(fail) << Self::FAIL_BIT
    }

    /// One instance of the clock circuit's witness by word arithmetic: what the walk of [`Self::circuit`] on `slots` writes, into zeroed buffers.
    ///
    /// Its input ports are the row's clock `ts`, then each access's previous timestamp `prev`.
    ///
    /// ```text
    ///     words 0..=n     inputs     z = A·z = the clock's bits 5..41, then each previous timestamp's 41 bits,  B·z = those bits set
    ///     word n + 1      step       bit 5 a copy of live, bits 6..41 its carries' products, bit 41 a copy of fail
    ///     bit 64(n + 2)   constant   z = A·z = B·z = 1
    ///     then            products   per access its compare's carries, then its OR into disagree;
    ///                                then the AND of the in-order bits, late, fail
    /// ```
    ///
    /// Access `i` compares by the sum `x + y`, `x = (ts ^ slot)` and `y = !prev` over 40 bits, whose carries `c = (x + y) ^ x ^ y` give each product:
    ///
    /// ```text
    ///     slot bits, above the slot's lowest one   A·z = y_b          B·z = c_b
    ///     bits 5..40                               A·z = x_b ^ c_b    B·z = y_b ^ c_b
    /// ```
    pub fn witness(slots: &[u32], ts: u64, prev: &[u64], z: &mut [u64], az: &mut [u64], bz: &mut [u64]) {
        Self::witness_with(slots, ts, prev, [0, 0], [z, az, bz], |_| {});
    }

    /// [`Self::witness`] for a circuit of [`Self::builder`] with `extra` more input and output ports past its own:
    /// the clock's words and products, then the products `more` pushes.
    ///
    /// The extra ports' words are the caller's to write: the step is word `n + 1 + extra[0]`, the constant the first
    /// bit of the word `extra[1]` past it.
    pub(crate) fn witness_with(
        slots: &[u32],
        ts: u64,
        prev: &[u64],
        extra: [usize; 2],
        [z, az, bz]: [&mut [u64]; 3],
        more: impl FnOnce(&mut Products),
    ) {
        let n = slots.len();
        assert_eq!(prev.len(), n);
        let step_word = n + 1 + extra[0];
        const LOW: u64 = (1 << Clock::LIVE_BIT) - 1;
        const READ: u64 = (1 << Clock::CLOCK_BITS) - 1;
        // The clock's slot bits are structural zeros, so its port reads the bits above them.
        const CLOCK: u64 = READ & !(Clock::CYCLE - 1);
        const CYCLES: u32 = Clock::LIVE_BIT - Clock::SLOT_BITS;
        let run = |bits: u32| (1u64 << bits) - 1;

        for (i, &word) in std::iter::once(&ts).chain(prev).enumerate() {
            let read = if i == 0 { CLOCK } else { READ };
            (z[i], az[i], bz[i]) = (word & read, word & read, read);
        }
        let ts = ts & CLOCK;
        let live = ts >> Self::LIVE_BIT;

        // The constant, then the products, start past the output ports.
        let mut products = Products::new([z, az, bz], step_word + 1 + extra[1]);
        products.push(1, 1, 1);

        let (mut in_order, mut disagree) = (0u32, 0);
        for (i, (&prev, &slot)) in prev.iter().zip(slots).enumerate() {
            let prev = prev & READ;
            let x = ts & LOW | u64::from(slot);
            let y = !prev & LOW;
            let c = (x + y) ^ x ^ y;
            if slot != 0 {
                let first = slot.trailing_zeros() + 1;
                let bits = Self::SLOT_BITS - first;
                products.push(y >> first & run(bits), c >> first & run(bits), bits);
            }
            let cycles = |w: u64| w >> Self::SLOT_BITS & run(CYCLES);
            products.push(cycles(x ^ c), cycles(y ^ c), CYCLES);
            in_order |= ((c >> Self::LIVE_BIT) as u32) << i;

            let differs = prev >> Self::LIVE_BIT ^ live;
            if i > 0 {
                products.push(disagree, differs, 1);
            }
            disagree |= differs;
        }
        let mut ordered = u64::from(in_order & 1);
        for i in 1..n {
            let next = u64::from(in_order >> i & 1);
            products.push(ordered, next, 1);
            ordered &= next;
        }
        let unordered = ordered ^ 1;
        products.push(live, unordered, 1);
        let late = live & unordered;
        products.push(late, disagree, 1);
        let fail = late | disagree;

        // The step is the carries of `cycle + live` from bit 5, and fail at bit 41.
        // Bits 5 and 41 are copies (`B·z = 1`); bit `j + 1` between is the product of `ts_j` and the carry at bit `j`.
        let cycle = ts >> Self::SLOT_BITS & run(CYCLES);
        let carries = ((cycle + live) ^ cycle) & run(CYCLES + 1);
        let step = carries << Self::SLOT_BITS | fail << Self::FAIL_BIT;
        let copies = live << Self::SLOT_BITS | fail << Self::FAIL_BIT;
        let ts_bits = cycle << (Self::SLOT_BITS + 1);
        let carry_bits = (carries & run(CYCLES)) << (Self::SLOT_BITS + 1);
        more(&mut products);
        let [z, az, bz] = products.finish();
        (z[step_word], az[step_word], bz[step_word]) = (
            step,
            ts_bits | copies,
            carry_bits | 1 << Self::SLOT_BITS | 1 << Self::FAIL_BIT,
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rv::Ext;
    use crate::tables::{TableId, Word};
    use fiat_shamir::{ProverState, SessionId, VerifierState};
    use flock::BatchRows;
    use flock::lincheck::LincheckCircuit;
    use flock::reduction;
    use flock::test_util::Witness;
    use primitives::field::F192;
    use primitives::test_util::Rng;

    #[test]
    fn clean_clock_proves_native_witnesses_and_rejects_false_steps_products_and_padding() {
        // Invariant: each production clock circuit proves the native witnesses of live, failing and padding rows, and a
        // flipped step bit, final private product or padding bit fails the proof.
        let mut rng = Rng::new(0x5C10);
        for table in TableId::ALL {
            let slots = table.spec().slots();
            let circuit = Clock::circuit(&slots);
            let block = circuit.block();
            let n_log = 6;
            let rows: Vec<Vec<u64>> = (0..1 << n_log)
                .map(|r| {
                    let ts = match r % 4 {
                        0 => 0,
                        1 => Clock::CLOCK_START,
                        _ => Clock::SEED_CLOCK | (rng.next_u64() % Clock::MAX_CYCLES * Clock::CYCLE),
                    };
                    let prev = slots.iter().map(|&slot| match rng.next_u64() % 4 {
                        0 => ts ^ u64::from(slot),
                        1 => ts.wrapping_sub(Clock::CYCLE),
                        2 => ts ^ Clock::SEED_CLOCK,
                        _ => rng.next_u64(),
                    });
                    std::iter::once(ts).chain(prev).collect()
                })
                .collect();
            let accepts = |tamper: Option<usize>| {
                let mut witness = Witness::by_instance(
                    &circuit,
                    BatchRows::new(&rows, &rows[0], n_log),
                    |row: &Vec<u64>, z, az, bz| {
                        Clock::witness(&slots, row[0], &row[1..], z, az, bz);
                    },
                );
                if let Some(bit) = tamper {
                    witness.z[bit / 64] ^= 1 << (bit % 64);
                }
                let label = b"clean-clock-native-witness";
                let mut ps = ProverState::new(&SessionId::new(label), &0u64);
                let claims = reduction::prove(&[witness.instance(block, n_log)], &mut ps);
                let proof = ps.into_proof();
                let mut vs = VerifierState::new(&SessionId::new(label), &0u64, &proof);
                reduction::verify(&[(block.shape(), n_log)], &mut vs)
                    .is_ok_and(|r| r[0].claim == claims[0] && r[0].matrices.check(block.circuit).is_ok())
                    && vs.check_eof().is_ok()
            };
            let name = table.spec().name;
            assert!(accepts(None), "{name}");
            let step = 64 * circuit.n_input_words();
            for bit in [
                step + Clock::SLOT_BITS as usize,
                step + Clock::SLOT_BITS as usize + 1,
                step + Clock::FAIL_BIT as usize,
                circuit.useful_bits() - 1,
                circuit.useful_bits(),
            ] {
                assert!(!accepts(Some(bit)), "{name}: flipping witness bit {bit} must reject");
            }
        }
    }

    #[test]
    fn the_clock_circuit_is_its_reference() {
        // Invariant: every production table's clock circuit computes what the executor and the tables put in its step port.
        //
        // Fixture state: per table, a row at cycle 1000 whose accesses were last one cycle earlier in their own slots.
        // Mutation: every previous timestamp swept around the row's own, the live bit flipped, and a padding row.
        for table in TableId::ALL {
            let slots = table.spec().slots();
            let n = slots.len();
            let circuit = Clock::circuit(&slots);
            let ts = Clock::SEED_CLOCK | (1000 * Clock::CYCLE);
            let honest: Vec<u64> = slots.iter().map(|&slot| ts - Clock::CYCLE + u64::from(slot)).collect();
            let mut cases = vec![
                (ts, honest.clone()),
                (0, slots.iter().map(|&slot| u64::from(slot)).collect()),
                ((Clock::MAX_CYCLES * Clock::CYCLE) | Clock::SEED_CLOCK, honest.clone()),
            ];
            for i in 0..n {
                for delta in [0, 1, 2, 3, 4, Clock::CYCLE] {
                    for prev in [
                        ts ^ u64::from(slots[i]),
                        ts + delta,
                        ts - delta,
                        (ts - delta) ^ Clock::SEED_CLOCK,
                    ] {
                        let mut case = honest.clone();
                        case[i] = prev;
                        cases.push((ts, case.clone()));
                        cases.push((ts ^ Clock::SEED_CLOCK, case));
                    }
                }
            }
            for (ts, prev) in cases {
                let inputs = [vec![ts], prev.clone()].concat();
                let z = Witness::of_instance(&circuit, &inputs).z;
                assert_eq!(
                    z[n + 1],
                    Clock { timestamp: ts }.step(&prev, &slots),
                    "{}: ts {ts:#x}, prev {prev:x?}",
                    table.spec().name
                );
            }
            assert_eq!(
                Clock { timestamp: ts }.step(&honest, &slots),
                Clock::CYCLE,
                "an honest row advances one cycle"
            );
        }
    }

    #[test]
    fn the_word_witness_is_the_gate_walk() {
        // Invariant: the word-level clock witness writes the tables the 64-lane walk of the clock circuit's gate list writes.
        //
        // Fixture state: every table's clock circuit, EXT's with its own ports.
        // Rows: padding rows (clock zero), the first and the last cycle, random cycles, all ones and random words; each previous timestamp at `ts ^ slot`, around it, with the live bit flipped, a padding tuple, a seed, zero, all ones, or a random word.
        // EXT's operands: pointers at zero, all ones, the sign bit, one limb or two below a wrap of 2^64 or of the sign bit, with every low bit set, aligned random or random; flags every legal word or a random word.
        let mut rng = Rng::new(0xC10C);
        let n_log = 12;
        for table in TableId::ALL {
            let spec = table.spec();
            let slots = spec.slots();
            let circuit = spec.clock_circuit();
            let operands = spec.clock_inputs;
            let rows: Vec<Vec<u64>> = (0..1 << n_log)
                .map(|r| {
                    let ts = match r % 6 {
                        0 => 0,
                        1 => Clock::CLOCK_START,
                        2 => Clock::SEED_CLOCK | (Clock::MAX_CYCLES * Clock::CYCLE),
                        3 => Clock::SEED_CLOCK | (rng.next_u64() % Clock::MAX_CYCLES * Clock::CYCLE),
                        4 => u64::MAX,
                        _ => rng.next_u64(),
                    };
                    let prev: Vec<u64> = (slots.iter())
                        .map(|&slot| {
                            let at = ts ^ u64::from(slot);
                            match rng.next_u64() % 10 {
                                0 => at,
                                1 => at.wrapping_sub(1),
                                2 => at.wrapping_add(1),
                                3 => at.wrapping_sub(Clock::CYCLE),
                                4 => at ^ Clock::SEED_CLOCK,
                                5 => u64::from(slot),
                                6 => Clock::SEED_CLOCK,
                                7 => 0,
                                8 => u64::MAX,
                                _ => rng.next_u64(),
                            }
                        })
                        .collect();
                    let operands: Vec<u64> = (operands.iter())
                        .map(|&word| match (word, rng.next_u64() % 12) {
                            (Word::Flags, k) if k < 8 => Ext::LEGAL[k as usize % Ext::LEGAL.len()],
                            (Word::Flags, _) => rng.next_u64(),
                            (_, 0) => 0,
                            (_, 1) => u64::MAX,
                            (_, 2) => 1 << 63,
                            (_, 3) => 8u64.wrapping_neg(),
                            (_, 4) => 16u64.wrapping_neg(),
                            (_, 5) => (1 << 63) - 8,
                            (_, 6) => (1 << 63) - 16,
                            (_, 7) => (1 << 63) - 1,
                            (_, 8) => 7,
                            (_, 9) => rng.next_u64() & !7,
                            _ => rng.next_u64(),
                        })
                        .collect();
                    [vec![ts], prev, operands].concat()
                })
                .collect();
            let rows = BatchRows::new(&rows, &rows[0], n_log);
            let walk = Witness::by_walk(&circuit, rows, |row: &Vec<u64>, words| words.copy_from_slice(row));
            let words = Witness::by_instance(&circuit, rows, |row: &Vec<u64>, z, az, bz| {
                spec.clock_witness(&slots, row, z, az, bz);
            });
            let name = spec.name;
            assert!(walk.z == words.z, "z, {name}");
            assert!(walk.az == words.az, "A·z, {name}");
            assert!(walk.bz == words.bz, "B·z, {name}");
        }
    }

    #[test]
    fn a_clock_with_slot_bits_cannot_read_its_own_push() {
        // Invariant: an access is ordered at the timestamp its tuple carries, so it cannot pull its own push.
        //
        // Fixture state: a live row at cycle 1000 whose clock has bit 0 set.
        // Mutation: its access in slot 1 pulls its own push, at `ts ^ 1`, which is below `ts | 1`, so the order check passes.
        let slots = [0, 1, 3];
        let circuit = Clock::circuit(&slots);
        let ts = Clock::SEED_CLOCK | (1000 * Clock::CYCLE) | 1;
        let prev = [ts - Clock::CYCLE, ts ^ 1, ts - Clock::CYCLE];
        assert_eq!(Clock { timestamp: ts }.step(&prev, &slots) >> Clock::FAIL_BIT, 0);

        // The instance as the gate walk fills it, then the clock's bit 0 as the forger commits it.
        let mut z = Witness::of_instance(&circuit, &[ts, prev[0], prev[1], prev[2]]).z;
        z[0] |= 1;
        let w: Vec<F192> = (0..circuit.n_cols())
            .map(|s| [F192::ZERO, F192::ONE][(z[s / 64] >> (s % 64) & 1) as usize])
            .collect();

        // Every row holds but bit 0's, whose empty row forces it to zero.
        let (a, b) = circuit.row_values(&w);
        let broken: Vec<usize> = (0..w.len()).filter(|&s| a[s] * b[s] != w[s]).collect();
        assert_eq!(broken, [0]);
    }
}
