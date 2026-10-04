//! Timestamp encoding and the circuit that orders a row's memory accesses.

use flock::circuit::{Builder, Circuit};

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
    /// - Inputs: row clock, then one previous timestamp per access.
    /// - Output: XOR mask for the next clock, with bit 41 recording an ordering failure.
    /// - Live accesses must be strictly ordered; padding accesses must remain non-live.
    ///
    /// # Panics
    ///
    /// Panics if an access slot does not fit in five bits.
    pub fn circuit(slots: &[u32]) -> Circuit {
        let mut c = Builder::new(&vec![Self::CLOCK_BITS; 1 + slots.len()], &[Self::CLOCK_BITS + 1]);
        let ts = c.input(0);
        let live = ts[Self::LIVE_BIT as usize];
        let mut in_order = Vec::with_capacity(slots.len());
        let mut disagree = None;
        for (i, &slot) in slots.iter().enumerate() {
            assert!(slot < 1 << Self::SLOT_BITS, "slot {slot} does not fit its bits");
            let prev = c.input(1 + i);
            // Strict ordering is the carry of current + !previous over the low 40 bits.
            // Equal timestamps produce no carry, rejecting a read of its own push.
            let mut carry = None;
            for (bit, &p) in prev[..Self::LIVE_BIT as usize].iter().enumerate() {
                let not_prev = c.not(p);
                carry = if bit >= Self::SLOT_BITS as usize {
                    let (x, y) = (c.xor(ts[bit], carry), c.xor(not_prev, carry));
                    let majority = c.and(x, y);
                    c.xor(majority, carry)
                } else if slot >> bit & 1 == 1 {
                    // The slot's bits are constants, so the carry is an OR or an AND.
                    c.or(not_prev, carry)
                } else {
                    c.and(not_prev, carry)
                };
            }
            in_order.push(carry);
            let differs = c.xor(prev[Self::LIVE_BIT as usize], live);
            disagree = c.or(disagree, differs);
        }
        let ordered = in_order.into_iter().reduce(|x, y| c.and(x, y)).flatten();
        let unordered = c.not(ordered);
        let late = c.and(live, unordered);
        let fail = c.or(late, disagree);
        // The live bit advances the cycle; padding rows keep their clock unchanged.
        // Carries identify precisely the bits toggled in the next timestamp.
        let mut carry = live;
        c.output(0, Self::SLOT_BITS as usize, carry);
        for (bit, &timestamp) in ts
            .iter()
            .enumerate()
            .take(Self::LIVE_BIT as usize)
            .skip(Self::SLOT_BITS as usize)
        {
            carry = c.and_output(0, bit + 1, timestamp, carry);
        }
        c.output(0, Self::FAIL_BIT as usize, fail);
        c.finish()
    }

    /// Reference clock transition as an XOR mask, with bit 41 set on an ordering failure.
    pub fn step(self, prev: &[u64], slots: &[u32]) -> u64 {
        let ts = self.timestamp;
        // The circuit reads 41 input bits and requires matching live bits.
        let read = |t: u64| t & ((1 << Self::CLOCK_BITS) - 1);
        let (ts, live) = (read(ts), ts >> Self::LIVE_BIT & 1);
        let low = (1u64 << Self::LIVE_BIT) - 1;
        let fail = prev.iter().zip(slots).any(|(&p, &slot)| {
            let p = read(p);
            let late = p & low >= (ts & low & !(Self::CYCLE - 1)) | u64::from(slot);
            p >> Self::LIVE_BIT != live || live == 1 && late
        });
        // A carry can flip several cycle bits, so the step is an XOR mask rather than an increment.
        let cycles = ts >> Self::SLOT_BITS;
        let carries = ((cycles + live) ^ cycles) & ((1 << (Self::CLOCK_BITS - Self::SLOT_BITS as usize)) - 1);
        carries << Self::SLOT_BITS | u64::from(fail) << Self::FAIL_BIT
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_clock_circuit_is_its_reference() {
        // Invariant: the clock circuit computes what the executor and the tables put in its step port.
        //
        // Fixture state: a row at cycle 1000 whose three accesses (slots 0, 1, 3) were last at cycles 999 and 1000.
        // Mutation: every previous timestamp swept around the row's own, the live bit flipped, and a padding row.
        let slots = [0, 1, 3];
        let circuit = Clock::circuit(&slots);
        let ts = Clock::SEED_CLOCK | (1000 * Clock::CYCLE);
        let honest = [ts - Clock::CYCLE + 3, ts - Clock::CYCLE + 1, ts];
        let mut cases = vec![
            (ts, honest),
            (0, [0; 3]),
            ((Clock::MAX_CYCLES * Clock::CYCLE) | Clock::SEED_CLOCK, honest),
        ];
        for i in 0..3 {
            for delta in [0, 1, 2, 3, 4, Clock::CYCLE] {
                for prev in [
                    ts ^ u64::from(slots[i]),
                    ts + delta,
                    ts - delta,
                    (ts - delta) ^ Clock::SEED_CLOCK,
                ] {
                    let mut case = honest;
                    case[i] = prev;
                    cases.push((ts, case));
                    cases.push((ts ^ Clock::SEED_CLOCK, case));
                }
            }
        }
        let words = (1usize << circuit.k_log()) / 64;
        for (ts, prev) in cases {
            let (mut z, mut az, mut bz) = (vec![0; words], vec![0; words], vec![0; words]);
            let inputs = [ts, prev[0], prev[1], prev[2]];
            circuit.witness_instance(&inputs, &mut z, &mut az, &mut bz);
            assert_eq!(
                z[4],
                Clock { timestamp: ts }.step(&prev, &slots),
                "ts {ts:#x}, prev {prev:x?}"
            );
        }
        assert_eq!(
            Clock { timestamp: ts }.step(&honest, &slots),
            Clock::CYCLE,
            "an honest row advances one cycle"
        );
    }
}
