//! Read-write memory by Twist (§sec:memchan).
//!
//! A memory is a log of its accesses in the order they happen, one row each.
//!
//! ```text
//!     Val(k, j) = M0(k) + sum_{j' < j} wa(k, j') inc(j')
//!     read      = Val(addr, j)
//!     write     = Val(addr, j) + inc(j)
//! ```
//!
//! - A log's live rows push their accesses onto the bus at position `g^j`, which the tables' rows pull.
//! - The read-write sumcheck reduces the bus's share of the log to its committed columns.
//! - The evaluation sumcheck proves `Val`, and that every address word is one-hot.
//!
//! What varies with the run is the verifier's input, not the shape: the live rows' count, as bits, and the outputs.

mod prove;
mod rounds;
mod verify;

pub(crate) use prove::{LogWitness, leaves, prove};
pub(crate) use verify::{live_bits, verify};

use crate::leaf::SparseColumn;
use crate::pcs::SliceClaim;
use fiat_shamir::arith::Arith;
use fiat_shamir::transcript::TranscriptError;
use primitives::field::{F64, F192};
use std::sync::Arc;
use thiserror::Error;

/// Bits of an address chunk.
pub(crate) const CHUNK_BITS: usize = 6;

/// Values of an address chunk: its one-hot word has a bit per value.
pub(crate) const CHUNK: usize = 1 << CHUNK_BITS;

/// The most chunks a memory cell has.
pub(crate) const MAX_CHUNKS: usize = 4;

/// A slot of a log's bus tuple.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Slot {
    /// A constant.
    Const(F64),
    /// `base`, plus `delta` on a flagged row.
    Flagged { base: F64, delta: F64 },
    /// The row's position `g^j`.
    Time,
    /// The word naming the group's cell.
    Address(usize),
    /// The group's cell before the row writes.
    Read(usize),
    /// The group's cell after the row writes.
    Written(usize),
}

/// A region of memory cells: its words, at a run of top-chunk values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Region {
    /// The address of its first word.
    pub(crate) base: u64,
    /// The base-two logarithm of its words.
    pub(crate) log_words: usize,
    /// Its first top-chunk value.
    pub(crate) first: usize,
}

impl Region {
    /// Its top-chunk values: one per `2^low` words, at least one.
    const fn symbols(self, low: usize) -> usize {
        1 << self.log_words.saturating_sub(low)
    }

    /// The cell of its word `z`.
    pub(crate) const fn cell(self, z: usize, low: usize) -> usize {
        (z & ((1 << low) - 1)) | (self.first + (z >> low)) << low
    }
}

/// RAM and the advice as memory cells.
///
/// A cell is `low` bits, then a top chunk whose low half holds RAM's values and high half the advice's.
#[derive(Clone, Debug)]
pub(crate) struct Regions {
    /// The cell bits below the top chunk.
    pub(crate) low: usize,
    /// RAM.
    pub(crate) ram: Region,
    /// The advice.
    pub(crate) advice: Region,
    /// RAM's initial words.
    pub(crate) image: Arc<SparseColumn>,
}

impl Regions {
    /// RAM and the advice at these bases and sizes, with the fewest low chunks leaving each half the top chunk.
    pub(crate) fn new(bases: [u64; 2], log_ram: usize, log_advice: usize, image: &[u64]) -> Self {
        let low = CHUNK_BITS
            * log_ram
                .max(log_advice)
                .saturating_sub(CHUNK_BITS - 1)
                .div_ceil(CHUNK_BITS);
        Self {
            low,
            ram: Region {
                base: bases[0],
                log_words: log_ram,
                first: 0,
            },
            advice: Region {
                base: bases[1],
                log_words: log_advice,
                first: CHUNK / 2,
            },
            image: Arc::new(SparseColumn::new(log_ram, &[(0, image)])),
        }
    }

    /// The chunks of a cell.
    pub(crate) const fn chunks(&self) -> usize {
        self.low / CHUNK_BITS + 1
    }

    /// The region holding top-chunk value `symbol`.
    fn region_of(&self, symbol: usize) -> Option<Region> {
        [self.ram, self.advice]
            .into_iter()
            .find(|r| (r.first..r.first + r.symbols(self.low)).contains(&symbol))
    }

    /// The word naming cell `k`: its top value's word, then its low bits as a word offset.
    pub(crate) fn address(&self, k: usize) -> F64 {
        let offset = ((k & ((1 << self.low) - 1)) as u64) << 3;
        self.top_word(k >> self.low) + F64(offset)
    }

    /// The word of top-chunk value `symbol`'s first cell, zero for a value of no region.
    fn top_word(&self, symbol: usize) -> F64 {
        self.region_of(symbol).map_or(F64::ZERO, |r| {
            F64(r.base | ((symbol - r.first) as u64) << (self.low + 3))
        })
    }

    /// The region smaller than a top-chunk value, if any: its low bits past its size must be zero.
    pub(crate) fn partial(&self) -> Option<Region> {
        [self.ram, self.advice].into_iter().find(|r| r.log_words < self.low)
    }

    /// The low chunks a partial region does not fill, with the values each allows.
    pub(crate) fn allowed(&self, region: Region) -> Vec<(usize, usize)> {
        (0..self.chunks() - 1)
            .filter_map(|c| {
                let bits = region.log_words.saturating_sub(CHUNK_BITS * c).min(CHUNK_BITS);
                (bits < CHUNK_BITS).then_some((c, 1 << bits))
            })
            .collect()
    }

    /// The top-chunk values no region holds.
    pub(crate) fn unused(&self) -> impl Iterator<Item = usize> + '_ {
        (0..CHUNK).filter(|&s| self.region_of(s).is_none())
    }

    /// A region's words at a cell point: the factor its fixed cell bits give, and the point its words are at.
    pub(crate) fn at<A: Arith>(&self, a: &mut A, fc_cell: &[A::E], region: Region) -> (A::E, Vec<A::E>) {
        let (r_low, r_top) = fc_cell.split_at(self.low);
        let (in_low, in_top) = (
            region.log_words.min(self.low),
            region.log_words.saturating_sub(self.low),
        );
        let mut factor = a.one();
        for &z in &r_low[in_low..] {
            factor = a.times_one_plus(factor, z);
        }
        for (i, &z) in r_top.iter().enumerate().skip(in_top) {
            factor = match region.first >> i & 1 {
                1 => a.mul(factor, z),
                _ => a.times_one_plus(factor, z),
            };
        }
        (factor, [&r_low[..in_low], &r_top[..in_top]].concat())
    }
}

/// What a log records.
#[derive(Clone, Debug)]
pub(crate) enum Kind {
    /// The register file: zero at the start, a flag forbidding a row's write, and cells whose final values are public.
    Registers { outputs: Vec<usize> },
    /// RAM and the advice.
    Memory(Regions),
}

/// A log's public structure, which both sides derive from the program and the announced counts.
#[derive(Clone, Debug)]
pub(crate) struct LogShape {
    /// The base-two logarithm of its rows.
    pub(crate) log_rows: usize,
    /// The bus tuple a live row pushes.
    pub(crate) slots: Vec<Slot>,
    /// What it records.
    pub(crate) kind: Kind,
}

impl LogShape {
    /// The addresses a row has: the registers' two reads and write, or memory's one access.
    pub(crate) const fn groups(&self) -> usize {
        match self.kind {
            Kind::Registers { .. } => 3,
            Kind::Memory(_) => 1,
        }
    }

    /// The group the row's increment is written at.
    pub(crate) const fn write(&self) -> usize {
        self.groups() - 1
    }

    /// The chunks of an address.
    pub(crate) const fn chunks(&self) -> usize {
        match &self.kind {
            Kind::Registers { .. } => 1,
            Kind::Memory(regions) => regions.chunks(),
        }
    }

    /// The bits of a cell.
    pub(crate) const fn cell_bits(&self) -> usize {
        CHUNK_BITS * self.chunks()
    }

    /// Whether rows carry a flag.
    pub(crate) const fn flagged(&self) -> bool {
        matches!(self.kind, Kind::Registers { .. })
    }

    /// The word naming cell `k`.
    pub(crate) fn address(&self, k: usize) -> F64 {
        match &self.kind {
            Kind::Registers { .. } => F64(k as u64),
            Kind::Memory(regions) => regions.address(k),
        }
    }

    /// The words naming the cells, at a cell point.
    pub(crate) fn address_mle<A: Arith>(&self, a: &mut A, fc_cell: &[A::E]) -> A::E {
        match &self.kind {
            Kind::Registers { .. } => a.int_index(F64::ZERO, 0, fc_cell),
            Kind::Memory(regions) => {
                let (low, top) = fc_cell.split_at(regions.low);
                let words: Vec<F64> = (0..CHUNK).map(|s| regions.top_word(s)).collect();
                let top = a.public_mle(&words, top);
                let offset = a.int_index(F64::ZERO, 3, low);
                a.add(top, offset)
            }
        }
    }

    /// The read-write sumcheck's coefficients per cycle round: `u prod_c E_c inner`.
    pub(crate) const fn read_write_coeffs(&self) -> usize {
        self.chunks() + 3
    }

    /// The evaluation sumcheck's coefficients: `LT prod_c E_c inc`, or `eq x^3` for the collisions.
    pub(crate) const fn evaluation_coeffs(&self) -> usize {
        let val = self.chunks() + 2;
        (if val > 4 { val } else { 4 }) + 1
    }
}

/// The slot weights of a log's tuple, gathered by role.
pub(crate) struct Link<E> {
    /// Each group's weight on its cell's value.
    pub(crate) value: Vec<E>,
    /// Each group's weight on its address word.
    pub(crate) address: Vec<E>,
    /// The weight on the increment, at the write group.
    pub(crate) inc: E,
    /// The weight on the flag.
    pub(crate) flag: E,
    /// The weight on the constant slots.
    pub(crate) constant: E,
    /// The weight on the position.
    pub(crate) time: E,
}

impl<E: Copy> Link<E> {
    /// Gather the fingerprint's slot weights.
    pub(crate) fn new<A: Arith<E = E>>(a: &mut A, shape: &LogShape, weights: &[E]) -> Self {
        let zero = a.zero();
        let mut link = Self {
            value: vec![zero; shape.groups()],
            address: vec![zero; shape.groups()],
            inc: zero,
            flag: zero,
            constant: zero,
            time: zero,
        };
        for (slot, &w) in shape.slots.iter().zip(weights) {
            match *slot {
                Slot::Const(c) => link.constant = a.mul_const_add(w, F192::from(c), link.constant),
                Slot::Flagged { base, delta } => {
                    link.constant = a.mul_const_add(w, F192::from(base), link.constant);
                    link.flag = a.mul_const_add(w, F192::from(delta), link.flag);
                }
                Slot::Time => link.time = a.add(link.time, w),
                Slot::Address(g) => link.address[g] = a.add(link.address[g], w),
                Slot::Read(g) => link.value[g] = a.add(link.value[g], w),
                Slot::Written(g) => {
                    link.value[g] = a.add(link.value[g], w);
                    link.inc = a.add(link.inc, w);
                }
            }
        }
        link
    }
}

/// What the verifier knows of a run's log beyond its shape.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Statement<'a, E> {
    /// The live rows' count, by its bits, lowest first: one per row bit, and one past.
    pub(crate) live: &'a [E],
    /// The registers' final values at the shape's output cells.
    pub(crate) outputs: &'a [E],
}

/// What the bus leaves a log: its block's leaves at the bus point.
#[derive(Clone, Debug)]
pub(crate) struct LinkShare<E> {
    /// The bus point over the log's rows.
    pub(crate) point: Vec<E>,
    /// The leaves' multilinear extension there.
    pub(crate) value: E,
    /// The fingerprint's slot weights.
    pub(crate) weights: Vec<E>,
    /// The fingerprint's shift.
    pub(crate) beta: E,
}

/// A claim on RAM's image, left to the program: `weight image(point) = value`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ImageClaim<E> {
    pub(crate) weight: E,
    pub(crate) point: Vec<E>,
    pub(crate) value: E,
}

/// What a log leaves the opening and the program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LogOpening<E> {
    /// Each address word column, group-major: its slices at the read-write point, then the evaluation point.
    pub(crate) addresses: Vec<[SliceClaim<E>; 2]>,
    /// The increments at the two points.
    pub(crate) inc: [(Vec<E>, E); 2],
    /// The packed flags' slices at the two points.
    pub(crate) flag: Option<[SliceClaim<E>; 2]>,
    /// The advice's initial words at a point.
    pub(crate) advice: Option<(Vec<E>, E)>,
    /// RAM's image.
    pub(crate) image: Option<ImageClaim<E>>,
}

/// Why a log's argument refuses.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum MemoryError {
    #[error(transparent)]
    Transcript(#[from] TranscriptError),
    /// The read-write sumcheck does not end at the opened values.
    #[error("the read-write sumcheck does not close")]
    ReadWrite,
    /// The evaluation sumcheck does not end at the opened values.
    #[error("the evaluation sumcheck does not close")]
    Evaluation,
    /// An address column has a row of even weight.
    #[error("an address column has a row of even weight")]
    Parity,
    /// A row names a cell no region has.
    #[error("an address names no cell")]
    Unmapped,
}

#[cfg(test)]
mod tests {
    use super::*;
    use fiat_shamir::transcript::{ProverState, VerifierState};
    use primitives::multilinear::{eq_table, inner_product, mle_eval};
    use primitives::test_util::Rng;

    /// The registers' tuple: a flagged separator, the three register numbers around the position, the values.
    fn register_slots() -> Vec<Slot> {
        vec![
            Slot::Flagged {
                base: F64(8),
                delta: F64(24),
            },
            Slot::Address(0),
            Slot::Time,
            Slot::Address(1),
            Slot::Address(2),
            Slot::Read(0),
            Slot::Read(1),
            Slot::Written(2),
        ]
    }

    /// A random register file's log: reads of 33 cells, writes of 32, some rows flagged.
    fn registers(rng: &mut Rng, log_rows: usize, live: usize) -> (LogShape, LogWitness) {
        let mut regs = [0u64; CHUNK];
        let mut w = LogWitness {
            cells: vec![Vec::new(); 3],
            initial: vec![F64::ZERO; CHUNK],
            live,
            ..LogWitness::default()
        };
        for j in 0..1 << log_rows {
            let is_live = j < live;
            let (rd, flag) = if is_live {
                (1 + rng.below(32), rng.below(7) == 0)
            } else {
                (0, false)
            };
            let new = if is_live && !flag { rng.next_u64() } else { regs[rd] };
            let (r1, r2) = (rng.below(33), rng.below(33));
            w.cells[0].push(r1 as u32);
            w.cells[1].push(r2 as u32);
            w.cells[2].push(rd as u32);
            w.reads.push([regs[r1], regs[r2], regs[rd]]);
            w.inc.push(F64(std::mem::replace(&mut regs[rd], new) ^ new));
            w.flag.push(flag);
        }
        let outputs = vec![10, 17];
        let shape = LogShape {
            log_rows,
            slots: register_slots(),
            kind: Kind::Registers { outputs },
        };
        (shape, w)
    }

    /// A random memory log over RAM and the advice: a read, then a write, of either region.
    fn memory(
        rng: &mut Rng,
        log_rows: usize,
        live: usize,
        log_ram: usize,
        log_advice: usize,
    ) -> (LogShape, LogWitness) {
        let image: Vec<u64> = (0..1 << log_ram.saturating_sub(1)).map(|_| rng.next_u64()).collect();
        let regions = Regions::new([0x4000_0000, 0x2000_0000], log_ram, log_advice, &image);
        let mut initial = vec![F64::ZERO; CHUNK << regions.low];
        for (z, &x) in image.iter().enumerate() {
            initial[regions.ram.cell(z, regions.low)] = F64(x);
        }
        for z in 0..1 << log_advice {
            initial[regions.advice.cell(z, regions.low)] = F64(rng.next_u64());
        }
        let mut cells: Vec<u64> = initial.iter().map(|x| x.0).collect();
        let mut w = LogWitness {
            cells: vec![Vec::new()],
            initial,
            live,
            ..LogWitness::default()
        };
        for j in 0..1 << log_rows {
            let cell = match (j < live, rng.below(4)) {
                (false, _) => regions.ram.cell(0, regions.low),
                (true, 0) => regions.advice.cell(rng.below(1 << log_advice), regions.low),
                (true, _) => regions.ram.cell(rng.below(1 << log_ram), regions.low),
            };
            let new = if j < live && rng.below(2) == 0 {
                rng.next_u64()
            } else {
                cells[cell]
            };
            w.cells[0].push(cell as u32);
            w.reads.push([cells[cell], 0, 0]);
            w.inc.push(F64(std::mem::replace(&mut cells[cell], new) ^ new));
        }
        let slots = vec![
            Slot::Const(F64(2)),
            Slot::Address(0),
            Slot::Time,
            Slot::Read(0),
            Slot::Written(0),
        ];
        let shape = LogShape {
            log_rows,
            slots,
            kind: Kind::Memory(regions),
        };
        (shape, w)
    }

    /// Recompute each row's reads from the increments, after a test has changed them.
    fn replay_reads(shape: &LogShape, w: &mut LogWitness) {
        let mut cells: Vec<u64> = w.initial.iter().map(|x| x.0).collect();
        for j in 0..w.live {
            w.reads[j] = std::array::from_fn(|g| w.cells.get(g).map_or(0, |c| cells[c[j] as usize]));
            cells[w.cells[shape.write()][j] as usize] ^= w.inc[j].0;
        }
    }

    /// The output cells' values after the log's live rows.
    fn final_values(shape: &LogShape, w: &LogWitness) -> Vec<F192> {
        let Kind::Registers { outputs } = &shape.kind else {
            return Vec::new();
        };
        let mut regs = [0u64; CHUNK];
        for j in 0..w.live {
            regs[w.cells[2][j] as usize] ^= w.inc[j].0;
        }
        outputs.iter().map(|&cell| F192::from(F64(regs[cell]))).collect()
    }

    /// Prove and verify a log against a bus share, then settle what it leaves against the witness.
    ///
    /// `forge` alters the leaves the share is of, as a table pulling a tuple the log never pushed would.
    fn run(shape: &LogShape, w: &LogWitness, forge: impl FnOnce(&mut [F192], &[F192])) -> Result<(), MemoryError> {
        run_with(shape, w, &final_values(shape, w), forge)
    }

    /// Prove and verify a log against claimed outputs, its leaves forged by `forge`.
    fn run_with(
        shape: &LogShape,
        w: &LogWitness,
        outputs: &[F192],
        forge: impl FnOnce(&mut [F192], &[F192]),
    ) -> Result<(), MemoryError> {
        let mut rng = Rng::new(shape.log_rows as u64);
        let (weights, beta, point) = (rng.ext_vec(16), rng.ext(), rng.ext_vec(shape.log_rows));
        let mut leaves = leaves(shape, w, &weights, beta);
        forge(&mut leaves, &weights);
        let value = inner_product(&eq_table(&point), &leaves);
        let share = LinkShare {
            point,
            value,
            weights,
            beta,
        };

        let mut ps = ProverState::from_label(b"memory");
        let proven = prove(&mut ps, shape, w, &share);
        let proof = ps.into_proof();
        let mut vs = VerifierState::from_label(b"memory", &proof);
        let live = live_bits(w.live, shape.log_rows);
        let statement = Statement { live: &live, outputs };
        let opening = verify(&mut vs, shape, statement, &share)?;
        vs.finish()?;
        // Both sides leave the same claims on the commitment; the image's is the verifier's to derive.
        let committed = |o: &LogOpening<F192>| (o.addresses.clone(), o.inc.clone(), o.flag.clone(), o.advice.clone());
        assert_eq!(committed(&proven), committed(&opening));

        // The opening's claims, which a proof's commitment settles.
        for (g, c) in (0..shape.groups()).flat_map(|g| (0..shape.chunks()).map(move |c| (g, c))) {
            let mut words = vec![F64::ZERO; w.inc.len()];
            w.address_words(g, c, &mut words);
            for claim in &opening.addresses[g * shape.chunks() + c] {
                let eq = eq_table(&claim.suffix_point);
                for (k, &slice) in claim.s_hat_v.iter().enumerate() {
                    let bit: Vec<F64> = words.iter().map(|x| F64(x.0 >> k & 1)).collect();
                    assert_eq!(slice, mle_eval(&bit, &claim.suffix_point), "{eq:?}");
                }
            }
        }
        for (point, value) in &opening.inc {
            assert_eq!(mle_eval(&w.inc, point), *value);
        }
        // The program's claim on RAM's image, which a false evaluation makes false.
        match (&opening.image, &shape.kind) {
            (Some(image), Kind::Memory(regions)) if image.weight * regions.image.eval(&image.point) != image.value => {
                Err(MemoryError::Evaluation)
            }
            _ => Ok(()),
        }
    }

    #[test]
    fn an_honest_register_log_verifies() {
        let mut rng = Rng::new(1);
        for (log_rows, live) in [(7, 128), (13, 5000), (14, 1 << 14)] {
            let (shape, w) = registers(&mut rng, log_rows, live);
            run(&shape, &w, |_, _| {}).expect("an honest log verifies");
        }
    }

    #[test]
    fn an_honest_memory_log_verifies() {
        // Regions smaller and larger than a top-chunk value, and an advice region of one word.
        let mut rng = Rng::new(2);
        for (log_rows, live, log_ram, log_advice) in
            [(8, 200, 2, 0), (10, 1000, 9, 4), (13, 6000, 17, 14), (12, 4096, 13, 0)]
        {
            let (shape, w) = memory(&mut rng, log_rows, live, log_ram, log_advice);
            run(&shape, &w, |_, _| {}).expect("an honest log verifies");
        }
    }

    #[test]
    fn a_stale_read_is_refused() {
        // The table's tuple says row 100's first read returned one more than its cell held.
        //
        //     leaf = beta + sum_i w_i slot_i,   slot 5 = the first read
        let mut rng = Rng::new(3);
        let (shape, w) = registers(&mut rng, 10, 1000);
        let forge = |leaves: &mut [F192], weights: &[F192]| leaves[100] += weights[5];
        assert_eq!(run(&shape, &w, forge), Err(MemoryError::ReadWrite));
    }

    #[test]
    fn a_write_under_the_flag_is_refused() {
        let mut rng = Rng::new(5);
        let (shape, mut w) = registers(&mut rng, 9, 500);
        let j = w.flag.iter().position(|&f| f).expect("a flagged row");
        w.inc[j] = F64(1);
        replay_reads(&shape, &mut w);
        assert_eq!(run(&shape, &w, |_, _| {}), Err(MemoryError::Evaluation));
    }

    #[test]
    fn a_wrong_output_is_refused() {
        // The statement claims each output register one more than the log leaves in it.
        let mut rng = Rng::new(7);
        let (shape, w) = registers(&mut rng, 9, 500);
        let honest = final_values(&shape, &w);
        for i in 0..honest.len() {
            let mut outputs = honest.clone();
            outputs[i] += F192::ONE;
            assert_eq!(
                run_with(&shape, &w, &outputs, |_, _| {}),
                Err(MemoryError::Evaluation),
                "output {i}"
            );
        }
    }

    #[test]
    fn a_cell_of_no_region_is_refused() {
        // RAM of 2^13 words takes two top values, a four-word advice one: value 40 is no region's.
        let mut rng = Rng::new(9);
        let (shape, mut w) = memory(&mut rng, 10, 1000, 13, 2);
        let Kind::Memory(regions) = &shape.kind else {
            unreachable!()
        };
        w.cells[0][7] = (40 << regions.low) as u32;
        assert_eq!(run(&shape, &w, |_, _| {}), Err(MemoryError::Unmapped));

        // The advice's word 5 is past its four.
        let (shape, mut w) = memory(&mut rng, 10, 1000, 13, 2);
        let Kind::Memory(regions) = &shape.kind else {
            unreachable!()
        };
        w.cells[0][7] = regions.advice.cell(5, regions.low) as u32;
        assert_eq!(run(&shape, &w, |_, _| {}), Err(MemoryError::Evaluation));
    }
}
