//! Boolean circuits as gate lists over word ports: what [`crate::gadgets`] and the
//! VM's instruction classes are written in.
//!
//! ## Witness layout per block
//!
//! ```text
//!   z[0 .. 64·P)            = the ports, a whole number of 64-bit words each:
//!                             inputs (free), then outputs (committed copies)
//!   z[64·P]                 = 1                  (constant wire)
//!   z[64·P + 1 .. useful)   = the circuit's products, in the order they are made
//!   z[useful .. 2^k_log)    = padding (forced to 0 by empty rows)
//! ```
//!
//! A port bit with no gate is an empty row too, hence zero: an output narrower than
//! its words, a single bit say, is that value as a 64-bit word. A caller that binds
//! ports to something outside (memory words, in the VM) relies on exactly this.
//!
//! A circuit is one gate list, where a wire is the gate driving it and each
//! committed wire is a row. As in the BLAKE2s circuit, no matrix is ever built: the
//! verifier walks the list forwards and the prover backwards (doc/leanvm, Annex
//! C "Evaluating the matrices"). Across implementations what has to agree is the
//! port layout and the order products are made in, which fixes their slots; the
//! order of the free XORs is nobody's business.

use primitives::PrimeCharacteristicRing;

use crate::lincheck::LincheckCircuit;
use crate::reduction::Block;
use crate::witness::{
    GroupTables, Tables, Witness, drive_witness_batched, drive_witness_groups, drive_witness_packed_and_lincheck,
    with_z,
};
use primitives::F192;
use primitives::bits::transpose_64x64;
use std::ops::Range;

/// Instances one word-wide walk of the gate list computes.
///
/// One per bit of a `u64`, so a gate is one word operation for all of them.
const LANES: usize = 64;

/// The gate driving a wire, or `None` for a structural zero.
pub type Wire = Option<u32>;

#[derive(Clone, Copy)]
enum Gate {
    /// The committed free wire at `slot`: an input bit, or the constant. Row `z[slot]·1 = z[slot]`.
    Free(u32),
    /// `w_x ⊕ w_y`, uncommitted.
    Xor(u32, u32),
    /// Row `w_x · w_y = z[slot]`.
    And(u32, u32, u32),
    /// Row `w_x · 1 = z[slot]`: an affine wire committed, which is how a result leaves the circuit.
    Copy(u32, u32),
}

/// A gate list under construction.
pub struct Builder {
    gates: Vec<Gate>,
    next_slot: usize,
    one: Wire,
    inputs: Vec<Vec<Wire>>,
    /// Each output port's first bit and width.
    outputs: Vec<(usize, usize)>,
    n_input_words: usize,
}

impl Builder {
    /// Ports of the given widths in bits, each rounded up to whole words: the inputs,
    /// whose bits are free wires, then the outputs.
    pub fn new(input_bits: &[usize], output_bits: &[usize]) -> Self {
        let inputs: Vec<Range<usize>> = input_bits.iter().map(|&bits| 0..bits).collect();
        Self::with_input_ranges(&inputs, output_bits)
    }

    /// Ports as above, each input port given as the range of its free bits, and as wide as the range's end.
    ///
    /// An input bit below its range is a structural zero: its empty row forces it to zero.
    pub fn with_input_ranges(inputs: &[Range<usize>], output_bits: &[usize]) -> Self {
        let input_bits: Vec<usize> = inputs.iter().map(|bits| bits.end).collect();
        let words = |bits: &[usize]| bits.iter().map(|b| b.div_ceil(64)).sum::<usize>();
        let n_input_words = words(&input_bits);
        let const_pos = 64 * (n_input_words + words(output_bits));
        let mut c = Self {
            gates: Vec::new(),
            next_slot: const_pos + 1,
            one: None,
            inputs: Vec::new(),
            outputs: Vec::new(),
            n_input_words,
        };
        c.one = Some(c.push(Gate::Free(const_pos as u32)));
        let mut base = 0;
        for bits in inputs {
            let wires = (0..bits.end)
                .map(|i| bits.contains(&i).then(|| c.push(Gate::Free((base + i) as u32))))
                .collect();
            c.inputs.push(wires);
            base += 64 * bits.end.div_ceil(64);
        }
        for &bits in output_bits {
            c.outputs.push((base, bits));
            base += 64 * bits.div_ceil(64);
        }
        c
    }

    fn push(&mut self, gate: Gate) -> u32 {
        self.gates.push(gate);
        (self.gates.len() - 1) as u32
    }

    /// The constant 1.
    pub const fn one(&self) -> Wire {
        self.one
    }

    /// Input port `port`'s bits, low first.
    pub fn input(&self, port: usize) -> Vec<Wire> {
        self.inputs[port].clone()
    }

    /// The slot the next product takes.
    pub const fn next_slot(&self) -> usize {
        self.next_slot
    }

    pub fn xor(&mut self, x: Wire, y: Wire) -> Wire {
        match (x, y) {
            (Some(x), Some(y)) => Some(self.push(Gate::Xor(x, y))),
            _ => x.or(y),
        }
    }

    pub fn not(&mut self, x: Wire) -> Wire {
        self.xor(x, self.one)
    }

    /// One product, and one slot, unless an operand is a structural zero.
    pub fn and(&mut self, x: Wire, y: Wire) -> Wire {
        let (x, y) = (x?, y?);
        let slot = self.next_slot as u32;
        self.next_slot += 1;
        Some(self.push(Gate::And(x, y, slot)))
    }

    pub fn or(&mut self, x: Wire, y: Wire) -> Wire {
        let both = self.and(x, y);
        let either = self.xor(x, y);
        self.xor(either, both)
    }

    /// `if s { x } else { y }`, one product.
    pub fn mux(&mut self, s: Wire, x: Wire, y: Wire) -> Wire {
        let d = self.xor(x, y);
        let picked = self.and(s, d);
        self.xor(picked, y)
    }

    /// Commits `wire` as bit `bit` of output port `port`. A structural zero needs no
    /// gate: the empty row is what forces the bit to zero.
    pub fn output(&mut self, port: usize, bit: usize, wire: Wire) {
        let slot = self.output_slot(port, bit);
        if let Some(wire) = wire {
            self.push(Gate::Copy(wire, slot));
        }
    }

    /// One product, committed as bit `bit` of output port `port` rather than at the next slot.
    ///
    /// The port bit is the product's row, so the output costs no copy.
    pub fn and_output(&mut self, port: usize, bit: usize, x: Wire, y: Wire) -> Wire {
        let slot = self.output_slot(port, bit);
        let (x, y) = (x?, y?);
        Some(self.push(Gate::And(x, y, slot)))
    }

    fn output_slot(&self, port: usize, bit: usize) -> u32 {
        let (base, bits) = self.outputs[port];
        assert!(bit < bits, "output port {port} has {bits} bits");
        (base + bit) as u32
    }

    pub fn finish(self) -> Circuit {
        let useful_bits = self.next_slot;
        Circuit {
            const_pos: 64 * (self.n_input_words + self.outputs.iter().map(|o| o.1.div_ceil(64)).sum::<usize>()),
            k_log: useful_bits.next_power_of_two().trailing_zeros() as usize,
            useful_bits,
            n_input_words: self.n_input_words,
            gates: self.gates,
        }
    }
}

pub struct Circuit {
    gates: Vec<Gate>,
    const_pos: usize,
    k_log: usize,
    useful_bits: usize,
    n_input_words: usize,
}

impl Circuit {
    /// `log2` of the bits one instance occupies.
    pub const fn k_log(&self) -> usize {
        self.k_log
    }

    /// The bits of an instance that carry data; the rest are zero.
    #[cfg(any(test, feature = "bench"))]
    pub const fn useful_bits(&self) -> usize {
        self.useful_bits
    }

    /// The constant wire's position.
    pub const fn const_pos(&self) -> usize {
        self.const_pos
    }

    pub const fn n_input_words(&self) -> usize {
        self.n_input_words
    }

    pub fn block(&self) -> Block<'_> {
        Block {
            k_log: self.k_log,
            useful_bits: self.useful_bits,
            circuit: self,
        }
    }

    /// One instance's `z`, `A·z` and `B·z`, by one walk of the gate list on bits.
    /// `inputs` are the input ports' words; the buffers come zeroed.
    pub fn witness_instance(&self, inputs: &[u64], z: &mut [u64], az: &mut [u64], bz: &mut [u64]) {
        assert_eq!(inputs.len(), self.n_input_words);
        let set = |buf: &mut [u64], slot: u32, v: bool| buf[slot as usize / 64] |= (v as u64) << (slot % 64);
        let mut wires: Vec<bool> = Vec::with_capacity(self.gates.len());
        for &gate in &self.gates {
            let v = match gate {
                Gate::Free(s) => {
                    let v = s as usize == self.const_pos || (inputs[s as usize / 64] >> (s % 64)) & 1 == 1;
                    set(z, s, v);
                    set(az, s, v);
                    set(bz, s, true);
                    v
                }
                Gate::Xor(x, y) => wires[x as usize] ^ wires[y as usize],
                Gate::And(x, y, s) => {
                    let (x, y) = (wires[x as usize], wires[y as usize]);
                    set(z, s, x & y);
                    set(az, s, x);
                    set(bz, s, y);
                    x & y
                }
                Gate::Copy(x, s) => {
                    let v = wires[x as usize];
                    set(z, s, v);
                    set(az, s, v);
                    set(bz, s, true);
                    v
                }
            };
            wires.push(v);
        }
    }

    /// Walks the gate list once for 64 instances, bit `l` of every word being instance `l`.
    ///
    /// ```text
    ///     Xor(x, y)      wire = x ^ y
    ///     And(x, y, s)   wire = x & y     z[s] = x & y    A·z[s] = x    B·z[s] = y
    /// ```
    ///
    /// Reads the input bits by slot and writes `z`, `A·z` and `B·z` by slot.
    ///
    /// A slot no gate drives is never written, so it keeps the zero the scratch starts with.
    fn walk_lanes(&self, lanes: &mut Lanes) {
        let Lanes {
            inputs, wires, z, a, b, ..
        } = lanes;
        // Wire `i` is gate `i`'s value, pushed in gate order.
        wires.clear();
        for &gate in &self.gates {
            let v = match gate {
                // An input bit or the constant: its row is `z[s] · 1 = z[s]`.
                Gate::Free(s) => {
                    let s = s as usize;
                    let v = if s == self.const_pos { u64::MAX } else { inputs[s] };
                    (z[s], a[s], b[s]) = (v, v, u64::MAX);
                    v
                }
                // Free in the R1CS: no row, no slot.
                Gate::Xor(x, y) => wires[x as usize] ^ wires[y as usize],
                // A product: its row is `x · y = z[s]`.
                Gate::And(x, y, s) => {
                    let (x, y) = (wires[x as usize], wires[y as usize]);
                    let s = s as usize;
                    (z[s], a[s], b[s]) = (x & y, x, y);
                    x & y
                }
                // A committed copy of an affine wire: its row is `x · 1 = z[s]`.
                Gate::Copy(x, s) => {
                    let v = wires[x as usize];
                    let s = s as usize;
                    (z[s], a[s], b[s]) = (v, v, u64::MAX);
                    v
                }
            };
            wires.push(v);
        }
    }

    /// The witness of `rows` of input words, padded with all-zero inputs to `2^n_blocks_log` instances.
    #[cfg(any(test, feature = "bench"))]
    pub fn generate_witness<const N: usize>(&self, rows: &[[u64; N]], n_blocks_log: usize) -> Witness {
        assert_eq!(N, self.n_input_words);
        self.generate_witness_from(rows, &[0; N], n_blocks_log, |row, words| words.copy_from_slice(row))
    }

    /// The same tables for the caller's own rows.
    ///
    /// - `input_words(row, words)` writes a row's input port words.
    /// - `padding` fills the instances past the rows.
    ///
    /// The gate list is walked for 64 instances at a time.
    ///
    /// The tables are bit for bit those of the one-instance walk.
    ///
    /// ```text
    ///     rows ──transpose──▶ input bits by slot ──walk──▶ z, A·z, B·z by slot
    ///                                                     │
    ///          ◀──transpose── instance-major tables ◀─────┤
    ///          ◀──byte q──── stripe of instances 8q..8q+8 ┘
    /// ```
    pub fn generate_witness_from<S: Sync>(
        &self,
        rows: &[S],
        padding: &S,
        n_blocks_log: usize,
        input_words: impl Fn(&S, &mut [u64]) + Sync,
    ) -> Witness {
        with_z(n_blocks_log, self.k_log, |z| {
            self.generate_witness_from_into(z, rows, padding, n_blocks_log, input_words, |_, _| {})
        })
    }

    /// [`Self::generate_witness_from`] with `z` written into the caller's buffer, and `check(row, z)` shown each
    /// instance's `z` words while they are in cache.
    pub fn generate_witness_from_into<S: Sync>(
        &self,
        z: &mut [u64],
        rows: &[S],
        padding: &S,
        n_blocks_log: usize,
        input_words: impl Fn(&S, &mut [u64]) + Sync,
        check: impl Fn(&S, &[u64]) + Sync,
    ) -> Tables {
        assert!(rows.len() <= 1 << n_blocks_log, "more rows than instances");
        // A batch below 64 instances is walked in full and stored in part.
        let lanes = LANES.min(1 << n_blocks_log);
        let n_in = self.n_input_words;
        // Packed words per instance.
        let words = (1usize << self.k_log) / 64;
        // Slot groups past the useful bits hold only zeros, so they skip the transpose.
        let live_words = self.useful_bits.div_ceil(64);
        drive_witness_groups(
            z,
            n_blocks_log,
            self.k_log,
            lanes,
            || Lanes::new(self),
            |s: &mut Lanes, first: usize, t: GroupTables<'_>| {
                // Phase 1: each lane's input words, a padding row past the batch's rows.
                for (l, row_words) in s.rows.chunks_exact_mut(n_in).enumerate() {
                    input_words(rows.get(first + l).unwrap_or(padding), row_words);
                }

                // Phase 2: input word `w` of 64 lanes, transposed, is its 64 bits by slot.
                //
                //     before: bits[l] = input word w of lane l
                //     after:  bits[i] = bit i of input word w, one bit per lane
                for (w, bits) in s.inputs.as_chunks_mut::<LANES>().0.iter_mut().enumerate() {
                    *bits = std::array::from_fn(|l| s.rows[l * n_in + w]);
                    transpose_64x64(bits);
                }

                // Phase 3: the gate list, once for all 64 lanes.
                self.walk_lanes(s);

                // Phase 4: back to instance-major, one transpose per 64-slot group.
                //
                //     before: m[i] = slot 64g + i of every lane
                //     after:  m[l] = packed word g of lane l
                for (by_slot, out) in [(&s.z, &mut *t.z), (&s.a, &mut *t.a), (&s.b, &mut *t.b)] {
                    for g in 0..words {
                        let mut m = [0u64; LANES];
                        if g < live_words {
                            m.copy_from_slice(&by_slot[g * LANES..(g + 1) * LANES]);
                            transpose_64x64(&mut m);
                        }
                        for (l, &word) in m[..lanes].iter().enumerate() {
                            out[l * words + g] = word;
                        }
                    }
                }

                // Phase 5: lincheck's stripes, straight from the slot words.
                //
                // The stripe of instances 8q..8q+8 holds slot s of instance 8q+x at byte s, bit x.
                // That byte is byte q of slot s's word.
                let k = words * 64;
                for (q, stripe) in t.stripes.chunks_exact_mut(k).enumerate() {
                    for (byte, &word) in stripe.iter_mut().zip(&s.z) {
                        *byte = (word >> (8 * q)) as u8;
                    }
                }
            },
            |i, z| check(rows.get(i).unwrap_or(padding), z),
        )
    }

    /// The walk's tables with the caller's own rows, padding row and way to
    /// fill an instance, for a circuit whose witness is cheaper as word arithmetic.
    pub fn generate_witness_with<S: Sync>(
        &self,
        rows: &[S],
        padding: &S,
        n_blocks_log: usize,
        instance: impl Fn(&S, &mut [u64], &mut [u64], &mut [u64]) + Sync,
    ) -> Witness {
        with_z(n_blocks_log, self.k_log, |z| {
            self.generate_witness_with_into(z, rows, padding, n_blocks_log, instance, |_, _| {})
        })
    }

    /// [`Self::generate_witness_with`] with `z` written into the caller's buffer, and `check(row, z)` shown each
    /// instance's `z` words while they are in cache.
    pub fn generate_witness_with_into<S: Sync>(
        &self,
        z: &mut [u64],
        rows: &[S],
        padding: &S,
        n_blocks_log: usize,
        instance: impl Fn(&S, &mut [u64], &mut [u64], &mut [u64]) + Sync,
        check: impl Fn(&S, &[u64]) + Sync,
    ) -> Tables {
        drive_witness_packed_and_lincheck(z, rows, Some(padding), n_blocks_log, self.k_log, instance, |i, z| {
            check(rows.get(i).unwrap_or(padding), z);
        })
    }

    /// Build native witnesses eight instances at a time.
    ///
    /// The callback fills three zeroed instance-major buffers for each group.
    pub fn generate_witness_batched<S: Sync>(
        &self,
        rows: &[S],
        padding: &S,
        n_blocks_log: usize,
        batch: impl Fn([&S; 8], &mut [u64], &mut [u64], &mut [u64]) + Sync,
    ) -> Witness {
        with_z(n_blocks_log, self.k_log, |z| {
            self.generate_witness_batched_into(z, rows, padding, n_blocks_log, batch, |_, _| {})
        })
    }

    /// [`Self::generate_witness_batched`] with `z` written into the caller's buffer, and `check(row, z)` shown each
    /// instance's `z` words while they are in cache.
    pub fn generate_witness_batched_into<S: Sync>(
        &self,
        z: &mut [u64],
        rows: &[S],
        padding: &S,
        n_blocks_log: usize,
        batch: impl Fn([&S; 8], &mut [u64], &mut [u64], &mut [u64]) + Sync,
        check: impl Fn(&S, &[u64]) + Sync,
    ) -> Tables {
        // Eight adjacent instances occupy one lincheck byte stripe.
        drive_witness_batched(z, rows, padding, n_blocks_log, self.k_log, batch, |i, z| {
            check(rows.get(i).unwrap_or(padding), z);
        })
    }

    /// The matrix-vector products `(A_0 w, B_0 w)`, by one forward walk.
    pub fn row_values(&self, w: &[F192]) -> (Vec<F192>, Vec<F192>) {
        let k = self.n_cols();
        assert_eq!(w.len(), k);
        let wc = w[self.const_pos];
        let mut ra = vec![F192::ZERO; k];
        let mut rb = vec![F192::ZERO; k];
        let mut wires: Vec<F192> = Vec::with_capacity(self.gates.len());
        for &gate in &self.gates {
            let v = match gate {
                Gate::Free(s) => {
                    let s = s as usize;
                    (ra[s], rb[s]) = (w[s], wc);
                    w[s]
                }
                Gate::Xor(x, y) => wires[x as usize] + wires[y as usize],
                Gate::And(x, y, s) => {
                    let s = s as usize;
                    (ra[s], rb[s]) = (wires[x as usize], wires[y as usize]);
                    w[s]
                }
                Gate::Copy(x, s) => {
                    let s = s as usize;
                    (ra[s], rb[s]) = (wires[x as usize], wc);
                    w[s]
                }
            };
            wires.push(v);
        }
        (ra, rb)
    }
}

/// One worker's scratch for the 64-instance walk.
///
/// Bit `l` of every word is instance `l`.
struct Lanes {
    /// The 64 instances' input port words, one row after another.
    rows: Vec<u64>,
    /// The input ports' bits, by slot.
    inputs: Vec<u64>,
    /// Every gate's value, in gate order.
    wires: Vec<u64>,
    /// `z` by slot, one word per slot of an instance.
    z: Vec<u64>,
    /// `A·z` by slot.
    a: Vec<u64>,
    /// `B·z` by slot.
    b: Vec<u64>,
}

impl Lanes {
    /// Zeroed scratch sized for one circuit.
    fn new(circuit: &Circuit) -> Self {
        // One word per slot of an instance.
        let slots = 1 << circuit.k_log;
        Self {
            rows: vec![0; LANES * circuit.n_input_words],
            inputs: vec![0; LANES * circuit.n_input_words],
            wires: Vec::with_capacity(circuit.gates.len()),
            z: vec![0; slots],
            a: vec![0; slots],
            b: vec![0; slots],
        }
    }
}

impl LincheckCircuit for Circuit {
    fn n_cols(&self) -> usize {
        1 << self.k_log
    }

    fn const_pin_col(&self) -> usize {
        self.const_pos
    }

    /// `(A_0 + α B_0)ᵀ u`, by one backward walk: every gate, in reverse, hands
    /// its wire's adjoint to its operands or deposits it on its slot.
    fn fold_alpha_batched(&self, alpha: F192, u: &[F192]) -> Vec<F192> {
        assert_eq!(u.len(), self.n_cols());
        let c = self.const_pos;
        let mut m = vec![F192::ZERO; u.len()];
        let mut adj = vec![F192::ZERO; self.gates.len()];
        for (i, &gate) in self.gates.iter().enumerate().rev() {
            let g = adj[i];
            match gate {
                Gate::Free(s) => {
                    let s = s as usize;
                    m[s] += g + u[s];
                    m[c] += alpha * u[s];
                }
                Gate::Xor(x, y) => {
                    adj[x as usize] += g;
                    adj[y as usize] += g;
                }
                Gate::And(x, y, s) => {
                    let s = s as usize;
                    m[s] += g;
                    adj[x as usize] += u[s];
                    adj[y as usize] += alpha * u[s];
                }
                Gate::Copy(x, s) => {
                    let s = s as usize;
                    m[s] += g;
                    adj[x as usize] += u[s];
                    m[c] += alpha * u[s];
                }
            }
        }
        m
    }

    fn bilinear_form(&self, alpha: F192, u: &[F192], w: &[F192]) -> Option<F192> {
        let (ra, rb) = self.row_values(w);
        Some(
            u.iter()
                .zip(ra.iter().zip(&rb))
                .fold(F192::ZERO, |acc, (&u, (&a, &b))| acc + u * (a + alpha * b)),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use primitives::test_util::Rng;

    /// A random circuit over the builder's whole vocabulary.
    ///
    /// A narrow input port and an undriven output bit are structural zeros.
    fn random_circuit(rng: &mut Rng) -> Circuit {
        // Ports: three input words, one of them narrow, and two outputs.
        let narrow = 1 + (rng.next_u32() % 63) as usize;
        let mut c = Builder::new(&[64, narrow, 64], &[64, narrow]);

        // Operands to draw from: every input bit, a structural zero and the constant.
        let mut pool: Vec<Wire> = (0..3).flat_map(|port| c.input(port)).collect();
        pool.extend([None, c.one()]);

        // 200 to 1000 random gates, each result an operand for the next.
        for _ in 0..200 + rng.next_u32() % 800 {
            let mut pick = || pool[rng.next_u32() as usize % pool.len()];
            let (s, x, y) = (pick(), pick(), pick());
            let wire = match rng.next_u32() % 5 {
                0 => c.xor(x, y),
                1 => c.and(x, y),
                2 => c.or(x, y),
                3 => c.mux(s, x, y),
                _ => c.not(x),
            };
            pool.push(wire);
        }
        // Drive about half the output bits, by a copy or by a product, leaving the rest structural zeros.
        for (port, bits) in [(0, 64), (1, narrow)] {
            for bit in 0..bits {
                let kind = rng.next_u32() % 4;
                let mut pick = || pool[rng.next_u32() as usize % pool.len()];
                match kind {
                    0 | 1 => {}
                    2 => c.output(port, bit, pick()),
                    _ => {
                        let (x, y) = (pick(), pick());
                        c.and_output(port, bit, x, y);
                    }
                }
            }
        }
        c.finish()
    }

    #[test]
    fn bitsliced_witness_is_the_gate_walk() {
        // Invariant: the 64-lane walk writes the four tables the one-instance walk writes.
        let mut rng = Rng::new(0xB175);
        for round in 0..40 {
            let circuit = random_circuit(&mut rng);

            // Fixture state: batches of 8, 16, 32, 64 and 128 instances.
            //
            //     8 to 32   one walk, stored in part
            //     64        one walk, stored in full
            //     128       two walks
            let n_log = 3 + round % 5;

            // Up to 6 instances past the rows take the padding row.
            let n_rows = (1 << n_log) - (round % 3) * 3;
            let mut row = || -> [u64; 3] { std::array::from_fn(|_| rng.next_u64()) };
            let rows: Vec<[u64; 3]> = (0..n_rows).map(|_| row()).collect();
            let padding = row();

            // The same batch through both generators, every table compared.
            let walk = circuit.generate_witness_with(&rows, &padding, n_log, |row, z, az, bz| {
                circuit.witness_instance(row, z, az, bz);
            });
            let sliced = circuit.generate_witness_from(&rows, &padding, n_log, |row, words| words.copy_from_slice(row));
            assert!(walk.z == sliced.z, "z, round {round}");
            assert!(walk.az == sliced.az, "A·z, round {round}");
            assert!(walk.bz == sliced.bz, "B·z, round {round}");
            assert!(walk.stripes == sliced.stripes, "lincheck stripes, round {round}");
        }
    }
}
