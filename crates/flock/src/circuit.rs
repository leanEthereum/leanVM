//! Boolean circuits as gate lists over word ports: the language of the gadgets and of the VM's instruction classes.
//!
//! One instance's witness, `2^k_log` bits:
//!
//! ```text
//!     z[0 .. 64 P)              the ports, whole 64-bit words each: inputs (free), then outputs (committed copies)
//!     z[64 P]                   1, the constant wire
//!     z[64 P + 1 .. useful)     the products, in the order they are made
//!     z[useful .. 2^k_log)      zero padding, forced by empty rows
//! ```
//!
//! A port bit no gate drives is an empty row too, hence zero.
//! So an output narrower than its words, a single bit say, is that value as a 64-bit word.
//! A caller binding ports to something outside, memory words in the VM, relies on exactly this.
//!
//! Each committed wire is one constraint row `a * b = z`.
//! No matrix is ever built: the verifier walks the list forwards and the prover backwards (doc/leanvm, Annex C).
//!
//! What two implementations must agree on is the port layout and the order products are made in.
//! The order of the free XORs is nobody's business.

use std::ops::Range;

use primitives::bits::transpose_64x64;
use primitives::field::F192;

use crate::lincheck::LincheckCircuit;
use crate::reduction::Block;
use crate::witness::{Batch, GroupTables, Tables, Witness};

/// Instances one word-wide walk of the gate list computes: one per bit of a word.
const LANES: usize = 64;

/// A bit of a circuit: the output of one gate, or the structural zero.
///
/// The zero has no gate.
///
/// Its empty constraint row forces it to 0, so it costs nothing.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Wire(Option<GateId>);

impl Wire {
    /// The structural zero.
    pub const ZERO: Self = Self(None);

    /// The constant one.
    ///
    /// Every circuit makes its constant first, so it is always the first gate.
    pub const ONE: Self = Self(Some(GateId(0)));

    /// The constant 0 or 1.
    pub const fn constant(bit: bool) -> Self {
        if bit { Self::ONE } else { Self::ZERO }
    }

    /// Whether this is the structural zero.
    pub const fn is_zero(self) -> bool {
        self.0.is_none()
    }
}

/// The position of a gate in the list.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct GateId(u32);

impl GateId {
    /// The position as an index into a per-gate table.
    const fn index(self) -> usize {
        self.0 as usize
    }
}

/// The position of a committed bit in an instance's witness.
#[derive(Clone, Copy, Debug)]
struct Slot(u32);

impl Slot {
    /// A slot from its position in the witness.
    ///
    /// # Panics
    ///
    /// Panics if the position does not fit in 32 bits.
    fn new(position: usize) -> Self {
        Self(u32::try_from(position).expect("a slot fits in 32 bits"))
    }

    /// The position as an index into the witness.
    const fn index(self) -> usize {
        self.0 as usize
    }
}

/// One gate of the list.
#[derive(Clone, Copy, Debug)]
enum Gate {
    /// A committed free bit: an input bit, or the constant.
    ///
    /// Its row is `z[slot] * 1 = z[slot]`.
    Free(Slot),

    /// The sum of two gates, uncommitted: no row.
    Xor(GateId, GateId),

    /// The product of two gates, committed at a slot.
    ///
    /// Its row is `x * y = z[slot]`.
    And(GateId, GateId, Slot),

    /// An affine bit committed at a slot, which is how a result leaves the circuit.
    ///
    /// Its row is `x * 1 = z[slot]`.
    Copy(GateId, Slot),
}

/// A gate list under construction.
#[derive(Debug)]
pub struct Builder {
    /// The gates so far, in order.
    gates: Vec<Gate>,
    /// The slot the next product takes.
    next_slot: usize,
    /// Each input port's wires, low bit first.
    inputs: Vec<Vec<Wire>>,
    /// Each output port's first slot and width in bits.
    outputs: Vec<(usize, usize)>,
    /// Words the input ports span.
    n_input_words: usize,
}

impl Builder {
    /// A circuit with input and output ports of the given widths in bits, each rounded up to whole words.
    ///
    /// Every input bit is a free wire.
    pub fn new(input_bits: &[usize], output_bits: &[usize]) -> Self {
        let inputs: Vec<Range<usize>> = input_bits.iter().map(|&bits| 0..bits).collect();
        Self::with_input_ranges(&inputs, output_bits)
    }

    /// The same, each input port given as the range of its free bits, and as wide as the range's end.
    ///
    /// An input bit below its range is a structural zero: its empty row forces it to zero.
    pub fn with_input_ranges(inputs: &[Range<usize>], output_bits: &[usize]) -> Self {
        // The constant sits right after the ports.
        let words = |bits: &mut dyn Iterator<Item = usize>| bits.map(|b| b.div_ceil(64)).sum::<usize>();
        let n_input_words = words(&mut inputs.iter().map(|bits| bits.end));
        let const_pos = 64 * (n_input_words + words(&mut output_bits.iter().copied()));

        // The constant is the first gate, which is what makes it the one wire.
        let mut c = Self {
            gates: vec![Gate::Free(Slot::new(const_pos))],
            next_slot: const_pos + 1,
            inputs: Vec::new(),
            outputs: Vec::new(),
            n_input_words,
        };

        // Each input port: a free wire per bit of its range, a structural zero below it.
        let mut base = 0;
        for bits in inputs {
            let wires = (0..bits.end)
                .map(|i| {
                    if bits.contains(&i) {
                        c.push(Gate::Free(Slot::new(base + i)))
                    } else {
                        Wire::ZERO
                    }
                })
                .collect();
            c.inputs.push(wires);
            base += 64 * bits.end.div_ceil(64);
        }

        // Each output port: its slots, which gates fill later.
        for &bits in output_bits {
            c.outputs.push((base, bits));
            base += 64 * bits.div_ceil(64);
        }
        c
    }

    /// Append a gate, returning its wire.
    fn push(&mut self, gate: Gate) -> Wire {
        let id = u32::try_from(self.gates.len()).expect("a gate list fits in 32 bits");
        self.gates.push(gate);
        Wire(Some(GateId(id)))
    }

    /// Take the next product slot.
    fn take_slot(&mut self) -> Slot {
        let slot = Slot::new(self.next_slot);
        self.next_slot += 1;
        slot
    }

    /// An input port's wires, low bit first.
    pub fn input(&self, port: usize) -> Vec<Wire> {
        self.inputs[port].clone()
    }

    /// The slot the next product takes.
    pub const fn next_slot(&self) -> usize {
        self.next_slot
    }

    /// `x + y`: free, no slot.
    pub fn xor(&mut self, x: Wire, y: Wire) -> Wire {
        match (x.0, y.0) {
            (Some(a), Some(b)) => self.push(Gate::Xor(a, b)),
            // Adding the zero leaves the other wire.
            (None, _) => y,
            (_, None) => x,
        }
    }

    /// `1 + x`: free, no slot.
    pub fn not(&mut self, x: Wire) -> Wire {
        self.xor(x, Wire::ONE)
    }

    /// `x * y`: one product and one slot, unless an operand is the zero.
    pub fn and(&mut self, x: Wire, y: Wire) -> Wire {
        let (Some(x), Some(y)) = (x.0, y.0) else {
            return Wire::ZERO;
        };
        let slot = self.take_slot();
        self.push(Gate::And(x, y, slot))
    }

    /// `x OR y = x + y + x y`: one product.
    pub fn or(&mut self, x: Wire, y: Wire) -> Wire {
        let both = self.and(x, y);
        let either = self.xor(x, y);
        self.xor(either, both)
    }

    /// `if s { x } else { y } = y + s (x + y)`: one product.
    pub fn mux(&mut self, s: Wire, x: Wire, y: Wire) -> Wire {
        let d = self.xor(x, y);
        let picked = self.and(s, d);
        self.xor(picked, y)
    }

    /// Commit `wire` as bit `bit` of output port `port`.
    ///
    /// The zero needs no gate: its empty row forces the bit to zero.
    pub fn output(&mut self, port: usize, bit: usize, wire: Wire) {
        let slot = self.output_slot(port, bit);
        if let Some(x) = wire.0 {
            self.push(Gate::Copy(x, slot));
        }
    }

    /// `x * y`, committed as bit `bit` of output port `port` rather than at the next slot.
    ///
    /// The port bit is the product's row, so the output costs no copy.
    pub fn and_output(&mut self, port: usize, bit: usize, x: Wire, y: Wire) -> Wire {
        let slot = self.output_slot(port, bit);
        let (Some(x), Some(y)) = (x.0, y.0) else {
            return Wire::ZERO;
        };
        self.push(Gate::And(x, y, slot))
    }

    /// The slot of bit `bit` of output port `port`.
    fn output_slot(&self, port: usize, bit: usize) -> Slot {
        let (base, bits) = self.outputs[port];
        assert!(bit < bits, "output port {port} has {bits} bits");
        Slot::new(base + bit)
    }

    /// The finished circuit, its instances padded to the next power of two.
    pub fn finish(self) -> Circuit {
        // Every slot so far is a port, the constant or a product; the rest of the power of two is padding.
        let useful_bits = self.next_slot;
        let output_words: usize = self.outputs.iter().map(|&(_, bits)| bits.div_ceil(64)).sum();
        Circuit {
            const_pos: 64 * (self.n_input_words + output_words),
            k_log: useful_bits.next_power_of_two().trailing_zeros() as usize,
            useful_bits,
            n_input_words: self.n_input_words,
            gates: self.gates,
        }
    }
}

/// A finished gate list: an R1CS over GF(2) whose matrices are never built.
#[derive(Debug)]
pub struct Circuit {
    /// The gates, in order; a gate's index is its wire.
    gates: Vec<Gate>,
    /// The constant wire's slot.
    const_pos: usize,
    /// The base-two logarithm of the bits per instance.
    k_log: usize,
    /// The slots before the zero padding.
    useful_bits: usize,
    /// Words the input ports span.
    n_input_words: usize,
}

impl Circuit {
    /// The base-two logarithm of the bits one instance occupies.
    pub const fn k_log(&self) -> usize {
        self.k_log
    }

    /// The bits of an instance that carry data; the rest are zero.
    pub const fn useful_bits(&self) -> usize {
        self.useful_bits
    }

    /// The constant wire's slot.
    pub const fn const_pos(&self) -> usize {
        self.const_pos
    }

    /// Words the input ports span.
    pub const fn n_input_words(&self) -> usize {
        self.n_input_words
    }

    /// The circuit as the reduction sees it.
    pub fn block(&self) -> Block<'_> {
        Block {
            k_log: self.k_log,
            useful_bits: self.useful_bits,
            circuit: self,
        }
    }

    /// One instance's `z`, `A z` and `B z`, by one walk of the gate list on bits.
    ///
    /// It is the reference every generator is pinned to.
    ///
    /// `inputs` are the input ports' words, and the three buffers come zeroed.
    pub fn witness_instance(&self, inputs: &[u64], z: &mut [u64], az: &mut [u64], bz: &mut [u64]) {
        assert_eq!(inputs.len(), self.n_input_words);
        let set = |buf: &mut [u64], slot: Slot, v: bool| {
            let i = slot.index();
            buf[i / 64] |= u64::from(v) << (i % 64);
        };
        // Wire `i` is gate `i`'s value.
        let mut wires: Vec<bool> = Vec::with_capacity(self.gates.len());
        for &gate in &self.gates {
            let v = match gate {
                // An input bit or the constant: `z * 1 = z`.
                Gate::Free(s) => {
                    let i = s.index();
                    let v = i == self.const_pos || (inputs[i / 64] >> (i % 64)) & 1 == 1;
                    set(z, s, v);
                    set(az, s, v);
                    set(bz, s, true);
                    v
                }
                // Free: no row.
                Gate::Xor(x, y) => wires[x.index()] ^ wires[y.index()],
                // A product: `x * y = z`.
                Gate::And(x, y, s) => {
                    let (x, y) = (wires[x.index()], wires[y.index()]);
                    set(z, s, x & y);
                    set(az, s, x);
                    set(bz, s, y);
                    x & y
                }
                // A committed copy: `x * 1 = z`.
                Gate::Copy(x, s) => {
                    let v = wires[x.index()];
                    set(z, s, v);
                    set(az, s, v);
                    set(bz, s, true);
                    v
                }
            };
            wires.push(v);
        }
    }

    /// Walk the gate list once for 64 instances, bit `l` of every word being instance `l`.
    ///
    /// ```text
    ///     Xor(x, y)      wire = x ^ y
    ///     And(x, y, s)   wire = x & y     z[s] = x & y    A z[s] = x    B z[s] = y
    /// ```
    ///
    /// Reads the input bits by slot and writes `z`, `A z` and `B z` by slot.
    /// A slot no gate drives is never written, so it keeps the scratch's zero.
    fn walk_lanes(&self, lanes: &mut Lanes) {
        let Lanes {
            inputs, wires, z, a, b, ..
        } = lanes;
        wires.clear();
        for &gate in &self.gates {
            let v = match gate {
                // An input bit or the constant: `z * 1 = z`.
                Gate::Free(s) => {
                    let s = s.index();
                    let v = if s == self.const_pos { u64::MAX } else { inputs[s] };
                    (z[s], a[s], b[s]) = (v, v, u64::MAX);
                    v
                }
                // Free: no row, no slot.
                Gate::Xor(x, y) => wires[x.index()] ^ wires[y.index()],
                // A product: `x * y = z`.
                Gate::And(x, y, s) => {
                    let (x, y) = (wires[x.index()], wires[y.index()]);
                    let s = s.index();
                    (z[s], a[s], b[s]) = (x & y, x, y);
                    x & y
                }
                // A committed copy: `x * 1 = z`.
                Gate::Copy(x, s) => {
                    let v = wires[x.index()];
                    let s = s.index();
                    (z[s], a[s], b[s]) = (v, v, u64::MAX);
                    v
                }
            };
            wires.push(v);
        }
    }

    /// The witness of the caller's rows, by walking the gate list 64 instances at a time.
    ///
    /// - `input_words(row, words)` writes a row's input port words.
    /// - `padding` fills the instances past the rows.
    ///
    /// The tables are bit for bit those of the one-instance walk.
    pub fn witness_by_walk<S: Sync>(
        &self,
        rows: &[S],
        padding: &S,
        n_blocks_log: usize,
        input_words: impl Fn(&S, &mut [u64]) + Sync,
    ) -> Witness {
        self.batch(n_blocks_log)
            .witness(|z| self.witness_by_walk_into(z, rows, padding, n_blocks_log, input_words, |_, _| {}))
    }

    /// The same, with `z` written into the caller's buffer.
    ///
    /// `check(row, z)` sees each instance's bits while they are in cache.
    ///
    /// ```text
    ///     rows  --transpose-->  input bits by slot  --walk-->  z, A z, B z by slot  --transpose-->  instance-major
    /// ```
    pub fn witness_by_walk_into<S: Sync>(
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
        let words = (1usize << self.k_log) / 64;
        // Slot groups past the useful bits hold only zeros, so they skip the transpose.
        let live_words = self.useful_bits.div_ceil(64);
        self.batch(n_blocks_log).fill_groups(
            z,
            lanes,
            || Lanes::new(self),
            |s: &mut Lanes, first: usize, t: GroupTables<'_>| {
                // Phase 1: each lane's input words, the padding row past the batch's rows.
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
            },
            |i, z| check(rows.get(i).unwrap_or(padding), z),
        )
    }

    /// The witness of the caller's rows, one instance at a time.
    ///
    /// It suits a circuit whose witness is cheaper as word arithmetic.
    ///
    /// `instance(row, z, a, b)` sets one instance's bits in three zeroed buffers.
    pub fn witness_by_instance<S: Sync>(
        &self,
        rows: &[S],
        padding: &S,
        n_blocks_log: usize,
        instance: impl Fn(&S, &mut [u64], &mut [u64], &mut [u64]) + Sync,
    ) -> Witness {
        self.batch(n_blocks_log)
            .witness(|z| self.witness_by_instance_into(z, rows, padding, n_blocks_log, instance, |_, _| {}))
    }

    /// The same, with `z` written into the caller's buffer.
    ///
    /// `check(row, z)` sees each instance's bits while they are in cache.
    pub fn witness_by_instance_into<S: Sync>(
        &self,
        z: &mut [u64],
        rows: &[S],
        padding: &S,
        n_blocks_log: usize,
        instance: impl Fn(&S, &mut [u64], &mut [u64], &mut [u64]) + Sync,
        check: impl Fn(&S, &[u64]) + Sync,
    ) -> Tables {
        self.batch(n_blocks_log)
            .fill_instances(z, rows, padding, instance, |i, z| {
                check(rows.get(i).unwrap_or(padding), z);
            })
    }

    /// The witness of the caller's rows, eight instances at a time.
    ///
    /// `batch(rows, z, a, b)` sets eight instances' bits in three zeroed instance-major buffers.
    pub fn witness_by_batch8<S: Sync>(
        &self,
        rows: &[S],
        padding: &S,
        n_blocks_log: usize,
        batch: impl Fn([&S; 8], &mut [u64], &mut [u64], &mut [u64]) + Sync,
    ) -> Witness {
        self.batch(n_blocks_log)
            .witness(|z| self.witness_by_batch8_into(z, rows, padding, n_blocks_log, batch, |_, _| {}))
    }

    /// The same, with `z` written into the caller's buffer.
    ///
    /// `check(row, z)` sees each instance's bits while they are in cache.
    pub fn witness_by_batch8_into<S: Sync>(
        &self,
        z: &mut [u64],
        rows: &[S],
        padding: &S,
        n_blocks_log: usize,
        batch: impl Fn([&S; 8], &mut [u64], &mut [u64], &mut [u64]) + Sync,
        check: impl Fn(&S, &[u64]) + Sync,
    ) -> Tables {
        self.batch(n_blocks_log).fill_batches8(z, rows, padding, batch, |i, z| {
            check(rows.get(i).unwrap_or(padding), z);
        })
    }

    /// A batch of `2^n_blocks_log` of this circuit's instances.
    const fn batch(&self, n_blocks_log: usize) -> Batch {
        Batch {
            n_blocks_log,
            k_log: self.k_log,
        }
    }

    /// The matrix-vector products `(A_0 w, B_0 w)`, by one forward walk.
    pub fn row_values(&self, w: &[F192]) -> (Vec<F192>, Vec<F192>) {
        let k = self.n_cols();
        assert_eq!(w.len(), k);
        // The constant column's weight is what `B` takes wherever its row reads the constant.
        let wc = w[self.const_pos];
        let mut ra = vec![F192::ZERO; k];
        let mut rb = vec![F192::ZERO; k];
        // Wire `i` carries gate `i`'s column combination: an XOR adds, a committed wire is its own column.
        let mut wires: Vec<F192> = Vec::with_capacity(self.gates.len());
        for &gate in &self.gates {
            let v = match gate {
                Gate::Free(s) => {
                    let s = s.index();
                    (ra[s], rb[s]) = (w[s], wc);
                    w[s]
                }
                Gate::Xor(x, y) => wires[x.index()] + wires[y.index()],
                Gate::And(x, y, s) => {
                    let s = s.index();
                    (ra[s], rb[s]) = (wires[x.index()], wires[y.index()]);
                    w[s]
                }
                Gate::Copy(x, s) => {
                    let s = s.index();
                    (ra[s], rb[s]) = (wires[x.index()], wc);
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
    /// `A z` by slot.
    a: Vec<u64>,
    /// `B z` by slot.
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

    /// `(A_0 + alpha B_0)^T u`, by one backward walk.
    ///
    /// Every gate, in reverse, hands its wire's adjoint to its operands or deposits it on its slot.
    fn fold_alpha_batched(&self, alpha: F192, u: &[F192]) -> Vec<F192> {
        assert_eq!(u.len(), self.n_cols());
        let c = self.const_pos;
        let mut m = vec![F192::ZERO; u.len()];
        // The adjoint of each wire: the row weight its consumers have handed back so far.
        let mut adj = vec![F192::ZERO; self.gates.len()];
        for (i, &gate) in self.gates.iter().enumerate().rev() {
            let g = adj[i];
            match gate {
                // `A` reads the slot itself, `B` the constant.
                Gate::Free(s) => {
                    let s = s.index();
                    m[s] += g + u[s];
                    m[c] += alpha * u[s];
                }
                // An XOR passes its adjoint to both operands.
                Gate::Xor(x, y) => {
                    adj[x.index()] += g;
                    adj[y.index()] += g;
                }
                // `A` reads `x`, `B` reads `y`; the slot's own column collects its consumers' adjoint.
                Gate::And(x, y, s) => {
                    let s = s.index();
                    m[s] += g;
                    adj[x.index()] += u[s];
                    adj[y.index()] += alpha * u[s];
                }
                // `A` reads `x`, `B` the constant.
                Gate::Copy(x, s) => {
                    let s = s.index();
                    m[s] += g;
                    adj[x.index()] += u[s];
                    m[c] += alpha * u[s];
                }
            }
        }
        m
    }

    fn bilinear_form(&self, alpha: F192, u: &[F192], w: &[F192]) -> Option<F192> {
        let (ra, rb) = self.row_values(w);
        Some((u.iter().zip(ra.iter().zip(&rb))).fold(F192::ZERO, |acc, (&u, (&a, &b))| acc + u * (a + alpha * b)))
    }
}

#[cfg(test)]
mod tests {
    use primitives::test_util::Rng;

    use super::*;

    /// A random circuit over the builder's whole vocabulary.
    ///
    /// A narrow input port and an undriven output bit are structural zeros.
    fn random_circuit(rng: &mut Rng) -> Circuit {
        // Ports: three input words, one of them narrow, and two outputs.
        let narrow = 1 + (rng.next_u32() % 63) as usize;
        let mut c = Builder::new(&[64, narrow, 64], &[64, narrow]);

        // Operands to draw from: every input bit, a structural zero and the constant.
        let mut pool: Vec<Wire> = (0..3).flat_map(|port| c.input(port)).collect();
        pool.extend([Wire::ZERO, Wire::ONE]);

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
        // Invariant: the 64-lane walk writes the three tables the one-instance walk writes.
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
            let walk = circuit.witness_by_instance(&rows, &padding, n_log, |row, z, az, bz| {
                circuit.witness_instance(row, z, az, bz);
            });
            let sliced = circuit.witness_by_walk(&rows, &padding, n_log, |row, words| words.copy_from_slice(row));
            assert!(walk.z == sliced.z, "z, round {round}");
            assert!(walk.az == sliced.az, "A z, round {round}");
            assert!(walk.bz == sliced.bz, "B z, round {round}");
        }
    }
}
