//! Boolean circuits as gate lists over word ports: what [`crate::arith`] and the
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
//! committed wire is a row. As in [`crate::hash`], no matrix is ever built: the
//! verifier walks the list forwards and the prover backwards (doc/leanvm, Annex
//! C "Evaluating the matrices"). Across implementations what has to agree is the
//! port layout and the order products are made in, which fixes their slots; the
//! order of the free XORs is nobody's business.

use crate::lincheck::LincheckCircuit;
use crate::reduction::Block;
use crate::witness::drive_witness_packed_and_lincheck;
use primitives::field::F192;
use zk_alloc::ArenaVec;

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
        let words = |bits: &[usize]| bits.iter().map(|b| b.div_ceil(64)).sum::<usize>();
        let n_input_words = words(input_bits);
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
        for &bits in input_bits {
            let wires = (0..bits).map(|i| Some(c.push(Gate::Free((base + i) as u32)))).collect();
            c.inputs.push(wires);
            base += 64 * bits.div_ceil(64);
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
    pub fn one(&self) -> Wire {
        self.one
    }

    /// Input port `port`'s bits, low first.
    pub fn input(&self, port: usize) -> Vec<Wire> {
        self.inputs[port].clone()
    }

    /// The slot the next product takes.
    pub fn next_slot(&self) -> usize {
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
        let (base, bits) = self.outputs[port];
        assert!(bit < bits, "output port {port} has {bits} bits");
        if let Some(wire) = wire {
            self.push(Gate::Copy(wire, (base + bit) as u32));
        }
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
    pub fn k_log(&self) -> usize {
        self.k_log
    }

    pub fn useful_bits(&self) -> usize {
        self.useful_bits
    }

    /// The constant wire's position.
    pub fn const_pos(&self) -> usize {
        self.const_pos
    }

    /// Products, which is what an instance pays beyond its ports.
    pub fn n_products(&self) -> usize {
        self.useful_bits - self.const_pos - 1
    }

    pub fn n_input_words(&self) -> usize {
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

    /// `(z, a, b, z_lincheck)` for `rows` of input words, padded with all-zero inputs
    /// to `2^n_blocks_log` instances: the bit-packed `z`, `A·z` and `B·z`
    /// (`2^k_log / 64` words per instance), and lincheck's byte stripes.
    pub fn generate_witness<const N: usize>(
        &self,
        rows: &[[u64; N]],
        n_blocks_log: usize,
    ) -> (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>) {
        assert_eq!(N, self.n_input_words);
        self.generate_witness_with(rows, &[0; N], n_blocks_log, |row, z, az, bz| {
            self.witness_instance(row, z, az, bz)
        })
    }

    /// [`Self::generate_witness`] over the caller's own rows, `inputs` writing a row's
    /// input words. `rows` fill the batch, or `padding` does.
    pub fn generate_witness_by<S: Sync>(
        &self,
        rows: &[S],
        padding: &S,
        n_blocks_log: usize,
        inputs: impl Fn(&S, &mut [u64]) + Sync,
    ) -> (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>) {
        const MAX_INPUT_WORDS: usize = 16;
        assert!(self.n_input_words <= MAX_INPUT_WORDS);
        self.generate_witness_with(rows, padding, n_blocks_log, |row, z, az, bz| {
            let mut words = [0u64; MAX_INPUT_WORDS];
            inputs(row, &mut words[..self.n_input_words]);
            self.witness_instance(&words[..self.n_input_words], z, az, bz)
        })
    }

    /// [`Self::generate_witness`] with the caller's own rows, padding row and way to
    /// fill an instance, for a circuit whose witness is cheaper as word arithmetic.
    pub(crate) fn generate_witness_with<S: Sync>(
        &self,
        rows: &[S],
        padding: &S,
        n_blocks_log: usize,
        instance: impl Fn(&S, &mut [u64], &mut [u64], &mut [u64]) + Sync,
    ) -> (ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u64>, ArenaVec<u8>) {
        drive_witness_packed_and_lincheck(rows, Some(padding), n_blocks_log, self.k_log, instance)
    }

    /// The matrix-vector products `(A_0 w, B_0 w)`, by one forward walk.
    pub(crate) fn row_values(&self, w: &[F192]) -> (Vec<F192>, Vec<F192>) {
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
