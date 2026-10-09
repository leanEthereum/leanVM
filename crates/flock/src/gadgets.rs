//! u64 arithmetic in the gate-list language: multiplication, wrapping or widening.
//!
//! A gadget takes wires and returns wires, so gadgets compose into larger circuits.
//! Its witness is word arithmetic on the structure its gate list is built from, never the generic walk.
//!
//! ## Partial products are free
//!
//! A schoolbook multiplier pays one product per partial product `a_i b_j`, then one per carry to sum them.
//! Over GF(2) the first half is avoidable.
//! With `e_ij = NOT(a_i XOR b_j)`, an integer identity holds bit by bit:
//!
//! ```text
//!     2 a_i b_j = a_i + b_j - 1 + e_ij
//! ```
//!
//! Summed over `i` and `j`, with `M = 2^64 - 1` and `NOT a = M - a` the complement:
//!
//! ```text
//!     2 a b = sum_i (a_i ? b : NOT b) 2^i + NOT a + NOT b + (a + b) 2^64 + 1 - 2^128
//! ```
//!
//! Every row there is affine in the inputs.
//! Its column 0 is `2 + 2g`, with `g = NOT a_0 * NOT b_0` the one product it costs.
//! After it the identity halves: `a b mod 2^N` is `1 + g` plus the other columns shifted down a place.
//! That is 66 rows of affine bits, with `1` and `g` in the empty low bits of two of them.
//!
//! ## Compression
//!
//! A carry-save step turns three rows into their XOR and their majority shifted up a place.
//! The majority `(x + z)(y + z) + z` is one product at each position where at least two rows have a bit.
//! The exception: where exactly two do and the carry row is still free there, one of the two bits moves into it.
//!
//! Taking the three rows that end lowest each time, the 64 steps cost as few products as summing column by column.
//! A ripple-carry addition finishes the last two rows.
//! The top position's majority would carry out of the modulus, so it is never a product.
//!
//! Every step is word arithmetic on 128-bit rows, and its products are one run of slots.
//! So an instance's witness is a few shifts and masks per step.

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
use std::arch::x86_64::{
    __m256i, _mm_cvtsi64_si128, _mm256_add_epi64, _mm256_and_si256, _mm256_loadu_si256, _mm256_or_si256,
    _mm256_set1_epi64x, _mm256_sll_epi64, _mm256_srl_epi64, _mm256_storeu_si256, _mm256_xor_si256,
};
use std::ops::{BitAnd, BitOr, BitXor, Not, Shl, Shr};

use crate::circuit::{Builder, Wire};
use crate::witness::InstanceRows;

/// The rows `(a_i ? b : NOT b)` for `i < 64`, then the `a` and `b` rows.
const N_ROWS: usize = 66;

/// The row of `NOT a`'s high bits and `a`.
const A_ROW: usize = 64;

/// The row of `NOT b`'s high bits and `b`.
const B_ROW: usize = 65;

/// One carry-save step: rows `x`, `y`, `z` become the sum row, stored in `x`, and the carry row, stored in `y`.
#[derive(Clone, Copy, Debug)]
struct Csa {
    x: usize,
    y: usize,
    z: usize,
    /// Positions whose majority is a product, one run of slots from `slot`.
    products: u128,
    /// Positions where the pair's `y` bit moves to the carry row instead.
    move_y: u128,
    /// Positions where the pair's `z` bit moves to the carry row instead.
    move_z: u128,
    /// The first product's slot.
    slot: usize,
}

/// A row's `(highest, lowest)` position.
const fn ends(row: u128) -> (u32, u32) {
    (127 - row.leading_zeros(), row.trailing_zeros())
}

/// Whether the set bits of `mask` are one run, so its products take consecutive slots.
fn is_run(mask: u128) -> bool {
    let run = mask.checked_shr(mask.trailing_zeros()).unwrap_or(0);
    run & run.wrapping_add(1) == 0
}

/// A built multiplier: the plan its witness replays as word arithmetic.
#[derive(Debug)]
pub struct Multiplier {
    /// The slot of `g = NOT a_0 * NOT b_0`.
    g_slot: usize,
    /// The carry-save steps, in order.
    steps: Vec<Csa>,
    /// The two rows the steps leave.
    last: (usize, usize),
    /// The positions where adding the last two rows makes a product.
    carries: u128,
    /// The first of those products' slots.
    carry_slot: usize,
    /// The positions below the product's width.
    width: u128,
}

impl Multiplier {
    /// The low `N` bits of `a b`, as wires.
    ///
    /// `N` is 64 for the low word, or 128 for the whole product.
    pub fn build<const N: usize>(c: &mut Builder, a: &[Wire; 64], b: &[Wire; 64]) -> ([Wire; N], Self) {
        const { assert!(64 <= N && N <= 128, "a product of two words has 64 to 128 bits") };
        let width = u128::MAX >> (128 - N);
        let not_a: [Wire; 64] = std::array::from_fn(|i| c.not(a[i]));
        let not_b: [Wire; 64] = std::array::from_fn(|i| c.not(b[i]));
        let g_slot = c.next_slot();
        let g = c.and(not_a[0], not_b[0]);

        // Phase 1: each row's wire per position, all shifted down a place.
        // Row 0's bit 0 is what `g` and the constant one replace.
        let mut rows = vec![vec![Wire::ZERO; N]; N_ROWS];
        for i in 0..64usize {
            for (j, &bj) in b.iter().enumerate() {
                if let Some(p) = (i + j).checked_sub(1).filter(|&p| p < N) {
                    rows[i][p] = c.xor(bj, not_a[i]);
                }
            }
        }
        // `(NOT a >> 1) + a 2^63`, and the same for `b`.
        for (row, low, high) in [(A_ROW, &not_a, a), (B_ROW, &not_b, b)] {
            let len = 64.min(N - 63);
            rows[row][..63].copy_from_slice(&low[1..]);
            rows[row][63..63 + len].copy_from_slice(&high[..len]);
        }
        rows[2][0] = Wire::ONE;
        rows[3][0] = g;
        // Half of the constant `2^128`, which survives only mod `2^128`.
        if N == 128 {
            rows[A_ROW][127] = Wire::ONE;
        }
        let mut present: Vec<u128> = rows
            .iter()
            .map(|row| (0..N).filter(|&p| !row[p].is_zero()).fold(0, |m, p| m | (1 << p)))
            .collect();

        // Phase 2: carry-save steps on the three rows that end lowest, until two rows remain.
        let mut live: Vec<usize> = (0..N_ROWS).collect();
        let mut steps = Vec::new();
        while live.len() > 2 {
            let mut order: Vec<usize> = (0..live.len()).collect();
            order.sort_by_key(|&t| ends(present[live[t]]));
            let [x, y, z] = [live[order[0]], live[order[1]], live[order[2]]];
            live.retain(|r| ![x, y, z].contains(r));
            live.extend([x, y]);

            // A position with two bits or more makes a carry; one product, unless a bit can move instead.
            let (px, py, pz) = (present[x], present[y], present[z]);
            let pairs = ((px & py) | (px & pz) | (py & pz)) & (width >> 1);
            let triples = px & py & pz;
            let (mut products, mut moves) = (0u128, 0u128);
            for p in (0..N - 1).filter(|&p| (pairs >> p) & 1 == 1) {
                // The carry row is free at `p` unless `p - 1` has a product.
                if (triples >> p) & 1 == 0 && (products << 1) >> p & 1 == 0 {
                    moves |= 1 << p;
                } else {
                    products |= 1 << p;
                }
            }
            assert!(is_run(products), "a step's products must be one run of slots");
            let step = Csa {
                x,
                y,
                z,
                products,
                move_y: moves & !pz,
                move_z: moves & pz,
                slot: c.next_slot(),
            };

            let (mut sum, mut carry) = (vec![Wire::ZERO; N], vec![Wire::ZERO; N]);
            for p in 0..N {
                let (wx, wy, wz) = (rows[x][p], rows[y][p], rows[z][p]);
                if (products >> p) & 1 == 1 {
                    // A full adder: the majority is the product, the sum is free.
                    let xz = c.xor(wx, wz);
                    let yz = c.xor(wy, wz);
                    let maj = c.and(xz, yz);
                    carry[p + 1] = c.xor(maj, wz);
                    sum[p] = c.xor(xz, wy);
                } else if (step.move_z >> p) & 1 == 1 {
                    carry[p] = wz;
                    sum[p] = c.xor(wx, wy);
                } else if (step.move_y >> p) & 1 == 1 {
                    carry[p] = wy;
                    sum[p] = wx;
                } else {
                    let xz = c.xor(wx, wz);
                    sum[p] = c.xor(xz, wy);
                }
            }
            rows[x] = sum;
            rows[y] = carry;
            present[x] = px | py | pz;
            present[y] = (products << 1) | moves;
            steps.push(step);
        }

        // Phase 3: a ripple-carry addition of the last two rows.
        let &[x, y] = live.as_slice() else {
            unreachable!("the steps stop at two rows")
        };
        let carry_slot = c.next_slot();
        let mut carries = 0u128;
        let mut carry = Wire::ZERO;
        let mut product = [Wire::ZERO; N];
        for (p, (&wx, &wy)) in rows[x].iter().zip(&rows[y]).enumerate() {
            let out = if p + 1 < N && [wx, wy, carry].iter().filter(|w| !w.is_zero()).count() >= 2 {
                carries |= 1 << p;
                let xc = c.xor(wx, carry);
                let yc = c.xor(wy, carry);
                let maj = c.and(xc, yc);
                carry = c.xor(maj, carry);
                c.xor(xc, wy)
            } else {
                let xy = c.xor(wx, wy);
                c.xor(xy, std::mem::take(&mut carry))
            };
            product[p] = out;
        }
        assert!(is_run(carries), "the final carries must be one run of slots");

        let multiplier = Self {
            g_slot,
            steps,
            last: (x, y),
            carries,
            carry_slot,
            width,
        };
        (product, multiplier)
    }

    /// Write the multiplication's product rows into zeroed packed buffers, and return the product.
    ///
    /// Only product slots are written, so the plan composes with other arithmetic.
    /// The caller fills the operand ports, the output ports and the constant.
    pub fn witness(&self, a: u64, b: u64, z: &mut [u64], az: &mut [u64], bz: &mut [u64]) -> u128 {
        self.witness_into(a, b, &mut InstanceRows::new(z, az, bz))
    }

    /// Write the complement selector, the carry-save products and the final carries.
    fn witness_into(&self, a: u64, b: u64, tables: &mut InstanceRows<'_>) -> u128 {
        // A wrapping product needs only the low half of every row.
        if self.width == u128::from(u64::MAX) {
            return u128::from(self.witness_low(a, b, tables));
        }
        let (na, nb) = (!a, !b);
        let mut rows = [0u128; N_ROWS];
        for (i, row) in rows[..64].iter_mut().enumerate() {
            let v = u128::from(b ^ ((a >> i) & 1).wrapping_sub(1));
            *row = if i == 0 { v >> 1 } else { v << (i - 1) };
        }
        rows[A_ROW] = u128::from(na >> 1) | (u128::from(a) << 63) | (1 << 127);
        rows[B_ROW] = u128::from(nb >> 1) | (u128::from(b) << 63);
        rows[2] |= 1;
        rows[3] |= u128::from(na & nb & 1);
        for row in &mut rows {
            *row &= self.width;
        }
        tables.products(self.g_slot, 1, u128::from(na), u128::from(nb));

        for s in &self.steps {
            let (rx, ry, rz) = (rows[s.x], rows[s.y], rows[s.z]);
            let (xz, yz) = (rx ^ rz, ry ^ rz);
            let moved = (ry & s.move_y) | (rz & s.move_z);
            rows[s.x] = rx ^ ry ^ rz ^ moved;
            rows[s.y] = ((((xz & yz) ^ rz) & s.products) << 1) | moved;
            tables.products(s.slot, s.products, xz, yz);
        }

        // The native sum's XOR with its operands recovers the final carry-in bits.
        let (rx, ry) = (rows[self.last.0], rows[self.last.1]);
        let sum = rx.wrapping_add(ry) & self.width;
        let carry_in = sum ^ rx ^ ry;
        tables.products(self.carry_slot, self.carries, rx ^ carry_in, ry ^ carry_in);
        sum
    }

    /// The same plan modulo `2^64`, on words: a 64-bit shift clips the rows for free.
    fn witness_low(&self, a: u64, b: u64, tables: &mut InstanceRows<'_>) -> u64 {
        let mut rows = [0u64; N_ROWS];
        for (i, row) in rows[..64].iter_mut().enumerate() {
            let v = b ^ ((a >> i) & 1).wrapping_sub(1);
            *row = if i == 0 { v >> 1 } else { v << (i - 1) };
        }
        rows[A_ROW] = (!a >> 1) | (a << 63);
        rows[B_ROW] = (!b >> 1) | (b << 63);
        rows[2] |= 1;
        rows[3] |= !a & !b & 1;
        tables.products(self.g_slot, 1, u128::from(!a), u128::from(!b));

        // Each step replaces three rows by the same sum and carry.
        for s in &self.steps {
            let (rx, ry, rz) = (rows[s.x], rows[s.y], rows[s.z]);
            let (xz, yz) = (rx ^ rz, ry ^ rz);
            let moved = (ry & s.move_y as u64) | (rz & s.move_z as u64);
            rows[s.x] = rx ^ ry ^ rz ^ moved;
            rows[s.y] = ((((xz & yz) ^ rz) & s.products as u64) << 1) | moved;
            tables.products(s.slot, s.products, u128::from(xz), u128::from(yz));
        }

        // The native sum's XOR with its operands recovers the final carry-in bits.
        let (rx, ry) = (rows[self.last.0], rows[self.last.1]);
        let sum = rx.wrapping_add(ry);
        let carry_in = sum ^ rx ^ ry;
        tables.products(
            self.carry_slot,
            self.carries,
            u128::from(rx ^ carry_in),
            u128::from(ry ^ carry_in),
        );
        sum
    }

    /// Write four wrapping multiplications' rows into word-major tables, and return the four products.
    ///
    /// Word `w` of each table holds word `w` of the four instances, side by side.
    /// The caller fills their ports and constant, then converts to instance-major storage.
    ///
    /// # Panics
    ///
    /// When the multiplier is not 64 bits wide.
    pub fn witness_batch4(
        &self,
        a: [u64; 4],
        b: [u64; 4],
        z: &mut [[u64; 4]],
        az: &mut [[u64; 4]],
        bz: &mut [[u64; 4]],
    ) -> [u64; 4] {
        assert_eq!(
            self.width,
            u128::from(u64::MAX),
            "batched multiplication wraps at 64 bits"
        );
        let (a, b) = (U64x4::new(a), U64x4::new(b));
        let mut tables = Tables4 { z, az, bz };

        // Every lane shares every mask and shift of the plan.
        let mut rows = [U64x4::splat(0); N_ROWS];
        for (i, row) in rows[..64].iter_mut().enumerate() {
            let v = b ^ ((a >> i) & U64x4::splat(1)).wrapping_add(U64x4::splat(u64::MAX));
            *row = if i == 0 { v >> 1 } else { v << (i - 1) };
        }
        let (na, nb) = (!a, !b);
        rows[A_ROW] = (na >> 1) | (a << 63);
        rows[B_ROW] = (nb >> 1) | (b << 63);
        rows[2] = rows[2] | U64x4::splat(1);
        rows[3] = rows[3] | (na & nb & U64x4::splat(1));
        tables.products(self.g_slot, 1, na, nb);

        for s in &self.steps {
            let (rx, ry, rz) = (rows[s.x], rows[s.y], rows[s.z]);
            let (xz, yz) = (rx ^ rz, ry ^ rz);
            let moved = (ry & U64x4::splat(s.move_y as u64)) | (rz & U64x4::splat(s.move_z as u64));
            rows[s.x] = rx ^ ry ^ rz ^ moved;
            rows[s.y] = ((((xz & yz) ^ rz) & U64x4::splat(s.products as u64)) << 1) | moved;
            tables.products(s.slot, s.products as u64, xz, yz);
        }

        // Native lane additions recover the final carries.
        let (rx, ry) = (rows[self.last.0], rows[self.last.1]);
        let sum = rx.wrapping_add(ry);
        let carry = sum ^ rx ^ ry;
        tables.products(self.carry_slot, self.carries as u64, rx ^ carry, ry ^ carry);
        sum.to_array()
    }
}

/// Four independent words, side by side: one AVX2 register on x86, an array elsewhere.
#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#[derive(Clone, Copy, Debug)]
struct U64x4(__m256i);

/// Four independent words, side by side: one AVX2 register on x86, an array elsewhere.
#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
#[derive(Clone, Copy, Debug)]
struct U64x4([u64; 4]);

#[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
impl U64x4 {
    fn new(words: [u64; 4]) -> Self {
        // SAFETY: the load reads exactly the four words.
        Self(unsafe { _mm256_loadu_si256(words.as_ptr().cast()) })
    }

    fn to_array(self) -> [u64; 4] {
        let mut out = [0; 4];
        // SAFETY: the store writes exactly the four words.
        unsafe { _mm256_storeu_si256(out.as_mut_ptr().cast(), self.0) };
        out
    }

    fn splat(v: u64) -> Self {
        // SAFETY: the target enables AVX2.
        Self(unsafe { _mm256_set1_epi64x(v as i64) })
    }

    /// Lane-wise addition modulo `2^64`.
    fn wrapping_add(self, rhs: Self) -> Self {
        // SAFETY: the target enables AVX2.
        Self(unsafe { _mm256_add_epi64(self.0, rhs.0) })
    }
}

#[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
impl U64x4 {
    const fn new(words: [u64; 4]) -> Self {
        Self(words)
    }

    const fn to_array(self) -> [u64; 4] {
        self.0
    }

    const fn splat(v: u64) -> Self {
        Self([v; 4])
    }

    /// Lane-wise addition modulo `2^64`.
    fn wrapping_add(self, rhs: Self) -> Self {
        Self(std::array::from_fn(|i| self.0[i].wrapping_add(rhs.0[i])))
    }
}

impl BitXor for U64x4 {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self {
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
        // SAFETY: the target enables AVX2.
        return Self(unsafe { _mm256_xor_si256(self.0, rhs.0) });
        #[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
        Self(std::array::from_fn(|i| self.0[i] ^ rhs.0[i]))
    }
}

impl BitAnd for U64x4 {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: Self) -> Self {
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
        // SAFETY: the target enables AVX2.
        return Self(unsafe { _mm256_and_si256(self.0, rhs.0) });
        #[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
        Self(std::array::from_fn(|i| self.0[i] & rhs.0[i]))
    }
}

impl BitOr for U64x4 {
    type Output = Self;

    #[inline(always)]
    fn bitor(self, rhs: Self) -> Self {
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
        // SAFETY: the target enables AVX2.
        return Self(unsafe { _mm256_or_si256(self.0, rhs.0) });
        #[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
        Self(std::array::from_fn(|i| self.0[i] | rhs.0[i]))
    }
}

impl Not for U64x4 {
    type Output = Self;

    #[inline(always)]
    fn not(self) -> Self {
        self ^ Self::splat(u64::MAX)
    }
}

/// Every lane shifted left by the same amount, below 64.
impl Shl<usize> for U64x4 {
    type Output = Self;

    #[inline(always)]
    fn shl(self, shift: usize) -> Self {
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
        // SAFETY: the target enables AVX2.
        return Self(unsafe { _mm256_sll_epi64(self.0, _mm_cvtsi64_si128(shift as i64)) });
        #[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
        Self(self.0.map(|x| x << shift))
    }
}

/// Every lane shifted right by the same amount, below 64.
impl Shr<usize> for U64x4 {
    type Output = Self;

    #[inline(always)]
    fn shr(self, shift: usize) -> Self {
        #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
        // SAFETY: the target enables AVX2.
        return Self(unsafe { _mm256_srl_epi64(self.0, _mm_cvtsi64_si128(shift as i64)) });
        #[cfg(not(all(target_arch = "x86_64", target_feature = "avx2")))]
        Self(self.0.map(|x| x >> shift))
    }
}

/// Four instances' tables, word-major: word `w` of each holds the four instances' word `w`.
struct Tables4<'a> {
    z: &'a mut [[u64; 4]],
    az: &'a mut [[u64; 4]],
    bz: &'a mut [[u64; 4]],
}

impl Tables4<'_> {
    /// Product rows from `slot`, one per set position of `mask`, in every lane.
    #[inline(always)]
    fn products(&mut self, slot: usize, mask: u64, left: U64x4, right: U64x4) {
        if mask == 0 {
            return;
        }
        // The mask is one run of positions, so a shift packs it into consecutive slots.
        let low = mask.trailing_zeros() as usize;
        let left = (left & U64x4::splat(mask)) >> low;
        let right = (right & U64x4::splat(mask)) >> low;
        let product = left & right;
        // The run spans at most two words from `slot`; the split shifts never shift by 64.
        let (word, shift) = (slot / 64, slot % 64);
        for (buf, bits) in [(&mut *self.z, product), (&mut *self.az, left), (&mut *self.bz, right)] {
            buf[word] = (U64x4::new(buf[word]) | (bits << shift)).to_array();
            buf[word + 1] = (U64x4::new(buf[word + 1]) | ((bits >> 1) >> (63 - shift))).to_array();
        }
    }
}
