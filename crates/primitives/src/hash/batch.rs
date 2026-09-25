//! Batched hashing: many independent inputs, one SIMD lane each.
//!
//! State word `i` becomes one vector holding that word for every lane.
//!
//! A round is then elementwise work, and equal-length inputs share one block counter.
//!
//! ```text
//!     lane     one input
//!     group    WIDTH inputs, one transposed state
//!     set      the groups one compression call advances together
//! ```

use std::mem::MaybeUninit;

use super::{BLOCK_LEN, IV, OUT_LEN, hash_from_state};

/// One state word across all lanes of a group: a vector of `WIDTH` 32-bit lanes.
///
/// Each backend supplies the lane arithmetic and its transposes.
///
/// # Safety
///
/// Loads and stores may be unaligned vector accesses over `WIDTH` contiguous `u32`.
pub(super) trait Lanes32: Copy {
    /// Lanes per vector.
    const WIDTH: usize;

    /// Groups one compression call advances together.
    ///
    /// Only 4 of a round's 8 G's are independent, which caps what one group keeps busy.
    ///
    /// A backend whose single group leaves pipes idle asks for more.
    const GROUPS: usize = 1;

    /// Whether the walk transposes each block one step ahead of its compression.
    const TRANSPOSE_AHEAD: bool = true;

    /// Load `WIDTH` contiguous `u32`.
    ///
    /// # Safety
    /// `p` must be valid for reads of `WIDTH` `u32`.
    unsafe fn load(p: *const u32) -> Self;

    /// Store `WIDTH` contiguous `u32`.
    ///
    /// # Safety
    /// `p` must be valid for writes of `WIDTH` `u32`.
    unsafe fn store(self, p: *mut u32);

    /// Every lane set to `x`.
    fn splat(x: u32) -> Self;

    /// Lane-wise wrapping addition.
    fn add(self, o: Self) -> Self;

    /// Lane-wise xor.
    fn xor(self, o: Self) -> Self;

    /// Rotate every lane right by `N`, one of BLAKE2s's 16, 12, 8, 7.
    fn rotr<const N: u32>(self) -> Self;

    /// Transpose one 64-byte block of each of `WIDTH` inputs.
    ///
    /// ```text
    ///     input l at src + l * stride    [w_0, w_1, ..., w_15]
    ///     block[w], lane l               input l's word w
    /// ```
    ///
    /// Backends with a shuffle network override this word-by-word default.
    ///
    /// # Safety
    /// Every input must be valid for 64 readable bytes.
    #[inline(always)]
    unsafe fn transpose(src: *const u8, stride: usize, block: &mut [Self; 16]) {
        // Gather into rows of 16 words, the widest backend's lane count.
        let mut words = [[0u32; 16]; 16];
        for lane in 0..Self::WIDTH {
            for w in 0..16 {
                // SAFETY: the caller guarantees 64 readable bytes per input.
                let word = unsafe { src.add(lane * stride + 4 * w).cast::<u32>().read_unaligned() };
                words[w][lane] = u32::from_le(word);
            }
        }
        // SAFETY: each row holds 16 >= WIDTH words.
        *block = std::array::from_fn(|w| unsafe { Self::load(words[w].as_ptr()) });
    }

    /// Write the chaining values out as `WIDTH` consecutive 32-byte digests.
    ///
    /// The reverse of the block transpose, over 8 words rather than 16.
    ///
    /// # Safety
    /// `out` must be valid for writes of `WIDTH * OUT_LEN` bytes.
    #[inline(always)]
    unsafe fn store_digests(h: &[Self; 8], out: *mut u8) {
        // Spill the eight vectors, then read each lane's eight words back as one digest.
        let mut words = [0u32; 8 * 16];
        for (i, hi) in h.iter().enumerate() {
            // SAFETY: `words` holds 8 * 16 >= 8 * WIDTH elements.
            unsafe { hi.store(words.as_mut_ptr().add(i * Self::WIDTH)) };
        }
        for lane in 0..Self::WIDTH {
            for i in 0..8 {
                let bytes = words[i * Self::WIDTH + lane].to_le_bytes();
                // SAFETY: `lane * 32 + i * 4 + 4 <= WIDTH * 32`.
                unsafe {
                    out.add(lane * OUT_LEN + 4 * i)
                        .copy_from_nonoverlapping(bytes.as_ptr(), 4)
                };
            }
        }
    }

    /// Compress `G` groups, each from its own transposed block, at byte counter `t`.
    ///
    /// A backend overrides it with a hand-scheduled kernel for its own group count.
    ///
    /// # Safety
    /// Every `m[g]` must be valid for reads.
    #[inline(always)]
    unsafe fn compress_groups<const G: usize>(h: &mut [[Self; 8]; G], m: [&[Self; 16]; G], t: u64, last: bool) {
        // SAFETY: forwarded from the caller.
        unsafe { compress_groups::<Self, G>(h, m, t, last) }
    }
}

/// The portable backend, and the reference the SIMD ones are checked against.
///
/// Dispatch is compile time, so only tests use it where a SIMD backend exists.
#[allow(dead_code)]
#[derive(Clone, Copy)]
pub(super) struct Scalar8([u32; 8]);

impl Lanes32 for Scalar8 {
    const WIDTH: usize = 8;

    #[inline(always)]
    unsafe fn load(p: *const u32) -> Self {
        Self(std::array::from_fn(|i| unsafe { *p.add(i) }))
    }
    #[inline(always)]
    unsafe fn store(self, p: *mut u32) {
        for (i, x) in self.0.into_iter().enumerate() {
            unsafe { *p.add(i) = x };
        }
    }
    #[inline(always)]
    fn splat(x: u32) -> Self {
        Self([x; 8])
    }
    #[inline(always)]
    fn add(self, o: Self) -> Self {
        Self(std::array::from_fn(|i| self.0[i].wrapping_add(o.0[i])))
    }
    #[inline(always)]
    fn xor(self, o: Self) -> Self {
        Self(std::array::from_fn(|i| self.0[i] ^ o.0[i]))
    }
    #[inline(always)]
    fn rotr<const N: u32>(self) -> Self {
        Self(std::array::from_fn(|i| self.0[i].rotate_right(N)))
    }
}

/// The G function over LITERAL state and message indices.
///
/// `$m` is the transposed block, so each message operand is a load at a constant offset.
macro_rules! g {
    ($v:ident, $m:ident, $a:expr, $b:expr, $c:expr, $d:expr, $x:expr, $y:expr) => {{
        $v[$a] = $v[$a].add($v[$b]).add($m[$x]);
        $v[$d] = $v[$d].xor($v[$a]).rotr::<16>();
        $v[$c] = $v[$c].add($v[$d]);
        $v[$b] = $v[$b].xor($v[$c]).rotr::<12>();
        $v[$a] = $v[$a].add($v[$b]).add($m[$y]);
        $v[$d] = $v[$d].xor($v[$a]).rotr::<8>();
        $v[$c] = $v[$c].add($v[$d]);
        $v[$b] = $v[$b].xor($v[$c]).rotr::<7>();
    }};
}

/// One round with the message schedule `s`: columns, then diagonals.
macro_rules! round {
    ($v:ident, $m:ident, [$s0:expr, $s1:expr, $s2:expr, $s3:expr, $s4:expr, $s5:expr, $s6:expr, $s7:expr,
      $s8:expr, $s9:expr, $s10:expr, $s11:expr, $s12:expr, $s13:expr, $s14:expr, $s15:expr]) => {{
        g!($v, $m, 0, 4, 8, 12, $s0, $s1);
        g!($v, $m, 1, 5, 9, 13, $s2, $s3);
        g!($v, $m, 2, 6, 10, 14, $s4, $s5);
        g!($v, $m, 3, 7, 11, 15, $s6, $s7);
        g!($v, $m, 0, 5, 10, 15, $s8, $s9);
        g!($v, $m, 1, 6, 11, 12, $s10, $s11);
        g!($v, $m, 2, 7, 8, 13, $s12, $s13);
        g!($v, $m, 3, 4, 9, 14, $s14, $s15);
    }};
}

/// The ten rounds as out-of-line functions, for interleaving groups.
macro_rules! round_fns {
    ($($name:ident [$($s:expr),*],)*) => {
        $(
            #[inline(never)]
            fn $name<S: Lanes32>(v: &mut [S; 16], m: &[S; 16]) {
                round!(v, m, [$($s),*])
            }
        )*
    };
}

round_fns! {
    round_0 [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    round_1 [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    round_2 [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    round_3 [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    round_4 [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    round_5 [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    round_6 [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    round_7 [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    round_8 [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    round_9 [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
}

/// The working state of one compression (RFC 7693, section 3.2).
///
/// ```text
///     v[0..8]    chaining value h
///     v[8..16]   IV, with v[12] ^= t_lo, v[13] ^= t_hi, v[14] = !v[14] on the final block
/// ```
#[inline(always)]
fn init<S: Lanes32>(h: &[S; 8], t: u64, last: bool) -> [S; 16] {
    // All ones on the final block, zero otherwise.
    let f0 = (last as u32).wrapping_neg();
    let row = [
        IV[0],
        IV[1],
        IV[2],
        IV[3],
        IV[4] ^ t as u32,
        IV[5] ^ (t >> 32) as u32,
        IV[6] ^ f0,
        IV[7],
    ];
    std::array::from_fn(|i| if i < 8 { h[i] } else { S::splat(row[i - 8]) })
}

/// Compress `G` groups.
///
/// One group runs its ten rounds inline, in registers.
///
/// Several groups keep their states in memory, one out-of-line call per round.
///
/// Each call fits the register file, and the calls of a round fill each other's stalls.
///
/// # Safety
/// Every `m[g]` must be valid for reads.
#[inline(always)]
pub(super) unsafe fn compress_groups<S: Lanes32, const G: usize>(
    h: &mut [[S; 8]; G],
    m: [&[S; 16]; G],
    t: u64,
    last: bool,
) {
    let mut v: [[S; 16]; G] = std::array::from_fn(|g| init(&h[g], t, last));
    // `G` is a constant, so only one of the two arms survives monomorphization.
    if G == 1 {
        let (v, m) = (&mut v[0], m[0]);
        round!(v, m, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]);
        round!(v, m, [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3]);
        round!(v, m, [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4]);
        round!(v, m, [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8]);
        round!(v, m, [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13]);
        round!(v, m, [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9]);
        round!(v, m, [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11]);
        round!(v, m, [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10]);
        round!(v, m, [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5]);
        round!(v, m, [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]);
    } else {
        macro_rules! round_all {
            ($($name:ident),*) => { $( for g in 0..G { $name(&mut v[g], m[g]); } )* };
        }
        round_all!(
            round_0, round_1, round_2, round_3, round_4, round_5, round_6, round_7, round_8, round_9
        );
    }
    // Feed-forward: h[i] ^= v[i] ^ v[i + 8].
    for g in 0..G {
        for i in 0..8 {
            h[g][i] = h[g][i].xor(v[g][i]).xor(v[g][i + 8]);
        }
    }
}

/// Hash `n_sets * G * WIDTH` consecutive inputs of `len` bytes into as many digests at `out`.
///
/// Software-pipelined if [`Lanes32::TRANSPOSE_AHEAD`], one step being one block of one set:
///
/// ```text
///     transpose 0
///     transpose 1    compress 0
///     transpose 2    compress 1
/// ```
///
/// No transpose then sits between two dependent compressions.
///
/// Out of line on purpose: inlined into the dispatcher, the walk measured slower.
///
/// # Safety
///
/// - `src` must be valid for `n_sets * G * WIDTH * len` bytes.
/// - `out` must be valid for `n_sets * G * WIDTH * OUT_LEN` bytes.
/// - `len` must be a nonzero multiple of 64.
#[inline(never)]
unsafe fn hash_sets<S: Lanes32, const G: usize>(
    src: *const u8,
    n_sets: usize,
    len: usize,
    state: &[u32; 8],
    t_offset: u64,
    out: *mut u8,
) {
    let n_blocks = len / BLOCK_LEN;
    let steps = n_sets * n_blocks;
    // No set: nothing to read, not even the first block.
    if steps == 0 {
        return;
    }

    // Step `k` is block `k % n_blocks` of set `k / n_blocks`.
    //
    //     set s, group g, lane l    input (s * G + g) * WIDTH + l
    let set_bytes = G * S::WIDTH * len;
    let transpose = |step: usize, buf: &mut [MaybeUninit<[S; 16]>; G]| {
        let (set, b) = (step / n_blocks, step % n_blocks);
        for (g, block) in buf.iter_mut().enumerate() {
            let first = set * set_bytes + g * S::WIDTH * len + b * BLOCK_LEN;
            // SAFETY: `step < steps`, so block `b` of every input in the group is in bounds.
            unsafe { S::transpose(src.add(first), len, block.as_mut_ptr().as_mut_unchecked()) };
        }
    };

    // Double buffer, never cleared: a block is transposed before it is read.
    let mut blocks = [[const { MaybeUninit::uninit() }; G]; 2];
    let [even, odd] = &mut blocks;
    // Every input starts from the same chaining value.
    let fresh = || [std::array::from_fn::<S, 8, _>(|i| S::splat(state[i])); G];
    let mut h = fresh();

    // Prologue: the first block has no compression to hide behind.
    if S::TRANSPOSE_AHEAD {
        transpose(0, even);
    }
    for step in 0..steps {
        // Ahead, this step reads one buffer while the next step fills the other.
        let (cur, next) = if S::TRANSPOSE_AHEAD && step % 2 == 1 {
            (&mut *odd, &mut *even)
        } else {
            (&mut *even, &mut *odd)
        };
        if !S::TRANSPOSE_AHEAD {
            transpose(step, cur);
        } else if step + 1 < steps {
            transpose(step + 1, next);
        }

        // Block `b` ends at byte `(b + 1) * 64`, after the shared prefix.
        let (set, b) = (step / n_blocks, step % n_blocks);
        let t = t_offset + ((b + 1) * BLOCK_LEN) as u64;
        // SAFETY: this step's transpose initialized every block of `cur`.
        let m = std::array::from_fn(|g| unsafe { cur[g].assume_init_ref() });
        // SAFETY: the blocks are initialized, and `h` is this set's chaining value.
        unsafe { S::compress_groups::<G>(&mut h, m, t, b + 1 == n_blocks) };

        // Last block of the set: write its digests, then restart for the next set.
        if b + 1 == n_blocks {
            for (g, hg) in h.iter().enumerate() {
                // SAFETY: the caller guarantees the output window of every set.
                unsafe { S::store_digests(hg, out.add((set * G + g) * S::WIDTH * OUT_LEN)) };
            }
            h = fresh();
        }
    }
}

/// Hash a whole batch: sets, then single groups, then scalar.
///
/// # Safety
///
/// - `data` must hold `n * len` bytes, and `out` must hold `n * OUT_LEN`.
/// - `len` must be a nonzero multiple of 64.
#[inline(always)]
pub(super) unsafe fn hash_many_with<S: Lanes32>(
    data: &[u8],
    len: usize,
    state: &[u32; 8],
    t_offset: u64,
    out: &mut [u8],
) {
    // The walk needs the group count as a const generic.
    match S::GROUPS {
        1 => unsafe { hash_many_grouped::<S, 1>(data, len, state, t_offset, out) },
        2 => unsafe { hash_many_grouped::<S, 2>(data, len, state, t_offset, out) },
        4 => unsafe { hash_many_grouped::<S, 4>(data, len, state, t_offset, out) },
        _ => unreachable!("GROUPS is 1, 2 or 4"),
    }
}

/// The batch driver with the backend's group count as a constant.
///
/// # Safety
///
/// As the batch driver.
#[inline(always)]
unsafe fn hash_many_grouped<S: Lanes32, const G: usize>(
    data: &[u8],
    len: usize,
    state: &[u32; 8],
    t_offset: u64,
    out: &mut [u8],
) {
    // 50 inputs on AVX-512 (16 lanes, 2 groups per set):
    //
    //     [ set: 32 ][ group: 16 ][ scalar: 2 ]
    let n = out.len() / OUT_LEN;
    let (sets, groups) = (n / (G * S::WIDTH), n % (G * S::WIDTH) / S::WIDTH);
    let (src, dst) = (data.as_ptr(), out.as_mut_ptr());
    // SAFETY: the sets, then the groups after them, stay inside `data` and `out`.
    unsafe {
        hash_sets::<S, G>(src, sets, len, state, t_offset, dst);
        let i = sets * G * S::WIDTH;
        hash_sets::<S, 1>(src.add(i * len), groups, len, state, t_offset, dst.add(i * OUT_LEN));
    }
    // Fewer than one group left: one input at a time.
    let i = (sets * G + groups) * S::WIDTH;
    for i in i..n {
        let d = hash_from_state(&data[i * len..(i + 1) * len], state, t_offset);
        out[i * OUT_LEN..(i + 1) * OUT_LEN].copy_from_slice(&d);
    }
}
