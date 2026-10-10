//! Keccak in software: the `Keccak-f[1600]` permutation, and keccak256 over it.
//!
//! The machine has no Keccak instruction, so this is ordinary code: on the VM the permutation is
//! `keccak_rv64.S`, the whole state in registers, and off it Rust.
//!
//! rv64im has no rotate and no and-not, so a round is shifts, ORs, XORs and ANDs.
//!
//! keccak256 is Ethereum's hash: `Keccak[c = 512]` with the original padding `10*1`, not SHA3-256's `0110*1`.

/// Lanes a sponge of capacity 512 absorbs per permutation: 136 bytes.
///
/// keccak256 and SHAKE256 share it.
pub const RATE: usize = 17;

/// keccak256 of the first `len` bytes of `words`, little-endian: each word is the next eight bytes.
///
/// Bytes of the last word past `len` are ignored.
///
/// # Panics
///
/// If `words` holds fewer than `len` bytes.
pub fn keccak256(words: &[u64], len: usize) -> [u64; 4] {
    let (full, tail) = (len / 8, len % 8);
    let mut state = [0; 25];
    // The message's whole words are lanes: XOR each into the rate, permuting once the rate is full.
    let mut lane = 0;
    for &w in &words[..full] {
        state[lane] ^= w;
        lane += 1;
        if lane == RATE {
            f1600(&mut state);
            lane = 0;
        }
    }

    // The last block: the message's partial lane, then the padding.
    //
    //     message bytes | 0x01 | 0x00 ... 0x00 | 0x80
    //                     ^ byte len % 136          ^ byte 135 of the block
    //
    // A message ending on byte 134 of a block puts both on byte 135: 0x81.
    //
    // The partial lane keeps only its `tail` message bytes: the word's other bytes are not the message's.
    let last = if tail == 0 {
        0
    } else {
        words[full] & ((1 << (8 * tail)) - 1)
    };
    state[lane] ^= last ^ (0x01 << (8 * tail));
    state[RATE - 1] ^= 0x80 << 56;
    f1600(&mut state);
    // The digest is the first 32 bytes of the state: four lanes.
    [state[0], state[1], state[2], state[3]]
}

/// The round constants, which break the rounds' symmetry.
static ROUND_CONSTANTS: [u64; 24] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808A,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808B,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008A,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000A,
    0x0000_0000_8000_808B,
    0x8000_0000_0000_008B,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800A,
    0x8000_0000_8000_000A,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

/// The lanes kept complemented through the rounds, `x + 5y` for `be bi go ki mi sa` (lane complementing).
///
/// With them complemented, chi needs one NOT per plane instead of one per lane.
#[cfg(not(target_arch = "riscv64"))]
const COMPLEMENTED: [usize; 6] = [1, 2, 8, 12, 17, 20];

/// The `Keccak-f[1600]` permutation, lane `x + 5y` at index `x + 5 * y`.
pub fn f1600(state: &mut [u64; 25]) {
    #[cfg(target_arch = "riscv64")]
    // SAFETY: the routine reads and writes the 25 lanes at `state` and nothing else but its own
    // stack frame, and restores every register the calling convention preserves.
    unsafe {
        leanvm_keccak_f1600(state);
    }
    #[cfg(not(target_arch = "riscv64"))]
    f1600_rust(state);
}

#[cfg(target_arch = "riscv64")]
core::arch::global_asm!(include_str!("keccak_rv64.S"), rc = sym ROUND_CONSTANTS);

#[cfg(target_arch = "riscv64")]
unsafe extern "C" {
    fn leanvm_keccak_f1600(state: *mut [u64; 25]);
}

/// The permutation in Rust, off the VM.
///
/// XKCP's 64-bit round, plane by plane:
///
/// - theta, rho and pi are fused into chi's inputs;
/// - the next round's column parities are summed from chi's outputs.
#[cfg(not(target_arch = "riscv64"))]
fn f1600_rust(state: &mut [u64; 25]) {
    let mut a = *state;
    for i in COMPLEMENTED {
        a[i] = !a[i];
    }
    let mut c: [u64; 5] = core::array::from_fn(|x| a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20]);
    let mut e = [0; 25];
    // Two rounds per step: the second maps the first's output back into `a`.
    for rc in ROUND_CONSTANTS.as_chunks::<2>().0 {
        c = round(&a, &mut e, c, rc[0]);
        c = round(&e, &mut a, c, rc[1]);
    }
    for i in COMPLEMENTED {
        a[i] = !a[i];
    }
    *state = a;
}

/// One round from `a` into `e`, given `a`'s column parities: returns `e`'s.
///
/// Each output plane `y` is chi over the five lanes pi moves to plane `y`.
///
/// Each lane is first XORed with its column's theta term, then rotated by rho.
#[cfg(not(target_arch = "riscv64"))]
#[inline(always)]
fn round(a: &[u64; 25], e: &mut [u64; 25], c: [u64; 5], rc: u64) -> [u64; 5] {
    let d: [u64; 5] = core::array::from_fn(|x| c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1));
    let b = |i: usize, x: usize, r: u32| (a[i] ^ d[x]).rotate_left(r);

    // Plane 0.
    let (ba, be, bi, bo, bu) = (b(0, 0, 0), b(6, 1, 44), b(12, 2, 43), b(18, 3, 21), b(24, 4, 14));
    e[0] = ba ^ (be | bi) ^ rc;
    e[1] = be ^ (!bi | bo);
    e[2] = bi ^ (bo & bu);
    e[3] = bo ^ (bu | ba);
    e[4] = bu ^ (ba & be);

    // Plane 1.
    let (ga, ge, gi, go, gu) = (b(3, 3, 28), b(9, 4, 20), b(10, 0, 3), b(16, 1, 45), b(22, 2, 61));
    e[5] = ga ^ (ge | gi);
    e[6] = ge ^ (gi & go);
    e[7] = gi ^ (go | !gu);
    e[8] = go ^ (gu | ga);
    e[9] = gu ^ (ga & ge);

    // Plane 2.
    let (ka, ke, ki, ko, ku) = (b(1, 1, 1), b(7, 2, 6), b(13, 3, 25), b(19, 4, 8), b(20, 0, 18));
    let not_ko = !ko;
    e[10] = ka ^ (ke | ki);
    e[11] = ke ^ (ki & ko);
    e[12] = ki ^ (not_ko & ku);
    e[13] = not_ko ^ (ku | ka);
    e[14] = ku ^ (ka & ke);

    // Plane 3.
    let (ma, me, mi, mo, mu) = (b(4, 4, 27), b(5, 0, 36), b(11, 1, 10), b(17, 2, 15), b(23, 3, 56));
    let not_mo = !mo;
    e[15] = ma ^ (me & mi);
    e[16] = me ^ (mi | mo);
    e[17] = mi ^ (not_mo | mu);
    e[18] = not_mo ^ (mu & ma);
    e[19] = mu ^ (ma | me);

    // Plane 4.
    let (sa, se, si, so, su) = (b(2, 2, 62), b(8, 3, 55), b(14, 4, 39), b(15, 0, 41), b(21, 1, 2));
    let not_se = !se;
    e[20] = sa ^ (not_se & si);
    e[21] = not_se ^ (si | so);
    e[22] = si ^ (so & su);
    e[23] = so ^ (su | sa);
    e[24] = su ^ (sa & se);

    core::array::from_fn(|x| e[x] ^ e[x + 5] ^ e[x + 10] ^ e[x + 15] ^ e[x + 20])
}
