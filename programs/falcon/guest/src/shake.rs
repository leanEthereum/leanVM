//! SHAKE256 over 64-bit lanes: the Keccak-f[1600] permutation and its sponge.
//!
//! rv64im has no rotate and no and-not, so a round is shifts, ORs, XORs and ANDs.

/// The rate: 136 bytes, 17 lanes, for SHAKE256's 256-bit capacity.
const RATE: usize = 17;

/// The round constants, which break the rounds' symmetry.
const ROUND_CONSTANTS: [u64; 24] = [
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
const COMPLEMENTED: [usize; 6] = [1, 2, 8, 12, 17, 20];

/// The Keccak-f[1600] permutation, lane `x + 5y` at index `x + 5 * y`.
///
/// XKCP's 64-bit round: plane by plane, theta, rho and pi fused into chi's inputs, the next round's column parities
/// summed from chi's outputs.
fn keccak_f1600(state: &mut [u64; 25]) {
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
/// Each output plane `y` is chi over five lanes of `a`, each XORed with its column's theta term and rotated by rho:
/// the lanes pi moves to plane `y`.
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

/// SHAKE256 absorbing whole 64-bit lanes: a message of whole words.
#[derive(Clone)]
pub struct Shake256 {
    /// The Keccak state.
    state: [u64; 25],
    /// The next lane of the rate to absorb into.
    lane: usize,
}

impl Shake256 {
    /// The empty sponge.
    pub const fn new() -> Self {
        Self {
            state: [0; 25],
            lane: 0,
        }
    }

    /// Absorb words, little-endian: each word is the next eight bytes.
    pub fn absorb(&mut self, words: &[u64]) {
        for &w in words {
            self.state[self.lane] ^= w;
            self.lane += 1;
            if self.lane == RATE {
                keccak_f1600(&mut self.state);
                self.lane = 0;
            }
        }
    }

    /// Pad and switch to squeezing.
    ///
    /// SHAKE's padding: the suffix bits `1111`, then `10*1`, at the byte after the message.
    pub fn finalize(mut self) -> Squeeze {
        self.state[self.lane] ^= 0x1F;
        self.state[RATE - 1] ^= 0x80 << 56;
        keccak_f1600(&mut self.state);
        Squeeze {
            state: self.state,
            lane: 0,
        }
    }
}

impl Default for Shake256 {
    fn default() -> Self {
        Self::new()
    }
}

/// SHAKE256's output, one lane at a time.
pub struct Squeeze {
    /// The Keccak state.
    state: [u64; 25],
    /// The next lane of the rate to output.
    lane: usize,
}

impl Squeeze {
    /// The next eight bytes of output, as a little-endian word.
    pub fn next_lane(&mut self) -> u64 {
        if self.lane == RATE {
            keccak_f1600(&mut self.state);
            self.lane = 0;
        }
        let lane = self.state[self.lane];
        self.lane += 1;
        lane
    }
}
