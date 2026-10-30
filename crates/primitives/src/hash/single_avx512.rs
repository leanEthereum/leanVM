//! A single state in five vectors, following pi through rows, columns, and four line slopes.
//! Scaling the lane indices keeps the shuffles cyclic; four cycles restore the original layout.
//! The layout approach is inspired by temporalxyz/svm-vec:
//! <https://github.com/temporalxyz/svm-vec/blob/88faced4247742dafc0170ec027781af2c01a492/programs/keccak/build.rs>

use core::arch::x86_64::*;

type Point = [usize; 2];

const INV: [usize; 5] = [0, 1, 3, 2, 4];
// Phase 1 holds columns; the other phases hold y = slope * x + vector (mod 5).
const SLOPE: [usize; 6] = [0, 0, 3, 2, 4, 1];
// Lane j holds coordinate j / SCALE[round] (mod 5).
const SCALE: [usize; 25] = {
    let mut out = [1; 25];
    let mut r = 0;
    while r < 24 {
        out[r + 1] = out[r]
            * match r % 6 {
                0 => 3,
                1 => 1,
                phase => INV[SLOPE[phase]],
            }
            % 5;
        r += 1;
    }
    assert!(out[24] == 1);
    out
};

const fn mid_scale(round: usize) -> usize {
    if round % 6 == 1 {
        SCALE[round] * 2 % 5
    } else {
        SCALE[round] * INV[(2 + 3 * SLOPE[round % 6]) % 5] % 5
    }
}

const fn point(phase: usize, scale: usize, vector: usize, lane: usize, by_y: bool) -> Point {
    let coordinate = lane * INV[scale] % 5;
    if phase == 1 {
        [vector, coordinate]
    } else {
        let slope = SLOPE[phase];
        if by_y {
            [(INV[slope] * (coordinate + 5 - vector)) % 5, coordinate]
        } else {
            [coordinate, (slope * coordinate + vector) % 5]
        }
    }
}

const fn rho(round: usize, vector: usize) -> [u64; 8] {
    let mut out = [0; 8];
    let mut j = 0;
    while j < 5 {
        let [x, y] = point(round % 6, SCALE[round], vector, j, false);
        out[j] = super::RHO[x + 5 * y] as u64;
        j += 1;
    }
    out
}

#[derive(Clone, Copy)]
struct Map {
    source: usize,
    lanes: [u64; 8],
}

const fn pi_map(round: usize, vector: usize) -> Map {
    let next = (round + 1) % 6;
    let mut map = Map {
        source: 5,
        lanes: [0, 0, 0, 0, 0, 5, 6, 7],
    };
    let mut j = 0;
    while j < 5 {
        let scale = if next == 0 { SCALE[round + 1] } else { mid_scale(round) };
        let want = point(next, scale, vector, j, next != 0);
        let mut found = false;
        let mut k = 0;
        while k < 5 {
            let mut l = 0;
            while l < 5 {
                let [x, y] = point(round % 6, SCALE[round], k, l, false);
                if y == want[0] && (2 * x + 3 * y) % 5 == want[1] {
                    assert!(map.source == 5 || map.source == k);
                    map.source = k;
                    map.lanes[j] = l as u64;
                    found = true;
                }
                l += 1;
            }
            k += 1;
        }
        assert!(found);
        j += 1;
    }
    map
}

const fn x_map(round: usize, vector: usize) -> [u64; 8] {
    if (round + 1) % 6 <= 1 {
        return [0, 1, 2, 3, 4, 5, 6, 7];
    }
    let mut out = [0, 0, 0, 0, 0, 5, 6, 7];
    let mut j = 0;
    while j < 5 {
        out[j] = (mid_scale(round) * point((round + 1) % 6, SCALE[round + 1], vector, j, false)[1] % 5) as u64;
        j += 1;
    }
    out
}

// All coordinate searches and shuffle tables are evaluated at compile time.
const MAPS: [[Map; 5]; 24] = {
    let mut out = [[Map {
        source: 0,
        lanes: [0; 8],
    }; 5]; 24];
    let mut p = 0;
    while p < 24 {
        let mut k = 0;
        while k < 5 {
            out[p][k] = pi_map(p, k);
            k += 1;
        }
        p += 1;
    }
    out
};

const RHOS: [[[u64; 8]; 5]; 24] = {
    let mut out = [[[0; 8]; 5]; 24];
    let mut p = 0;
    while p < 24 {
        let mut k = 0;
        while k < 5 {
            out[p][k] = rho(p, k);
            k += 1;
        }
        p += 1;
    }
    out
};

const X_MAPS: [[[u64; 8]; 5]; 24] = {
    let mut out = [[[0; 8]; 5]; 24];
    let mut p = 0;
    while p < 24 {
        let mut k = 0;
        while k < 5 {
            out[p][k] = x_map(p, k);
            k += 1;
        }
        p += 1;
    }
    out
};

#[inline(always)]
fn indices(x: &[u64; 8]) -> __m512i {
    // SAFETY: the array holds a full vector, and this module requires AVX-512F.
    unsafe { _mm512_loadu_si512(x.as_ptr().cast()) }
}

#[inline(always)]
fn permute_lanes(v: __m512i, lanes: &[u64; 8]) -> __m512i {
    // SAFETY: this module requires AVX-512F.
    unsafe { _mm512_permutexvar_epi64(indices(lanes), v) }
}

#[inline(always)]
fn rotate_by(v: __m512i, n: usize) -> __m512i {
    let lanes = [
        (n % 5) as u64,
        ((n + 1) % 5) as u64,
        ((n + 2) % 5) as u64,
        ((n + 3) % 5) as u64,
        ((n + 4) % 5) as u64,
        5,
        6,
        7,
    ];
    permute_lanes(v, &lanes)
}

#[inline(always)]
fn round<const P: usize>(mut s: [__m512i; 5], rc: u64) -> [__m512i; 5] {
    // SAFETY: this module requires AVX-512F.
    unsafe {
        if P % 6 == 1 {
            let c: [__m512i; 5] = core::array::from_fn(|k| {
                let a = _mm512_xor_si512(s[k], rotate_by(s[k], 1));
                _mm512_ternarylogic_epi64::<0x96>(a, rotate_by(a, 2), rotate_by(s[k], 4))
            });
            s = core::array::from_fn(|k| {
                _mm512_ternarylogic_epi64::<0x96>(s[k], c[(k + 4) % 5], _mm512_rol_epi64::<1>(c[(k + 1) % 5]))
            });
        } else {
            let c = _mm512_ternarylogic_epi64::<0x96>(_mm512_ternarylogic_epi64::<0x96>(s[0], s[1], s[2]), s[3], s[4]);
            let prev = rotate_by(c, 5 - SCALE[P]);
            let next = _mm512_rol_epi64::<1>(rotate_by(c, SCALE[P]));
            s = s.map(|v| _mm512_ternarylogic_epi64::<0x96>(v, prev, next));
        }
        s = core::array::from_fn(|k| _mm512_rolv_epi64(s[k], indices(&RHOS[P][k])));
        let b: [__m512i; 5] = core::array::from_fn(|k| {
            let map = MAPS[P][k];
            permute_lanes(s[map.source], &map.lanes)
        });
        let next = (P + 1) % 6;
        if next == 0 {
            s = b.map(|v| {
                _mm512_ternarylogic_epi64::<0xd2>(v, rotate_by(v, SCALE[P + 1]), rotate_by(v, 2 * SCALE[P + 1]))
            });
        } else {
            let neighbor = if next == 1 { 1 } else { 5 - SLOPE[next] };
            s = core::array::from_fn(|k| {
                _mm512_ternarylogic_epi64::<0xd2>(b[k], b[(k + neighbor) % 5], b[(k + 2 * neighbor) % 5])
            });
        }
        s[0] = _mm512_xor_si512(s[0], _mm512_maskz_set1_epi64(1, rc as i64));
        if next > 1 {
            s = core::array::from_fn(|k| permute_lanes(s[k], &X_MAPS[P][k]));
        }
        s
    }
}

#[inline(never)]
pub(super) fn permute(state: &mut [u64; 25]) {
    // SAFETY: each masked access touches five lanes of the 25-lane state; AVX-512F is enabled.
    unsafe {
        let mut s = core::array::from_fn(|i| _mm512_maskz_loadu_epi64(0x1f, state.as_ptr().add(5 * i).cast()));
        s = round::<0>(s, super::RC[0]);
        s = round::<1>(s, super::RC[1]);
        s = round::<2>(s, super::RC[2]);
        s = round::<3>(s, super::RC[3]);
        s = round::<4>(s, super::RC[4]);
        s = round::<5>(s, super::RC[5]);
        s = round::<6>(s, super::RC[6]);
        s = round::<7>(s, super::RC[7]);
        s = round::<8>(s, super::RC[8]);
        s = round::<9>(s, super::RC[9]);
        s = round::<10>(s, super::RC[10]);
        s = round::<11>(s, super::RC[11]);
        s = round::<12>(s, super::RC[12]);
        s = round::<13>(s, super::RC[13]);
        s = round::<14>(s, super::RC[14]);
        s = round::<15>(s, super::RC[15]);
        s = round::<16>(s, super::RC[16]);
        s = round::<17>(s, super::RC[17]);
        s = round::<18>(s, super::RC[18]);
        s = round::<19>(s, super::RC[19]);
        s = round::<20>(s, super::RC[20]);
        s = round::<21>(s, super::RC[21]);
        s = round::<22>(s, super::RC[22]);
        s = round::<23>(s, super::RC[23]);
        for i in 0..5 {
            _mm512_mask_storeu_epi64(state.as_mut_ptr().add(5 * i).cast(), 0x1f, s[i]);
        }
    }
}
