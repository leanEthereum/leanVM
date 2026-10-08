//! AVX2/VPCLMULQDQ lane-major copies. Half h contains elements 2h and 2h+1.
//! Iterator/array closures are spelled as bounded loops; pointer helpers are trusted explicitly.
use super::*;

verus! {
pub type Lanes4 = [[__m256i; 2]; 2];
pub type Wide4 = [[__m256i; 3]; 2];
pub type MixedAcc8 = [[__m256i; 6]; 2];

pub open spec fn half_elem(l: [__m256i; 2], i: int) -> F192 {
    F192 { c0: m256(l[0])[2*i], c1: m256(l[0])[2*i+1], c2: m256(l[1])[2*i] }
}
pub open spec fn half_ok(l: [__m256i; 2]) -> bool {
    forall|i: int| 0 <= i < 2 ==> #[trigger] m256(l[1])[2*i+1] == m256(l[1])[2*i]
}
pub open spec fn half_wide(d: [__m256i; 3], i: int) -> F192Unreduced {
    F192Unreduced { coeffs: [[m256(d[0])[2*i], m256(d[0])[2*i+1]],
        [m256(d[1])[2*i], m256(d[1])[2*i+1]], [m256(d[2])[2*i], m256(d[2])[2*i+1]]] }
}
pub open spec fn lanes4_elem(l: Lanes4, i: int) -> F192 { half_elem(l[i/2], i%2) }
pub open spec fn lanes4_ok(l: Lanes4) -> bool { half_ok(l[0]) && half_ok(l[1]) }
pub open spec fn wide4_value(d: Wide4, i: int) -> F192Unreduced { half_wide(d[i/2], i%2) }
pub open spec fn wide4_sum(d: Wide4) -> F192 {
    e_add(e_add(e_add(e_value(wide4_value(d,0)), e_value(wide4_value(d,1))),
        e_value(wide4_value(d,2))), e_value(wide4_value(d,3)))
}
pub open spec fn acc8_row(a: MixedAcc8, i: int) -> F192Unreduced {
    let h = i/4;
    let j = (i%4)/2;
    F192Unreduced { coeffs: [
        [m256(a[h][acc_reg(i,0)])[2*j], m256(a[h][acc_reg(i,0)])[2*j+1]],
        [m256(a[h][acc_reg(i,1)])[2*j], m256(a[h][acc_reg(i,1)])[2*j+1]],
        [m256(a[h][acc_reg(i,2)])[2*j], m256(a[h][acc_reg(i,2)])[2*j+1]]] }
}

#[inline]
pub unsafe fn lanes4(v: [F192; 4]) -> (r: Lanes4)
    ensures lanes4_ok(r), forall|i: int| 0 <= i < 4 ==> #[trigger] lanes4_elem(r,i) == v[i],
{
    proof { lemma_i64_round_trip_all(); }
    let half = |a: F192, b: F192| -> (r: [__m256i; 2])
        ensures half_ok(r), half_elem(r,0) == a, half_elem(r,1) == b,
    {
        [_mm256_set_epi64x(b.c1 as i64,b.c0 as i64,a.c1 as i64,a.c0 as i64),
         _mm256_set_epi64x(b.c2 as i64,b.c2 as i64,a.c2 as i64,a.c2 as i64)]
    };
    [half(v[0],v[1]),half(v[2],v[3])]
}

/// Trusted pointer loads only, before the production permutation.
#[verifier::external_body]
pub fn load_half(v: &[F192;4], h: usize) -> (r: (__m256i, __m256d))
    requires h < 2,
    ensures
        m256(r.0) == [v[2*h].c0,v[2*h].c1,v[2*h+1].c0,v[2*h+1].c1],
        m256d(r.1) == [v[2*h].c2,v[2*h+1].c0,v[2*h+1].c1,v[2*h+1].c2],
{
    unsafe {
        let w = v.as_ptr().cast::<i64>().add(6*h);
        (_mm256_loadu2_m128i(w.add(3).cast(),w.cast()),_mm256_loadu_pd(w.add(2).cast()))
    }
}
#[inline]
pub unsafe fn load_lanes4(v: &[F192;4]) -> (r: Lanes4)
    ensures lanes4_ok(r), forall|i: int| 0 <= i < 4 ==> #[trigger] lanes4_elem(r,i) == v[i],
{
    let half = |h: usize| -> (r: [__m256i;2])
        requires h < 2,
        ensures half_ok(r), forall|i: int| 0 <= i < 2 ==> #[trigger] half_elem(r,i) == v[2*h+i],
    {
        proof { assert((2u64 >> 1u64) & 1u64 == 1u64 && (0u64 >> 1u64) & 1u64 == 0u64) by (bit_vector); }
        let (c01, tail) = load_half(v,h);
        let c22 = _mm256_permutevar_pd(tail,_mm256_set_epi64x(2,2,0,0));
        [c01,_mm256_castpd_si256(c22)]
    };
    [half(0),half(1)]
}

/// Trusted two stores for one six-word half. Other slots are preserved.
#[verifier::external_body]
pub fn store_half(out: &mut [MaybeUninit<F192>;4], h: usize, head: __m128i, tail: __m256i)
    requires h < 2,
    ensures
        final(out)[2*h].mem_contents() == MemContents::Init(F192 { c0:m128(head)[0],c1:m128(head)[1],c2:m256(tail)[0] }),
        final(out)[2*h+1].mem_contents() == MemContents::Init(F192 { c0:m256(tail)[1],c1:m256(tail)[2],c2:m256(tail)[3] }),
        forall|i: int| 0 <= i < 4 && !(2*h <= i < 2*h+2) ==> #[trigger] final(out)[i].mem_contents() == old(out)[i].mem_contents(),
{
    unsafe {
        let w = out.as_mut_ptr().cast::<i64>().add(6*h);
        _mm_storeu_si128(w.cast(),head);
        _mm256_storeu_si256(w.add(2).cast(),tail);
    }
}
pub proof fn lemma_move_selectors()
    ensures
        ((0xF8u8 >> 2u8) & 3u8) == 2u8, ((0xF8u8 >> 4u8) & 3u8) == 3u8,
        (0xC3u8 & 1u8) == 1u8, ((0xC3u8 >> 1u8) & 1u8) == 1u8,
        ((0xC3u8 >> 2u8) & 1u8) == 0u8, ((0xC3u8 >> 3u8) & 1u8) == 0u8,
        ((0xC3u8 >> 4u8) & 1u8) == 0u8, ((0xC3u8 >> 5u8) & 1u8) == 0u8,
        ((0xC3u8 >> 6u8) & 1u8) == 1u8, ((0xC3u8 >> 7u8) & 1u8) == 1u8,
        (0x20u8 & 15u8) == 0u8, ((0x20u8 >> 4u8) & 15u8) == 2u8,
        (0x31u8 & 15u8) == 1u8, ((0x31u8 >> 4u8) & 15u8) == 3u8,
        (0u8 & 8u8) == 0u8, (1u8 & 8u8) == 0u8, (2u8 & 8u8) == 0u8, (3u8 & 8u8) == 0u8,
        (0u8 & 3u8) == 0u8, (1u8 & 3u8) == 1u8, (2u8 & 3u8) == 2u8, (3u8 & 3u8) == 3u8,
        ((0xC3u8 >> 0u8) & 1u8) == 1u8,
        ((0x20u8 >> 0u8) & 15u8) == 0u8, ((0x31u8 >> 0u8) & 15u8) == 1u8,
{
    assert(((0xC3u8 >> 0u8) & 1u8) == 1u8 && ((0x20u8 >> 0u8) & 15u8) == 0u8
        && ((0x31u8 >> 0u8) & 15u8) == 1u8) by (bit_vector);
    assert(((0xF8u8 >> 2u8) & 3u8) == 2u8 && ((0xF8u8 >> 4u8) & 3u8) == 3u8) by (bit_vector);
    assert((0xC3u8 & 1u8) == 1u8 && ((0xC3u8 >> 1u8) & 1u8) == 1u8
        && ((0xC3u8 >> 2u8) & 1u8) == 0u8 && ((0xC3u8 >> 3u8) & 1u8) == 0u8
        && ((0xC3u8 >> 4u8) & 1u8) == 0u8 && ((0xC3u8 >> 5u8) & 1u8) == 0u8
        && ((0xC3u8 >> 6u8) & 1u8) == 1u8 && ((0xC3u8 >> 7u8) & 1u8) == 1u8) by (bit_vector);
    assert((0x20u8 & 15u8) == 0u8 && ((0x20u8 >> 4u8) & 15u8) == 2u8
        && (0x31u8 & 15u8) == 1u8 && ((0x31u8 >> 4u8) & 15u8) == 3u8) by (bit_vector);
    assert((0u8 & 8u8) == 0u8 && (1u8 & 8u8) == 0u8 && (2u8 & 8u8) == 0u8 && (3u8 & 8u8) == 0u8
        && (0u8 & 3u8) == 0u8 && (1u8 & 3u8) == 1u8 && (2u8 & 3u8) == 2u8 && (3u8 & 3u8) == 3u8) by (bit_vector);
}

#[inline]
pub unsafe fn store_lanes4(lanes: Lanes4, out: &mut [MaybeUninit<F192>;4])
    requires lanes4_ok(lanes),
    ensures forall|i: int| 0 <= i < 4 ==> #[trigger] final(out)[i].mem_contents() == MemContents::Init(lanes4_elem(lanes,i)),
{
    for h in 0..2usize
        invariant lanes4_ok(lanes),
            forall|i: int| 0 <= i < 2*h ==> #[trigger] out[i].mem_contents() == MemContents::Init(lanes4_elem(lanes,i)),
    {
        let (c01,c22) = (lanes[h][0],lanes[h][1]);
        let perm = _mm256_permute4x64_epi64::<0xF8>(c01);
        let tail = _mm256_blend_epi32::<0xC3>(perm,c22);
        proof {
            lemma_move_selectors();
            assert(half_ok(lanes[h as int]));
            assert(m256(perm)[1] == m256(c01)[2] && m256(perm)[2] == m256(c01)[3]);
            let (a,b,c,d) = (m256(c22)[0],m256(perm)[1],m256(perm)[2],m256(c22)[3]);
            assert((a & 0xFFFF_FFFFu64) | (a & 0xFFFF_FFFF_0000_0000u64) == a
                && (b & 0xFFFF_FFFFu64) | (b & 0xFFFF_FFFF_0000_0000u64) == b
                && (c & 0xFFFF_FFFFu64) | (c & 0xFFFF_FFFF_0000_0000u64) == c
                && (d & 0xFFFF_FFFFu64) | (d & 0xFFFF_FFFF_0000_0000u64) == d) by (bit_vector);
            assert(blend_epi32_lane(m256(perm)@,m256(c22)@,0xC3,0) == a);
            assert(blend_epi32_lane(m256(perm)@,m256(c22)@,0xC3,1) == b);
            assert(blend_epi32_lane(m256(perm)@,m256(c22)@,0xC3,2) == c);
            assert(blend_epi32_lane(m256(perm)@,m256(c22)@,0xC3,3) == d);
            assert(m256(tail)[0] == m256(c22)[0] && m256(tail)[1] == m256(c01)[2]
                && m256(tail)[2] == m256(c01)[3] && m256(tail)[3] == m256(c22)[3]);
        }
        store_half(out,h,_mm256_castsi256_si128(c01),tail);
    }
}

#[inline]
pub unsafe fn transpose_lanes4(rows: [Lanes4;4]) -> (r: [Lanes4;4])
    ensures
        forall|i: int,h: int,p: int,x: int| 0 <= i < 4 && 0 <= h < 2 && 0 <= p < 2 && 0 <= x < 4 ==>
            #[trigger] m256(r[i][h][p])[x] == m256(rows[2*h+x/2][i/2][p])[2*(i%2)+x%2],
        forall|i: int,j: int| 0 <= i < 4 && 0 <= j < 4 ==> #[trigger] lanes4_elem(r[i],j) == lanes4_elem(rows[j],i),
        (forall|i: int| 0 <= i < 4 ==> #[trigger] lanes4_ok(rows[i])) ==> forall|i: int| 0 <= i < 4 ==> #[trigger] lanes4_ok(r[i]),
{
    let pick = |i: usize,h: usize,p: usize| -> (r: __m256i)
        requires i < 4,h < 2,p < 2,
        ensures forall|x: int| 0 <= x < 4 ==> #[trigger] m256(r)[x] == m256(rows[2*h+x/2][(i/2) as int][p as int])[2*(i%2)+x%2],
    {
        let (a,b) = (rows[2*h][i/2][p],rows[2*h+1][i/2][p]);
        proof { lemma_move_selectors(); }
        if i%2 == 0 {
            let r = _mm256_permute2x128_si256::<0x20>(a,b);
            proof {
                assert(m256(r)[0] == m256(a)[0]); assert(m256(r)[1] == m256(a)[1]);
                assert(m256(r)[2] == m256(b)[0]); assert(m256(r)[3] == m256(b)[1]);
            }
            r
        } else {
            let r = _mm256_permute2x128_si256::<0x31>(a,b);
            proof {
                assert(m256(r)[0] == m256(a)[2]); assert(m256(r)[1] == m256(a)[3]);
                assert(m256(r)[2] == m256(b)[2]); assert(m256(r)[3] == m256(b)[3]);
            }
            r
        }
    };
    let mut r = rows;
    for i in 0..4usize
        invariant
            forall|a: usize,h: usize,p: usize| a < 4 && h < 2 && p < 2 ==> #[trigger] pick.requires((a,h,p)),
            forall|a: usize,h: usize,p: usize,v: __m256i| a < 4 && h < 2 && p < 2 && #[trigger] pick.ensures((a,h,p),v) ==>
                forall|x: int| 0 <= x < 4 ==> #[trigger] m256(v)[x] == m256(rows[2*h+x/2][(a/2) as int][p as int])[2*(a%2)+x%2],
            forall|a: int,h: int,p: int,x: int| 0 <= a < i && 0 <= h < 2 && 0 <= p < 2 && 0 <= x < 4 ==>
                #[trigger] m256(r[a][h][p])[x] == m256(rows[2*h+x/2][a/2][p])[2*(a%2)+x%2],
    {
        r[i] = [[pick(i,0,0),pick(i,0,1)],[pick(i,1,0),pick(i,1,1)]];
    }
    proof {
        assert forall|i: int,j: int| 0 <= i < 4 && 0 <= j < 4 implies #[trigger] lanes4_elem(r[i],j) == lanes4_elem(rows[j],i) by {
            assert(m256(r[i][j/2][0])[2*(j%2)] == m256(rows[j][i/2][0])[2*(i%2)]);
            assert(m256(r[i][j/2][0])[2*(j%2)+1] == m256(rows[j][i/2][0])[2*(i%2)+1]);
            assert(m256(r[i][j/2][1])[2*(j%2)] == m256(rows[j][i/2][1])[2*(i%2)]);
        }
        if forall|i: int| 0 <= i < 4 ==> #[trigger] lanes4_ok(rows[i]) {
            assert forall|i: int| 0 <= i < 4 implies #[trigger] lanes4_ok(r[i]) by {
                assert forall|h: int,j: int| 0 <= h < 2 && 0 <= j < 2 implies
                    #[trigger] m256(r[i][h][1])[2*j+1] == m256(r[i][h][1])[2*j] by {
                    assert(lanes4_ok(rows[2*h+j]));
                    assert(half_ok(rows[2*h+j][i/2]));
                    assert(m256(rows[2*h+j][i/2][1])[2*(i%2)+1] == m256(rows[2*h+j][i/2][1])[2*(i%2)]);
                    assert(m256(r[i][h][1])[2*j+1] == m256(rows[2*h+j][i/2][1])[2*(i%2)+1]);
                    assert(m256(r[i][h][1])[2*j] == m256(rows[2*h+j][i/2][1])[2*(i%2)]);
                }
            }
        }
    }
    r
}

pub open spec fn lanes_xor<const N: usize>(a: [[__m256i;N];2],b: [[__m256i;N];2],r: [[__m256i;N];2]) -> bool {
    forall|h: int,i: int,x: int| 0 <= h < 2 && 0 <= i < N && 0 <= x < 4 ==> #[trigger] m256(r[h][i])[x] == m256(a[h][i])[x] ^ m256(b[h][i])[x]
}
#[inline]
pub unsafe fn xor_lanes<const N: usize>(a: [[__m256i;N];2],b: [[__m256i;N];2]) -> (r: [[__m256i;N];2])
    ensures lanes_xor(a,b,r),
{
    let mut r = a;
    for h in 0..2usize
        invariant forall|g: int,i: int,x: int| 0 <= g < h && 0 <= i < N && 0 <= x < 4 ==> #[trigger] m256(r[g][i])[x] == m256(a[g][i])[x] ^ m256(b[g][i])[x],
    {
        let mut half = a[h];
        for i in 0..N
            invariant h < 2,
                forall|j: int,x: int| 0 <= j < i && 0 <= x < 4 ==> #[trigger] m256(half[j])[x] == m256(a[h as int][j])[x] ^ m256(b[h as int][j])[x],
        { half[i] = _mm256_xor_si256(a[h][i],b[h][i]); }
        r[h] = half;
    }
    r
}
pub proof fn lemma_lanes4_xor(a: Lanes4,b: Lanes4,r: Lanes4)
    requires lanes_xor(a,b,r),
    ensures forall|i: int| 0 <= i < 4 ==> #[trigger] lanes4_elem(r,i) == e_add(lanes4_elem(a,i),lanes4_elem(b,i)),
        lanes4_ok(a) && lanes4_ok(b) ==> lanes4_ok(r),
{}
pub proof fn lemma_wide4_xor(a: Wide4,b: Wide4,r: Wide4)
    requires lanes_xor(a,b,r),
    ensures forall|i: int| 0 <= i < 4 ==> #[trigger] wide4_value(r,i) == u_xor(wide4_value(a,i),wide4_value(b,i)),
{}
pub proof fn lemma_zeroed_wide4()
    ensures forall|i: int| 0 <= i < 4 ==> #[trigger] wide4_value(zeroed_value::<Wide4>(),i) == F192Unreduced::ZERO,
{ axiom_zeroed_m256_pairs::<3>(); }
pub proof fn lemma_zeroed_acc8()
    ensures forall|i: int| 0 <= i < 8 ==> #[trigger] acc8_row(zeroed_value::<MixedAcc8>(),i) == F192Unreduced::ZERO,
{ axiom_zeroed_m256_pairs::<6>(); }

#[inline]
unsafe fn mul_half(a: [__m256i;2],b: [__m256i;2]) -> (r: [__m256i;3])
    requires half_ok(a),half_ok(b),
    ensures forall|i: int| 0 <= i < 2 ==> #[trigger] half_wide(r,i) == prod_unreduced(half_elem(a,i),half_elem(b,i)),
{
    proof { lemma_clmul_sel(); lemma_cw_all(); }
    let (a01,a22,b01,b22) = (a[0],a[1],b[0],b[1]);
    let (a_s,b_s) = (_mm256_xor_si256(a01,a22),_mm256_xor_si256(b01,b22));
    let a_x = _mm256_xor_si256(a01,_mm256_shuffle_epi32::<0x4E>(a01));
    let b_x = _mm256_xor_si256(b01,_mm256_shuffle_epi32::<0x4E>(b01));
    let p0 = _mm256_clmulepi64_epi128::<0x00>(a01,b01);
    let p1 = _mm256_clmulepi64_epi128::<0x11>(a01,b01);
    let p2 = _mm256_clmulepi64_epi128::<0x00>(a22,b22);
    let p01 = _mm256_clmulepi64_epi128::<0x00>(a_x,b_x);
    let p02 = _mm256_clmulepi64_epi128::<0x00>(a_s,b_s);
    let p12 = _mm256_clmulepi64_epi128::<0x11>(a_s,b_s);
    let xor = |x: __m256i,y: __m256i| -> (z: __m256i)
        ensures forall|i: int| 0 <= i < 4 ==> #[trigger] m256(z)[i] == m256(x)[i] ^ m256(y)[i],
    { _mm256_xor_si256(x,y) };
    let r = fold(p0,p1,p2,p01,p02,p12,xor);
    proof {
        lemma_fold(xor,|v: __m256i| m256(v)@,4,p0,p1,p2,p01,p02,p12,r);
        assert forall|i: int| 0 <= i < 2 implies #[trigger] half_wide(r,i) == prod_unreduced(half_elem(a,i),half_elem(b,i)) by {
            let (x,y) = (half_elem(a,i),half_elem(b,i));
            lemma_karatsuba_words(x,y);
            lemma_swap_words(m256(a01)@,2*i);
            lemma_swap_words(m256(b01)@,2*i);
            assert(m256(a22)[2*i+1] == x.c2 && m256(b22)[2*i+1] == y.c2);
            assert(m256(a_x)[2*i] == x.c0 ^ x.c1 && m256(b_x)[2*i] == y.c0 ^ y.c1);
            assert forall|k: int,w: int| 0 <= k < 3 && 0 <= w < 2 implies #[trigger] half_wide(r,i).coeffs[k][w] == prod_unreduced(x,y).coeffs[k][w] by {
                assert((2*i+w)/2 == i && (2*i+w)%2 == w);
                assert(m256(p0)[2*i+w] == cw(x.c0,y.c0,w));
                assert(m256(p1)[2*i+w] == cw(x.c1,y.c1,w));
                assert(m256(p2)[2*i+w] == cw(x.c2,y.c2,w));
                assert(m256(p01)[2*i+w] == cw(x.c0^x.c1,y.c0^y.c1,w));
                assert(m256(p02)[2*i+w] == cw(x.c0^x.c2,y.c0^y.c2,w));
                assert(m256(p12)[2*i+w] == cw(x.c1^x.c2,y.c1^y.c2,w));
                assert(m256(r[k])[2*i+w] == kara_word(x,y,k,w));
                assert(prod_unreduced(x,y).coeffs[k][w] == split(prod_coeffs(x,y)[k])[w]);
                assert(half_wide(r,i).coeffs[k][w] == m256(r[k])[2*i+w]);
            }
            lemma_unreduced_ext(half_wide(r,i),prod_unreduced(x,y));
        }
    }
    r
}
pub unsafe fn mul_lanes4(a: Lanes4,b: Lanes4) -> (r: Wide4)
    requires lanes4_ok(a),lanes4_ok(b),
    ensures forall|i: int| 0 <= i < 4 ==> #[trigger] wide4_value(r,i) == prod_unreduced(lanes4_elem(a,i),lanes4_elem(b,i)),
{ [mul_half(a[0],b[0]),mul_half(a[1],b[1])] }

unsafe fn reduce_half(d: [__m256i;3]) -> (r: [__m256i;2])
    ensures half_ok(r),forall|i: int| 0 <= i < 2 ==> #[trigger] half_elem(r,i) == e_value(half_wide(d,i)),
{
    let (d0,d1,d2) = (d[0],d[1],d[2]);
    let r = [reduce_lanes256(_mm256_unpacklo_epi64(d0,d1),_mm256_unpackhi_epi64(d0,d1)),
        reduce_lanes256(_mm256_unpacklo_epi64(d2,d2),_mm256_unpackhi_epi64(d2,d2))];
    proof {
        assert forall|i: int| 0 <= i < 2 implies #[trigger] half_elem(r,i) == e_value(half_wide(d,i)) by {
            assert(m256(r[0])[2*i] == reduce_word(m256(d0)[2*i],m256(d0)[2*i+1]));
            assert(m256(r[0])[2*i+1] == reduce_word(m256(d1)[2*i],m256(d1)[2*i+1]));
            assert(m256(r[1])[2*i] == reduce_word(m256(d2)[2*i],m256(d2)[2*i+1]));
        }
    }
    r
}
pub unsafe fn reduce_lanes4(d: Wide4) -> (r: Lanes4)
    ensures lanes4_ok(r),forall|i: int| 0 <= i < 4 ==> #[trigger] lanes4_elem(r,i) == e_value(wide4_value(d,i)),
{ [reduce_half(d[0]),reduce_half(d[1])] }

pub unsafe fn sum_lanes4(d: Wide4) -> (r: F192Unreduced)
    ensures e_value(r) == wide4_sum(d),
        r == u_xor(u_xor(u_xor(wide4_value(d,0),wide4_value(d,1)),wide4_value(d,2)),wide4_value(d,3)),
{
    proof { lemma_imm_one(); }
    let mut coeffs = [[0u64;2];3];
    for k in 0..3usize
        invariant forall|c: int,x: int| 0 <= c < k && 0 <= x < 2 ==> #[trigger] coeffs[c][x] ==
            m256(d[0][c])[x] ^ m256(d[0][c])[2+x] ^ m256(d[1][c])[x] ^ m256(d[1][c])[2+x],
    {
        proof { lemma_imm_one(); }
        let half = _mm256_xor_si256(d[0][k],d[1][k]);
        let low = _mm256_castsi256_si128(half);
        let high = _mm256_extracti128_si256::<1>(half);
        let q = _mm_xor_si128(low,high);
        coeffs[k] = transmute::<__m128i,[u64;2]>(q);
        proof {
            assert forall|x: int| 0 <= x < 2 implies coeffs[k as int][x] ==
                m256(d[0][k as int])[x] ^ m256(d[0][k as int])[2+x] ^ m256(d[1][k as int])[x] ^ m256(d[1][k as int])[2+x] by {
                assert(m128(q)[x] == m256(half)[x] ^ m256(half)[2+x]);
                assert(m256(half)[x] == m256(d[0][k as int])[x] ^ m256(d[1][k as int])[x]);
                assert(m256(half)[2+x] == m256(d[0][k as int])[2+x] ^ m256(d[1][k as int])[2+x]);
                let (a,b,c,e) = (m256(d[0][k as int])[x],m256(d[0][k as int])[2+x],m256(d[1][k as int])[x],m256(d[1][k as int])[2+x]);
                assert((a^c)^(b^e) == a^b^c^e) by (bit_vector);
            }
        }
    }
    let r = F192Unreduced { coeffs };
    proof {
        let (a,b,c,e) = (wide4_value(d,0),wide4_value(d,1),wide4_value(d,2),wide4_value(d,3));
        lemma_u_xor_words(a,b); lemma_u_xor_words(u_xor(a,b),c); lemma_u_xor_words(u_xor(u_xor(a,b),c),e);
        let s = u_xor(u_xor(u_xor(a,b),c),e);
        assert forall|k: int,x: int| 0 <= k < 3 && 0 <= x < 2 implies #[trigger] r.coeffs[k][x] == s.coeffs[k][x] by {
            assert(a.coeffs[k][x] == m256(d[0][k])[x]);
            assert(b.coeffs[k][x] == m256(d[0][k])[2+x]);
            assert(c.coeffs[k][x] == m256(d[1][k])[x]);
            assert(e.coeffs[k][x] == m256(d[1][k])[2+x]);
        }
        lemma_unreduced_ext(r,s);
        lemma_e_value_xor(a,b); lemma_e_value_xor(u_xor(a,b),c); lemma_e_value_xor(u_xor(u_xor(a,b),c),e);
    }
    r
}

unsafe fn mul_by_pairs256(lo: __m256i,hi: __m256i,c2: __m256i,k: __m256i) -> (r: [__m256i;6])
    ensures forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r[0])[i] == cw(m256(lo)[2*(i/2)],m256(k)[2*(i/2)],i%2),
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r[1])[i] == cw(m256(lo)[2*(i/2)+1],m256(k)[2*(i/2)],i%2),
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r[2])[i] == cw(m256(hi)[2*(i/2)],m256(k)[2*(i/2)+1],i%2),
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r[3])[i] == cw(m256(hi)[2*(i/2)+1],m256(k)[2*(i/2)+1],i%2),
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r[4])[i] == cw(m256(c2)[2*(i/2)],m256(k)[2*(i/2)],i%2),
        forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r[5])[i] == cw(m256(c2)[2*(i/2)+1],m256(k)[2*(i/2)+1],i%2),
{
    proof { lemma_clmul_sel(); lemma_cw_all(); }
    [_mm256_clmulepi64_epi128::<0x00>(lo,k),_mm256_clmulepi64_epi128::<0x01>(lo,k),
     _mm256_clmulepi64_epi128::<0x10>(hi,k),_mm256_clmulepi64_epi128::<0x11>(hi,k),
     _mm256_clmulepi64_epi128::<0x00>(c2,k),_mm256_clmulepi64_epi128::<0x11>(c2,k)]
}
/// Trusted unaligned load of four base scalars.
#[verifier::external_body]
pub fn load_k4(k: &[F64;8],h: usize) -> (r: __m256i)
    requires h < 2,
    ensures forall|i: int| 0 <= i < 4 ==> #[trigger] m256(r)[i] == k[4*h+i].0,
{ unsafe { _mm256_loadu_si256(k.as_ptr().add(4*h).cast()) } }

pub unsafe fn mul_base8_add(acc: &mut MixedAcc8,t: F192,k: [F64;8])
    ensures forall|i: int| 0 <= i < 8 ==> #[trigger] acc8_row(*final(acc),i) == u_xor(acc8_row(*old(acc),i),base_unreduced(t,k[i].0)),
{
    proof { lemma_i64_round_trip_all(); }
    let t01 = _mm256_broadcastsi128_si256(pair(t.c0,t.c1));
    let t2 = _mm256_set1_epi64x(t.c2 as i64);
    for h in 0..2usize
        invariant
            m256(t01) == [t.c0,t.c1,t.c0,t.c1], m256(t2) == [t.c2,t.c2,t.c2,t.c2],
            forall|g: int,c: int,x: int| h <= g < 2 && 0 <= c < 6 && 0 <= x < 4 ==> #[trigger] m256(acc[g][c])[x] == m256(old(acc)[g][c])[x],
            forall|i: int| 0 <= i < 4*h ==> #[trigger] acc8_row(*acc,i) == u_xor(acc8_row(*old(acc),i),base_unreduced(t,k[i].0)),
    {
        let kv = load_k4(&k,h);
        let p = mul_by_pairs256(t01,t01,t2,kv);
        let ghost before_update = *acc;
        let a = acc[h];
        acc[h] = [_mm256_xor_si256(a[0],p[0]),_mm256_xor_si256(a[1],p[1]),
            _mm256_xor_si256(a[2],p[2]),_mm256_xor_si256(a[3],p[3]),
            _mm256_xor_si256(a[4],p[4]),_mm256_xor_si256(a[5],p[5])];
        proof {
            assert forall|i: int| 0 <= i < 4*h implies #[trigger] acc8_row(*acc,i) == acc8_row(before_update,i) by {
                assert(i/4 < h);
            }
        }
        proof {
            assert forall|i: int| 4*h <= i < 4*h+4 implies #[trigger] acc8_row(*acc,i) == u_xor(acc8_row(*old(acc),i),base_unreduced(t,k[i].0)) by {
                lemma_base_words(t,k[i].0);
                let (before,after,b) = (acc8_row(*old(acc),i),acc8_row(*acc,i),base_unreduced(t,k[i].0));
                lemma_u_xor_words(before,b);
                assert(i/4 == h && 4*h+i%4 == i);
                assert forall|c: int,x: int| 0 <= c < 3 && 0 <= x < 2 implies #[trigger] after.coeffs[c][x] == u_xor(before,b).coeffs[c][x] by {
                    if i%2 == 0 {} else {}
                    if c == 0 {} else if c == 1 {} else {}
                    assert(m256(p[acc_reg(i,c)])[2*((i%4)/2)+x] == cw(coef(t,c),k[i].0,x));
                }
                lemma_unreduced_ext(after,u_xor(before,b));
            }
        }
    }
}

pub unsafe fn mul_base8_reduce(acc: MixedAcc8) -> (r: [F192;8])
    ensures forall|i: int| 0 <= i < 8 ==> #[trigger] r[i] == e_value(acc8_row(acc,i)),
{
    let mut r = [F192::ZERO;8];
    for h in 0..2usize
        invariant forall|i: int| 0 <= i < 4*h ==> #[trigger] r[i] == e_value(acc8_row(acc,i)),
    {
        let a = acc[h];
        let red = |x: __m256i,y: __m256i| -> (r: [u64;4])
            ensures forall|j: int| 0 <= j < 4 ==> #[trigger] r[j] == (if j%2 == 0 {
                reduce_word(m256(x)[j],m256(x)[j+1])
            } else { reduce_word(m256(y)[j-1],m256(y)[j]) }),
        {
            let lo = _mm256_unpacklo_epi64(x,y);
            let hi = _mm256_unpackhi_epi64(x,y);
            let v = reduce_lanes256(lo,hi);
            proof {
                assert forall|j: int| 0 <= j < 4 implies #[trigger] m256(v)[j] == (if j%2 == 0 {
                    reduce_word(m256(x)[j],m256(x)[j+1])
                } else { reduce_word(m256(y)[j-1],m256(y)[j]) }) by {
                    assert(m256(v)[j] == reduce_word(m256(lo)[j],m256(hi)[j]));
                    assert(m256(lo)[j] == unpacklo_lane(m256(x)@,m256(y)@,j));
                    assert(m256(hi)[j] == unpackhi_lane(m256(x)@,m256(y)@,j));
                }
            }
            let r = transmute::<__m256i,[u64;4]>(v);
            proof {
                assert(r == m256(v));
                assert forall|j: int| 0 <= j < 4 implies #[trigger] r[j] == (if j%2 == 0 {
                    reduce_word(m256(x)[j],m256(x)[j+1])
                } else { reduce_word(m256(y)[j-1],m256(y)[j]) }) by {
                    assert(m256(v)[j] == reduce_word(m256(lo)[j],m256(hi)[j]));
                }
            }
            r
        };
        let even = red(a[0],a[1]);
        let odd = red(a[2],a[3]);
        let c2 = red(a[4],a[5]);
        for i in 0..4usize
            invariant h < 2,
                forall|j: int| 0 <= j < 4*h+i ==> #[trigger] r[j] == e_value(acc8_row(acc,j)),
                forall|j: int| 0 <= j < 4 ==>
                    #[trigger] even[j] == reduce_word(m256(a[j%2])[2*(j/2)],m256(a[j%2])[2*(j/2)+1]),
                forall|j: int| 0 <= j < 4 ==>
                    #[trigger] odd[j] == reduce_word(m256(a[2+j%2])[2*(j/2)],m256(a[2+j%2])[2*(j/2)+1]),
                forall|j: int| 0 <= j < 4 ==>
                    #[trigger] c2[j] == reduce_word(m256(a[4+j%2])[2*(j/2)],m256(a[4+j%2])[2*(j/2)+1]),
                a == acc[h as int],
        {
            let w = if i%2 == 0 { even } else { odd };
            r[4*h+i] = F192::new(w[2*(i/2)],w[2*(i/2)+1],c2[i]);
        }
    }
    r
}
} // verus!
