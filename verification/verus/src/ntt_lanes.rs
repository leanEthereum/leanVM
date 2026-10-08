//! The lane-interleaved additive NTT transforms every lane independently.
//!
//! A buffer of `m` interleaved lanes holds lane `l`'s word `v` at word `m v + l` ([`lane`]). The layers of
//! `crate::ntt` act on such a buffer row by row, the same butterfly on every lane of a row pair; this module
//! proves that the lanes do not mix, so the single-lane theorems of `crate::ntt` hold lane by lane.
//!
//! Main results: [`lemma_lane_layer`] (one layer commutes with taking a lane), [`lemma_lane_forward_layers`]
//! and [`lemma_lane_inverse_layers`] (so do the forward and inverse transforms), and for
//! `AdditiveNttF64::standard(dim)` the evaluation theorems [`lemma_standard_lanes_forward_evaluates`]
//! (output word `m v + l` is lane `l`'s polynomial at the point `v`) and
//! [`lemma_standard_lanes_encode_evaluates`] (the encoder at rate `2^-r` Reed-Solomon encodes every lane).
//! No executable code: the copy these are about is `crate::ntt::forward_scalar_from_layer`, whose
//! postcondition is [`forward_layers`] for any lane count.
use crate::gf2_64::*;
use crate::ntt::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

/// Lane `l` of a buffer of `m` interleaved lanes: word `v` of the lane is word `m v + l` of the buffer.
pub open spec fn lane(data: Seq<F64>, m: nat, l: nat) -> Seq<F64> {
    Seq::new(data.len() / m, |v: int| data[(m as int) * v + (l as int)])
}

/// A lane of a buffer of `n` rows has `n` words.
pub proof fn lemma_lane_len(data: Seq<F64>, m: nat, l: nat, n: nat)
    requires
        m > 0,
        data.len() == n * m,
    ensures
        lane(data, m, l).len() == n,
{
    lemma_div_by_multiple(n as int, m as int);
}

/// Word `v` of a lane, `v = 2h b + r`, is word `(2h b + r) m + l` of the buffer, in block `b` and row `r`
/// of that block, both as a lane (`m = 1`) and in the buffer.
proof fn lemma_lane_word(v: int, m: nat, l: nat, h: nat)
    requires
        0 <= v,
        l < m,
        h > 0,
    ensures
        ({
            let (b, r) = (v / ((2 * h) as int), v % ((2 * h) as int));
            let p = (m as int) * v + (l as int);
            &&& 0 <= b
            &&& 0 <= r < 2 * h
            &&& v == (b * (2 * h) + r) * 1 + 0
            &&& p == (b * (2 * h) + r) * m + l
            &&& blk_of(v, 1, h) == b && r_of(v, 1, h) == r
            &&& blk_of(p, m, h) == b && r_of(p, m, h) == r
        }),
{
    let (b, r) = (v / ((2 * h) as int), v % ((2 * h) as int));
    lemma_fundamental_div_mod(v, (2 * h) as int);
    lemma_mod_pos_bound(v, (2 * h) as int);
    lemma_div_pos_is_pos(v, (2 * h) as int);
    assert(v == (b * (2 * h) + r) * 1 + 0) by (nonlinear_arith)
        requires
            v == (2 * h) * b + r,
    ;
    assert((m as int) * v + (l as int) == (b * (2 * h) + r) * m + l) by (nonlinear_arith)
        requires
            v == (2 * h) * b + r,
    ;
    lemma_compose(b, r, 0, 1, h);
    lemma_compose(b, r, l as int, m, h);
}

/// One layer of butterflies commutes with taking a lane: lane `l` of the layer's output is the same layer
/// applied to lane `l` alone, for either direction and any twiddles.
pub proof fn lemma_lane_layer(data: Seq<F64>, m: nat, l: nat, h: nat, nb: nat, tw: spec_fn(int) -> u64, inverse: bool)
    requires
        l < m,
        h > 0,
        data.len() == nb * (2 * h) * m,
    ensures
        lane(layer_map(data, m, h, tw, inverse), m, l) == layer_map(lane(data, m, l), 1, h, tw, inverse),
{
    let x = lane(data, m, l);
    let lhs = lane(layer_map(data, m, h, tw, inverse), m, l);
    let rhs = layer_map(x, 1, h, tw, inverse);
    lemma_lane_len(data, m, l, nb * (2 * h));
    lemma_lane_len(layer_map(data, m, h, tw, inverse), m, l, nb * (2 * h));
    assert forall|v: int| 0 <= v < x.len() implies lhs[v] == rhs[v] by {
        lemma_lane_word(v, m, l, h);
        let (b, r) = (v / ((2 * h) as int), v % ((2 * h) as int));
        let p = (m as int) * v + (l as int);
        assert(v < nb * (2 * h) * 1) by (nonlinear_arith)
            requires
                v < nb * (2 * h),
        ;
        lemma_blk_bound(v, 1, h, nb);
        lemma_bound(b, r, l as int, m, h, nb);
        assert(nb * (2 * h) * m == (nb * (2 * h)) * m) by (nonlinear_arith);
        if r < h {
            lemma_bound(b, r + h, l as int, m, h, nb);
            lemma_bound(b, r + h, 0, 1, h, nb);
            assert(p + h * m == (m as int) * (v + h) + (l as int)) by (nonlinear_arith)
                requires
                    p == (m as int) * v + (l as int),
            ;
            assert((b * (2 * h) + (r + h)) * m + l == p + h * m) by (nonlinear_arith)
                requires
                    p == (b * (2 * h) + r) * m + l,
            ;
            assert((b * (2 * h) + (r + h)) * 1 + 0 == v + h * 1) by (nonlinear_arith)
                requires
                    v == (b * (2 * h) + r) * 1 + 0,
            ;
            assert(x[v + h * 1] == data[p + h * m]);
        } else {
            assert(p - h * m == (m as int) * (v - h) + (l as int)) by (nonlinear_arith)
                requires
                    p == (m as int) * v + (l as int),
            ;
            assert(0 <= v - h) by (nonlinear_arith)
                requires
                    v == (b * (2 * h) + r) * 1 + 0,
                    r >= h,
                    b >= 0,
            ;
            assert(x[v - h * 1] == data[p - h * m]);
        }
    }
    assert(lhs =~= rhs);
}

/// The forward layers `start..end` commute with taking a lane: lane `l` of the output is the single-lane
/// transform of lane `l` of the input.
pub proof fn lemma_lane_forward_layers(
    tab: Seq<Seq<F64>>,
    data: Seq<F64>,
    m: nat,
    log_d: nat,
    start: nat,
    end: nat,
    l: nat,
)
    requires
        l < m,
        data.len() == m * pow2(log_d),
        end <= log_d,
    ensures
        lane(forward_layers(tab, data, m, log_d, start, end), m, l) == forward_layers(
            tab,
            lane(data, m, l),
            1,
            log_d,
            start,
            end,
        ),
    decreases end,
{
    if end > start {
        let layer = (end - 1) as nat;
        lemma_lane_forward_layers(tab, data, m, log_d, start, layer, l);
        let y = forward_layers(tab, data, m, log_d, start, layer);
        lemma_forward_layers_len(tab, data, m, log_d, start, layer);
        lemma_layer_shape(log_d, layer, m);
        lemma_lane_layer(y, m, l, layer_half(log_d, layer), pow2(layer), layer_twiddles(tab, layer), false);
    }
}

/// The inverse layers commute with taking a lane too.
pub proof fn lemma_lane_inverse_layers(tab: Seq<Seq<F64>>, data: Seq<F64>, m: nat, log_d: nat, lo: nat, l: nat)
    requires
        l < m,
        data.len() == m * pow2(log_d),
    ensures
        lane(inverse_layers(tab, data, m, log_d, lo), m, l) == inverse_layers(tab, lane(data, m, l), 1, log_d, lo),
    decreases log_d - lo,
{
    if lo < log_d {
        lemma_lane_inverse_layers(tab, data, m, log_d, lo + 1, l);
        let y = inverse_layers(tab, data, m, log_d, lo + 1);
        lemma_inverse_layers_len(tab, data, m, log_d, lo + 1);
        lemma_layer_shape(log_d, lo, m);
        lemma_lane_layer(y, m, l, layer_half(log_d, lo), pow2(lo), layer_twiddles(tab, lo), true);
    }
}

/// Word `m v + l` of a buffer of `n` rows is word `v` of lane `l`.
proof fn lemma_lane_index(data: Seq<F64>, m: nat, l: nat, n: nat, v: int)
    requires
        l < m,
        data.len() == n * m,
        0 <= v < n,
    ensures
        0 <= (m as int) * v + (l as int) < data.len(),
        lane(data, m, l)[v] == data[(m as int) * v + (l as int)],
{
    lemma_lane_len(data, m, l, n);
    assert((m as int) * v + (l as int) < n * m) by (nonlinear_arith)
        requires
            0 <= v < n,
            l < m,
    ;
    lemma_mul_nonnegative(m as int, v);
}

/// The lane-interleaved forward transform of `AdditiveNttF64::standard(dim)` evaluates every lane's
/// novel-basis polynomial on the domain `{0, .., 2^dim - 1}`: on `m` lanes of `2^dim` rows, output word
/// `m v + l` is `P_l(v) = Σ_{j < 2^dim} a_(m j + l) X_j(v)` ([`novel_sum`] of lane `l` of the input).
pub proof fn lemma_standard_lanes_forward_evaluates(tab: Seq<Seq<F64>>, dim: nat, m: nat, a: Seq<F64>)
    requires
        AdditiveNttF64::is_table_of(tab, standard_basis(dim)),
        1 <= dim <= 63,
        m > 0,
        a.len() == m * pow2(dim),
    ensures
        forall|v: int, l: int|
            0 <= v < pow2(dim) && 0 <= l < m ==> (#[trigger] forward_layers(tab, a, m, dim, 0, dim)[(m as int) * v
                + l]).0 == novel_sum(standard_basis(dim), lane(a, m, l as nat), dim, v as u64),
{
    let y = forward_layers(tab, a, m, dim, 0, dim);
    lemma_forward_layers_len(tab, a, m, dim, 0, dim);
    assert(a.len() == pow2(dim) * m) by (nonlinear_arith)
        requires
            a.len() == m * pow2(dim),
    ;
    assert forall|v: int, l: int| 0 <= v < pow2(dim) && 0 <= l < m implies (#[trigger] y[(m as int) * v + l]).0
        == novel_sum(standard_basis(dim), lane(a, m, l as nat), dim, v as u64) by {
        let x = lane(a, m, l as nat);
        lemma_lane_len(a, m, l as nat, pow2(dim));
        lemma_lane_forward_layers(tab, a, m, dim, 0, dim, l as nat);
        lemma_lane_index(y, m, l as nat, pow2(dim), v);
        lemma_standard_forward_evaluates(tab, dim, x);
        assert(forward_layers(tab, x, 1, dim, 0, dim)[v] == y[(m as int) * v + l]);
    }
}

/// Lane `l` of `n m` words of copies of an `m`-lane message is `n` words of copies of the message's lane `l`.
proof fn lemma_lane_replicate(msg: Seq<F64>, m: nat, l: nat, k: nat, n: nat)
    requires
        l < m,
        k > 0,
        msg.len() == m * k,
    ensures
        lane(replicate(msg, n * m), m, l) == replicate(lane(msg, m, l), n),
{
    let x = replicate(msg, n * m);
    let lm = lane(msg, m, l);
    lemma_lane_len(x, m, l, n);
    assert(msg.len() == k * m) by (nonlinear_arith)
        requires
            msg.len() == m * k,
    ;
    lemma_lane_len(msg, m, l, k);
    assert forall|v: int| 0 <= v < n implies #[trigger] lane(x, m, l)[v] == replicate(lm, n)[v] by {
        let (q, s) = (v / (k as int), v % (k as int));
        lemma_fundamental_div_mod(v, k as int);
        lemma_mod_pos_bound(v, k as int);
        lemma_div_pos_is_pos(v, k as int);
        let p = (m as int) * v + (l as int);
        assert(p == q * (m * k) + ((m as int) * s + l)) by (nonlinear_arith)
            requires
                v == k * q + s,
                p == (m as int) * v + (l as int),
        ;
        assert(0 <= (m as int) * s + l < m * k) by (nonlinear_arith)
            requires
                0 <= s < k,
                l < m,
        ;
        lemma_fundamental_div_mod_converse(p, (m * k) as int, q, (m as int) * s + l);
        lemma_lane_index(x, m, l, n, v);
        lemma_lane_index(msg, m, l, k, s);
    }
    assert(lane(x, m, l) =~= replicate(lm, n));
}

/// The lane-interleaved encoder of `AdditiveNttF64::standard(dim)` at rate `2^-r` Reed-Solomon encodes every
/// lane: on `2^r` copies of an `m`-lane message of `2^(dim - r)` rows, the layers `r..dim` give, at word
/// `m v + l`, `P_l(v)`, `P_l` the novel-basis polynomial whose coefficients are lane `l` of the message,
/// zero-padded (degree below `2^(dim - r)`).
pub proof fn lemma_standard_lanes_encode_evaluates(tab: Seq<Seq<F64>>, dim: nat, m: nat, msg: Seq<F64>, r: nat)
    requires
        AdditiveNttF64::is_table_of(tab, standard_basis(dim)),
        1 <= dim <= 63,
        r <= dim,
        m > 0,
        msg.len() == m * pow2((dim - r) as nat),
    ensures
        ({
            let codeword = forward_layers(tab, replicate(msg, m * pow2(dim)), m, dim, r, dim);
            &&& codeword.len() == m * pow2(dim)
            &&& forall|v: int, l: int|
                0 <= v < pow2(dim) && 0 <= l < m ==> (#[trigger] codeword[(m as int) * v + l]).0 == novel_sum(
                    standard_basis(dim),
                    zero_pad(lane(msg, m, l as nat), pow2(dim)),
                    dim,
                    v as u64,
                )
        }),
{
    let rep = replicate(msg, m * pow2(dim));
    let codeword = forward_layers(tab, rep, m, dim, r, dim);
    lemma_forward_layers_len(tab, rep, m, dim, r, dim);
    lemma_pow2_pos((dim - r) as nat);
    assert(m * pow2(dim) == pow2(dim) * m) by (nonlinear_arith);
    assert forall|v: int, l: int| 0 <= v < pow2(dim) && 0 <= l < m implies (#[trigger] codeword[(m as int) * v
        + l]).0 == novel_sum(standard_basis(dim), zero_pad(lane(msg, m, l as nat), pow2(dim)), dim, v as u64) by {
        let lm = lane(msg, m, l as nat);
        assert(msg.len() == pow2((dim - r) as nat) * m) by (nonlinear_arith)
            requires
                msg.len() == m * pow2((dim - r) as nat),
        ;
        lemma_lane_len(msg, m, l as nat, pow2((dim - r) as nat));
        lemma_lane_replicate(msg, m, l as nat, pow2((dim - r) as nat), pow2(dim));
        lemma_lane_forward_layers(tab, rep, m, dim, r, dim, l as nat);
        lemma_lane_index(codeword, m, l as nat, pow2(dim), v);
        lemma_standard_encode_evaluates(tab, dim, lm, r);
        let single = forward_layers(tab, replicate(lm, pow2(dim)), 1, dim, r, dim);
        assert(single[v] == codeword[(m as int) * v + l]);
    }
}

} // verus!
