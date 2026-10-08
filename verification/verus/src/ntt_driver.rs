//! Permission-backed executable refinement of the parallel additive NTT driver.
//! `run_layers`, `fused_rows` and row groups copy the portable production operations;
//! `transform` composes a caller-supplied gathered/deep plan on populated replicas.
//!
//! Memory is held as [`crate::parallel::owns`] permissions. Raw accesses require the
//! touched elements' permissions; distinct dispatched tasks receive disjoint maps.
//! The real pool's exactly-once joined dispatch is trusted, not proved. Production's
//! cache planner, fused replication, row sinks and streaming fences are not verified.
//! Function comments document rewrites; differential tests supply finite evidence only.
//!
//! Specification:
//!
//! - [`gather`]: rows `base + r + i * step` of a buffer, as a buffer of their own.
//! - [`sub_layers`]: the forward layers `first..end` of a `2^log_d`-row transform run on one of its
//!   `2^o` sub-blocks, which fixes the global block index, and so the twiddle, of each block.
//!
//! Main results: a layer commutes with a gather of rows it pairs among themselves
//! ([`lemma_gather_layer`], [`lemma_gather_sub_layers`]); `run_layers`, the fused groups and
//! `gathered_pass` run the layers they claim; `transform` computes [`forward_layers`], the specification of
//! the verified reference `forward_scalar_from_layer`.
// `global size_of usize` expands to a braced block.
#![allow(unused_braces)]

use crate::gf2_64::*;
use crate::ntt::*;
use crate::parallel;
use crate::parallel::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;
use vstd::arithmetic::power2::*;
use vstd::bits::*;
use vstd::prelude::*;
use vstd::raw_ptr::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// The index in the buffer of word `q` of a gather: row `base + r + (q / m) * step`, lane `q % m`.
pub open spec fn gidx(m: nat, base: int, r: int, step: int, q: int) -> int {
    (base + r + (q / (m as int)) * step) * (m as int) + q % (m as int)
}

/// Rows `base + r + i * step`, `i < cnt`, of a buffer of `m` lanes, as one buffer of `cnt` rows.
pub open spec fn gather(x: Seq<F64>, m: nat, base: int, r: int, step: int, cnt: nat) -> Seq<F64> {
    Seq::new(cnt * m, |q: int| x[gidx(m, base, r, step, q)])
}

/// The twiddles of one layer on sub-block `s` of `2^o`: block `b` of the sub-block is block
/// `s * 2^(layer - o) + b` of the domain.
pub open spec fn sub_twiddles(tab: Seq<Seq<F64>>, layer: nat, o: nat, s: int) -> spec_fn(int) -> u64 {
    |b: int| twiddle_spec(tab, layer, (s * pow2((layer - o) as nat) + b) as usize)
}

/// The forward layers `first..end` of a `2^log_d`-row transform on `m` lanes, run on its sub-block `s`
/// of `2^o` (`o <= first`), a buffer of `2^(log_d - o)` rows.
pub open spec fn sub_layers(
    tab: Seq<Seq<F64>>,
    x: Seq<F64>,
    m: nat,
    log_d: nat,
    o: nat,
    s: int,
    first: nat,
    end: nat,
) -> Seq<F64>
    decreases end,
{
    if end <= first {
        x
    } else {
        layer_map(
            sub_layers(tab, x, m, log_d, o, s, first, (end - 1) as nat),
            m,
            layer_half(log_d, (end - 1) as nat),
            sub_twiddles(tab, (end - 1) as nat, o, s),
            false,
        )
    }
}

// ---------------------------------------------------------------------------------------------
// Arithmetic
// ---------------------------------------------------------------------------------------------
/// Word `lane` of row `row` is word `row * m + lane`.
pub proof fn lemma_word(row: int, lane: int, m: int)
    requires
        m > 0,
        0 <= lane < m,
    ensures
        (row * m + lane) / m == row,
        (row * m + lane) % m == lane,
{
    lemma_fundamental_div_mod_converse(row * m + lane, m, row, lane);
}

/// Every word is `row * m + lane`.
pub proof fn lemma_split_word(q: int, m: int)
    requires
        m > 0,
        q >= 0,
    ensures
        q == (q / m) * m + q % m,
        q / m >= 0,
        0 <= q % m < m,
{
    lemma_fundamental_div_mod(q, m);
    lemma_mod_bound(q, m);
    lemma_div_pos_is_pos(q, m);
    lemma_mul_is_commutative(q / m, m);
}

/// Row `base + r + i * step`, with `base` a multiple of `2H = 2 k step` and `r < step`, lies in block
/// `base / 2H + i / 2k`, at row `(i % 2k) * step + r` of it: a top row exactly when `i % 2k < k`.
pub proof fn lemma_row_split(base: int, r: int, i: int, step: int, k: int)
    requires
        step > 0,
        0 <= r < step,
        k > 0,
        i >= 0,
        base >= 0,
        base % (2 * k * step) == 0,
    ensures
        (base + r + i * step) / (2 * k * step) == base / (2 * k * step) + i / (2 * k),
        (base + r + i * step) % (2 * k * step) == (i % (2 * k)) * step + r,
        ((i % (2 * k)) * step + r < k * step) == (i % (2 * k) < k),
{
    let h2 = 2 * k * step;
    assert(h2 > 0) by (nonlinear_arith)
        requires
            k > 0,
            step > 0,
            h2 == 2 * k * step,
    ;
    let a = i / (2 * k);
    let j = i % (2 * k);
    let c0 = base / h2;
    lemma_fundamental_div_mod(i, 2 * k);
    lemma_mod_bound(i, 2 * k);
    lemma_fundamental_div_mod(base, h2);
    assert(base + r + i * step == (c0 + a) * h2 + (j * step + r)) by (nonlinear_arith)
        requires
            i == (2 * k) * a + j,
            base == h2 * c0,
            h2 == 2 * k * step,
    ;
    assert(0 <= j * step + r < h2) by (nonlinear_arith)
        requires
            0 <= j < 2 * k,
            0 <= r < step,
            h2 == 2 * k * step,
    ;
    lemma_fundamental_div_mod_converse(base + r + i * step, h2, c0 + a, j * step + r);
    if j < k {
        assert(j * step + r < k * step) by (nonlinear_arith)
            requires
                0 <= j <= k - 1,
                r < step,
                step > 0,
        ;
    } else {
        assert(j * step + r >= k * step) by (nonlinear_arith)
            requires
                j >= k,
                r >= 0,
                step > 0,
        ;
    }
}

/// A word of a gather below `cnt` rows, and its partner rows `k` away.
proof fn lemma_gather_rows(q: int, m: int, cnt: int, k: int)
    requires
        m > 0,
        k > 0,
        cnt % (2 * k) == 0,
        0 <= q < cnt * m,
    ensures
        0 <= q / m < cnt,
        (q / m) % (2 * k) < k ==> q / m + k < cnt && q + k * m < cnt * m && (q + k * m) / m == q / m + k && (q + k * m) % m
            == q % m,
        (q / m) % (2 * k) >= k ==> q / m >= k && q - k * m >= 0 && (q - k * m) / m == q / m - k && (q - k * m) % m == q % m,
        (q / m) / (2 * k) < cnt / (2 * k),
{
    let i = q / m;
    let lane = q % m;
    lemma_split_word(q, m);
    assert(i < cnt) by (nonlinear_arith)
        requires
            q == i * m + lane,
            0 <= lane,
            q < cnt * m,
            m > 0,
    ;
    let a = i / (2 * k);
    let j = i % (2 * k);
    let c = cnt / (2 * k);
    lemma_fundamental_div_mod(i, 2 * k);
    lemma_mod_bound(i, 2 * k);
    lemma_fundamental_div_mod(cnt, 2 * k);
    assert(a < c) by (nonlinear_arith)
        requires
            i == (2 * k) * a + j,
            cnt == (2 * k) * c,
            0 <= j,
            i < cnt,
            k > 0,
    ;
    if j < k {
        assert(i + k < cnt) by (nonlinear_arith)
            requires
                i == (2 * k) * a + j,
                cnt == (2 * k) * c,
                0 <= j < k,
                a + 1 <= c,
                k > 0,
        ;
        assert(q + k * m == (i + k) * m + lane) by (nonlinear_arith)
            requires
                q == i * m + lane,
        ;
        lemma_word(i + k, lane, m);
        assert((i + k) * m + lane < cnt * m) by (nonlinear_arith)
            requires
                i + k + 1 <= cnt,
                lane < m,
                m > 0,
        ;
    } else {
        assert(q - k * m == (i - k) * m + lane) by (nonlinear_arith)
            requires
                q == i * m + lane,
        ;
        lemma_word(i - k, lane, m);
        assert((i - k) * m + lane >= 0) by (nonlinear_arith)
            requires
                i >= k,
                lane >= 0,
                m > 0,
        ;
    }
}

// ---------------------------------------------------------------------------------------------
// A layer commutes with a gather of the rows it pairs
// ---------------------------------------------------------------------------------------------
/// One layer of half `H = k * step`, gathered on rows `base + r + i * step` (`r < step`, `base` a multiple
/// of a block), is the layer of half `k` on the gathered buffer, with the twiddles of the blocks the
/// gathered rows come from.
pub proof fn lemma_gather_layer(
    x: Seq<F64>,
    m: nat,
    h: nat,
    tw: spec_fn(int) -> u64,
    tw2: spec_fn(int) -> u64,
    inverse: bool,
    base: int,
    r: int,
    step: int,
    cnt: nat,
    k: nat,
)
    requires
        m > 0,
        step > 0,
        0 <= r < step,
        k > 0,
        h == k * step,
        cnt % (2 * k) == 0,
        base >= 0,
        base % (2 * h as int) == 0,
        (base + cnt * step) * m <= x.len(),
        forall|b: int| 0 <= b < cnt / (2 * k) ==> #[trigger] tw2(b) == tw(base / (2 * h as int) + b),
    ensures
        gather(layer_map(x, m, h, tw, inverse), m, base, r, step, cnt) == layer_map(
            gather(x, m, base, r, step, cnt),
            m,
            k,
            tw2,
            inverse,
        ),
{
    let y = layer_map(x, m, h, tw, inverse);
    let g = gather(x, m, base, r, step, cnt);
    let lhs = gather(y, m, base, r, step, cnt);
    let rhs = layer_map(g, m, k, tw2, inverse);
    let mi = m as int;
    assert forall|q: int| 0 <= q < cnt * m implies lhs[q] == rhs[q] by {
        let i = q / mi;
        let lane = q % mi;
        lemma_split_word(q, mi);
        lemma_gather_rows(q, mi, cnt as int, k as int);
        let row = base + r + i * step;
        let p = row * mi + lane;
        assert(gidx(m, base, r, step, q) == p);
        lemma_word(row, lane, mi);
        assert(2 * h as int == 2 * (k as int) * step) by (nonlinear_arith)
            requires
                h == k * step,
        ;
        lemma_row_split(base, r, i, step, k as int);
        assert(row >= 0) by (nonlinear_arith)
            requires
                row == base + r + i * step,
                base >= 0,
                r >= 0,
                i >= 0,
                step > 0,
        ;
        assert(row + 1 <= base + cnt * step) by (nonlinear_arith)
            requires
                row == base + r + i * step,
                i + 1 <= cnt,
                0 <= r < step,
                step > 0,
        ;
        assert(p < x.len()) by (nonlinear_arith)
            requires
                p == row * mi + lane,
                row + 1 <= base + cnt * step,
                0 <= lane < mi,
                row >= 0,
                (base + cnt * step) * mi <= x.len(),
        ;
        assert(p >= 0) by (nonlinear_arith)
            requires
                p == row * mi + lane,
                row >= 0,
                lane >= 0,
                mi > 0,
        ;
        // The full layer at `p`: row `row`, block `base / 2H + i / 2k`, in-block row `(i % 2k) step + r`.
        assert(row_of(p, m) == row);
        assert(blk_of(p, m, h) == base / (2 * h as int) + i / (2 * k as int));
        assert(r_of(p, m, h) == (i % (2 * k as int)) * step + r);
        // The gathered layer at `q`: row `i`, block `i / 2k`, in-block row `i % 2k`.
        assert(row_of(q, m) == i);
        assert(blk_of(q, m, k) == i / (2 * k as int));
        assert(r_of(q, m, k) == i % (2 * k as int));
        assert(tw2(i / (2 * k as int)) == tw(base / (2 * h as int) + i / (2 * k as int)));
        if i % (2 * k as int) < k {
            let q2 = q + k * m;
            assert((row + k * step) * mi == row * mi + (k * step) * mi) by (nonlinear_arith);
            assert((i + k) * step == i * step + k * step) by (nonlinear_arith);
            assert(h * m == (k * step) * mi);
            assert(gidx(m, base, r, step, q2) == p + h * m);
            assert(g[q2] == x[p + h * m]);
        } else {
            let q2 = q - k * m;
            assert((row - k * step) * mi == row * mi - (k * step) * mi) by (nonlinear_arith);
            assert((i - k) * step == i * step - k * step) by (nonlinear_arith);
            assert(h * m == (k * step) * mi);
            assert(gidx(m, base, r, step, q2) == p - h * m);
            assert(g[q2] == x[p - h * m]);
        }
    }
    assert(lhs =~= rhs);
}

/// Layers with twiddles that agree on every block are equal.
pub proof fn lemma_layer_map_tw(x: Seq<F64>, m: nat, h: nat, tw: spec_fn(int) -> u64, tw2: spec_fn(int) -> u64, inverse: bool)
    requires
        m > 0,
        h > 0,
        forall|b: int| 0 <= b ==> #[trigger] tw(b) == tw2(b),
    ensures
        layer_map(x, m, h, tw, inverse) == layer_map(x, m, h, tw2, inverse),
{
    assert forall|p: int| 0 <= p < x.len() implies layer_map(x, m, h, tw, inverse)[p] == layer_map(x, m, h, tw2, inverse)[p] by {
        lemma_div_pos_is_pos(p, m as int);
        lemma_div_pos_is_pos(row_of(p, m), 2 * h as int);
    }
    assert(layer_map(x, m, h, tw, inverse) =~= layer_map(x, m, h, tw2, inverse));
}

/// A gather of `cnt` consecutive rows is a subrange.
pub proof fn lemma_gather_contiguous(x: Seq<F64>, m: nat, base: int, cnt: nat)
    requires
        m > 0,
        base >= 0,
        (base + cnt) * m <= x.len(),
    ensures
        gather(x, m, base, 0, 1, cnt) == x.subrange(base * m, (base + cnt) * m),
{
    let mi = m as int;
    assert((base + cnt) * m - base * m == cnt * m) by (nonlinear_arith);
    assert(base * m >= 0) by (nonlinear_arith)
        requires
            base >= 0,
    ;
    assert forall|q: int| 0 <= q < cnt * m implies gather(x, m, base, 0, 1, cnt)[q] == x.subrange(base * m, (base + cnt) * m)[q] by {
        lemma_split_word(q, mi);
        assert(gidx(m, base, 0, 1, q) == base * mi + q) by (nonlinear_arith)
            requires
                gidx(m, base, 0, 1, q) == (base + 0 + (q / mi) * 1) * mi + q % mi,
                q == (q / mi) * mi + q % mi,
        ;
    }
    assert((base + cnt) * m - base * m == cnt * m) by (nonlinear_arith);
    assert(gather(x, m, base, 0, 1, cnt) =~= x.subrange(base * m, (base + cnt) * m));
}

proof fn lemma_sub_layers_len(tab: Seq<Seq<F64>>, x: Seq<F64>, m: nat, log_d: nat, o: nat, s: int, first: nat, end: nat)
    ensures
        sub_layers(tab, x, m, log_d, o, s, first, end).len() == x.len(),
    decreases end,
{
    if end > first {
        lemma_sub_layers_len(tab, x, m, log_d, o, s, first, (end - 1) as nat);
    }
}

/// Layers `first..end` are layers `first..mid` followed by layers `mid..end`.
pub proof fn lemma_sub_layers_split(tab: Seq<Seq<F64>>, x: Seq<F64>, m: nat, log_d: nat, o: nat, s: int, first: nat, mid: nat, end: nat)
    requires
        first <= mid <= end,
    ensures
        sub_layers(tab, sub_layers(tab, x, m, log_d, o, s, first, mid), m, log_d, o, s, mid, end) == sub_layers(
            tab,
            x,
            m,
            log_d,
            o,
            s,
            first,
            end,
        ),
    decreases end,
{
    if end > mid {
        lemma_sub_layers_split(tab, x, m, log_d, o, s, first, mid, (end - 1) as nat);
    }
}

/// On the whole domain (`o = 0`), the sub-block layers are [`forward_layers`].
pub proof fn lemma_forward_is_sub(tab: Seq<Seq<F64>>, x: Seq<F64>, m: nat, log_d: nat, first: nat, end: nat)
    requires
        m > 0,
        end <= log_d,
    ensures
        forward_layers(tab, x, m, log_d, first, end) == sub_layers(tab, x, m, log_d, 0, 0, first, end),
    decreases end,
{
    if end > first {
        let l = (end - 1) as nat;
        lemma_forward_is_sub(tab, x, m, log_d, first, l);
        lemma_layer_shape(log_d, l, m);
        lemma_layer_map_tw(
            sub_layers(tab, x, m, log_d, 0, 0, first, l),
            m,
            layer_half(log_d, l),
            layer_twiddles(tab, l),
            sub_twiddles(tab, l, 0, 0),
            false,
        );
    }
}

/// The layers of a sub-block, gathered on rows they pair among themselves, are the layers of a smaller
/// domain on the gathered buffer.
///
/// The buffer `x` is sub-block `s` of `2^o` of a `2^log_d`-row domain. The gather takes the rows
/// `base + r + i * 2^(log_d - log_d2)` of sub-block `s2` of `2^o2` of it, `i < 2^(log_d2 - o2)`; on them the
/// layers `first..end` (`o2 <= first`) are those of sub-block `s2` of a `2^log_d2`-row domain.
pub proof fn lemma_gather_sub_layers(
    tab: Seq<Seq<F64>>,
    x: Seq<F64>,
    m: nat,
    log_d: nat,
    o: nat,
    s: int,
    log_d2: nat,
    o2: nat,
    s2: int,
    r: int,
    first: nat,
    end: nat,
)
    requires
        m > 0,
        o <= o2 <= first <= end <= log_d2 <= log_d,
        s >= 0,
        s * pow2((o2 - o) as nat) <= s2 < (s + 1) * pow2((o2 - o) as nat),
        0 <= r < pow2((log_d - log_d2) as nat),
        x.len() == m * pow2((log_d - o) as nat),
    ensures
        ({
            let base = (s2 - s * pow2((o2 - o) as nat)) * pow2((log_d - o2) as nat);
            let step = pow2((log_d - log_d2) as nat) as int;
            let cnt = pow2((log_d2 - o2) as nat);
            gather(sub_layers(tab, x, m, log_d, o, s, first, end), m, base, r, step, cnt) == sub_layers(
                tab,
                gather(x, m, base, r, step, cnt),
                m,
                log_d2,
                o2,
                s2,
                first,
                end,
            )
        }),
    decreases end,
{
    let rb = s2 - s * pow2((o2 - o) as nat);
    let base = rb * pow2((log_d - o2) as nat);
    let step = pow2((log_d - log_d2) as nat) as int;
    let cnt = pow2((log_d2 - o2) as nat);
    if end > first {
        let l = (end - 1) as nat;
        lemma_gather_sub_layers(tab, x, m, log_d, o, s, log_d2, o2, s2, r, first, l);
        let y = sub_layers(tab, x, m, log_d, o, s, first, l);
        lemma_sub_layers_len(tab, x, m, log_d, o, s, first, l);
        let h = layer_half(log_d, l);
        let k = layer_half(log_d2, l);
        // H = k * step, 2k = 2^(log_d2 - l), cnt = 2k * 2^(l - o2), 2H = 2^(log_d - l).
        lemma_pow2_adds((log_d2 - l - 1) as nat, (log_d - log_d2) as nat);
        assert((log_d2 - l - 1) as nat + (log_d - log_d2) as nat == (log_d - l - 1) as nat);
        lemma_pow2_unfold((log_d2 - l) as nat);
        lemma_pow2_unfold((log_d - l) as nat);
        lemma_pow2_adds((log_d2 - l) as nat, (l - o2) as nat);
        assert((log_d2 - l) as nat + (l - o2) as nat == (log_d2 - o2) as nat);
        lemma_pow2_adds((log_d - l) as nat, (l - o2) as nat);
        assert((log_d - l) as nat + (l - o2) as nat == (log_d - o2) as nat);
        lemma_pow2_adds((o2 - o) as nat, (log_d - o2) as nat);
        assert((o2 - o) as nat + (log_d - o2) as nat == (log_d - o) as nat);
        lemma_pow2_adds((o2 - o) as nat, (l - o2) as nat);
        assert((o2 - o) as nat + (l - o2) as nat == (l - o) as nat);
        lemma_pow2_pos((l - o2) as nat);
        lemma_pow2_pos((log_d - l) as nat);
        lemma_pow2_pos((log_d - o2) as nat);
        lemma_pow2_pos((log_d2 - l - 1) as nat);
        lemma_pow2_pos((log_d - log_d2) as nat);
        lemma_pow2_adds((log_d2 - o2) as nat, (log_d - log_d2) as nat);
        assert((log_d2 - o2) as nat + (log_d - log_d2) as nat == (log_d - o2) as nat);
        let p_lo2 = pow2((l - o2) as nat) as int;
        let p2h = pow2((log_d - l) as nat) as int;
        assert(0 <= rb < pow2((o2 - o) as nat)) by (nonlinear_arith)
            requires
                rb == s2 - s * pow2((o2 - o) as nat),
                s * pow2((o2 - o) as nat) <= s2 < (s + 1) * pow2((o2 - o) as nat),
        ;
        assert(base == (rb * p_lo2) * p2h) by (nonlinear_arith)
            requires
                base == rb * pow2((log_d - o2) as nat),
                pow2((log_d - o2) as nat) == p2h * p_lo2,
        ;
        assert(2 * h == p2h);
        lemma_mod_multiples_basic(rb * p_lo2, p2h);
        lemma_div_multiples_vanish(rb * p_lo2, p2h);
        assert(base / (2 * h as int) == rb * p_lo2) by {
            lemma_mul_is_commutative(rb * p_lo2, p2h);
        }
        assert(base % (2 * h as int) == 0) by {
            lemma_mul_is_commutative(rb * p_lo2, p2h);
        }
        assert(cnt as int == (2 * k) * p_lo2);
        lemma_mod_multiples_basic(p_lo2, 2 * k as int);
        assert(cnt % (2 * k) == 0) by {
            lemma_mul_is_commutative(p_lo2, 2 * k as int);
        }
        assert(cnt / (2 * k) == p_lo2) by {
            lemma_div_multiples_vanish(p_lo2, 2 * k as int);
            lemma_mul_is_commutative(p_lo2, 2 * k as int);
        }
        assert((base + cnt * step) * m <= y.len()) by (nonlinear_arith)
            requires
                base == rb * pow2((log_d - o2) as nat),
                cnt * step == pow2((log_d - o2) as nat),
                rb + 1 <= pow2((o2 - o) as nat),
                y.len() == m * pow2((log_d - o) as nat),
                pow2((log_d - o) as nat) == pow2((o2 - o) as nat) * pow2((log_d - o2) as nat),
                m > 0,
        ;
        let tw = sub_twiddles(tab, l, o, s);
        let tw2 = sub_twiddles(tab, l, o2, s2);
        assert forall|b: int| 0 <= b < cnt / (2 * k) implies #[trigger] tw2(b) == tw(base / (2 * h as int) + b) by {
            assert(s * pow2((l - o) as nat) + rb * p_lo2 == s2 * p_lo2) by (nonlinear_arith)
                requires
                    rb == s2 - s * pow2((o2 - o) as nat),
                    pow2((l - o) as nat) == pow2((o2 - o) as nat) * p_lo2,
            ;
        }
        lemma_gather_layer(y, m, h, tw, tw2, false, base, r, step, cnt, k);
    }
}

// ---------------------------------------------------------------------------------------------
// Fused layers on row groups
// ---------------------------------------------------------------------------------------------
/// Rows of `m` words, as one buffer.
pub open spec fn rows_seq(rows: Seq<Seq<F64>>, m: nat) -> Seq<F64> {
    Seq::new(rows.len() * m, |p: int| rows[p / (m as int)][p % (m as int)])
}

/// The rows `b` are one butterfly layer of half `h` on the rows `a`, lane by lane.
pub open spec fn layer_rows(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, h: nat, tw: spec_fn(int) -> u64) -> bool {
    &&& a.len() == b.len()
    &&& forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == m && b[i].len() == m
    &&& forall|i: int, lane: int|
        0 <= i < a.len() && 0 <= lane < m ==> if i % (2 * h as int) < h {
            (#[trigger] b[i][lane]).0 == bf_top(a[i][lane].0, a[i + h][lane].0, tw(i / (2 * h as int)))
        } else {
            b[i][lane].0 == bf_bot(a[i - h][lane].0, a[i][lane].0, tw(i / (2 * h as int)))
        }
}

/// Layers L, L+1 and L+2 on a block of `8e` rows: rows `4e`, `2e`, then `e` apart, with the seven
/// twiddles `t` breadth-first.
pub open spec fn layer3(x: Seq<F64>, m: nat, e: nat, t: Seq<F64>) -> Seq<F64> {
    layer_map(
        layer_map(layer_map(x, m, 4 * e, |b: int| t[0].0, false), m, 2 * e, |b: int| t[1 + b].0, false),
        m,
        e,
        |b: int| t[3 + b].0,
        false,
    )
}

/// Layers L and L+1 on a block of `4e` rows: rows `2e` then `e` apart.
pub open spec fn layer2(x: Seq<F64>, m: nat, e: nat, t_outer: u64, t_inner_a: u64, t_inner_b: u64) -> Seq<F64> {
    layer_map(
        layer_map(x, m, 2 * e, |b: int| t_outer, false),
        m,
        e,
        pick2(t_inner_a, t_inner_b),
        false,
    )
}

/// Twiddle `a` for block 0, `b` for block 1.
pub open spec fn pick2(a: u64, b: u64) -> spec_fn(int) -> u64 {
    |x: int|
        if x == 0 {
            a
        } else {
            b
        }
}

/// `gp` holds exactly the permissions of the words `off .. off + m` of each of `n` slabs `stride` words
/// long, of the buffer at `base`.
pub open spec fn holds_group(gp: Map<int, PointsTo<F64>>, base: *mut F64, off: int, stride: int, n: nat, m: nat) -> bool {
    &&& 0 <= off
    &&& off + m <= stride
    &&& base@.addr + n * stride * size_of::<F64>() <= usize::MAX
    &&& n * stride <= usize::MAX
    &&& forall|k: int| #[trigger] gp.dom().contains(k) <==> 0 <= k < n * stride && off <= k % stride < off + m
    &&& forall|k: int| #[trigger] gp.dom().contains(k) ==> gp[k].ptr() == ptr_at(base, k) && gp[k].is_init()
}

/// The words of a group, row by row, as one buffer.
pub open spec fn group_seq(gp: Map<int, PointsTo<F64>>, off: int, stride: int, n: nat, m: nat) -> Seq<F64> {
    Seq::new(n * m, |q: int| gp[off + (q / (m as int)) * stride + q % (m as int)].value())
}

/// What `fused_rows` hands its closure: the permissions of row `off / m` of every slab, with the
/// block's values `x`.
pub open spec fn group_pre(gp: Map<int, PointsTo<F64>>, base: *mut F64, off: int, stride: int, n: nat, m: nat, x: Seq<F64>) -> bool {
    &&& holds_group(gp, base, off, stride, n, m)
    &&& off % (m as int) == 0
    &&& forall|k: int| #[trigger] gp.dom().contains(k) ==> gp[k].value() == x[k]
}

/// What the closure returns: the same permissions, with the values `target`.
pub open spec fn group_post(res: Map<int, PointsTo<F64>>, gp: Map<int, PointsTo<F64>>, target: Seq<F64>) -> bool {
    &&& res.dom() == gp.dom()
    &&& forall|k: int|
        #[trigger] gp.dom().contains(k) ==> res[k].ptr() == gp[k].ptr() && res[k].is_init() && res[k].value() == target[k]
}

/// A layer on rows given lane by lane is the layer on the buffer of the rows.
pub proof fn lemma_rows_layer(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, h: nat, tw: spec_fn(int) -> u64)
    requires
        m > 0,
        h > 0,
        a.len() % (2 * h) == 0,
        layer_rows(a, b, m, h, tw),
    ensures
        layer_map(rows_seq(a, m), m, h, tw, false) == rows_seq(b, m),
{
    let mi = m as int;
    let n = a.len() as int;
    let x = rows_seq(a, m);
    assert forall|p: int| 0 <= p < n * mi implies layer_map(x, m, h, tw, false)[p] == rows_seq(b, m)[p] by {
        lemma_split_word(p, mi);
        lemma_gather_rows(p, mi, n, h as int);
        let i = p / mi;
        assert(row_of(p, m) == i);
        if i % (2 * h as int) < h {
            assert(x[p + h * m] == a[i + h][p % mi]);
        } else {
            assert(x[p - h * m] == a[i - h][p % mi]);
        }
    }
    assert(layer_map(x, m, h, tw, false) =~= rows_seq(b, m));
}

/// The three layers of a block, gathered on one row group, are the three layers of the group.
pub proof fn lemma_gather_layer3(x: Seq<F64>, m: nat, e: nat, t: Seq<F64>, r: int)
    requires
        m > 0,
        e > 0,
        0 <= r < e,
        x.len() == 8 * e * m,
    ensures
        gather(layer3(x, m, e, t), m, 0, r, e as int, 8) == layer3(gather(x, m, 0, r, e as int, 8), m, 1, t),
{
    let t0 = |b: int| t[0].0;
    let t1 = |b: int| t[1 + b].0;
    let t2 = |b: int| t[3 + b].0;
    let x1 = layer_map(x, m, 4 * e, t0, false);
    let x2 = layer_map(x1, m, 2 * e, t1, false);
    let g = gather(x, m, 0, r, e as int, 8);
    assert((0 + 8 * e) * m <= x.len()) by (nonlinear_arith)
        requires
            x.len() == 8 * e * m,
    ;
    assert(8nat % (2 * 4nat) == 0 && 8nat % (2 * 2nat) == 0 && 8nat % (2 * 1nat) == 0) by (compute);
    lemma_gather_layer(x, m, 4 * e, t0, t0, false, 0, r, e as int, 8, 4);
    lemma_gather_layer(x1, m, 2 * e, t1, t1, false, 0, r, e as int, 8, 2);
    lemma_gather_layer(x2, m, e, t2, t2, false, 0, r, e as int, 8, 1);
}

/// The two layers of a block, gathered on one row group, are the two layers of the group.
pub proof fn lemma_gather_layer2(x: Seq<F64>, m: nat, e: nat, t_outer: u64, t_inner_a: u64, t_inner_b: u64, r: int)
    requires
        m > 0,
        e > 0,
        0 <= r < e,
        x.len() == 4 * e * m,
    ensures
        gather(layer2(x, m, e, t_outer, t_inner_a, t_inner_b), m, 0, r, e as int, 4) == layer2(
            gather(x, m, 0, r, e as int, 4),
            m,
            1,
            t_outer,
            t_inner_a,
            t_inner_b,
        ),
{
    let t0 = |b: int| t_outer;
    let t1 = pick2(t_inner_a, t_inner_b);
    let x1 = layer_map(x, m, 2 * e, t0, false);
    assert((0 + 4 * e) * m <= x.len()) by (nonlinear_arith)
        requires
            x.len() == 4 * e * m,
    ;
    assert(4nat % (2 * 2nat) == 0 && 4nat % (2 * 1nat) == 0) by (compute);
    lemma_gather_layer(x, m, 2 * e, t0, t0, false, 0, r, e as int, 4, 2);
    lemma_gather_layer(x1, m, e, t1, t1, false, 0, r, e as int, 4, 1);
}

/// Word `off + i * stride + lane` of a group is word `q = i * m + lane` of its gather.
proof fn lemma_group_word(q: int, m: int, e: int, r: int)
    requires
        m > 0,
        q >= 0,
    ensures
        gidx(m as nat, 0, r, e, q) == r * m + (q / m) * (e * m) + q % m,
{
    assert((0 + r + (q / m) * e) * m == r * m + (q / m) * (e * m)) by (nonlinear_arith);
}

/// The key `k` of a group is `off + i * stride + lane`, word `i * m + lane` of the group's buffer.
proof fn lemma_group_key(k: int, off: int, stride: int, n: nat, m: nat)
    requires
        m > 0,
        0 <= off,
        off + m <= stride,
        0 <= k < n * stride,
        off <= k % stride < off + m,
    ensures
        ({
            let i = k / stride;
            let lane = k % stride - off;
            &&& 0 <= i < n
            &&& 0 <= lane < m
            &&& k == off + i * stride + lane
            &&& 0 <= i * m + lane < n * m
            &&& (i * m + lane) / (m as int) == i
            &&& (i * m + lane) % (m as int) == lane
        }),
{
    let i = k / stride;
    let lane = k % stride - off;
    lemma_split_word(k, stride);
    assert(i < n) by (nonlinear_arith)
        requires
            k == i * stride + k % stride,
            k % stride >= 0,
            k < n * stride,
            stride > 0,
    ;
    lemma_word(i, lane, m as int);
    assert(i * m + lane < n * m) by (nonlinear_arith)
        requires
            i + 1 <= n,
            0 <= lane < m,
    ;
    assert(i * m + lane >= 0) by (nonlinear_arith)
        requires
            i >= 0,
            lane >= 0,
    ;
}

/// A group's buffer is the gather of its rows of the block.
proof fn lemma_group_seq(gp: Map<int, PointsTo<F64>>, base: *mut F64, x: Seq<F64>, off: int, n: nat, m: nat, e: nat)
    requires
        m > 0,
        e > 0,
        off % (m as int) == 0,
        x.len() == n * (e * m),
        group_pre(gp, base, off, (e * m) as int, n, m, x),
    ensures
        group_seq(gp, off, (e * m) as int, n, m) == gather(x, m, 0, off / (m as int), e as int, n),
{
    let mi = m as int;
    let stride = (e * m) as int;
    let r = off / mi;
    lemma_fundamental_div_mod(off, mi);
    assert forall|q: int| 0 <= q < n * m implies group_seq(gp, off, stride, n, m)[q] == gather(x, m, 0, r, e as int, n)[q] by {
        lemma_split_word(q, mi);
        lemma_group_word(q, mi, e as int, r);
        let i = q / mi;
        let lane = q % mi;
        let k = off + i * stride + lane;
        assert(r * mi == off) by {
            lemma_mul_is_commutative(r, mi);
        }
        assert(i < n) by (nonlinear_arith)
            requires
                q == i * mi + lane,
                lane >= 0,
                q < n * mi,
                mi > 0,
        ;
        assert(k >= 0) by (nonlinear_arith)
            requires
                k == off + i * stride + lane,
                off >= 0,
                i >= 0,
                stride > 0,
                lane >= 0,
        ;
        assert(k < n * stride) by (nonlinear_arith)
            requires
                k == off + i * stride + lane,
                i + 1 <= n,
                off + lane < stride,
                stride > 0,
        ;
        lemma_fundamental_div_mod_converse(k, stride, i, off + lane);
        assert(gp.dom().contains(k));
    }
    assert(group_seq(gp, off, stride, n, m) =~= gather(x, m, 0, r, e as int, n));
}

/// Back from a group's buffer to its keys: the group's words are the target's.
proof fn lemma_group_back(gp: Map<int, PointsTo<F64>>, res: Map<int, PointsTo<F64>>, base: *mut F64, target: Seq<F64>, off: int, n: nat, m: nat, e: nat)
    requires
        m > 0,
        e > 0,
        off % (m as int) == 0,
        target.len() == n * (e * m),
        holds_group(gp, base, off, (e * m) as int, n, m),
        res.dom() == gp.dom(),
        group_seq(res, off, (e * m) as int, n, m) == gather(target, m, 0, off / (m as int), e as int, n),
    ensures
        forall|k: int| #[trigger] gp.dom().contains(k) ==> res[k].value() == target[k],
{
    let mi = m as int;
    let stride = (e * m) as int;
    let r = off / mi;
    lemma_fundamental_div_mod(off, mi);
    assert forall|k: int| #[trigger] gp.dom().contains(k) implies res[k].value() == target[k] by {
        lemma_group_key(k, off, stride, n, m);
        let i = k / stride;
        let lane = k % stride - off;
        let q = i * mi + lane;
        lemma_group_word(q, mi, e as int, r);
        assert(r * mi == off) by {
            lemma_mul_is_commutative(r, mi);
        }
        assert(group_seq(res, off, stride, n, m)[q] == res[k].value());
        assert(gather(target, m, 0, r, e as int, n)[q] == target[k]);
    }
}

/// Row `i` of a group: its words are in the group, with their permissions, and end inside the block.
proof fn lemma_row_in_group(g: Map<int, PointsTo<F64>>, base: *mut F64, off: int, stride: int, n: nat, m: nat, i: int)
    requires
        m > 0,
        0 <= i < n,
        holds_group(g, base, off, stride, n, m),
    ensures
        Set::range(i * stride + off, i * stride + off + m) <= g.dom(),
        i * stride + off + m <= n * stride,
        i * stride >= 0,
        base@.addr + (i * stride + off + m) * size_of::<F64>() <= usize::MAX,
        base@.addr + (i * stride + off) * size_of::<F64>() <= usize::MAX,
{
    assert(i * stride + off + m <= n * stride) by (nonlinear_arith)
        requires
            i + 1 <= n,
            off + m <= stride,
            0 <= off,
    ;
    assert(i * stride >= 0) by (nonlinear_arith)
        requires
            i >= 0,
            stride >= 0,
    ;
    lemma_mul_le(i * stride + off + m, n * stride, size_of::<F64>() as int);
    lemma_mul_le(i * stride + off, i * stride + off + m, size_of::<F64>() as int);
    assert forall|k: int| Set::range(i * stride + off, i * stride + off + m).contains(k) implies g.dom().contains(k) by {
        lemma_fundamental_div_mod_converse(k, stride, i, k - i * stride);
    }
}

/// A group's buffer, given row by row.
proof fn lemma_rows_group_seq(g: Map<int, PointsTo<F64>>, off: int, stride: int, n: nat, m: nat, rows: Seq<Seq<F64>>)
    requires
        m > 0,
        rows.len() == n,
        forall|i: int| 0 <= i < n ==> (#[trigger] rows[i]).len() == m,
        forall|i: int, lane: int| 0 <= i < n && 0 <= lane < m ==> (#[trigger] rows[i][lane]) == g[i * stride + off + lane].value(),
    ensures
        group_seq(g, off, stride, n, m) == rows_seq(rows, m),
{
    let mi = m as int;
    assert forall|q: int| 0 <= q < n * m implies group_seq(g, off, stride, n, m)[q] == rows_seq(rows, m)[q] by {
        lemma_split_word(q, mi);
        assert(q / mi < n) by (nonlinear_arith)
            requires
                q == (q / mi) * mi + q % mi,
                q % mi >= 0,
                q < n * mi,
                mi > 0,
        ;
        assert(off + (q / mi) * stride + q % mi == (q / mi) * stride + off + q % mi);
    }
    assert(group_seq(g, off, stride, n, m) =~= rows_seq(rows, m));
}

/// The butterfly of rows `i` and `i + h` of `a`, lane by lane, gives rows `i` and `i + h` of `b`.
pub open spec fn pair_fact(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, i: int, h: int, t: u64) -> bool {
    forall|lane: int|
        0 <= lane < m ==> ((#[trigger] b[i][lane]).0, b[i + h][lane].0) == butterfly_spec(false, a[i][lane].0, a[i + h][lane].0, t)
}

/// Rows of `m` lanes, `n` of them.
pub open spec fn rows_shape(a: Seq<Seq<F64>>, n: nat, m: nat) -> bool {
    a.len() == n && forall|i: int| 0 <= i < n ==> (#[trigger] a[i]).len() == m
}

proof fn lemma_radix8_layer_a(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, tw: spec_fn(int) -> u64)
    requires
        rows_shape(a, 8, m),
        rows_shape(b, 8, m),
        pair_fact(a, b, m, 0, 4, tw(0)),
        pair_fact(a, b, m, 1, 4, tw(0)),
        pair_fact(a, b, m, 2, 4, tw(0)),
        pair_fact(a, b, m, 3, 4, tw(0)),
    ensures
        layer_rows(a, b, m, 4, tw),
{
    assert forall|i: int, lane: int| 0 <= i < 8 && 0 <= lane < m implies if i % (2 * 4nat as int) < 4 {
        (#[trigger] b[i][lane]).0 == bf_top(a[i][lane].0, a[i + 4][lane].0, tw(i / (2 * 4nat as int)))
    } else {
        b[i][lane].0 == bf_bot(a[i - 4][lane].0, a[i][lane].0, tw(i / (2 * 4nat as int)))
    } by {
        if i == 0 {
            assert((b[0][lane].0, b[4][lane].0) == butterfly_spec(false, a[0][lane].0, a[4][lane].0, tw(0)));
        } else if i == 1 {
            assert((b[1][lane].0, b[5][lane].0) == butterfly_spec(false, a[1][lane].0, a[5][lane].0, tw(0)));
        } else if i == 2 {
            assert((b[2][lane].0, b[6][lane].0) == butterfly_spec(false, a[2][lane].0, a[6][lane].0, tw(0)));
        } else if i == 3 {
            assert((b[3][lane].0, b[7][lane].0) == butterfly_spec(false, a[3][lane].0, a[7][lane].0, tw(0)));
        } else if i == 4 {
            assert((b[0][lane].0, b[4][lane].0) == butterfly_spec(false, a[0][lane].0, a[4][lane].0, tw(0)));
        } else if i == 5 {
            assert((b[1][lane].0, b[5][lane].0) == butterfly_spec(false, a[1][lane].0, a[5][lane].0, tw(0)));
        } else if i == 6 {
            assert((b[2][lane].0, b[6][lane].0) == butterfly_spec(false, a[2][lane].0, a[6][lane].0, tw(0)));
        } else {
            assert((b[3][lane].0, b[7][lane].0) == butterfly_spec(false, a[3][lane].0, a[7][lane].0, tw(0)));
        }
    }
}

proof fn lemma_radix8_layer_b(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, tw: spec_fn(int) -> u64)
    requires
        rows_shape(a, 8, m),
        rows_shape(b, 8, m),
        pair_fact(a, b, m, 0, 2, tw(0)),
        pair_fact(a, b, m, 1, 2, tw(0)),
        pair_fact(a, b, m, 4, 2, tw(1)),
        pair_fact(a, b, m, 5, 2, tw(1)),
    ensures
        layer_rows(a, b, m, 2, tw),
{
    assert forall|i: int, lane: int| 0 <= i < 8 && 0 <= lane < m implies if i % (2 * 2nat as int) < 2 {
        (#[trigger] b[i][lane]).0 == bf_top(a[i][lane].0, a[i + 2][lane].0, tw(i / (2 * 2nat as int)))
    } else {
        b[i][lane].0 == bf_bot(a[i - 2][lane].0, a[i][lane].0, tw(i / (2 * 2nat as int)))
    } by {
        if i == 0 {
            assert((b[0][lane].0, b[2][lane].0) == butterfly_spec(false, a[0][lane].0, a[2][lane].0, tw(0)));
        } else if i == 1 {
            assert((b[1][lane].0, b[3][lane].0) == butterfly_spec(false, a[1][lane].0, a[3][lane].0, tw(0)));
        } else if i == 2 {
            assert((b[0][lane].0, b[2][lane].0) == butterfly_spec(false, a[0][lane].0, a[2][lane].0, tw(0)));
        } else if i == 3 {
            assert((b[1][lane].0, b[3][lane].0) == butterfly_spec(false, a[1][lane].0, a[3][lane].0, tw(0)));
        } else if i == 4 {
            assert((b[4][lane].0, b[6][lane].0) == butterfly_spec(false, a[4][lane].0, a[6][lane].0, tw(1)));
        } else if i == 5 {
            assert((b[5][lane].0, b[7][lane].0) == butterfly_spec(false, a[5][lane].0, a[7][lane].0, tw(1)));
        } else if i == 6 {
            assert((b[4][lane].0, b[6][lane].0) == butterfly_spec(false, a[4][lane].0, a[6][lane].0, tw(1)));
        } else {
            assert((b[5][lane].0, b[7][lane].0) == butterfly_spec(false, a[5][lane].0, a[7][lane].0, tw(1)));
        }
    }
}

proof fn lemma_radix8_layer_c(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, tw: spec_fn(int) -> u64)
    requires
        rows_shape(a, 8, m),
        rows_shape(b, 8, m),
        pair_fact(a, b, m, 0, 1, tw(0)),
        pair_fact(a, b, m, 2, 1, tw(1)),
        pair_fact(a, b, m, 4, 1, tw(2)),
        pair_fact(a, b, m, 6, 1, tw(3)),
    ensures
        layer_rows(a, b, m, 1, tw),
{
    assert forall|i: int, lane: int| 0 <= i < 8 && 0 <= lane < m implies if i % (2 * 1nat as int) < 1 {
        (#[trigger] b[i][lane]).0 == bf_top(a[i][lane].0, a[i + 1][lane].0, tw(i / (2 * 1nat as int)))
    } else {
        b[i][lane].0 == bf_bot(a[i - 1][lane].0, a[i][lane].0, tw(i / (2 * 1nat as int)))
    } by {
        if i == 0 {
            assert((b[0][lane].0, b[1][lane].0) == butterfly_spec(false, a[0][lane].0, a[1][lane].0, tw(0)));
        } else if i == 1 {
            assert((b[0][lane].0, b[1][lane].0) == butterfly_spec(false, a[0][lane].0, a[1][lane].0, tw(0)));
        } else if i == 2 {
            assert((b[2][lane].0, b[3][lane].0) == butterfly_spec(false, a[2][lane].0, a[3][lane].0, tw(1)));
        } else if i == 3 {
            assert((b[2][lane].0, b[3][lane].0) == butterfly_spec(false, a[2][lane].0, a[3][lane].0, tw(1)));
        } else if i == 4 {
            assert((b[4][lane].0, b[5][lane].0) == butterfly_spec(false, a[4][lane].0, a[5][lane].0, tw(2)));
        } else if i == 5 {
            assert((b[4][lane].0, b[5][lane].0) == butterfly_spec(false, a[4][lane].0, a[5][lane].0, tw(2)));
        } else if i == 6 {
            assert((b[6][lane].0, b[7][lane].0) == butterfly_spec(false, a[6][lane].0, a[7][lane].0, tw(3)));
        } else {
            assert((b[6][lane].0, b[7][lane].0) == butterfly_spec(false, a[6][lane].0, a[7][lane].0, tw(3)));
        }
    }
}

proof fn lemma_radix4_layer_a(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, tw: spec_fn(int) -> u64)
    requires
        rows_shape(a, 4, m),
        rows_shape(b, 4, m),
        pair_fact(a, b, m, 0, 2, tw(0)),
        pair_fact(a, b, m, 1, 2, tw(0)),
    ensures
        layer_rows(a, b, m, 2, tw),
{
    assert forall|i: int, lane: int| 0 <= i < 4 && 0 <= lane < m implies if i % (2 * 2nat as int) < 2 {
        (#[trigger] b[i][lane]).0 == bf_top(a[i][lane].0, a[i + 2][lane].0, tw(i / (2 * 2nat as int)))
    } else {
        b[i][lane].0 == bf_bot(a[i - 2][lane].0, a[i][lane].0, tw(i / (2 * 2nat as int)))
    } by {
        if i == 0 {
            assert((b[0][lane].0, b[2][lane].0) == butterfly_spec(false, a[0][lane].0, a[2][lane].0, tw(0)));
        } else if i == 1 {
            assert((b[1][lane].0, b[3][lane].0) == butterfly_spec(false, a[1][lane].0, a[3][lane].0, tw(0)));
        } else if i == 2 {
            assert((b[0][lane].0, b[2][lane].0) == butterfly_spec(false, a[0][lane].0, a[2][lane].0, tw(0)));
        } else {
            assert((b[1][lane].0, b[3][lane].0) == butterfly_spec(false, a[1][lane].0, a[3][lane].0, tw(0)));
        }
    }
}

proof fn lemma_radix4_layer_b(a: Seq<Seq<F64>>, b: Seq<Seq<F64>>, m: nat, tw: spec_fn(int) -> u64)
    requires
        rows_shape(a, 4, m),
        rows_shape(b, 4, m),
        pair_fact(a, b, m, 0, 1, tw(0)),
        pair_fact(a, b, m, 2, 1, tw(1)),
    ensures
        layer_rows(a, b, m, 1, tw),
{
    assert forall|i: int, lane: int| 0 <= i < 4 && 0 <= lane < m implies if i % (2 * 1nat as int) < 1 {
        (#[trigger] b[i][lane]).0 == bf_top(a[i][lane].0, a[i + 1][lane].0, tw(i / (2 * 1nat as int)))
    } else {
        b[i][lane].0 == bf_bot(a[i - 1][lane].0, a[i][lane].0, tw(i / (2 * 1nat as int)))
    } by {
        if i == 0 {
            assert((b[0][lane].0, b[1][lane].0) == butterfly_spec(false, a[0][lane].0, a[1][lane].0, tw(0)));
        } else if i == 1 {
            assert((b[0][lane].0, b[1][lane].0) == butterfly_spec(false, a[0][lane].0, a[1][lane].0, tw(0)));
        } else if i == 2 {
            assert((b[2][lane].0, b[3][lane].0) == butterfly_spec(false, a[2][lane].0, a[3][lane].0, tw(1)));
        } else {
            assert((b[2][lane].0, b[3][lane].0) == butterfly_spec(false, a[2][lane].0, a[3][lane].0, tw(1)));
        }
    }
}

/// The union of `rest` with the maps `fs[0..n]`, later ones taking precedence.
pub open spec fn union_all(rest: Map<int, PointsTo<F64>>, fs: Seq<Map<int, PointsTo<F64>>>, n: nat) -> Map<int, PointsTo<F64>>
    decreases n,
{
    if n == 0 {
        rest
    } else {
        union_all(rest, fs, (n - 1) as nat).union_prefer_right(fs[n - 1])
    }
}

/// A key of `fs[i]` that no later map holds keeps its permission in the union.
proof fn lemma_union_all(rest: Map<int, PointsTo<F64>>, fs: Seq<Map<int, PointsTo<F64>>>, n: nat, i: int, k: int)
    requires
        0 <= i < n,
        fs[i].dom().contains(k),
        forall|j: int| i < j < n ==> !(#[trigger] fs[j].dom().contains(k)),
    ensures
        union_all(rest, fs, n).dom().contains(k),
        union_all(rest, fs, n)[k] == fs[i][k],
    decreases n,
{
    if i < n - 1 {
        lemma_union_all(rest, fs, (n - 1) as nat, i, k);
    }
}

/// The domain of the union.
proof fn lemma_union_all_dom(rest: Map<int, PointsTo<F64>>, fs: Seq<Map<int, PointsTo<F64>>>, n: nat, k: int)
    ensures
        union_all(rest, fs, n).dom().contains(k) <==> rest.dom().contains(k) || exists|j: int| 0 <= j < n && #[trigger] fs[j].dom().contains(k),
    decreases n,
{
    if n > 0 {
        lemma_union_all_dom(rest, fs, (n - 1) as nat, k);
        if exists|j: int| 0 <= j < n && #[trigger] fs[j].dom().contains(k) {
            let j = choose|j: int| 0 <= j < n && #[trigger] fs[j].dom().contains(k);
            if j < n - 1 {
                assert(exists|j: int| 0 <= j < n - 1 && #[trigger] fs[j].dom().contains(k));
            }
        }
    }
}

/// Take the permissions of the words `lo .. lo + m` out of a map.
proof fn take_row(tracked gp: &mut Map<int, PointsTo<F64>>, base: *mut F64, lo: int, m: nat) -> (tracked p: Map<int, PointsTo<F64>>)
    requires
        0 <= lo,
        base@.addr + (lo + m) * size_of::<F64>() <= usize::MAX,
        Set::range(lo, lo + m) <= old(gp).dom(),
        forall|k: int| #[trigger] old(gp).dom().contains(k) ==> old(gp)[k].ptr() == ptr_at(base, k) && old(gp)[k].is_init(),
    ensures
        owns(p, base, lo, m as int),
        forall|j: int| 0 <= j < m ==> #[trigger] vals(p, lo, m as int)[j] == old(gp)[lo + j].value(),
        *final(gp) == old(gp).remove_keys(Set::range(lo, lo + m)),
{
    let ghost g = *gp;
    let tracked p = gp.tracked_remove_keys(Set::range(lo, lo + m));
    assert(p.dom() =~= Set::range(lo, lo + m));
    assert forall|k: int| lo <= k < lo + m implies (#[trigger] p[k]).ptr() == ptr_at(base, k) && p[k].is_init() by {
        assert(g.dom().contains(k));
    }
    p
}

/// The rows of a group, taken out row by row, run, and put back: the group's permissions, with the
/// rows' new values.
proof fn lemma_group_rows_back(
    g0: Map<int, PointsTo<F64>>,
    rest: Map<int, PointsTo<F64>>,
    fs: Seq<Map<int, PointsTo<F64>>>,
    base: *mut F64,
    off: int,
    stride: int,
    n: nat,
    m: nat,
    s0: Seq<Seq<F64>>,
    s3: Seq<Seq<F64>>,
)
    requires
        m > 0,
        holds_group(g0, base, off, stride, n, m),
        fs.len() == n,
        rows_shape(s0, n, m),
        rows_shape(s3, n, m),
        forall|k: int| #[trigger] rest.dom().contains(k) ==> g0.dom().contains(k) && rest[k] == g0[k],
        forall|i: int| 0 <= i < n ==> owns(#[trigger] fs[i], base, i * stride + off, m as int) && s3[i] == vals(fs[i], i * stride + off, m as int),
        forall|i: int, lane: int| 0 <= i < n && 0 <= lane < m ==> (#[trigger] s0[i][lane]) == g0[i * stride + off + lane].value(),
    ensures
        union_all(rest, fs, n).dom() == g0.dom(),
        forall|k: int| #[trigger] g0.dom().contains(k) ==> union_all(rest, fs, n)[k].ptr() == g0[k].ptr() && union_all(rest, fs, n)[k].is_init(),
        group_seq(union_all(rest, fs, n), off, stride, n, m) == rows_seq(s3, m),
        group_seq(g0, off, stride, n, m) == rows_seq(s0, m),
{
    let u = union_all(rest, fs, n);
    // A word of row `i` of the group belongs to no other row.
    assert forall|i: int, lane: int| 0 <= i < n && 0 <= lane < m implies #[trigger] u[i * stride + off + lane] == fs[i][i * stride + off + lane]
        && u.dom().contains(i * stride + off + lane) by {
        let k = i * stride + off + lane;
        assert(fs[i].dom().contains(k));
        assert forall|j: int| i < j < n implies !(#[trigger] fs[j].dom().contains(k)) by {
            assert(j * stride >= (i + 1) * stride) by (nonlinear_arith)
                requires
                    j >= i + 1,
                    stride >= 0,
            ;
            assert((i + 1) * stride == i * stride + stride) by (nonlinear_arith);
        }
        lemma_union_all(rest, fs, n, i, k);
    }
    assert forall|k: int| #[trigger] g0.dom().contains(k) implies u.dom().contains(k) by {
        lemma_group_key(k, off, stride, n, m);
        let i = k / stride;
        let lane = k % stride - off;
        assert(u[i * stride + off + lane] == fs[i][i * stride + off + lane]);
        assert(u.dom().contains(i * stride + off + lane));
    }
    assert forall|k: int| #[trigger] u.dom().contains(k) implies g0.dom().contains(k) by {
        lemma_union_all_dom(rest, fs, n, k);
        if !rest.dom().contains(k) {
            let j = choose|j: int| 0 <= j < n && #[trigger] fs[j].dom().contains(k);
            lemma_row_in_group(g0, base, off, stride, n, m, j);
            assert(owns(fs[j], base, j * stride + off, m as int));
            assert(Set::range(j * stride + off, j * stride + off + m).contains(k));
        }
    }
    assert(u.dom() =~= g0.dom());
    assert forall|k: int| #[trigger] g0.dom().contains(k) implies u[k].ptr() == g0[k].ptr() && u[k].is_init() by {
        lemma_group_key(k, off, stride, n, m);
        let i = k / stride;
        let lane = k % stride - off;
        assert(u[i * stride + off + lane] == fs[i][i * stride + off + lane]);
    }
    lemma_rows_group_seq(u, off, stride, n, m, s3);
    lemma_rows_group_seq(g0, off, stride, n, m, s0);
}

/// The twelve butterflies of one radix-8 row group, with its seven twiddles breadth-first.
///
/// Rewritten: the eight rows are eight arguments (production's `rows: &mut [&mut [F64]; 8]` and
/// `let [r0, ..] = rows`); Verus does not support arrays of mutable references. The twelve calls are
/// production's.
fn radix8_butterflies(
    r0: &mut [F64],
    r1: &mut [F64],
    r2: &mut [F64],
    r3: &mut [F64],
    r4: &mut [F64],
    r5: &mut [F64],
    r6: &mut [F64],
    r7: &mut [F64],
    t: &[F64; 7],
)
    requires
        rows_shape(seq![old(r0)@, old(r1)@, old(r2)@, old(r3)@, old(r4)@, old(r5)@, old(r6)@, old(r7)@], 8, old(r0)@.len()),
    ensures
        rows_shape(seq![final(r0)@, final(r1)@, final(r2)@, final(r3)@, final(r4)@, final(r5)@, final(r6)@, final(r7)@], 8, old(r0)@.len()),
        rows_seq(seq![final(r0)@, final(r1)@, final(r2)@, final(r3)@, final(r4)@, final(r5)@, final(r6)@, final(r7)@], old(r0)@.len())
            == layer3(
            rows_seq(seq![old(r0)@, old(r1)@, old(r2)@, old(r3)@, old(r4)@, old(r5)@, old(r6)@, old(r7)@], old(r0)@.len()),
            old(r0)@.len(),
            1,
            t@,
        ),
{
    let ghost m = r0@.len();
    let ghost s0 = seq![r0@, r1@, r2@, r3@, r4@, r5@, r6@, r7@];
    // Layer L: rows 4 apart, one twiddle for the whole block.
    butterfly_lanes(r0, r4, t[0]);
    butterfly_lanes(r1, r5, t[0]);
    butterfly_lanes(r2, r6, t[0]);
    butterfly_lanes(r3, r7, t[0]);
    let ghost s1 = seq![r0@, r1@, r2@, r3@, r4@, r5@, r6@, r7@];
    // Layer L+1: rows 2 apart, one twiddle per half.
    butterfly_lanes(r0, r2, t[1]);
    butterfly_lanes(r1, r3, t[1]);
    butterfly_lanes(r4, r6, t[2]);
    butterfly_lanes(r5, r7, t[2]);
    let ghost s2 = seq![r0@, r1@, r2@, r3@, r4@, r5@, r6@, r7@];
    // Layer L+2: adjacent rows, one twiddle per quarter.
    butterfly_lanes(r0, r1, t[3]);
    butterfly_lanes(r2, r3, t[4]);
    butterfly_lanes(r4, r5, t[5]);
    butterfly_lanes(r6, r7, t[6]);
    let ghost s3 = seq![r0@, r1@, r2@, r3@, r4@, r5@, r6@, r7@];
    proof {
        let tw0 = |b: int| t@[0].0;
        let tw1 = |b: int| t@[1 + b].0;
        let tw2 = |b: int| t@[3 + b].0;
        assert(rows_shape(s1, 8, m) && rows_shape(s2, 8, m) && rows_shape(s3, 8, m));
        lemma_radix8_layer_a(s0, s1, m, tw0);
        lemma_radix8_layer_b(s1, s2, m, tw1);
        lemma_radix8_layer_c(s2, s3, m, tw2);
        if m > 0 {
            assert(8nat % (2 * 4nat) == 0 && 8nat % (2 * 2nat) == 0 && 8nat % (2 * 1nat) == 0) by (compute);
            lemma_rows_layer(s0, s1, m, 4, tw0);
            lemma_rows_layer(s1, s2, m, 2, tw1);
            lemma_rows_layer(s2, s3, m, 1, tw2);
        } else {
            assert(rows_seq(s3, m) =~= layer3(rows_seq(s0, m), m, 1, t@));
        }
    }
}

/// The rows of group `off` of a block of eight slabs, built as `fused_rows` builds them, through the
/// radix-8 butterflies.
///
/// This is production's `fused_rows` loop body for `N = 8` (`std::array::from_fn` of
/// `from_raw_parts_mut(base.add(i * stride + off), num_ntts)`, then `do_one(&mut rows)`), written out per
/// row: Verus has no `from_fn` and no arrays of mutable references.
fn radix8_group(
    base: *mut F64,
    stride: usize,
    off: usize,
    num_ntts: usize,
    gp: Tracked<Map<int, PointsTo<F64>>>,
    t: &[F64; 7],
) -> (res: Tracked<Map<int, PointsTo<F64>>>)
    requires
        num_ntts > 0,
        holds_group(gp@, base, off as int, stride as int, 8, num_ntts as nat),
    ensures
        res@.dom() == gp@.dom(),
        forall|k: int| #[trigger] gp@.dom().contains(k) ==> res@[k].ptr() == gp@[k].ptr() && res@[k].is_init(),
        group_seq(res@, off as int, stride as int, 8, num_ntts as nat) == layer3(
            group_seq(gp@, off as int, stride as int, 8, num_ntts as nat),
            num_ntts as nat,
            1,
            t@,
        ),
{
    let ghost g0 = gp@;
    let ghost m = num_ntts as nat;
    let tracked mut gp = gp.get();
    proof {
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 0);
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 1);
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 2);
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 3);
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 4);
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 5);
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 6);
        lemma_row_in_group(g0, base, off as int, stride as int, 8, m, 7);
    }
    let tracked mut p0 = take_row(&mut gp, base, (0 * stride + off) as int, m);
    let tracked mut p1 = take_row(&mut gp, base, (1 * stride + off) as int, m);
    let tracked mut p2 = take_row(&mut gp, base, (2 * stride + off) as int, m);
    let tracked mut p3 = take_row(&mut gp, base, (3 * stride + off) as int, m);
    let tracked mut p4 = take_row(&mut gp, base, (4 * stride + off) as int, m);
    let tracked mut p5 = take_row(&mut gp, base, (5 * stride + off) as int, m);
    let tracked mut p6 = take_row(&mut gp, base, (6 * stride + off) as int, m);
    let tracked mut p7 = take_row(&mut gp, base, (7 * stride + off) as int, m);
    // SAFETY:
    // - The groups are disjoint, as argued above.
    // - The row ends inside its slab, since the row index is below the slab height.
    let r0 = unsafe { from_raw_parts_mut(base.add(0 * stride + off), num_ntts, Ghost(base), Ghost((0 * stride + off) as int), Tracked(&mut p0)) };
    let r1 = unsafe { from_raw_parts_mut(base.add(1 * stride + off), num_ntts, Ghost(base), Ghost((1 * stride + off) as int), Tracked(&mut p1)) };
    let r2 = unsafe { from_raw_parts_mut(base.add(2 * stride + off), num_ntts, Ghost(base), Ghost((2 * stride + off) as int), Tracked(&mut p2)) };
    let r3 = unsafe { from_raw_parts_mut(base.add(3 * stride + off), num_ntts, Ghost(base), Ghost((3 * stride + off) as int), Tracked(&mut p3)) };
    let r4 = unsafe { from_raw_parts_mut(base.add(4 * stride + off), num_ntts, Ghost(base), Ghost((4 * stride + off) as int), Tracked(&mut p4)) };
    let r5 = unsafe { from_raw_parts_mut(base.add(5 * stride + off), num_ntts, Ghost(base), Ghost((5 * stride + off) as int), Tracked(&mut p5)) };
    let r6 = unsafe { from_raw_parts_mut(base.add(6 * stride + off), num_ntts, Ghost(base), Ghost((6 * stride + off) as int), Tracked(&mut p6)) };
    let r7 = unsafe { from_raw_parts_mut(base.add(7 * stride + off), num_ntts, Ghost(base), Ghost((7 * stride + off) as int), Tracked(&mut p7)) };
    let ghost s0 = seq![r0@, r1@, r2@, r3@, r4@, r5@, r6@, r7@];
    radix8_butterflies(r0, r1, r2, r3, r4, r5, r6, r7, t);
    let ghost s3 = seq![r0@, r1@, r2@, r3@, r4@, r5@, r6@, r7@];
    proof {
        let fs = seq![p0, p1, p2, p3, p4, p5, p6, p7];
        let rest = gp;
        gp.tracked_union_prefer_right(p0);
        gp.tracked_union_prefer_right(p1);
        gp.tracked_union_prefer_right(p2);
        gp.tracked_union_prefer_right(p3);
        gp.tracked_union_prefer_right(p4);
        gp.tracked_union_prefer_right(p5);
        gp.tracked_union_prefer_right(p6);
        gp.tracked_union_prefer_right(p7);
        reveal_with_fuel(union_all, 9);
        assert(gp == union_all(rest, fs, 8));
        assert forall|i: int| 0 <= i < 8 implies owns(#[trigger] fs[i], base, i * stride + off, m as int) && s3[i] == vals(
            fs[i],
            i * stride + off,
            m as int,
        ) by {
            if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {} else if i == 5 {} else if i == 6 {} else {}
        }
        assert forall|i: int, lane: int| 0 <= i < 8 && 0 <= lane < m implies (#[trigger] s0[i][lane]) == g0[i * stride + off + lane].value() by {
            if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {} else if i == 5 {} else if i == 6 {} else {}
        }
        lemma_group_rows_back(g0, rest, fs, base, off as int, stride as int, 8, m, s0, s3);
    }
    Tracked(gp)
}

/// The body of the closure that `butterfly_interleaved_fused_2layer` hands `fused_rows`: layers L and
/// L+1 on one group of four rows.
///
/// Rewritten: the four rows are four arguments (production's `let [row_a, row_b, row_c, row_d] = rows`).
fn radix4_rows(row_a: &mut [F64], row_b: &mut [F64], row_c: &mut [F64], row_d: &mut [F64], t_outer: F64, t_inner_a: F64, t_inner_b: F64)
    requires
        rows_shape(seq![old(row_a)@, old(row_b)@, old(row_c)@, old(row_d)@], 4, old(row_a)@.len()),
    ensures
        rows_shape(seq![final(row_a)@, final(row_b)@, final(row_c)@, final(row_d)@], 4, old(row_a)@.len()),
        rows_seq(seq![final(row_a)@, final(row_b)@, final(row_c)@, final(row_d)@], old(row_a)@.len()) == layer2(
            rows_seq(seq![old(row_a)@, old(row_b)@, old(row_c)@, old(row_d)@], old(row_a)@.len()),
            old(row_a)@.len(),
            1,
            t_outer.0,
            t_inner_a.0,
            t_inner_b.0,
        ),
{
    let ghost m = row_a@.len();
    let ghost s0 = seq![row_a@, row_b@, row_c@, row_d@];
    // Layer L: rows 2 apart, one twiddle for the block.
    butterfly_lanes(row_a, row_c, t_outer);
    butterfly_lanes(row_b, row_d, t_outer);
    let ghost s1 = seq![row_a@, row_b@, row_c@, row_d@];
    // Layer L+1: adjacent rows, one twiddle per half.
    butterfly_lanes(row_a, row_b, t_inner_a);
    butterfly_lanes(row_c, row_d, t_inner_b);
    let ghost s2 = seq![row_a@, row_b@, row_c@, row_d@];
    proof {
        let tw0 = |b: int| t_outer.0;
        let tw1 = pick2(t_inner_a.0, t_inner_b.0);
        assert(rows_shape(s1, 4, m) && rows_shape(s2, 4, m));
        lemma_radix4_layer_a(s0, s1, m, tw0);
        lemma_radix4_layer_b(s1, s2, m, tw1);
        if m > 0 {
            assert(4nat % (2 * 2nat) == 0 && 4nat % (2 * 1nat) == 0) by (compute);
            lemma_rows_layer(s0, s1, m, 2, tw0);
            lemma_rows_layer(s1, s2, m, 1, tw1);
        } else {
            assert(rows_seq(s2, m) =~= layer2(rows_seq(s0, m), m, 1, t_outer.0, t_inner_a.0, t_inner_b.0));
        }
    }
}

/// The rows of group `off` of a block of four slabs, built as `fused_rows` builds them, through the
/// radix-4 butterflies: production's `fused_rows` loop body for `N = 4`, written out per row as
/// [`radix8_group`] is.
fn radix4_group(
    base: *mut F64,
    stride: usize,
    off: usize,
    num_ntts: usize,
    gp: Tracked<Map<int, PointsTo<F64>>>,
    t_outer: F64,
    t_inner_a: F64,
    t_inner_b: F64,
) -> (res: Tracked<Map<int, PointsTo<F64>>>)
    requires
        num_ntts > 0,
        holds_group(gp@, base, off as int, stride as int, 4, num_ntts as nat),
    ensures
        res@.dom() == gp@.dom(),
        forall|k: int| #[trigger] gp@.dom().contains(k) ==> res@[k].ptr() == gp@[k].ptr() && res@[k].is_init(),
        group_seq(res@, off as int, stride as int, 4, num_ntts as nat) == layer2(
            group_seq(gp@, off as int, stride as int, 4, num_ntts as nat),
            num_ntts as nat,
            1,
            t_outer.0,
            t_inner_a.0,
            t_inner_b.0,
        ),
{
    let ghost g0 = gp@;
    let ghost m = num_ntts as nat;
    let tracked mut gp = gp.get();
    proof {
        lemma_row_in_group(g0, base, off as int, stride as int, 4, m, 0);
        lemma_row_in_group(g0, base, off as int, stride as int, 4, m, 1);
        lemma_row_in_group(g0, base, off as int, stride as int, 4, m, 2);
        lemma_row_in_group(g0, base, off as int, stride as int, 4, m, 3);
    }
    let tracked mut p0 = take_row(&mut gp, base, (0 * stride + off) as int, m);
    let tracked mut p1 = take_row(&mut gp, base, (1 * stride + off) as int, m);
    let tracked mut p2 = take_row(&mut gp, base, (2 * stride + off) as int, m);
    let tracked mut p3 = take_row(&mut gp, base, (3 * stride + off) as int, m);
    // SAFETY:
    // - The groups are disjoint, as argued above.
    // - The row ends inside its slab, since the row index is below the slab height.
    let row_a = unsafe { from_raw_parts_mut(base.add(0 * stride + off), num_ntts, Ghost(base), Ghost((0 * stride + off) as int), Tracked(&mut p0)) };
    let row_b = unsafe { from_raw_parts_mut(base.add(1 * stride + off), num_ntts, Ghost(base), Ghost((1 * stride + off) as int), Tracked(&mut p1)) };
    let row_c = unsafe { from_raw_parts_mut(base.add(2 * stride + off), num_ntts, Ghost(base), Ghost((2 * stride + off) as int), Tracked(&mut p2)) };
    let row_d = unsafe { from_raw_parts_mut(base.add(3 * stride + off), num_ntts, Ghost(base), Ghost((3 * stride + off) as int), Tracked(&mut p3)) };
    let ghost s0 = seq![row_a@, row_b@, row_c@, row_d@];
    radix4_rows(row_a, row_b, row_c, row_d, t_outer, t_inner_a, t_inner_b);
    let ghost s2 = seq![row_a@, row_b@, row_c@, row_d@];
    proof {
        let fs = seq![p0, p1, p2, p3];
        let rest = gp;
        gp.tracked_union_prefer_right(p0);
        gp.tracked_union_prefer_right(p1);
        gp.tracked_union_prefer_right(p2);
        gp.tracked_union_prefer_right(p3);
        reveal_with_fuel(union_all, 5);
        assert(gp == union_all(rest, fs, 4));
        assert forall|i: int| 0 <= i < 4 implies owns(#[trigger] fs[i], base, i * stride + off, m as int) && s2[i] == vals(
            fs[i],
            i * stride + off,
            m as int,
        ) by {
            if i == 0 {} else if i == 1 {} else if i == 2 {} else {}
        }
        assert forall|i: int, lane: int| 0 <= i < 4 && 0 <= lane < m implies (#[trigger] s0[i][lane]) == g0[i * stride + off + lane].value() by {
            if i == 0 {} else if i == 1 {} else if i == 2 {} else {}
        }
        lemma_group_rows_back(g0, rest, fs, base, off as int, stride as int, 4, m, s0, s2);
    }
    Tracked(gp)
}

/// Group `r` of a block of slabs `stride` words long takes row `r` of every slab: the words whose offset in
/// their slab, divided by the row width `m`, is `r`.
pub open spec fn group_owner(stride: int, m: int) -> spec_fn(int) -> int {
    |k: int| (k % stride) / m
}

/// The permissions of group `r` of a block: a group as [`holds_group`] describes it.
proof fn lemma_group_of_block(perms: Map<int, PointsTo<F64>>, base: *mut F64, x: Seq<F64>, n: nat, stride_rows: nat, m: nat, r: int)
    requires
        n > 0,
        m > 0,
        0 <= r < stride_rows,
        owns(perms, base, 0, (n * (stride_rows * m)) as int),
        x.len() == n * (stride_rows * m),
        n * (stride_rows * m) <= usize::MAX,
        forall|k: int|
            0 <= k < x.len() && (group_owner((stride_rows * m) as int, m as int))(k) >= r ==> #[trigger] perms[k].value() == x[k],
    ensures
        ({
            let gp = perms.restrict(keys_of(perms, group_owner((stride_rows * m) as int, m as int), r, r + 1));
            group_pre(gp, base, r * m, (stride_rows * m) as int, n, m, x)
        }),
{
    let stride = (stride_rows * m) as int;
    let owner = group_owner(stride, m as int);
    let gp = perms.restrict(keys_of(perms, owner, r, r + 1));
    assert(stride > 0) by (nonlinear_arith)
        requires
            stride == stride_rows * m,
            r < stride_rows,
            r >= 0,
            m > 0,
    ;
    assert(r * m + m <= stride) by (nonlinear_arith)
        requires
            stride == stride_rows * m,
            r + 1 <= stride_rows,
    ;
    assert(r * m >= 0) by (nonlinear_arith)
        requires
            r >= 0,
    ;
    assert forall|k: int| #[trigger] gp.dom().contains(k) <==> 0 <= k < n * stride && r * m <= k % stride < r * m + m by {
        if 0 <= k {
            lemma_mod_bound(k, stride);
            lemma_chunk_keys(k % stride, r, m as int);
        }
    }
    assert((r * m) % (m as int) == 0) by {
        lemma_mod_multiples_basic(r, m as int);
    }
    assert forall|k: int| #[trigger] gp.dom().contains(k) implies gp[k].value() == x[k] by {
        lemma_mod_bound(k, stride);
        lemma_chunk_keys(k % stride, r, m as int);
    }
}

/// Visit every row group of a fused multi-layer block.
///
/// ```text
///     the block is N slabs of equal height
///
///     slab 0:     row 0   row 1   ...   row r   ...
///     slab 1:     row 0   row 1   ...   row r   ...
///     ...
///     slab N-1:   row 0   row 1   ...   row r   ...
///
///     group r  =  row r of every slab
/// ```
///
/// # Why the rows are disjoint
///
/// - Distinct groups take distinct rows inside each slab.
/// - The slabs do not overlap.
/// - So the groups are pairwise disjoint, and one base pointer can stand in for N nested splits.
///
/// Verified: group `r` receives exactly the permissions of its rows, taken from the block's; `do_one`
/// returns them with the values `target`, so the block ends as `target`. Rewritten: production builds the
/// `N` rows here with `std::array::from_fn` and passes `&mut rows`; Verus supports neither, so `do_one`
/// receives the base pointer, the stride, the row offset and the group's permissions, and builds the rows
/// itself ([`radix8_group`], [`radix4_group`]). The `debug_assert_eq!` is a proven `assert`, and the target
/// is a ghost argument.
fn fused_rows<const N: usize, F>(block: &mut [F64], stride_rows: usize, num_ntts: usize, do_one: F, Ghost(target): Ghost<Seq<F64>>)
where
    F: Fn(*mut F64, usize, usize, Tracked<Map<int, PointsTo<F64>>>) -> Tracked<Map<int, PointsTo<F64>>>,
    requires
        N > 0,
        num_ntts > 0,
        stride_rows > 0,
        old(block)@.len() == N * (stride_rows * num_ntts),
        old(block)@.len() <= usize::MAX,
        target.len() == old(block)@.len(),
        forall|base: *mut F64, off: usize, gp: Map<int, PointsTo<F64>>|
            group_pre(gp, base, off as int, (stride_rows * num_ntts) as int, N as nat, num_ntts as nat, old(block)@)
                ==> #[trigger] do_one.requires((base, (stride_rows * num_ntts) as usize, off, Tracked(gp))),
        forall|base: *mut F64, off: usize, gp: Map<int, PointsTo<F64>>, res: Tracked<Map<int, PointsTo<F64>>>|
            group_pre(gp, base, off as int, (stride_rows * num_ntts) as int, N as nat, num_ntts as nat, old(block)@)
                && #[trigger] do_one.ensures((base, (stride_rows * num_ntts) as usize, off, Tracked(gp)), res) ==> group_post(
                res@,
                gp,
                target,
            ),
    ensures
        final(block)@ == target,
{
    let ghost x0 = block@;
    let ghost len = x0.len() as int;
    // Words from one slab to the next.
    proof {
        assert(stride_rows * num_ntts <= N * (stride_rows * num_ntts)) by (nonlinear_arith)
            requires
                N > 0,
        ;
    }
    let stride = stride_rows * num_ntts;
    assert(block.len() == N * stride);
    // Rewritten from `block.as_mut_ptr()`: the pointer comes with the block's permissions.
    let (base, Tracked(perms)) = slice_as_mut_ptr(block);
    let ghost owner = group_owner(stride as int, num_ntts as int);
    for r in 0..stride_rows
        invariant
            N > 0,
            num_ntts > 0,
            stride == stride_rows * num_ntts,
            len == N * stride,
            x0.len() == len,
            len <= usize::MAX,
            target.len() == len,
            owner == group_owner(stride as int, num_ntts as int),
            owns(*perms, base, 0, len),
            forall|k: int| 0 <= k < len && owner(k) < r ==> #[trigger] perms[k].value() == target[k],
            forall|k: int| 0 <= k < len && owner(k) >= r ==> #[trigger] perms[k].value() == x0[k],
            forall|base: *mut F64, off: usize, gp: Map<int, PointsTo<F64>>|
                group_pre(gp, base, off as int, stride as int, N as nat, num_ntts as nat, x0)
                    ==> #[trigger] do_one.requires((base, stride, off, Tracked(gp))),
            forall|base: *mut F64, off: usize, gp: Map<int, PointsTo<F64>>, res: Tracked<Map<int, PointsTo<F64>>>|
                group_pre(gp, base, off as int, stride as int, N as nat, num_ntts as nat, x0)
                    && #[trigger] do_one.ensures((base, stride, off, Tracked(gp)), res) ==> group_post(res@, gp, target),
    {
        proof {
            assert(r * num_ntts < stride) by (nonlinear_arith)
                requires
                    r < stride_rows,
                    stride == stride_rows * num_ntts,
                    num_ntts > 0,
            ;
        }
        // Row `r` of each slab starts this many words into it.
        let off = r * num_ntts;
        let ghost cur = *perms;
        proof {
            lemma_group_of_block(cur, base, x0, N as nat, stride_rows as nat, num_ntts as nat, r as int);
        }
        let tracked gp = perms.tracked_remove_keys(keys_of(cur, owner, r as int, r + 1));
        let ghost g = gp;
        let Tracked(res) = do_one(base, stride, off, Tracked(gp));
        proof {
            perms.tracked_union_prefer_right(res);
            assert(perms.dom() =~= cur.dom());
            assert forall|k: int| 0 <= k < len implies (#[trigger] perms[k]).ptr() == ptr_at(base, k) && perms[k].is_init() && (owner(k) < r + 1 ==> perms[k].value() == target[k]) && (owner(k) >= r + 1 ==> perms[k].value() == x0[k]) by {
                if owner(k) == r {
                    assert(g.dom().contains(k));
                } else {
                    assert(!g.dom().contains(k));
                }
            }
        }
    }
    proof {
        assert forall|k: int| 0 <= k < len implies perms[k].value() == target[k] by {
            lemma_mod_bound(k, stride as int);
            lemma_div_is_ordered(k % (stride as int), stride as int, num_ntts as int);
            lemma_div_multiples_vanish(stride_rows as int, num_ntts as int);
            lemma_mul_is_commutative(stride_rows as int, num_ntts as int);
            if owner(k) >= stride_rows {
                lemma_fundamental_div_mod(k % (stride as int), num_ntts as int);
                lemma_mod_bound(k % (stride as int), num_ntts as int);
                assert(false) by (nonlinear_arith)
                    requires
                        k % (stride as int) == num_ntts * owner(k) + (k % (stride as int)) % (num_ntts as int),
                        (k % (stride as int)) % (num_ntts as int) >= 0,
                        owner(k) >= stride_rows,
                        k % (stride as int) < stride,
                        stride == stride_rows * num_ntts,
                        num_ntts > 0,
                ;
            }
        }
        assert(vals(*perms, 0, len) =~= target);
    }
}

/// Layers L, L+1 and L+2 fused into one sweep over a layer-L block.
///
/// ```text
///     a group is 8 rows, e = (block rows) / 8 apart:  r, r + e, ..., r + 7e
///
///     layer L     pairs rows 4e apart
///     layer L+1   pairs rows 2e apart
///     layer L+2   pairs rows  e apart
/// ```
///
/// - The eight rows stay in L1 across all twelve butterflies.
/// - The seven twiddles are breadth-first: one for layer L, two for L+1, four for L+2.
///
/// The closure builds its group's rows from the permissions `fused_rows` hands it (see [`fused_rows`]).
fn butterfly_interleaved_fused_3layer(block: &mut [F64], t: &[F64; 7], eighth: usize, num_ntts: usize)
    requires
        eighth > 0,
        num_ntts > 0,
        old(block)@.len() == 8 * (eighth * num_ntts),
        old(block)@.len() <= usize::MAX,
    ensures
        final(block)@ == layer3(old(block)@, num_ntts as nat, eighth as nat, t@),
{
    let ghost x0 = block@;
    let ghost target = layer3(x0, num_ntts as nat, eighth as nat, t@);
    proof {
        lemma_layer3_len(x0, num_ntts as nat, eighth as nat, t@);
    }
    fused_rows::<8, _>(
        block,
        eighth,
        num_ntts,
        |base: *mut F64, stride: usize, off: usize, gp: Tracked<Map<int, PointsTo<F64>>>| -> (res: Tracked<Map<int, PointsTo<F64>>>)
            requires
                eighth > 0,
                num_ntts > 0,
                stride == eighth * num_ntts,
                x0.len() == 8 * stride,
                group_pre(gp@, base, off as int, stride as int, 8, num_ntts as nat, x0),
            ensures
                group_post(res@, gp@, layer3(x0, num_ntts as nat, eighth as nat, t@)),
        {
            let res = radix8_group(base, stride, off, num_ntts, gp, t);
            proof {
                let m = num_ntts as nat;
                let e = eighth as nat;
                let r = off / num_ntts;
                lemma_group_seq(gp@, base, x0, off as int, 8, m, e);
                lemma_fundamental_div_mod(off as int, num_ntts as int);
                assert(r < e) by (nonlinear_arith)
                    requires
                        off as int == num_ntts * r + (off as int) % (num_ntts as int),
                        (off as int) % (num_ntts as int) == 0,
                        off + num_ntts <= stride,
                        stride == e * num_ntts,
                        num_ntts > 0,
                ;
                assert(x0.len() == 8 * e * m) by (nonlinear_arith)
                    requires
                        x0.len() == 8 * stride,
                        stride == e * m,
                ;
                lemma_gather_layer3(x0, m, e, t@, r as int);
                lemma_layer3_len(x0, m, e, t@);
                lemma_group_back(gp@, res@, base, layer3(x0, m, e, t@), off as int, 8, m, e);
            }
            res
        },
        Ghost(target),
    );
}

proof fn lemma_layer3_len(x: Seq<F64>, m: nat, e: nat, t: Seq<F64>)
    ensures
        layer3(x, m, e, t).len() == x.len(),
{
}

proof fn lemma_layer2_len(x: Seq<F64>, m: nat, e: nat, a: u64, b: u64, c: u64)
    ensures
        layer2(x, m, e, a, b, c).len() == x.len(),
{
}

/// Layers L and L+1 fused into one sweep over a layer-L block, four rows at a time.
///
/// The closure builds its group's rows from the permissions `fused_rows` hands it (see [`fused_rows`]);
/// its four butterflies are [`radix4_rows`].
fn butterfly_interleaved_fused_2layer(
    block: &mut [F64],
    t_outer: F64,
    t_inner_a: F64,
    t_inner_b: F64,
    quarter: usize,
    num_ntts: usize,
)
    requires
        quarter > 0,
        num_ntts > 0,
        old(block)@.len() == 4 * (quarter * num_ntts),
        old(block)@.len() <= usize::MAX,
    ensures
        final(block)@ == layer2(old(block)@, num_ntts as nat, quarter as nat, t_outer.0, t_inner_a.0, t_inner_b.0),
{
    let ghost x0 = block@;
    let ghost target = layer2(x0, num_ntts as nat, quarter as nat, t_outer.0, t_inner_a.0, t_inner_b.0);
    fused_rows::<4, _>(
        block,
        quarter,
        num_ntts,
        |base: *mut F64, stride: usize, off: usize, gp: Tracked<Map<int, PointsTo<F64>>>| -> (res: Tracked<Map<int, PointsTo<F64>>>)
            requires
                quarter > 0,
                num_ntts > 0,
                stride == quarter * num_ntts,
                x0.len() == 4 * stride,
                group_pre(gp@, base, off as int, stride as int, 4, num_ntts as nat, x0),
            ensures
                group_post(res@, gp@, layer2(x0, num_ntts as nat, quarter as nat, t_outer.0, t_inner_a.0, t_inner_b.0)),
        {
            let res = radix4_group(base, stride, off, num_ntts, gp, t_outer, t_inner_a, t_inner_b);
            proof {
                let m = num_ntts as nat;
                let e = quarter as nat;
                let r = off / num_ntts;
                lemma_group_seq(gp@, base, x0, off as int, 4, m, e);
                lemma_fundamental_div_mod(off as int, num_ntts as int);
                assert(r < e) by (nonlinear_arith)
                    requires
                        off as int == num_ntts * r + (off as int) % (num_ntts as int),
                        (off as int) % (num_ntts as int) == 0,
                        off + num_ntts <= stride,
                        stride == e * num_ntts,
                        num_ntts > 0,
                ;
                assert(x0.len() == 4 * e * m) by (nonlinear_arith)
                    requires
                        x0.len() == 4 * stride,
                        stride == e * m,
                ;
                lemma_gather_layer2(x0, m, e, t_outer.0, t_inner_a.0, t_inner_b.0, r as int);
                lemma_layer2_len(x0, m, e, t_outer.0, t_inner_a.0, t_inner_b.0);
                lemma_group_back(gp@, res@, base, layer2(x0, m, e, t_outer.0, t_inner_a.0, t_inner_b.0), off as int, 4, m, e);
            }
            res
        },
        Ghost(target),
    );
}

/// One layer on one block of `2 * block_size_half` rows.
///
/// Rewritten: the `split_at_mut` halves are bound to their lengths once more for the proof (no exec change).
#[inline]
fn butterfly_interleaved_block(block: &mut [F64], twiddle: F64, block_size_half: usize, num_ntts: usize)
    requires
        num_ntts > 0,
        block_size_half > 0,
        old(block)@.len() == 2 * (block_size_half * num_ntts),
        old(block)@.len() <= usize::MAX,
    ensures
        final(block)@ == layer_map(old(block)@, num_ntts as nat, block_size_half as nat, |b: int| twiddle.0, false),
{
    let ghost x0 = block@;
    let ghost m = num_ntts as int;
    let ghost h = block_size_half as int;
    proof {
        assert(block_size_half * num_ntts <= 2 * (block_size_half * num_ntts)) by (nonlinear_arith);
    }
    let half_offset = block_size_half * num_ntts;
    let (top, bot) = block.split_at_mut(half_offset);
    let ghost (top0, bot0) = (top@, bot@);
    assert(0 * m == 0);
    for r in 0..block_size_half
        invariant
            m == num_ntts,
            h == block_size_half,
            m > 0,
            half_offset == h * m,
            top0.len() == half_offset,
            bot0.len() == half_offset,
            top@.len() == half_offset,
            bot@.len() == half_offset,
            forall|p: int|
                0 <= p < r * m ==> (#[trigger] top@[p]).0 == bf_top(top0[p].0, bot0[p].0, twiddle.0) && bot@[p].0 == bf_bot(
                    top0[p].0,
                    bot0[p].0,
                    twiddle.0,
                ),
            forall|p: int| r * m <= p < half_offset ==> #[trigger] top@[p] == top0[p] && bot@[p] == bot0[p],
    {
        proof {
            assert((r + 1) * m <= h * m) by (nonlinear_arith)
                requires
                    r + 1 <= h,
                    m > 0,
            ;
            assert((r + 1) * m == r * m + m) by (nonlinear_arith);
        }
        let off = r * num_ntts;
        let ghost (t1, b1) = (top@, bot@);
        butterfly_lanes(&mut top[off..off + num_ntts], &mut bot[off..off + num_ntts], twiddle);
        proof {
            assert forall|p: int| 0 <= p < (r + 1) * m implies (#[trigger] top@[p]).0 == bf_top(top0[p].0, bot0[p].0, twiddle.0)
                && bot@[p].0 == bf_bot(top0[p].0, bot0[p].0, twiddle.0) by {
                if p >= r * m {
                    let j = p - off;
                    assert(top@[p] == top@.subrange(off as int, off + m)[j]);
                    assert(bot@[p] == bot@.subrange(off as int, off + m)[j]);
                    assert(t1.subrange(off as int, off + m)[j] == t1[p]);
                    assert(b1.subrange(off as int, off + m)[j] == b1[p]);
                    assert((top@.subrange(off as int, off + m)[j].0, bot@.subrange(off as int, off + m)[j].0) == butterfly_spec(
                        false,
                        t1.subrange(off as int, off + m)[j].0,
                        b1.subrange(off as int, off + m)[j].0,
                        twiddle.0,
                    ));
                } else {
                    assert(top@[p] == top@.subrange(0, off as int)[p]);
                    assert(bot@[p] == bot@.subrange(0, off as int)[p]);
                }
            }
            assert forall|p: int| (r + 1) * m <= p < half_offset implies #[trigger] top@[p] == top0[p] && bot@[p] == bot0[p] by {
                assert(top@[p] == top@.subrange(off + m, half_offset as int)[p - off - m]);
                assert(bot@[p] == bot@.subrange(off + m, half_offset as int)[p - off - m]);
            }
        }
    }
    proof {
        let y = layer_map(x0, num_ntts as nat, block_size_half as nat, |b: int| twiddle.0, false);
        assert(x0 == top0 + bot0);
        let fin = top@ + bot@;
        assert forall|p: int| 0 <= p < x0.len() implies fin[p] == y[p] by {
            lemma_split_word(p, m);
            let row = p / m;
            assert(row < 2 * h) by (nonlinear_arith)
                requires
                    p == row * m + p % m,
                    p % m >= 0,
                    p < 2 * (h * m),
                    m > 0,
            ;
            lemma_small_div(row, 2 * h);
            assert(row_of(p, num_ntts as nat) == row);
            assert(blk_of(p, num_ntts as nat, block_size_half as nat) == 0);
            assert(r_of(p, num_ntts as nat, block_size_half as nat) == row);
            if row < h {
                assert(p < h * m) by (nonlinear_arith)
                    requires
                        p == row * m + p % m,
                        p % m < m,
                        row + 1 <= h,
                ;
                assert(x0[p + h * m] == bot0[p]);
                assert(x0[p] == top0[p]);
                assert(fin[p] == top@[p]);
                assert(top@[p].0 == bf_top(top0[p].0, bot0[p].0, twiddle.0));
                assert(y[p] == F64(bf_top(x0[p].0, x0[p + h * m].0, twiddle.0)));
            } else {
                assert(p >= h * m) by (nonlinear_arith)
                    requires
                        p == row * m + p % m,
                        p % m >= 0,
                        row >= h,
                        m > 0,
                ;
                assert(x0[p - h * m] == top0[p - h * m]);
                assert(x0[p] == bot0[p - h * m]);
                assert(fin[p] == bot@[p - h * m]);
                assert(top@[p - h * m].0 == bf_top(top0[p - h * m].0, bot0[p - h * m].0, twiddle.0));
                assert(bot@[p - h * m].0 == bf_bot(top0[p - h * m].0, bot0[p - h * m].0, twiddle.0));
                assert(y[p] == F64(bf_bot(x0[p - h * m].0, x0[p].0, twiddle.0)));
            }
        }
        assert(fin =~= y);
    }
}

/// A row below the block size is in block 0, at itself.
proof fn lemma_small_div(row: int, n: int)
    requires
        0 <= row < n,
    ensures
        row / n == 0,
        row % n == row,
{
    lemma_fundamental_div_mod_converse(row, n, 0, row);
}

// ---------------------------------------------------------------------------------------------
// Layers on one sub-block
// ---------------------------------------------------------------------------------------------
/// `buf` is `prev` with its first `n_done` words replaced by those of `target`.
pub open spec fn swept_to(buf: Seq<F64>, prev: Seq<F64>, target: Seq<F64>, n_done: int) -> bool {
    &&& buf.len() == prev.len()
    &&& target.len() == prev.len()
    &&& forall|p: int| 0 <= p < n_done ==> #[trigger] buf[p] == target[p]
    &&& forall|p: int| n_done <= p < prev.len() ==> #[trigger] buf[p] == prev[p]
}

/// Layers with twiddles that agree on the blocks of the buffer are equal.
pub proof fn lemma_layer_map_tw_n(x: Seq<F64>, m: nat, h: nat, tw: spec_fn(int) -> u64, tw2: spec_fn(int) -> u64, nb: nat)
    requires
        m > 0,
        h > 0,
        x.len() == nb * (2 * h * m),
        forall|b: int| 0 <= b < nb ==> #[trigger] tw(b) == tw2(b),
    ensures
        layer_map(x, m, h, tw, false) == layer_map(x, m, h, tw2, false),
{
    assert forall|p: int| 0 <= p < x.len() implies layer_map(x, m, h, tw, false)[p] == layer_map(x, m, h, tw2, false)[p] by {
        let mi = m as int;
        lemma_split_word(p, mi);
        let row = p / mi;
        assert(row < nb * (2 * h)) by (nonlinear_arith)
            requires
                p == row * mi + p % mi,
                p % mi >= 0,
                p < nb * (2 * h * m),
                mi == m,
                m > 0,
        ;
        lemma_div_pos_is_pos(row, 2 * h as int);
        lemma_div_is_ordered(row, nb * (2 * h) - 1, 2 * h as int);
        assert(nb * (2 * h) - 1 == (nb - 1) * (2 * h) + (2 * h - 1)) by (nonlinear_arith)
            requires
                nb >= 1,
        ;
        lemma_div_multiples_vanish_fancy(nb - 1, 2 * h - 1, 2 * h as int);
        assert((nb - 1) * (2 * h) == (2 * h) * (nb - 1)) by (nonlinear_arith);
    }
    assert(layer_map(x, m, h, tw, false) =~= layer_map(x, m, h, tw2, false));
}

/// Block `b` of a layer of a sub-block: the target layers, restricted to it, are the layers of the block
/// as sub-block `s * 2^(layer - o) + b` of `2^layer`.
proof fn lemma_block_target(tab: Seq<Seq<F64>>, prev: Seq<F64>, m: nat, log_d: nat, o: nat, s: int, layer: nat, c: nat, b: int)
    requires
        m > 0,
        o <= layer,
        layer + c <= log_d,
        s >= 0,
        0 <= b < pow2((layer - o) as nat),
        prev.len() == m * pow2((log_d - o) as nat),
    ensures
        ({
            let be = pow2((log_d - layer) as nat) * m;
            let s2 = s * pow2((layer - o) as nat) + b;
            &&& (b + 1) * be <= prev.len()
            &&& b * be + be == (b + 1) * be
            &&& b * be >= 0
            &&& be > 0
            &&& sub_layers(tab, prev, m, log_d, o, s, layer, layer + c).subrange(b * be, b * be + be) == sub_layers(
                tab,
                prev.subrange(b * be, b * be + be),
                m,
                log_d,
                layer,
                s2,
                layer,
                layer + c,
            )
        }),
{
    let bs = pow2((log_d - layer) as nat) as int;
    let be = bs * m;
    let po = pow2((layer - o) as nat) as int;
    let s2 = s * po + b;
    let target = sub_layers(tab, prev, m, log_d, o, s, layer, layer + c);
    lemma_sub_layers_len(tab, prev, m, log_d, o, s, layer, layer + c);
    lemma_pow2_pos((log_d - layer) as nat);
    lemma_pow2_adds((layer - o) as nat, (log_d - layer) as nat);
    assert((layer - o) as nat + (log_d - layer) as nat == (log_d - o) as nat);
    assert(pow2(0) == 1) by {
        lemma2_to64();
    }
    assert(s * po <= s2 < (s + 1) * po) by (nonlinear_arith)
        requires
            s2 == s * po + b,
            0 <= b < po,
    ;
    lemma_gather_sub_layers(tab, prev, m, log_d, o, s, log_d, layer, s2, 0, layer, layer + c);
    assert((b + 1) * bs * m <= prev.len()) by (nonlinear_arith)
        requires
            b + 1 <= po,
            prev.len() == m * (po * bs),
            bs > 0,
    ;
    assert(b * bs >= 0) by (nonlinear_arith)
        requires
            b >= 0,
            bs > 0,
    ;
    assert((b * bs + bs) * m == (b + 1) * bs * m) by (nonlinear_arith);
    lemma_gather_contiguous(target, m, b * bs, bs as nat);
    lemma_gather_contiguous(prev, m, b * bs, bs as nat);
    assert(b * bs * m == b * be && (b * bs + bs) * m == b * be + be && (b + 1) * be == b * be + be) by (nonlinear_arith)
        requires
            be == bs * m,
    ;
    assert(be > 0) by (nonlinear_arith)
        requires
            be == bs * m,
            bs > 0,
            m > 0,
    ;
    assert(b * be >= 0) by (nonlinear_arith)
        requires
            b >= 0,
            be > 0,
    ;
    assert(s2 - s * po == b);
}

/// One block done: the sweep moves past it.
proof fn lemma_block_swept(before: Seq<F64>, after: Seq<F64>, prev: Seq<F64>, target: Seq<F64>, start: int, be: int)
    requires
        0 <= start,
        0 <= be,
        start + be <= prev.len(),
        swept_to(before, prev, target, start),
        after == before.subrange(0, start) + target.subrange(start, start + be) + before.subrange(start + be, before.len() as int),
    ensures
        swept_to(after, prev, target, start + be),
{
    assert forall|p: int| 0 <= p < start + be implies #[trigger] after[p] == target[p] by {
        if p < start {
            assert(after[p] == before.subrange(0, start)[p]);
        } else {
            assert(after[p] == target.subrange(start, start + be)[p - start]);
        }
    }
    assert forall|p: int| start + be <= p < prev.len() implies #[trigger] after[p] == prev[p] by {
        assert(after[p] == before.subrange(start + be, before.len() as int)[p - start - be]);
    }
}

/// Three layers on one block, as the fused sweep runs them with `twiddles_radix8`'s twiddles.
proof fn lemma_sub3(tab: Seq<Seq<F64>>, blk: Seq<F64>, m: nat, log_d: nat, layer: nat, s2: int, t: Seq<F64>)
    requires
        m > 0,
        layer + 3 <= log_d,
        blk.len() == m * pow2((log_d - layer) as nat),
        t.len() == 7,
        t[0].0 == twiddle_spec(tab, layer, s2 as usize),
        t[1].0 == twiddle_spec(tab, layer + 1, (2 * s2) as usize),
        t[2].0 == twiddle_spec(tab, layer + 1, (2 * s2 + 1) as usize),
        t[3].0 == twiddle_spec(tab, layer + 2, (4 * s2) as usize),
        t[4].0 == twiddle_spec(tab, layer + 2, (4 * s2 + 1) as usize),
        t[5].0 == twiddle_spec(tab, layer + 2, (4 * s2 + 2) as usize),
        t[6].0 == twiddle_spec(tab, layer + 2, (4 * s2 + 3) as usize),
    ensures
        sub_layers(tab, blk, m, log_d, layer, s2, layer, layer + 3) == layer3(blk, m, pow2((log_d - layer - 3) as nat), t),
{
    let e = pow2((log_d - layer - 3) as nat);
    lemma_pow2_unfold((log_d - layer) as nat);
    lemma_pow2_unfold((log_d - layer - 1) as nat);
    lemma_pow2_unfold((log_d - layer - 2) as nat);
    lemma_pow2_pos((log_d - layer - 3) as nat);
    lemma2_to64();
    assert(layer_half(log_d, layer) == 4 * e);
    assert(layer_half(log_d, layer + 1) == 2 * e);
    assert(layer_half(log_d, layer + 2) == e);
    let x0 = blk;
    let x1 = layer_map(x0, m, 4 * e, sub_twiddles(tab, layer, layer, s2), false);
    let y1 = layer_map(x0, m, 4 * e, |b: int| t[0].0, false);
    assert(blk.len() == 1 * (2 * (4 * e) * m)) by (nonlinear_arith)
        requires
            blk.len() == m * (2 * (2 * (2 * e))),
    ;
    lemma_layer_map_tw_n(x0, m, 4 * e, sub_twiddles(tab, layer, layer, s2), |b: int| t[0].0, 1);
    assert(x1.len() == 2 * (2 * (2 * e) * m)) by (nonlinear_arith)
        requires
            x1.len() == 1 * (2 * (4 * e) * m),
    ;
    let x2 = layer_map(x1, m, 2 * e, sub_twiddles(tab, layer + 1, layer, s2), false);
    assert forall|b: int| 0 <= b < 2 implies #[trigger] (sub_twiddles(tab, layer + 1, layer, s2))(b) == (|b: int| t[1 + b].0)(b) by {
        assert(pow2(((layer + 1) - layer) as nat) == 2);
        if b == 0 {} else {}
    }
    lemma_layer_map_tw_n(x1, m, 2 * e, sub_twiddles(tab, layer + 1, layer, s2), |b: int| t[1 + b].0, 2);
    assert(x2.len() == 4 * (2 * e * m)) by (nonlinear_arith)
        requires
            x2.len() == 2 * (2 * (2 * e) * m),
    ;
    assert forall|b: int| 0 <= b < 4 implies #[trigger] (sub_twiddles(tab, layer + 2, layer, s2))(b) == (|b: int| t[3 + b].0)(b) by {
        assert(pow2(((layer + 2) - layer) as nat) == 4);
        if b == 0 {} else if b == 1 {} else if b == 2 {} else {}
    }
    lemma_layer_map_tw_n(x2, m, e, sub_twiddles(tab, layer + 2, layer, s2), |b: int| t[3 + b].0, 4);
    reveal_with_fuel(sub_layers, 4);
    assert(sub_layers(tab, blk, m, log_d, layer, s2, layer, layer + 3) == layer_map(
        x2,
        m,
        e,
        sub_twiddles(tab, layer + 2, layer, s2),
        false,
    ));
}

/// Two layers on one block, as the fused sweep runs them with the block's three twiddles.
proof fn lemma_sub2(tab: Seq<Seq<F64>>, blk: Seq<F64>, m: nat, log_d: nat, layer: nat, s2: int, t_outer: u64, t_inner_a: u64, t_inner_b: u64)
    requires
        m > 0,
        layer + 2 <= log_d,
        blk.len() == m * pow2((log_d - layer) as nat),
        t_outer == twiddle_spec(tab, layer, s2 as usize),
        t_inner_a == twiddle_spec(tab, layer + 1, (2 * s2) as usize),
        t_inner_b == twiddle_spec(tab, layer + 1, (2 * s2 + 1) as usize),
    ensures
        sub_layers(tab, blk, m, log_d, layer, s2, layer, layer + 2) == layer2(
            blk,
            m,
            pow2((log_d - layer - 2) as nat),
            t_outer,
            t_inner_a,
            t_inner_b,
        ),
{
    let e = pow2((log_d - layer - 2) as nat);
    lemma_pow2_unfold((log_d - layer) as nat);
    lemma_pow2_unfold((log_d - layer - 1) as nat);
    lemma_pow2_pos((log_d - layer - 2) as nat);
    lemma2_to64();
    assert(layer_half(log_d, layer) == 2 * e);
    assert(layer_half(log_d, layer + 1) == e);
    let x0 = blk;
    let x1 = layer_map(x0, m, 2 * e, sub_twiddles(tab, layer, layer, s2), false);
    assert(blk.len() == 1 * (2 * (2 * e) * m)) by (nonlinear_arith)
        requires
            blk.len() == m * (2 * (2 * e)),
    ;
    assert(pow2((layer - layer) as nat) == 1);
    assert(s2 * pow2((layer - layer) as nat) == s2) by {
        lemma_mul_basics(s2);
    }
    assert((sub_twiddles(tab, layer, layer, s2))(0) == t_outer);
    lemma_layer_map_tw_n(x0, m, 2 * e, sub_twiddles(tab, layer, layer, s2), |b: int| t_outer, 1);
    assert(x1.len() == 2 * (2 * e * m)) by (nonlinear_arith)
        requires
            x1.len() == 1 * (2 * (2 * e) * m),
    ;
    assert forall|b: int| 0 <= b < 2 implies #[trigger] (sub_twiddles(tab, layer + 1, layer, s2))(b) == (pick2(t_inner_a, t_inner_b))(b) by {
        assert(pow2(((layer + 1) - layer) as nat) == 2);
        if b == 0 {} else {}
    }
    lemma_layer_map_tw_n(x1, m, e, sub_twiddles(tab, layer + 1, layer, s2), pick2(t_inner_a, t_inner_b), 2);
    reveal_with_fuel(sub_layers, 3);
    assert(sub_layers(tab, blk, m, log_d, layer, s2, layer, layer + 2) == layer_map(
        x1,
        m,
        e,
        sub_twiddles(tab, layer + 1, layer, s2),
        false,
    ));
}

/// One layer on one block.
proof fn lemma_sub1(tab: Seq<Seq<F64>>, blk: Seq<F64>, m: nat, log_d: nat, layer: nat, s2: int, t: u64)
    requires
        m > 0,
        layer + 1 <= log_d,
        blk.len() == m * pow2((log_d - layer) as nat),
        t == twiddle_spec(tab, layer, s2 as usize),
    ensures
        sub_layers(tab, blk, m, log_d, layer, s2, layer, layer + 1) == layer_map(
            blk,
            m,
            pow2((log_d - layer - 1) as nat),
            |b: int| t,
            false,
        ),
{
    let h = pow2((log_d - layer - 1) as nat);
    lemma_pow2_unfold((log_d - layer) as nat);
    lemma_pow2_pos((log_d - layer - 1) as nat);
    lemma2_to64();
    assert(blk.len() == 1 * (2 * h * m)) by (nonlinear_arith)
        requires
            blk.len() == m * (2 * h),
    ;
    assert(pow2((layer - layer) as nat) == 1);
    lemma_layer_map_tw_n(blk, m, h, sub_twiddles(tab, layer, layer, s2), |b: int| t, 1);
    reveal_with_fuel(sub_layers, 2);
}

/// The table rows a layer's twiddles read.
proof fn lemma_table_rows(ntt: &AdditiveNttF64, layer: nat)
    requires
        ntt.well_formed(),
        layer < ntt.table().len(),
    ensures
        ntt.table()[ntt.table().len() - layer - 1].len() == layer + 1,
        ntt.table().len() <= 63,
{
}

/// The global index of block `b` of sub-block `s` is below the layer's block count.
proof fn lemma_global_block(s: int, o: nat, layer: nat, b: int)
    requires
        o <= layer,
        0 <= s < pow2(o),
        0 <= b < pow2((layer - o) as nat),
    ensures
        0 <= s * pow2((layer - o) as nat) + b < pow2(layer),
{
    lemma_pow2_adds(o, (layer - o) as nat);
    assert(o + (layer - o) as nat == layer);
    assert(0 <= s * pow2((layer - o) as nat) + b < pow2(o) * pow2((layer - o) as nat)) by (nonlinear_arith)
        requires
            0 <= s < pow2(o),
            0 <= b < pow2((layer - o) as nat),
    ;
}

impl AdditiveNttF64 {
    /// Run a range of layers in place over one sub-block of the domain.
    ///
    /// - The domain has `2^d` rows and splits into `2^o` equal sub-blocks.
    /// - The buffer is one of them; its index fixes the global block index, and so the twiddle, of each block.
    /// - Three layers fuse into one radix-8 sweep where blocks are wide enough, then two, then one.
    ///
    /// Verified: the buffer ends as [`sub_layers`]. Rewritten: the `global` closure carries its
    /// specification (a ghost addition).
    #[allow(clippy::too_many_arguments)]
    pub fn run_layers(
        &self,
        buf: &mut [F64],
        log_d: usize,
        num_ntts: usize,
        first_layer: usize,
        end_layer: usize,
        outer_log: usize,
        sub_idx: usize,
    )
        requires
            self.well_formed(),
            num_ntts > 0,
            outer_log <= first_layer <= end_layer <= log_d <= self.table().len(),
            sub_idx < pow2(outer_log as nat),
            old(buf)@.len() == num_ntts * pow2((log_d - outer_log) as nat),
            old(buf)@.len() <= usize::MAX,
        ensures
            final(buf)@ == sub_layers(
                self.table(),
                old(buf)@,
                num_ntts as nat,
                log_d as nat,
                outer_log as nat,
                sub_idx as int,
                first_layer as nat,
                end_layer as nat,
            ),
    {
        let ghost tab = self.table();
        let ghost b0 = buf@;
        let ghost m = num_ntts as nat;
        let ghost len = b0.len() as int;
        let mut layer = first_layer;
        while layer < end_layer
            invariant
                self.well_formed(),
                tab == self.table(),
                m == num_ntts,
                num_ntts > 0,
                outer_log <= first_layer <= layer <= end_layer <= log_d <= tab.len(),
                sub_idx < pow2(outer_log as nat),
                len == b0.len(),
                len == num_ntts * pow2((log_d - outer_log) as nat),
                len <= usize::MAX,
                buf@ == sub_layers(tab, b0, m, log_d as nat, outer_log as nat, sub_idx as int, first_layer as nat, layer as nat),
            decreases end_layer - layer,
        {
            let ghost prev = buf@;
            proof {
                lemma_sub_layers_len(tab, b0, m, log_d as nat, outer_log as nat, sub_idx as int, first_layer as nat, layer as nat);
                lemma_table_rows(self, layer as nat);
                lemma_usize_pow2_no_overflow((layer - outer_log) as nat);
                lemma_usize_pow2_no_overflow((log_d - layer) as nat);
                lemma_usize_shl_is_mul(1, (layer - outer_log) as usize);
                lemma_usize_shl_is_mul(1, (log_d - layer) as usize);
                lemma_pow2_adds((layer - outer_log) as nat, (log_d - layer) as nat);
                assert((layer - outer_log) as nat + (log_d - layer) as nat == (log_d - outer_log) as nat);
                lemma_pow2_pos((layer - outer_log) as nat);
                lemma_pow2_pos((log_d - layer) as nat);
                assert(pow2((log_d - layer) as nat) * num_ntts <= len) by (nonlinear_arith)
                    requires
                        len == num_ntts * (pow2((layer - outer_log) as nat) * pow2((log_d - layer) as nat)),
                        pow2((layer - outer_log) as nat) >= 1,
                ;
            }
            // This layer's blocks inside the buffer: how many, and their size in rows and words.
            let num_blocks_in_buf = 1usize << (layer - outer_log);
            let block_size = 1usize << (log_d - layer);
            let block_elems = block_size * num_ntts;
            // A block's index in the whole domain, which picks its twiddle.
            let global = |block_in_buf: usize| -> (r: usize)
                requires
                    block_in_buf < num_blocks_in_buf,
                    num_blocks_in_buf == pow2((layer - outer_log) as nat),
                    sub_idx < pow2(outer_log as nat),
                    outer_log <= layer < 64,
                ensures
                    r == sub_idx * num_blocks_in_buf + block_in_buf,
                    r < pow2(layer as nat),
                {
                    proof {
                        lemma_global_block(sub_idx as int, outer_log as nat, layer as nat, block_in_buf as int);
                        lemma_usize_pow2_no_overflow(layer as nat);
                    }
                    sub_idx * num_blocks_in_buf + block_in_buf
                };
            let ghost tw_layers: nat = if layer + 2 < end_layer && block_size >= 8 {
                3
            } else if layer + 1 < end_layer && block_size >= 4 {
                2
            } else {
                1
            };
            let ghost target = sub_layers(tab, prev, m, log_d as nat, outer_log as nat, sub_idx as int, layer as nat, (layer + tw_layers) as nat);
            proof {
                lemma_sub_layers_len(tab, prev, m, log_d as nat, outer_log as nat, sub_idx as int, layer as nat, (layer + tw_layers) as nat);
            }
            if layer + 2 < end_layer && block_size >= 8 {
                // Three layers to go and blocks of at least 8 rows: one radix-8 sweep.
                let eighth = block_size >> 3;
                proof {
                    lemma_usize_shr_is_div(block_size, 3);
                    lemma_pow2_unfold((log_d - layer) as nat);
                    lemma_pow2_unfold((log_d - layer - 1) as nat);
                    lemma_pow2_unfold((log_d - layer - 2) as nat);
                    lemma2_to64();
                    lemma_div_multiples_vanish(pow2((log_d - layer - 3) as nat) as int, 8);
                    assert(eighth == pow2((log_d - layer - 3) as nat));
                    lemma_table_rows(self, (layer + 1) as nat);
                    lemma_table_rows(self, (layer + 2) as nat);
                    assert(0 * block_elems == 0);
                }
                for block_in_buf in 0..num_blocks_in_buf
                    invariant
                        self.well_formed(),
                        tab == self.table(),
                        num_ntts > 0,
                        m == num_ntts,
                        outer_log <= layer,
                        layer + 3 <= end_layer <= log_d <= tab.len() <= 63,
                        sub_idx < pow2(outer_log as nat),
                        num_blocks_in_buf == pow2((layer - outer_log) as nat),
                        block_size == pow2((log_d - layer) as nat),
                        block_elems == block_size * num_ntts,
                        eighth == pow2((log_d - layer - 3) as nat),
                        block_size == 8 * eighth,
                        prev.len() == len,
                        len == num_ntts * pow2((log_d - outer_log) as nat),
                        len <= usize::MAX,
                        target == sub_layers(tab, prev, m, log_d as nat, outer_log as nat, sub_idx as int, layer as nat, (layer + 3) as nat),
                        swept_to(buf@, prev, target, block_in_buf * block_elems),
                        forall|b: usize| b < num_blocks_in_buf ==> #[trigger] global.requires((b,)),
                        forall|b: usize, r: usize|
                            #[trigger] global.ensures((b,), r) ==> r == sub_idx * num_blocks_in_buf + b && r < pow2(layer as nat),
                {
                    proof {
                        lemma_block_target(tab, prev, m, log_d as nat, outer_log as nat, sub_idx as int, layer as nat, 3, block_in_buf as int);
                        assert(block_elems == m * pow2((log_d - layer) as nat)) by (nonlinear_arith)
                            requires
                                block_elems == block_size * num_ntts,
                                block_size == pow2((log_d - layer) as nat),
                                m == num_ntts,
                        ;
                    }
                    let t = self.twiddles_radix8(layer, global(block_in_buf));
                    let start = block_in_buf * block_elems;
                    let ghost before = buf@;
                    proof {
                        let s2 = sub_idx * pow2((layer - outer_log) as nat) + block_in_buf;
                        lemma_sub3(tab, prev.subrange(start as int, start + block_elems), m, log_d as nat, layer as nat, s2, t@);
                        assert(before.subrange(start as int, start + block_elems) =~= prev.subrange(start as int, start + block_elems));
                        assert(block_elems == 8 * (eighth * num_ntts)) by (nonlinear_arith)
                            requires
                                block_elems == block_size * num_ntts,
                                block_size == 8 * eighth,
                        ;
                    }
                    butterfly_interleaved_fused_3layer(&mut buf[start..start + block_elems], &t, eighth, num_ntts);
                    proof {
                        lemma_block_swept(before, buf@, prev, target, start as int, block_elems as int);
                        assert((block_in_buf + 1) * block_elems == start + block_elems) by (nonlinear_arith)
                            requires
                                start == block_in_buf * block_elems,
                        ;
                    }
                }
                layer += 3;
            } else if layer + 1 < end_layer && block_size >= 4 {
                // Two layers to go: one radix-4 sweep.
                let quarter = block_size >> 2;
                proof {
                    lemma_usize_shr_is_div(block_size, 2);
                    lemma_pow2_unfold((log_d - layer) as nat);
                    lemma_pow2_unfold((log_d - layer - 1) as nat);
                    lemma2_to64();
                    lemma_div_multiples_vanish(pow2((log_d - layer - 2) as nat) as int, 4);
                    assert(quarter == pow2((log_d - layer - 2) as nat));
                    lemma_table_rows(self, (layer + 1) as nat);
                    assert(0 * block_elems == 0);
                }
                for block_in_buf in 0..num_blocks_in_buf
                    invariant
                        self.well_formed(),
                        tab == self.table(),
                        num_ntts > 0,
                        m == num_ntts,
                        outer_log <= layer,
                        layer + 2 <= end_layer <= log_d <= tab.len() <= 63,
                        sub_idx < pow2(outer_log as nat),
                        num_blocks_in_buf == pow2((layer - outer_log) as nat),
                        block_size == pow2((log_d - layer) as nat),
                        block_elems == block_size * num_ntts,
                        quarter == pow2((log_d - layer - 2) as nat),
                        block_size == 4 * quarter,
                        prev.len() == len,
                        len == num_ntts * pow2((log_d - outer_log) as nat),
                        len <= usize::MAX,
                        target == sub_layers(tab, prev, m, log_d as nat, outer_log as nat, sub_idx as int, layer as nat, (layer + 2) as nat),
                        swept_to(buf@, prev, target, block_in_buf * block_elems),
                        forall|b: usize| b < num_blocks_in_buf ==> #[trigger] global.requires((b,)),
                        forall|b: usize, r: usize|
                            #[trigger] global.ensures((b,), r) ==> r == sub_idx * num_blocks_in_buf + b && r < pow2(layer as nat),
                {
                    proof {
                        lemma_block_target(tab, prev, m, log_d as nat, outer_log as nat, sub_idx as int, layer as nat, 2, block_in_buf as int);
                        assert(block_elems == m * pow2((log_d - layer) as nat)) by (nonlinear_arith)
                            requires
                                block_elems == block_size * num_ntts,
                                block_size == pow2((log_d - layer) as nat),
                                m == num_ntts,
                        ;
                    }
                    let global_block = global(block_in_buf);
                    proof {
                        lemma_pow2_unfold((layer + 1) as nat);
                        lemma_usize_pow2_no_overflow((layer + 1) as nat);
                    }
                    let t_outer = self.twiddle(layer, global_block);
                    let t_inner_a = self.twiddle(layer + 1, 2 * global_block);
                    let t_inner_b = self.twiddle(layer + 1, 2 * global_block + 1);
                    let start = block_in_buf * block_elems;
                    let ghost before = buf@;
                    proof {
                        let s2 = sub_idx * pow2((layer - outer_log) as nat) + block_in_buf;
                        lemma_sub2(tab, prev.subrange(start as int, start + block_elems), m, log_d as nat, layer as nat, s2, t_outer.0, t_inner_a.0, t_inner_b.0);
                        assert(before.subrange(start as int, start + block_elems) =~= prev.subrange(start as int, start + block_elems));
                        assert(block_elems == 4 * (quarter * num_ntts)) by (nonlinear_arith)
                            requires
                                block_elems == block_size * num_ntts,
                                block_size == 4 * quarter,
                        ;
                    }
                    butterfly_interleaved_fused_2layer(
                        &mut buf[start..start + block_elems],
                        t_outer,
                        t_inner_a,
                        t_inner_b,
                        quarter,
                        num_ntts,
                    );
                    proof {
                        lemma_block_swept(before, buf@, prev, target, start as int, block_elems as int);
                        assert((block_in_buf + 1) * block_elems == start + block_elems) by (nonlinear_arith)
                            requires
                                start == block_in_buf * block_elems,
                        ;
                    }
                }
                layer += 2;
            } else {
                // One layer: a plain butterfly sweep.
                let block_size_half = block_size >> 1;
                proof {
                    lemma_usize_shr_is_div(block_size, 1);
                    lemma_pow2_unfold((log_d - layer) as nat);
                    lemma2_to64();
                    lemma_div_multiples_vanish(pow2((log_d - layer - 1) as nat) as int, 2);
                    assert(block_size_half == pow2((log_d - layer - 1) as nat));
                    lemma_pow2_pos((log_d - layer - 1) as nat);
                    assert(0 * block_elems == 0);
                }
                for block_in_buf in 0..num_blocks_in_buf
                    invariant
                        self.well_formed(),
                        tab == self.table(),
                        num_ntts > 0,
                        m == num_ntts,
                        outer_log <= layer,
                        layer + 1 <= end_layer <= log_d <= tab.len() <= 63,
                        sub_idx < pow2(outer_log as nat),
                        num_blocks_in_buf == pow2((layer - outer_log) as nat),
                        block_size == pow2((log_d - layer) as nat),
                        block_elems == block_size * num_ntts,
                        block_size_half == pow2((log_d - layer - 1) as nat),
                        block_size == 2 * block_size_half,
                        block_size_half > 0,
                        prev.len() == len,
                        len == num_ntts * pow2((log_d - outer_log) as nat),
                        len <= usize::MAX,
                        target == sub_layers(tab, prev, m, log_d as nat, outer_log as nat, sub_idx as int, layer as nat, (layer + 1) as nat),
                        swept_to(buf@, prev, target, block_in_buf * block_elems),
                        forall|b: usize| b < num_blocks_in_buf ==> #[trigger] global.requires((b,)),
                        forall|b: usize, r: usize|
                            #[trigger] global.ensures((b,), r) ==> r == sub_idx * num_blocks_in_buf + b && r < pow2(layer as nat),
                {
                    proof {
                        lemma_block_target(tab, prev, m, log_d as nat, outer_log as nat, sub_idx as int, layer as nat, 1, block_in_buf as int);
                        assert(block_elems == m * pow2((log_d - layer) as nat)) by (nonlinear_arith)
                            requires
                                block_elems == block_size * num_ntts,
                                block_size == pow2((log_d - layer) as nat),
                                m == num_ntts,
                        ;
                    }
                    let twiddle = self.twiddle(layer, global(block_in_buf));
                    let start = block_in_buf * block_elems;
                    let ghost before = buf@;
                    proof {
                        let s2 = sub_idx * pow2((layer - outer_log) as nat) + block_in_buf;
                        lemma_sub1(tab, prev.subrange(start as int, start + block_elems), m, log_d as nat, layer as nat, s2, twiddle.0);
                        assert(before.subrange(start as int, start + block_elems) =~= prev.subrange(start as int, start + block_elems));
                        assert(block_elems == 2 * (block_size_half * num_ntts)) by (nonlinear_arith)
                            requires
                                block_elems == block_size * num_ntts,
                                block_size == 2 * block_size_half,
                        ;
                    }
                    butterfly_interleaved_block(&mut buf[start..start + block_elems], twiddle, block_size_half, num_ntts);
                    proof {
                        lemma_block_swept(before, buf@, prev, target, start as int, block_elems as int);
                        assert((block_in_buf + 1) * block_elems == start + block_elems) by (nonlinear_arith)
                            requires
                                start == block_in_buf * block_elems,
                        ;
                    }
                }
                layer += 1;
            }
            proof {
                assert(num_blocks_in_buf * block_elems == len) by (nonlinear_arith)
                    requires
                        num_blocks_in_buf == pow2((layer - tw_layers - outer_log) as nat),
                        block_elems == pow2((log_d - (layer - tw_layers)) as nat) * num_ntts,
                        len == num_ntts * (pow2((layer - tw_layers - outer_log) as nat) * pow2((log_d - (layer - tw_layers)) as nat)),
                ;
                assert(buf@ =~= target);
                lemma_sub_layers_split(tab, b0, m, log_d as nat, outer_log as nat, sub_idx as int, first_layer as nat, (layer - tw_layers) as nat, layer as nat);
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------
// The gathered pass
// ---------------------------------------------------------------------------------------------
/// Word `k` is in the gather of the rows `base_row + r + i * step`, `i < cnt`.
pub open spec fn in_gather(k: int, m: nat, base_row: int, r: int, step: int, cnt: nat) -> bool {
    &&& 0 <= k
    &&& base_row <= k / (m as int) < base_row + cnt * step
    &&& (k / (m as int) - base_row) % step == r
}

/// Row `i` of a gather: its word offset, and the gather words it holds.
proof fn lemma_gather_row(m: nat, base_row: int, r: int, step: int, cnt: nat, i: int)
    requires
        m > 0,
        base_row >= 0,
        0 <= r < step,
        0 <= i < cnt,
    ensures
        (base_row + r + i * step) * m >= 0,
        (base_row + r + i * step) * m + m <= (base_row + cnt * step) * m,
        forall|lane: int| 0 <= lane < m ==> #[trigger] gidx(m, base_row, r, step, i * m + lane) == (base_row + r + i * step) * m + lane,
{
    let mi = m as int;
    assert(base_row + r + i * step >= 0) by (nonlinear_arith)
        requires
            base_row >= 0,
            r >= 0,
            i >= 0,
            step > 0,
    ;
    assert(base_row + r + i * step + 1 <= base_row + cnt * step) by (nonlinear_arith)
        requires
            i + 1 <= cnt,
            0 <= r < step,
    ;
    assert((base_row + r + i * step) * mi >= 0) by (nonlinear_arith)
        requires
            base_row + r + i * step >= 0,
            mi > 0,
    ;
    assert((base_row + r + i * step) * mi + mi <= (base_row + cnt * step) * mi) by (nonlinear_arith)
        requires
            base_row + r + i * step + 1 <= base_row + cnt * step,
            mi > 0,
    ;
    assert forall|lane: int| 0 <= lane < m implies #[trigger] gidx(m, base_row, r, step, i * m + lane) == (base_row + r + i * step) * m + lane by {
        lemma_word(i, lane, mi);
    }
}

/// The words of row `i` of a gather are in it.
proof fn lemma_row_in_gather(k: int, m: nat, base_row: int, r: int, step: int, cnt: nat, i: int)
    requires
        m > 0,
        base_row >= 0,
        0 <= r < step,
        0 <= i < cnt,
        (base_row + r + i * step) * m <= k < (base_row + r + i * step) * m + m,
    ensures
        in_gather(k, m, base_row, r, step, cnt),
{
    let mi = m as int;
    lemma_gather_row(m, base_row, r, step, cnt, i);
    lemma_word(base_row + r + i * step, k - (base_row + r + i * step) * mi, mi);
    assert(base_row + r + i * step + 1 <= base_row + cnt * step) by (nonlinear_arith)
        requires
            i + 1 <= cnt,
            0 <= r < step,
    ;
    assert(i * step >= 0) by (nonlinear_arith)
        requires
            i >= 0,
            step > 0,
    ;
    lemma_fundamental_div_mod_converse(r + i * step, step, i, r);
}

/// Every word of a gather is word `q` of row `q / m`.
proof fn lemma_in_gather_index(k: int, m: nat, base_row: int, r: int, step: int, cnt: nat)
    requires
        m > 0,
        base_row >= 0,
        0 <= r < step,
        in_gather(k, m, base_row, r, step, cnt),
    ensures
        ({
            let q = ((k / (m as int) - base_row) / step) * m + k % (m as int);
            &&& 0 <= q < cnt * m
            &&& gidx(m, base_row, r, step, q) == k
        }),
{
    let mi = m as int;
    let row = k / mi;
    let i = (row - base_row) / step;
    let lane = k % mi;
    lemma_split_word(k, mi);
    lemma_fundamental_div_mod(row - base_row, step);
    lemma_div_pos_is_pos(row - base_row, step);
    assert(row - base_row == i * step + r) by {
        lemma_mul_is_commutative(step, i);
    }
    assert(i < cnt) by (nonlinear_arith)
        requires
            row - base_row == i * step + r,
            r >= 0,
            row < base_row + cnt * step,
            step > 0,
    ;
    lemma_gather_row(m, base_row, r, step, cnt, i);
    lemma_word(i, lane, mi);
    assert(i * mi + lane < cnt * mi) by (nonlinear_arith)
        requires
            i + 1 <= cnt,
            lane < mi,
            mi > 0,
    ;
    assert(i * mi + lane >= 0) by (nonlinear_arith)
        requires
            i >= 0,
            lane >= 0,
            mi > 0,
    ;
}

/// Lend this thread's scratch buffer, grown to the requested length.
///
/// - It is cache-line aligned, so a full-width load never splits a line.
/// - It lives as long as the thread, so no pass allocates in its hot loop.
///
/// Trusted (`external_body`): Verus has no model of `thread_local!` and `RefCell`. Specification: `f`
/// runs once, on a slice of exactly `len` words. Rewritten: `f` also takes a `state` argument, which
/// `with_scratch` hands it untouched; Verus does not support closures that capture a mutable
/// reference, which the deep pass's closure does (its task's slice).
#[verifier::external_body]
fn with_scratch<S, R, F: FnOnce(&mut [F64], S) -> R>(len: usize, state: S, f: F) -> (r: R)
    requires
        forall|s: &mut [F64]| s@.len() == len ==> #[trigger] f.requires((s, state)),
    ensures
        exists|s: &mut [F64]| s@.len() == len && #[trigger] f.ensures((s, state), r),
{
    // One cache line of words.
    #[derive(Clone, Copy)]
    #[repr(C, align(64))]
    struct Line([F64; 8]);
    thread_local! {
        static SCRATCH: std::cell::RefCell<Vec<Line>> = const { std::cell::RefCell::new(Vec::new()) };
    }
    SCRATCH.with_borrow_mut(|lines| {
        // Grow only; a later, smaller request reuses the same lines.
        if lines.len() * 8 < len {
            lines.resize(len.div_ceil(8), Line([F64(0); 8]));
        }
        // SAFETY:
        // - A line is exactly eight contiguous words, with no padding.
        // - The buffer holds at least the requested words, all initialized.
        f(unsafe { std::slice::from_raw_parts_mut(lines.as_mut_ptr().cast::<F64>(), len) }, state)
    })
}

/// What a group reads: the gathered input `src`, from the codeword (no message) or from the message
/// (`in_place`: block 0 of the codeword; otherwise its own buffer).
pub open spec fn group_src(
    own: Map<int, PointsTo<F64>>,
    mperms: Map<int, PointsTo<F64>>,
    base: *mut F64,
    msg: Option<SendPtr<F64>>,
    in_place: bool,
    m: nat,
    block_row: int,
    r: int,
    step: int,
    rows: nat,
    src: Seq<F64>,
) -> bool {
    &&& src.len() == rows * m
    &&& base@.addr + (block_row + rows * step) * m * size_of::<F64>() <= usize::MAX
    &&& match msg {
        None => forall|q: int|
            0 <= q < rows * m ==> #[trigger] own[gidx(m, block_row, r, step, q)].value() == src[q],
        Some(mp) => if in_place {
            &&& mp.0 == base
            &&& forall|q: int|
                0 <= q < rows * m ==> own.dom().contains(#[trigger] gidx(m, 0, r, step, q)) && own[gidx(m, 0, r, step, q)].ptr() == ptr_at(
                    base,
                    gidx(m, 0, r, step, q),
                ) && own[gidx(m, 0, r, step, q)].is_init() && own[gidx(m, 0, r, step, q)].value() == src[q]
        } else {
            &&& covers(mperms, mp.0, 0, rows * step * m)
            &&& forall|q: int| 0 <= q < rows * m ==> #[trigger] mperms[gidx(m, 0, r, step, q)].value() == src[q]
        },
    }
}

/// The words of row `i` of a gather, all held by a map that holds the whole gather.
proof fn lemma_row_keys_in(own: Map<int, PointsTo<F64>>, m: nat, base_row: int, r: int, step: int, cnt: nat, i: int)
    requires
        m > 0,
        base_row >= 0,
        0 <= r < step,
        0 <= i < cnt,
        forall|q: int| 0 <= q < cnt * m ==> own.dom().contains(#[trigger] gidx(m, base_row, r, step, q)),
    ensures
        Set::range((base_row + r + i * step) * m, (base_row + r + i * step) * m + m) <= own.dom(),
{
    let mi = m as int;
    lemma_gather_row(m, base_row, r, step, cnt, i);
    assert forall|k: int| Set::range((base_row + r + i * step) * m, (base_row + r + i * step) * m + m).contains(k) implies own.dom().contains(k) by {
        let lane = k - (base_row + r + i * step) * mi;
        assert(gidx(m, base_row, r, step, i * m + lane) == k);
        assert(i * mi + lane < cnt * mi) by (nonlinear_arith)
            requires
                i + 1 <= cnt,
                0 <= lane < mi,
        ;
        assert(i * mi + lane >= 0) by (nonlinear_arith)
            requires
                i >= 0,
                lane >= 0,
                mi > 0,
        ;
    }
}

/// `a` holds the permissions of `b`, with the same values.
pub open spec fn same_vals(a: Map<int, PointsTo<F64>>, b: Map<int, PointsTo<F64>>) -> bool {
    &&& a.dom() == b.dom()
    &&& forall|k: int|
        #[trigger] b.dom().contains(k) ==> a[k].ptr() == b[k].ptr() && a[k].is_init() && a[k].value() == b[k].value()
}

impl AdditiveNttF64 {
    /// One row group of a gathered pass: gather, transform, scatter.
    ///
    /// This is production's `group` closure inside `gathered_pass`, as a function: Verus does not support
    /// closures that capture mutable state (the scratch buffer). Its body is the closure's, with
    /// `chunks_exact(_mut)(num_ntts).enumerate()` as index loops and the permissions of each row taken
    /// out for its slice and put back (ghost). Streaming stores are not modeled: `Stream::copy` copies
    /// `src` over `dst` as `copy_from_slice` does (`primitives::stream`), so both arms are
    /// `copy_from_slice` here.
    #[allow(clippy::too_many_arguments)]
    fn group(
        &self,
        scratch: &mut [F64],
        base: SendPtr<F64>,
        msg: Option<SendPtr<F64>>,
        log_d: usize,
        num_ntts: usize,
        layer: usize,
        g: usize,
        log_step: usize,
        block: usize,
        r: usize,
        Tracked(own): Tracked<&mut Map<int, PointsTo<F64>>>,
        Tracked(mperms): Tracked<&Map<int, PointsTo<F64>>>,
        Ghost(in_place): Ghost<bool>,
        Ghost(src): Ghost<Seq<F64>>,
    )
        requires
            self.well_formed(),
            num_ntts > 0,
            0 < g,
            layer + g <= log_d <= self.table().len(),
            log_step == log_d - layer - g,
            block < pow2(layer as nat),
            r < pow2(log_step as nat),
            old(scratch)@.len() == pow2(g as nat) * num_ntts,
            num_ntts * pow2(log_d as nat) <= usize::MAX,
            base.0@.addr + num_ntts * pow2(log_d as nat) * size_of::<F64>() <= usize::MAX,
            forall|q: int|
                0 <= q < pow2(g as nat) * num_ntts ==> old(own).dom().contains(
                    #[trigger] gidx(num_ntts as nat, block * pow2((log_d - layer) as nat), r as int, pow2(log_step as nat) as int, q),
                ),
            forall|k: int| #[trigger] old(own).dom().contains(k) ==> old(own)[k].ptr() == ptr_at(base.0, k) && old(own)[k].is_init(),
            group_src(
                *old(own),
                *mperms,
                base.0,
                msg,
                in_place,
                num_ntts as nat,
                block * pow2((log_d - layer) as nat),
                r as int,
                pow2(log_step as nat) as int,
                pow2(g as nat),
                src,
            ),
        ensures
            final(own).dom() == old(own).dom(),
            forall|k: int| #[trigger] old(own).dom().contains(k) ==> final(own)[k].ptr() == old(own)[k].ptr() && final(own)[k].is_init(),
            forall|q: int|
                0 <= q < pow2(g as nat) * num_ntts ==> #[trigger] final(own)[gidx(
                    num_ntts as nat,
                    block * pow2((log_d - layer) as nat),
                    r as int,
                    pow2(log_step as nat) as int,
                    q,
                )].value() == sub_layers(
                    self.table(),
                    src,
                    num_ntts as nat,
                    (layer + g) as nat,
                    layer as nat,
                    block as int,
                    layer as nat,
                    (layer + g) as nat,
                )[q],
            forall|k: int|
                #[trigger] old(own).dom().contains(k) && !in_gather(
                    k,
                    num_ntts as nat,
                    block * pow2((log_d - layer) as nat),
                    r as int,
                    pow2(log_step as nat) as int,
                    pow2(g as nat),
                ) ==> final(own)[k] == old(own)[k],
    {
        let ghost m = num_ntts as nat;
        let ghost stp = pow2(log_step as nat) as int;
        let ghost rws = pow2(g as nat);
        let ghost bs = pow2((log_d - layer) as nat) as int;
        let ghost brow = block * bs;
        let ghost own0 = *own;
        proof {
            lemma_pow2_adds(g as nat, log_step as nat);
            assert(g as nat + log_step as nat == (log_d - layer) as nat);
            lemma_pow2_adds(layer as nat, (log_d - layer) as nat);
            assert(layer as nat + (log_d - layer) as nat == log_d as nat);
            lemma_pow2_pos(log_step as nat);
            lemma_pow2_pos(g as nat);
            lemma_usize_pow2_no_overflow(log_step as nat);
            lemma_usize_pow2_no_overflow((log_d - layer) as nat);
            lemma_usize_shl_is_mul(1, log_step);
            assert(brow + bs <= pow2(log_d as nat)) by (nonlinear_arith)
                requires
                    block + 1 <= pow2(layer as nat),
                    brow == block * bs,
                    pow2(log_d as nat) == pow2(layer as nat) * bs,
            ;
            assert(brow >= 0) by (nonlinear_arith)
                requires
                    brow == block * bs,
                    block >= 0,
                    bs > 0,
            ;
            assert((brow + bs) * m <= num_ntts * pow2(log_d as nat)) by (nonlinear_arith)
                requires
                    brow + bs <= pow2(log_d as nat),
                    m == num_ntts,
            ;
            assert(bs == rws * stp);
            assert(pow2(log_d as nat) <= num_ntts * pow2(log_d as nat)) by (nonlinear_arith)
                requires
                    num_ntts > 0,
            ;
            lemma_usize_shl_is_mul(block, (log_d - layer) as usize);
            assert(brow * m <= (brow + bs) * m) by (nonlinear_arith)
                requires
                    bs > 0,
            ;
            assert(rws * m <= (brow + bs) * m) by (nonlinear_arith)
                requires
                    bs == rws * stp,
                    stp >= 1,
                    rws > 0,
                    brow >= 0,
            ;
        }
        // Row `i` of the group, as a word offset inside its block.
        let row = |i: usize| -> (o: usize)
            requires
                i < rws,
                r < stp,
                stp == 1usize << log_step,
                (r + i * stp) * m <= usize::MAX,
                log_step < 64,
                num_ntts > 0,
                m == num_ntts,
            ensures
                o == (r + i * stp) * m,
            {
                proof {
                    assert(i * stp >= 0) by (nonlinear_arith)
                        requires
                            stp > 0,
                    ;
                    assert(r + i * stp <= (r + i * stp) * m) by (nonlinear_arith)
                        requires
                            m >= 1,
                            r >= 0,
                            i * stp >= 0,
                    ;
                    lemma_usize_shl_is_mul(i, log_step);
                }
                (r + (i << log_step)) * num_ntts
            };
        let block_off = (block << (log_d - layer)) * num_ntts;
        proof {
            assert(0 * m == 0);
            assert forall|i: usize| i < rws implies #[trigger] row.requires((i,)) by {
                lemma_gather_row(m, 0, r as int, stp, rws, i as int);
                assert((r + i * stp) * m + m <= bs * m) by (nonlinear_arith)
                    requires
                        (0 + r + i * stp) * m + m <= (0 + rws * stp) * m,
                        bs == rws * stp,
                ;
                assert(bs * m <= (brow + bs) * m) by (nonlinear_arith)
                    requires
                        brow >= 0,
                        m > 0,
                ;
            }
        }
        // Gather: the scattered rows become one contiguous 2^g-row buffer.
        //
        // Rewritten from `for (i, dst) in scratch.chunks_exact_mut(num_ntts).enumerate()`.
        let rows = 1usize << g;
        proof {
            lemma_usize_pow2_no_overflow(g as nat);
            lemma_usize_shl_is_mul(1, g);
        }
        for i in 0..rows
            invariant
                // ...
                rows == rws,
                m == num_ntts,
                num_ntts > 0,
                stp > 0,
                0 <= r < stp,
                bs == rws * stp,
                brow == block * bs,
                brow >= 0,
                block_off == brow * m,
                (brow + bs) * m <= num_ntts * pow2(log_d as nat),
                num_ntts * pow2(log_d as nat) <= usize::MAX,
                base.0@.addr + num_ntts * pow2(log_d as nat) * size_of::<F64>() <= usize::MAX,
                scratch@.len() == rws * m,
                rws * m <= usize::MAX,
                same_vals(*own, own0),
                forall|k: int| #[trigger] own0.dom().contains(k) && !in_gather(k, m, brow, r as int, stp, rws) ==> own[k] == own0[k],
                forall|q: int| 0 <= q < rws * num_ntts ==> own0.dom().contains(#[trigger] gidx(m, brow, r as int, stp, q)),
                forall|k: int| #[trigger] own0.dom().contains(k) ==> own0[k].ptr() == ptr_at(base.0, k) && own0[k].is_init(),
                group_src(own0, *mperms, base.0, msg, in_place, m, brow, r as int, stp, rws, src),
                forall|q: int| 0 <= q < i * m ==> #[trigger] scratch@[q] == src[q],
                forall|i: usize| i < rws ==> #[trigger] row.requires((i,)),
                forall|i: usize, o: usize| #[trigger] row.ensures((i,), o) ==> o == (r + i * stp) * m,
        {
            proof {
                lemma_gather_row(m, brow, r as int, stp, rws, i as int);
                lemma_gather_row(m, 0, r as int, stp, rws, i as int);
                assert((i + 1) * m <= rws * m) by (nonlinear_arith)
                    requires
                        i + 1 <= rws,
                ;
                assert((i + 1) * m == i * m + m) by (nonlinear_arith);
                assert((r + i * stp) * m + m <= bs * m) by (nonlinear_arith)
                    requires
                        (0 + r + i * stp) * m + m <= (0 + rws * stp) * m,
                        bs == rws * stp,
                ;
                assert(bs * m <= (brow + bs) * m) by (nonlinear_arith)
                    requires
                        brow >= 0,
                        m > 0,
                ;
                assert(block_off + (r + i * stp) * m == (brow + r + i * stp) * m) by (nonlinear_arith)
                    requires
                        block_off == brow * m,
                ;
            }
            let dst = &mut scratch[i * num_ntts..(i + 1) * num_ntts];
            let ghost lo = (brow + r + i * stp) * m;
            proof {
                lemma_mul_le(lo + m, num_ntts * pow2(log_d as nat), size_of::<F64>() as int);
                lemma_row_keys_in(own0, m, brow, r as int, stp, rws, i as int);
            }
            let ghost lo0 = (r + i * stp) * m;
            let ghost cur = *own;
            proof {
                lemma_gather_row(m, 0, r as int, stp, rws, i as int);
                lemma_mul_le(lo0 + m, num_ntts * pow2(log_d as nat), size_of::<F64>() as int);
                lemma_mul_le(lo0, num_ntts * pow2(log_d as nat), size_of::<F64>() as int);
                assert(lo0 + m <= bs * m) by (nonlinear_arith)
                    requires
                        (0 + r + i * stp) * m + m <= (0 + rws * stp) * m,
                        lo0 == (r + i * stp) * m,
                        bs == rws * stp,
                ;
                if let Some(mp) = msg {
                    assert forall|k: int| lo0 <= k < lo0 + m implies {
                        if in_place {
                            &&& #[trigger] own.dom().contains(k)
                            &&& own[k].ptr() == ptr_at(mp.0, k)
                            &&& own[k].is_init()
                            &&& own[k].value() == src[i * m + (k - lo0)]
                        } else {
                            mperms[k].value() == src[i * m + (k - lo0)]
                        }
                    } by {
                        let lane = k - lo0;
                        assert(gidx(m, 0, r as int, stp, i * m + lane) == k);
                        assert(i * m + lane < rws * m) by (nonlinear_arith)
                            requires
                                i + 1 <= rws,
                                0 <= lane < m,
                        ;
                        assert(i * m + lane >= 0) by (nonlinear_arith)
                            requires
                                lane >= 0,
                        ;
                        if in_place {
                            assert(own0.dom().contains(k));
                        }
                    }
                    assert(lo0 >= 0) by (nonlinear_arith)
                        requires r >= 0, i >= 0, stp > 0, m > 0, lo0 == (r + i * stp) * m;
                    if !in_place {
                        lemma_mul_le(lo0 + m, rws * stp * m, size_of::<F64>() as int);
                        lemma_mul_le(lo0, rws * stp * m, size_of::<F64>() as int);
                        assert(covers(*mperms, mp.0, lo0, m as int));
                    } else {
                        assert(mp.0 == base.0);
                        assert forall|k: int| lo0 <= k < lo0 + m implies
                            #[trigger] own.dom().contains(k) && own[k].ptr() == ptr_at(mp.0, k) && own[k].is_init() by {
                            let lane = k - lo0;
                            let q = i * m + lane;
                            lemma_word(i as int, lane, m as int);
                            assert(0 <= q < rws * m) by (nonlinear_arith)
                                requires q == i * m + lane, 0 <= lane < m, 0 <= i < rws, m > 0;
                            assert(gidx(m, 0, r as int, stp, q) == k);
                            assert(own0.dom().contains(gidx(m, 0, r as int, stp, q)));
                        }
                        assert(m as int >= 0);
                        lemma_mul_le(lo0 + m, num_ntts * pow2(log_d as nat), size_of::<F64>() as int);
                        assert(mp.0@.addr + (lo0 + m) * size_of::<F64>() <= usize::MAX);
                        assert(covers(*own, mp.0, lo0, m as int));
                    }
                }
            }
            let tracked mut rowp = Map::<int, PointsTo<F64>>::tracked_empty();
            proof {
                if msg is None {
                    rowp = take_row(own, base.0, lo, m);
                }
            }
            // SAFETY:
            // - The message and the codeword both cover every row addressed here.
            // - Tasks own disjoint residues, so no other task writes these rows.
            // - Block 0 is written last, after every read of the message in it.
            let src_row = unsafe {
                match msg {
                    Some(mp) => parallel::from_raw_parts(
                        mp.add(row(i)),
                        num_ntts,
                        Ghost(mp.0),
                        Ghost(lo0),
                        Tracked(
                            if in_place {
                                &*own
                            } else {
                                mperms
                            },
                        ),
                    ),
                    None => base.slice(block_off + row(i), num_ntts, Tracked(&mut rowp)),
                }
            };
            dst.copy_from_slice(src_row);
            proof {
                if msg is None {
                    let rp = rowp;
                    own.tracked_union_prefer_right(rowp);
                    assert(own.dom() =~= own0.dom());
                    assert forall|k: int| #[trigger] own0.dom().contains(k) implies own[k].ptr() == own0[k].ptr() && own[k].is_init()
                        && own[k].value() == own0[k].value() by {
                        if lo <= k < lo + m {
                            assert(own[k] == rp[k]);
                            assert(vals(rp, lo, m as int)[k - lo] == rp[k].value());
                        }
                    }
                }
                assert(same_vals(*own, own0));
                assert forall|k: int| #[trigger] own0.dom().contains(k) && !in_gather(k, m, brow, r as int, stp, rws) implies own[k] == own0[k] by {
                    if lo <= k < lo + m {
                        lemma_row_in_gather(k, m, brow, r as int, stp, rws, i as int);
                    }
                }
                assert forall|q: int| 0 <= q < (i + 1) * m implies #[trigger] scratch@[q] == src[q] by {
                    if q >= i * m {
                        lemma_word(i as int, q - i * m, m as int);
                        assert(gidx(m, brow, r as int, stp, i * m + (q - i * m)) == lo + (q - i * m));
                        assert(gidx(m, 0, r as int, stp, i * m + (q - i * m)) == lo0 + (q - i * m));
                    }
                }
            }
        }
        // Transform: a (layer + g)-layer domain whose sub-block index is the global block.
        proof {
            assert(scratch@ =~= src);
            lemma_pow2_adds(layer as nat, g as nat);
            assert(pow2(((layer + g) - layer) as nat) == rws);
        }
        self.run_layers(scratch, layer + g, num_ntts, layer, layer + g, layer, block);
        let ghost out = scratch@;
        proof {
            lemma_sub_layers_len(self.table(), src, m, (layer + g) as nat, layer as nat, block as int, layer as nat, (layer + g) as nat);
        }
        // Scatter: every row returns to its place.
        //
        // Rewritten from `for (i, src) in scratch.chunks_exact(num_ntts).enumerate()`; both arms of the
        // `stream` match are `copy_from_slice` (see above).
        for i in 0..rows
            invariant
                rows == rws,
                m == num_ntts,
                num_ntts > 0,
                stp > 0,
                0 <= r < stp,
                bs == rws * stp,
                brow == block * bs,
                brow >= 0,
                block_off == brow * m,
                (brow + bs) * m <= num_ntts * pow2(log_d as nat),
                num_ntts * pow2(log_d as nat) <= usize::MAX,
                base.0@.addr + num_ntts * pow2(log_d as nat) * size_of::<F64>() <= usize::MAX,
                scratch@ == out,
                out.len() == rws * m,
                rws * m <= usize::MAX,
                own.dom() == own0.dom(),
                forall|q: int| 0 <= q < rws * num_ntts ==> own0.dom().contains(#[trigger] gidx(m, brow, r as int, stp, q)),
                forall|k: int| #[trigger] own0.dom().contains(k) ==> own0[k].ptr() == ptr_at(base.0, k) && own0[k].is_init(),
                forall|k: int| #[trigger] own0.dom().contains(k) ==> own[k].ptr() == ptr_at(base.0, k) && own[k].is_init(),
                forall|q: int| 0 <= q < i * m ==> #[trigger] own[gidx(m, brow, r as int, stp, q)].value() == out[q],
                forall|k: int| #[trigger] own0.dom().contains(k) && !in_gather(k, m, brow, r as int, stp, rws) ==> own[k] == own0[k],
                forall|i: usize| i < rws ==> #[trigger] row.requires((i,)),
                forall|i: usize, o: usize| #[trigger] row.ensures((i,), o) ==> o == (r + i * stp) * m,
        {
            proof {
                lemma_gather_row(m, brow, r as int, stp, rws, i as int);
                lemma_gather_row(m, 0, r as int, stp, rws, i as int);
                assert((i + 1) * m <= rws * m) by (nonlinear_arith)
                    requires
                        i + 1 <= rws,
                ;
                assert((i + 1) * m == i * m + m) by (nonlinear_arith);
                assert((r + i * stp) * m + m <= bs * m) by (nonlinear_arith)
                    requires
                        (0 + r + i * stp) * m + m <= (0 + rws * stp) * m,
                        bs == rws * stp,
                ;
                assert(bs * m <= (brow + bs) * m) by (nonlinear_arith)
                    requires
                        brow >= 0,
                        m > 0,
                ;
                assert(block_off + (r + i * stp) * m == (brow + r + i * stp) * m) by (nonlinear_arith)
                    requires
                        block_off == brow * m,
                ;
            }
            let src_row = &scratch[i * num_ntts..(i + 1) * num_ntts];
            let ghost lo = (brow + r + i * stp) * m;
            proof {
                lemma_mul_le(lo + m, num_ntts * pow2(log_d as nat), size_of::<F64>() as int);
                lemma_row_keys_in(own0, m, brow, r as int, stp, rws, i as int);
            }
            let ghost cur = *own;
            let tracked mut rowp = take_row(own, base.0, lo, m);
            // SAFETY: this group alone owns these rows of the codeword.
            let dst = unsafe { base.slice(block_off + row(i), num_ntts, Tracked(&mut rowp)) };
            dst.copy_from_slice(src_row);
            proof {
                own.tracked_union_prefer_right(rowp);
                assert(own.dom() =~= own0.dom());
                let rp = rowp;
                assert forall|q: int| 0 <= q < (i + 1) * m implies #[trigger] own[gidx(m, brow, r as int, stp, q)].value() == out[q] by {
                    if q >= i * m {
                        let lane = q - i * m;
                        lemma_word(i as int, lane, m as int);
                        assert(gidx(m, brow, r as int, stp, i * m + lane) == lo + lane);
                        assert(own[lo + lane] == rp[lo + lane]);
                        assert(vals(rp, lo, m as int)[lane] == rp[lo + lane].value());
                        assert(out.subrange(i * m, (i + 1) * m)[lane] == out[q]);
                    } else {
                        lemma_split_word(q, m as int);
                        let iq = q / (m as int);
                        assert(iq < i) by (nonlinear_arith)
                            requires
                                q == iq * m + q % (m as int),
                                q % (m as int) >= 0,
                                q < i * m,
                                m > 0,
                        ;
                        lemma_gather_row(m, brow, r as int, stp, rws, iq);
                        lemma_word(iq, q % (m as int), m as int);
                        assert(gidx(m, brow, r as int, stp, q) < lo) by (nonlinear_arith)
                            requires
                                gidx(m, brow, r as int, stp, q) == (brow + r + iq * stp) * m + q % (m as int),
                                q % (m as int) < m,
                                lo == (brow + r + i * stp) * m,
                                iq + 1 <= i,
                                stp > 0,
                        ;
                    }
                }
                assert forall|k: int| #[trigger] own0.dom().contains(k) && !in_gather(k, m, brow, r as int, stp, rws) implies own[k] == own0[k] by {
                    if lo <= k < lo + m {
                        lemma_row_in_gather(k, m, brow, r as int, stp, rws, i as int);
                    }
                }
            }
        }
        proof {
            let s_out = sub_layers(self.table(), src, m, (layer + g) as nat, layer as nat, block as int, layer as nat, (layer + g) as nat);
            assert(out == s_out);
            assert forall|k: int|
                #[trigger] own0.dom().contains(k) && !in_gather(k, m, brow, r as int, stp, rws) implies own[k] == own0[k] by {}
            assert(rws * num_ntts == rws * m);
        }
    }
}

/// A gathered task owns one residue in one block.
pub open spec fn gather_owner(m: int, bs: int, step: int, k: int) -> int {
    (k / m / bs) * step + (k / m) % step
}

proof fn lemma_gather_partition(m: int, bs: int, step: int, rows: int, blocks: int, k: int)
    requires m > 0, step > 0, rows > 0, blocks > 0, bs == rows * step,
        0 <= k < blocks * bs * m,
    ensures
        0 <= k / m / bs < blocks,
        0 <= (k / m) % step < step,
        0 <= gather_owner(m, bs, step, k) < blocks * step,
        in_gather(k, m as nat, (k / m / bs) * bs, (k / m) % step, step, rows as nat),
{
    assert(bs > 0) by (nonlinear_arith) requires bs == rows * step, rows > 0, step > 0;
    lemma_split_word(k, m);
    let row = k / m;
    lemma_fundamental_div_mod(row, bs);
    lemma_mod_bound(row, bs);
    lemma_div_pos_is_pos(row, bs);
    lemma_mod_bound(row, step);
    assert(0 <= row < blocks * bs) by (nonlinear_arith)
        requires k == row * m + k % m, 0 <= k % m < m,
            0 <= k < blocks * bs * m, m > 0;
    assert(row / bs < blocks) by (nonlinear_arith)
        requires row == bs * (row / bs) + row % bs, 0 <= row % bs,
            row < blocks * bs, bs > 0;
    lemma_mod_multiples_basic((row / bs) * rows, step);
    assert((row / bs) * bs == ((row / bs) * rows) * step) by (nonlinear_arith)
        requires bs == rows * step;
    lemma_mod_multiples_vanish(-((row / bs) * rows), row, step);
    assert(step * -((row / bs) * rows) + row == row - (row / bs) * bs) by (nonlinear_arith)
        requires bs == rows * step;
    assert(0 <= gather_owner(m, bs, step, k) < blocks * step) by (nonlinear_arith)
        requires 0 <= row / bs < blocks, 0 <= row % step < step, step > 0,
            gather_owner(m, bs, step, k) == (row / bs) * step + row % step;
}

proof fn lemma_gather_owner(m: nat, bs: int, step: int, rows: nat, block: int, r: int, q: int)
    requires m > 0, step > 0, rows > 0, bs == rows * step,
        block >= 0, 0 <= r < step, 0 <= q < rows * m,
    ensures
        0 <= gidx(m, block * bs, r, step, q) < (block + 1) * bs * m,
        gather_owner(m as int, bs, step, gidx(m, block * bs, r, step, q)) == block * step + r,
{
    lemma_split_word(q, m as int);
    let i = q / (m as int);
    let lane = q % (m as int);
    assert(i < rows) by (nonlinear_arith)
        requires q == i * m + lane, lane >= 0, q < rows * m, m > 0;
    lemma_gather_row(m, block * bs, r, step, rows, i);
    assert(0 <= r + i * step < bs) by (nonlinear_arith)
        requires 0 <= i < rows, 0 <= r < step, bs == rows * step, step > 0;
    lemma_word(block * bs + r + i * step, lane, m as int);
    lemma_fundamental_div_mod_converse(block * bs + r + i * step, bs, block, r + i * step);
    assert(block * bs + r + i * step == (block * rows + i) * step + r) by (nonlinear_arith)
        requires bs == rows * step;
    lemma_fundamental_div_mod_converse(block * bs + r + i * step, step, block * rows + i, r);
    assert((block * bs + rows * step) * m == (block + 1) * bs * m) by (nonlinear_arith)
        requires bs == rows * step;
}

impl AdditiveNttF64 {
    /// Gather, run and scatter a band of layers after its input replicas exist.
    ///
    /// Executable refinement of production's no-message pass: `for_each` replaces
    /// the chunk loop and borrows scratch once per group rather than once per claimed
    /// range. The dispatcher still runs the real pool. Streaming stores are replaced
    /// by ordinary copies. These changes do not verify production's cache policy.
    pub fn gathered_pass(
        &self, data: &mut [F64], log_d: usize, num_ntts: usize, layer: usize, g: usize,
    )
        requires self.well_formed(), num_ntts > 0,
            0 < g, layer + g <= log_d <= self.table().len(),
            old(data)@.len() == num_ntts * pow2(log_d as nat),
            old(data)@.len() <= usize::MAX,
        ensures final(data)@ == sub_layers(self.table(), old(data)@, num_ntts as nat,
            log_d as nat, 0, 0, layer as nat, (layer + g) as nat),
    {
        let ghost x = data@;
        let ghost m = num_ntts as nat;
        let ghost target = sub_layers(self.table(), x, m, log_d as nat, 0, 0, layer as nat, (layer + g) as nat);
        let log_step = log_d - layer - g;
        proof {
            lemma_usize_pow2_no_overflow(g as nat);
            lemma_usize_pow2_no_overflow(log_step as nat);
            lemma_usize_pow2_no_overflow(layer as nat);
            lemma_usize_pow2_no_overflow((log_d - layer) as nat);
            lemma_usize_shl_is_mul(1, g);
            lemma_usize_shl_is_mul(1, log_step);
            lemma_usize_shl_is_mul(1, layer);
            lemma_usize_shl_is_mul(1, (log_d - layer) as usize);
            lemma_pow2_adds(g as nat, log_step as nat);
            lemma_pow2_adds(layer as nat, (log_d - layer) as nat);
            lemma_pow2_pos(g as nat);
            lemma_pow2_pos(log_step as nat);
            lemma_pow2_pos(layer as nat);
            lemma_sub_layers_len(self.table(), x, m, log_d as nat, 0, 0, layer as nat, (layer + g) as nat);
        }
        let rows = 1usize << g;
        let step = 1usize << log_step;
        let blocks = 1usize << layer;
        let bs = 1usize << (log_d - layer);
        proof {
            assert(bs == rows * step);
            assert(x.len() == blocks * bs * m) by (nonlinear_arith)
                requires x.len() == m * pow2(log_d as nat),
                    pow2(log_d as nat) == blocks * bs;
            assert(blocks * step <= x.len() && rows * m <= x.len()) by (nonlinear_arith)
                requires x.len() == blocks * bs * m, bs == rows * step,
                    blocks > 0, rows > 0, step > 0, m > 0;
        }
        let n_tasks = blocks * step;
        let scratch_len = rows * num_ntts;
        let (ptr, Tracked(perms)) = slice_as_mut_ptr(data);
        let base = SendPtr(ptr);
        let ghost p0 = *perms;
        let ghost owner = |k: int| gather_owner(m as int, bs as int, step as int, k);
        let ghost post = |t: int, p: Map<int, PointsTo<F64>>| group_post(p, claimed(p0, owner, t, t + 1), target);
        proof {
            assert forall|k: int| #[trigger] p0.dom().contains(k) implies 0 <= owner(k) < n_tasks by {
                lemma_gather_partition(m as int, bs as int, step as int, rows as int, blocks as int, k);
            }
        }
        let tracked all = perms.tracked_remove_keys(perms.dom());
        proof { assert(all =~= p0); }
        let Tracked(out) = parallel::for_each(n_tasks,
            |t: usize, tp: Tracked<Map<int, PointsTo<F64>>>| -> (res: Tracked<Map<int, PointsTo<F64>>>)
                requires t < n_tasks, tp@ == claimed(p0, owner, t as int, t + 1),
                ensures res@.dom() == keys_of(p0, owner, t as int, t + 1), post(t as int, res@),
            {
                let block = t / step;
                let r = t % step;
                let ghost src = gather(x, m, block * bs, r as int, step as int, rows as nat);
                let tracked mut own = tp.get();
                let ghost before = own;
                proof {
                    lemma_split_word(t as int, step as int);
                    assert(block < blocks) by (nonlinear_arith)
                        requires t == block * step + r, r >= 0, t < blocks * step, step > 0;
                    assert forall|q: int| 0 <= q < rows * m implies own.dom().contains(
                        #[trigger] gidx(m, block * bs, r as int, step as int, q)) by {
                        lemma_gather_owner(m, bs as int, step as int, rows as nat, block as int, r as int, q);
                        assert((block + 1) * bs * m <= x.len()) by (nonlinear_arith)
                            requires block + 1 <= blocks, x.len() == blocks * bs * m, bs > 0, m > 0;
                    }
                    assert((block * bs + rows * step) * m <= x.len()) by (nonlinear_arith)
                        requires block + 1 <= blocks, x.len() == blocks * bs * m,
                            bs == rows * step, bs > 0, m > 0;
                    lemma_mul_le((block * bs + rows * step) * m, x.len() as int, size_of::<F64>() as int);
                    assert forall|q: int| 0 <= q < rows * m implies
                        #[trigger] own[gidx(m, block * bs, r as int, step as int, q)].value() == src[q] by {
                        let k = gidx(m, block * bs, r as int, step as int, q);
                        assert(own.dom().contains(k));
                        assert(p0[k].value() == vals(p0, 0, x.len() as int)[k]);
                    }
                    assert(group_src(own, Map::empty(), base.0, None, false, m, block * bs,
                        r as int, step as int, rows as nat, src));
                }
                let Tracked(result) = with_scratch(scratch_len, Tracked(own),
                    |scratch: &mut [F64], tp: Tracked<Map<int, PointsTo<F64>>>| -> (res: Tracked<Map<int, PointsTo<F64>>>)
                        requires scratch@.len() == scratch_len, tp@ == before,
                        ensures res@.dom() == before.dom(), post(t as int, res@),
                    {
                        let tracked mut p = tp.get();
                        let tracked empty = Map::tracked_empty();
                        self.group(scratch, base, None, log_d, num_ntts, layer, g, log_step,
                            block, r, Tracked(&mut p), Tracked(&empty), Ghost(false), Ghost(src));
                        proof {
                            lemma_gather_sub_layers(self.table(), x, m, log_d as nat, 0, 0,
                                (layer + g) as nat, layer as nat, block as int, r as int,
                                layer as nat, (layer + g) as nat);
                            assert forall|k: int| #[trigger] before.dom().contains(k) implies
                                p[k].ptr() == before[k].ptr() && p[k].is_init() && p[k].value() == target[k] by {
                                lemma_gather_partition(m as int, bs as int, step as int, rows as int, blocks as int, k);
                                let b = k / (m as int) / (bs as int);
                                let rr = (k / (m as int)) % (step as int);
                                lemma_fundamental_div_mod_converse(t as int, step as int, b, rr);
                                assert(b == block && rr == r);
                                lemma_in_gather_index(k, m, block * bs, r as int, step as int, rows as nat);
                                let q = ((k / (m as int) - block * bs) / (step as int)) * m + k % (m as int);
                                assert(gather(target, m, block * bs, r as int, step as int, rows as nat)[q] == target[k]);
                            }
                        }
                        Tracked(p)
                    });
                proof {
                    assert(post(t as int, result));
                    assert(result.dom() =~= keys_of(p0, owner, t as int, t + 1));
                }
                Tracked(result)
            }, Tracked(all), Ghost(owner), Ghost(post));
        proof {
            perms.tracked_union_prefer_right(out);
            assert(perms.dom() =~= p0.dom());
            assert forall|k: int| 0 <= k < x.len() implies
                (#[trigger] perms[k]).ptr() == ptr_at(ptr, k) && perms[k].is_init() && perms[k].value() == target[k] by {
                lemma_gather_partition(m as int, bs as int, step as int, rows as int, blocks as int, k);
                let t = owner(k);
                let p = out.restrict(keys_of(p0, owner, t, t + 1));
                assert(post(t, p));
                let orig = claimed(p0, owner, t, t + 1);
                assert(orig.dom().contains(k));
                assert(orig[k] == p0[k]);
                assert(p0[k].ptr() == ptr_at(ptr, k));
                assert(perms[k] == out[k]);
                assert(p[k] == out[k]);
            }
            assert(owns(*perms, ptr, 0, x.len() as int));
            assert(vals(*perms, 0, x.len() as int) =~= target);
        }
    }
    /// Contiguous deep pass, one pool item per sub-block. Production batches
    /// adjacent sub-blocks; here the pool's claim coalescing is the only batching.
    pub fn deep_pass(&self, data: &mut [F64], log_d: usize, num_ntts: usize, first: usize)
        requires self.well_formed(), num_ntts > 0, first <= log_d <= self.table().len(),
            old(data)@.len() == num_ntts * pow2(log_d as nat), old(data)@.len() <= usize::MAX,
        ensures final(data)@ == sub_layers(self.table(), old(data)@, num_ntts as nat,
            log_d as nat, 0, 0, first as nat, log_d as nat),
    {
        let ghost x = data@;
        let ghost m = num_ntts as nat;
        let ghost target = sub_layers(self.table(), x, m, log_d as nat, 0, 0, first as nat, log_d as nat);
        proof {
            lemma_usize_pow2_no_overflow((log_d - first) as nat);
            lemma_usize_shl_is_mul(1, (log_d - first) as usize);
            lemma_pow2_pos((log_d - first) as nat);
            lemma_pow2_pos(first as nat);
            lemma_pow2_adds(first as nat, (log_d - first) as nat);
            lemma_sub_layers_len(self.table(), x, m, log_d as nat, 0, 0, first as nat, log_d as nat);
            assert(pow2((log_d - first) as nat) * m <= x.len()) by (nonlinear_arith)
                requires x.len() == m * (pow2(first as nat) * pow2((log_d - first) as nat)),
                    pow2(first as nat) >= 1, m > 0, pow2((log_d - first) as nat) > 0;
        }
        let chunk = (1usize << (log_d - first)) * num_ntts;
        let ghost count = pow2(first as nat) as int;
        proof {
            assert(chunk > 0) by (nonlinear_arith)
                requires chunk == pow2((log_d - first) as nat) * m,
                    pow2((log_d - first) as nat) > 0, m > 0;
            assert(x.len() == count * chunk) by (nonlinear_arith)
                requires x.len() == m * (pow2(first as nat) * pow2((log_d - first) as nat)),
                    chunk == pow2((log_d - first) as nat) * m, count == pow2(first as nat);
            lemma_div_multiples_vanish_fancy(count, chunk - 1, chunk as int);
            assert((x.len() + chunk - 1) / (chunk as int) == count);
            assert forall|i: int| 0 <= i < count implies
                #[trigger] chunk_len(x.len(), chunk as nat, i) == chunk by {
                assert((i + 1) * chunk <= x.len()) by (nonlinear_arith)
                    requires i + 1 <= count, x.len() == count * chunk, chunk > 0;
                assert(x.len() - i * chunk >= chunk) by (nonlinear_arith)
                    requires (i + 1) * chunk <= x.len();
                assert(i * chunk + chunk == (i + 1) * chunk) by (nonlinear_arith);
            }
        }
        let ghost post = |i: int, before: Seq<F64>, after: Seq<F64>|
            after == target.subrange(i * chunk, (i + 1) * chunk);
        parallel::chunks_mut(data, chunk,
            |i: usize, sub: &mut [F64]|
                requires i < count, sub@ == x.subrange(i * chunk, i * chunk + chunk_len(x.len(), chunk as nat, i as int)),
                ensures final(sub)@.len() == old(sub)@.len(), post(i as int, old(sub)@, final(sub)@),
            {
                let ghost before = sub@;
                proof {
                    assert(chunk_len(x.len(), chunk as nat, i as int) == chunk);
                    assert(i * chunk + chunk == (i + 1) * chunk) by (nonlinear_arith);
                    lemma_block_target(self.table(), x, m, log_d as nat, 0, 0, first as nat,
                        (log_d - first) as nat, i as int);
                }
                self.run_layers(sub, log_d, num_ntts, first, log_d, first, i);
                proof {
                    lemma_sub_layers_len(self.table(), before, m, log_d as nat, first as nat,
                        i as int, first as nat, log_d as nat);
                }
            }, Ghost(post));
        proof {
            assert(data@ =~= target) by {
                assert forall|k: int| 0 <= k < x.len() implies data@[k] == target[k] by {
                    lemma_split_word(k, chunk as int);
                    let i = k / (chunk as int);
                    assert(i < count) by (nonlinear_arith)
                        requires k == i * chunk + k % (chunk as int), k % (chunk as int) >= 0,
                            k < x.len(), x.len() == count * chunk, chunk > 0;
                    assert(chunk_len(x.len(), chunk as nat, i) == chunk);
                    assert(i * chunk + chunk == (i + 1) * chunk) by (nonlinear_arith);
                    assert(post(i, x.subrange(i * chunk, (i + 1) * chunk),
                        data@.subrange(i * chunk, (i + 1) * chunk)));
                    assert(data@.subrange(i * chunk, (i + 1) * chunk)[k - i * chunk] == data@[k]);
                }
            }
        }
    }

    /// Execute any valid gathered/deep plan on populated replicas. The cache
    /// planner is an explicit input. Message replication, row sinks and streaming
    /// store fences are not performed by this entry point.
    pub fn transform(&self, data: &mut [F64], log_d: usize, num_ntts: usize,
        start: usize, deep_start: usize, gathered_width: usize)
        requires self.well_formed(), num_ntts > 0, gathered_width > 0,
            start <= deep_start <= log_d <= self.table().len(),
            old(data)@.len() == num_ntts * pow2(log_d as nat), old(data)@.len() <= usize::MAX,
        ensures final(data)@ == forward_layers(self.table(), old(data)@, num_ntts as nat,
            log_d as nat, start as nat, log_d as nat),
    {
        let ghost x = data@;
        let ghost m = num_ntts as nat;
        let mut layer = start;
        while layer < deep_start
            invariant self.well_formed(), num_ntts > 0, gathered_width > 0,
                start <= layer <= deep_start <= log_d <= self.table().len(),
                x.len() == num_ntts * pow2(log_d as nat), x.len() <= usize::MAX,
                m == num_ntts,
                data@ == sub_layers(self.table(), x, m, log_d as nat, 0, 0, start as nat, layer as nat),
            decreases deep_start - layer,
        {
            proof { lemma_sub_layers_len(self.table(), x, m, log_d as nat, 0, 0, start as nat, layer as nat); }
            let g = if deep_start - layer < gathered_width { deep_start - layer } else { gathered_width };
            self.gathered_pass(data, log_d, num_ntts, layer, g);
            proof {
                lemma_sub_layers_split(self.table(), x, m, log_d as nat, 0, 0,
                    start as nat, layer as nat, (layer + g) as nat);
            }
            layer += g;
        }
        proof { lemma_sub_layers_len(self.table(), x, m, log_d as nat, 0, 0, start as nat, deep_start as nat); }
        self.deep_pass(data, log_d, num_ntts, deep_start);
        proof {
            lemma_sub_layers_split(self.table(), x, m, log_d as nat, 0, 0,
                start as nat, deep_start as nat, log_d as nat);
            lemma_forward_is_sub(self.table(), x, m, log_d as nat, start as nat, log_d as nat);
        }
    }
}

} // verus!
