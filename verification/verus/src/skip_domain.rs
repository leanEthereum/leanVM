//! The univariate skip's domain and its Lagrange interpolation.
//!
//! The executable functions are `SkipDomain` of `crates/flock/src/zerocheck/skip_domain.rs`, which is generic over
//! the `Arith` trait of `crates/fiat_shamir/src/arith.rs`, instantiated here at its native arithmetic `Native`
//! (whose trait methods, the defaults included, are copied as inherent methods); `tests/equivalence/skip_domain.rs`
//! checks the two agree. Where Verus rejects the production form (iterator chains, `fold`, `.rev()`, `vec![x]`,
//! the generic parameter, `assert!` on an argument), the copy spells out the same arithmetic; each such spot says
//! what it replaces.
//!
//! Specification: the domain of `l = 2^k` nodes is `S = {s_0, .., s_(l-1)}`, `s_i = φ₈(i)` ([`node`]), an
//! `F_2`-subspace of `K`. Its vanishing polynomial is `V_l(z) = prod_i (z + s_i)` ([`vanishing_spec`]) and its
//! Lagrange basis the textbook one,
//!
//! ```text
//!     L_i(z) = prod_{k != i} (z + s_k) / prod_{k != i} (s_i + s_k)        ([`lagrange_basis`])
//! ```
//!
//! with `L_i(s_j) = [i = j]` ([`lemma_lagrange_basis_at_nodes`]). The theorems: `vanishing` is `V_l`;
//! `lagrange_at` is `sum_i values_i L_i(z)` and `first_round_at` is `sum_i values_i L_(l+i)(z)` over the window
//! of `2l` nodes, for every `z` off the nodes. At a node `s_j` production returns 0 rather than `values_j` (the
//! formula divides by `z + s_j` with `1 / 0 = 0`), so the theorems exclude the nodes.
use crate::gf2_64::*;
use crate::gf2_64x3::*;
use crate::multilinear::*;
use crate::phi8_tower::*;
use vstd::arithmetic::power2::*;
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------------------------
/// `prod_{k < n} f(k)`, from the first factor up.
pub open spec fn e_prod_fn(f: spec_fn(int) -> F192, n: nat) -> F192
    decreases n,
{
    if n == 0 {
        F192::ONE
    } else {
        e_mul(e_prod_fn(f, (n - 1) as nat), f(n - 1))
    }
}

/// Node `k` of the domain, `φ₈(k)`.
pub open spec fn node(k: int) -> F192 {
    phi8_e(k as u8)
}

/// `V_l(z) = prod_{k < l} (z + s_k)`, the vanishing polynomial of the first `l` nodes.
pub open spec fn vanishing_spec(l: nat, z: F192) -> F192 {
    e_prod_fn(|k: int| e_add(z, node(k)), l)
}

/// `f` with its factor at `i` replaced by one: a product of it skips `i`.
pub open spec fn except(f: spec_fn(int) -> F192, i: int) -> spec_fn(int) -> F192 {
    |k: int| if k == i {
        F192::ONE
    } else {
        f(k)
    }
}

/// The inverse in `E`, `a^(2^192 - 2)` (zero at zero), what `F192::inv` returns.
pub open spec fn e_inv(a: F192) -> F192 {
    e_pow(a, (pow2(192) - 2) as nat)
}

/// The Lagrange basis polynomial of node `i` among the first `l`, at `z`.
pub open spec fn lagrange_basis(l: nat, i: int, z: F192) -> F192 {
    e_mul(
        e_prod_fn(except(|k: int| e_add(z, node(k)), i), l),
        e_inv(e_prod_fn(except(|k: int| e_add(node(i), node(k)), i), l)),
    )
}

/// `sum_i values_i L_i(z)` over the first `l` nodes.
pub open spec fn lagrange_sum(l: nat, values: Seq<F192>, z: F192) -> F192 {
    e_sum_fn(|i: int| e_mul(values[i], lagrange_basis(l, i, z)), values.len())
}

/// `sum_i values_i L_(l+i)(z)` over the window of the first `2l` nodes: the interpolant of `values` on the coset
/// `Λ = {s_l, .., s_(2l-1)}` and of zero on `S`.
pub open spec fn window_sum(l: nat, values: Seq<F192>, z: F192) -> F192 {
    e_sum_fn(|i: int| e_mul(values[i], lagrange_basis(2 * l, l + i, z)), values.len())
}

/// `sum_{j < n} c_j x^(2^j)`, a linearized polynomial at `x`.
pub open spec fn lin_upto(c: Seq<F192>, x: F192, n: nat) -> F192 {
    e_sum_fn(|j: int| e_mul(c[j], e_sq_iter(x, j as nat)), n)
}

pub open spec fn lin(c: Seq<F192>, x: F192) -> F192 {
    lin_upto(c, x, c.len())
}

/// `z` is none of the first `l` nodes.
pub open spec fn off_nodes(l: nat, z: F192) -> bool {
    forall|k: int| 0 <= k < l ==> z != #[trigger] node(k)
}

pub open spec fn sq(a: F192) -> F192 {
    e_mul(a, a)
}

// ---------------------------------------------------------------------------------------------
// Algebra
// ---------------------------------------------------------------------------------------------
proof fn lemma_xor4(a: u64, b: u64, c: u64, d: u64)
    ensures
        (a ^ b) ^ (b ^ d) == a ^ d,
        (a ^ c) ^ (b ^ d) == (a ^ b) ^ (c ^ d),
{
    assert((a ^ b) ^ (b ^ d) == a ^ d && (a ^ c) ^ (b ^ d) == (a ^ b) ^ (c ^ d)) by (bit_vector);
}

proof fn lemma_e_add4(a: F192, b: F192, c: F192, d: F192)
    ensures
        e_add(e_add(a, b), e_add(b, d)) == e_add(a, d),
        e_add(e_add(a, c), e_add(b, d)) == e_add(e_add(a, b), e_add(c, d)),
{
    lemma_xor4(a.c0, b.c0, c.c0, d.c0);
    lemma_xor4(a.c1, b.c1, c.c1, d.c1);
    lemma_xor4(a.c2, b.c2, c.c2, d.c2);
}

/// `z + s = 0` only when `z = s`.
proof fn lemma_e_add_zero(z: F192, s: F192)
    ensures
        e_add(z, s) == F192::ZERO <==> z == s,
{
    let (a, b, c, d, e, f) = (z.c0, s.c0, z.c1, s.c1, z.c2, s.c2);
    assert((a ^ b == 0 && c ^ d == 0 && e ^ f == 0) <==> (a == b && c == d && e == f)) by (bit_vector);
}

/// Squaring is additive: `(a + b)^2 = a^2 + b^2`.
pub proof fn lemma_sq_add(a: F192, b: F192)
    ensures
        sq(e_add(a, b)) == e_add(sq(a), sq(b)),
{
    let s = e_add(a, b);
    lemma_e_mul_distrib(s, a, b);
    lemma_e_mul_distrib(a, a, b);
    lemma_e_mul_distrib(b, a, b);
    lemma_e_mul_comm(a, s);
    lemma_e_mul_comm(b, s);
    lemma_e_mul_comm(a, b);
    lemma_e_add4(sq(a), e_mul(a, b), e_mul(b, a), sq(b));
}

/// Squaring is multiplicative: `(ab)^2 = a^2 b^2`.
pub proof fn lemma_sq_mul(a: F192, b: F192)
    ensures
        sq(e_mul(a, b)) == e_mul(sq(a), sq(b)),
{
    let ab = e_mul(a, b);
    lemma_e_mul_assoc(a, b, ab);
    lemma_e_mul_assoc(b, a, b);
    lemma_e_mul_comm(b, a);
    lemma_e_mul_assoc(a, b, b);
    lemma_e_mul_assoc(a, a, sq(b));
}

pub proof fn lemma_sq_iter_add(a: F192, b: F192, n: nat)
    ensures
        e_sq_iter(e_add(a, b), n) == e_add(e_sq_iter(a, n), e_sq_iter(b, n)),
    decreases n,
{
    if n > 0 {
        lemma_sq_iter_add(a, b, (n - 1) as nat);
        lemma_sq_add(e_sq_iter(a, (n - 1) as nat), e_sq_iter(b, (n - 1) as nat));
    }
}

pub proof fn lemma_sq_zero_one()
    ensures
        sq(F192::ZERO) == F192::ZERO,
        sq(F192::ONE) == F192::ONE,
{
    lemma_e_mul_zero(F192::ZERO);
    lemma_e_mul_one(F192::ONE);
}

/// `sum_i (g1(i) + g2(i)) = sum_i g1(i) + sum_i g2(i)`.
pub proof fn lemma_sum_add(g1: spec_fn(int) -> F192, g2: spec_fn(int) -> F192, n: nat)
    ensures
        e_sum_fn(|i: int| e_add(g1(i), g2(i)), n) == e_add(e_sum_fn(g1, n), e_sum_fn(g2, n)),
    decreases n,
{
    if n == 0 {
        lemma_e_add(F192::ZERO, F192::ZERO, F192::ZERO);
    } else {
        lemma_sum_add(g1, g2, (n - 1) as nat);
        lemma_e_add4(e_sum_fn(g1, (n - 1) as nat), e_sum_fn(g2, (n - 1) as nat), g1(n - 1), g2(n - 1));
    }
}

/// The square of a sum is the sum of the squares.
pub proof fn lemma_sq_sum(g: spec_fn(int) -> F192, n: nat)
    ensures
        sq(e_sum_fn(g, n)) == e_sum_fn(|i: int| sq(g(i)), n),
    decreases n,
{
    if n == 0 {
        lemma_sq_zero_one();
    } else {
        lemma_sq_sum(g, (n - 1) as nat);
        lemma_sq_add(e_sum_fn(g, (n - 1) as nat), g(n - 1));
    }
}

// ---------------------------------------------------------------------------------------------
// Products
// ---------------------------------------------------------------------------------------------
pub proof fn lemma_prod_ext(f: spec_fn(int) -> F192, g: spec_fn(int) -> F192, n: nat)
    requires
        forall|i: int| 0 <= i < n ==> #[trigger] f(i) == g(i),
    ensures
        e_prod_fn(f, n) == e_prod_fn(g, n),
    decreases n,
{
    if n > 0 {
        lemma_prod_ext(f, g, (n - 1) as nat);
    }
}

/// A product split after `m` factors.
pub proof fn lemma_prod_split(f: spec_fn(int) -> F192, m: nat, k: nat)
    ensures
        e_prod_fn(f, m + k) == e_mul(e_prod_fn(f, m), e_prod_fn(shifted(f, m as int), k)),
    decreases k,
{
    if k == 0 {
        lemma_e_mul_one(e_prod_fn(f, m));
    } else {
        lemma_prod_split(f, m, (k - 1) as nat);
        assert(shifted(f, m as int)(k - 1) == f(m + k - 1));
        lemma_e_mul_assoc(e_prod_fn(f, m), e_prod_fn(shifted(f, m as int), (k - 1) as nat), f(m + k - 1));
    }
}

/// One factor out of a product: `prod_k f(k) = f(i) prod_{k != i} f(k)`.
pub proof fn lemma_prod_remove(f: spec_fn(int) -> F192, l: nat, i: int)
    requires
        0 <= i < l,
    ensures
        e_prod_fn(f, l) == e_mul(f(i), e_prod_fn(except(f, i), l)),
    decreases l,
{
    let g = except(f, i);
    if i == l - 1 {
        lemma_prod_ext(f, g, (l - 1) as nat);
        lemma_e_mul_one(e_prod_fn(g, (l - 1) as nat));
        lemma_e_mul_comm(e_prod_fn(f, (l - 1) as nat), f(i));
    } else {
        lemma_prod_remove(f, (l - 1) as nat, i);
        let (a, p, b) = (f(i), e_prod_fn(g, (l - 1) as nat), f(l - 1));
        lemma_e_mul_assoc(a, p, b);
    }
}

/// `k -> i ^ k`, a permutation of every aligned power-of-two range containing `i`.
pub open spec fn xor_perm(g: spec_fn(int) -> F192, i: int) -> spec_fn(int) -> F192 {
    |k: int| g(((i as usize) ^ (k as usize)) as int)
}

proof fn lemma_xor_halves(i: usize, k: usize, s: usize)
    requires
        s < 8,
        k < (1usize << s),
    ensures
        i < (1usize << s) ==> (i ^ k) < (1usize << s) && (i ^ ((1usize << s) + k) as usize) == (1usize << s) + (i ^ k),
        (1usize << s) <= i < 2 * (1usize << s) ==> (i ^ k) == (1usize << s) + ((i - (1usize << s)) as usize ^ k) && (i
            ^ ((1usize << s) + k) as usize) == ((i - (1usize << s)) as usize ^ k),
{
    assert(i < (1usize << s) ==> (i ^ k) < (1usize << s) && (i ^ ((1usize << s) + k) as usize) == (1usize << s) + (i
        ^ k)) by (bit_vector)
        requires
            s < 8,
            k < (1usize << s),
    ;
    assert((1usize << s) <= i < 2 * (1usize << s) ==> (i ^ k) == (1usize << s) + ((i - (1usize << s)) as usize ^ k)
        && (i ^ ((1usize << s) + k) as usize) == ((i - (1usize << s)) as usize ^ k)) by (bit_vector)
        requires
            s < 8,
            k < (1usize << s),
    ;
}

/// The product over an aligned power-of-two range is invariant under `k -> i ^ k`.
pub proof fn lemma_prod_xor(g: spec_fn(int) -> F192, j: nat, i: int)
    requires
        j <= 8,
        0 <= i < pow2(j),
    ensures
        e_prod_fn(xor_perm(g, i), pow2(j)) == e_prod_fn(g, pow2(j)),
    decreases j,
{
    lemma_pow2_shl_small(j);
    lemma2_to64();
    if j == 0 {
        let iu = i as usize;
        assert(iu == 0);
        assert(iu ^ 0usize == 0usize) by (bit_vector)
            requires
                iu == 0,
        ;
        assert(xor_perm(g, i)(0) == g(0));
        assert(e_prod_fn(xor_perm(g, i), 0) == F192::ONE);
        assert(e_prod_fn(g, 0) == F192::ONE);
        assert(e_prod_fn(xor_perm(g, i), 1) == e_mul(F192::ONE, xor_perm(g, i)(0)));
        assert(e_prod_fn(g, 1) == e_mul(F192::ONE, g(0)));
    } else {
        let s = (j - 1) as usize;
        lemma_pow2_shl_small(s as nat);
        lemma_pow2_unfold(j);
        let m = pow2(s as nat);
        let p = xor_perm(g, i);
        lemma_prod_split(p, m, m);
        lemma_prod_split(g, m, m);
        let gh = shifted(g, m as int);
        if i < m {
            lemma_prod_xor(g, s as nat, i);
            lemma_prod_xor(gh, s as nat, i);
            assert forall|k: int| 0 <= k < m implies #[trigger] shifted(p, m as int)(k) == xor_perm(gh, i)(k) by {
                lemma_xor_halves(i as usize, k as usize, s);
            }
            lemma_prod_ext(shifted(p, m as int), xor_perm(gh, i), m);
            assert forall|k: int| 0 <= k < m implies #[trigger] p(k) == xor_perm(g, i)(k) by {}
        } else {
            let i2 = i - m;
            lemma_prod_xor(g, s as nat, i2);
            lemma_prod_xor(gh, s as nat, i2);
            assert forall|k: int| 0 <= k < m implies #[trigger] p(k) == xor_perm(gh, i2)(k) by {
                lemma_xor_halves(i as usize, k as usize, s);
            }
            assert forall|k: int| 0 <= k < m implies #[trigger] shifted(p, m as int)(k) == xor_perm(g, i2)(k) by {
                lemma_xor_halves(i as usize, k as usize, s);
            }
            lemma_prod_ext(p, xor_perm(gh, i2), m);
            lemma_prod_ext(shifted(p, m as int), xor_perm(g, i2), m);
            lemma_e_mul_comm(e_prod_fn(gh, m), e_prod_fn(g, m));
        }
    }
}

proof fn lemma_pow2_shl_small(j: nat)
    requires
        j <= 8,
    ensures
        pow2(j) == (1usize << (j as usize)),
        pow2(j) <= 256,
        pow2(j) >= 1,
{
    lemma2_to64();
    let u = j as usize;
    assert(u <= 8 ==> (1usize << u) == (if u == 0 { 1usize } else if u == 1 { 2 } else if u == 2 { 4 } else if u == 3 { 8 } else if u == 4 { 16 } else if u == 5 { 32 } else if u == 6 { 64 } else if u == 7 { 128 } else { 256 })) by (bit_vector);
}

/// Sums of nodes: `s_i + s_k = s_(i ^ k)`.
pub proof fn lemma_node_add(i: int, k: int)
    requires
        0 <= i < 256,
        0 <= k < 256,
    ensures
        e_add(node(i), node(k)) == node(((i as usize) ^ (k as usize)) as int),
{
    let (iu, ku) = (i as usize, k as usize);
    assert(iu < 256 && ku < 256 ==> (iu ^ ku) < 256 && ((iu ^ ku) as u8) == (iu as u8) ^ (ku as u8)) by (bit_vector);
    lemma_phi8_xor(i as u8, k as u8);
    assert(0u64 ^ 0u64 == 0u64) by (bit_vector);
}

/// The product of the nonzero nodes of the first `n` is `prod_{k=1}^{n-1} φ₈(k)` in `K`.
proof fn lemma_prod_nonzero_nodes(n: nat)
    requires
        1 <= n <= 256,
    ensures
        e_prod_fn(except(|k: int| node(k), 0), n) == e_from_k(phi8_prod(n)),
    decreases n,
{
    let h = except(|k: int| node(k), 0);
    if n == 1 {
        lemma_e_mul_one(F192::ONE);
        assert(e_prod_fn(h, 0) == F192::ONE);
        assert(h(0) == F192::ONE);
        assert(e_prod_fn(h, 1) == e_mul(e_prod_fn(h, 0), h(0)));
        assert(phi8_prod(1) == 1);
        assert(e_from_k(1) == F192::ONE);
    } else {
        lemma_prod_nonzero_nodes((n - 1) as nat);
        lemma_e_from_k_mul(phi8_prod((n - 1) as nat), phi8((n - 1) as u8));
        assert(h(n - 1) == e_from_k(phi8((n - 1) as u8)));
        assert(e_prod_fn(h, n) == e_mul(e_prod_fn(h, (n - 1) as nat), h(n - 1)));
        assert(phi8_prod(n) == k_mul(phi8_prod((n - 1) as nat), phi8((n - 1) as u8)));
    }
}

/// `prod_{k != i} (s_i + s_k)` is the same for every node of a window: the product of its nonzero nodes.
pub proof fn lemma_node_differences(log: nat, i: int)
    requires
        log <= 8,
        0 <= i < pow2(log),
    ensures
        e_prod_fn(except(|k: int| e_add(node(i), node(k)), i), pow2(log)) == e_from_k(phi8_prod(pow2(log))),
{
    lemma_pow2_shl_small(log);
    let l = pow2(log);
    let h = except(|k: int| node(k), 0);
    let f = except(|k: int| e_add(node(i), node(k)), i);
    assert forall|k: int| 0 <= k < l implies #[trigger] f(k) == xor_perm(h, i)(k) by {
        lemma_node_add(i, k);
        let (iu, ku) = (i as usize, k as usize);
        assert((iu ^ ku) == 0 <==> iu == ku) by (bit_vector);
        assert(iu < 256 && ku < 256 ==> (iu ^ ku) < 256) by (bit_vector);
    }
    lemma_prod_ext(f, xor_perm(h, i), l);
    lemma_prod_xor(h, log, i);
    lemma_prod_nonzero_nodes(l);
}

/// `1 / prod_{k != i} (s_i + s_k)` is the window's weight `D`.
pub proof fn lemma_weight_inverts(log: nat, i: int)
    requires
        log <= 8,
        0 <= i < pow2(log),
    ensures
        e_inv(e_prod_fn(except(|k: int| e_add(node(i), node(k)), i), pow2(log))) == denominator_spec(log),
        e_prod_fn(except(|k: int| e_add(node(i), node(k)), i), pow2(log)) != F192::ZERO,
{
    lemma_node_differences(log, i);
    lemma_denominator_inverts(log);
    let q = e_from_k(phi8_prod(pow2(log)));
    let d = denominator_spec(log);
    assert(q != F192::ZERO);
    lemma_e_inverse(q);
    let w = e_inv(q);
    lemma_e_mul_assoc(d, q, w);
    lemma_e_mul_one(d);
    lemma_e_mul_one(w);
}

/// The basis is the Lagrange basis: `L_i(s_j) = 1` if `i = j`, else 0.
pub proof fn lemma_lagrange_basis_at_nodes(log: nat, i: int, j: int)
    requires
        log <= 8,
        0 <= i < pow2(log),
        0 <= j < pow2(log),
    ensures
        lagrange_basis(pow2(log), i, node(j)) == (if i == j {
            F192::ONE
        } else {
            F192::ZERO
        }),
{
    let l = pow2(log);
    lemma_weight_inverts(log, i);
    let q = e_prod_fn(except(|k: int| e_add(node(i), node(k)), i), l);
    let f = |k: int| e_add(node(j), node(k));
    if i == j {
        lemma_prod_ext(except(f, i), except(|k: int| e_add(node(i), node(k)), i), l);
        lemma_e_inverse(q);
    } else {
        lemma_prod_remove(except(f, i), l, j);
        lemma_e_add(node(j), node(j), node(j));
        lemma_e_mul_zero(e_prod_fn(except(except(f, i), j), l));
        lemma_e_mul_zero(e_inv(q));
    }
}

/// The vanishing polynomial of `2m` nodes from that of `m`: `V_2m(x) = V_m(x) V_m(x + s_m)`.
pub proof fn lemma_vanishing_double(j: nat, x: F192)
    requires
        j < 8,
    ensures
        vanishing_spec(2 * pow2(j), x) == e_mul(vanishing_spec(pow2(j), x), vanishing_spec(pow2(j), e_add(x, node(pow2(j) as int)))),
{
    lemma_pow2_shl_small(j);
    lemma2_to64();
    lemma_pow2_strictly_increases(j, 8);
    let m = pow2(j);
    let f = |k: int| e_add(x, node(k));
    let a = node(m as int);
    lemma_prod_split(f, m, m);
    assert forall|k: int| 0 <= k < m implies #[trigger] shifted(f, m as int)(k) == e_add(e_add(x, a), node(k)) by {
        let (mu, ku, ju) = (m as usize, k as usize, j as usize);
        assert(mu == (1usize << ju) && ju < 8 && ku < mu ==> (mu ^ ku) == mu + ku) by (bit_vector);
        lemma_node_add(m as int, k);
        lemma_e_add(x, a, node(k));
    }
    lemma_prod_ext(shifted(f, m as int), |k: int| e_add(e_add(x, a), node(k)), m);
}

// ---------------------------------------------------------------------------------------------
// Linearized polynomials
// ---------------------------------------------------------------------------------------------
/// A linearized polynomial is additive.
pub proof fn lemma_lin_add(c: Seq<F192>, x: F192, y: F192, n: nat)
    ensures
        lin_upto(c, e_add(x, y), n) == e_add(lin_upto(c, x, n), lin_upto(c, y, n)),
    decreases n,
{
    if n == 0 {
        lemma_e_add(F192::ZERO, F192::ZERO, F192::ZERO);
    } else {
        let j = n - 1;
        lemma_lin_add(c, x, y, (n - 1) as nat);
        lemma_sq_iter_add(x, y, j as nat);
        lemma_e_mul_distrib(c[j], e_sq_iter(x, j as nat), e_sq_iter(y, j as nat));
        lemma_e_add4(
            lin_upto(c, x, (n - 1) as nat),
            lin_upto(c, y, (n - 1) as nat),
            e_mul(c[j], e_sq_iter(x, j as nat)),
            e_mul(c[j], e_sq_iter(y, j as nat)),
        );
    }
}

/// The step the coefficients take when a basis element joins the subspace: with `c'_k = c_(k-1)^2 + va c_k` (and
/// the top coefficient zero), `lin(c') = lin(c)^2 + va lin(c)`.
pub proof fn lemma_lin_step(c: Seq<F192>, va: F192, x: F192)
    requires
        c.len() >= 1,
        c.last() == F192::ZERO,
    ensures
        lin(Seq::new(c.len(), |k: int| e_add(if k == 0 { F192::ZERO } else { sq(c[k - 1]) }, e_mul(va, c[k]))), x) == e_add(
            sq(lin(c, x)),
            e_mul(va, lin(c, x)),
        ),
{
    let n = c.len();
    let cn = Seq::new(n, |k: int| e_add(if k == 0 { F192::ZERO } else { sq(c[k - 1]) }, e_mul(va, c[k])));
    let xs = |k: int| e_sq_iter(x, k as nat);
    let ta = |k: int| e_mul(if k == 0 { F192::ZERO } else { sq(c[k - 1]) }, xs(k));
    let tb = |k: int| e_mul(e_mul(va, c[k]), xs(k));
    let tc = |k: int| e_mul(c[k], xs(k));
    // lin(c') = sum ta + sum tb.
    assert forall|k: int| 0 <= k < n implies #[trigger] e_mul(cn[k], e_sq_iter(x, k as nat)) == e_add(ta(k), tb(k)) by {
        lemma_e_mul_distrib(xs(k), if k == 0 { F192::ZERO } else { sq(c[k - 1]) }, e_mul(va, c[k]));
        lemma_e_mul_comm(xs(k), if k == 0 { F192::ZERO } else { sq(c[k - 1]) });
        lemma_e_mul_comm(xs(k), e_mul(va, c[k]));
        lemma_e_mul_comm(xs(k), cn[k]);
    }
    lemma_sum_ext(|j: int| e_mul(cn[j], e_sq_iter(x, j as nat)), |k: int| e_add(ta(k), tb(k)), n);
    lemma_sum_add(ta, tb, n);
    // sum tb = va lin(c).
    assert forall|k: int| 0 <= k < n implies #[trigger] tb(k) == e_mul(va, tc(k)) by {
        lemma_e_mul_assoc(va, c[k], xs(k));
    }
    lemma_sum_ext(tb, |k: int| e_mul(va, tc(k)), n);
    lemma_sum_scale(va, tc, n);
    lemma_sum_ext(tc, |j: int| e_mul(c[j], e_sq_iter(x, j as nat)), n);
    // sum ta = sum_{j < n - 1} c_j^2 x^(2^(j+1)).
    let td = |j: int| e_mul(sq(c[j]), e_sq_iter(x, (j + 1) as nat));
    lemma_sum_split(ta, 1, (n - 1) as nat);
    lemma_e_mul_zero(xs(0));
    lemma_e_add(F192::ZERO, F192::ZERO, F192::ZERO);
    assert(e_sum_fn(ta, 0) == F192::ZERO);
    assert(ta(0) == F192::ZERO);
    assert(e_sum_fn(ta, 1) == F192::ZERO);
    assert forall|j: int| 0 <= j < n - 1 implies #[trigger] shifted(ta, 1)(j) == td(j) by {
        assert((j + 1) as nat == (1 + j) as nat);
    }
    lemma_sum_ext(shifted(ta, 1), td, (n - 1) as nat);
    lemma_e_add(F192::ZERO, e_sum_fn(td, (n - 1) as nat), F192::ZERO);
    // lin(c)^2 = sum_{j < n} c_j^2 x^(2^(j+1)), whose last term is zero.
    lemma_sq_sum(tc, n);
    assert forall|j: int| 0 <= j < n implies #[trigger] sq(tc(j)) == td(j) by {
        lemma_sq_mul(c[j], xs(j));
    }
    lemma_sum_ext(|j: int| sq(tc(j)), td, n);
    lemma_sq_zero_one();
    lemma_e_mul_zero(e_sq_iter(x, n as nat));
    lemma_e_add(e_sum_fn(td, (n - 1) as nat), F192::ZERO, F192::ZERO);
}

/// A linearized polynomial with coefficients `1, 0, .., 0` is the identity.
proof fn lemma_lin_first(c: Seq<F192>, x: F192, n: nat)
    requires
        1 <= n <= c.len(),
        c[0] == F192::ONE,
        forall|k: int| 1 <= k < c.len() ==> #[trigger] c[k] == F192::ZERO,
    ensures
        lin_upto(c, x, n) == x,
    decreases n,
{
    if n == 1 {
        lemma_e_mul_one(x);
        lemma_e_add(x, F192::ZERO, F192::ZERO);
        assert(lin_upto(c, x, 0) == F192::ZERO);
    } else {
        lemma_lin_first(c, x, (n - 1) as nat);
        lemma_e_mul_zero(e_sq_iter(x, (n - 1) as nat));
        lemma_e_add(x, F192::ZERO, F192::ZERO);
    }
}

// ---------------------------------------------------------------------------------------------
// Executable code
// ---------------------------------------------------------------------------------------------
/// The domain's size exponent in flock (`crates/flock/src/zerocheck.rs`).
pub const K_SKIP: usize = 6;

/// Plain `F192` arithmetic, for the prover's share of code the verifiers also run.
///
/// The `Arith` implementation of `fiat_shamir::arith::Native`: its methods, with the trait's default methods it
/// inherits (`zero`, `mul`, `square`, `mul_const`, `add_const`), as inherent methods.
#[derive(Clone, Copy, Debug, Default)]
pub struct Native;

impl Native {
    /// The constant `c`.
    pub fn constant(&mut self, c: F192) -> (r: F192)
        ensures
            r == c,
    {
        c
    }

    /// `a·b + d`.
    pub fn mul_add(&mut self, a: F192, b: F192, d: F192) -> (r: F192)
        ensures
            r == e_add(e_mul(a, b), d),
    {
        a * b + d
    }

    /// `a + d`.
    pub fn add(&mut self, a: F192, d: F192) -> (r: F192)
        ensures
            r == e_add(a, d),
    {
        a + d
    }

    /// `a·c + d` for a constant `c`.
    pub fn mul_const_add(&mut self, a: F192, c: F192, d: F192) -> (r: F192)
        ensures
            r == e_add(e_mul(a, c), d),
    {
        a * c + d
    }

    /// `1 / a`, zero for zero.
    pub fn inv(&mut self, a: F192) -> (r: F192)
        ensures
            r == e_inv(a),
    {
        proof {
            lemma_e_inverse(a);
        }
        if a.is_zero() { F192::ZERO } else { a.inv() }
    }

    /// The constant zero.
    pub fn zero(&mut self) -> (r: F192)
        ensures
            r == F192::ZERO,
    {
        self.constant(F192::ZERO)
    }

    /// `a·b`.
    pub fn mul(&mut self, a: F192, b: F192) -> (r: F192)
        ensures
            r == e_mul(a, b),
    {
        let zero = self.zero();
        proof {
            lemma_e_add(e_mul(a, b), F192::ZERO, F192::ZERO);
        }
        self.mul_add(a, b, zero)
    }

    /// `a^2`.
    pub fn square(&mut self, a: F192) -> (r: F192)
        ensures
            r == e_mul(a, a),
    {
        self.mul(a, a)
    }

    /// `a·c` for a constant `c`.
    pub fn mul_const(&mut self, a: F192, c: F192) -> (r: F192)
        ensures
            r == e_mul(a, c),
    {
        let zero = self.zero();
        proof {
            lemma_e_add(e_mul(a, c), F192::ZERO, F192::ZERO);
        }
        self.mul_const_add(a, c, zero)
    }

    /// `a + c` for a constant `c`.
    pub fn add_const(&mut self, a: F192, c: F192) -> (r: F192)
        ensures
            r == e_add(a, c),
    {
        let c = self.constant(c);
        self.add(a, c)
    }
}

/// The skip domain `S`, the first `2^k_skip` nodes of the phi_8 table: an `F_2`-subspace of `K`, since phi_8 is linear on its index.
///
/// Its coset `Lambda = S + phi_8(2^k_skip)` holds the zerocheck's first message.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SkipDomain {
    k_skip: usize,
}

impl SkipDomain {
    /// `k_skip`.
    pub closed spec fn spec_k_skip(self) -> nat {
        self.k_skip as nat
    }

    /// The domain the zerocheck skips and the lincheck interpolates over.
    ///
    /// Verus's `exec const` form (the field is private).
    pub exec const FLOCK: Self
        ensures
            Self::FLOCK.spec_k_skip() == K_SKIP,
    {
        Self { k_skip: K_SKIP }
    }

    /// The domain of `2^k_skip` nodes.
    ///
    /// Production asserts `k_skip < 8` (the window fits the phi_8 table); here a `requires`.
    pub const fn new(k_skip: usize) -> (d: Self)
        requires
            k_skip < 8,
        ensures
            d.spec_k_skip() == k_skip,
    {
        Self { k_skip }
    }

    /// The base-two logarithm of its size.
    pub const fn k_skip(self) -> (k: usize)
        ensures
            k == self.spec_k_skip(),
    {
        self.k_skip
    }

    /// Its size, and the zerocheck's first message's.
    pub const fn size(self) -> (s: usize)
        requires
            self.spec_k_skip() < 8,
        ensures
            s == pow2(self.spec_k_skip()),
    {
        proof {
            lemma_pow2_shl_small(self.k_skip as nat);
        }
        1 << self.k_skip
    }

    /// The coefficients `c_j` of `V_S(X) = prod_{s in S} (X + s) = sum_j c_j X^(2^j)`, lowest first.
    ///
    /// Adding a basis element `a` to a subspace takes `V` to `V(X)^2 + V(a) V(X)`, since `V(X + a) = V(X) + V(a)`.
    ///
    /// `for k in (0..=j + 1).rev()` is a `while` counting down.
    fn vanishing_coefficients(self) -> (c: Vec<F192>)
        requires
            self.spec_k_skip() < 8,
        ensures
            c.len() == self.spec_k_skip() + 1,
            c@[self.spec_k_skip() as int] == F192::ONE,
            forall|x: F192| #[trigger] lin(c@, x) == vanishing_spec(pow2(self.spec_k_skip()), x),
    {
        let ghost n = self.k_skip + 1;
        let mut c = vec![F192::ZERO; self.k_skip + 1];
        c[0] = F192::ONE;
        proof {
            lemma2_to64();
            lemma_phi8_zero_one();
            assert forall|t: int| 1 <= t < c.len() implies #[trigger] c@[t] == F192::ZERO by {}
            assert forall|x: F192| #[trigger] lin(c@, x) == vanishing_spec(pow2(0), x) by {
                lemma_lin_first(c@, x, n as nat);
                lemma_e_add(x, F192::ZERO, F192::ZERO);
                lemma_e_mul_one(x);
                assert(node(0) == F192::ZERO);
                let f = |k: int| e_add(x, node(k));
                assert(e_prod_fn(f, 0) == F192::ONE);
                assert(e_prod_fn(f, 1) == e_mul(F192::ONE, f(0)));
            }
        }
        for j in 0..self.k_skip
            invariant
                n == self.k_skip + 1,
                self.k_skip < 8,
                c.len() == n,
                c@[j as int] == F192::ONE,
                forall|k: int| j < k < n ==> #[trigger] c@[k] == F192::ZERO,
                forall|x: F192| #[trigger] lin(c@, x) == vanishing_spec(pow2(j as nat), x),
        {
            proof {
                lemma_pow2_shl_small(j as nat);
                lemma2_to64();
                lemma_pow2_strictly_increases(j as nat, 8);
            }
            let a = PHI_8_TABLE_192[1 << j];
            let at_a = Self::linearized(&c, a);
            let ghost prev = c@;
            let ghost cn = Seq::new(n as nat, |k: int| e_add(if k == 0 { F192::ZERO } else { sq(prev[k - 1]) }, e_mul(at_a, prev[k])));
            let mut k = j + 2;
            while k > 0
                invariant
                    n == self.k_skip + 1,
                    j < self.k_skip,
                    c.len() == n,
                    k <= j + 2,
                    forall|t: int| k <= t <= j + 1 ==> #[trigger] c@[t] == cn[t],
                    prev.len() == n,
                    cn.len() == n,
                    forall|t: int| 0 <= t < n ==> #[trigger] cn[t] == e_add(if t == 0 { F192::ZERO } else { sq(prev[t - 1]) }, e_mul(at_a, prev[t])),
                    forall|t: int| 0 <= t < k ==> #[trigger] c@[t] == prev[t],
                    forall|t: int| j + 1 < t < n ==> #[trigger] c@[t] == prev[t],
                decreases k,
            {
                k -= 1;
                let squared = if k == 0 { F192::ZERO } else { c[k - 1].square() };
                c[k] = squared + at_a * c[k];
            }
            proof {
                lemma_sq_zero_one();
                lemma_e_mul_zero(at_a);
                lemma_e_add(F192::ZERO, F192::ZERO, F192::ZERO);
                lemma_e_add(F192::ONE, F192::ZERO, F192::ZERO);
                assert forall|t: int| j + 1 < t < n implies #[trigger] cn[t] == F192::ZERO by {}
                assert(c@ =~= cn);
                assert(cn[j + 1] == F192::ONE);
                lemma_pow2_unfold((j + 1) as nat);
                assert forall|x: F192| #[trigger] lin(c@, x) == vanishing_spec(pow2((j + 1) as nat), x) by {
                    lemma_lin_step(prev, at_a, x);
                    lemma_lin_add(prev, x, a, n as nat);
                    lemma_vanishing_double(j as nat, x);
                    let (v, va) = (lin(prev, x), lin(prev, a));
                    assert(v == vanishing_spec(pow2(j as nat), x));
                    assert(va == vanishing_spec(pow2(j as nat), a));
                    assert(lin(prev, e_add(x, a)) == vanishing_spec(pow2(j as nat), e_add(x, a)));
                    lemma_e_mul_distrib(v, v, va);
                    lemma_e_mul_comm(v, va);
                }
            }
        }
        c
    }

    /// A linearized polynomial `sum_j c_j x^(2^j)` at `x`.
    ///
    /// `for &cj in c` is a loop over the indices.
    fn linearized(c: &[F192], x: F192) -> (r: F192)
        ensures
            r == lin(c@, x),
    {
        let (mut power, mut acc) = (x, F192::ZERO);
        for j in 0..c.len()
            invariant
                power == e_sq_iter(x, j as nat),
                acc == lin_upto(c@, x, j as nat),
        {
            acc += c[j] * power;
            power = power.square();
        }
        acc
    }

    /// `V_S(z)`: `k_skip` squarings and as many products by constants of `K`.
    ///
    /// The generic `A: Arith` is `Native`. `vec![z]` is a push, and the fold over `c[..k_skip]` zipped with the
    /// powers is a loop; the `debug_assert_eq!` that `V` is monic is proven (`vanishing_coefficients`).
    pub fn vanishing(self, a: &mut Native, z: F192) -> (v: F192)
        requires
            self.spec_k_skip() < 8,
        ensures
            v == vanishing_spec(pow2(self.spec_k_skip()), z),
    {
        let c = self.vanishing_coefficients();
        let mut powers: Vec<F192> = Vec::new();
        powers.push(z);
        for j in 0..self.k_skip
            invariant
                self.k_skip < 8,
                powers.len() == j + 1,
                forall|t: int| 0 <= t <= j ==> #[trigger] powers@[t] == e_sq_iter(z, t as nat),
        {
            let p = a.square(powers[j]);
            powers.push(p);
        }
        let ghost k = self.k_skip;
        let mut acc = powers[self.k_skip];
        proof {
            lemma_e_add(e_sq_iter(z, k as nat), F192::ZERO, F192::ZERO);
            assert(lin_upto(c@, z, 0) == F192::ZERO);
        }
        for j in 0..self.k_skip
            invariant
                k == self.k_skip,
                k < 8,
                c.len() == k + 1,
                powers.len() == k + 1,
                forall|t: int| 0 <= t <= k ==> #[trigger] powers@[t] == e_sq_iter(z, t as nat),
                acc == e_add(lin_upto(c@, z, j as nat), e_sq_iter(z, k as nat)),
        {
            proof {
                let t = e_mul(c@[j as int], powers@[j as int]);
                lemma_e_mul_comm(powers@[j as int], c@[j as int]);
                lemma_e_add(t, lin_upto(c@, z, j as nat), e_sq_iter(z, k as nat));
                lemma_e_add(lin_upto(c@, z, j as nat), t, e_sq_iter(z, k as nat));
            }
            acc = a.mul_const_add(powers[j], c[j], acc);
        }
        proof {
            lemma_e_mul_one(e_sq_iter(z, k as nat));
            assert(lin(c@, z) == vanishing_spec(pow2(k as nat), z));
            assert(lin(c@, z) == e_add(lin_upto(c@, z, k as nat), e_mul(c@[k as int], e_sq_iter(z, k as nat))));
        }
        acc
    }

    /// `1 / (z + node)` for each node.
    ///
    /// The generic `A: Arith` is `Native`; the `map` and `collect` are a loop pushing each inverse.
    fn inverses_at(a: &mut Native, z: F192, nodes: &[F192]) -> (r: Vec<F192>)
        ensures
            r.len() == nodes.len(),
            forall|i: int| 0 <= i < nodes.len() ==> #[trigger] r@[i] == e_inv(e_add(z, nodes@[i])),
    {
        let mut out: Vec<F192> = Vec::new();
        for i in 0..nodes.len()
            invariant
                out.len() == i,
                forall|t: int| 0 <= t < i ==> #[trigger] out@[t] == e_inv(e_add(z, nodes@[t])),
        {
            let node = nodes[i];
            let difference = a.add_const(z, node);
            out.push(a.inv(difference));
        }
        out
    }

    /// `1 / (z + s_i)` over `S`, which the Lagrange sum over `S` takes.
    pub fn inverses(self, a: &mut Native, z: F192) -> (r: Vec<F192>)
        requires
            self.spec_k_skip() < 8,
        ensures
            r.len() == pow2(self.spec_k_skip()),
            forall|i: int| 0 <= i < r.len() ==> #[trigger] r@[i] == e_inv(e_add(z, node(i))),
    {
        let size = self.size();
        proof {
            lemma_pow2_shl_small(self.k_skip as nat);
        }
        Self::inverses_at(a, z, &PHI_8_TABLE_192[..size])
    }

    /// `scale * sum_i values_i * inverses_i`.
    ///
    /// The generic `A: Arith` is `Native`; the `assert_eq!` on the lengths is a `requires`, the fold a loop.
    pub fn lagrange_with(a: &mut Native, scale: F192, inverses: &[F192], values: &[F192]) -> (r: F192)
        requires
            inverses.len() == values.len(),
        ensures
            r == e_mul(scale, e_sum_fn(|i: int| e_mul(values@[i], inverses@[i]), values.len() as nat)),
    {
        let zero = a.zero();
        let mut sum = zero;
        for i in 0..values.len()
            invariant
                inverses.len() == values.len(),
                sum == e_sum_fn(|t: int| e_mul(values@[t], inverses@[t]), i as nat),
        {
            proof {
                lemma_e_add(e_mul(values@[i as int], inverses@[i as int]), sum, sum);
            }
            sum = a.mul_add(values[i], inverses[i], sum);
        }
        a.mul(scale, sum)
    }

    /// The first round's message, known on `Lambda` and zero on `S`, interpolated at `z` over the window `S + Lambda`.
    ///
    /// Its value is `D_2l · V_S(z) · V_Lambda(z) · sum_i values_i / (z + lambda_i)`, `l` the domain's size, with `V_Lambda(z) = V_S(z) + V_S(phi_8(l))`.
    ///
    /// This barycentric form is the interpolant only for `z` off the window `S + Lambda`: at a node the vanishing factor is zero and `1 / 0` is taken as zero, so it gives 0 rather than the node's value. `z` is the verifier's challenge, so it lands on a node with probability at most `128 / 2^192`, where an honest proof would be rejected.
    ///
    /// The generic `A: Arith` is `Native`. `z` off the window's nodes and `vanishing = V_S(z)` are `requires`. The
    /// coefficients `self.vanishing_coefficients()` are bound to a name before `linearized` reads them.
    pub fn first_round_at(self, a: &mut Native, z: F192, vanishing: F192, values: &[F192]) -> (r: F192)
        requires
            self.spec_k_skip() < 8,
            vanishing == vanishing_spec(pow2(self.spec_k_skip()), z),
            values.len() == pow2(self.spec_k_skip()),
            off_nodes(2 * pow2(self.spec_k_skip()), z),
        ensures
            r == window_sum(pow2(self.spec_k_skip()), values@, z),
    {
        let ghost k = self.k_skip as nat;
        let size = self.size();
        proof {
            lemma_pow2_shl_small(k);
            lemma_pow2_shl_small(k + 1);
            lemma_pow2_unfold(k + 1);
        }
        let lambda = &PHI_8_TABLE_192[size..2 * size];
        let c = self.vanishing_coefficients();
        let offset = Self::linearized(&c, lambda[0]);
        let on_lambda = a.add_const(vanishing, offset);
        let both = a.mul(vanishing, on_lambda);
        let scaled = a.mul_const(both, window_denominator(2 * size));
        let inverses = Self::inverses_at(a, z, lambda);
        let r = Self::lagrange_with(a, scaled, &inverses, values);
        proof {
            let l = pow2(k);
            let s = node(l as int);
            assert(lambda@[0] == s);
            assert(lin(c@, s) == vanishing_spec(l, s));
            assert(lin(c@, z) == vanishing_spec(l, z));
            lemma_lin_add(c@, z, s, c.len() as nat);
            assert(lin(c@, e_add(z, s)) == vanishing_spec(l, e_add(z, s)));
            lemma_vanishing_double(k, z);
            assert(both == vanishing_spec(2 * l, z));
            assert(scaled == e_mul(vanishing_spec(pow2(k + 1), z), denominator_spec(k + 1)));
            let h = |i: int| e_mul(values@[i], inverses@[i]);
            lemma_sum_scale(scaled, h, l);
            assert forall|i: int| 0 <= i < l implies #[trigger] e_mul(scaled, h(i)) == e_mul(
                values@[i],
                lagrange_basis(2 * l, l + i, z),
            ) by {
                assert(lambda@[i] == node(l + i));
                lemma_lagrange_term(k + 1, l + i, z, values@[i]);
            }
            lemma_sum_ext(|i: int| e_mul(scaled, h(i)), |i: int| e_mul(values@[i], lagrange_basis(2 * l, l + i, z)), l);
        }
        r
    }

    /// `D_l · V_S(z)`, `l` the domain's size: the scale of the Lagrange sum over `S`.
    pub fn lagrange_scale(self, a: &mut Native, vanishing: F192) -> (r: F192)
        requires
            self.spec_k_skip() < 8,
        ensures
            r == e_mul(vanishing, denominator_spec(self.spec_k_skip())),
    {
        let size = self.size();
        proof {
            lemma_pow2_shl_small(self.k_skip as nat);
        }
        a.mul_const(vanishing, window_denominator(size))
    }

    /// `sum_i L_i(z) values_i` over `S`, `L_i` its Lagrange basis: `D_l · V_S(z) · sum_i values_i / (z + s_i)`.
    ///
    /// This barycentric form is the interpolant only for `z` off `S`: at a node `V_S(z)` is zero and `1 / 0` is taken as zero, so it gives 0 rather than the node's value. `z` is the verifier's challenge, so it lands on a node with probability at most `128 / 2^192`, where an honest proof would be rejected.
    ///
    /// The generic `A: Arith` is `Native`. `z` off the nodes and `vanishing = V_S(z)` are `requires`.
    pub fn lagrange_at(self, a: &mut Native, z: F192, vanishing: F192, values: &[F192]) -> (r: F192)
        requires
            self.spec_k_skip() < 8,
            vanishing == vanishing_spec(pow2(self.spec_k_skip()), z),
            values.len() == pow2(self.spec_k_skip()),
            off_nodes(pow2(self.spec_k_skip()), z),
        ensures
            r == lagrange_sum(pow2(self.spec_k_skip()), values@, z),
    {
        let scaled = self.lagrange_scale(a, vanishing);
        let inverses = self.inverses(a, z);
        let r = Self::lagrange_with(a, scaled, &inverses, values);
        proof {
            let log = self.k_skip as nat;
            let l = pow2(log);
            let h = |i: int| e_mul(values@[i], inverses@[i]);
            lemma_sum_scale(scaled, h, l);
            assert forall|i: int| 0 <= i < l implies #[trigger] e_mul(scaled, h(i)) == e_mul(values@[i], lagrange_basis(l, i, z)) by {
                lemma_lagrange_term(log, i, z, values@[i]);
            }
            lemma_sum_ext(|i: int| e_mul(scaled, h(i)), |i: int| e_mul(values@[i], lagrange_basis(l, i, z)), l);
        }
        r
    }
}

/// One term of the Lagrange sum as production computes it: `(V(z) D) (v / (z + s_i)) = v L_i(z)`, for `z` not
/// node `i`.
pub proof fn lemma_lagrange_term(log: nat, i: int, z: F192, v: F192)
    requires
        log <= 8,
        0 <= i < pow2(log),
        z != node(i),
    ensures
        e_mul(e_mul(vanishing_spec(pow2(log), z), denominator_spec(log)), e_mul(v, e_inv(e_add(z, node(i)))))
            == e_mul(v, lagrange_basis(pow2(log), i, z)),
{
    let l = pow2(log);
    let f = |k: int| e_add(z, node(k));
    let fi = f(i);
    let p = e_prod_fn(except(f, i), l);
    let d = denominator_spec(log);
    let h = e_inv(fi);
    lemma_prod_remove(f, l, i);
    lemma_e_add_zero(z, node(i));
    lemma_e_inverse(fi);
    lemma_weight_inverts(log, i);
    // V h = p (f_i h) = p.
    lemma_e_mul_comm(fi, p);
    lemma_e_mul_assoc(p, fi, h);
    lemma_e_mul_one(p);
    let vv = e_mul(fi, p);
    assert(e_mul(vv, h) == p);
    // (V d)(v h) = v ((V h) d).
    lemma_e_mul_assoc(e_mul(vv, d), v, h);
    lemma_e_mul_comm(e_mul(vv, d), v);
    lemma_e_mul_assoc(v, e_mul(vv, d), h);
    lemma_e_mul_assoc(vv, d, h);
    lemma_e_mul_comm(d, h);
    lemma_e_mul_assoc(vv, h, d);
}

} // verus!
