# 44. Conjecture P and primitive lists: what the divisor argument gives, one root outside $D$, the complete check at $n = 32$, and P implies PL in a window at every rate

Researcher 44, round 7. Brief: `34-round5-brief.md`. Starting points: notes 17 (Conjecture P), 26 (Theorem A), 30 (merges), 37 (transfer lemma, gap theorem, difference descent) and 39 (reduction to primitive lists), which are not repeated. Every statement is tagged **[proved]** (proof in this note), **[quoted]** (from a cited note, not re-proved), **[checked]** (numerically, sizes stated) or **[conjectured]**. Scripts are `scripts/44_*`, section 7 says how to run them.

Notation as in notes 17, 26, 37, 39. $F$ is a field of characteristic two, $D \subset F$ an $\mathbb{F}_2$-subspace of dimension $N$, $n = 2^N$. $D$ is **generic** if it has a basis $b_1, \dots, b_N$ algebraically independent over $\mathbb{F}_2$ (the formal model), and then $A = \mathbb{F}_2[b]$, $K = \mathbb{F}_2(b)$: $A$ is a unique factorization domain whose only unit is 1, and the nonzero elements of $D$ are pairwise non-associate primes of it. For nonconstant $\xi \in F(X)$ of degree $\delta$: $\xi = u_0/u_1$ with $u_0 + u_1 + u_2 = 0$ pairwise coprime, $R_i$ the roots of $u_i$ in $D$ (the fibres over $0, \infty, 1$), $r_i = |R_i|$, $\nu(\xi) = r_0 + r_1 + r_2$, $\Pi(\xi) = \{a \in D : \xi(X + a) = \xi(X)\}$. **P**: $\nu \le 2\delta + |\Pi|$ on a generic $D$. **P$_0$**: $\Pi = 0 \Rightarrow \nu \le 2\delta + 1$. $Z_S = \prod_{s \in S}(X + s)$, $L_U = Z_U$ for a subspace $U$. A point of a fibre of $\xi$ that lies outside $D \cup \{\infty\}$ is a **phantom root**. A character of $D$ is a homomorphism $\varphi : D \to \{\pm 1\}$, $\hat f(\varphi) = \sum_x f(x)\varphi(x)$, and $W^\perp$ is the group of characters trivial on a subspace $W$. Codewords are polynomials of degree $< k$, $T$ is an agreement count, $\Delta = T - k + 1$ the slack, $\rho = k/n$, $\tau = T/n$. A triple of list members is **bad** if its triple function is constant or has a nonzero period, a list is **primitive** if it has no bad triple, **PL**$(f)$: primitive lists have at most $f$ members (note 39).

## 0. Summary

**The honest headline.** Conjecture P is neither proved nor refuted in full. The divisor argument proposed in the brief does not prove it: carried out, it is the transfer lemma of note 37 in pointwise form, plus an identity that never couples two points of a fibre, and its key step is false (an explicit function with one root outside $D$ has a fibre of three points that is not a coset of periods). What the same circle of ideas does give is a complete theorem for one root outside $D$, by three-term identities and a Walsh transform. P is now verified exhaustively in every degree at $n = 32$, so it holds in every dimension $N \le 5$. For lists there is a new and simple consequence of P: a three-wise Johnson bound. It shows that P implies PL$(f)$ with an explicit $f(\rho, \tau)$ for every $\tau$ above a threshold $\tau_3(\rho)$ that lies strictly below the Johnson radius at every rate, and that no statement about three members can go below $\tau_3$. Through the reduction of note 39 this gives conditional list bounds of $2^{420}$ to $2^{790}$ at $N = 25$ in windows at all four rates, where note 17 had a window at rate 1/2 only.

| | statement | where it holds | status |
| --- | --- | --- | --- |
| 1.1 | A violation of P$_0$ is defined over $\mathbb{F}_2(b)$, homogeneous of degree 0 in $(b, X)$, and its contents are products of elements of $D$ | generic $D$ | proved (first part quoted from note 37) |
| 1.2 | If the zeros and poles of $\xi$ lie in a generic subspace $D^+ \supseteq D$, every other fibre meets $D$ in at most one coset of $\Pi(\xi)$ and P holds for $\xi$. Roots outside $D$ in general position are harmless | generic $D$ | proved |
| 2.1, 2.2 | **The divisor identity.** For $y$ in the fibre over 1: the parts without linear factors of the two phantom polynomials at $y$ coincide, and the linear parts satisfy one equation per direction. The second statement is the transfer lemma of note 37, the first contains no information on $R$ | generic $D$ | proved |
| 2.3 | Step (ii) of the brief is false, and step (i) is empty: $\xi = \prod_{h \in H \setminus 0}(X + h)/(e_2 X + e_3)$ has one pole outside $D$, no period, and takes the value 1 exactly on the three nonzero points of a plane $A_0$ | generic $D$, $N \ge 4$ | proved |
| 3.2 | **One root outside $D$.** If $\xi = c\,(X + \theta)^{\pm 1}\prod_{x \in D}(X + x)^{m(x)}$ with $\theta \notin D$, every fibre $\{y \in D : \xi(y) = c'\}$, $c' \ne 0, \infty$, has at most 3 points, and the functions with 3 points are exactly $\Psi \cdot \bigl(\Lambda/(\Lambda \bmod L_{A_0})\bigr)(X + y_\ast)$ with $\Psi$ periodic under a plane $A_0$, $\Lambda = L_H^{2^j}$, $H \cap A_0 = 0$, $\deg\Lambda \ge 4$ | generic $D$, all fields | proved; checked exhaustively on $1.6 \cdot 10^6$ divisors at $n = 16$ and $7.6 \cdot 10^5$ at $n = 8$ |
| 3.3, 3.4 | P holds whenever two of the three fibres have together at most one point outside $D \cup \{\infty\}$, counted with multiplicity. Hence P holds for $\nu \ge 3\delta - 2$, and **for all $\delta \le 4$ in every dimension without any computation** | generic $D$, all fields | proved |
| 3.5 | Two poles outside $D$, $n = 16$: fibres of 3, 4 and 6 points occur, $3072$ and $16$ functions without period have 4 and 6. No violation of P | generic $D$ | checked, exhaustive |
| 4 | **P at $n = 32$, all degrees.** Degrees 8, 9, 10, 11 (the open ones): $6.0 \cdot 10^9$ configurations after a full reduction by $\mathrm{AGL}(5, 2)$, representing $7.7 \cdot 10^{17}$; every solution is periodic and of a type that P allows. With degrees 2 to 7 and 12 to 15 rerun: **P holds in every dimension $N \le 5$** | generic $D$ | checked, exhaustive, two seeds |
| 5.1 | A primitive triple under P$_0$: $|S_i \cap S_j| + |S_i \cap S_l| + |S_j \cap S_l| \le 2k - 1 + |S_i \cap S_j \cap S_l|$, and its form at the levels of the descent | every subspace domain on which the hypothesis holds | proved from the hypothesis |
| 5.2 | **Three-wise Johnson bound.** $M$ sets of size $\alpha n_e$ in $n_e$ points whose triples all satisfy that inequality with $2\varrho n_e$ on the right: $M \le \max\bigl(1/(1 - \alpha),\ 3(\alpha + \alpha^2 - 2\varrho)/(\alpha^2(3 - \alpha) - 2\varrho)\bigr)$ as soon as $\alpha^2(3 - \alpha) > 2\varrho$ | any sets | proved |
| 5.3 | Sharpness: below $\tau_3(\rho)$, the root of $\tau^2(3 - \tau) = 2\rho$, exponentially many random sets satisfy every pair and triple constraint. So no statement about three members bounds lists below $\tau_3$ | any sets | proved |
| 5.5 | **P implies PL and a list bound.** If aperiodic functions obey $\nu \le 2\delta + 1$ on the quotients $D/U$, $\dim U < j_0$ (an excess $\epsilon n$ is allowed), then for $\tau > \tau_3(\rho)$ primitive lists at all levels have at most $f$ members and $\Lambda \le \binom{f+1}{3}^{j_0} 2^{Nj_0 - j_0(j_0-1)/2}\bigl((n/\Delta)^{\kappa_0 + 1} + 1\bigr)$ | every subspace domain on which the hypothesis holds; the hypothesis is Conjecture P for a generic $D$ | proved conditional on the hypothesis |

**Thresholds and numbers (section 5.4).** $\tau_3 = 0.6527, 0.4421, 0.3045, 0.2117$ at rates $1/2, 1/4, 1/8, 1/16$, against the Johnson radii $0.7071, 0.5, 0.3536, 0.25$. At $N = 25$, conditional on P: $2^{583}$ at $(1/2, 0.66)$, $2^{503}$ at $(1/4, 0.46)$, $2^{530}$ at $(1/8, 0.32)$, $2^{581}$ at $(1/16, 0.22)$. In the accounting of the brief (lists up to $2^{35(s - 10)}$ with $s$ points per level) the table of section 5.4 needs $s$ between 23 and 33.

**What this implies for H$_K$.** No unconditional theorem. The conditional statement is now: on a generic subspace, P (or its weak form wP of section 5.1: a linear excess forces one period) implies H$_K(\tau, b)$ with $b \approx N^2/2 + 3N\log_2 f$ for every $\tau > \tau_3(\rho)$ at every rate. Below $\tau_3$ a statement about four or more members is needed, whatever is proved about P.

## 1. Normal form, and roots in general position

**Lemma 1.1 (what a violation looks like). [proved; the first sentence quoted from note 37, section 4]** Let $D$ be generic and $\xi \in F(X)$ nonconstant with $\nu \ge 2\delta + 2$. Then $\xi \in K(X)$, and $\xi = v_0/v_1$, $v_0 + v_1 + v_2 = 0$, $v_i = \gamma_i Z_i h_i$ with $\gamma_i \in A$ pairwise coprime, $Z_i = \prod_{x \in R_i}(X + x)^{m_i(x)}$ and $h_i \in A[X]$ primitive without roots in $D$, $\deg_X h_i \le s_i := \delta - r_i$. Moreover (a) every prime factor of $\gamma_0\gamma_1\gamma_2$ is an element of $D$, and (b) $\xi$ is homogeneous of degree 0: $\xi(\lambda X; \lambda b) = \xi(X; b)$, so the $v_i$ can be taken homogeneous in $(b, X)$ and every irreducible factor of $h_i$ in $\mathbb{F}_2[b, X]$ is homogeneous.

*Proof.* (a) Let $p$ be a prime of $A$ dividing $\gamma_l$ and reduce modulo $p$: $\bar v_i = \bar v_j \ne 0$ has degree at most $\delta$ and is divisible by $\bar Z_i$ and $\bar Z_j$. If $p$ is not an element of $D$, the reduction is injective on $D$ (two points coincide modulo $p$ only if $p$ divides their sum), so $\bar Z_i\bar Z_j$ divides $\bar v_i$, and $r_i + r_j \ge \nu - \delta \ge \delta + 2$ is a contradiction. (b) Let $\lambda$ be an indeterminate and $\sigma$ the automorphism $b_i \mapsto \lambda b_i$ of $K(\lambda)$ over $\mathbb{F}_2(\lambda)$. The function $\eta(X) = \xi^\sigma(\lambda X)$ has degree $\delta$ and the points of $R$ in the same fibres as $\xi$, so $\eta = \xi$ by the uniqueness lemma (note 26 Lemma 1.2). $\square$

So the first subtlety of the brief disappears for violations: the coefficients are in $\mathbb{F}_2(b)$ and the phantom roots are algebraic over it. The opposite case is easy:

**Proposition 1.2 (roots in general position). [proved]** Let $D^+ \supseteq D$ be a generic subspace of $F$ (for instance $D \oplus \langle\theta_1, \dots, \theta_r\rangle$ with $b_1, \dots, b_N, \theta_1, \dots, \theta_r$ algebraically independent over $\mathbb{F}_2$), and let all zeros and poles of $\xi$ lie in $D^+ \cup \{\infty\}$. Then for every $c' \ne 0, \infty$ the set $\{y \in D : \xi(y) = c'\}$ is empty or contained in one coset of $\Pi(\xi)$, and $\nu(\xi) \le r_0 + r_1 + |\Pi(\xi)|$.

*Proof.* Theorem A of note 26 on $D^+$: two points of $D$ with the same value differ by a period of $\xi$ lying in $D^+$, and this period is in $D$. $\square$

All the difficulty of P is therefore in phantom roots that are algebraically dependent on $b$, and in a violation every one of them is.

## 2. The divisor identity: what it says and where the argument of the brief stops

Let $D$ be generic and $\xi \in K(X)$ in the normal form of Lemma 1.1, with contents $\gamma_i$ that are products of elements of $D$ (by the proof of part (a) this is automatic for $\nu \ge 2\delta + 1$, and it holds trivially in Example 2.3). For $q \in A \setminus 0$ write $q = \mathrm{lin}(q)\,\mathrm{nl}(q)$, the product of the prime factors of $q$ that are elements of $D$ and the rest, $v_a$ for the valuation of $A$ at $a \in D \setminus 0$, and $c_i(a) = v_a(\gamma_i)$.

**Proposition 2.1 (divisor form of a fibre). [proved]** Let $\{i, j, l\} = \{0, 1, 2\}$ and $y \in D$ with $Z_i(y)Z_j(y) \ne 0$. Then $v_l(y) = 0$ (that is, $y \in R_l$) if and only if

1. $\mathrm{nl}(h_i(y)) = \mathrm{nl}(h_j(y))$, and
2. for every $a \in D \setminus 0$: $\ v_a(h_i(y)) - v_a(h_j(y)) = c_j(a) - c_i(a) + m_j(y + a) - m_i(y + a)$.

*Proof.* $v_l(y) = 0$ iff $\gamma_i Z_i(y) h_i(y) = \gamma_j Z_j(y) h_j(y)$ in $A$. $Z_i(y) = \prod_{a \ne 0} a^{m_i(y + a)}$, the $\gamma$ are products of elements of $D$, and $A$ is factorial with the single unit 1. $\square$

This is the statement "the divisor of $\xi(y)$ is zero" of the brief, written on $\mathbb{P}^{N-1}$ with coordinates $b$: with $\theta$ running over the roots of $h_i$ and $h_j$, the divisor of $\prod(y + \theta)^{\pm 1}$ is the divisor of $h_i(y)/h_j(y)$ up to leading coefficients, and passing to a model of the splitting field adds nothing, because both sides of the identity are norms.

**Corollary 2.2. [proved]** (2) for all $y \in R_l$ is the transfer lemma (note 37 Lemma 4.1) in pointwise form: if $y \in R_l$, $y + a \in R_j$ and $a \nmid \gamma_i$ then $a \mid h_i(y)$, that is, the class of $y$ modulo $a$ is a root of $\bar h_i$; if $a \mid \gamma_i$ and $y + a \notin R_j$ then $a \mid h_j(y)$. Summing over $y$ gives $|R_l \cap (R_j + a)| \le s_i$ off the content of $v_i$, which is part 1 of that lemma, and $|R_l \setminus (R_j + a)| \le 2s_j$ on it, which is its part 2 up to the factor 2 that the count with multiplicities of note 37 removes. (1) contains no information about $(R_0, R_1, R_2)$: it compares the phantom zeros and the phantom poles at one and the same point $y$.

*Proof.* In (2), $m_j(y + a) \ge 1$, $m_i(y + a) = 0$ and $c_i(a) = 0$ give $v_a(h_i(y)) \ge 1$. In the second case $c_i(a) \ge 1$, $c_j(a) = 0$, $m_j(y + a) = 0$ give $v_a(h_j(y)) \ge 1$. $\bar h_i$ has at most $s_i$ roots and a class has two points. $\square$

**Where the argument of the brief stops.** The brief proposes: (i) the phantom roots organize in cosets $\theta + D$ and $m$ extends to them; (ii) away from places over linear forms the divisor identity forces $m(y_1 + z) = m(y_2 + z)$, hence a period; (iii) the places over linear forms are handled by an induction on $N$. The identity for $y_1$ and the identity for $y_2$ are two separate instances of Proposition 2.1. Away from linear forms each of them is (1), which is satisfied by matching, at the same $y$, the zeros of $y + \theta$ ($\theta$ a phantom zero) with the zeros of $y + \theta'$ ($\theta'$ a phantom pole). Nothing relates $y_1$ to $y_2$ there. Over the linear forms each of them is (2), in which a zero of $\xi$ at $y + a$ is compensated by a phantom pole that reduces to the class of $y$ modulo $a$. In Theorem A there are no phantom roots, (2) reads $m_j(y + a) - m_i(y + a) = c_i(a) - c_j(a)$, the right side does not depend on $y$, and that is the whole proof. With phantom roots the right side is corrected by $v_a(h_i(y)) - v_a(h_j(y))$, which depends on $y$, and the conclusion fails:

**Example 2.3 (a fibre that is not a coset). [proved]** Let $N \ge 4$, $A_0$ and $H$ two planes of $D$ with $A_0 \cap H = 0$, with nonzero elements $a_1, a_2, a_3$ and $h_1, h_2, h_3$, and $e_2 = e_2(a) + e_2(h)$, $e_3 = e_3(a) + e_3(h)$ (elementary symmetric functions of the two triples; $e_1 = 0$ for both). Then
$$\prod_{k}(X + h_k) + \prod_{i}(X + a_i) = e_2 X + e_3, \qquad \xi := \frac{(X + h_1)(X + h_2)(X + h_3)}{e_2 X + e_3} \quad\text{satisfies}\quad \xi + 1 = \frac{(X + a_1)(X + a_2)(X + a_3)}{e_2 X + e_3} .$$
$\xi$ has degree 3, so no period ($|\Pi|$ divides $\delta$), its only pole in $\overline K$ besides $\infty$ is $\theta = e_3/e_2 \notin D$ ($e_2$ is a nondegenerate quadratic form in $a_1, a_2, h_1, h_2$, hence irreducible, and it does not divide $e_3$), and its fibre over 1 in $D$ is $\{a_1, a_2, a_3\}$: three points, not a coset, and $m = 1_{H \setminus 0}$ is not invariant under $a_1 + a_2$. Here $a_i + \theta = \prod_k(a_i + h_k)/e_2$: the zeros of $y + \theta$ are at the linear places $a_i + h_k$, where the phantom pole collides with the zero $h_k$ of $\xi$ at the point $y = a_i$ itself. So (ii) fails although every cross term sits at a linear place. (i) is bookkeeping without content here: the coset $\theta + D$ carries a single root. In the family of section 3 the phantom root is $y_\ast$ plus the nonzero element of the kernel of an additive polynomial of degree 2, and the natural generalization (section 6) has phantom roots forming an $\mathbb{F}_2$-space that meets $D$ in 0, translated by a point of $D$: a structure transversal to the cosets of $D$.

(iii) is the merge of note 30 (its Lemma 4.1 and Lemma 7.1: rank is semicontinuous and the excess does not decrease under a nondegenerate reduction). Its obstruction is known and I have nothing to add to it: the terminal patterns of note 30 section 6.1, and in the dense regime the fact that every direction is degenerate (note 26 section 5.3).

**The precise residue.** For a function with zeros and poles in $D$ except $r$ phantom poles, the fibre condition on $r + 2$ points $Y$ is the vanishing of the $(r+1)$-th divided difference of $y \mapsto P_y = \prod_x (y + x)^{m(x)}$, an identity $\sum_{y \in Y} \varrho_y = 0$ between $r + 2$ products of elements of $D$, where $\varrho_y$ has the exponent $(m - 1_Y)(y + a)$ at $a$. $r = 0$ is Theorem A (two terms), $r = 1$ is section 3 (three terms, classified by note 26 Lemma 2.2). For $r \ge 2$ no classification is known, and P in the dense regime needs $r$ of order $n$: for three members at agreement $0.7\,n$ and rate 1/2 each fibre has about $n/10$ phantom roots.

## 3. One root outside $D$

### 3.1 Three-term identities with integer exponents

**Lemma 3.1. [quoted: note 26 Lemma 2.2, after clearing denominators]** Let $D$ be generic and $T_1, T_2, T_3 \in K^\times$ products of integer powers of nonzero elements of $D$, $T_i = \prod_{a} a^{e_i(a)}$, with $T_1 + T_2 + T_3 = 0$. Then there are $G : D \setminus 0 \to \mathbb{Z}$, a subspace $H \le D$, elements $\ell_1, \ell_2, \ell_3 \in D \setminus H$ with $\ell_1 + \ell_2 + \ell_3 \in H$ (so the three cosets $\ell_i + H$ are distinct) and $j \ge 0$ such that $e_i = G + 2^j\,1_{\ell_i + H}$ for $i = 1, 2, 3$.

### 3.2 The theorem

**Theorem 3.2 (one root outside $D$). [proved]** Let $D$ be generic, $m : D \to \mathbb{Z}$, $c \in F^\times$, $\theta \in F \setminus D$ and $\xi = c\,(X + \theta)^{-1}\prod_{x \in D}(X + x)^{m(x)}$.

1. For every $c' \in F^\times$ the fibre $\{y \in D : \xi(y) = c'\}$ has at most three points.
2. If $y_1, y_2, y_3$ are three points of one fibre, put $a_1 = y_2 + y_3$, $a_2 = y_1 + y_3$, $a_3 = y_1 + y_2$, $A_0 = \{0, a_1, a_2, a_3\}$ and $y_\ast = y_1 + y_2 + y_3$. Then there are a subspace $H \le D$ with $H \cap A_0 = 0$ and $j \ge 0$ with $Q := 2^j|H| \ge 4$ such that
$$m = g + 2^j\,1_{y_\ast + H} - \delta_{y_\ast}, \qquad g \text{ invariant under } A_0,\quad g = 0 \text{ on } y_\ast + A_0 .$$
Moreover, with $\Lambda = L_H^{2^j}$ (an additive polynomial of degree $Q$) and $\Lambda \bmod L_{A_0} = c_1 X^2 + c_0 X$:
$$\xi(X) = \Psi(X)\cdot\frac{\Lambda(X + y_\ast)}{(\Lambda \bmod L_{A_0})(X + y_\ast)}, \qquad \Psi \text{ invariant under } A_0 \text{ with divisor } g, \qquad \theta = y_\ast + c_0/c_1 \in K .$$
3. Conversely, for every plane $A_0$, point $y_\ast$, subspace $H$ with $H \cap A_0 = 0$, $j$ with $2^j|H| \ge 4$ and $A_0$-invariant $g$ vanishing on $y_\ast + A_0$, the function so defined has $\theta \notin D$ and takes one value on the three points $y_\ast + a_i$.

The same holds for $\xi = c\,(X + \theta)\prod(X + x)^{m(x)}$, applied to $1/\xi$.

*Proof.* Let $y_1, y_2, y_3$ be distinct points of the fibre over $c'$. Then $m(y_i) = 0$ and, with $P_i = \prod_x (y_i + x)^{m(x)} \in K^\times$ and $\lambda = c'/c$: $y_i + \theta = P_i/\lambda$. Subtracting, $\lambda(y_i + y_j) = P_i + P_j$, so $\lambda \in K^\times$, and eliminating $\lambda$:
$$T_1 + T_2 + T_3 = 0, \qquad T_i := P_i a_i, \qquad e_i(a) = m(y_i + a) + [a = a_i] \quad (a \in D \setminus 0).$$
Apply Lemma 3.1. Put $m^\ast = m + \delta_{y_\ast}$ and $C_i = y_i + \ell_i + H$. Since $y_i + a_i = y_\ast$ for each $i$, substituting $x = y_i + a$ gives
$$m^\ast(x) = G(x + y_i) + 2^j\,1_{C_i}(x) \qquad (x \ne y_i,\ i = 1, 2, 3). \tag{1}$$

*Step A.* Let $i \ne k$ and $u = y_i + y_k$. Equating (1) for $i$ and $k$ at $x$ and at $x + u$ and adding: $1_{C_i} + 1_{C_i + u} = 1_{C_k} + 1_{C_k + u}$ on $D \setminus \{y_i, y_k\}$. The four sets are cosets of $H$, and the two sides are invariant under $u$ and under $H$. If $C_k \notin \{C_i, C_i + u\}$ then $C_k$ and $C_k + u$ are disjoint from the support of the left side, so they lie in $\{y_i, y_k\}$, and symmetrically for $C_i$, $C_i + u$. If $u \notin H$ this forces $|H| = 1$ and $\{C_k, C_k + u\} = \{\{y_i\}, \{y_k\}\} = \{C_i, C_i + u\}$, and if $u \in H$ it forces $C_k = \{y_i, y_k\} = C_i$: a contradiction in both cases. So $C_k \in \{C_i, C_i + u\}$.

*Step B.* $C_k = C_i + u$ means $\ell_k + H = \ell_i + H$, which is excluded. So $C_k = C_i$, that is $\ell_i + \ell_k + u \in H$, and as $\ell_i + \ell_k \in \ell_l + H$: $a_l = u \in \ell_l + H$. Hence $\ell_l + H = a_l + H$ for $l = 1, 2, 3$, $H \cap A_0 = 0$, and $C_i = y_i + a_i + H = y_\ast + H =: C$ for all $i$.

*Step C.* By (1), $G(x + y_i) = G(x + y_k)$ for $x \notin \{y_i, y_k\}$: $G(a) = G(a + a_l)$ for $a \notin \{0, a_l\}$. So $G$ is constant on every coset of $A_0$ other than $A_0$, and $G(a_1) = G(a_2) = G(a_3)$. Evaluating (1) with the index $i$ at $x = y_k$, $k \ne i$: $0 = m^\ast(y_k) = G(a_l) + 2^j[a_k \in H] = G(a_l)$. So $G = 0$ on $A_0 \setminus 0$, and at $x = y_\ast$: $m^\ast(y_\ast) = G(a_i) + 2^j = 2^j$. With $g(x) = G(x + y_1)$ off $y_\ast + A_0$ and $g = 0$ on it, (1) is $m^\ast = g + 2^j 1_C$ on all of $D$, which is the formula of part 2.

*Step D.* $T_i = M_0\,\Lambda(a_i)$ with $M_0 = \prod_a a^{G(a)}$, so $P_i = M_0\Lambda(a_i)/a_i$, $\lambda = M_0(a_2\Lambda(a_1) + a_1\Lambda(a_2))/(a_1a_2a_3)$ and
$$\theta = y_1 + \frac{a_2a_3\,\Lambda(a_1)}{a_2\Lambda(a_1) + a_1\Lambda(a_2)} .$$
If $Q = 1$ then $\Lambda = X$ and $P_1 = P_2$, impossible. If $Q = 2$ then $\Lambda = X^2 + hX$ with $h \in D \setminus A_0$ or $h = 0$, the denominator is $a_1a_2a_3$ and $\theta = y_\ast + h \in D$, excluded. So $Q \ge 4$. Writing $\Lambda \equiv c_1X^2 + c_0X$ modulo $L_{A_0}$, the values on $A_0$ give $c_1 = (a_2\Lambda(a_1) + a_1\Lambda(a_2))/(a_1a_2a_3)$ and $c_0 = \Lambda(a_1)/a_1 + c_1a_1$, so $c_0/c_1 = \theta + y_\ast$, and $\Lambda(X')/(\Lambda \bmod L_{A_0})(X')$, $X' = X + y_\ast$, has the divisor $2^j 1_{y_\ast + H} - \delta_{y_\ast} - \delta_\theta$. This is the second formula, with $\Psi$ of divisor $g$.

*Step E (Walsh).* For a character $\varphi \notin A_0^\perp$, $\hat g(\varphi) = 0$, so
$$\hat m(\varphi) = \varphi(y_\ast)\bigl(Q\,[\varphi \in H^\perp] - 1\bigr) \in \{\pm 1, \pm(Q - 1)\}, \qquad Q - 1 \ge 3. \tag{2}$$

*Step F (no fourth point).* Let $y_4$ be a fourth point of the fibre. The triple $(y_1, y_2, y_4)$ has its own data $A_0', H', Q' \ge 4$ and $y_\ast' = y_1 + y_2 + y_4 \ne y_\ast$. For $\varphi \notin A_0^\perp \cup A_0'^\perp$ both forms of (2) hold. If the common absolute value is 1, then $\varphi \notin H^\perp \cup H'^\perp$ and $\varphi(y_\ast) = \varphi(y_\ast')$. If it is at least 3, then $\varphi \in H^\perp \cap H'^\perp$, $Q = Q'$ and again $\varphi(y_\ast) = \varphi(y_\ast')$. So the $n/2$ characters with $\varphi(y_\ast + y_\ast') = -1$ lie in $A_0^\perp \cup A_0'^\perp$. But $A_0^\perp \cap A_0'^\perp = (A_0 + A_0')^\perp$ has at least $n/8$ elements ($A_0 + A_0'$ has dimension at most 3, because both planes contain $y_1 + y_2$), so $|A_0^\perp \cup A_0'^\perp| \le n/4 + n/4 - n/8 < n/2$. Contradiction. This proves part 1.

*Part 3.* The identity $\sum_i M_0\Lambda(a_i) = M_0\Lambda(a_1 + a_2 + a_3) = 0$ holds, $a_2\Lambda(a_1) + a_1\Lambda(a_2) \ne 0$ for $Q \ge 2$ (the two terms are distinct products of primes), so $\lambda$ and $\theta$ are defined and $y_i + \theta = P_i/\lambda$ for $i = 1, 2, 3$. If $\theta$ were a point $z$ of $D$, $\xi$ would have its divisor in $D$ and by Theorem A of note 26 the function $m - \delta_z = g + 2^j 1_{y_\ast + H} - \delta_{y_\ast} - \delta_z$ would be $A_0$-invariant. A coset of $A_0$ meets $y_\ast + H$ in at most one point, so on the coset of $y_\ast + h$, $h \in H \setminus 0$, invariance forces $z = y_\ast + h$ and $2^j = 1$, hence $|H| \le 2$ and $j = 0$ if $|H| = 2$. On $y_\ast + A_0$ it forces $2^j - 1 - [z = y_\ast] = 0$, and if $H = 0$ the coset of $z$ (where the function is $-1$ at $z$ and $0$ elsewhere unless $z = y_\ast$) forces $z = y_\ast$, so $j = 1$. In every case $Q \le 2$. $\square$

In words: with one phantom root the conclusion of Theorem A (a fibre is a coset of periods) is false, but the count survives with room to spare, and the only way to get three points is the Euclidean division of one additive polynomial by another: $\Lambda \equiv \Lambda \bmod L_{A_0}$ on $A_0$, both sides additive, the left one split over $D$ and the right one not. Example 2.3 is $H$ a plane, $j = 0$, $g = 0$, $y_\ast = 0$.

### 3.3 Consequences for P

**Corollary 3.3. [proved]** Let $D$ be generic and $\xi \in F(X)$ nonconstant such that two of its three fibres over $0, 1, \infty$ contain together at most one point outside $D \cup \{\infty\}$, counted with multiplicity. Then $\nu(\xi) \le 2\delta + |\Pi(\xi)|$. If there is such a point, $\nu(\xi) \le 2\delta + 1$.

*Proof.* By the symmetry of the three values let the two fibres be those over $0$ and $\infty$. Without a phantom root this is Theorem A of note 26. Otherwise, replacing $\xi$ by $1/\xi$ if needed, $\xi$ is as in Theorem 3.2. Let $M^+ = \sum_x m(x)^+$ and $M^- = \sum_x m(x)^-$, so $\delta = \max(M^+, M^- + 1)$, $r_0 \le M^+$, $r_1 \le M^-$ and $r_2 \le 3$. If $r_2 \le 2$: $\nu \le M^+ + (M^- + 1) + 1 \le 2\delta + 1$. If $r_2 = 3$: $\sum_x m(x) = \sum_x g(x) + Q - 1 \equiv -1 \pmod 4$, because $g$ is invariant under a plane and $4 \mid Q$. So $M^+ - (M^- + 1) \equiv 2 \pmod 4$, the smaller of $M^+$ and $M^- + 1$ is at most $\delta - 2$, and $\nu \le M^+ + (M^- + 1) + 2 \le 2\delta$. $\square$

**Corollary 3.4. [proved]** (i) P holds for every $\xi$ with $\nu(\xi) \ge 3\delta - 2$, and for $\nu = 3\delta - 3$ unless $r_0 = r_1 = r_2 = \delta - 1$. (ii) **P holds for all $\xi$ of degree at most 4, on generic subspaces of every dimension, over every field, without any computation.**

*Proof.* (i) $\sum_i(\delta - r_i) \le 2$ gives two fibres with $(\delta - r_i) + (\delta - r_j) \le 1$, and a fibre with $\delta - r_i = 1$ has at most one point outside $D \cup \{\infty\}$, simple. For the sum 3 the patterns $(3, 0, 0)$ and $(2, 1, 0)$ have such a pair. (ii) A violation of P$_0$ in degree $\delta \le 4$ has $\nu \ge 2\delta + 2 \ge 3\delta - 2$. P follows from P$_0$ in the same degrees (note 17 Lemma 4.1). $\square$

Note 26 had (i) for $\nu \ge 3\delta - 1$ and (ii) for $\delta \le 3$ by hand and for $\delta = 4$ by a computation of $1.7 \cdot 10^8$ configurations. The list of cases in which P is proved is now: two fibres in $D \cup \{\infty\}$ (note 26); two fibres with one simple phantom root (Corollary 3.3); roots in general position (Proposition 1.2); $3\delta - \nu < \delta^2/4n$ (note 37); $\delta \le 4$; $N \le 5$ (section 4, computer).

### 3.4 Checks

**[checked, exhaustive]** `44_onephantom N maxmult`: $D$ a random subspace of $\mathrm{GF}(2^{64})$, the three points $1, 2, 3$ of $\mathbb{F}_2^N$ (every triple of distinct points is equivalent to it under the affine group), every $m : D \setminus \{1, 2, 3\} \to [-\mu, \mu]$. For each $m$ with $P_1a_1 + P_2a_2 + P_3a_3 = 0$ the program computes $\theta$, the whole fibre, and searches $(H, j)$.

| $n$ | $\mu$ | divisors | identity holds | $\theta = \infty$ | $\theta \in D$ | $\theta \notin D$ | fibre sizes for $\theta \notin D$ | types $(2^j, \lvert H\rvert)$ : count | without the structure |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 16 | 1 | 1594323 | 522 | 27 | 243 | 252 | 3 : 252 | $(1, 4)$ : 128, $(2, 2)$ : 108, $(2, 4)$ : 16 | 0 |
| 8 | 3 | 16807 | 77 | 7 | 31 | 39 | 3 : 39 | $(2, 2)$ : 20, $(4, 1)$ : 7, $(4, 2)$ : 12 | 0 |
| 8 | 7 | 759375 | 240 | 15 | 71 | 154 | 3 : 154 | $(2, 2)$ : 52, $(4, 1)$ : 15, $(4, 2)$ : 44, $(8, 1)$ : 15, $(8, 2)$ : 28 | 0 |

The counts at $n = 16$ are those of part 3: $16$ planes $H$ complementary to $A_0$ times $2^3$ choices of $g$ on the three cosets $h + A_0$ for $(1, 4)$; $12 \cdot 9$ for $(2, 2)$; $16$ for $(2, 4)$. Same numbers with a second seed.

### 3.5 Beyond one root: the additive mechanism, and data for two poles

**Remark 3.5 (the additive mechanism). [proved]** For subspaces $A_1, H \le D$ with $H \cap A_1 = 0$ and $\Lambda = L_H^{2^j}$ with $\deg\Lambda \ge |A_1|$, the remainder $\Lambda \bmod L_{A_1}$ is an additive polynomial of degree at most $|A_1|/2$ (the remainder of $X^{2^i}$ modulo an additive polynomial is additive), it agrees with $\Lambda$ on $A_1$, and so $\xi = \Lambda/(\Lambda \bmod L_{A_1})$ takes the value 1 on $A_1 \setminus 0$. Its poles are the nonzero elements of the kernel of the remainder, an $\mathbb{F}_2$-space of at most $|A_1|/2$ elements. So $|A_1| - 1$ points in a fibre cost at most $|A_1|/2 - 1$ poles outside $D$: 3 points for one pole, 7 for three. Theorem 3.2 says that for one phantom root this is the only mechanism, up to a factor periodic under $A_1$.

**[checked, exhaustive]** `44_twophantom`: $n = 16$, the points $1, 2, 3$ in a fibre, every $m$ with values in $\{-1, 0, 1\}$ on the other 13 points, $q$ the polynomial of degree at most 2 with $q(y_i) = P_{y_i}$, $\xi = \prod(X + x)^{m(x)}/q$. Of the $3^{13}$ functions, $1590061$ have two poles outside $D$. Their fibre through the three points has 3 points for $1585143$ of them, 4 points for $4782$ ($1710$ of these have a period, under which the two phantom poles are exchanged) and 6 points for $136$ ($120$ with a period). There is no fibre of 5 or of more than 6 points. The $3072$ and $16$ functions without period and with 4 and 6 points have $|\deg\text{num} - \deg\text{den}| \ge 2$ and $= 12$, and none violates P. So with two phantom roots a fibre can be larger than with one, in a way that does not fit the numerology of Remark 3.5, the four-term identities have solutions without period, and in all of them the degrees of numerator and denominator differ by more than P requires (P needs a difference of at least 1 for 4 points and 3 for 6 points). I have no classification.

## 4. P at $n = 32$ in every degree

Notes 17 and 26 left degrees 8 to 11 at $n = 32$ unchecked, estimating $10^{11}$ configurations per degree. With a complete reduction by the affine group there are between $4 \cdot 10^8$ and $3 \cdot 10^9$.

**Method.** `44_n32 N delta part parts [seed]`. A configuration is $(R_0, R_1, R_2)$, pairwise disjoint, $\delta \ge |R_0| \ge |R_1| \ge |R_2|$, $\sum = 2\delta + 2$. $R_2$ runs over representatives of the orbits of $\mathrm{AGL}(N, 2)$ on $|R_2|$-subsets (breadth-first search on all subsets with three generators of the group, a transversal element stored for every subset). $R_1$ runs over representatives of the orbits, on the subsets of the complement, of a subgroup $H_0$ of the stabilizer of $R_2$ generated by up to 14 random Schreier generators. $R_0$ runs over all subsets of the rest. **Coverage does not depend on $H_0$ being the whole stabilizer** (a smaller group gives more representatives, never fewer), and the program verifies it: the orbit sizes are summed, and the weighted number of configurations must equal $\binom{n}{r_2}\binom{n - r_2}{r_1}\binom{n - r_2 - r_1}{r_0}$ for every size pattern. It does, in every run (the sums are in double precision; for every size pattern the sum equals the expected value exactly, and the grand total at $\delta = 11$ differs from its expected value by one unit of rounding). The singularity test is the Hankel determinant of note 26 section 6.1, of size $t = \delta - r_0 + 1 \le 5$, with the products $Z_{R_0}(y)$, $y \in R_2$, updated along the enumeration. A configuration that is nonsingular for the random basis is nonsingular for the generic subspace, so "no solution" is rigorous up to the correctness of the program. For a singular configuration the solution space is computed, and the reduced $\xi$, its degree, $\nu$ and $|\Pi|$ (code of `26_search.c`); by note 26 Lemma 1.2 this is the only reduced solution.

**Validation. [checked]** At $n = 8$ and $n = 16$ the weighted numbers of configurations and of singular ones equal those of note 17 in every degree: $420$ and $28$, $280$ and $0$ at $n = 8$; at $n = 16$, $120120$ and $840$; $3603600$ and $0$; $29429400$ and $19320$; $76096020$ and $23660$; $52972920$ and $26040$; $4458168$ and $0$. At $n = 32$ the types in degrees 2 to 7 and 12 to 15 are those of notes 17 and 26. Two exact counts at $n = 32$, done by hand from the description "periodic with misplaced points" (the "if" direction of note 17 Proposition 4.2), equal the weighted numbers of singular configurations of the program. Degree 11: the singular patterns should be exactly the flats with at most 3 misplaced points (three cosets of a subspace $V$ of 8 elements, one per colour, of which $24 - z$ points are kept, and $z \le 3$ further points that lie in the fourth coset or carry a wrong colour and are absorbed in a common factor of degree $z$). Their number is $620\,\sum_{z \le 3}\binom{24}{z}\sum_{w \le z}\binom 8w 3^w\binom zw 2^{z-w} = 620 \cdot 6817457 = 4226823340$, the number found. Degree 14: $31 \cdot 16 \cdot 1758471 = 872201616$ patterns that are unions of 15 classes of some $\{0, a\}$ (colourings with at most 7 classes per colour), $7812000$ further ones of the type "seven cosets of a plane and two points" and $11249280$ further ones of the type "three cosets of $V$ and six points": in total $891262896$, the number found. So in these two degrees the singular configurations are exactly those that P allows, counted independently of the program.

**Results at $n = 32$. [checked, exhaustive]** Seed 1. Degrees 8 to 11 were also run with seed 2 (another random subspace and other Schreier generators): identical numbers of orbits, of singular configurations and of types.

| $\delta$ | representatives tested | configurations represented (unordered) | singular representatives | singular configurations | reduced types $(\deg, \nu, \lvert\Pi\rvert)$ : representatives | violations of P |
| --- | --- | --- | --- | --- | --- | --- |
| 2 | 756 | $1.36 \cdot 10^7$ | 14 | 17360 | $(2, 6, 2)$ : 14 | 0 |
| 3 | 8775 | $2.95 \cdot 10^9$ | 0 | 0 | | 0 |
| 4 | 209300 | $2.37 \cdot 10^{11}$ | 84 | 2447760 | $(4, 10, 2)$ : 72, $(4, 12, 4)$ : 12 | 0 |
| 5 | 1923306 | $9.44 \cdot 10^{12}$ | 622 | 6466600 | $(4, 12, 4)$ : 622 | 0 |
| 6 | 16050573 | $2.08 \cdot 10^{14}$ | 2375 | 76123600 | $(4, 12, 4)$ : 1235, $(6, 14, 2)$ : 1140 | 0 |
| 7 | 78801987 | $2.68 \cdot 10^{15}$ | 0 | 0 | | 0 |
| **8** | 367435110 | $2.06 \cdot 10^{16}$ | 2960 | 757017520 | $(8, 18, 2)$ : 2656, $(8, 20, 4)$ : 112, $(8, 24, 8)$ : 192 | 0 |
| **9** | 984329580 | $9.51 \cdot 10^{16}$ | 2871 | 981838200 | $(8, 20, 4)$ : 1031, $(8, 24, 8)$ : 1840 | 0 |
| **10** | 2040304266 | $2.58 \cdot 10^{17}$ | 15235 | 5706288048 | $(8, 20, 4)$ : 750, $(8, 24, 8)$ : 8944, $(10, 22, 2)$ : 5541 | 0 |
| **11** | 2613361868 | $3.95 \cdot 10^{17}$ | 23833 | 4226823340 | $(8, 24, 8)$ : 23833 | 0 |
| 12 | 1782128257 | $3.17 \cdot 10^{17}$ | 17925 | 5447932560 | $(8, 24, 8)$ : 13965, $(12, 26, 2)$ : 3508, $(12, 28, 4)$ : 452 | 0 |
| 13 | 597358776 | $1.16 \cdot 10^{17}$ | 3543 | 449788920 | $(8, 24, 8)$ : 2793, $(12, 28, 4)$ : 750 | 0 |
| 14 | 75089673 | $1.48 \cdot 10^{16}$ | 985 | 891262896 | $(8, 24, 8)$ : 139, $(12, 28, 4)$ : 103, $(14, 30, 2)$ : 743 | 0 |
| 15 | 1270122 | $2.74 \cdot 10^{14}$ | 0 | 0 | | 0 |

Every solution in degrees 8 to 11 is one of: $\xi_0 \circ L_{\{0, a\}}$ with $\xi_0$ of degree 4 or 5 on $D/a$ and the generic count $2\delta_0 + 1$ of points ($(8, 18, 2)$, $(10, 22, 2)$); $\xi_0 \circ L_\Pi$ with $|\Pi| = 4$, $\deg\xi_0 = 2$ and 5 of the 8 points of $D/\Pi$ ($(8, 20, 4)$); a flat $\mu \circ L_\Pi$, $|\Pi| = 8$ ($(8, 24, 8)$), in each case with the remaining points of the pattern absorbed in a common factor. All are equality cases of P, $\nu = 2\deg + |\Pi|$. In degree 11 only the flats occur.

**Corollary 4.1. [checked: follows from the table, from the runs at $n = 8, 16$ and from note 17 Lemma 4.1]** Conjecture P holds on generic subspaces of dimension $N \le 5$, for every $\xi$ over every field. (For $2\delta + 2 > n$ there is nothing to check, and P follows from P$_0$ in dimensions up to $N$.)

*Rigor.* The absence of solutions is exact. That a singular configuration has a periodic solution was decided for the random basis. If the generic solution of such a configuration had no period, its specialization would have none either unless the basis is a root of a nonzero polynomial of bounded degree (a few thousand at most, by the degrees of the determinants involved), which for a random basis in $\mathrm{GF}(2^{64})$ has probability below $2^{-50}$, and the two seeds agree. I label the corollary checked, not proved.

## 5. Primitive lists: what P gives for lists

### 5.1 A primitive triple obeys the generic count

The statements of this section are implications from a hypothesis on aperiodic functions, and hold on every subspace domain $D$ of every field on which the hypothesis holds. Level problems are those of note 37 Definition 3.1: $U \le D$, $D' = L_U(D)$, members $P(L_U(X))$ with $\deg P \le \kappa$, a word $v : D \to F \cup \{\bot\}$, agreement at least $a$. Put $K = |U|\kappa$ and $n_e = \#\{x : v(x) \ne \bot\}$. The ordinary problem is $U = 0$, $K = k - 1$, $n_e = n$.

**Hypothesis wP$(D, U, E)$.** Every nonconstant $\xi \in F'(Y)$, $F' \supseteq F$, without period in $D' \setminus 0$ has $|U|\,\nu_{D'}(\xi) \le |U|(2\deg\xi + 1) + E$.

For a generic $D$, P$_0$ in dimension $N - \dim U$ is wP$(D, U, 0)$ ($D'$ is generic, note 17 Lemma 4.1). wP with $E = \epsilon n$ says: an excess above $\epsilon|D'|$ forces one nonzero period. Nothing is asked about the size of the period group.

**Lemma 5.1 (a primitive triple). [proved from the hypothesis]** Assume wP$(D, U, E)$. Let $P_0, P_1, P_2$ be three members of a level problem whose triple function is not constant and has no period in $D' \setminus 0$, and $S_i'$ any subsets of their agreement sets, $p_{ij} = |S_i' \cap S_j'|$, $t = |S_0' \cap S_1' \cap S_2'|$. Then
$$p_{01} + p_{02} + p_{12} \ \le\ 2K + |U| + E + t .$$
For the ordinary problem under P$_0$: $p_{01} + p_{02} + p_{12} \le 2k - 1 + t$.

*Proof.* Let $G' = \gcd(P_1 - P_0, P_2 - P_0)$ in $F[Y]$, $\gamma' = \deg G'$, $\gamma_D'$ the number of its roots in $D'$, and $\xi$ the triple function, of degree $\delta' \le \kappa - \gamma'$. A point $x$ with $G'(L_U(x)) \ne 0$ lies in at most two of the sets, and in two only if $\xi(L_U(x)) \in \{0, 1, \infty\}$ (note 17 Theorem 2.1). So the number of points in at least two sets is at most $|U|\nu_{D'}(\xi) + |U|\gamma_D'$, and $t \le |U|\gamma_D'$. Hence $\sum p_{ij} = \#\{\ge 2\} + 2t \le |U|(2\delta' + 1) + E + |U|\gamma_D' + 2t \le |U|(2\kappa + 1) + E - |U|\gamma_D' + 2t \le 2K + |U| + E + t$. $\square$

For generic points this is the three-member case of the generalized Singleton bound in inclusion-exclusion form. On a subspace it holds for the triples that are not bad, which is exactly how the descent of note 39 splits a list.

### 5.2 The three-wise Johnson bound

**Lemma 5.2. [proved]** Let $S_1, \dots, S_M$ be subsets of size $a$ of a set of $n_e$ points, $M \ge 3$, such that every triple satisfies $p_{ij} + p_{il} + p_{jl} - t_{ijl} \le c$. Put $h_M(d) = (M - 2)\binom d2 - \binom d3$ and let $\hat h_M$ be its piecewise linear interpolation at the integers. Then
$$n_e\,\hat h_M\!\Bigl(\frac{Ma}{n_e}\Bigr) \ \le\ \binom M3\,c . \tag{3}$$
With $\alpha = a/n_e$, $\varrho = c/2n_e$, $\mathcal{A} = \alpha^2(3 - \alpha) - 2\varrho$, $\mathcal{B} = 3(\alpha + \alpha^2 - 2\varrho)$: if $\mathcal{A} > 0$ and $\alpha \ge \varrho$ then
$$M \ \le\ \max\Bigl(\frac{1}{1 - \alpha},\ \frac{\mathcal{B}}{\mathcal{A}}\Bigr) .$$

*Proof.* Let $d_x$ be the number of sets containing $x$. Each pair lies in $M - 2$ triples, so the sum of the left sides over all triples is $(M - 2)\sum_x\binom{d_x}{2} - \sum_x\binom{d_x}{3} = \sum_x h_M(d_x)$. The second difference of $h_M$ at $d$ is $M - 1 - d \ge 0$ for $1 \le d \le M - 1$, so $\hat h_M$ is convex on $[0, M]$ and Jensen gives $\sum_x h_M(d_x) \ge n_e\hat h_M(\bar d)$ with $\bar d = Ma/n_e$. This is (3). As a real function $h_M(d) = d(d-1)(3M - 4 - d)/6$ has $h_M'' = M - 1 - d$, so it is convex on $[0, M - 1]$ and $\hat h_M \ge h_M$ there. If $M\alpha \le M - 1$, (3) gives $\alpha(M\alpha - 1)((3 - \alpha)M - 4) \le 2\varrho(M - 1)(M - 2)$, that is $\mathcal{A}M^2 - \mathcal{B}M + 4(\alpha - \varrho) \le 0$, and $M \le \mathcal{B}/\mathcal{A}$. Otherwise $M < 1/(1 - \alpha)$. $\square$

For $M = 3$, (3) is $3a - n_e \le c$, the three-member bound itself. For $M \to \infty$ it is $\alpha^2(3 - \alpha) \le 2\varrho$. With $c = 2k - 1$ and $n_e = n$ the threshold is
$$\tau_3(\rho):\qquad \tau^2(3 - \tau) = 2\rho, \qquad \rho < \tau_3(\rho) < \sqrt\rho ,$$
the second inequality because $\rho(3 - \sqrt\rho) > 2\rho$. This is the analogue for three sets of the Johnson bound (pairs: $\alpha^2 \le \varrho$), and both are the cases $m = 2, 3$ of $m\tau - 1 + (1 - \tau)^m = (m - 1)\rho$.

**[checked]** `44_pl_bound.py check`: the second differences for $M < 60$, the identity $\sum_{\text{triples}} = \sum_x h_M(d_x)$ and the Jensen step on 300 random set systems.

**Remark 5.3 (three members cannot do better). [proved]** Let $\alpha < \tau_3(\rho)$ and $\eta > 0$ small. Choose $M = e^{\eta^2 n/8}$ subsets of an $n$-set by taking each point independently with probability $\alpha$. With positive probability every set has at least $(\alpha - \eta)n$ points, every pair meets in at most $(\alpha^2 + \eta)n$ points, and every triple has $\sum p - t \le (3\alpha^2 - \alpha^3 + 4\eta)n$ (Hoeffding, and the union bound over fewer than $3M^3$ events of probability at most $e^{-2\eta^2 n}$; a point contributes 0, 1 or 2 to $\sum p - t$, with mean $3\alpha^2 - \alpha^3$). Since $\alpha^2 < \rho$ and $3\alpha^2 - \alpha^3 < 2\rho$, for $\eta$ small and $n$ large every three of these sets satisfy the criterion of note 17 Proposition 4.2 with $\Pi = 0$, $Z = \emptyset$, $\delta_0 = k - 1 - |B|$ (its conditions are $p_{ij} \le k - 1$ and $\sum p - t \le 2k - 1$), whose "if" direction is proved on every subspace domain: **every three of the sets are the agreement sets of three codewords of degree $< k$ for a suitable word.** So below $\tau_3(\rho)$ there are exponentially large families of sets of density $\alpha$ that are consistent three by three, on every subspace domain. No argument that looks at three members at a time, P in full included, can bound lists below $\tau_3$, and the brief's question "does primitivity force the generalized Singleton count" has the answer no (note 39 has examples: 133 against 7 at $(k, T) = (17, 19)$, $n = 32$, where $\tau = 0.594 < \tau_3$). What P gives is a bound on primitive lists above $\tau_3$.

### 5.3 The levels

The descent of note 37 Proposition 3.3 changes $(a, K, n_e)$: the agreement $a$ and the degree bound $K$ do not increase, the slack $a - K$ does not decrease, and the points where the word becomes undefined contain the lost agreements, so $n_e - a$ does not increase.

**Lemma 5.4 (the class of reachable problems). [proved]** Let $\mathcal{C} = \mathcal{C}(T, k)$ be the class of level problems with $a \le T$, $a - K \ge \Delta = T - k + 1$ and $n_e - a \le t_0 := n - T$.

1. $\mathcal{C}$ contains the ordinary problem at agreement $T$ ($a = T$, $K = k - 1$, $n_e = n$), and for every list of a problem of $\mathcal{C}$ at level $j$ and every pair of its members, each set $M_{a'}$ of note 37 Proposition 3.3 injects into a list of a problem of $\mathcal{C}$ at level $j + 1$.
2. The ordinary problem is the worst one for Lemma 5.2: if (3) fails for some $M$ with $(a, n_e, c) = (T, n, 2(k - 1) + c_0)$, it fails for the same $M$ with $(a, n_e, 2K + c_0)$ for every $(a, K, n_e)$ of the class.

*Proof.* (1) In Proposition 3.3, $K' = 2|U|\kappa' \le K - |U|\deg\varrho$, $a' = a - z_0$ with $z_0$ the number of agreement points of $P_0$ at which $\varrho(L_U(x)) = 0$, and the new word is undefined, in addition, exactly at the defined points with $\varrho(L_U(x)) = 0$, of which there are at least $z_0$ and at most $|U|\deg\varrho$. So $a' \le a$, $a' - K' \ge a - K$ and $n_e' - a' \le n_e - a$. (2) Let $\Phi(a, K, n_e) = n_e\hat h_M(Ma/n_e) - \binom M3(2K + c_0)$, so that (3) fails iff $\Phi > 0$. $\Phi$ decreases with $K$. It does not increase with $n_e$: $\partial_{n_e}\bigl(n_e\hat h_M(Ma/n_e)\bigr) = \hat h_M(\bar d) - \bar d\,\hat h_M'(\bar d) \le \hat h_M(0) = 0$ by convexity. So $\Phi(a, K, n_e) \ge \Phi(a, a - \Delta, a + t_0) =: \phi(a)$. Along this line $\bar d = Ma/(a + t_0)$, $d\bar d/da = (M - \bar d)/(a + t_0)$, and
$$\phi'(a) = \hat h_M(\bar d) + (M - \bar d)\,\hat h_M'(\bar d) - 2\tbinom M3 \ \le\ \hat h_M(M) - 2\tbinom M3 = 0,$$
again by convexity, and because $h_M(M) = (M - 2)\binom M2 - \binom M3 = 2\binom M3$. So $\phi(a) \ge \phi(T)$ for $a \le T$. (Derivatives are one-sided at the integers.) $\square$

So the levels cost nothing in the threshold: a problem reached by the descent is a pinned version of the ordinary one or better, and pinning helps. **[checked]** `44_pl_bound.py check`: on $7200$ random points of the class at $N = 12, 14$ and on a grid along the extreme line at $N = 25, 28$ the largest $M$ satisfying (3) is never larger than at the ordinary problem.

### 5.4 P implies PL and a list bound

**Theorem 5.5. [proved conditional on the hypothesis]** Let $D$ be a subspace domain of dimension $N$, $k < T$, $\Delta = T - k + 1$, $1 \le j_0 \le N - 1$ and $E \ge 0$. Assume wP$(D, U, E)$ for every subspace $U \le D$ of dimension less than $j_0$. Let $f \ge 2$ be such that (3) fails for every $M > f$ at $(a, n_e, c) = (T, n, 2(k - 1) + 2^{j_0 - 1} + E)$; such an $f$ exists as soon as $\tau^2(3 - \tau) > (2k - 2 + 2^{j_0 - 1} + E)/n$. Then primitive lists of the problems of the class $\mathcal{C}(T, k)$ at the levels $j < j_0$ have at most $f$ members, and every word on $D$ has at most
$$\binom{f + 1}{3}^{j_0}\ 2^{Nj_0 - j_0(j_0 - 1)/2}\ \Bigl(\bigl(\tfrac n\Delta\bigr)^{\kappa_0 + 1} + 1\Bigr), \qquad \kappa_0 = \Bigl\lfloor\frac{k - 1}{2^{j_0}}\Bigr\rfloor,$$
codewords of degree $< k$ at agreement $T$, with any number of lanes. For a generic $D$ the hypothesis with $E = 0$ is Conjecture P$_0$ in the dimensions $N - j_0 < N' \le N$.

*Proof.* A primitive list of a problem of the class at level $j$ has all its triples as in Lemma 5.1. Cut its agreement sets down to size $a$: (3) holds for its number of members $M$ with $c = 2K + 2^j + E \le 2K + 2^{j_0 - 1} + E$, so by Lemma 5.4 (2) it holds at the ordinary problem with $c_0 = 2^{j_0 - 1} + E$, and $M \le f$. Now the proof of note 39 Theorem 1.3 runs inside the class: let $\alpha_j$ be the largest list of a problem of the class at level $j$. A list with $L > f$ members has no primitive sublist of $f + 1$ members, so by the supersaturation lemma (note 39 Lemma 1.2) some pair has at least $(L - 2)/\binom{f+1}{3}$ bad thirds, each bad third lies in some $M_{a'}$, $a' \in (D/U) \setminus 0$, and $|M_{a'}| \le \alpha_{j+1}$ by Lemma 5.4. So $\alpha_j \le f + \binom{f+1}{3}2^{N-j}\alpha_{j+1}$, and unrolling as in note 39 gives the factor in front of $\alpha_{j_0} + 1$. At level $j_0$ the members have degree at most $\kappa_0$ in $L_U$ and slack at least $\Delta$, so $\alpha_{j_0} \le (n/\Delta)^{\kappa_0 + 1}$ (note 37 Lemma 3.2). Lanes: note 12 Proposition 1.1. $\square$

**Numbers. [proved conditional on P; evaluated by `44_pl_bound.py` with exact integers in (3)]** $E = 0$, $k = \rho n$, $T = \lfloor\tau n\rfloor + 1$. $f_0$ is the largest $M$ satisfying (3) for ordinary lists ($c = 2k - 1$), $f$ the value of the theorem (the largest $M$ satisfying (3) with $c = 2k - 2 + 2^{j_0 - 1}$; all larger $M$ fail, by the closed form of Lemma 5.2 beyond $\max(\mathcal{B}/\mathcal{A}, 1/(1 - \alpha)) + 2$ and by direct evaluation below), and $j_0$ minimizes the bound.

| rate | $\tau_3$ | Johnson | $\tau$ | $f_0$ | $f$ | $j_0$, $\kappa_0$ | bound, $N = 25$ | bound, $N = 28$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | 0.6527 | 0.7071 | 0.655 | 38 | 107 | 18, 63 | $2^{788}$ | $2^{922}$ |
| | | | 0.66 | 11 | 19 | 19, 31 | $2^{583}$ | $2^{694}$ |
| | | | 0.665 | 6 | 12 | 20, 15 | $2^{516}$ | $2^{621}$ |
| 1/4 | 0.4421 | 0.5 | 0.45 | 25 | 33 | 18, 31 | $2^{598}$ | $2^{717}$ |
| | | | 0.46 | 11 | 13 | 19, 15 | $2^{503}$ | $2^{609}$ |
| | | | 0.48 | 4 | 5 | 19, 15 | $2^{421}$ | $2^{515}$ |
| 1/8 | 0.3045 | 0.3536 | 0.31 | 52 | 68 | 17, 31 | $2^{634}$ | $2^{762}$ |
| | | | 0.32 | 19 | 22 | 18, 15 | $2^{530}$ | $2^{643}$ |
| | | | 0.34 | 8 | 9 | 19, 7 | $2^{454}$ | $2^{556}$ |
| 1/16 | 0.2117 | 0.25 | 0.216 | 81 | 102 | 16, 31 | $2^{646}$ | $2^{780}$ |
| | | | 0.22 | 42 | 53 | 17, 15 | $2^{581}$ | $2^{706}$ |
| | | | 0.23 | 19 | 22 | 17, 15 | $2^{515}$ | $2^{628}$ |

(The values of $f$, $j_0$ and $\kappa_0$ are those at $N = 25$. At $N = 28$ the optimal $j_0$ is larger by 3 with the same $f$ and $\kappa_0$, except in the row $(1/2, 0.665)$, where $j_0 = 22$, $\kappa_0 = 31$, $f = 9$.) For $3T \ge n + 2k - 1 + 2^{j_0 - 1}$ there are no primitive triples at any level, $f = 2$, and for $3T \ge n + 2k$ note 17 Theorem 5.1 gives polynomial bounds directly from P. The new range is $\tau_3 < \tau < (1 + 2\rho)/3$, which at rates $1/4, 1/8, 1/16$ is the whole stretch between $\tau_3$ and the Johnson radius. The shape $2^{N^2/2 + O(N)} = n^{O(\log n)}$ cannot be improved in general on subspace domains: on $D = \mathbb{F}_{2^N}$ the lists at rate 1/4 are $n^{\Omega(\log n)}$ for every fixed $\tau < 1/2$ (note 43, quoting [DKTZ26]), so on a field domain either wP fails or the bound of the theorem has the true order.

**Consistency with the small cases. [checked]** At $n = 16$ and $n = 32$ the hypothesis is Corollary 4.1, so Lemma 5.2 applies to ordinary lists there. On 16 points it gives at most $3, 4, 6, 10$ members for a primitive list at $(k, T) = (3, 7), (6, 9), (9, 11), (12, 13)$ and nothing at $(8, 10)$, where $\tau < \tau_3$. This agrees with the classification of note 27: its only class of four-member lists at $(3, 7)$ is a lift (every triple is bad), and its four-member lists without any period occur at $(9, 11)$, $(12, 13)$ and $(8, 10)$. At $(7, 10)$, $(5, 9)$, $(6, 10)$ on 16 points no primitive triple can exist, and all list triples of note 17 section 2.3 at these points are periodic. On 32 points: at most 5 members at $(16, 21)$ (the list of 16 members of note 39 section 4.4 has no primitive triple) and nothing at $(17, 19)$, where note 39 has primitive sublists of 133 members.

**Remark 5.6 (the hypothesis that is needed). [proved]** With $E = \epsilon n$ the theorem needs only: on the quotients $D/U$, a function with $\nu \ge 2\delta + 2 + \epsilon|D/U|$ has a nonzero period. The threshold moves from $\tau_3(\rho)$ to $\tau_3(\rho + \epsilon/2)$. This is weaker than P and than the weak form of note 17 section 6.1 (which asks for a period group of size proportional to the excess), and it concerns only functions with a positive density of points in their fibres, in dimensions $N' > N - j_0$, that is, large.

**Remark 5.7 (more members). [the counting proved, the hypotheses not formulated]** The same Jensen argument with $m$-wise counts has the threshold $m\tau - 1 + (1 - \tau)^m = (m - 1)\rho$: at rate 1/2, $0.6198$ for $m = 4$ (below $5/8$) and $0.5979$ for $m = 5$; at rates $1/4, 1/8, 1/16$: $0.4065, 0.2745, 0.1884$ for $m = 4$. What is missing for $m = 4$ is twofold: the four-member statement (Conjecture Q of note 27, whose exceptional configurations include periods of the cross-ratio functions and a sporadic excess of 2), and a descent for the exceptional quadruples that are not explained by a bad triple.

## 6. Status, answers to the brief, and what remains

**1. Is P true in the formal model?** Not decided. Proved here: one simple root outside $D$ in two of the fibres (Theorem 3.2, Corollary 3.3), roots in general position (Proposition 1.2), $\nu \ge 3\delta - 2$, and $\delta \le 4$ without computer. Checked here: every degree at $n = 32$, so P in dimension at most 5. Refuted here: the mechanism of the brief (Example 2.3). Exactly what remains: functions with at least two phantom roots, algebraic over $\mathbb{F}_2(b)$, in each pair of fibres. In the form of section 2: the solutions of $\sum_{y \in Y}\varrho_y = 0$ with $r + 2 \ge 4$ terms. The data of section 3.5 show that already for $r = 2$ these have solutions that do not fit the additive mechanism, with fibres of 4 and 6 points, and that P survives there through the imbalance of the degrees. A proof for $r$ of order $n$ needs an idea that is not in this note. The predictions tested on exhaustive data: Theorem 3.2 (fibre at most 3, the three families at $n = 16$ with their exact counts), P in degrees 8 to 11 at $n = 32$ (in particular no aperiodic solution among the patterns of sizes $(\delta, \delta - 1, \cdot)$, as Corollary 3.3 says), and the exact numbers of singular configurations in degrees 11 and 14.

**2. PL.** Under P (in fact under wP with a small linear excess): PL$(f)$ holds for $\tau > \tau_3(\rho)$ with $f \approx 3(\tau + \tau^2 - 2\rho)/(\tau^2(3 - \tau) - 2\rho)$ at level 0 and the values of the table at all levels. Primitivity does not force the generalized Singleton count (note 39, and Remark 5.3 in principle). Below $\tau_3$, P gives nothing for lists. The values of $f$ are far below the $2^{10}$ that the reduction can afford.

**3. Through the reduction of note 39.** Windows $(\tau_3(\rho), \sqrt\rho)$: $(0.6527, 0.7071)$, $(0.4421, 0.5)$, $(0.3045, 0.3536)$, $(0.2117, 0.25)$. List bounds $2^{420}$ to $2^{790}$ at $N = 25$ and $2^{515}$ to $2^{922}$ at $N = 28$, for all words and any number of lanes, conditional on P in the formal model. On every subspace domain: Lemma 5.2, Lemma 5.4 and Theorem 5.5 hold as implications, with the hypothesis wP on that domain and its quotients; Proposition 2.1, Theorem 3.2 and section 4 are statements about the formal model only (they use unique factorization in $\mathbb{F}_2[b]$). On the real domain wP is not known and P is false at small depth for the usual reasons; whether wP with a linear excess holds there at depth of order $n$ is the usual open question.

**What remains, in order of use.**

1. wP for dense functions: on a generic subspace of large dimension, $\nu \ge 2\delta + \epsilon n$ implies one nonzero period. By Lemma 1.1 such a function is defined over $\mathbb{F}_2(b)$ and homogeneous, and in the cases that lists produce it has of the order of $n$ phantom roots in each fibre.
2. An unconditional substitute. With the gap theorem of note 37 ($\nu \le 3\delta - \delta^2/4n$ for functions that are not flats) in place of P, Lemma 5.1 becomes $\sum p \le 3K - (K - t)^2/4n$ and the counting of Lemma 5.2 gives a contradiction only within about $10^{-3}$ of the Johnson radius at rate 1/2 **[heuristic estimate with the extremal two-point distribution of the degrees, not proved, and not carried through the levels]**. That would widen the window of note 37 Theorem 5.1 a hundredfold and is still useless for parameters. What would count: a theorem $\nu \le c\,\delta + o(n)$ for aperiodic functions with a constant $2 \le c < 3$ gives $\sum p \le cK + (3 - c)t$ in Lemma 5.1, the function $(M - 2)\binom d2 - (3 - c)\binom d3$ is again convex, and the threshold becomes the root of $3\tau^2 - (3 - c)\tau^3 = c\rho$ ($0.686$ at rate 1/2 for $c = 5/2$) **[proved by the same counting]**.
3. Four members (Remark 5.7), for the part of the windows below $\tau_3$, which at rate 1/2 is $(5/8, 0.6527]$.
4. The classification of the four-term identities of section 3.5.

## 7. Reproduction

Under `doc/whir_soundness_gap_notes/scripts/`, C with the system compiler, `02_gf.h` for the field ($\mathrm{GF}(2^{64})$ with the leanVM modulus, random basis from a fixed xorshift seed). Times on one core of an Apple M4 Max.

- `44_n32.c`: `cc -O2 -o 44_n32 44_n32.c`, `./44_n32 N delta part parts [seed]`. Validation: `./44_n32 3 d 0 1` for $d = 2, 3$ and `./44_n32 4 d 0 1` for $d = 2, \dots, 7$ (instant). Section 4: `./44_n32 5 d 0 1` for $d = 2, \dots, 15$: under 2 s up to $d = 7$, then 11 s, 34 s, 94 s, 180 s, 193 s, 195 s, 224 s, 261 s for $d = 8, \dots, 15$ (for $d \ge 13$ most of it is the orbit enumeration; up to 0.6 GB of memory at $d \ge 14$). `./44_n32 5 d 0 1 2` for the second seed. `part parts` splits the representatives over processes.
- `44_onephantom.c`: `cc -O2 -o 44_onephantom 44_onephantom.c`, `./44_onephantom 4 1`, `./44_onephantom 3 3`, `./44_onephantom 3 7` (under a second each).
- `44_twophantom.c`: `cc -O2 -o 44_twophantom 44_twophantom.c`, `./44_twophantom [seed]` (one second).
- `44_pl_bound.py`: `python3 44_pl_bound.py check` (the checks of Lemma 5.2 and of the class maximum) and `python3 44_pl_bound.py` (thresholds and the table of section 5.4, 7 s).

## References

Notes 12 (Proposition 1.1), 17 (Theorem 2.1, Lemma 4.1, Conjecture P, Theorem 5.1), 26 (Lemma 1.2, Theorem A, Lemma 2.2, sections 5.3 and 6), 27 (Conjecture Q), 30 (Lemmas 4.1, 7.1, section 6.1), 37 (Definition 3.1, Lemma 3.2, Proposition 3.3, Lemma 4.1, Theorem 4.3, Theorem 5.1), 39 (Lemma 1.2, Theorem 1.3, Conjecture PL, section 4) and 43 (the Gold lists on field domains) of this directory. No external source was used.
