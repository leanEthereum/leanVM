# 26. Conjecture P: unique factorization, a reduction to bounded dimension, and the dense end at $n = 32$

Researcher 26. Starting point: note 17, which is not repeated. Every statement is tagged **[proved]** (proof here), **[quoted]**, **[checked]** (numerically, sizes stated) or **[conjectured]**. The program is `scripts/26_search.c`, section 8 says how to run it.

Notation as in note 17. $F$ has characteristic two, $D \subset F$ is a generic $\mathbb{F}_2$-subspace of dimension $N$ (a basis $b_1, \dots, b_N$ algebraically independent over $\mathbb{F}_2$), $n = 2^N$, $K = \mathbb{F}_2(b)$. For nonconstant $\xi \in F(X)$ of degree $\delta$: $\xi = u_0/u_1$ with $u_0 + u_1 + u_2 = 0$ pairwise coprime, $R_i$ the set of roots of $u_i$ in $D$ (the fibres over $0, \infty, 1$), $r_i = |R_i| \le \delta$, $R = R_0 \sqcup R_1 \sqcup R_2$, $\nu = |R|$, $e = \nu - 2\delta - 1$ the excess, $\Pi(\xi)$ the group of periods in $D$. $Z_S = \prod_{s \in S}(X - s)$. **P**: $\nu \le 2\delta + |\Pi|$. **P$_0$**: $\Pi = 0 \Rightarrow \nu \le 2\delta + 1$. P in all dimensions $\le N$ is equivalent to P$_0$ in all dimensions $\le N$ (note 17 Lemma 4.1). "P holds in dimension $N$" means: for every field, every generic $D$ of dimension $N$ and every $\xi$.

## 0. Summary

**Headline.** P is neither proved nor refuted. It is proved in three new regimes (two fibres inside $D$; degree at most 4; dimension large against the degree, by an induction that needs P one dimension lower), it is verified exhaustively at the dense end of $n = 32$ (degrees 12 to 15, the regime that the list bound of note 17 uses), and the obstruction to a full proof is reduced to one precise missing step (section 5). No counterexample was found anywhere.

| | statement | status |
| --- | --- | --- |
| 1.1 | $\nu(\xi)$ is the number of points of $D$ that $\xi$ maps into $\mathbb{P}^1(\mathbb{F}_2)$ | proved (trivial) |
| A (2.1) | **Split functions.** If all zeros and poles of $\xi$ lie in $D \cup \{\infty\}$, then for every $c \ne 0, \infty$ the set $\{x \in D : \xi(x) = c\}$ is empty or exactly one coset of $\Pi(\xi)$. Hence P holds for every $\xi$ with two of its three fibres inside $D \cup \{\infty\}$, on every generic $D$, over every field | proved |
| 2.2 | Consequences: P holds whenever $\nu \ge 3\delta - 1$; $\nu = 3\delta$ forces $\xi = \mu \circ L_\Pi$ with $\deg \mu = 1$; **P holds for $\delta \le 3$ in every dimension**, without computer | proved |
| 2.3 | Three-term identities: products of $\mathbb{F}_2$-linear forms with $T_1 + T_2 + T_3 = 0$ and no common factor are exactly $T_i = L_H(\ell_i)^{2^j}$, $\ell_1 + \ell_2 + \ell_3 \in H$ | proved |
| 2.4 | One fibre inside $D$ ($r_0 = \delta$): every difference $y + z$, $y \in R_1$, $z \in R_2$, occurs at least $e + 1$ times, so $\lvert R_1 + R_2\rvert \le r_1 r_2/(e+1)$ and the stabilizer $H$ of $R_1 + R_2$ has $\lvert H\rvert \ge r_1 + r_2 - r_1 r_2/(e+1)$. Whether $H \le \Pi(\xi)$ is open | proved |
| B (3.1) | **Reduction to bounded dimension.** If P holds in dimension $N - 1$ and $\xi$ on a generic $D$ of dimension $N$ has no period and $2\delta + 2$ points $R$ in its fibres, then $D \subseteq R + R + R + R$. So P$_0$ holds in dimension $N$ for degree $\delta$ as soon as $2^N > 1 + \binom{2\delta+2}{2} + \binom{2\delta+2}{4}$ | proved |
| 3.2 | Same hypothesis: the affine span of $R$ has dimension at most $\delta + 2$ | proved |
| 3.3 | For each degree P is a finite problem: a counterexample of least dimension has $N \le \min(\delta + 2, \log_2(1 + \binom{2\delta+2}{2} + \binom{2\delta+2}{4}))$ | proved |
| 3.4 | **P holds for $\delta \le 4$ in every dimension** | proved from 3.2 plus an exhaustive computation in dimensions 4, 5, 6 ($1.7 \cdot 10^8$ configurations) |
| C (4.1) | Strengthening of note 17 Theorem 3.2: with $\sigma_\varepsilon$ the substitution $z \mapsto z + \varepsilon z^2$ on $b_1, \dots, b_N, X$, $\sigma_\varepsilon(\xi) \equiv \xi \bmod \varepsilon^{e+2}$. All zeros, poles and ones of $\xi$ outside $D$ move like points of $D$ to order $e + 1$ | proved |
| 5.1 | P$_{\mathrm{mult}}$: $\sum_{x \in D}\mathrm{mult}_x(\xi) \le 2\delta + q\lvert\Pi\rvert$, $q$ the inseparability degree | conjectured. Exhaustive: $n = 8$, $\delta \le 6$; $n = 16$, $\delta \le 3$; 0 violations |
| 5.2 | Induction skeleton: under P$_{\mathrm{mult}}$ in dimension $N - 1$, a violation in dimension $N$ has a degenerate reduction (constant, inseparable or periodic) in every direction $a \ne 0$ | proved |
| 6 | Exhaustive at $n = 32$: degree 15 ($6.0 \cdot 10^8$ configurations, no solution), degree 14 ($8.4 \cdot 10^8$), degree 13 ($1.6 \cdot 10^9$), degree 12 ($2.4 \cdot 10^9$): every solution periodic, 0 violations. With note 17 (degrees $\le 7$): open at $n = 32$ are degrees 8 to 11 | checked |

**What it means for the conditional list bound (note 17 Theorem 5.1).** Nothing unconditional. The triples that Theorem 5.1 needs have $\delta$ of order $n$ and $R$ of positive density, where $R + R + R + R = D$ and where the fibres are not inside $D$ in general, so neither B nor A applies. The bound stays conditional on P, or on its weak form. What changed is the evidence and the shape of the gap: P is now verified at $n = 32$ in exactly the dense regime of Theorem 5.1 (degrees 12 to 15, where $R$ is all of $D$ up to at most 6 points), and the missing step is isolated (section 5.3): find one direction $a$ in which the reduction of $\xi$ is not degenerate, when every direction carries pairs of $R$.

## 1. A reformulation

**Lemma 1.1. [proved]** $\xi(x) \in \{0, 1, \infty\}$ iff $\xi(x) \in \mathbb{P}^1(\mathbb{F}_2)$ iff $u_0 u_1 (u_0 + u_1)$ vanishes at $x$. So $\nu(\xi) = \#\{x \in D : \xi(x) \in \mathbb{P}^1(\mathbb{F}_2)\}$, the symmetry group $S_3$ of the three values is $\mathrm{PGL}_2(\mathbb{F}_2)$, and the three polynomials are the nonzero elements of the $\mathbb{F}_2$-plane $\{0, u_0, u_1, u_2\} \subset F[X]$.

P says: a rational function of degree $\delta$ maps at most $2\delta + |\Pi|$ points of a generic $\mathbb{F}_2$-subspace to $\mathbb{F}_2$-rational points. For $x \in R$ the value $\xi(x)$ is a constant of every derivation and of every endomorphism of the generic model. Note 17 Lemma 3.1 is this statement for derivations, Theorem C below for one family of endomorphisms.

**Lemma 1.2 (uniqueness). [proved]** Let $(u_i)$ and $(u_i')$ be two triples with $\sum_i u_i = \sum_i u_i' = 0$, degrees at most $\delta$ and $\delta'$, such that $u_i$ and $u_i'$ vanish on $R_i$ for $i = 0, 1, 2$ (with multiplicities $m_x$ if a pattern with multiplicities is prescribed). If $\sum_x m_x > \delta + \delta'$ then $u_0 u_1' = u_1 u_0'$. In particular for a pattern with $|R| = 2\delta + 2$ and all $r_i \le \delta$, all solutions of degree at most $\delta$ are multiples $Q \cdot (v_0, v_1, v_2)$ of one coprime triple: the reduced function $\xi$ of a configuration is unique.

*Proof.* $\Omega = u_0 u_1' + u_1 u_0'$ has degree at most $\delta + \delta'$, and $\Omega = u_0 u_2' + u_2 u_0' = u_1 u_2' + u_2 u_1'$, so it vanishes on all three $R_i$. With $r_i \le \delta$ and $|R| = 2\delta + 2$ no component of a nonzero solution is zero (if $u_0 = 0$ then $u_1 = u_2$ has $r_1 + r_2 \ge \delta + 2$ roots). $\square$

This is what makes every exhaustive check below (and in note 17) rigorous: analysing one solution of a singular configuration analyses all of them.

## 2. Unique factorization

$\mathbb{F}_2[b_1, \dots, b_N]$ is a unique factorization domain whose only unit is 1, and the $n - 1$ nonzero elements of $D$ are pairwise non-associate primes of it. Note 17 uses derivations and valuations of $K$. It does not use this, and it is what makes the generic model rigid.

### 2.1 Split functions

**Theorem A. [proved]** Let $D$ be generic and $\xi = c \prod_{x \in D}(X - x)^{m(x)}$ with $c \in F^\times$ and $m : D \to \mathbb{Z}$ not identically zero (the divisor of $\xi$ is supported on $D \cup \{\infty\}$). If $y_1 \ne y_2$ are points of $D$ with $m(y_1) = m(y_2) = 0$ and $\xi(y_1) = \xi(y_2)$, then $y_1 + y_2 \in \Pi(\xi)$. Consequently every fibre $\{x \in D : \xi(x) = c'\}$, $c' \ne 0, \infty$, is empty or one coset of $\Pi(\xi)$, and
$$\nu(\xi) \ \le\ r_0 + r_1 + |\Pi(\xi)| \ \le\ 2\delta + |\Pi(\xi)| .$$

*Proof.* $\prod_x (y_1 + x)^{m(x)} = \prod_x (y_2 + x)^{m(x)}$ is an identity in $K$ between products of nonzero elements of $D$ (no factor vanishes because $m(y_1) = m(y_2) = 0$). By unique factorization the exponent of each prime $z \in D \setminus 0$ is the same on both sides: $m(y_1 + z) = m(y_2 + z)$ for all $z \ne 0$. With $a = y_1 + y_2$ this says $m(x) = m(x + a)$ for all $x \ne y_1, y_2$, and $m(y_1) = m(y_2)$ holds too. So the divisor is invariant under $a$, and $\xi(X + a) = c\prod_x (X - x)^{m(x + a)} = \xi(X)$. The fibre over $c'$ is invariant under $\Pi$ and any two of its points differ by a period. $\square$

By the $S_3$ symmetry: **P holds for every $\xi$ such that two of its three fibres over $0, 1, \infty$ lie in $D \cup \{\infty\}$** (with any multiplicities). This contains the case "numerator and denominator split over $D$", in particular a split numerator over a subspace polynomial. The proof uses genericity only through unique factorization, and no induction.

### 2.2 Consequences

**Corollary 2.1. [proved]** (i) If $\nu(\xi) \ge 3\delta - 1$ then P holds for $\xi$. (ii) If $\nu(\xi) = 3\delta$ then $\xi = \mu \circ L_\Pi$ with $|\Pi| = \delta$ and $\mu$ of degree one: the equality case of the trivial bound is exactly the flats. (iii) P holds for all $\xi$ of degree at most 3, on generic subspaces of every dimension, over every field.

*Proof.* (i) $r_i \le \delta$ and $\sum r_i \ge 3\delta - 1$ force two fibres of size $\delta$, which are then complete and simple. (ii) All three fibres are complete, the fibre over 1 is one coset of $\Pi$, so $|\Pi| = \delta$ and $\xi = \xi_0 \circ L_\Pi$ with $\deg\xi_0 = 1$. (iii) A violation of P$_0$ has $\nu \ge 2\delta + 2$: impossible for $\delta = 1$, and for $\delta = 2, 3$ the sizes are $(2,2,2)$, $(3,3,2)$ or $(3,3,3)$, with two complete fibres. P follows from P$_0$ on the quotients, which have smaller degree. $\square$

### 2.3 Three-term identities

**Lemma 2.2. [proved]** Let $T_1, T_2, T_3$ be nonzero products of nonzero $\mathbb{F}_2$-linear forms in independent variables, with $T_1 + T_2 + T_3 = 0$ and no common factor. Then there are a subspace $H$ of the space of linear forms, forms $\ell_i \notin H$ with $\ell_1 + \ell_2 + \ell_3 \in H$, and $j \ge 0$ such that $T_i = L_H(\ell_i)^{2^j}$, where $L_H(\ell) = \prod_{h \in H}(\ell + h)$.

*Proof.* The $T_i$ are pairwise coprime and homogeneous of one degree $\ge 1$. Let $\Phi_i$ be the multiset of linear factors of $T_i$. For $\ell \in \Phi_3$ reduce modulo $\ell$: $\bar T_1 = \bar T_2 \ne 0$ in a polynomial ring in one variable less, where linear forms are again primes, so the images of $\Phi_1$ and $\Phi_2$ in the quotient by $\{0, \ell\}$ agree as multisets. Because $\Phi_1$ and $\Phi_2$ have disjoint supports, a class $\{m, m + \ell\}$ cannot contain elements of the same $\Phi_i$ twice, and $\Phi_2 = \Phi_1 + \ell$. So $\Phi_1$ is invariant under $\ell + \ell'$ for $\ell, \ell' \in \Phi_3$, hence under the group $H$ they generate, and so are $\Phi_2 = \Phi_1 + \ell$ and, by the symmetric statement, $\Phi_3$. The support of $\Phi_3$ lies in one coset of $H$ and is $H$-invariant, so it is that coset, with constant multiplicity $\mu$. Then $\Phi_2 = \Phi_3 + \ell_1$ and $\Phi_1 = \Phi_2 + \ell_3$ are cosets with the same multiplicity, $T_i = L_H(\ell_i)^\mu$, and $(A + B)^\mu = A^\mu + B^\mu$ for the coprime forms $A = L_H(\ell_1)$, $B = L_H(\ell_2)$ forces $\mu$ to be a power of two. $\square$

So over $\mathbb{F}_2$ the only three-term relations between products of linear forms are the additivity of subspace polynomials (the Plücker relation $(x_1 + x_2)(x_3 + x_4) + (x_1 + x_3)(x_2 + x_4) + (x_1 + x_4)(x_2 + x_3) = 0$ is the case $|H| = 2$). It gives Corollary 2.1 (ii) a second time. Its use beyond Theorem A: eliminating a cofactor of degree $a$ from $h_0 Z_{R_0} + h_1 Z_{R_1} + h_2 Z_{R_2} = 0$ by divided differences gives an identity with $a + 2$ terms, so P for cofactor degrees $(0, 0, \cdot)$ is a two-term identity (Theorem A), cofactor degrees $(0, \cdot, 1)$ give a three-term identity $\sum_{\mathrm{cyc}} Z_{R_0}(y_1) Z_{R_2}(y_2) Z_{R_2}(y_3)(y_2 + y_3) = 0$ for every three points $y_1, y_2, y_3$ of $R_1$ (already the fact that a common factor of two terms divides the third shows that $R_2$ meets every coset of the plane $\langle y_1 + y_2, y_1 + y_3\rangle$ in 0, 3 or 4 points, except the coset of the $y_i$, where it can contain only $y_1 + y_2 + y_3$), and the general case needs identities with about $\delta/3$ terms, for which I have no classification. **[the last sentence is a description, not a theorem]**

### 2.4 One fibre inside $D$

**Proposition 2.3. [proved]** Let $D$ be generic and $r_0 = \delta$ (so $u_0 = c\,Z_{R_0}$). Then for all $y \in R_1$, $z \in R_2$:
$$|R_1 \cap (R_2 + y + z)| \ \ge\ r_1 + r_2 - \delta = e + 1 .$$
Hence $|R_1 + R_2| \le r_1 r_2/(e + 1)$, and by Kneser's theorem **[quoted]** the stabilizer $H$ of $R_1 + R_2$ satisfies $|H| \ge r_1 + r_2 - |R_1 + R_2| \ge s - s^2/(4(e+1))$ with $s = \delta + 1 + e$, and $R_1, R_2$ are unions of cosets of $H$ up to at most $|R_1 + R_2| + |H| - s$ missing points in total. In particular $|H| > s/4$ as soon as $e + 1 > s/3$.

*Proof.* Normalize $c = 1$: $Z_{R_0} + h_1 Z_{R_1} + h_2 Z_{R_2} = 0$, $\deg h_i \le \delta - r_i$. Let $a = y + z$ and $w$ a place of $F$ above the $a$-adic place of $K$ (note 17, section 3.4). At $X = y$: $Z_{R_0}(y) = h_2(y) Z_{R_2}(y)$. $Z_{R_0}(y)$ is a product of elements of $D$ different from $0$ and $a$, a unit at $w$, and $Z_{R_2}(y)$ contains the factor $y + z = a$. So $w(h_2(y)) < 0$, the Gauss valuation of $h_2$ is negative, and after scaling the reduction of the triple is $(0, \bar h_1 \bar Z_{R_1}, \bar h_2 \bar Z_{R_2})$ with $\bar h_1 \bar Z_{R_1} = \bar h_2 \bar Z_{R_2} \ne 0$. The reductions $\bar Z_{R_1}$, $\bar Z_{R_2}$ have a common factor of degree $|R_1 \cap (R_2 + a)|$, and $\bar Z_{R_1}$ divided by it divides $\bar h_2$: $r_1 - |R_1 \cap (R_2 + a)| \le \delta - r_2$. $\square$

So with one complete fibre and positive excess no difference between the other two fibres is unique, and for $e \ge \delta/2$ the two other fibres are close to unions of cosets of a nonzero subgroup. I could not show that this subgroup consists of periods of $\xi$. In the language of section 2: for a coprime triple with coefficients in $\mathbb{F}_2[b, t]$ ($t$ free parameters) and $e \ge 0$, the content of each cofactor $h_l$ is a product of linear forms $a \in D$, each with $|R_i \cap (R_j + a)| \ge r_i + r_j - \delta$ (reduce modulo a prime $p$ of the content: $\bar h_i \bar Z_{R_i} = \bar h_j \bar Z_{R_j}$, and two points of $D$ coincide modulo $p$ only if $p$ is their sum). **[proved]** Proposition 2.3 says that with a complete fibre the content of its constant cofactor is divisible by every element of $R_1 + R_2$.

## 3. Reduction to bounded dimension

For $R \subseteq D$ let $4R = R + R + R + R$. It contains $0$ and $R + R$, and $|4R| \le B(\delta) := 1 + \binom{2\delta + 2}{2} + \binom{2\delta + 2}{4}$ when $|R| = 2\delta + 2$.

**Theorem B. [proved]** Let $N \ge 1$ and suppose P holds in dimension $N - 1$ for degrees at most $\delta$. Let $D$ be generic of dimension $N$ in $F$, $\xi \in F(X)$ of degree $\delta$ with $\Pi(\xi) = 0$, and $R$ a set of $2\delta + 2$ points of $D$ in the fibres of $\xi$ over $0, 1, \infty$. Then $D \subseteq 4R$. In particular, if $2^N > B(\delta)$ then $\nu(\xi) \le 2\delta + 1$.

*Proof.* Suppose $a \in D \setminus 4R$. Write $R_i$ for the part of $R$ in the $i$-th fibre, so $r_i \le \delta$ and $\sum r_i = 2\delta + 2$.

*Step 1, the reduction.* Choose a basis of $D$ ending with $a$, let $v$ be the $a$-adic valuation of $K$ (trivial on the field generated by the other basis elements) and $w$ an extension to $F$, with residue field $\kappa$. The image $\bar D$ of $D$ is a generic subspace of dimension $N - 1$ of $\kappa$, and $x \mapsto \bar x$ is injective on $R$ because $a \notin R + R$. Scale $(u_0, u_1, u_2)$ to least Gauss valuation 0 and reduce: $\bar u_0 + \bar u_1 + \bar u_2 = 0$, not all zero, degrees $\le \delta$, and $\bar Z_{R_i} \mid \bar u_i$ with $\bar Z_{R_i}$ having $r_i$ simple roots, the three root sets disjoint. No $\bar u_i$ is zero (if $\bar u_2 = 0$ then $\bar u_0 = \bar u_1$ has $r_0 + r_1 \ge \delta + 2$ roots). Let $\bar G = \gcd(\bar u_i)$, $g = \deg\bar G$, $v_i = \bar u_i/\bar G$, $\bar\delta = \max\deg v_i \le \delta - g$. The $v_i$ are not all constant (otherwise $\bar G$ has $2\delta + 2$ roots). So $\bar\xi = v_0/v_1$ is nonconstant of degree $\bar\delta$. Let $B \subseteq R$ be the set of points whose image is a root of $\bar G$, $g_D = |B| \le g$. For $x \in R_i \setminus B$, $\bar x$ lies in the $i$-th fibre of $\bar\xi$.

*Step 2, the induction hypothesis.* P in dimension $N - 1$: $\nu(\bar\xi) \le 2\bar\delta + \pi$ with $\pi = |\bar\Pi|$, $\bar\Pi = \Pi(\bar\xi)$. Since $\nu(\bar\xi) \ge 2\delta + 2 - g_D$: $\pi \ge 2 + 2g - g_D \ge 2$. Write $\bar\xi = \bar\xi_0 \circ L_{\bar\Pi}$, $\bar\delta_0 = \bar\delta/\pi \ge 1$. The fibres $\bar R_i^+$ of $\bar\xi$ in $\bar D$ are $\bar\Pi$-invariant, consist of $m_i \le \bar\delta_0$ cosets, and $\sum m_i = \nu(\bar\xi)/\pi \le 2\bar\delta_0 + 1$. The set $\mathcal{H}$ of points of $\bar R^+ = \bigsqcup \bar R_i^+$ that are not images of points of $R \setminus B$ (the holes) has $|\mathcal{H}| = \nu(\bar\xi) - (2\delta + 2 - g_D) \le \pi - 2 - 2g + g_D$.

*Step 3, lifting the period group.* Let $\bar c \in \bar\Pi \setminus 0$. For $x \in R_i \setminus B$ the point $\bar x + \bar c$ lies in $\bar R_i^+$. If it is not a hole it is $\bar x'$ for a unique $x' \in R_i \setminus B$, and $x + x'$ is a lift of $\bar c$ in $R + R$. At least $2\delta + 2 - g_D - |\mathcal{H}| \ge 2\delta + 4 - \pi > 0$ points $x$ are of this kind (recall $\pi \le \bar\delta \le \delta$). The two lifts of $\bar c$ differ by $a$, and they cannot both lie in $R + R$ because $a \notin 4R$. So $\bar c$ has a unique lift $c^\ast \in R + R$, and for every $x \in R_i \setminus B$: either $\bar x + \bar c$ is a hole, or $x + c^\ast \in R_i \setminus B$. Let $\Pi' = \{0\} \cup \{c^\ast\}$. It is a subgroup: for $\bar c_1 \ne \bar c_2$ there are at least $2\delta + 2 - g_D - 2|\mathcal{H}| \ge 2\delta + 6 - 2\pi + g > 0$ points $x \in R \setminus B$ with neither $\bar x + \bar c_1$ nor $\bar x + \bar c_1 + \bar c_2$ a hole, for such $x$ both $x + c_1^\ast$ and $x + c_1^\ast + c_2^\ast$ lie in $R$, so $c_1^\ast + c_2^\ast \in R + R$ is the lift $(c_1 + c_2)^\ast$. So $\Pi' \le D$ has order $\pi$ and meets $\{0, a\}$ trivially.

*Step 4, the lifted fibres.* Let $R_i^+ = (R_i \setminus B) + \Pi'$. Reduction is injective on $R^+ = \bigcup R_i^+$ (two points with the same image differ by $0$ or $a$, and their difference lies in $R + R + \Pi' \subseteq 4R$) and maps $R_i^+$ into $\bar R_i^+$. So the $R_i^+$ are pairwise disjoint, $\Pi'$-invariant, and consist of $m_i' \le m_i$ cosets of $\Pi'$.

*Step 5, a periodic competitor.* In $L_{\Pi'}(D)$ let $Y_i = L_{\Pi'}(R_i^+)$: pairwise disjoint, $|Y_i| \le \bar\delta_0$, $\sum |Y_i| \le 2\bar\delta_0 + 1$. The space of $(p_0, p_1, p_2)$ over $F$ with $\sum p_i = 0$, $\deg p_i \le \bar\delta_0$, $Z_{Y_i} \mid p_i$ has dimension at least $2\bar\delta_0 + 2 - \sum|Y_i| \ge 1$, and each subspace $\{p_i = 0\}$ has dimension $(\bar\delta_0 + 1 - |Y_j| - |Y_l|)^+$, which is smaller. $F$ is infinite, so there is a solution with all $p_i \ne 0$. Put $P_i = p_i \circ L_{\Pi'}$: $\sum P_i = 0$, $\deg P_i \le \pi\bar\delta_0 = \bar\delta \le \delta - g$, and $P_i$ vanishes on $R_i^+ \supseteq R_i \setminus B$.

*Step 6, uniqueness.* By Lemma 1.2 applied to the pattern $R \setminus B$, of size $2\delta + 2 - g_D > \delta + (\delta - g)$: $u_0 P_1 = u_1 P_0$. So $\xi = P_0/P_1 = (p_0/p_1) \circ L_{\Pi'}$, and $\Pi' \le \Pi(\xi)$ has order $\pi \ge 2$. Contradiction. $\square$

**Theorem 3.2. [proved]** Under the hypotheses of Theorem B (P in dimension $N - 1$, $\Pi(\xi) = 0$, $|R| = 2\delta + 2$): if some $a \in D \setminus 0$ is not in $R + R$, then the affine span of $R$ has dimension at most $\delta + 2$. Such an $a$ exists whenever $N \ge \delta + 3$.

*Proof.* Steps 1 and 2 above use only $a \notin R + R$. The image of $R \setminus B$ lies in the union of $m = \sum m_i \le 2\bar\delta_0 + 1$ cosets of $\bar\Pi$, whose affine span has dimension at most $\log_2\pi + 2\bar\delta/\pi$. For $2 \le \pi \le \bar\delta$ this is at most $\bar\delta + 1 \le \delta - g + 1$ (the function is convex in $\pi$ and the bound holds at both ends). Adding the $g_D \le g$ points of $B$ and the direction $a$: the affine span of $R$ has dimension at most $\delta + 2$. For the last claim, $|R + R \setminus 0| \le (\delta + 1)(2\delta + 1) < 2^{\delta + 3} - 1$. $\square$

**Corollary 3.3. [proved]** Fix $\delta^\ast$. If P fails in some degree $\le \delta^\ast$, let $(\xi, D)$ be a counterexample to P$_0$ of degree $\delta \le \delta^\ast$ whose dimension $N$ is least among all counterexamples of degree at most $\delta^\ast$. Then $D = 4R$ for every choice of $2\delta + 2$ points $R$ in the fibres, every such $R$ that misses a direction of $D$ in $R + R$ spans at most $\delta + 2$ affine dimensions, and
$$N \ \le\ \min\bigl(\delta + 2,\ \log_2 B(\delta)\bigr), \qquad B(\delta) = 1 + \tbinom{2\delta+2}{2} + \tbinom{2\delta+2}{4} .$$
Equivalently: P holds in all dimensions for all degrees $\le \delta^\ast$ if P$_0$ holds for the finitely many pairs $(N, \delta)$ with $\delta \le \delta^\ast$ and $N \le \min(\delta + 2, \log_2 B(\delta))$. The bounds are $N \le 6, 7, 8, 9, 10$ for $\delta = 4, 5, 6, 7, 8$, and $N \le 15$ for $\delta = 15$.

*Proof.* Take $N$ least among the counterexamples of degree at most $\delta^\ast$. Then P$_0$, hence P, holds in all dimensions below $N$ for these degrees. Restricting $D$ to the span of the differences of $R$ keeps genericity, the fibres and aperiodicity, so $R$ spans $D$ affinely by minimality. Apply Theorems B and 3.2. $\square$

**Corollary 3.4. [proved from 2.1, 3.3 and a computation]** P holds for all $\xi$ of degree at most 4, on generic subspaces of every dimension, over every field.

*Proof.* Degrees $\le 3$: Corollary 2.1. Degree 4: by Corollary 3.3 it suffices that no aperiodic $\xi$ of degree 4 has 10 points in its fibres on a generic subspace of dimension $N \le 6$ spanned by them. **[checked]** `26_search small 4 N` enumerates every 10-point set containing an affine frame of $\mathbb{F}_2^N$ and every colouring with sizes $\le 4$: for $N = 6$, $1.08 \cdot 10^8$ configurations, none with a solution. For $N = 4, 5$ the solutions found are periodic (table in 6.1). By Lemma 1.2 the solution of a configuration is unique, and a configuration without solution for the random basis has none for the generic one. As a check that does not use Theorem 3.2, $N = 7$ and $N = 8$ were also run ($2.6 \cdot 10^7$ and $9.1 \cdot 10^5$ configurations, no solution), and 10 points span at most 9 dimensions, where they are affinely independent. $\square$

Remarks. (i) Theorem B is the lifting of a period from one reduction to $\xi$. It works because a direction outside $4R$ makes the reduction multiplicity-free and the lift of the period group unique, and then the periodic function built on the lifted fibres has degree at most $\delta$ and must be $\xi$. (ii) In the regime of the list bound $R$ has positive density and $4R = D$: Theorem B does not apply there. (iii) The counts in steps 2 to 6 have slack that grows with the excess, so the same argument should give $|\Pi(\xi)| \ge e + 1$ directly for $|R| = 2\delta + 1 + e$ and $D \not\subseteq 4R$. I did not write this out, and it is not needed: P follows from P$_0$. **[not checked]**

## 4. Invariance under additive deformations

As in note 17 section 3, let $F_0 = \mathbb{F}_2(b)(t)$ with free parameters $t$ (the field of the generic point of the solution space of a pattern), and let $\sigma_\varepsilon : \mathbb{F}_2[b, t, X] \to \mathbb{F}_2[b, t, X][\varepsilon]$ be the ring homomorphism with $b_i \mapsto b_i + \varepsilon b_i^2$, $X \mapsto X + \varepsilon X^2$, $t \mapsto t$. Since squaring is additive, $\sigma_\varepsilon(X + x) = (X + x)(1 + \varepsilon(X + x))$ for every $x \in D$. $\sigma_\varepsilon$ extends to $F_0(X) \to F_0(X)((\varepsilon))$.

**Theorem C. [proved]** Let $u_0 + u_1 + u_2 = 0$ in $\mathbb{F}_2[b, t][X]$, pairwise coprime, of degree $\delta$, with $\nu = 2\delta + 1 + e$ roots in $D$, $e \ge 0$. Then
$$\sigma_\varepsilon(\xi) \ \equiv\ \xi \pmod{\varepsilon^{e + 2}} .$$
Equivalently each $u_i$ satisfies $\sigma_\varepsilon(u_i) \equiv \lambda u_i \bmod \varepsilon^{e+2}$ with one common $\lambda \in 1 + \varepsilon\,F_0[X][\varepsilon]$. If the zeros of $u_0 u_1 u_2$ are simple, every zero $\varrho$ of $u_0 u_1 u_2$ in an algebraic closure satisfies $\sigma^c_\varepsilon(\varrho) \equiv \varrho + \varepsilon\varrho^2 \bmod \varepsilon^{e+2}$, where $\sigma^c_\varepsilon$ is the substitution on $b$ alone, extended to the closure: the zeros, poles and ones of $\xi$ outside $D$ move, to order $e + 1$, exactly as the points of $D$ do.

*Proof.* $\sigma_\varepsilon(u_i)$ is divisible by $Z_{R_i}$. So $C = u_0\sigma_\varepsilon(u_1) + u_1\sigma_\varepsilon(u_0)$, which equals $u_0\sigma_\varepsilon(u_2) + u_2\sigma_\varepsilon(u_0)$, is divisible by $Z_R$, and so is each coefficient $\Omega_k$ of $\varepsilon^k$ in it. The coefficient of $\varepsilon^k$ in $\sigma_\varepsilon(u_i)$ has degree at most $\delta + k$ in $X$ with top coefficient $\binom{\delta}{k}$ times the leading coefficient of $u_i$ (or lower, if $\deg u_i < \delta$), so the top terms cancel in $\Omega_k$ and $\deg_X\Omega_k \le 2\delta + k - 1$. For $k \le e + 1$ this is less than $\nu$, so $\Omega_k = 0$. Then $u_1\sigma_\varepsilon(u_0) \equiv u_0\sigma_\varepsilon(u_1)$ modulo $\varepsilon^{e+2}$, and since $u_0, u_1$ are coprime, induction on the power of $\varepsilon$ gives $\lambda$: if $\sigma_\varepsilon(u_i) \equiv \lambda u_i + \varepsilon^k w_i$ modulo $\varepsilon^{k+1}$ then $u_1 w_0 = u_0 w_1$, so $w_i = \lambda_k u_i$. For the last claim evaluate $\sigma_\varepsilon(u_0)(X) = \sigma^c_\varepsilon(u_0)(X + \varepsilon X^2)$ at $X = \varrho$: $\prod_j(\varrho + \varepsilon\varrho^2 - \sigma^c_\varepsilon(\varrho_j)) \equiv 0$, and the factors with $\varrho_j \ne \varrho$ are units. $\square$

The case $e = 0$ is $\mathfrak{E}_2\xi = 0$ of note 17 Theorem 3.2. The coefficients of $\varepsilon^k$, $k \ge 2$, are Hasse-Schmidt operators of order $k$. They act nontrivially on squares ($\sigma_\varepsilon(f^2) = \sigma_\varepsilon(f)^2$), so Theorem C sees what the derivations of note 17 cannot (its section 6.1, item 2). The same proof with $z \mapsto z + \varepsilon z^{q}$, $q$ a power of two, gives invariance modulo $\varepsilon^{k}$ for $k(q - 1) \le e + 1$. For the flats $\xi = \mu\circ L_U$ a direct computation gives $\sigma_\varepsilon(\xi) \equiv \xi$ modulo $\varepsilon^{2|U|}$ and not better, against $\varepsilon^{|U| + 1}$ from the theorem ($e = |U| - 1$). **[proved, by hand]** Theorem C is a necessary condition, like Theorem 3.2 of note 17: the functions invariant to a given order form a field, which contains sums of functions with different periods, so invariance alone does not give a period. By homogeneity $\sigma_\varepsilon(\xi)(X) = \xi^{(\theta)}(X^2 + \theta X)$ with $\theta = 1/\varepsilon$, where $\xi^{(\theta)}$ is the solution of the same pattern on the generic subspace $\{x^2 + \theta x\}$: Theorem C compares $\xi$ with its own lift to $D \oplus \theta$ as $\theta \to \infty$.

## 5. The induction with multiplicities, and what is missing

### 5.1 The statement an induction on $N$ must carry

Reducing at a direction $a$ merges $x$ and $x + a$, so the induction hypothesis must allow multiple points, and reductions can be inseparable. For nonconstant $\xi$ let $\mathrm{mult}_x(\xi)$ be the order of vanishing of $\xi - \xi(x)$ at $x$ if $\xi(x) \in \{0, 1, \infty\}$ (order of the pole for $\infty$) and 0 otherwise, and $q(\xi)$ the largest power of two with $\xi \in F(X^q)$.

**Conjecture P$_{\mathrm{mult}}$. [conjectured]** On a generic $D$: $\sum_{x \in D}\mathrm{mult}_x(\xi) \le 2\deg\xi + q(\xi)\,|\Pi(\xi)|$.

For $q = 1$ and simple points this is P. It is the form anticipated in note 17 section 6.1 item 4. **[checked, exhaustive]** `26_search mult N delta`: all patterns of multiplicities on $D$ with three colours, each colour of total multiplicity $\le \delta$, total $2\delta + 2$, solved by linear algebra, and for each solution $\sum\mathrm{mult}$, $q$ and $|\Pi|$ computed.

| $n$ | $\delta$ | patterns | with a solution | types $(\deg, \sum\mathrm{mult}, \lvert\Pi\rvert, q)$ | violations |
| --- | --- | --- | --- | --- | --- |
| 8 | 2 | 1736 | 84 | $(2,6,1,2)$, $(2,6,2,1)$ | 0 |
| 8 | 3 | 24388 | 0 | | 0 |
| 8 | 4 | 163996 | 2520 | $(4,10,1,2)$, $(4,10,2,1)$, $(4,12,1,4)$, $(4,12,2,2)$ | 0 |
| 8 | 5 | 735602 | 4788 | $(4,12,1,4)$, $(4,12,2,2)$ | 0 |
| 8 | 6 | $2.5 \cdot 10^6$ | 31640 | $(4,12,1,4)$, $(4,12,2,2)$, $(6,14,1,2)$, $(6,14,2,1)$ | 0 |
| 16 | 2 | 197120 | 1400 | $(2,6,1,2)$, $(2,6,2,1)$ | 0 |
| 16 | 3 | $1.3 \cdot 10^7$ | 0 | | 0 |

Every solution has $q|\Pi| \ge 2$, and equality $\sum\mathrm{mult} = 2\deg + q|\Pi|$ occurs with every split of $q|\Pi|$ into the two factors.

### 5.2 The skeleton

**Proposition 5.1. [proved]** Suppose P$_{\mathrm{mult}}$ holds in dimension $N - 1$. Let $D$ be generic of dimension $N$ and $\xi$ with $\sum_x \mathrm{mult}_x(\xi) \ge 2\delta + 2$. Then for every $a \in D \setminus 0$ and every place $w$ of $F$ above the $a$-adic place of $K$, the reduction of $(u_0, u_1, u_2)$ at $w$ either has a zero component (the reduced function is one of the constants $0, 1, \infty$), or its reduced function $\bar\xi_a$ is inseparable or has a nonzero period in $D/a$.

*Proof.* Scale and reduce as in Theorem B, step 1. If all $\bar u_i \ne 0$ were proportional, they would vanish at the class $y$ of $\{x, x + a\}$ to order at least half of $M_y = \mathrm{mult}_x + \mathrm{mult}_{x+a}$, so $\delta \ge \frac12\sum_x\mathrm{mult}_x \ge \delta + 1$. Otherwise let $\bar G$ be the gcd, $g_y$ its order at $y$, $\bar\delta \le \delta - \deg\bar G$. If both points of a class have the same colour $c$, $\bar u_c$ vanishes to order $M_y$ and $\mathrm{mult}_y(\bar\xi_a) \ge M_y - g_y$. If they have different colours with multiplicities $m \le m'$, all three $\bar u_i$ vanish to order $m$, so $g_y \ge m$ and $\mathrm{mult}_y(\bar\xi_a) \ge m' - g_y \ge M_y - 2g_y$. So $\sum_y \mathrm{mult}_y(\bar\xi_a) \ge 2\delta + 2 - 2\deg\bar G \ge 2\bar\delta + 2$, and P$_{\mathrm{mult}}$ gives $q(\bar\xi_a)|\Pi(\bar\xi_a)| \ge 2$. $\square$

For simple points the three kinds of degenerate directions leave these traces on $R$ **[proved, the first two in note 17 Proposition 3.5, the third by counting roots of $\bar u_0\bar u_1\bar u_2$, whose reduced parts are squares]**: constant $\bar\xi_a$ (component $l$ zero): $|R_i \cap (R_j + a)| \ge r_i + r_j - \delta$; inseparable: $4 d_{\mathrm{same}}(a) + 2 d_{\mathrm{mix}}(a) \ge \nu + 3 + 3e$, with $d_{\mathrm{same}}$, $d_{\mathrm{mix}}$ the numbers of classes of $\{0, a\}$ with two points of $R$ of the same, of different colours; and $a$ is a period of $\xi$ iff $d_{\mathrm{same}}(a) \ge \delta$ (note 17 Proposition 3.4, with the degree of $u_0(X)u_1(X + a) + u_1(X)u_0(X + a)$, which is at most $2\delta - 2$).

### 5.3 The missing step

To close the induction one needs: *if $\sum\mathrm{mult} \ge 2\delta + 2$ and $\xi$ is separable without period, then some direction $a$ has a nondegenerate reduction.* Theorem B proves this when a direction outside $4R$ exists: there the reduction cannot be constant or inseparable for counting reasons, and a period of the reduction lifts. In general three things fail at once, and each is a precise obstruction:

1. **Constant reductions.** When $a \in R_i + R_j$ occurs $\ge r_i + r_j - \delta$ times the reduction can lose a component, and then it carries no function at all on $D/a$. In the flats every $a \notin \Pi$ is of this kind. The information that survives is the divisibility $\bar h_i\bar Z_{R_i} = \bar h_j\bar Z_{R_j}$ (section 2.4), an approximate translation of $R_i$ onto $R_j$, not a period.
2. **Lifts are not unique.** A period $\bar c$ of the reduction at $a$ lifts to $c$ or $c + a$, and when $a \in 4R$ different points of $R$ may use different lifts. Example **[proved]**: for $\delta = 2$, $R_0 = \{0, c\}$, $R_1 = \{y, y + c\}$, $R_2 = \{z, z + c + a\}$ has a singular reduction at $a$ with period $\bar c$, and no solution on $D$ (the determinant is $a\,y(y + c) \ne 0$).
3. **The competitor is too large.** The periodic function that the reduction provides on $D$ is $\bar\xi_a \circ L_a$, of degree up to $2\delta$, and Lemma 1.2 needs more than $3\delta$ common fibre points to identify it with $\xi$. Only a competitor of degree $\le \delta$, built from fibres that are unions of cosets of a lifted group as in Theorem B step 5, can be compared, and this needs item 2.

In the dense regime $\nu > n/2 + \delta - 1$ (it contains the triples of the list bound whose gcd has few roots, and all configurations of section 6.2) every direction is constant or inseparable by note 17 Proposition 3.5 (ii), because $|R \cap (R + a)| \ge 2\nu - n$, so $D \setminus 0$ is partitioned into the three constant types and the inseparable type. A proof of P there has to show that the inseparable directions with $d_{\mathrm{same}} \ge \delta$ exist, from the sizes of the four classes. The counts available (5.2) are consistent with no such direction: I checked that for $r_i \approx 7n/24$, $\delta = 3n/8$ the three constant classes may cover all of $D \setminus 0$ without contradiction. **[heuristic count]** So the dense case needs an exact tool again, and the natural candidates are the content divisibilities of section 2.4 (the product of the elements of the three constant classes divides the three contents, which bounds their number by the degree of the solution in $b$) and Theorem C. I did not find the argument.

## 6. Numerical coverage

### 6.1 Method

`26_search.c`, random basis in $\mathrm{GF}(2^{64})$. A configuration $(R_0, R_1, R_2)$ with $|R_i| \le \delta$, $\sum = 2\delta + 2$ has a solution iff a Hankel determinant of size $\delta - \max r_i + 1$ in the moments of the weights $Z_{R_0}(y)/(Z_{R_1}(y) Z'_{R_2}(y))$, $y \in R_2$, vanishes ($R_2$ the smallest set, $R_0$ the largest). **[proved: $h_0 Z_{R_0} + h_1 Z_{R_1}$ vanishes on $R_2$ iff $h_1$ interpolates $h_0 Z_{R_0}/Z_{R_1}$ there, iff the divided differences of order above $\deg h_1$ vanish.]** This is the key equation of note 17 Proposition 2.6 in the roles of the three fibres, and it makes a test cost a few hundred field multiplications. A configuration that is nonsingular for the random basis is nonsingular for the generic one. For each singular one a solution is computed by linear algebra and its reduced $\xi$, $\deg$, $\nu$, $|\Pi|$ are recorded; by Lemma 1.2 this is the only reduced solution.

Validation **[checked]**: `all 3 2`, `all 4 2`, `all 4 4` reproduce note 17's counts (420 and 28, 120120 and 840, $2.94 \cdot 10^7$ and 19320 with types $(4,10,2)$ and $(4,12,4)$). `densetest` is a positive control of the incremental code path (three cosets of an 8-element subspace at $\delta = 11$: 65 singular among 6435, all of type $(8, 24, 8)$). The degree-14 and degree-13 runs find the periodic solutions that P allows, in the same code path that reports no solution at degree 15.

### 6.2 The dense end at $n = 32$

A violation of P$_0$ in degree $\delta$ needs $2\delta + 2$ points, that is all of $D$ but $u = 30 - 2\delta$ points. `dense` ($u = 0$) and `dense2 u` enumerate every partition of $D$ minus $u$ points into three sets of size $\le \delta$, with the pair (unused set, smallest set) over representatives of the orbits of $\mathrm{AGL}(5, 2)$ (canonical forms by minimizing over affine frames), the middle set over all subsets.

| $\delta$ | unused | orbits of (unused, smallest) by size of the smallest | configurations | with a solution | reduced types $(\deg, \nu, \lvert\Pi\rvert)$ | violations |
| --- | --- | --- | --- | --- | --- | --- |
| 15 | 0 | 1, 1, 2, 2, 4, 5, 8, 9, 15 (sizes 2 to 10) | 601,717,992 | 0 | | 0 |
| 14 | 2 | 2, 3, 7, 12, 25, 41, 78, 124, 204 | 841,993,816 | 9012 | $(14,30,2)$: 8712, $(12,28,4)$: 194, $(8,24,8)$: 106 | 0 |
| 13 | 4 | 7, 16, 41, 85, 204, 418, 854, 1549 (sizes 2 to 9) | 1,623,257,172 | 1482 | $(12,28,4)$: 575, $(8,24,8)$: 907 | 0 |
| 12 | 6 | 25, 67, 204, 533, 1388, 3175, 6657 (sizes 2 to 8) | 2,355,502,422 | 6884 | $(12,26,2)$: 5492, $(12,28,4)$: 126, $(8,24,8)$: 1266 | 0 |

**[checked, exhaustive]** Consequences, by Lemma 1.2: on a generic 5-dimensional subspace no rational function of degree $\le 15$ has all 32 points in its fibres over $0, 1, \infty$; every function of degree $\le 14$ with 30 points has degree 14 and a period (it is $\xi_0 \circ L_{\{0, a\}}$ with $\xi_0$ of degree 7 and 15 of the 16 points of $D/a$, the generic count); no function of degree $\le 13$ has 28 points except with $|\Pi| = 4$ in degree 12 (seven of the eight cosets); every function of degree $\le 12$ with 26 points has degree 12 and $|\Pi| = 2$ (13 of the 16 points of $D/a$ in the fibres of a function of degree 6) or $|\Pi| = 4$. So **P holds at $n = 32$ for degrees 12, 13, 14, 15**, in addition to degrees $\le 7$ from note 17. In 145 of the 17378 singular configurations (62 in degree 13, 83 in degree 12) the solution space has dimension above one, which Lemma 1.2 covers. The types with $\nu$ below the pattern size are solutions with a common factor, as in note 17. Degrees 8 to 11 at $n = 32$ are not covered: the number of configurations grows to about $10^{11}$ per degree.

### 6.3 Small degree in every dimension

`small delta N`: every set of $2\delta + 2$ points containing the frame $0, e_1, \dots, e_N$, every colouring up to permutation of the colours.

| $\delta$ | $N$ | configurations | with a solution | types | violations |
| --- | --- | --- | --- | --- | --- |
| 4 | 4 | 1,697,850 | 1065 | $(4,10,2)$: 540, $(4,12,4)$: 525 | 0 |
| 4 | 5 | 54,941,250 | 225 | $(4,10,2)$: 225 | 0 |
| 4 | 6 | 107,530,500 | 0 | | 0 |
| 4 | 7 | 26,239,500 | 0 | | 0 |
| 4 | 8 | 907,725 | 0 | | 0 |

This is the computation behind Corollary 3.4.

### 6.4 Symmetric colourings

`sym N mode seed poly...`: colourings of $D$ that are invariant under a linear map $g$ (a block companion matrix), with $g$ fixing the three colours (mode 0) or permuting them cyclically (mode 1), all sizes at once ($\delta = |R|/2 - 1$, sizes $\le \delta$). **[checked]** $N = 5$: $g$ of order 7, 5 and 3 fixing the colours and of order 3 rotating them, $1.4 \cdot 10^6$ configurations in degrees 2 to 15. $N = 6$: $g$ of order 9, 7 and 15, $1.4 \cdot 10^5$ configurations in degrees up to 31. $N = 7$: $g$ of order 7 with characteristic polynomial $(x^3 + x + 1)(x^3 + x^2 + 1)(x + 1)$, $4.2 \cdot 10^7$ random invariant colourings. Every solution found is periodic and satisfies P, several with equality: $(\deg, \nu, |\Pi|) = (10, 22, 2)$ and $(12, 26, 2)$ at $n = 32$, $(28, 60, 4)$ and $(16, 48, 16)$ at $n = 64$, $(42, 86, 2)$ at $n = 128$. This is thin (invariant colourings are a negligible fraction of all), but it is the only data in degrees 8 to 11 at $n = 32$ and at $n = 64, 128$ beyond degree 4.

### 6.5 Not done

Degrees 8 to 11 at $n = 32$. Anything exhaustive at $n = 64$ beyond degree 4 (Corollary 3.4 covers degrees $\le 4$ there, and by Corollary 3.3 degree 5 would need the 12-point configurations spanning 6 and 7 dimensions, about $10^{11}$ without a classification of the point sets up to affine equivalence, a few $10^7$ with one). Four-member configurations.

## 7. Answers to the brief

- **Proved:** P for functions with two fibres in $D$ (Theorem A: numerator and denominator split, or by symmetry any two of the three), hence for $\nu \ge 3\delta - 1$ and for $\delta \le 3$. P for $\delta \le 4$ in every dimension (Corollary 3.4, computer assisted). P$_0$ in dimension $N$ from P in dimension $N - 1$ whenever $D \not\subseteq 4R$, in particular when $2^N > B(\delta)$ (Theorem B). A strengthening of the ramification theorem of note 17 by higher-order operators (Theorem C).
- **Not proved:** P, its weak form, the case of one complete fibre (only Proposition 2.3), P$_{\mathrm{mult}}$.
- **Disproved:** nothing. No violation in $5.4 \cdot 10^9$ new configurations at $n = 32$, $1.9 \cdot 10^8$ in degree 4 up to $n = 256$, and $1.6 \cdot 10^7$ multiplicity patterns.
- **The ideas of the brief.** (1) The generic model taken literally is what gives everything here: unique factorization in $\mathbb{F}_2[b]$, and the specialization $a \to 0$ with the period lifted back (Theorem B). (2) Counting over all translations gives nothing in the dense regime, as note 17 found. The exact version that works is Proposition 2.3. (3) I did not use Riemann-Hurwitz. Theorem C is the exact form of the wild ramification at infinity. (4) Lemma 1.1 is the $\mathbb{F}_2$-linear form of the problem. I found no use of Walsh spectra.
- **For the list bound:** Theorem 5.1 of note 17 remains conditional on P. Its hypothesis is now verified at $n = 32$ at the dense end, where it is used.

## 8. Reproduction

`cc -O2 -o 26_search 26_search.c` in `scripts/` (needs `02_gf.h`). Times on one core of an Apple M4 Max.

- `./26_search all N delta`: validation, $N \le 4$. `all 4 4`: 34 s.
- `./26_search dense part 4` for `part` = 0, 1, 2, 3: degree 15, 62 s per process (46 s of it for the orbit representatives).
- `./26_search dense2 2 part 4`: degree 14, 53 s per process. `./26_search dense2 4 part 4`: degree 13, 87 s per process. `./26_search dense2 6 part 3` for `part` = 0, 1, 2: degree 12, 4.2 to 4.8 minutes per process (3.5 minutes of it for the orbit representatives).
- `./26_search small 4 N` for $N = 4, \dots, 8$: 61 s at $N = 6$, less elsewhere.
- `./26_search mult N delta`: $n = 8$, $\delta \le 6$ and $n = 16$, $\delta \le 3$, under two minutes each.
- `./26_search sym N mode seed poly...`: section 6.4.
- `./26_search densetest`, `./26_search reps`, `./26_search pairreps u`: the positive control and the orbit counts.

## References

- Note 17 (`17-all-words-theory.md`) for the three-fibre form, Conjecture P, Propositions 3.4 and 3.5 and Theorem 5.1. Note 04 (`04-list-bounds-beyond-johnson.md`) Lemma 2.1 for the places of $K$.
- M. Kneser, Abschätzung der asymptotischen Dichte von Summenmengen, Math. Z. 58 (1953). Used in the form $|A + B| \ge |A| + |B| - |H|$ for finite subsets of an abelian group with $H$ the stabilizer of $A + B$. **[quoted from memory, not re-read]**
