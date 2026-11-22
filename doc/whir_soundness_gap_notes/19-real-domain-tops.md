# 19. Unconditional bounds on the real domain: the dual criterion and list bounds inside a previous-level class

Researcher 19 (round 4). Every statement is tagged **[proved]** (proof in this note), **[proved, machine-checked finite case]** (the proof uses a finite computation that was run), **[checked]** (numerically, sizes stated), **[quoted]** or **[conjectured]**. Scripts are `scripts/19_*`, section 9 says how to run them.

Notation as in notes 09, 12, 13. $F$ is a field of characteristic two, $D \subset F$ an $\mathbb{F}_2$-subspace of dimension $N \ge 4$, $n = 2^N$, $u = n/16$. Nothing is assumed about $D$ or $F$ unless stated: every theorem of sections 1 to 3 holds on every subspace domain of every field, in particular on the real domains $D_{\kappa,R} \subset K$. For $c \in \mathbb{Z}^D$ with $\sum c = 0$: $\Lambda_c(X) = \prod_s (1 - sX)^{c(s)}$, $\hat c(\varphi) = \sum_x c(x)(-1)^{\varphi(x)}$ for $\varphi$ in the dual space $D^\vee$, and $L_e = \{c : \hat c \equiv 0 \bmod 2^{e+1}\}$. Two $T$-sets share $e_1..e_g$ ("depth $g$") iff $\Lambda_{1_S - 1_{S'}} \equiv 1 \pmod{X^{g+1}}$, iff $\deg(Z_S - Z_{S'}) < T - g$. A strict common top list of a monic word of degree $T$ with codewords of degree $< k$ is a set of $T$-sets pairwise at depth $g = T - k$ (with the analysis degree $d = k - 1 + \ell$: $g = T - k - \ell$). A **previous-level class** is a class of sets modulo $L_{N-3}$: equal sizes and $n_\varphi(S) \equiv n_\varphi(S') \pmod{n/8}$ for all $\varphi$. On a generic domain these are the classes at depth $n/16 \le g < n/8$ (the second dyadic range of note 12).

For $\varphi \ne 0$ let $H = \ker\varphi$, $\delta_\varphi = \prod_{x \notin H} x = L_H(t)$ for any $t \notin H$, and $a_\varphi = 1/\delta_\varphi$, $a_0 = 0$. The **dual space** is $D^\star = \{a_\varphi\}$.

## 0. Summary

**The brief asked for** an unconditional bound "every monic word of degree $T$ in the window has at most $B$ codewords within agreement $T$ on the real $D$". **I do not have that.** What I have is the following, and I believe it is exactly as far as the pigeonhole structure of note 13 can be turned into theorems.

| | statement | domain | status |
| --- | --- | --- | --- |
| Theorem 1 (1.2) | **Dual criterion.** For $c \in L_e$ with $\hat c = 2^{e+1} d$ and $\Omega = \{\varphi : d_\varphi \text{ odd}\}$: $\theta_i(c)^{2^{N-1-e}} = \sum_{\varphi \in \Omega} \delta_\varphi\, c_i(\ker\varphi)$, and the vanishing of $\theta_0..\theta_{i-1}$ is equivalent to $P_1(\Omega) = \dots = P_i(\Omega) = 0$, $P_m(\Omega) = \sum_{\varphi \in \Omega} a_\varphi^{-(2^m - 1)}$. So two sets of one previous-level class share a top to depth $g$ iff the odd Walsh support of their difference, seen as a set of points of $D^\star$, has $\sum 1/a = 0$ (for $g < 3n/16$), and also $\sum 1/a^3 = 0$ (for $g < 7n/32$), and so on | every $D$, every $F$, all integer differences (sets and multisets) | proved, checked |
| Theorem 2 (2) | **Dual BCH bound.** In a previous-level class $\Omega$ is empty or has at least 6 points when $g \ge n/8$, and at least 8 points when $g \ge 3n/16$. In particular four dual points never produce a coincidence | every $D$, every $F$ | proved, checked |
| Theorem 3a (3.1) | Sets of size $T$ in one previous-level class that share a top to depth $g \ge 3n/16$ pairwise differ in at least $n/2$ points, and there are at most $1/(1 - 2\tau)^2$ of them, the generic Johnson-type value. Rate 1/2, $T \in [11n/16, n/\sqrt2)$: at most 7. Rate 1/8, $T \in [5n/16, 0.3536n)$: at most 11. Rate 1/4, $T \in [7n/16, n/2)$: at most $n^2/(n - 2T)^2$ | every $D$, every $F$ | proved, checked |
| Theorem 3b (3.2) | The same with $n/8 \le g < 3n/16$: pairwise distance at least $3n/8$, and fewer than $2^{32}$ members at rate 1/2 for $T \in [5n/8, 11n/16)$, fewer than $2^{36}$ at rate 1/4 for $T \in [3n/8, 7n/16)$, fewer than $2^{21}/(\tau - \frac14)^2$ at rate 1/8 for $T \in (n/4, 5n/16)$. No classification of the formal classes is used | every $D$, every $F$ | proved |
| Theorem 3c (3.3) | Rate 1/16, $T \in [3n/16, n/4)$: at most $\frac{3}{16(\frac34 - \tau)(\frac14 - \tau)}$ members in one previous-level class (5 at $3n/16$, 11 at $7n/32$), any two at distance exactly $3n/8$. Attained (5) at $n = 16$ | every $D$, every $F$ | proved, checked |
| Proposition 5.1 | **The real domain is not generic inside the windows.** On $D_{\kappa,R}$, $N = 25, 26, 27, 28$, the subspaces $V = \{f : f(0) = f(1) = f_{N-1}\}$ and $V' = (x^2 + x + 1)\,\mathbb{F}_2[x]_{<N-2}$ of size $n/4$ have $\deg(L_V - L_{V'}) \le n/16$. So there are monic words of degree $T$ with two codewords at agreement $T$ whose agreement sets differ in $3n/8$ points, at rate 1/2 for every $T \in (5n/8, 11n/16)$, at rate 1/8 for $T \in (n/4, 5n/16)$ and at rate 1/16 for $T \in [3n/16, n/4)$, where the generic theorems say "every pair is a hyperplane swap" and (rate 1/16) "the list is 1" | the real domains | proved, machine-checked finite case |

**What "inside one previous-level class" means for a word.** Let $w$ be monic of degree $T$ and let $M(w)$ be the number of previous-level classes that its list of agreement sets meets. Then the list has at most $B \cdot M(w)$ members, $B$ the bound of Theorem 3. On a generic domain $M(w) = 1$. On the real domain $M(w) > 1$ needs a **deep accident**: two list members whose difference lies in $L_{e'} \setminus L_{e'+1}$ for some $e' \le N - 4$. Section 4 states exactly what that is in the dual space (a nonzero Boolean function of degree at most $e' + 1$ on $D^\star$ whose support satisfies $e' + 1$ power-sum equations in $K$, followed by the conditions of the later blocks, which are not sparse), shows that such accidents do occur in fields of 32 and 64 elements, and explains why I cannot exclude them in $K$: it is a minimum-distance statement about $\{0, \pm 1\}$-valued words of an explicit code with far more codewords than checks. **So the theorems above are unconditional statements about the real domain, but they bound the list of a word only up to the factor $M(w)$, which nobody can bound.** This is the precise form of the remark of note 13, section 8 item 2 ("it would still not cover deep accidents"). What is new relative to note 13 is that the "one-parameter families" hypothesis is not needed: the bound inside a class holds for every class, by a degree argument in the dual space plus the geometry of Walsh vectors, with the generic constant above $11n/16$.

**What is not covered at all:** arbitrary words (phantom degree $r \ge 1$ with roots outside $D$, the subject of researchers 17 and 18); multiset tops beyond the remark of section 6.1; the ranges below the first dyadic point of each window (rate 1/16 on $(n/8, 3n/16)$, rate 1/2 on $(9n/16, 5n/8)$), where the same method gives a distance of only $3n/16$ and no count. Section 8 says why the method cannot extend to phantom roots.

## 1. The dual criterion

### 1.1 The dual space

**Lemma 1.1. [proved; the additivity is note 05 Proposition 4.1]** (i) $\varphi \mapsto a_\varphi$ is an injective $\mathbb{F}_2$-linear map $D^\vee \to F$. (ii) $L_D = L_H^2 + \delta_\varphi L_H$ for $H = \ker\varphi$. Writing $L_D(Y) = \sum_{i=0}^{N} D_i Y^{2^{N-i}}$ and $L_H(Y) = \sum_{i=0}^{N-1} c_i(\varphi) Y^{2^{N-1-i}}$ ($D_0 = c_0 = 1$): $c_i(\varphi)^2 = D_i + \delta_\varphi c_{i-1}(\varphi)$ for $1 \le i \le N - 1$, hence
$$\bigl(\delta_\varphi c_i(\varphi)\bigr)^{2^i} = \delta_\varphi^{2^{i+1} - 1} + \sum_{j=1}^{i} D_j^{2^{j-1}}\, \delta_\varphi^{2^{i+1} - 2^j} .$$

*Proof.* (i) $\ell_\varphi = L_H/\delta_\varphi$ is a linearized polynomial of degree $n/2$ that equals $\varphi$ on $D$ (0 on $H$, 1 off $H$). For $\varphi_3 = \varphi_1 + \varphi_2$ the polynomial $\ell_{\varphi_1} + \ell_{\varphi_2} + \ell_{\varphi_3}$ has degree at most $n/2$ and vanishes on the $n$ points of $D$, so it is zero, and its leading coefficient is $a_{\varphi_1} + a_{\varphi_2} + a_{\varphi_3}$. Injective because $a_\varphi \ne 0$ for $\varphi \ne 0$. (ii) $L_D = L_{L_H(D)} \circ L_H$ and $L_H(D) = \{0, \delta_\varphi\}$. Compare coefficients, then induct on $i$. $\square$

### 1.2 The theorem

Recall Proposition 3.1 of note 13: for $c \in L_e$, $\Lambda_c \equiv 1 + \sum_{i=0}^{e} \theta_i(c) X^{2^{e+1} - 2^{e-i}} \pmod{X^{2^{e+1}}}$ with additive $\theta_i$.

**Theorem 1 (dual criterion). [proved]** Let $c \in \mathbb{Z}^D$, $\sum c = 0$.

1. (Exact identity.) With $\sigma$ the Frobenius acting on coefficients and $u_\varphi(X) = \delta_\varphi X^{n/2}/L^{\mathrm{rev}}_{\ker\varphi}(X)$, $L_H^{\mathrm{rev}}(X) = X^{n/2} L_H(1/X)$:
$$\Lambda_c^{\sigma^N}(X^n) = \prod_{\varphi \ne 0} \bigl(1 + u_\varphi(X)\bigr)^{-\hat c(\varphi)} .$$
2. If $c \in L_e$, $\hat c = 2^{e+1} d$ and $\Omega(c) = \{\varphi : d_\varphi \text{ odd}\}$, then for $0 \le i \le e$
$$\theta_i(c)^{2^{N-1-e}} = \sum_{\varphi \in \Omega(c)} \delta_\varphi\, c_i(\varphi) .$$
(This also reproves the sparse support of Proposition 3.1 of note 13.)
3. With $P_m(\Omega) = \sum_{\varphi \in \Omega} \delta_\varphi^{2^m - 1} = \sum_{\varphi \in \Omega} a_\varphi^{-(2^m - 1)}$:
$$\theta_i(c)^{2^{N-1-e+i}} = P_{i+1}(\Omega) + \sum_{j=1}^{i} D_j^{2^{j-1}}\, P_{i+1-j}(\Omega)^{2^j} .$$
So $\theta_0(c) = \dots = \theta_{i-1}(c) = 0$ iff $P_1(\Omega(c)) = \dots = P_i(\Omega(c)) = 0$.
4. $\Omega(c)$ is the support of a Boolean function of degree at most $e + 1$ on $D^\vee$ that vanishes at 0. Hence $\sum_{\varphi \in \Omega(c)} a_\varphi^t = 0$ for every $t \ge 0$ whose binary expansion has at most $N - e - 2$ ones. For $e \le N - 3$: $\lvert\Omega\rvert$ is even and $\sum_{\Omega} a_\varphi = 0$.

*Proof.* (1) $\chi_\varphi = 1_H - 1_{D \setminus H}$, $\Lambda_H = L_H^{\mathrm{rev}}$ and $\Lambda_{D \setminus H} = X^{n/2} L_H(1/X - t) = L_H^{\mathrm{rev}} + \delta_\varphi X^{n/2}$, so $\Lambda_{\chi_\varphi} = (1 + u_\varphi)^{-1}$. Fourier inversion is $n\,c = \sum_{\varphi \ne 0} \hat c(\varphi)\chi_\varphi$ in $\mathbb{Z}^D$, $c \mapsto \Lambda_c$ is a homomorphism to the multiplicative group of $F[[X]]$, and $\Lambda_c(X)^n = \Lambda_c^{\sigma^N}(X^n)$ in characteristic two.

(2) Put $q = 2^{e+1}$. The right side of (1) is $\prod (1 + u_\varphi^q)^{-d_\varphi}$ and $u_\varphi^q = O(X^{qn/2})$, so modulo $X^{qn}$ it is $1 + \sum_\varphi d_\varphi u_\varphi^q$, and only the parity of $d_\varphi$ matters. $L_H^{\mathrm{rev}} = 1 + w$ with $w = \sum_{i \ge 1} c_i(\varphi) X^{n/2 - 2^{N-1-i}} = O(X^{n/4})$, so $1/L_H^{\mathrm{rev}} \equiv 1 + w \pmod{X^{n/2}}$ and
$$u_\varphi^q \equiv \sum_{i=0}^{N-1} \bigl(\delta_\varphi c_i(\varphi)\bigr)^q X^{qn - q 2^{N-1-i}} \pmod{X^{qn}} .$$
The left side of (1) has exponents divisible by $n$ only. $qn - q2^{N-1-i} = n(2^{e+1} - 2^{e-i})$ for $i \le e$, and it is not a multiple of $n$ for $i > e$. Comparing coefficients gives $\theta_i(c)^{2^N} = \sum_{\Omega} (\delta_\varphi c_i(\varphi))^{2^{e+1}}$ at the positions of Proposition 3.1 and zero elsewhere below $X^{qn}$. Take $2^{e+1}$-th roots.

(3) Raise (2) to the power $2^i$ and use Lemma 1.1 (ii). The system is triangular in $P_1, P_2, \dots$ with unit diagonal.

(4) $L_e$ is generated by $2^{e+1-\lvert A\rvert}\varepsilon_A$ ($\lvert A\rvert \le e + 1$) and $\varepsilon_A$ ($\lvert A\rvert > e+1$) (note 02 Theorem W, note 13 Proposition 3.1), and $\hat\varepsilon_A(\varphi) = (-2)^{\lvert A\rvert}\prod_{i \in A}\varphi(b_i)$. So $d \bmod 2$ is a combination of monomials of degree at most $e + 1$ in the coordinates $\varphi(b_i)$ of $\varphi$, without constant term. The dual of $\mathrm{RM}(e+1, N)$ is $\mathrm{RM}(N - e - 2, N)$, and $\varphi \mapsto a_\varphi^t = \prod_l (\sum_i \varphi(b_i)\,a_{b_i^\ast}^{2^{j_l}})$ for $t = \sum_l 2^{j_l}$ is an $F$-combination of monomials of degree at most the number of ones of $t$. $\square$

**Corollary 1.3 (what a non-formal coincidence is). [proved]** Let $S, S'$ be sets of equal size in one previous-level class, $d = (\hat S - \hat S')/(n/4)$, $\Omega = \{d \text{ odd}\} \subset D^\vee \setminus 0$. Then:

- $S, S'$ are in the same class modulo $L_{N-2}$ (they share their top to depth $n/4 - 1$ on every domain) iff $\Omega = \emptyset$;
- for $n/8 \le g < 3n/16$: they share their top to depth $g$ on $D$ iff $\sum_{\Omega} 1/a_\varphi = 0$;
- for $3n/16 \le g < 7n/32$: iff $\sum_\Omega 1/a_\varphi = \sum_\Omega 1/a_\varphi^3 = 0$; for $7n/32 \le g < 15n/64$ add $\sum_\Omega 1/a_\varphi^7 = 0$; and so on with the exponents $2^m - 1$;
- in every case $\lvert\Omega\rvert$ is even and $\sum_\Omega a_\varphi = 0$.

The same holds for multisets of equal mass, and for the classes modulo $L_e$ at every level (with $n/4$ replaced by $2^{e+1}$ and the depths by $2^{e+1} - 2^{e-i}$).

So inside a previous-level class the real domain differs from the generic one by the words of a code of Melas type on the dual space: sets $\Omega$ of points of $D^\star$ with $\sum a = 0$ and $\sum 1/a = 0$. On a generic domain there are none. In $K$ there are some: section 5.

**[checked]** `19_dual_check.py A`: parts 2, 3, 4 and Lemma 1.1 (i) for random $c \in L_e$, all levels $e = 1..N-2$, $N = 5, 6$, power shape in $K$ and in $\mathrm{GF}(2^{13})$, random bases in $K$, $\mathrm{GF}(2^8)$, $\mathrm{GF}(2^{10})$: 192 identities, the key computed by multiplying out $\Lambda_c$. `19_dual_check.py B`: for $n = 16$ and all pairs of equal-sum $s$-sets, $s = 3..8$ ($2.75 \cdot 10^8$ pairs over 23 domains in fields of degree 4, 5, 6, 8, 13, 64): "same $e_2$ iff $P_1(\Omega) = 0$" and "same $e_2, e_3$ iff $P_1(\Omega) = P_2(\Omega) = 0$" held for every pair.

## 2. A degree argument in the dual space

**Theorem 2 (dual BCH bound). [proved]** Let $S \ne S'$ be sets of equal size in one previous-level class that share their top to depth $g$ on $D$, and $\Omega$ as in Corollary 1.3.

1. If $g \ge n/8$: $\Omega = \emptyset$ or $\lvert\Omega\rvert \ge 6$.
2. If $g \ge 3n/16$: $\Omega = \emptyset$ or $\lvert\Omega\rvert \ge 8$.
3. $\lvert S \triangle S'\rvert = u \sum_\varphi d_\varphi^2$ with $\sum_\varphi d_\varphi^2$ even. If $\Omega = \emptyset$ then $\lvert S \triangle S'\rvert \ge n/2$. So $\lvert S \triangle S'\rvert \ge 3n/8$ in case 1, with equality iff $d = \pm 1$ on exactly six functionals and $0$ elsewhere, and $\lvert S \triangle S'\rvert \ge n/2$ in case 2.

*Proof.* Let $\Omega = \{a_1, .., a_w\}$ as distinct nonzero elements of $F$ (Lemma 1.1 (i)) and $p_m = \sum_i a_i^m$. If $p_m = 0$ for $r$ consecutive integers $m = m_0, .., m_0 + r - 1$ and $1 \le w \le r$, the matrix $(a_i^{m_0 + j})_{i \le w,\, j < w}$ is a Vandermonde matrix times an invertible diagonal matrix, and the all-ones vector is in its kernel: impossible. So $w \ge r + 1$. By Corollary 1.3, $p_0 = p_1 = 0$ and $p_{-1} = 0$, and in characteristic two $p_{2m} = p_m^2$, so $p_m = 0$ for $m = -2, .., 2$: $w \ge 6$. In case 2 also $p_{-3} = 0$ and $p_{-4} = p_{-1}^4 = 0$: $m = -4, .., 2$, $w \ge 8$. (3) With $c = 1_S - 1_{S'} = \frac14\sum_\varphi d_\varphi\chi_\varphi$: Parseval gives $\sum d^2 = n\lvert S\triangle S'\rvert/(n/4)^2 = \lvert S \triangle S'\rvert/u$, and $\sum_\varphi d_\varphi = 4c(0) \equiv 0 \pmod 4$ gives the parity. If $\Omega = \emptyset$ then $d = 2d'$, and $\sum d'^2 = 1$ would mean $c = \pm\frac12\chi_\varphi$, not integer valued, so $\sum d^2 \ge 8$. If $\lvert\Omega\rvert \ge 6$ then $\sum d^2 \ge 6$ with equality iff $d$ is $\pm 1$ on $\Omega$, $\lvert\Omega\rvert = 6$, and zero elsewhere. $\square$

A direct proof that four points never suffice: for $a_1 + a_2 + a_3 + a_4 = 0$ put $a = a_1 + a_2$, then $1/a_1 + 1/a_2 = a/(a_1(a_1 + a))$ and $1/a_3 + 1/a_4 = a/(a_3(a_3 + a))$, and $y \mapsto y^2 + ay$ is two-to-one, so equality forces $a_3 \in \{a_1, a_2\}$. Consequences on every domain: swapping a flat of size $n/8$ for a parallel one inside a flat of size $n/4$ never preserves a top beyond depth $n/8 - 1$, and two flats of size $n/4$ whose direction planes in $D^\vee$ share a line never share $c_1$ (this is note 13's "accidents are impossible because all the planes share a point of $D^\star$").

**Remark 2.2 (six points always give a swap). [proved]** Conversely, for any six distinct nonzero functionals with $\sum\varphi_i = 0$ and signs $\epsilon_i$ with an odd number of minus signs, $c = \frac14\sum_i \epsilon_i\chi_{\varphi_i}$ takes values in $\{0, \pm1\}$ (at every $x$ the number of $-1$ among $\epsilon_i(-1)^{\varphi_i(x)}$ is odd, so the sum is $0$ or $\pm 4$), $A = \{c = 1\}$ and $B = \{c = -1\}$ have $3n/16$ points each, and $Z_A - Z_B$ is a constant iff $\sum_i 1/a_{\varphi_i} = 0$ (Corollary 1.3 with $g = 3n/16 - 1$). So the weight-6 words of the dual Melas code correspond (one word to 16 pairs) to the pairs of disjoint $3n/16$-sets in one previous-level class whose locators differ by a constant, and every such pair glues $A \cup C$ to $B \cup C$ for every $C$ disjoint from both. A random model predicts about $\binom{n}{5}/(6 \cdot 2^{64}) = 2^{51.5}$ such words in $D^\star$ at $N = 25$. **[conjectured]** as a count; one explicit word is in section 5.

**[checked]** `19_dual_check.py B` ($n = 16$) and `19_ct32` ($n = 32$, 24 runs in fields of 32 to 256 elements, section 7): among all pairs in a common previous-level class and a common real class, $\lvert\Omega\rvert$ took the values 0, 6, 8, 10, 12 at depth in $[2u, 3u)$ and 0, 8, 10, 12 at depth $\ge 3u$, never 2 or 4, and never 6 at depth $\ge 3u$; the distances were at least $6u$, respectively $8u$.

## 3. List bounds inside a previous-level class

Throughout, $S_1, .., S_L$ are distinct sets of the same size $T$, pairwise in one previous-level class, pairwise sharing their top to depth $g \ge n/8$ on $D$. Replacing every $S_i$ by its complement changes neither hypothesis ($\Lambda_{D \setminus S} = \Lambda_D/\Lambda_S$, and $\hat S$ changes sign off $0$), so let $s = \min(T, n - T)$ and assume $\lvert S_i\rvert = s \le n/2$. Put
$$v_i = \bigl(\hat S_i(\varphi)/4u\bigr)_{\varphi \ne 0} \in \mathbb{R}^{n-1}, \qquad d^{ij} = v_i - v_j \in \mathbb{Z}^{n-1}, \qquad \rho^2 = \lvert v_i\rvert^2 = \frac{s(n - s)}{16u^2} .$$
By Theorem 2, $\lvert d^{ij}\rvert^2 = \lvert S_i \triangle S_j\rvert/u \in \{6, 8, 10, \dots\}$, and $\langle v_i, v_j\rangle = \rho^2 - \lvert d^{ij}\rvert^2/2$.

**Lemma 3.1 (pairs at distance at least $n/2$). [proved]** If $s < n/2$ and $\lvert S_i \triangle S_j\rvert \ge n/2$ for all $i \ne j$, then $L \le J := \lfloor 1/(1 - 2s/n)^2 \rfloor$.

*Proof.* $\langle v_i, v_j\rangle \le \rho^2 - 4 < 0$, and $0 \le \lvert\sum v_i\rvert^2 \le L\rho^2 - L(L-1)(4 - \rho^2)$ gives $L \le 4/(4 - \rho^2) = 64u^2/(8u - s)^2$. $\square$

### 3.1 Above the second position

**Theorem 3a. [proved]** If $g \ge 3n/16$ and $s < n/2$, then $\lvert S_i \triangle S_j\rvert \ge n/2$ for all $i \ne j$ and $L \le 1/(1 - 2s/n)^2$. If $s < n/4$ then $L = 1$.

*Proof.* Theorem 2, parts 2 and 3, then Lemma 3.1. For $s < n/4$ a symmetric difference of $n/2$ points does not fit. $\square$

This is the bound $1/(2\tau - 1)^2$ of the generic theory (note 04 Corollary 2.5, note 12 Theorem A with $M = T$), now on every domain, for lists inside one previous-level class. At rate 1/2 the range is $T \in [11n/16, n/\sqrt2)$ and the bound is $64/9$, so 7, falling to 5. At rate 1/8, $T \in [5n/16, 0.3536n)$: at most 11. At rate 1/4, $T \in [7n/16, n/2)$: $n^2/(n - 2T)^2$, which is 64 at $7n/16$ and $n^2/4$ at $T = n/2 - 1$, where the $n - 1$ members of the hyperplane family live (they are pairwise congruent modulo $L_{N-2}$, at distance $n/2$).

### 3.2 Between the first and the second position

Here $n/8 \le g < 3n/16$, pairs at distance $3n/8$ are possible (section 5 shows that they occur on the real domain), $\rho^2 \ge 3$ in the windows of rates 1/2, 1/4, 1/8, and no Johnson-type count applies. The bound comes from three inequalities for Walsh coefficients of a set and from Theorem 2 applied to pairs of neighbours.

**Lemma 3.2 (one, two, three Walsh coefficients). [proved]** Let $S \subset D$, $4u \le \lvert S\rvert = s \le 8u$, $v = \hat S/4u$. For distinct nonzero functionals $z_1, z_2, z_3$ and signs $\epsilon_i$: (F1) $\epsilon_1 v(z_1) \le s/4u =: m_1$; (F2) $\epsilon_1 v(z_1) + \epsilon_2 v(z_2) \le 2$; (F3) $\sum_{i \le 3}\epsilon_i v(z_i) \le 3 - \kappa$ with $\kappa = \min(s - 4u, 8u - s)/4u$.

*Proof.* $\sum_i \epsilon_i \hat S(z_i) = \sum_{x \in S}\sum_i \epsilon_i(-1)^{z_i(x)}$. (F1) is clear. (F2): a point contributes 2 only on one coset of $\ker z_1 \cap \ker z_2$ ($4u$ points) and at most 0 elsewhere. (F3): if the $z_i$ are independent, a point contributes 3 on one flat of $2u$ points and at most 1 elsewhere, total at most $s + 4u$. If $z_3 = z_1 + z_2$ and $\epsilon_1\epsilon_2\epsilon_3 = 1$, a point contributes 3 on one flat $V$ of $4u$ points and $-1$ elsewhere, total $4\lvert S \cap V\rvert - s \le 16u - s$. If $\epsilon_1\epsilon_2\epsilon_3 = -1$ it contributes 1 or $-3$, total at most $s$. So the sum is at most $\max(16u - s, s + 4u) = 12u - 4u\kappa$. $\square$

**Theorem 3b. [proved]** Let $n/8 \le g < 3n/16$ and $4u < s < 8u$, and let $\rho^2, m_1, \kappa, J$ be as above. Then $\lvert S_i \triangle S_j\rvert \ge 3n/8$ for all $i \ne j$ and
$$L \ \le\ J\bigl(\min(J, 32)\,Q + 1\bigr), \qquad Q = \lfloor 4\rho^2\rfloor \cdot \Bigl\lfloor \frac{25\rho^2}{(3 - m_1)^2}\Bigr\rfloor \cdot \lfloor 16\rho^2\rfloor \cdot \Bigl\lfloor \frac{9\rho^2}{\kappa^2}\Bigr\rfloor .$$

*Proof.* Let $G$ be the graph on $\{1, .., L\}$ with $i \sim j$ iff $\lvert d^{ij}\rvert^2 = 6$. An independent set of $G$ has pairwise distances at least $n/2$, so at most $J$ elements (Lemma 3.1). A graph with maximal degree $\Delta$ and no independent set of more than $J$ vertices has at most $J(\Delta + 1)$ vertices. It remains to bound the degree of the vertex 1.

For a neighbour $j$ write $d = d^{1j} = v_1 - v_j$: by Theorem 2 it is $\pm 1$ on a 6-set $\Omega_j$ and 0 elsewhere. For two neighbours $j \ne l$, the odd support of $d^{jl} = d^{1l} - d^{1j}$ is $\Omega_j \triangle \Omega_l$, which by Theorem 2 is empty or has at least 6 points. So either $\Omega_j = \Omega_l$ or $\lvert\Omega_j \cap \Omega_l\rvert \le 3$: **a neighbour's $\Omega$ is determined by any four of its points.** Neighbours with the same $\Omega$ are pairwise at distance at least $n/2$ (their difference is even), so there are at most $\min(J, 32)$ of them (32 sign patterns). Hence $\Delta \le \min(J, 32)\,Q'$ with $Q'$ the number of distinct $\Omega_j$.

Now $\lvert v_j\rvert = \lvert v_1\rvert$ gives $\langle v_1, d\rangle = \lvert d\rvert^2/2 = 3$, that is $\sum_{\varphi \in \Omega_j} t_\varphi = 3$ with $t_\varphi = d_\varphi v_1(\varphi)$, $\lvert t_\varphi\rvert = \lvert v_1(\varphi)\rvert$. Order the six values $t_1 \ge \dots \ge t_6$. Then $t_1 \ge 1/2$. By (F1), $t_2 + \dots + t_6 \ge 3 - m_1$, so $t_2 \ge (3 - m_1)/5$. By (F2), $t_3 + \dots + t_6 \ge 1$, so $t_3 \ge 1/4$. By (F3), $t_4 + t_5 + t_6 \ge \kappa$, so $t_4 \ge \kappa/3$. So the four points of $\Omega_j$ with the largest $t$ lie in the sets $\{\lvert v_1\rvert \ge 1/2\}$, $\{\lvert v_1\rvert \ge (3 - m_1)/5\}$, $\{\lvert v_1\rvert \ge 1/4\}$, $\{\lvert v_1\rvert \ge \kappa/3\}$ respectively, and $\{\lvert v_1\rvert \ge x\}$ has at most $\rho^2/x^2$ elements. Distinct $\Omega_j$ have distinct top-four sets. So $Q' \le Q$. $\square$

Numbers. The four factors of $Q$ and $J$ are bounded separately over each range.

| rate | range of $T$ | $s$ | $J$ | $Q \le$ | $L \le$ |
| --- | --- | --- | --- | --- | --- |
| 1/2 | $(5n/8, 11n/16)$ | $(5u, 6u)$ | 15 | $14 \cdot 41 \cdot 59 \cdot 539$ | $4{,}107{,}099{,}165 < 2^{32}$ |
| 1/2 | $5n/8$ (degree $< n/2$) | $6u$ | 16 | $15 \cdot 41 \cdot 60 \cdot 135$ | $1{,}275{,}264{,}016 < 2^{31}$ |
| 1/4 | $[3n/8, 7n/16)$ | $[6u, 7u)$ | 63 | $15 \cdot 62 \cdot 62 \cdot 566$ | $65{,}793{,}289{,}023 < 2^{36}$ |
| 1/8 | $(n/4, 5n/16)$, $\epsilon = \tau - \frac14$ | $(4u, 5u)$ | 7 | $13 \cdot 28 \cdot 54 \cdot 1.934/\epsilon^2$ | $< 2^{21}/\epsilon^2$ ($2^{33}$ at $T = 17n/64$) |

The constants are far from the truth: the proof counts every 4-set of large Walsh coefficients as a possible neighbour. Under Law P of note 13 the cells have at most about $5 \cdot 15$ members at level-0 sizes, and in the exhaustive runs of section 7 the largest cell has 17 members in a field of 64 elements. What the theorem gives is a bound that does not depend on $n$, on the field, or on any classification of the formal classes. (A previous-level class itself has $56n - 392$ members for the word of note 02, grows with $n$ in every example of note 12, and is only known to have at most $2n^5 = 2^{126}$ members.) The bound degenerates as $\kappa \to 0$, that is at $T \to n/4$ at rate 1/8, as it must: at $T = n/4$ the previous-level class of a flat of size $n/4$ contains all $2^{53}$ such flats.

### 3.3 Rate 1/16

**Theorem 3c. [proved]** If $g \ge n/8$ and $3u \le s < 4u$, then $\lvert S_i \triangle S_j\rvert = 3n/8$ for all $i \ne j$ and
$$L \ \le\ \frac{3}{3 - \rho^2} = \frac{48u^2}{(12u - s)(4u - s)} .$$
If $s < 3u$ then $L = 1$.

*Proof.* $\lvert d^{ij}\rvert^2 = \lvert S_i \triangle S_j\rvert/u \le 2s/u < 8$, so it is 6 by Theorem 2. Then $\langle v_i, v_j\rangle = \rho^2 - 3 < 0$ because $s < 4u$, and the count of Lemma 3.1 gives $L \le 3/(3 - \rho^2)$. $\square$

At rate 1/16 the range is $T \in [3n/16, n/4)$ ($g = T - n/16 \ge n/8$): 5 at $3n/16$, 11 at $7n/32$, $6u/(4u - T)$ near $n/4$. The generic value is 1, section 5 shows that 2 occurs on $D_{24,4}$, and the value 5 is attained at $n = 16$ in $\mathrm{GF}(32)$ (section 7).

### 3.4 What these theorems say about a word

**Corollary 3.3. [proved]** Let $w$ be a monic polynomial of degree $T$ and $\mathcal{L}(w)$ the set of polynomials $c$ of degree $< T - g$ with $w - c = Z_S$ for a $T$-set $S \subseteq D$ (the strict common top list of $w$). Let $M(w)$ be the number of previous-level classes among these $S$. Then $\lvert\mathcal{L}(w)\rvert \le B\,M(w)$, with $B$ the bound of Theorem 3a, 3b or 3c for $(T, g)$. If the word is over an extension of $F$ or has several lanes, the same holds (a strict common top list has its locators in the field generated by $D$, note 13 section 3.5).

On a generic domain $M(w) = 1$ whenever $g \ge n/16$ (note 02 Theorem W and its converse). For $N = 4$, $M(w) = 1$ on every domain, because the previous level is the class of $e_1$, the sum. For $N \ge 5$ on a concrete domain, $M(w) = 1$ is the statement that no deep accident occurs.

## 4. Deep accidents: what the theorems leave out

### 4.1 Exact description

Let $S, S'$ be $T$-sets that share their top to depth $g \ge n/8$ on $D$ and are **not** in one previous-level class. Let $e'$ be the largest level with $c = 1_S - 1_{S'} \in L_{e'}$. Then $1 \le e' \le N - 4$ ($e_1$ is the sum, so $c \in L_1$), and by Theorem 1 with $e = e'$, since $g \ge 2^{e'+1}$:

**Proposition 4.1. [proved]** $\Omega' = \{\varphi : \hat c(\varphi)/2^{e'+1} \text{ odd}\}$ is the support of a nonzero Boolean function of degree at most $e' + 1$ on $D^\vee$ (so $\lvert\Omega'\rvert \ge 2^{N - e' - 1}$), and as a subset of $D^\star$ it satisfies the $e' + 1$ equations
$$\sum_{\varphi \in \Omega'} a_\varphi^{-(2^m - 1)} = 0 \quad (m = 1, .., e' + 1), \qquad\text{and}\qquad \sum_{\varphi \in \Omega'} a_\varphi^{t} = 0 \ \text{ for } t \ge 0 \text{ with at most } N - e' - 2 \text{ ones in binary.}$$
After that block the key of $c$ is no longer sparse (because $c \notin L_{e'+1}$), and the remaining conditions up to depth $g$ are those of the identity of Theorem 1, part 1, with no further reduction that I know. For $e' = N - 4$ the vanishing power sums include the exponents $-4, .., 6$, so $\lvert\Omega'\rvert \ge 12$ (as in Theorem 2) and $\lvert S \triangle S'\rvert = \frac u4\sum (\hat c/2u)^2 \ge 3n/16$.

This is the statement "a difference that is formally trivial to some depth, then a coincidence of $e' + 1$ field elements" of note 13, Corollary 3.2 part 3, in closed form: the $e' + 1$ field elements are the first $e' + 1$ inverse power sums $2^m - 1$ of a Reed-Muller codeword on the dual space. A distance of $3n/16$ is all it gives. No count follows from it, because nothing bounds the number of pairwise accidents in a list.

### 4.2 They exist in small fields

**[checked]** `19_ct32` ($n = 32$, all $s$-sets of a random 5-dimensional subspace): in $\mathrm{GF}(32)$ and $\mathrm{GF}(64)$ at depth $g = 4$, one real class meets up to 4 previous-level classes ($s = 6$), 7 ($s = 7$), 6 ($s = 8$), and the real class (8 members for $s = 7$ in $\mathrm{GF}(32)$) is larger than every cell (5). At depths 5, 6, 7 no real class met two previous-level classes in any of the 19 runs, in fields of 32 to 256 elements. So $M(w) > 1$ is a real phenomenon when $2^{64}$ is replaced by 32, and the factor $M(w)$ in Corollary 3.3 cannot be dropped by a field-independent argument.

### 4.3 Why I cannot exclude them in $K$

**[proved]** as statements about the structure.

1. *The linear part is never injective.* By Theorem 1 the map $\Theta^{(e')} : L_{e'}/L_{e'+1} \to F^{e'+1}$ is $\mathbb{F}_2$-linear on a space of dimension $\sum_{a=1}^{e'+1}\binom Na$ (the Reed-Muller code without constants). In $K$ the target has $64(e'+1)$ bits. At $N = 25$ the kernel has dimension at least 197 for $e' = 1$ and at least $2^{25} - 327 - 1408$ for $e' = 21$. So at every level there are integer differences that are accidentally trivial through the whole next block.
2. *The accident lattice is huge.* Let $I = \{c : \sum c = 0\}$ and $R_g = \{c \in I : \Lambda_c \equiv 1 \bmod X^{g+1}\}$. $I/R_g$ embeds in the units of $K[X]/X^{g+1}$, so $[I : R_g] \le 2^{64g}$, while $[I : L_{N-3}] = 2^{\sum_{a \le N-2}(N-2-a)\binom Na} = 2^{(N/2 - 2)n + 4}$. Hence for $g < (N/2 - 2)n/64$ ($0.164n$ at $N = 25$, $0.1875n$ at $N = 28$) $R_g \not\subseteq L_{N-3}$, and $R_g/(R_g \cap L_{N-3})$ has at least $2^{(N/2 - 2)n - 64g}$ elements ($2^{2.5n}$ at $g = n/8$, $N = 25$). Integer differences with a deep accident exist in abundance, by counting.
3. *What a proof must show* is that none of these lattice points is a difference of two $T$-sets (entries in $\{0, \pm1\}$), that is a statement about the short vectors of an explicit lattice of rank $n - 1$ and index $2^{64g}$ (equivalently about the $\{0, \pm1\}$-valued words of the Galois-ring code of note 13, Proposition 3.3). A count gives $3^n \cdot 2^{-64g} \le 2^{-6.4n}$ expected solutions, and a count is not a proof. Theorem 2 is a proof of exactly this kind at the last level only, where the dual object has at most 12 points and a Vandermonde determinant decides. At level $e'$ the dual object has at least $2^{N - e' - 1}$ points and $e' + 1$ equations, and the number of equations is far below the number of points.
4. *No finite verification helps.* The rank of $\Theta^{(e')}$ on the real domain is computable (a $1408 \times 2^{25}$ binary matrix at the top level), but its value says nothing about $\{0, \pm1\}$ solutions. A direct search is over pairs of $T$-sets.

So: **the number $M(w)$ of previous-level classes in a strict common top list is not bounded by anything in this note, on any concrete domain with $N \ge 5$.**

## 5. The real domain is not generic inside the windows

**Proposition 5.1. [proved, machine-checked finite case]** Let $D = D_{\kappa,R} \subset K$, $N = \kappa + R \in \{25, 26, 27, 28\}$, identified with the polynomials $f \in \mathbb{F}_2[x]$ of degree $< N$, and
$$V = \{f : f(0) = f(1) = f_{N-1}\}, \qquad V' = \{f : x^2 + x + 1 \text{ divides } f\} .$$
Then $\lvert V\rvert = \lvert V'\rvert = n/4$, $\lvert V \cap V'\rvert = n/16$, and $\deg(L_V - L_{V'}) \le n/16$. Equivalently the six points of $D^\star$ on the two planes $V^\perp, V'^\perp \subset D^\vee$ have $\sum 1/a = 0$. Their $\sum 1/a^3$ is not zero.

*Proof.* $L_V = X^{n/4} + c_1(V)X^{n/8} + c_2(V)X^{n/16} + \dots$, so the claim is $c_1(V) = c_1(V')$, an equality of two explicit elements of $K$ for each $N$. `19_real_pair.py` computes $c_1$ by the recursion $c_1(V_{i+1}) = c_1(V_i)^2 + L_{V_i}(b_{i+1})$ along a basis ($O(N^2)$ multiplications in $K$), and independently the six $\delta_\varphi$, for $N = 25..28$: $c_1(V) = c_1(V') =$ `cba43a67a8eb80e2`, `1ffceca7a13db23d`, `77ed94d3be30112c`, `cbca51b44a3f6baf`. $\square$

The coincidence also holds in $\mathbb{F}_2[x]/(x^{64} + x^4 + x^3 + x^2 + 1)$ and for every $N$ from 6 to 12 tried, so it is an identity of $\mathbb{F}_2(x)$ (tier 2 of note 13; it is the pair of planes that note 13 section 4.3 found by enumeration). For $N \le 9$ the script also multiplies out $Z_A$ and $Z_B$ below. **[checked]**

**Corollary 5.2. [proved, given 5.1]** Let $A = V \setminus V'$, $B = V' \setminus V$ ($3n/16$ points each). Then $Z_A - Z_B$ is a nonzero constant, and for every $C \subseteq D$ disjoint from $A \cup B$ the sets $A \cup C$ and $B \cup C$ share their top to depth $3n/16 - 1$ and no further. They are in one previous-level class and differ in $3n/8$ points, so they are not in one formal class at depth $\ge n/8$ (there the differences have $n/2$ points). On the real level-0 domains this gives monic words of degree $T$ with two codewords of degree $< k$ at agreement $T$ whose agreement sets are not a hyperplane swap:

| rate, $N$ | $T$ | sets | degree of the codewords | generic theory |
| --- | --- | --- | --- | --- |
| 1/2, 25 | every $T \in (5n/8, 11n/16)$ | $V \cup C$, $V' \cup C$, $\lvert C\rvert = T - n/4$, $C \cap (V \cup V') = \emptyset$ | $T - 3n/16 < n/2$ | every pair of a class is a hyperplane swap |
| 1/4, 26 | every $T \in [3n/8, 7n/16)$ | the same | $T - 3n/16 < n/4$ | the same |
| 1/8, 27 | every $T \in (n/4, 5n/16)$ | the same | $T - 3n/16 < n/8$ | the same |
| 1/16, 28 | every $T \in [3n/16, n/4)$ | $A \cup C$, $B \cup C$, $\lvert C\rvert = T - 3n/16$ | $T - 3n/16 < n/16$ | the list is 1 |

So the target "the real classes are the generic ones" is false on $D_{\kappa,R}$, for explicit words, in all four windows below the second position, and the correct real-domain statement in $[n/8, 3n/16)$ of depth has to allow distance $3n/8$: Theorem 3b and 3c are of the right shape. Above the second position the generic shape survives (Theorem 3a). This example does not make lists large: it merges classes in pairs, and note 13 found exactly one such pair of planes. Law P of note 13 predicts about $2^{51.5}$ weight-6 words in $D^\star$ at $N = 25$ in all (Remark 2.2), almost all of them wraps and none of them explicit.

## 6. Multisets, small phantom degree, lower ranges

**Remark 6.1 (multiset tops). [proved]** Theorems 1 and 2 are statements about integer differences and hold verbatim for multisets $\mu, \mu'$ of equal mass $M$ in one class modulo $L_{N-3}$ at depth $g = M - k$: $\sum_x(\mu - \mu')(x)^2 \ge 3n/8$ for $g \ge n/8$ and $\ge n/2$ for $g \ge 3n/16$. The count of Lemma 3.1 then gives, for a multiset top list inside one such class with $3n/16 \le g < n/4$ and second moments $\sum_x\mu_i(x)^2 \le E$:
$$L \ \le\ \frac{1}{1 - 4\bigl(E/n - (M/n)^2\bigr)} \qquad\text{whenever } E/n - (M/n)^2 < \tfrac14 .$$
For multiplicities at most 2 and supports of size $T$, $E = 3M - 2T$, and the condition holds for $M - T$ up to about $0.02n$ at $\tau = 0.69$. This is much weaker than Theorem A of note 12 (which needs no moment condition, on a generic domain): the Frobenius descent and parity lemmas of note 12 use congruences modulo $L_{N-2}$ and $L_{N-1}$, which on the real domain hold only when $\Omega = \emptyset$. I did not find a multiset analogue of Theorem 3b.

**Remark 6.2 (phantom degree below $n/8$, same class). [proved]** Let $w$ be monic of degree $T + r$ with $r < n/8$, and $c_i, c_j$ two list members with $w - c_i = Z_{S_i}g_i$, $\lvert S_i\rvert = T$, $\deg g_i = r$, and $S_i, S_j$ in one previous-level class. Then $g_i = g_j$ and $S_i, S_j$ share their top to depth $T + r - k$. (Proof: with $\hat g = X^r g(1/X)$, $\Lambda_{S_i}/\Lambda_{S_j} \equiv \hat g_j/\hat g_i \pmod{X^{T + r - k + 1}}$ and the left side is $1$ modulo $X^{n/8}$, so the polynomials $\hat g_i, \hat g_j$ of degree $\le r < n/8$ are equal.) So Theorem 3 applies to such members with the depth $g + r$. This does not bound the list of $w$: with phantom roots the members are not congruent modulo $L_{N-3}$ even on a generic domain (note 12 Theorem B: they differ from a hyperplane swap in up to $4r + 8r^2/n$ points), so the number of classes is the whole question.

**Remark 6.3 (the ranges one level down). [proved]** For rate 1/16 on $(n/8, 3n/16)$ and rate 1/2 on $(9n/16, 5n/8)$ the depth is in $[n/16, n/8)$ and the previous level is $L_{N-4}$. Theorem 1 with $e = N - 4$ and the Vandermonde argument give: two sets of one class modulo $L_{N-4}$ that share a top to depth $g \ge n/16$ and are not congruent modulo $L_{N-3}$ have $\lvert\Omega\rvert \ge 10$ (exponents $-2..6$) and $\lvert S \triangle S'\rvert \ge 5n/32$, and for $g \ge 3n/32$, $\lvert\Omega\rvert \ge 12$ and $\lvert S \triangle S'\rvert \ge 3n/16$. That is below what a Johnson-type count needs, and I have no bound on the cells there. (At rate 1/2 these cells contain the formal classes of $105n$ members of note 12 anyway.)

## 7. Checks

`19_ct32 s g m r seed`: all $s$-subsets of a 5-dimensional subspace of $\mathrm{GF}(2^m)$ ($n = 32$, $u = 2$), keyed exactly on $(e_1..e_g)$ and on $(n_\varphi \bmod 4)_\varphi$. A cell is (real class) $\cap$ (previous-level class). For every pair in a cell the program checks $P_1(\Omega) = 0$ (and $P_2$ if $g \ge 6$), $\lvert\Omega\rvert \in \{0\} \cup [6, \infty)$ (resp. $[8, \infty)$), the distance, and the cell size against Theorem 3a ($g \ge 6$) or 3c ($s < 8$). **[checked]**: no violation in 24 runs.

| $s$, $g$ | meaning ($n = 32$) | field sizes | largest cell | bound | largest real class | most classes in one real class | $\lvert\Omega\rvert$ seen |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 10, 6 | rate 1/2 $T = 22$; rate 1/8 $T = 10$ | 32, 64, 64, 128, 256 | 3 | 7 | 3 | 1 | 0, 8, 10 |
| 9, 6 | $s = 4.5u$, depth $3u$ | 32, 64 | 3 | 5 | 3 | 1 | 0, 8 |
| 11, 6 and 11, 7 | rate 1/8 $T = 11$ | 64, 256 | 3 | 10 | 3 | 1 | 0, 8, 10 |
| 12, 6 | rate 1/2 $T = 20$, degree $< 14$ | 64 | 7 | 16 | 7 | 1 | 0, 8, 10, 12 |
| 8, 6 | $s = 4u$ | 64 | 4 | 4 | 4 | 1 | 0, 8 |
| 11, 5 | rate 1/2 $T = 21$ | 64, 128, 256 | 17, 13, 10 | $2^{32}$ | 17 | 1 | 0, 6, 8, 10 |
| 9, 5 | rate 1/8 $T = 9$ | 64, 256 | 15, 9 | (3b) | 15 | 1 | 0, 6, 8 |
| 6, 4 and 6, 5 | rate 1/16 $T = 6$ | 32, 64, 64 | 2, 5, 5 | 5 | 4, 5, 5 | 4, 3, 1 | 6 |
| 7, 4 and 7, 5 | rate 1/16 $T = 7$ | 32, 64, 256 | 5, 5, 3 | 11 | 8, 5, 3 | 7, 1, 1 | 6 |
| 8, 4 | $s = 4u$, depth $2u$ | 64 | 20 | none | 20 | 6 | 0, 6, 8 |

`19_dual_check.py B` ($n = 16$, where the previous level is the sum and there are no deep accidents): the largest real classes over 23 domains are 5 for $s = 3$ at depth 2 (bound 5 of Theorem 3c, attained), 4 for $s = 4$ at depth 3 (bound 4, attained), 3, 7, 15 for $s = 5, 6, 7$ at depth 3 (bounds 7, 16, 64). **[checked]** So Theorem 3a and 3c are tight in small fields at $n = 16$ in two cells, and the bound of Theorem 3b is not approached anywhere.

## 8. Where the method stops

1. **Deep accidents** (section 4). The theorems bound a strict common top list only up to the number $M(w)$ of previous-level classes it meets. On a generic domain $M(w) = 1$. On $D_{\kappa,R}$ nothing bounds it, and in fields of 32 and 64 elements it exceeds 1. This is the same obstruction that note 13 stated ("a count is not a proof"), now with the dual object written down (Proposition 4.1). I see no way to turn the count into a proof: it is a shortest-vector statement.
2. **Arbitrary words.** The method is pairwise: it analyses the difference $c = 1_{S_i} - 1_{S_j}$ of two agreement sets through its Walsh transform, and it needs that difference to have a trivial key. With phantom degree $r$ the key of $c$ only has to be the key of a ratio $\hat g_j/\hat g_i$ of two polynomials of degree $r$, and for $r \ge T - k$ every key is of that form (note 12 section 4.1), so no pairwise statement survives, on any domain. Remark 6.2 is the only thing left for small $r$. So this method can never reach arbitrary words. The Gold family at rate 1/4 and $T = 3n/8$ (note 01) is an instance: its word has degree $n/2$, it is not a strict common top, and Theorem 3b at $s = 6u$ says nothing about it. It is also blind to the reason phantom roots matter on the real domain: a phantom root in $K \setminus D$ is not a point of $D$, and the dual space $D^\star$ has no place for it.
3. **Constants in $[n/8, 3n/16)$.** $2^{32}$ and $2^{36}$ come from counting 4-sets of large Walsh coefficients. A classification of the previous-level classes in the window (note 12, Conjecture 5.3) would replace them by a Bezout count as in note 13, Proposition 4.1 (in the dual language: if the six-point supports of a class are of the form "fixed points plus $b + \{$fixed points$\}$" for one free $b$, then $\sum 1/a$ is a rational function of $a_b$ of degree at most 10 and each value is taken at most 10 times). I did not need the classification and did not attempt it.
4. **Below the first dyadic point of each window** (Remark 6.3): only a distance bound.
5. **Usefulness for the protocol.** The DEEP-fold hypothesis of note 11 is ListBound for all words. These theorems cover the list members that are (i) strict common tops and (ii) congruent modulo $L_{N-3}$. They confirm, with proofs valid on $D_{\kappa,R}$, two predictions of note 13 that the design relies on: above the second position ($11n/16$ at rate 1/2, $5n/16$ at rate 1/8, $7n/16$ at rate 1/4) the non-formal coincidences inside a class cannot increase the Johnson-type constant at all, and between the positions they cost at most a factor that does not grow with $n$. They also show that the generic rigidity statement itself is false on $D_{\kappa,R}$ (Proposition 5.1), so any future real-domain theorem in the lower zones must be stated with distance $3n/8$, not $n/2$.

## 9. Reproduction

All under `doc/whir_soundness_gap_notes/scripts/`. C with the system compiler, Python 3 without dependencies. `19_run_all.sh [builddir]` rebuilds and reruns everything (about 4 minutes on four cores, 3 GB), `19_results.txt` is its output.

| script | what it does | time |
| --- | --- | --- |
| `19_dual_check.py A` | Theorem 1 (parts 2, 3, 4) and Lemma 1.1 on random lattice elements, $N = 5, 6$, six domains | 1 s |
| `19_dual_check.py B` | $n = 16$, 23 domains, all pairs of equal-sum sets: Corollary 1.3 as an equivalence, Theorem 2, Theorems 3a and 3c | 65 s |
| `19_ct32.c` | $n = 32$ exhaustive in $\mathrm{GF}(2^m)$, $m \le 9$: Theorems 2, 3a, 3c inside cells, and the deep-accident statistic (uses `13_gf.h`) | 2 to 40 s per run, up to 3 GB |
| `19_real_pair.py` | Proposition 5.1 on $D_{\kappa,R}$, $N = 25..28$, and by multiplying out $Z_A, Z_B$ for $N \le 10$ | 1 s |
