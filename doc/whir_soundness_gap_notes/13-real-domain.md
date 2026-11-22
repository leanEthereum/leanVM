# 13. The real domain: decisive experiments, the pigeonhole law, provable handles

Researcher 13 (round 2). Every statement is tagged **[proved]** (proof in this note), **[checked]** (numerically, sizes stated), **[quoted]** (from another note or the literature) or **[conjectured]**. Scripts are `scripts/13_*`, section 9 says how to run them.

Notation as in `09-round1-synthesis.md`. In addition: $F$ is a field of characteristic two of degree $m$ over $\mathbb{F}_2$ ($m = 64$ for $K$), $D \subset F$ an $\mathbb{F}_2$-subspace of dimension $N$, $n = 2^N$, $k = \rho n$. For $c \in \mathbb{Z}^D$ (a difference of multisets) $\Lambda_c(X) = \prod_{s \in D}(1 - sX)^{c(s)} \in F[[X]]$ and $\hat c$ is its Walsh transform. Two $T$-sets $S, S'$ share $e_1, \dots, e_g$ iff $\Lambda_{1_S - 1_{S'}} \equiv 1 \pmod{X^{g+1}}$. "Depth $g$" always means this. $L_e = \{c : \sum c = 0,\ \hat c \equiv 0 \bmod 2^{e+1}\}$ is the lattice of differences that are trivial to depth $2^e - 1$ on every domain (Theorem W of note 02). $D^\star = \{0\} \cup \{1/\delta_H\}$, $\delta_H = \prod_{d \in D \setminus H} d$ over the hyperplanes $H$ of $D$, is the dual space: an $N$-dimensional $\mathbb{F}_2$-space indexed additively by the functionals of $D$ (note 05, Proposition 4.1). The **power shape** is $D = \mathrm{span}(1, x, \dots, x^{N-1})$ in $\mathbb{F}_2[x]/(f)$ with $f$ the lowest irreducible polynomial of degree $m$ (for $m = 64$ this is leanVM's $x^{64} + x^4 + x^3 + x + 1$). The **scaled family** is the power shape with $m = \mathrm{round}(2.56 N)$.

## 0. Summary

**Answer to the brief.** The evidence supports Conjecture C of note 04 and does not refute it. The non-generic part of the lists on the real domain is a pigeonhole term that I can now state exactly (it is a theorem that the term has this form, section 3), that fits every measurement to within statistical error (sections 4 and 5), and that is zero or a small constant in the windows of Conjecture C at the real parameters, with one exception that was already known: rate 1/16 below $0.153n$. There is still no route to a proof of ListBound for all words on any concrete domain. Two things are new on the provable side: an exact description of the real-domain classes inside each formal class, valid on every domain (Proposition 3.1), and an unconditional bound, independent of $n$, for the one family that note 04 singled out as the decisive test (Proposition 4.1).

| | result | status |
| --- | --- | --- |
| 3.1 | **Sparse top keys.** If $c \in L_e$ then $\Lambda_c \equiv 1 + \sum_{i=0}^{e} \theta_i(c) X^{2^{e+1} - 2^{e-i}} \pmod{X^{2^{e+1}}}$ with additive $\theta_i$. Inside a class that is formal to depth $2^e - 1$, the real classes at depth $g < 2^{e+1}$ are the fibres of a map to $F^{i(g)}$, $i(g) = \#\{i : 2^{e+1} - 2^{e-i} \le g\}$: one field element for $g < 1.5 \cdot 2^e$, two for $g < 1.75 \cdot 2^e$ | any domain, any multisets. proved, checked |
| 3.2 | Hence pigeonhole is exact: a formal class $\mathcal{F}$ contains a real list of at least $\lvert\mathcal{F}\rvert / 2^{64 i(g)}$ members, and two members outside a common formal class of the previous level need at least $64(e'+1)$ bits of coincidence | proved |
| 3.3 | Exact criterion on the real domain: $S, S'$ share $e_1..e_g$ iff $\sum_S \tau(s)^j \equiv \sum_{S'} \tau(s)^j \pmod{2^{\ell_j}}$ in $W(K)$ for all odd $j \le g$ ($\tau$ the Teichmüller lift, $\ell_j = 1 + \lfloor \log_2(g/j) \rfloor$) | quoted (Artin-Hasse), checked $n = 16$ |
| 3.4 | **Interleaved words reduce to one or two lanes.** A bound $2^b$ for single $K$-valued words gives $2^{b+1}$ for every number of lanes and every extension of $K$ if $b \le 62$; a bound for single $E$-valued words does the same up to $b = 126$. So the hypothesis of note 11 (all lane counts, extensions of degree up to 128) needs no separate pigeonhole analysis | proved |
| 3.5 | $\Lambda_{K^2}(T) \le \Lambda_K(T)(1 + \Lambda_K(2T - d))$, and $\le 2\Lambda_K(T)$ for $T > (n + 3d)/4$ (at rate 1/2: above $5n/8$) | proved |
| 4.1 | **The $5n/8$ class cannot have growing fibres.** For every $U$, every $N$ and every subspace domain of every field, each value of $e_{n/8}$ is taken by at most 3591 of the $56n - 392$ members | proved |
| 4.1 | On the real domain $D_{24,1} \subset K$ ($N = 25$): for 18 subspaces $U$ the 1.88 billion members split into fibres of at most 7 (the formal value), with no coincidence at all for 16 random $U$ and 24 structural pairs (fibres of 4) for $U = \mathrm{span}(1..x^{21})$ and for $x^3$ times it | checked at the real size |
| 4.1 to 4.2 | Random model for the pigeonhole term on the scaled real shape, $N = 8$ to $20$: observed over predicted coincidences $1.031$ ($5n/8$ class, $10^5$ events), $1.0003$ and $1.0013$ (second coefficient of codimension-2 flats, $N = 15, 16$), $1.0000$ (codimension-3 flats, $N = 12$, $4 \cdot 10^7$ events; also with mean fibre 777), $1.0000$ (pairs of flats), $1.006$ (Gold, $N = 16$) | checked |
| 4.3 | Three tiers: formal $\subset$ $\mathbb{F}_2(x)$-identities $\subset$ real. The middle tier (coincidences that survive two moduli) is $O(1)$ and constant in $N$: 1 pair (codimension-2 flats, $N = 6..16$), 3 pairs (codimension 3), 246 pairs with fibres $\le 6$ (pairs of flats), 0 (Gold), 24 pairs (the $5n/8$ class of the two "ideal" $U$, $N = 7..25$), 0 for random $U$ once $N \ge 9$ | checked |
| 4.4 | $n = 32$ is not representative: there the middle tier dominates (103 structural pairs per $U$ at $N = 5$, 9 at $N = 6$, 1 at $N = 7$, 0.04 at $N = 8$). This is the source of the "13 against 7" of note 04 | checked |
| 5, 6 | Law and extrapolation, tables below | conjectured, fitted |

**Predicted lists at level 0 on the real domain** (section 6). "Formal" is the generic-domain value of notes 02, 04, 05, which round 2 is still working on below the first dyadic point. The column for $K$-valued single words is the prediction of Law P. The next column is what it implies for interleaved words with any number of lanes and for words over any extension of $K$: one more bit by Proposition 3.4 wherever the list is below $2^{62}$, and the bound of Proposition 3.5 in the two cells above $2^{62}$. $t$ is the query count at the lower end of the range for a budget that covers the interleaved list.

| rate, $N$ | range of $T/n$ | pigeonhole term | $\log_2 \Lambda$, $K$-valued single words | $\log_2 \Lambda$, any lanes, any extension | $t$ |
| --- | --- | --- | --- | --- | --- |
| 1/2, 25 | $(0.632, 0.707)$ | none (expected accidental pairs per word $2^{-5}$; over all words a factor $\le 3$) | $\le 10$ (formal multiset tops dominate) | $\le 11$ | 164 (168 at $0.64$) |
| 1/2, 25 | $5/8$ to $0.632$ | none | $27.8$ to $30.8$ at $5/8$, falling to 10 | $\le 32$ | 160 |
| 1/2, 25 | $(9/16, 19/32)$ | $2^{38.7 - 1.1 j}$ at $T = 9n/16 + j$ (proved to exist), at most about $2^{38.7}$ in the range | $\max(38.7, \text{formal})$ | one more bit if below 62 | 131 |
| 1/2, 25 | $9/16$ | (formal) | $102.7$ | $103$ to $113$ | 131 |
| 1/4, 26 | $(3/8, 1/2)$ | Gold at $7/16$: $2^{13.5}$; flats: factor $\le 4$ | $27$ (the hyperplanes) | $28$ | 77 |
| 1/4, 26 | $3/8$ | Gold: $2^{34.5}$ | $34.5$ | $35.5$ | 77 |
| 1/8, 27 | $(1/4, 0.354)$ | none ($\le 16$ members) | $\le 5$ | $\le 6$ | 55 |
| 1/8, 27 | $1/4$ | none | $53.4$ (flats) | $54.4$ | 54 |
| 1/16, 28 | $(0.153, 1/4)$ | pairs up to $0.172$, then nothing | $\le 6$ | $\le 7$ | 40 |
| 1/16, 28 | $(1/8, 0.153]$ | $2^{15.6}$ (proved to exist) | $15.6$ | $16.6$ | 37 |
| 1/16, 28 | $1/8$ | none | $79.6$ (flats) | $80.6$ to $87$ | 36 |

Against 218, 109, 73, 55 deployed. Since the list budget is cheap in the DEEP-fold design (note 11: about 35 bits of list per extra point) what matters is the smallest $\tau$ at which the list is finite and known, and the table says where the real domain differs from the formal picture: nowhere at the thresholds $5/8$ (rate 1/2), above $3/8$ (rate 1/4), $1/4$ (rate 1/8) and $1/8$ (rate 1/16); by Gold's $2^{34.5}$ at $3/8$ exactly (rate 1/4); by a term $2^{15.6}$ just above $1/8$ at rate 1/16; and by a term $2^{38.7}$ just above $9/16$ at rate 1/2. All three are far inside a budget of $2^{100}$. Confidence: high that the pigeonhole term is right for words whose agreement sets are locator-type (strict or multiset tops), since that part is a theorem plus a random model verified to three digits, and Proposition 3.4 carries it to all lanes and extensions; none for words with many phantom roots outside $D$, which no experiment in this project reaches. What would falsify it is listed in section 6.5.

**Provable handles** (section 7): (i) no domain choice makes ListBound provable. Evaluation points in $E$ make every exposed coefficient worth 128 bits (all pigeonhole terms above vanish) at about the cost of halving the rate, which already buys a proof. (ii) Character sums and the Li-Wan sieve cannot work for $T - k = \Theta(n)$: their error term is at least $2^{\Omega(\sqrt n \log n)}$ even under perfect square-root cancellation, and on our domain no cancellation is available at all because $n < \sqrt{\lvert K \rvert}$. (iii) No hypothesis of the form "no sparse relation among low-degree monomials" can carry the generic proof. What is finite and checkable is the injectivity of the explicit maps $\theta_i$ on explicit formal classes, and for one-parameter classes this is even provable (Proposition 4.1). The precise obstruction to more: for families with two or more parameters the fibres are sets of points of a curve in a product of small subspaces, where nothing is known.

## 1. Three tiers, and what "scaled down" has to preserve

A coincidence $e_j(S) = e_j(S')$ on the power shape can hold for three reasons.

1. **Formal.** It is an identity in the basis elements: it holds on every domain. Notes 02, 04, 05 classify these for strict common tops.
2. **An identity of $\mathbb{F}_2(x)$.** On the power shape $D$ is the set of polynomials of degree $< N$, $e_j(S)$ is a polynomial in $x$, and two of them can be equal as polynomials without being formally equal. Such a coincidence holds for every modulus $f$ and every $m$. It reflects the arithmetic of $\mathbb{F}_2[x]$: $D$ is stable under $x \mapsto x + 1$ and under reversal, it contains the "ideals" $g \cdot \mathrm{span}(1..x^{s-1})$, and $L_D$ is a Carlitz polynomial.
3. **Wrap.** The two polynomials differ and are congruent modulo $f$. This is the only tier that depends on $m$, and it is what "64 bits per coefficient" refers to.

The tiers are separated experimentally by computing every key in two fields at once, $\mathbb{F}_2[x]/(f_1)$ and $\mathbb{F}_2[x]/(f_2)$ with the same polynomials for the domain: a coincidence in both is an identity of $\mathbb{F}_2(x)$ up to an error $2^{-(m_1 + m_2)}$ per pair. With two random bases instead, two fields give the formal tier.

For tier 3 a scaled instance is in the regime of the real one when $\log_2(\text{family size})/m$ is the same, not when $n$ is: for the families that matter the size is $2^{aN + O(1)}$ with $a \in \{1, 2, 3\}$, so $m/N = 64/25$ is the right thing to preserve, and $N = 8$ to $20$ is enough to see the law. Tier 2 does not scale that way: it is large at $N = 5$ and gone at $N = 9$ (section 4.4), and this is why the exhaustive $n = 32$ tables of notes 02 and 04 overstate the non-generic part.

## 2. The $5n/8$ class: its next coefficient

Let $U \le D$ with $\lvert U \rvert = n/8$. For a hyperplane $W$ of $U$ let $\eta_W$ be the nonzero element of $L_W(U)$, $\Lambda_W = L_W(D)$ (16 labels), and for a 10-subset $Y \subseteq \Lambda_W$ with $\sum Y = \eta_W$ let $S = L_W^{-1}(Y)$. These $56n - 392$ sets share $e_1, \dots, e_{n/8-1}$ (note 02, Theorem 5). The members that share one genuine word at agreement $5n/8$ are those that also share $e_{n/8}$.

**Lemma 2.1. [proved]** $e_{n/8}(S) = e_2(Y)$, the second elementary symmetric function of the ten labels.

*Proof.* $Z_S = \sum_{i=0}^{10} e_i(Y) L_W^{10-i}$ and $L_W = \sum_{j \le N-4} c_j X^{2^j}$, $\lvert W \rvert = n/16$. The coefficient of $X^{n/2}$: $L_W^{10} = L_W^8 L_W^2$ has exponents $8 \cdot 2^j + 2 \cdot 2^l$ with $j, l \le N - 4$, never equal to $n/2$; $L_W^9 = L_W^8 L_W$ has exponents $8 \cdot 2^j + 2^l$, never $n/2$; $L_W^8$ contributes 1; the terms $i \ge 3$ have degree $\le 7n/16$. $\square$

Choose $v_1, v_2, v_3$ spanning $D$ modulo $U$ and coordinates $(\eta_W; \beta_1, \beta_2, \beta_3)$ on $\Lambda_W$, $\beta_i = L_W(v_i) = \eta_W t_i$. Then $t_i^2 + t_i = \lambda_i \alpha_W$ with $\lambda_i = L_U(v_i)$ (independent of $W$) and $\alpha_W = \eta_W^{-2}$, and **both $\alpha_W$ and $t_i$ are additive in the functional of $U$ that defines $W$** (the polynomial $L_W/\eta_W$ is the linearized polynomial of that functional, and three such polynomials whose functionals sum to zero vanish on $U$, which has more points than their degree). **[proved]** So all $n/8 - 1$ hyperplanes are reached by a Gray code, and
$$e_{n/8}(S) = \eta_W^2\, Q_{c(Y)}(1, t_1, t_2, t_3), \qquad Q_c = \sum_{0 \le i \le j \le 3} c_{ij} t_i t_j,\ t_0 = 1,$$
where $c(Y) \in \mathbb{F}_2^{10}$ is the formal class of $Y$: $c_{ii} = \binom{n_i}{2}$, $c_{ij} = n_i n_j - n_{ij} \bmod 2$, with $n_i$ ($n_{ij}$) the number of labels of $Y$ whose coordinate $i$ (coordinates $i$ and $j$) is 1. **[proved]** The 504 label sets fall into 232 formal classes: 8 classes of 7 sets, which are the 56 sets invariant under $U$ and whose key does not depend on $W$, and 224 classes of 2 sets. **[checked]** by enumeration; this is the "at most 7, attained" of note 02, Proposition 6.

`13_class58 -check` verifies all of this by brute force (the locator of $S$, coefficient by coefficient) for $N = 7, 8, 9$ on power and random shapes, in $K$ and in $\mathrm{GF}(2^{20})$, $\mathrm{GF}(2^{23})$: the common top, Lemma 2.1, the formula with $Q_c$, and the additivity. **[checked]** The main loop also asserts at every hyperplane that the keys of the invariant classes have not moved.

## 3. Exact structure, on every domain

### 3.1 Sparse top keys

**Proposition 3.1. [proved]** Let $D$ be an $\mathbb{F}_2$-subspace of any field $F$ of characteristic two, $0 \le e \le N - 1$, and $c \in L_e$. Then
$$\Lambda_c(X) \equiv 1 + \sum_{i=0}^{e} \theta_i(c)\, X^{2^{e+1} - 2^{e-i}} \pmod{X^{2^{e+1}}},$$
and $\theta_0, \dots, \theta_e : L_e \to F$ are additive and vanish on $L_{e+1}$. With a basis $b_1..b_N$ of $D$ and $\varepsilon_A = \prod_{i \in A}([b_i] - [0])$ (the signed indicator of the cube spanned by $A$), $L_e$ is generated by the $2^{e+1-\lvert A \rvert}\varepsilon_A$ with $1 \le \lvert A \rvert \le e + 1$ and the $\varepsilon_A$ with $\lvert A \rvert > e + 1$, and
$$\theta_i\bigl(2^{e+1-a}\varepsilon_A\bigr) = \bigl(\delta_A\, c_i(H_A)\bigr)^{2^{e+1-a}} \ (i < a = \lvert A \rvert), \qquad 0 \ (i \ge a),$$
where $H_A$ is the even-weight hyperplane of $\mathrm{span}(A)$, $L_{H_A} = X^q + c_1 X^{q/2} + \dots + c_{a-1} X$ with $q = 2^{a-1}$, $c_0 = 1$, and $\delta_A = L_{H_A}(b)$ for any $b \in A$.

*Proof.* The generators are those of Theorem W (i) of note 02. $\varepsilon_A$ is the indicator of one coset of $H_A$ in $\mathrm{span}(A)$ minus the other, and $\Lambda_{H} = L_H^{\mathrm{rev}} := X^q L_H(1/X)$, $\Lambda_{d + H} = L_H^{\mathrm{rev}} + L_H(d) X^q$. So $\Lambda_{\varepsilon_A}^{\pm 1} = 1 + \delta_A X^q / L_{H_A}^{\mathrm{rev}}$, and modulo $X^{2q}$ both signs give $1 + \delta_A X^q (1 + c_1 X^{q/2} + c_2 X^{3q/4} + \dots + c_{a-1} X^{q-1})$, because $L^{\mathrm{rev}} = 1 + u$ with $u = O(X^{q/2})$ and $1/(1 + u) \equiv 1 + u \pmod{X^q}$ in characteristic two. For $a > e + 1$ this is $1$ modulo $X^{2^{e+1}}$. For $a \le e + 1$ raise to the power $2^{e+1-a}$: Frobenius multiplies exponents by $2^{e+1-a}$, so the positions become $2^e(2 - 2^{-i})$, $i < a$. Finally the product of two series of the form $1 + O(X^{2^e})$ is additive modulo $X^{2^{e+1}}$. $\square$

In words: once a difference is formally trivial to depth $2^e - 1$, the next dyadic block of its key is not $2^e$ field elements. It is at most $e + 1$ of them, at the positions $2^e, \tfrac32 2^e, \tfrac74 2^e, \dots$, and they depend additively on the difference. In the formal model the same holds with values in $\mathbb{F}_2[b]$ in place of $F$.

**[checked]** `13_sparse_key_check.py`, part A: random integer combinations of generators, $N = 5, 6$, power and random shape in $K$, all levels $e = 1..N-2$, 88 pairs: the support is as stated and $\theta(c + c') = \theta(c) + \theta(c')$.

### 3.2 What this gives

Let $\mathcal{F}$ be a set of multisets on $D$ of the same mass that are pairwise congruent modulo $L_e$ (by Theorem W they share their top to depth $2^e - 1$ on every domain: a formal class of level $e$), $m_0 \in \mathcal{F}$, and for $2^e \le g < 2^{e+1}$ let $i(g) = \#\{i \ge 0 : 2^{e+1} - 2^{e-i} \le g\}$ and $\Theta_g(m) = (\theta_i(m - m_0))_{i < i(g)} \in F^{i(g)}$.

**Corollary 3.2. [proved]**

1. $m, m' \in \mathcal{F}$ share their top to depth $g$ on $D$ iff $\Theta_g(m) = \Theta_g(m')$. So the classes of the real domain inside $\mathcal{F}$ are the fibres of one explicit map to $F^{i(g)}$, and each is a union of formal sub-classes (the fibres of the same map with formal values).
2. (Pigeonhole, a lower bound.) Some class at depth $g$ has at least $\lvert \mathcal{F} \rvert / \lvert F \rvert^{i(g)}$ members. If $\mathcal{F}$ consists of $T$-sets and $g = T - k$ this is a list of that many genuine codewords at agreement $T$. For multisets of mass $M$ take $g = M - k$ and the agreement is the size of the support.
3. (Deep accidents.) If two $T$-sets share their top to depth $g \ge 2^{e'+1}$ on $D$ and their difference lies in $L_{e'} \setminus L_{e'+1}$, then all $e' + 1$ values $\theta^{(e')}_i$ of the difference vanish: $(e'+1)\log_2\lvert F\rvert$ bits of coincidence, before anything is asked of the later blocks.

So the cost of a non-formal coincidence is exactly $i(g) \in \{1, 2, 3, \dots\}$ field elements for pairs inside a formal class of the previous level, and at least $e' + 1$ field elements (22 or more at level-0 sizes) otherwise. This is the accounting of note 04, section 3.4, as a theorem, with "the number $c$ of coefficients that are not formally constant" identified: $c = i(g)$.

Values of $i(g)$ in the windows ($e$ is the level whose block contains $g = T - k$):

| rate | $T/n$ | block | $i(g)$ |
| --- | --- | --- | --- |
| 1/2 | $(9/16, 19/32)$, $[19/32, 39/64)$ | $[n/16, n/8)$ | 1, 2 |
| 1/2 | $[5/8, 11/16)$, $[11/16, 0.707)$ | $[n/8, n/4)$ | 1, 2 |
| 1/4 | $[3/8, 7/16)$, $[7/16, 15/32)$ | $[n/8, n/4)$ | 1, 2 |
| 1/8 | $[1/4, 5/16)$, $[5/16, 11/32)$, $[11/32, 0.354)$ | $[n/8, n/4)$ | 1, 2, 3 |
| 1/16 | $[1/8, 5/32)$, $[5/32, 11/64)$, $[11/64, 23/128)$ | $[n/16, n/8)$ | 1, 2, 3 |
| 1/16 | $[3/16, 1/4)$ | $[n/8, n/4)$ | 1 |

**A consequence at rate 1/2. [proved, given the count $M_3$ quoted in note 01 from [DKTZ26]]** Let $W$ be a subspace of size $n/16$ and $\mathcal{A}$ the $M_3(N)$ supports of height-3 trees avoiding $W$ ($2^{102.7}$ at $N = 25$). Averaging over $j$-subsets $J$ of $D \setminus W$, some $J$ is avoided by at least $M_3 \binom{7n/16}{j}/\binom{15n/16}{j} \approx M_3 (7/15)^j$ supports. The sets $W \cup J \cup A$ have $9n/16 + j$ points and form a formal class of level $N - 4$, and for $j < n/32$ the depth $g = n/16 + j$ has $i(g) = 1$. So on $D_{24,1} \subset K$ some word has at least $2^{38.7 - 1.1j}$ genuine codewords (degree $< n/2$) at agreement $9n/16 + j$, for every $j \le 26$ or so. These lists are not formal and not explicit. They matter for the choice of a threshold just above $9n/16$: the budget there is at least $2^{38}$ whatever the formal classification of round 2 gives.

### 3.3 The exact criterion on the real domain

**Proposition 3.3. [quoted: the Artin-Hasse decomposition of the big Witt vectors; checked]** Let $F$ be a perfect field of characteristic two, $W(F)$ its Witt vectors, $\tau : F \to W(F)$ the Teichmüller lift. For $c \in \mathbb{Z}^D$,
$$\Lambda_c \equiv 1 \pmod{X^{g+1}} \iff \sum_{s} c(s)\, \tau(s)^j \equiv 0 \pmod{2^{\ell_j}} \ \text{ for every odd } j \le g, \qquad \ell_j = 1 + \lfloor \log_2 (g/j) \rfloor .$$

Reason: $1 + XF[[X]]$ under multiplication is the group of big Witt vectors of $F$, which splits as a product over odd $j$ of copies of $W(F)$, the truncation modulo $X^{g+1}$ is the truncation of the $j$-th copy modulo $2^{\ell_j}$, and $1 - sX$ goes to $(-\tfrac1j \tau(s)^j)_j$. **[checked]** `13_sparse_key_check.py`, part B: in $\mathrm{GF}(2^8)$ and $\mathrm{GF}(2^{10})$ with $n = 16$ (where accidental coincidences abound), the partition of all $T$-subsets by $(e_1..e_g)$ equals the partition by the Teichmüller power sums in the Galois ring, for all $T = 3..9$ and $g = 1..7$ (98 cells).

This is the statement that replaces "Walsh spectra congruent modulo $2^{a+2}$" on a domain that is not generic. The mod-2 part ($\ell_j = 1$ for all $j$) is the binary alternant code $B_m$ of note 04, Proposition 3.1. The full statement says that $1_S - 1_{S'}$ lies in a BCH-type code over $\mathbb{Z}/2^{a+1}$ defined over the Galois ring $W(K)/2^{a+1}$ and punctured to $D$, in the family of the $\mathbb{Z}_4$-linear Kerdock and Preparata codes. ListBound for strict common tops is a statement about the words of that code with entries in $\{-1, 0, 1\}$. I could not use it beyond Proposition 3.1 (which is its structure on $L_e$), and section 7.2 explains why its character sums do not help.

### 3.4 Interleaved words and words over extensions

Note 11 needs ListBound for interleaved words with any number of lanes, equivalently for single-lane words over every extension of $K$ of degree up to 128 (its Remark D0), and observes that a bound for $K$-valued or $E$-valued words alone is not enough. With a factor 2 it is enough:

**Proposition 3.4 (reduction to one or two lanes). [proved]** Let $D \subset K$, let $F'$ be any finite-dimensional $K$-vector space of values (an extension of $K$ of any degree, $K^h$ or $E^h$ for any number of lanes $h$), and let $s \ge 1$. If every $s$-lane word over $K$ has at most $2^b$ list members at agreement $T$ and $b \le 64s - 2$, then every word $D \to F'$ has fewer than $2^{b+1}$. In particular: a bound $2^b \le 2^{62}$ for single $K$-valued words gives $2^{b+1}$ for all lane counts and all extensions, and a bound $2^b \le 2^{126}$ for single $E$-valued words (two lanes over $K$) does the same.

*Proof.* Take a list of $L$ members $c_i \in F'[X]$ with agreement sets $S_i$ and a uniformly random $K$-linear $\lambda : F' \to K^s$. Since $D \subset K$, $\lambda$ commutes with evaluation on $D$, so $\lambda c_i$ (coefficientwise) has degree at most $d$ and agrees with $\lambda \circ w$ on $S_i$. For $i \ne j$ some coefficient $\gamma$ of $c_i - c_j$ is nonzero and $\Pr[\lambda\gamma = 0] = \lvert K \rvert^{-s}$. So some $\lambda$ has at most $\binom{L}{2}/2^{64s}$ colliding pairs, and the number of distinct $\lambda c_i$ is at least $L$ minus that. For $L = 2^{b+1}$ this is $2^{b+1}(1 - 2^{b - 64s}) > 2^b$. $\square$

(Note 04, Proposition 1.1, is the case $s = 1$ without collisions, hence its limit $2^{32}$.)

### 3.5 Two lanes against one, and which words each statement covers

**Proposition 3.5 (two lanes against one). [proved]** $\Lambda_{K^2}(T) \le \Lambda_K(T)\,(1 + \Lambda_K(2T - d))$, where $d$ is the degree bound. If $2T - d > (n + d)/2$, that is $T > (n + 3d)/4$, then $\Lambda_{K^2}(T) \le 2\Lambda_K(T)$.

*Proof.* Group the pairs $(c^1_i, c^2_i)$ by their first component. If two members share it, their second components differ and agree on $S_i \cap S_{i'}$, so $\lvert S_i \cap S_{i'} \rvert \le d$ and the common first component agrees with the first lane on $\lvert S_i \cup S_{i'} \rvert \ge 2T - d$ points. There are at most $\Lambda_K(T)$ first components, at most $\Lambda_K(2T - d)$ of them are shared, and each is shared by at most $\Lambda_K(T)$ members (their second components are a list of the second lane). Beyond half the minimum distance there is one codeword. $\square$

At rate 1/2 the condition $T > (n + 3d)/4$ is $T > 5n/8 + 3\ell/4$: in the whole window of Conjecture C(a), interleaved lists are at most twice (two lanes) or four times (any lanes, by 3.4 with $s = 2$) the single-lane lists over $K$, with no restriction other than a final size below $2^{126}$.

**Which statements of this note cover which words.**

| statement | (a) $K$-valued single words | (b) words over any extension | (c) any number of lanes |
| --- | --- | --- | --- |
| Proposition 3.1, Corollary 3.2, Proposition 3.3, Lemma 2.1, Proposition 4.1 | yes | yes | yes |
| the experiments of section 4 | yes | yes | yes |
| Law P and the predictions of section 6, when the predicted list is at most $2^{62}$ | yes | yes, with a factor 2 (Proposition 3.4) | yes, with a factor 2 |
| predictions above $2^{62}$ (rate 1/16 at $n/8$, rate 1/2 at $9n/16$) | yes | through Proposition 3.5, with the loss stated in section 6 | the same as (b), by Proposition 3.4 with $s = 2$ |

The first two rows hold for every alphabet for a simple reason: they are statements about agreement sets. A list whose members are $w - c_i = \lambda Z_{S_i}$, or $Z_{m_i}$ for multisets on $D$, has locators in $K[X]$ whatever field or lane count the word has, and an $h$-lane common top is a single-lane common top times a constant vector. The pigeonhole term therefore does not grow with the extension degree: the conditions are equalities of elements of $K$, and a larger value field only adds conditions on the phantom part. What Proposition 3.4 adds is that this is true of *all* lists, not only of locator-type ones: any list over any extension or lane count, of size up to $2^{62}$, projects to a list over $K$ with the same agreement sets and at least half the members. So there is no "large extension" pigeonhole to evaluate separately. The only genuinely interleaved effect is the product structure of Proposition 3.5 (one lane close to a codeword on a large set, a list of the other lane inside that set), and it needs single-lane lists at agreement $2T - d$.

### 3.6 Dictionary: which statistic governs which family

All the families of notes 01 and 05 that carry a pigeonhole are covered by Proposition 3.1, and their $\theta_0$ is a statistic of the dual space $D^\star$:

- One free flat of size $Q = 2^{e+1}$ plus a fixed multiset $B$, members $1_{a+V} + B$: $\theta_i = c_{i+1}(V) - c_{i+1}(V')$, where $L_V = X^Q + c_1 X^{Q/2} + c_2 X^{Q/4} + \dots$. By note 05, Proposition 4.1, for $V$ of codimension $r$, $c_1(V)^{2^r} = \mathrm{const} + \iota_r(A_V)$ with $\iota_r(A) = \sum_{a \in A \setminus 0} 1/a$ and $A_V = \{1/\delta_H : H \supseteq V\}$ an $r$-dimensional subspace of $D^\star$. So the real classes are the fibres of $\iota_r$ on the $r$-dimensional subspaces of $D^\star$. Rate 1/16 below $5n/32$ is $r = 3$; rates 1/8 and 1/4 are $r = 2$. **[proved]**
- Two free flats of size $n/4$ through a common subspace of codimension 3 (the tree supports): $\theta_0 = c_1(V_1) + c_1(V_2)$, and $\theta_0^4$ is the sum of $1/a$ over an affine plane of $D^\star$ off the origin. **[proved]**
- The $5n/8$ class: $\theta_0 = e_2(Y)$ (Lemma 2.1).
- Gold sets (note 01, 3.5) are not of this type (the word has degree $n/2$ and the list lives in the subcode of squares), but their count is again a plane statistic: two planes of $D^\star$ with the same product of nonzero elements and trivial intersection are one of the 10 decompositions of a rank-4 solution. **[quoted]** from note 01, **[checked]**: `13_planes` reproduces its counts 82, 1411, 22979.
- Two planes of $D^\star$ that share a line never have the same $\iota_2$ or the same product ($b \mapsto b^2 + ab$ is two-to-one onto its image), so the candidates are the pairs with trivial intersection. **[proved]**, as in note 05, section 4.1.

## 4. Experiments

### 4.1 Step 3 of note 04: the fibres of $e_{n/8}$ on the $5n/8$ class

**Proposition 4.1. [proved]** For every field $F$ of characteristic two, every subspace domain $D \subset F$ with $N \ge 5$ and every $U \le D$ of size $n/8$, each value of $e_{n/8}$ is taken by at most $7 + 16 \cdot 224 = 3591$ members of the class of $L_U^5$. So the genuine list at agreement $5n/8$ that this class contributes to any one word has at most 3591 members, whatever $n$ is.

*Proof.* By section 2, a member with $W$-coordinates $(\alpha, t_1, t_2, t_3)$ and formal class $c$ has $e_{n/8} = v$ iff $Q_c(1, t) = v\alpha$, and its coordinates lie on the curve $C : t_i^2 + t_i = \lambda_i \alpha$ ($i = 1, 2, 3$). Eliminating $\alpha$, $C$ is the intersection of two quadrics in the $t$-space, and it is geometrically irreducible: it is a fibre product of Artin-Schreier covers of the $t_1$-line, which is irreducible unless some $(a\lambda_2 + b\lambda_3)/\lambda_1 \cdot (t_1^2 + t_1)$ is of the form $h^2 + h$, that is unless $a\lambda_2 + b\lambda_3 \in \{0, \lambda_1\}$, and $\lambda_1, \lambda_2, \lambda_3$ are $\mathbb{F}_2$-independent because $L_U$ is injective on $D/U$. Writing $Q_c(1,t) - v\alpha$ in the basis $1, t_2, t_3, t_2t_3$ of the function field over $F(t_1)$, it vanishes identically on $C$ iff $c_{00} = 0$, $c_{ij} = 0$ for $1 \le i < j$, $c_{0i} = c_{ii}$ and $v = \sum c_{ii}\lambda_i$. These 8 masks are exactly the 8 classes of the $U$-invariant sets, and none of the 224 others (**checked** by the program, a finite enumeration). For every other mask Bézout gives at most $4 \cdot 2 = 8$ points of $C$ on the quadric, hence at most 8 hyperplanes $W$, each with 2 sets. The 8 invariant classes have distinct values $\sum c_{ii}\lambda_i$, so at most one of them (7 sets) has the value $v$. $\square$

This settles the test that note 04 called decisive ("a fibre of size growing with $n$ would refute Conjecture C(a) at once"): no such fibre exists, on any domain. The bound is crude. The truth is in the tables.

**Scaled real shape, random $U$. [checked]** `13_class58 N power random:1000 m r -n count`. A "coincidence" is an equality of $e_{n/8}$ between two different formal classes (a non-formal pair of fibres). The random model is $R(R-1)/2^{m+1}$ with $R = 224(n/8 - 1) + 8$ records. Coincidences come in groups of 8 (one algebraic event merges 8 pairs of 2-set classes into 8 fibres of 4 sets), so the statistical unit is a group and the standard error is $\sqrt{8 \cdot \text{count}}$.

| $N$ | $m$ | subspaces $U$ | coincident pairs | random model | ratio | largest genuine list |
| --- | --- | --- | --- | --- | --- | --- |
| 8 | 20 | 2000 | 46808 | 46080 | 1.016 | 9 |
| 9 | 23 | 2000 | 25264 | 23770 | 1.063 | 9 |
| 10 | 26 | 2000 | 13376 | 12070 | 1.109 | 7 |
| 11 | 28 | 2000 | 11960 | 12160 | 0.984 | 7 |
| 12 | 31 | 1000 | 3128 | 3051 | 1.025 | 7 |
| 13 | 33 | 1000 | 2792 | 3057 | 0.913 | 7 |
| 14 | 36 | 600 | 1040 | 918 | 1.133 | 7 |
| 15 | 38 | 400 | 504 | 612 | 0.823 | 7 |
| 16 | 41 | 300 | 144 | 230 | 0.627 | 7 |
| 17 | 44 | 150 | 136 | 57 | 2.37 | 7 |
| 18 | 46 | 100 | 40 | 38 | 1.05 | 7 |
| 19 | 49 | 50 | 0 | 9.6 | 0 | 7 |
| 20 | 51 | 30 | 8 | 5.7 | 1.39 | 7 |
| all | | | 105200 | 102059 | 1.031 | |
| $N \ge 14$ | | | 1872 | 1871 | 1.001 | |

Every entry is within about two standard errors of the model except $N = 9, 10$ (a 6 to 11% excess, which is the tail of tier 2, see 4.4) and $N = 17$ (17 groups against 7.2 expected, the one outlier in 13 rows). The merged fibres have 4 sets (two classes of 2), rarely 6 or 9. A fibre never exceeded 9 sets in $1.1 \cdot 10^4$ subspaces, and never exceeded the formal 7 for $N \ge 10$. Nothing grows with $n$.

**The real domain. [checked]** `13_class58 25 power <U> 64 0x1b`: $D = D_{24,1} = \mathrm{span}(1..x^{24}) \subset K$, all $2^{22} - 1$ hyperplanes of $U$, all $1{,}879{,}047{,}800$ members, $9.4 \cdot 10^8$ keys sorted, 30 seconds per $U$.

| $U$ | coincidences between formal classes | random model | genuine list at $5n/8$ from the class |
| --- | --- | --- | --- |
| $\mathrm{span}(1..x^{21})$ | 24 pairs (structural, fibres of 4) | 0.024 | 7 |
| $x^3 \cdot \mathrm{span}(1..x^{21})$ | 24 pairs (structural, fibres of 4) | 0.024 | 7 |
| 16 random $U$ (seeds 1..4 and 100..111) | 0 in each | 0.024 each, 0.38 in all | 7 in each |

So on the real domain, for these 18 words, the list of note 02's Theorem 5 splits at the next coefficient exactly as on a generic domain: 8 fibres of 7 and fibres of 2, except for 24 fibres of 4 when $U$ is one of the two ideal-like subspaces. This is a direct check of the accounting of note 04 ("expected number of accidental pairs $2^{60.6-64} < 1$") at the real size. With $2^{66}$ subspaces $U$ the same model predicts that some words do have accidents: a value shared by three formal classes is expected for about $2^{25}$ of the subspaces ($R^3/(6 \cdot 2^{128}) = 2^{-41}$ each) and a value shared by four for none ($2^{-77}$ each). The possible fibres are then $2, 4, 6, 7, 9, 11$ sets, so the largest genuine list at $5n/8$ from classes of this type, over all words, is 11. **[conjectured]**

### 4.2 The plane statistics: rates 1/4, 1/8, 1/16 and the Gold calibration

`13_planes N stat power m r` enumerates all subspaces of the stated kind of $D^\star$ (all $\binom{N}{2}_2$ planes, all $\binom{N}{3}_2$ three-dimensional subspaces, all $7\binom{N}{3}_2$ affine planes off the origin), sorts the invariant and compares the number of colliding pairs and the whole fibre-size histogram with the random model (uniform independent values: pairs $=$ candidates$/2^m$, fibre sizes Poisson). Scaled real shape. **[checked]**

| statistic (what it governs) | $N$, $m$ | objects | colliding pairs | random model | ratio | largest fibre (Poisson) |
| --- | --- | --- | --- | --- | --- | --- |
| $\iota_2$ (codim-2 flats: rates 1/8, 1/4, top of 1/16) | 12, 31 | $2^{21.4}$ | 1783 | 1814 | 0.983 | 2 (2) |
| | 13, 33 | $2^{23.4}$ | 7256 | 7268 | 0.998 | 3 (3) |
| | 14, 36 | $2^{25.4}$ | 14552 | 14550 | 1.0001 | 3 (3) |
| | 15, 38 | $2^{27.4}$ | 58247 | 58230 | 1.0003 | 3 (3) |
| | 16, 41 | $2^{29.4}$ | 116632 | 116500 | 1.0013 | 3 (3) |
| product (Gold, rate 1/4 at $3n/8$) | 12, 31 | $2^{21.4}$ | 1860 | 1814 | 1.025 | 3 |
| | 13, 33 | $2^{23.4}$ | 7340 | 7268 | 1.010 | 3 |
| | 14, 36 | $2^{25.4}$ | 14320 | 14550 | 0.984 | 3 |
| | 15, 38 | $2^{27.4}$ | 57730 | 58230 | 0.991 | 3 |
| | 16, 41 | $2^{29.4}$ | 117160 | 116500 | 1.006 | 3 |
| $\iota_3$ (codim-3 flats: rate 1/16 below $5n/32$) | 10, 26 | $2^{22.6}$ | 300615 | 300200 | 1.0013 | 5 |
| | 11, 28 | $2^{25.6}$ | 4834625 | 4836000 | 0.9996 | 6 |
| | 12, 31 | $2^{28.6}$ | 38821817 | 38820000 | 1.0000 | 7 (7) |
| $\iota_3$, small field (fibres much larger than 1) | 11, 16 | $2^{25.6}$ | $1.98085 \cdot 10^{10}$ | $1.981 \cdot 10^{10}$ | 0.9999 | 907, mean 777.5 |
| | 12, 20 | $2^{28.6}$ | $7.95096 \cdot 10^{10}$ | $7.951 \cdot 10^{10}$ | 1.0000 | 483, mean 389.4 |
| affine planes (two flats of size $n/4$) | 10, 26 | $2^{25.4}$ | 14708878 | 14710000 | 0.9999 | 9 (9) |
| | 11, 28 | $2^{28.4}$ | 236989096 | $2.370 \cdot 10^8$ | 1.0000 | 12 (12) |

For the Gold statistic solutions come in groups of 10, so its standard error is $\sqrt{10 \cdot \text{count}}$ and every row is within one standard error. The fibre-size histograms agree with Poisson in every cell printed by the program (for example $N = 12$, $\iota_3$: observed 337635013, 32101783, 2033758, 96742, 3655, 113, 3 fibres of sizes 1 to 7 against $3.376 \cdot 10^8$, $3.210 \cdot 10^7$, $2.035 \cdot 10^6$, 96720, 3678, 116.6, 3.17). A random basis in the same field gives the same statistics (largest fibre 899 against 907 at $N = 11$, $m = 16$). For $N \le 11$ the ratios are within 10% (small counts, and the structural pairs of 4.3 are visible: 73 against 54 at $N = 8$).

So for every invariant that carries a pigeonhole, the real shape with wrap behaves as a random function to three or four digits, in both regimes (fibres much smaller and much larger than 1). This is the calibration of the random model that the brief asks for in (c) and (d).

### 4.3 The structural tier: identities of $\mathbb{F}_2(x)$

The same programs in the real field $K$ at sizes where the random model predicts nothing (expected number of accidental pairs below $0.02$), and with two moduli of degree 64 at once (`... 64 0x1b 64 0x1d`), where it predicts $2^{-70}$. **[checked]**

| family | structural coincidences | sizes tested |
| --- | --- | --- |
| $\iota_2$, planes of $D^\star$ | exactly 1 pair: the plane of the functionals $f(0) + f_\infty$, $f(1) + f_\infty$ and the plane of the place $x^2 + x + 1$ (the pair found in note 05, 4.2) | $N = 6, 8, 10, 12, 14, 16$; two moduli at $N = 12$ |
| product (Gold) | none | the same |
| $\iota_3$ | exactly 3 pairs | $N = 8, 10, 12$; two moduli at $N = 12$ |
| affine planes | exactly 246 pairs: 204 fibres of 2, 9 of 3, one of 6 | $N = 8, 10, 11$; two moduli at $N = 10$ |
| $5n/8$ class, $U = \mathrm{span}(1..x^{N-4})$ or $x^3$ times it | exactly 24 pairs (3 groups), between $W = \ker f(0)$ and $W = \ker f(1)$ | every $N$ from 7 to 20 and $N = 25$; two moduli at $N = 7..10, 12, 16, 20$ |
| $5n/8$ class, random $U$ | none for $N \ge 9$ (200 subspaces per $N$, two moduli), see 4.4 for $N \le 8$ | $N = 5..10$, 12, 16, 20 |
| any of the above on a random basis | none | $N = 10, 12$ |

The counts do not depend on $N$. They are tied to the three rational places and the quadratic place of $\mathbb{F}_2(x)$, that is to the group $\mathrm{PGL}_2(\mathbb{F}_2)$ acting on the polynomials of degree $< N$. I did not derive them by hand. Their effect on lists is a bounded factor: the largest structural fibre is 6 (affine planes), and for the $5n/8$ class they merge classes of 2 into fibres of 4, below the formal 7.

### 4.4 Exhaustive $n = 32$, and why it is not representative

`13_ct32 T g shape m r [m2 r2]` is note 04's exhaustive enumeration with the field free. The cells are the complement duals of rate 1/2 at $T = 20, 21, 22$ and the windows of rates 1/8 and 1/16. "pairs" are pairs of sets in a common class, "non-formal" the pairs that violate the generic congruence. **[checked]**

| cell $(T, g)$ | meaning | formal (two random bases, $m = 64 + 64$) | power, $m = 16, 20, 26, 64$ (identical) | power, $m = 13$ | random basis, $m = 13$ | $m = 15$ | $m = 16$ | $m = 20$ | $m = 26$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $(12, 4)$ | rate 1/2, $T = 20$ | 1692600 pairs, largest 7 | 23217496, 13 | 23484056, 13 | 5414184, 9 | 2822120, 9 | 1791224, 7 | 1752952, 7 | 1692600, 7 |
| $(11, 5)$ | rate 1/2, $T = 21$ | 520800, 3 | 8486880, 7 | 8557152, 7 | 1738720, 5 | 916320, 4 | 546016, 3 | 539104, 3 | 520800, 3 |
| $(10, 6)$ | rate 1/2, $T = 22$ | 111600, 3 | 111600, 3 | 111600, 3 | 111600, 3 | 111600, 3 | 111600, 3 | 111600, 3 | 111600, 3 |
| $(9, 5)$ | rate 1/8, $T = 9$ | 14880, 3 | 517728, 6 | 519264, 6 | 70304, 6 | 36960, 3 | 15392, 3 | 15392, 3 | 14880, 3 |
| $(11, 7)$ | rate 1/8, $T = 11$ | 520800, 3 | 520800, 3 | 520800, 3 | 520800, 3 | 520800, 3 | 520800, 3 | 520800, 3 | 520800, 3 |
| $(5, 3)$ | rate 1/16, $T = 5$ | 104160, 7 | 104160, 7 | 104160, 7 | 104160, 7 | 104160, 7 | 104160, 7 | 104160, 7 | 104160, 7 |
| $(6, 4)$ | rate 1/16, $T = 6$ | none | 400, 2 | 400, 2 | 32, 2 | 16, 2 | none | none | none |
| $(7, 5)$ | rate 1/16, $T = 7$ | none | 8000, 2 | 8000, 2 | 640, 2 | 320, 2 | none | none | none |

Each entry is the number of pairs and the largest class. A second random basis at $m = 13$ gives 4602776 (7), 1485024 (4), 62880 (3), 32, 640 in the cells that are not formal.

Reading. (1) On the power shape the count is the same for $m = 16, 20, 26, 64$ in every cell: at $n = 32$ the non-generic part is entirely tier 2 (identities of $\mathbb{F}_2[x]$ among polynomials of degree at most 16), and wrap only shows at $m = 13$, where it adds about 1%. (2) The cells that are not formal are exactly the ones with $i(g) = 1$ (Proposition 3.1 with $e = 2$: the positions are 4, 6, 7, so depths 4 and 5 see one field element, depths 6 and 7 two or three), and the cells with $i(g) \ge 2$ are formal on every domain and in every field tried, down to $m = 13$. (3) On a random basis the excess over the formal count decays quickly with $m$ and is zero at $m = 26$. It is lumpy (one algebraic coincidence produces thousands of pairs of sets), so single cells are not a clean test of a rate. (4) The largest class is 13 on the power shape in the first cell for every $m$, as in note 04: a tier-2 effect.

The formal classes of the previous level (depth 3) have 1400, 589, 513, 465 members for the duals of $T = 20, 21, 22, 23$ (`13_ct32 T 3 random:1 64 0x1b 64 0x1d` for $T = 11, 10, 9$): above $5n/8$ they stay of the order of the $56n - 392$ of the $5n/8$ class and decrease. **[checked]** at $n = 32$ only. This is the quantity $R$ of Law P in the rate-1/2 window.

Tier 2 is a small-$N$ phenomenon. Structural coincidences of the $5n/8$ class per subspace $U$ (random $U$, 200 per $N$, two moduli of degree 64, `13_class58 N power random:50 64 0x1b 64 0x1d -n 200`): **[checked]**

| $N$ | 5 | 6 | 7 | 8 | 9 | 10 |
| --- | --- | --- | --- | --- | --- | --- |
| structural pairs per $U$ | 103.2 | 9.28 | 1.08 | 0.04 | 0 | 0 |
| largest genuine list | 13 | 7 | 7 | 7 | 7 | 7 |
| the two ideal-like $U$ | 240 | 32 | 24 | 24 | 24 | 24 |

At $N = 5$ the labels are products of four polynomials of degree at most 4 and unique factorization produces coincidences everywhere. At $N \ge 9$ only the two special $U$ keep their 24. The "13 against 7" and "9 against the formal bound 7.1" of notes 02 and 04 are this effect and say nothing about $N = 25$.

## 5. The law

**Law P. [conjectured, fitted to sections 4.1 to 4.3]** Let $D$ be the power-shape domain in a field of degree $m$, $\mathcal{F}$ a formal class of level $e$ with $R$ formal sub-classes at depth $g \in [2^e, 2^{e+1})$, of sizes at most $\mu$. By Corollary 3.2 the real classes inside $\mathcal{F}$ are the fibres of $\Theta_g : \mathcal{F} \to F^{i(g)}$. Then the values of $\Theta_g$ on the $R$ sub-classes behave as independent uniform elements of $F^{i(g)}$, apart from $O(1)$ structural coincidences (fibres of at most 6 in all cases found) and apart from pairs that provably cannot collide. Hence:

- the expected number of $j$-fold coincidences is $\binom{R}{j} 2^{-m\,i(g)(j-1)}$;
- if $R \ge 2^{m\,i(g)}$ the largest real class has about $\mu R / 2^{m\,i(g)}$ members (and at least $\lvert\mathcal{F}\rvert/2^{m\,i(g)}$, unconditionally);
- if $R < 2^{m\,i(g)}$ it has at most $j^\ast \mu$ members, $j^\ast$ the largest $j$ with $\binom{R}{j} \ge 2^{m\,i(g)(j-1)}$ (take the maximum over the words in play, which multiplies the left side by their number);
- pairs outside a common formal class of level $e$ cost at least $m(e'+1)$ bits and do not occur.

In formula, for the flat families (free flats of codimension $r$, $2^r\binom{N}{r}_2 \approx 2^{r(N-r) + r + 1.5}$ of them, padding of mass $\beta n$): at rate $2^{-R}$ with $r = R - 1$, agreement $T = (2^{1-R} + \beta(1 - 2^{1-R}))n$ and
$$\log_2(\text{pigeonhole list}) = \bigl[\, r(N - r) + r + 1.5 - m \cdot i \,\bigr]^+, \qquad i = 1 \text{ for } \beta < 2^{-R-1},\ 2 \text{ for } \beta < 2^{-R-1} + 2^{-R-2}, \dots$$
which is $15.6$ for $(R, N, m) = (4, 28, 64)$ and $0$ for $R \le 3$ at level-0 sizes, where instead $j^\ast = 4$ ($N = 26, 27$). For the $5n/8$ class $R = 2^{N + 4.8}$ and the expected number of coincidences is $2^{2N + 8.6 - m}$ per word. For Gold at rate 1/4, $t = 2$: $2^{4N - 9.5 - m}$ rank-4 solutions, 16 codewords each, so $2^{4N - 5.5 - m}$ codewords (note 01's formula, confirmed).

"Real list $=$ generic list $+$ pigeonhole term" is then: $\Lambda_{\mathrm{real}}(T) \le j^\ast \cdot \Lambda_{\mathrm{formal}}(T) + \max_{\mathcal{F}} \lvert\mathcal{F}\rvert / 2^{m\,i(T-k)}$, the maximum over formal classes of the previous level with supports of size at least $T$, with $j^\ast \le 5$ at level-0 sizes.

Fit: the table of 4.1 (ratio $1.031$ over $10^5$ events, $1.001$ for $N \ge 14$), the table of 4.2 (ratios $1.000$), the Poisson histograms, the absence of any coincidence at the real size in 16 random $U$ (expected $0.4$), the structural counts of 4.3. Nothing measured deviates from the law by more than the stated statistical error once $N \ge 11$.

Scope. The law is about lists whose agreement sets are locators with or without multiplicities (strict and multiset common tops) and about Gold-type lists. It says nothing about words with many phantom roots outside $D$. For those there is no construction, no bound and no experiment, in this note or in the others.

## 6. Extrapolation to the real parameters

Level 0 has $N = 24 + R$: $N = 25, 26, 27, 28$ for rates 1/2, 1/4, 1/8, 1/16, and $m = 64$. Numbers of subspaces: $\binom{N}{2}_2 = 2^{2N - 2.58}$, $\binom{N}{3}_2 = 2^{3N - 7.39}$. $t = \lceil 108/\log_2(n/A) \rceil$ for a threshold $A$ whose list is within the budget $2^b$ (the DEEP-fold accounting of note 07, not re-derived here).

### 6.1 Rate 1/2, $N = 25$

- $T \in [5n/8, 11n/16)$, $i = 1$. The formal classes of the previous level (depth $n/8 - 1$) with supports of this size that I know are one-parameter: the class of $L_U^5$ and its sub-families with a fixed set added ($R \le 2^{29.8}$), and flats of size $n/4$ beside a padding inside a hyperplane ($R \le 2^{N+1}$, and there accidents are impossible because all the planes share a point of $D^\star$). Expected accidental pairs per word: $2^{2 \cdot 29.8 - 65} = 2^{-5.4}$ at most. Over all words $j^\ast \le 3$. So $\Lambda_{\mathrm{real}} \le 3\Lambda_{\mathrm{formal}}$: with note 01's formal multiset family ($L$ members at $5/8 + \sqrt{3/(64L)}$) and the strict bound $1/(2\tau-1)^2$, lists of $2^{10}$ stop at about $0.632n$ and lists of $2^{20}$ at $0.6252n$. **[conjectured]**; the part "no accident in the $5n/8$ class" is **[checked]** at the real size and bounded unconditionally by Proposition 4.1.
- $T \in [11n/16, n/\sqrt2)$, $i = 2$: nothing.
- $T = 5n/8$ to $5n/8 + \ell - 1$: $2^{30.8}$ to $2^{27.8}$ (notes 01, 02, 05), all formal.
- $T \in (9n/16, 19n/32)$, $i = 1$ at level $N - 4$: the pigeonhole term is $2^{38.7 - 1.1j}$ at $9n/16 + j$ (section 3.2, proved to exist) and at most about $2^{38.7}$ in the range (it needs a formal class of $2^{102.7}$ sets of that size, and the count drops with the padding). For $T \ge 19n/32$, $i \ge 2$ and it is gone. The formal lists in $(9n/16, 5n/8)$ are the open classification of note 04, step 2.

### 6.2 Rate 1/4, $N = 26$

Below $n/2$ every list contains the $2n - 2 = 2^{27}$ hyperplane polynomials. $T \in (3n/8, 7n/16)$: flats of size $n/4$ with a common second coefficient, $R \le 2^{51.4}$, $j^\ast = 4$ (expected 4-fold fibres of $\iota_2$: $2^{1.1}$), so at most 16 extra members; Gold with $t = 3$ at $7n/16$: $2^{13.5}$. So $\Lambda \approx 2^{27}$ on $(3n/8, n/2)$. At $T = 3n/8$: Gold $2^{34.5}$ (calibrated in 4.2) and the formal $2^{31.8}$ of note 05. In $(5n/16, 3n/8)$ the pigeonhole on the $2^{50}$ family of note 05 gives at most 4-fold merges. So with the DEEP fold: $b = 28$ allows $A$ just above $3n/8$, $t = 77$ against 109; $b = 36$ allows $A = 3n/8$ (no gain in $t$); $A$ just above $5n/16$, $t = 65$, needs the formal classification of the second dyadic range and at least $b = 36$.

### 6.3 Rates 1/8 and 1/16, $N = 27, 28$

Rate 1/8, $T \in (n/4, 5n/16)$: fibres of $\iota_2$ on $2^{51.4}$ planes, $j^\ast = 4$ (expected 4-fold: $2^{9.1}$, 5-fold: $2^{-5.8}$), four cosets each, so at most 16 members besides the formal 4; above $5n/16$ nothing. $\Lambda \le 2^5$ in the whole window. At $T = n/4$: the flats, $2^{53.4}$ with slack.

Rate 1/16. $T \in (n/8, 5n/32)$: fibres of $\iota_3$ on $2^{76.6}$ subspaces: mean $2^{12.6}$, eight cosets each, so $2^{15.6}$ members, at agreement $n/8 + \tfrac78 \beta n$ for a padding of mass $\beta n < n/32$ in general position, that is up to $0.1523n$ (this is the padded family of note 01, 3.2; the random model for it is the $\iota_3$ rows of 4.2, including the regime of large fibres). A padding chosen to avoid the flats gains about $0.001n$ for a list of $2^{10}$ and reaches $5n/32$ only for lists of about 26. $T \in [5n/32, 11n/64)$, $i = 2$: pairs only ($2^{30}$ of them exist, no triple). $T \in [3n/16, n/4)$: flats of size $n/4$ minus a common set, fibres of $\iota_2$ on $2^{53.4}$ planes, $j^\ast = 5$. So $\Lambda \approx 2^{15.6}$ up to $0.153n$ and $\Lambda \le 2^6$ above. Conjecture C(c) of note 04 ($2^{10}$ from $3n/16$) can be sharpened to $0.153n$, $t = 40$ instead of 45, and with $b = 17$ the threshold is $n/8 + \ell$, $t = 37$.

### 6.4 Interleaved words, extensions, and large budgets

Everything above is stated for single $K$-valued words. By Proposition 3.4 the same list sizes hold, up to a factor 2, for every number of lanes and every extension of $K$, as long as the list is below $2^{62}$: that covers every cell of the windows. The two thresholds whose lists are above $2^{62}$ are dyadic points where the list is formal:

- Rate 1/16 at $A = n/8$: $\Lambda_K = 2^{79.6}$ (flats, with slack). By Proposition 3.5, $\Lambda_{K^2}(n/8) \le 2^{79.6}(1 + \Lambda_K(3n/16 - \ell))$, and the second factor is a list inside the window, predicted at most $2^6$. With Proposition 3.4 ($s = 2$): at most $2^{87}$ for any lanes and extensions. I expect $2^{80.6}$: a shared first component must agree with its lane on $3n/16$ points, and the second lane would need $2^{79}$ flats of size $n/8$ inside that set. **[conjectured]**
- Rate 1/2 at $A = 9n/16$: $\Lambda_K \ge 2^{102.7}$. Here $2T - d \approx 5n/8$, where $\Lambda_K \approx 2^{30.8}$, so Proposition 3.5 alone gives $2^{133.5}$. Splitting the shared first components by the size of their agreement set $D_a$: if $\lvert D_a \rvert < T^2/d \approx 0.633n$ the second lane restricted to $D_a$ is above its own Johnson radius and contributes at most about 10 members, and there are at most $\Lambda_K(0.633n) \le 2^{10}$ first components with a larger agreement set. So $\Lambda_{K^2}(9n/16) \le 2^{102.7}(1 + 2^{10}) + 10 \cdot 2^{30.8}$, about $2^{113}$, given the window prediction. **[proved]** as an implication, **[conjectured]** as a number; I expect $2^{103.7}$.

With budgets of $2^{100}$ or more, the thresholds that Law P leaves open are therefore decided by the formal lists alone, plus the two real-domain terms: rate 1/2, $A$ just above $9n/16$ ($t = 131$) needs the formal lists on $(9n/16, 5n/8)$ to be below the budget, and the real domain adds $2^{38.7}$; rate 1/4, $A$ just above $5n/16$ ($t = 65$) needs the formal lists on $(5n/16, 3n/8)$, and the real domain adds Gold's $2^{34.5}$ and nothing else; rate 1/8, $A = n/4$ ($t = 54$) needs $b \ge 55$; rate 1/16, $A = n/8$ ($t = 36$) needs $b \ge 87$ by what is proved here, 81 expected. Going below these dyadic points (rate 1/8 below $n/4$, rate 1/16 below $n/8$) is a question about the next formal level, which this note does not address.

### 6.5 Confidence, and what would falsify it

- The pigeonhole exponents are exact consequences of counts and of Proposition 3.1. The random model behind $j^\ast$ and behind "no accident" is verified to three digits on the scaled real shape and directly at $N = 25$ for one family. I consider this part reliable to within one or two bits.
- The formal list sizes are taken from notes 01, 02, 05 and are theorems only for strict common tops. Below the first dyadic point of each window they are not known.
- Falsifiers: (1) a structural (tier 2) family whose size grows with $N$. Everything found is constant from $N = 7$ on, but the plane statistics were only run to $N = 16$. (2) A formal class of the previous level, with supports inside a window, much larger than the ones used here ($2^{30}$ at rate 1/2): then $j^\ast$ grows, and at $R \ge 2^{64}$ a pigeonhole list appears. The formal classification of round 2 decides this. (3) A deviation of any $\Theta$ statistic from uniformity at larger $N$ (the runs stop at $2^{29.4}$ objects). (4) Words with phantom roots outside $D$: untested. (5) An error in the DEEP-fold accounting that turns $b$ into $t$, which is outside this note.

## 7. Is there a provable handle on a concrete domain?

### 7.1 Domain choice

**Points in $E$.** If $D \subset E$ is an $N$-dimensional $\mathbb{F}_2$-space in general position (not inside $cK$), every $\theta_i$ is worth 128 bits. Under Law P with $m = 128$ all the pigeonhole terms of section 6 vanish: rate 1/16 has $2^{79.6 - 128} < 1$ (accidental pairs exist, $2^{24}$ of them, no triple), Gold has $2^{98.8 - 1 - 128} < 1$, the list just above $9n/16$ at rate 1/2 has $2^{102.7 - 128} < 1$. So on such a domain "real $=$ formal" would be the prediction at every level-0 rate. **[conjectured]** It proves nothing: Proposition 3.1 and the counting are the same, only the exponent changes. Cost: the values of a $K$-coefficient polynomial on $D$ are no longer in $K$, so if the level-0 lanes are $K$-valued the leaf bytes and the hashing double and the NTT multiplies $E \times E$. That is about the cost of halving the rate, which gives 109 proven queries at rate 1/2 against a conjectural 160. (Note 11 lists the $K$-valuedness of level 0 among the facts the protocol relies on. Were the lanes $E$-valued, only the twiddles would change.) Verdict: dominated.

**Unions of cosets (note 06, 6.2).** Removes the flats and with them the rate-1/16 pigeonhole (it needs free flats of size $2k$ in $2^{76}$ directions; a Sidon union of 16 cosets has 120). Not a subspace, so the formal theory has to be redone. Nothing provable.

**A domain on which the hypotheses become finite.** The generic proofs need the monomials of degree up to $n/8$ in a basis to be independent. There are $\binom{N+1}{2} = 325$ monomials of degree 2 already, against $m = 64$ or 128. What is finite on a concrete domain is the list of maps $\theta_i$ on an explicit formal class: "$\Theta_g$ is injective on the sub-classes of $\mathcal{F}$" is a computation of size $\lvert\mathcal{F}\rvert$ (30 seconds for the $5n/8$ class of one $U$ at $N = 25$). It certifies one word at a time, and there are $2^{66}$ subspaces $U$.

### 7.2 Counting through character sums, the Li-Wan sieve, moments

By Proposition 3.3 the number of $T$-sets with a prescribed top is $\lvert G \rvert^{-1} \sum_{\chi} \bar\chi(\text{key}) \cdot [X^T]\prod_{s \in D}(1 + \chi_s X)$, the sum over the characters of $G = \prod_{j \text{ odd}} W_{\ell_j}(K)$ ($\lvert G \rvert = 2^{64g}$), with $\chi_s = \chi((\tau(s)^j)_j)$ a root of unity. The main term is $\binom{n}{T}/2^{64g}$. Every bound of Li-Wan type estimates the other terms through the sums $\sum_{s \in D} \chi_s^r$. Two independent reasons why this cannot reach $2^{100}$: **[proved]** as statements about the method.

1. *No cancellation is available.* The Weil-type bound for Galois-ring sums (Kumar, Helleseth, Calderbank) is $(\text{degree} - 1)\sqrt{\lvert K \rvert} \ge 2^{32}$ for a sum over all of $K$, and a sum over a subspace is an average of such sums, with the same bound. The trivial bound is $n = 2^{25}$. Since $n < \sqrt{\lvert K \rvert}$, nothing nontrivial is known for any sum of degree at least 2 over $D$. (Burgess-type bounds for boxes exist for multiplicative characters only.)
2. *A square-root barrier.* Even if every nontrivial sum were of size $\sqrt n$, the coefficient $[X^T]$ is bounded only by about $\binom{T + \sqrt n}{T} = 2^{\Theta(\sqrt n \log n)}$, which is $2^{70000}$ at $N = 25$. And the characters that correspond to formal structure (traces that restrict to functionals of $D$) have no cancellation at all. So the method can only prove that the count is $\binom{n}{T}/2^{64g}$ up to that error, which is non-trivial only when $64 g < nH(\tau) - \Theta(\sqrt n \log n)$, that is $\tau - \rho < H(\tau)/64 \approx 0.0156$ at rate 1/2. That is the regime of the generic pigeonhole of note 01, 3.7, where it proves that lists are huge. For $T - k = \Theta(n)$ beyond $n/64$ it says nothing.

Moment methods have the same input. I see no regime of our parameters where they give an upper bound.

### 7.3 A finite hypothesis under which the generic proof goes through

Not of the form suggested in the brief. The generic proofs extract the coefficient of $b_a^{2^e}$ from $e_{2^e}(S) - e_{2^e}(S')$, a formal polynomial with a number of monomials that is exponential in $n$; a hypothesis "no relation of weight at most $w$ among the monomials of degree at most $j$" applies only to differences of weight at most $w$, and independence of all monomials is impossible beyond degree 1 ($D \cdot D$ has dimension 49 on the power shape and at most 64 on any domain, against 325). For the record, on the power shape there are relations of weight 2 in degree 2 ($x^i x^j = x^{i'} x^{j'}$). **[proved]**

What Proposition 3.1 offers instead is a reduction with an explicit loss, level by level:

> Inside a formal class of level $e$, the real classes at depth $g$ are the formal ones merged along the fibres of $\Theta_g$. If every fibre of $\Theta_g$ on the formal sub-classes of $\mathcal{F}$ has at most $J$ elements, the real classes inside $\mathcal{F}$ are at most $J$ times the formal ones.

For a one-parameter class this hypothesis is a theorem: the fibres are intersections of an irreducible curve with a hypersurface, and Bézout bounds them independently of $n$ (Proposition 4.1: $J \le 16 \cdot 224$ for the $5n/8$ class). For the classes with two or more parameters (flats in varying directions: planes of $D^\star$) the fibre is the set of points of a curve, for instance $a^2 + ab + b^2 = v\,ab(a+b)$, with both coordinates in the subspace $D^\star$ of density $2^{N - 64}$, and no bound better than the trivial $2^N/3$ is known. This is the precise obstruction. It is a question about points of curves in products of subspaces ("how many points of a fixed cubic have both coordinates in a 25-dimensional subspace of $\mathrm{GF}(2^{64})$"), the same kind of question as short character sums, and I know of no technique.

Three things remain out of reach even with such a bound: the pairs that are not in a common formal class of the previous level (Corollary 3.2, part 3: at least $64 \cdot 22$ bits of coincidence each, but a count is not a proof), multisets, and words with phantom roots outside $D$. So: **no route to a proof of ListBound on a concrete domain exists today**, on $D_{\kappa,R}$ or on any domain compatible with the additive NTT.

## 8. What to do with this

1. Use Proposition 3.1 in the formal classification of round 2 (note 12): it says that in each dyadic block the formal key of a class of the previous level has only $e + 1$ nonzero coefficients, which organizes the "second dyadic range" completely (one coefficient up to $1.5 \cdot 2^e$, two up to $1.75 \cdot 2^e$).
2. If the formal classes of level $N - 3$ with supports in $[5n/8, 11n/16)$ can be shown to be finite unions of one-parameter families of the glued type, Proposition 4.1 extends to them and gives, for strict common tops inside one class of the previous level, a real-domain bound independent of $n$. That would be the first unconditional real-domain statement in the window. It would still not cover deep accidents.
3. For note 11: by Proposition 3.4 its hypothesis $\mathrm{ListBound}_i(L_i)$ for all lane counts follows from the same statement for single $K$-valued words with $L_i/2$ (if $L_i \le 2^{63}$), or for single $E$-valued words (if $L_i \le 2^{127}$). So the conjecture can be stated, tested and attacked on single words over $K$.
4. State the assumption for the DEEP-fold design as Conjecture C with the explicit correction: "$\Lambda(T) \le 2^{10}$ for $T \ge 0.64n$ (rate 1/2), $T \ge 17n/64$ (rate 1/8), $T \ge 0.153n$ (rate 1/16); $\Lambda(T) \le 2^{28}$ for $T > 3n/8$ (rate 1/4)", and keep in mind that just above $9n/16$ at rate 1/2 and below $0.153n$ at rate 1/16 the real domain has lists that the formal model does not see ($2^{38}$ and $2^{15.6}$).
5. Runs designed and not made: (a) the plane statistics at $N = 17, 18$ (the program has a `-p passes` option that splits the keys; $N = 18$ is $1.1 \cdot 10^{10}$ planes, about 15 minutes and 12 GB with 8 passes); (b) the class of $L_U^9$ at $9n/16$ (32 labels, $2^{15}$ formal classes per hyperplane), the same program with a 5-dimensional label space, to test Law P at level $N - 4$ on a glued family; (c) an explicit Gold solution on the real domain (note 01, step 4), still worth doing as a sanity check of 6.2 and unchanged by this note.

## 9. Reproduction

All under `doc/whir_soundness_gap_notes/scripts/`. C with the system compiler (NEON carry-less multiply, portable fallback), Python 3 without dependencies. Binaries and outputs were kept outside the repository. `13_run_all.sh [builddir] [quick]` builds everything and reruns every table (about 30 minutes on four cores; `quick` skips the $N = 25$ runs and the $n = 32$ batch).

| script | what it does | time |
| --- | --- | --- |
| `13_irred.py` | lowest irreducible polynomial of each degree 8..64 (the moduli of the scaled family) and a second one | 2 s |
| `13_gf.h` | $\mathrm{GF}(2^m)$, $m \le 64$, any modulus: multiply, inverse, subspace polynomial values, radix sort | |
| `13_class58.c` | section 4.1: all fibres of $e_{n/8}$ on the class of $L_U^5$; `-check` is the brute-force check of section 2; a second field gives the $\mathbb{F}_2(x)$ tier | 0.1 s at $N = 16$, 30 s and 16 GB at $N = 25$ |
| `13_planes.c` | sections 4.2, 4.3: `iota2`, `pi2`, `iota3`, `aff2` statistics of $D^\star$, with the random model and the Poisson histogram; `-v` lists the colliding objects | 15 s at $N = 16$ |
| `13_ct32.c` | section 4.4: exhaustive common-top classes at $n = 32$ in any field, 4 threads | 10 to 40 s per cell |
| `13_sparse_key_check.py` | Proposition 3.1 and Proposition 3.3 | 5 s |
| `13_results.txt` | the raw output lines behind every table of this note | |
