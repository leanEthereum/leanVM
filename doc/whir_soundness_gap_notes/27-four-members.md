# 27. Four members and more on a subspace: the criterion, the classification at $n = 16$, a conjecture, and conditional bounds

Researcher 27, round 5. Every statement is tagged **[proved]** (proof in this note), **[quoted]** (from a cited note or paper, not re-proved), **[checked]** (numerically, sizes stated) or **[conjectured]**. Scripts are `scripts/27_*`, section 9 says how to run them.

Notation as in note 17. $F$ is a field of characteristic two, $D \subset F$ an $\mathbb{F}_2$-subspace of dimension $N$, $n = 2^N$, **generic** if it has a basis $b_1, \dots, b_N$ algebraically independent over $\mathbb{F}_2$. Codewords are polynomials of degree $< k$, $T$ is an agreement count, $m = T - k$, $t = n - T$, $d = n + k - 2T$. A list has $L + 1$ members $c_0, \dots, c_L$ with agreement sets $S_i$ and error sets $E_i = D \setminus S_i$. $L_U = \prod_{u \in U}(X - u)$ for a subspace $U$, and for a rational function $f$, $\Pi(f) = \{a \in D : f(X + a) = f(X)\}$ (all of $D$ if $f$ is constant).

## 0. Summary

**The honest headline.** There is still no unconditional list bound for all words in any window, and the four-member theory turned out to be richer than the three-member one: the direct analogue of Conjecture P of note 17 is false, in three different ways, already at $n = 16$. What this note delivers is (a) the exact criterion for $L + 1$ sets in three equivalent forms with the count for independent points, and a lift-invariant *excess density* that locates lists of $L + 1$ members on subspaces; (b) the complete classification of all four-member lists on a generic 16-point subspace at five parameter points ($4.0 \cdot 10^{10}$ quadruples of error sets at $(k, T) = (8, 10)$ alone); (c) a conjecture (Q) that fits every one of them and a search at $n = 32$; (d) proofs of the "if" directions, of the three-member Conjecture P in the totally split case by a new and very short method (unique factorization in $\mathbb{F}_2[b]$), of the four-member case of degree one, and of a four-member analogue of the Frobenius-Euler identities; (e) a list bound for all words conditional on a weak form of Q, with numbers, and an account of what an induction on the number of members can and cannot reach.

| | statement | where | status |
| --- | --- | --- | --- |
| 1.1 | Criterion for $L + 1$ sets: block-matrix form, syndrome form, curve form, and the exact dimension for independent points | every domain | proved (the generic-points dimension is quoted from [BGM]) |
| 1.3, 1.4 | $\sum_i \lvert S_i\rvert \le n + J + L\gamma_D$, and for independent points $J \le L\delta + L - 1$. The excess $\mathrm{exc} = J - L\delta - L + 1$ satisfies $\mathrm{exc} \ge (L+1)T - n - Lk + 1$ for every list | every domain (1.3), independent points (1.4) | proved (1.4 from [BGM]) |
| 1.5 | Lifting: $\mathrm{exc}(\Xi_0 \circ L_U) + L - 1 = \lvert U\rvert(\mathrm{exc}(\Xi_0) + L - 1)$. The density $(\mathrm{exc} + L - 1)/n$ is invariant under lifting | subspace domains | proved |
| 1.6 | **Four members exist at rate exactly 1/2 and agreement $11n/16 - 1$ for every $n \ge 32$** (the bound for independent points is $5n/8 - 1$). So four-member lists fill the whole window $(5/8, 2/3]$ | generic subspaces | proved from one list at $n = 16$, and checked directly at $n = 32, 64, 128$ |
| 2 | Four members have eight natural functions (four triple functions, the cross-ratio, three opposite ratios), each with its own period group, and a Cremona symmetry ($S_5$) | every domain | proved |
| 3 | All four-member lists at $n = 16$ for $(k, T) = (12, 13), (9, 11), (8, 10), (6, 9), (3, 7)$: 621 classes, $4.05 \cdot 10^{10}$ quadruples. Refuted: "excess needs a period of the curve", "excess is bounded by the periods of the cross-ratio functions", "excess shows as ramification at infinity" | generic, $n = 16$ | checked, exhaustive |
| Q (4.1) | **Conjecture Q.** $\mathrm{exc}(\Xi) \le \max_\chi \lvert\Pi(\chi)\rvert + 3\lvert\Pi(\Xi)\rvert - 2$, $\chi$ over the eight functions. Equivalently: a curve without period has $\mathrm{exc} \le 1 + \max_\chi\lvert\Pi(\chi)\rvert$, in particular $\mathrm{exc} \le 2$ if no function has a period | generic $D$ | conjectured. 0 violations in the $n = 16$ data, sharp there; conics at $n = 32$: see 4.2 |
| 5.1 | **Split triples.** If $u_0 + u_1 + u_2 = 0$ are pairwise coprime and all three split over $D$, then $u_i = \lambda_i (L_U + \alpha_i)^q$ for one subspace $U$ and one power of two $q$. So Conjecture P holds whenever all roots lie in $D$ | generic $D$, all fields | proved |
| 5.3 | Degree one: four lines have their six intersection abscissae in $D$ iff the three pairs of opposite intersections have a common difference | generic $D$ (the "if" on every subspace) | proved |
| 5.5 | Four-member Frobenius-Euler: $\det(\Xi, \mathfrak{E}_q\Xi, \mathfrak{E}_{q'}\Xi) = 0$ as soon as the incidences exceed $3\delta + q + q' - 4$ | generic $D$ | proved (not checked numerically) |
| 6.3 | **Conditional list bound.** Under H4($C$) (a weak form of Q restricted to the functions that give affine classes), $\Lambda(T) \le 3 + 24\binom{N}{c}_2 \prod_{i \le \delta^\ast + 1}\frac{n - k + i}{T - k + i}$ | generic $D$, all words, any number of lanes | proved conditional on H4($C$) |

**Conditional numbers** (section 6.4; $C = 2$ is the best possible constant, $C = 4$ is the constant that the $n = 16$ data requires).

| window | range of $\tau$ | $N = 25$ | $N = 28$ |
| --- | --- | --- | --- |
| rate 1/2, four members | $(0.6563, 2/3]$, $C = 2$ | $2^{79}$ | $2^{88}$ |
| | $(0.6407, 0.6563]$, $C = 2$ | $2^{105}$ | $2^{117}$ |
| | $(0.6563, 2/3]$, $C = 4$ | $2^{103}$ | $2^{115}$ |
| rate 1/4, four members | $(0.469, 1/2)$, $C = 2$ | $2^{76}$ | $2^{85}$ |
| | $(0.469, 1/2)$, $C = 4$ | $2^{97}$ | $2^{109}$ |
| rates 1/8, 1/16 | need 5 to 15 members | extrapolation only (6.5) | |

So even conditionally the four-member method reaches a budget of $2^{100}$ only in the upper third of the rate-1/2 window and only with the optimistic constant, and the hypothesis has no support beyond $n = 16$ (where every period statement of index $\le 16$ is empty). Below $5n/8$ one needs five and more members, the exponent $c$ grows by one about every time the number of members doubles, and the dyadic points $9/16$ and $17/32$ are out of reach of a budget of $2^{100}$ by this route (section 6.5).

**What replaces the period group** (the question of the brief). Not one subspace and not a nested pair. In the data the excess of a four-member configuration is the sum of three kinds of contributions: a period of the whole curve (factor: the lift formula 1.5), periods of single functions among the eight, each with its own subspace (a periodic triple with a fourth member through it, its Cremona images, opposite ratios periodic along two different subspaces), and a bounded sporadic part (at most 2 at $n = 16$) that has no period at all and is caused by $\mathbb{F}_2$-linear relations between the special points (the simplest: four 3-sets with equal sums). Conjecture Q is the inequality that holds for all of them.

## 1. The exact criterion for $L + 1$ sets

### 1.1 Three forms

For $S_0, \dots, S_L \subseteq D$ put $J_x = \{i : x \in S_i\}$ and $V(S) = \{(c_i) \in (F[X]_{<k})^{L+1} : c_i(x) = c_j(x) \text{ for all } i, j \in J_x,\ x \in D\}$. It contains the diagonal $\{c_0 = \dots = c_L\}$, of dimension $k$. For a partition $\mathcal{P}$ of $\{0, \dots, L\}$ let $S^{\mathcal{P}}$ be the family of the unions $\bigcup_{i \in P} S_i$, $P \in \mathcal{P}$.

**Theorem 1.1 (criterion). [proved, the last sentence of (b) quoted]** Let $D$ be any set of $n$ points of any infinite field $F$ and $S_0, \dots, S_L \subseteq D$. The following are equivalent.

(a) There are a word $w$ and pairwise distinct polynomials $c_0, \dots, c_L$ of degree $< k$ with $c_i = w$ on $S_i$.

(b) (Block matrix.) For every pair $i \ne j$, $V(S) \not\subseteq \{c_i = c_j\}$, that is $\dim V(S) > \dim V(S^{ij})$ where $S^{ij}$ merges $S_i$ and $S_j$ into their union. $V(S)$ is the kernel of the matrix with $\sum_x (\lvert J_x\rvert - 1)^+ = \sum_i \lvert S_i\rvert - \lvert\bigcup_i S_i\rvert$ rows and $(L + 1)k$ columns whose row for $(x; i, j)$ has the entries $x^a$ in block $i$ and $-x^a$ in block $j$. If the points are algebraically independent and $\lvert S_i\rvert \ge k$, then $\dim V(S) = \max_{\mathcal{P}}\bigl(\lvert\mathcal{P}\rvert k - \sum_x (\lvert\mathcal{P}(J_x)\rvert - 1)^+\bigr)$, where $\mathcal{P}(J_x)$ is the set of parts that meet $J_x$.

(c) (Syndromes, for $\lvert S_i\rvert \ge k$.) With $H$ a parity-check matrix of the code and $U_E$ the span of its columns indexed by $E$: there is $y \in \bigcap_i U_{E_i}$ that lies in no $U_{E_i \cap E_j}$, $i \ne j$. Moreover $\dim V(S) = k + \dim\bigcap_i U_{E_i} - (n - \lvert\bigcup_i S_i\rvert)$, and $y \in U_E$ iff $y$ kills the $n - k - \lvert E\rvert$ shifted locators $X^l Z_E$ (on a subspace domain, where the column multipliers are constant).

(d) (Curve.) There are polynomials $G \ne 0$ and $v_0 = 0, v_1, \dots, v_L$, pairwise distinct, $\gcd(v_1, \dots, v_L) = 1$, $\deg G + \max\deg v_i \le k - 1$, such that for every $x \in D$ with $G(x) \ne 0$ the values $v_i(x)$, $i \in J_x$, coincide. That is: the map $\Xi = (v_1 : \dots : v_L) : \mathbb{P}^1 \to \mathbb{P}^{L-1}$, of degree $\delta = \max\deg v_i \le k - 1 - \deg G$, sends every $x \in D$ off the roots of $G$ into the stratum $\{y_i = y_j \text{ for } i, j \in J_x\}$ of the braid arrangement ($y_0 = 0$).

*Proof.* (a) $\Leftrightarrow$ (b): a list is a point of $V(S)$ with pairwise distinct coordinates, the word being defined by $w = c_i$ on $S_i$, and a linear space over an infinite field that lies in no one of finitely many subspaces has a point outside all of them. (a) $\Leftrightarrow$ (c): with $e_i = w - c_i$, supported on $E_i$, the syndrome $y = He_i$ does not depend on $i$. Conversely $y \in \bigcap U_{E_i}$ has representations $y = He_i$, unique because $\lvert E_i\rvert \le n - k$, and $c_i = e_0 - e_i + c_0$ are codewords. $e_i = e_j$ iff both are supported on $E_i \cap E_j$. The map from pairs (word, point of $V(S)$) to points of $V(S)$ has fibres $F^{n - \lvert\bigcup S_i\rvert}$ and the map to tuples $(e_i)$ has the code as fibre, which gives the dimension. (a) $\Leftrightarrow$ (d): $G = \gcd_i(c_i - c_0)$ and $v_i = (c_i - c_0)/G$, and conversely $c_i = Gv_i$. For the dimension on independent points, Theorem 1.16 of [BGM] (note 17, Theorem 1.2) gives $\dim\bigcap_i U_{E_i} = \max_{\mathcal{P}}\bigl(\sum_{P}\lvert\bigcap_{i \in P}E_i\rvert - (\lvert\mathcal{P}\rvert - 1)(n - k)\bigr)$, and $\lvert\bigcap_{i \in P}E_i\rvert = n - \lvert\bigcup_{i \in P}S_i\rvert$, $\sum_P \lvert S^{\mathcal{P}}_P\rvert - \lvert\bigcup S_i\rvert = \sum_x(\lvert\mathcal{P}(J_x)\rvert - 1)^+$. $\square$

So on independent points the dimension is the naive count "unknowns minus equations", maximized over the ways to merge members. On a subspace the points are linear forms in $b$ and the same matrix has smaller rank at structured configurations. The rest of the note is about which ones.

**Remark 1.2 (module form). [proved, standard]** $\{(f_1, \dots, f_L) \in F[X]^L : f_i(x) = f_j(x),\ i, j \in J_x,\ f_0 = 0\}$ is a free $F[X]$-module of rank $L$ whose determinant has degree $I = \sum_x (\lvert J_x\rvert - 1)^+$. If $a_1 \le \dots \le a_L$ are the degrees of a reduced basis, then $\sum a_j = I$, a nontrivial solution of degree $< k$ exists iff $a_1 \le k - 1$, and for independent points a dimension count predicts that the $a_j$ differ by at most one unless a merging explains the imbalance (with $J$ of section 1.2 in the place of $I$ this is Lemma 1.4). All of the subspace theory is the statement that the module can be unbalanced: for a configuration cut out by a curve of degree $\delta = a_1$, $I - L\delta - (L - 1) = \sum_{j \ge 2}(a_j - a_1 - 1)$.

### 1.2 The count, and the excess

For a curve $\Xi = (v_1 : \dots : v_L)$ as in (d) and $x \in D$ let $j_x$ be the largest number of coinciding values among $v_0(x), \dots, v_L(x)$, and
$$J(\Xi) = \sum_{x \in D}(j_x - 1), \qquad \mathrm{exc}(\Xi) = J(\Xi) - L\delta - (L - 1) .$$
(For four members a point where two disjoint pairs coincide counts once in $J$. It imposes two conditions, and I write $I(\Xi) \ge J(\Xi)$ for the number of conditions, with $j_x - 1$ replaced by $L + 1$ minus the number of distinct values.)

**Lemma 1.3. [proved]** For every list with curve $\Xi$, common factor $G$ and $\gamma_D = \#\{x \in D : G(x) = 0\}$: $\sum_i \lvert S_i\rvert \le n + J(\Xi) + L\gamma_D$, with equality for the word that takes at each point a value shared by the most members. Hence for a list at agreement $T$
$$\mathrm{exc}(\Xi) \ \ge\ e_{L+1} := (L + 1)T - n - Lk + 1 .$$

*Proof.* The members that agree with $w$ at $x$ have equal values, so there are at most $j_x$ of them if $G(x) \ne 0$ and at most $L + 1$ otherwise. Then $(L+1)T \le n + J + L\gamma_D$ and $\delta + \gamma_D \le k - 1$. $\square$

**Lemma 1.4. [proved from note 17, Theorem 1.1, quoted from [BGM]]** On algebraically independent points $\mathrm{exc}(\Xi) \le 0$ for every curve with pairwise distinct coordinates.

*Proof.* Apply the generalized Singleton bound to the $L + 1$ polynomials $v_i$, of degree $< \delta + 1$, and the word of Lemma 1.3: $n + J \le n + L(\delta + 1) - 1$. $\square$

So $e_{L+1} \ge 1$ is the range where $L + 1$ members are impossible on independent points, and there every $L + 1$ members of a list on a subspace have a curve with positive excess. At rate 1/2: $e_3 \ge 1$ above $2n/3$, $e_4 \ge 1$ above $5n/8$, $e_{L+1} \ge 1$ above $(1 + L\rho)n/(L+1)$.

### 1.3 Lifting and the excess density

**Proposition 1.5 (lifting). [proved, every subspace domain]** Let $U \le D$, $D_0 = L_U(D)$, and $\Xi_0$ a curve of degree $\delta_0$ for $D_0$. Then $\Xi = \Xi_0 \circ L_U$ has $\delta = \lvert U\rvert\delta_0$, $J(\Xi) = \lvert U\rvert J(\Xi_0)$ and
$$\mathrm{exc}(\Xi) + L - 1 = \lvert U\rvert\,\bigl(\mathrm{exc}(\Xi_0) + L - 1\bigr) .$$
So the **excess density** $\epsilon(\Xi) = (\mathrm{exc}(\Xi) + L - 1)/n$ is invariant under lifting, a list of $L + 1$ members at rate $\rho$ has $\tau \le \frac{1 + L\rho + \epsilon(\Xi)}{L + 1}$, and a curve on $n_0$ points with at least $(\rho n_0 - \delta_0)$ points that are not special gives lists of $L + 1$ members with $\sum_i\lvert S_i\rvert = n(1 + L\rho + \epsilon) - L$ at rate $\rho$ for every $n = n_0\lvert U\rvert$.

*Proof.* $j_x$ depends on $L_U(x)$ only, and $L_U : D \to D_0$ is $\lvert U\rvert$ to one. For the last claim take $G$ of degree $k - 1 - \delta$ with all roots at points of $D$ where the values are pairwise distinct and use Lemma 1.3. $\square$

In particular a curve with $\mathrm{exc}(\Xi_0) = 0$, which exists by counting (one more unknown than equations), lifts to a curve with excess $(L - 1)(\lvert U\rvert - 1)$: **the period supplies the excess.** For three members this is all that happens (Conjecture P). The trivial lists ($T_0 = k_0$ on $n_0$ points, $\binom{n_0}{k_0}$ members) lift to the families at the dyadic points: $n_0 = 4, 8, 16$ with $k_0 - 1 = n_0/2$ give 4 members at $3n/4$, 56 at $5n/8$ and 11440 at $9n/16$, which are the numbers of the main document.

**Corollary 1.6 (four members beyond $5n/8$ at rate 1/2). [proved, given the list at $n = 16$, which is checked; and checked directly at $n = 32, 64, 128$]** For every $n = 16\lvert U\rvert \ge 32$ a generic subspace has lists of four codewords of degree $< n/2$ at agreement $T = 11n/16 - 1$, where independent points allow $T \le 5n/8 - 1$. With degree $\le n/2$ the agreement is $11n/16$.

*Proof.* `27_lists 9 11` finds four-member lists at $(n, k, T) = (16, 9, 11)$ whose differences have a common root $g_0 \in D_0$ (classes with `gamD` $\ge 1$, for instance the error sets `0117 02e8 5640 6a80`, curve of degree 7 with $J = 25$). Compose with $L_U$ (note 02, Lemma 3): four polynomials of degree $\le n/2$ with agreement $11n/16$. Divide the differences by $X - g$ for one $g \in D$ with $L_U(g) = g_0$ (the twist of note 17, Proposition 2.4): the degree drops to $< n/2$ and every agreement set loses only $g$. `27_lift` builds the lifted curve with a common factor of degree $n/2 - 1 - \delta$ whose roots are points of $D$ with pairwise distinct values, and counts the agreements with the word of Lemma 1.3: $(21, 21, 21, 22)$ of 32, $(43, 43, 43, 44)$ of 64, $(87, 87, 87, 88)$ of 128. $\square$

Consequences. (i) Since a list at agreement $T$ is a list at every smaller agreement, four-member lists exist on generic subspaces in the whole rate-1/2 window $(5/8, 2/3]$ and up to $11/16$. (Consistent with note 18: its exact maximum at $(16, 8, 11)$ is 3, where the corollary gives nothing, and it finds at least 16 members at $(32, 16, 21)$.) (ii) The triples inside these lists have $e_3 = n/16 - 2$ and period $n/16$, so they are extremal for Conjecture P up to one unit. (iii) Any four-member theorem in the window must therefore be a structure theorem, as P is for three members above $2n/3$, and cannot be a non-existence theorem.

## 2. Four members: eight functions and a symmetry

Let $L = 3$, $\Xi = (v_1 : v_2 : v_3)$, $v_0 = 0$, and $d_{ij} = v_i - v_j$. The six lines $y_i = y_j$ of $\mathbb{P}^2$ meet three at a time in four points $p_l$ (the three members other than $l$ coincide) and pairwise elsewhere in three points (two disjoint pairs coincide). A point of $D$ is a *pair point*, a *triple point* or a *double pair point* of $\Xi$ accordingly, and $J = \#\text{pair} + 2\,\#\text{triple} + \#\text{double}$, $I = \#\text{pair} + 2\,\#\text{triple} + 2\,\#\text{double}$.

**The eight functions.** The *triple functions* $\xi_l = d_{ab}/d_{ac}$ for $\{a, b, c\} = \{0, 1, 2, 3\} \setminus \{l\}$ (the function of note 17 for the three members other than $l$; its degree is at most $\delta - m_l$, $m_l$ the degree of the gcd of the three differences). The *cross-ratio* $\Phi = d_{01}d_{23}/(d_{02}d_{13})$, of degree at most $2\delta - \sum_l m_l$, with fibres over $0, \infty, 1$ containing $R_{01} \cup R_{23}$, $R_{02} \cup R_{13}$, $R_{03} \cup R_{12}$ ($R_{ij}$ the roots of $d_{ij}$ in $D$). The *opposite ratios* $\zeta_1 = d_{01}/d_{23}$, $\zeta_2 = d_{02}/d_{13}$, $\zeta_3 = d_{03}/d_{12}$: the three products of opposite differences $d_{01}d_{23}$, $d_{02}d_{13}$, $d_{03}d_{12}$ add up to zero, $\Phi$ is the quotient of the first two, and the $\zeta_i$ are the quotients inside each product. The five functions $\xi_l, \Phi$ are the cross-ratios of the five marked values $(c_0, c_1, c_2, c_3, \infty)$, that is the five forgetful maps of $\overline{M}_{0,5}$, the blow-up of $\mathbb{P}^2$ in the four points $p_l$. The $\zeta$ are not invariant under $\mathrm{PGL}_2$ but they are units on the complement of the six lines, and a monomial in the $d_{ij}$ of degree zero is the general such unit. $\Pi(\Xi) = \bigcap_\chi \Pi(\chi) = \Pi(\xi_3) \cap \Pi(\xi_2)$.

**Proposition 2.1 (Cremona symmetry). [proved]** Let $g = \gcd(v_2v_3, v_1v_3, v_1v_2)$ and $\Xi' = (v_2v_3 : v_1v_3 : v_1v_2)/g$ (the configuration $1/(c_i - c_0)$). Then $\Xi'$ is a four-member curve of degree at most $2\delta - m_1 - m_2 - m_3$, pair points of type $\{i, j\}$ with $i, j \ne 0$ and triple points of type $\{1, 2, 3\}$ keep their type, pair points of type $\{0, i\}$ become triple points of type $\{0, j, l\}$ and conversely, the triple function of the members $1, 2, 3$ of $\Xi'$ is a cross-ratio of $\Xi$, and $\Pi(\Xi') = \Pi(\Xi)$. Together with the permutations of the members this is the action of $S_5$ on $\overline{M}_{0,5}$.

*Proof.* $(1/v_1 - 1/v_2)/(1/v_1 - 1/v_3) = v_3 d_{12}/(v_2 d_{13})$, a cross-ratio of $(0, v_1, v_2, v_3)$. At a root of $v_i$ only, two coordinates of $\Xi'$ vanish. At a common root of $v_j, v_l$ the factor is in $g$ and after division one coordinate vanishes. $\square$

It exchanges the two basic non-periodic mechanisms below ("a periodic triple and a fourth member through its points" with "a periodic cross-ratio"), and it is why periods of all five cross-ratio functions must enter a four-member statement.

## 3. All four-member lists at $n = 16$

### 3.1 The computation

**[checked, exhaustive]** `27_lists.c`: $D$ a random 4-dimensional subspace of $\mathrm{GF}(2^{64})$. In the syndrome form of Theorem 1.1 (c), four $t$-sets carry a list iff the $4m \times (n - k)$ matrix of shifted locators has a kernel vector outside the degenerate loci. The program takes $E_0$ over the orbits of $\mathrm{AGL}(4, 2)$, $E_1$ over the orbits of the stabilizer, every $E_2$, computes the syndrome space of the triple, scans every $E_3$, and for every list reconstructs the codewords, the curve $\Xi$, its incidences, and the degree, the number $\nu$ of points of $D$ over $\{0, 1, \infty\}$ and the period group of each of the eight functions. Counts are weighted to exact numbers of unordered quadruples of error sets. A system that has no solution for the random basis has none for the generic one, so absences are rigorous for generic $D$ up to the correctness of the program, and presences hold for the basis used (a second basis, seed 2, gives the same totals and the same 18 and 25 classes at $(12, 13)$ and $(9, 11)$). The parameter points are those where four members beat the count for independent points and three do not ($d/2 \le m \le d - 1$), with $m = d - 1$ or $m = 2$.

| $(k, T)$ | $(t, d, m)$ | $e_4$ | lifts to rate, $\tau$ | four-member lists | classes | $\mathrm{exc}$ of the curves | no period of the curve: by $\mathrm{exc}$ | no period of any of the eight functions: by $\mathrm{exc}$ | Q violated |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $(12, 13)$ | $(3, 2, 1)$ | 1 | $11/16$, $13/16$ | 4164160 | 18 | 1, 2 | 1: 3692080 | 1: 592480 | 0 |
| $(9, 11)$ | $(5, 3, 2)$ | 2 | $1/2$, $11/16$ | 16289280 | 25 | 2, 3, 4, 6 | 2: 6347040, 3: 3628800 | 2: 80640 | 0 |
| $(8, 10)$ | $(6, 4, 2)$ | 1 | $7/16$, $5/8$ | 40424540520 | 567 | 1, 2, 3, 4 | 1: $3.73 \cdot 10^{10}$, 2: $1.85 \cdot 10^9$, 3: $6.1 \cdot 10^8$ | 1: $1.08 \cdot 10^9$, 2: 6612480 | 0 |
| $(6, 9)$ | $(7, 4, 3)$ | 3 | $5/16$, $9/16$ | 7758240 | 10 | 3, 4 | 3: 5564160 | none | 0 |
| $(3, 7)$ | $(9, 5, 4)$ | 4 | $1/8$, $7/16$ | 20160 | 1 | 4 | none | none | 0 |

("Lifts to" is the rate $(k - 1)/16$ and the agreement fraction of the lists that Proposition 1.5 produces from the row. The points $(5, 8)$, $(2, 6)$ and $(4, 7)$, with syndrome spaces of dimension 2 or 3 and 11440 sets, were not run (more than an hour each by the timing of $(8, 10)$).) In every list $\mathrm{exc} \ge e_4$, as Lemma 1.3 demands. `27_summary.py` produces the columns from the class histograms.

### 3.2 What the classes are

Each class is a value of the invariant vector (degree, common factor, numbers of pair, triple and double points, period group of the curve, the triples $(\deg, \nu, \lvert\Pi\rvert)$ of the eight functions). The mechanisms, with one example each (error sets as hex masks, $(k, T)$ in brackets):

1. **Lifts** ($\lvert\Pi(\Xi)\rvert \ge 2$). All of them have $\mathrm{exc} + 2 = \lvert\Pi\rvert(\mathrm{exc}_0 + 2)$ for a curve on $D/\Pi$ of one of the types below or of excess 0. Example: `001f 00f1 0f01 f001` $[9, 11]$, the curve of four parallel planes (member $l$ errs on plane $l$), $\delta = 8$, 16 triple points, $\mathrm{exc} = 6 = 4 \cdot 0 + 2 \cdot 3$. The only class at $(3, 7)$ is the lift through $\{0, a\}$ of four lines on 8 points with their six intersections in $D/a$ ($\mathrm{exc} = 2 \cdot 1 + 2$), the quadrilateral of note 18.
2. **A periodic triple and a fourth member** (one $\xi_l$ periodic, the curve not). Example: `001f 0f10 1164 f010` $[9, 11]$: $\xi$ of three members is $\mu \circ L_U$, $\lvert U\rvert = 4$ ($\deg 4$, $\nu = 12$), the other three triple functions have $\nu = 2\deg + 1$ and no period, $\mathrm{exc} = 2 \le \lvert U\rvert - 1$. Here the Wronskian of the curve has full degree: the excess is invisible at infinity.
3. **A periodic cross-ratio** (the Cremona image of 2). The smallest case is degree one: four lines whose six intersection abscissae are three pairs with a common difference $s$, `0007 0034 0052 0061` $[12, 13]$, $\Phi$ of degree 2 with $\nu = 6$ and period $s$, all triple functions of degree 1, $\mathrm{exc} = 1$ (Proposition 5.3).
4. **Several functions periodic along different subspaces.** `001f 0711 3403 5205` $[9, 11]$: $\delta = 3$, $J = 14$, $\mathrm{exc} = 3$, all four $\xi_l$ and $\Phi$ have a period group of size 2, the curve has none. On 8 points there is a totally split curve of degree 3 with four triple points (an affine plane $P$), three double pair points and one common root (the other coset of $P$), in which the four $\xi_l$ are periodic along the four directions outside $P$ and the three $\zeta$ along the three directions of $P$. Its lift is `0117 01e8 0e18 3224` $[9, 11]$ ($I = 28$, $J = 22$).
5. **Sum relations, no period of anything.** `0007 0034 0502 1420` $[12, 13]$: $\delta = 3$, four pair points and four triple points, all eight functions without period, $\mathrm{exc} = 1$. The four error sets are 3-sets with the same sum, and that is the whole reason (Proposition 5.4). `27_generalize` confirms it: of the $\mathbb{F}_2$-linear relations between the eight special points exactly the three relations "equal sums" are needed. Further examples: `003f 01c7 0c5a 0da8` $[8, 10]$, a conic with nine pair points ($\Phi$ of degree 4 with $\nu = 9$), needs three relations (a plane $\{p, p + s_1, p + s_2, p + s_1 + s_2\}$ carrying the types $13, 12, 03, 02$, a pair of type $01$ with difference $s_1$, a pair of type $23$ with difference $s_2$, and one free point): the translations by $s_1$ and $s_2$ act on the types as the transpositions $(2\,3)$ and $(0\,1)$, a twisted period of a part of the configuration. `0117 022b 4d04 80e8` $[9, 11]$, $\delta = 6$, six pair and eight triple points, $\mathrm{exc} = 2$, the only class of excess 2 without any period (it occurs at $(9, 11)$ and at $(8, 10)$): 8 of the 9 relations between its 14 points are needed, so it is essentially a configuration of the 16-point space itself.

**[checked]** The three natural analogues of Conjecture P are false:

- "*Excess needs a period of the curve*": false by mechanisms 2 to 5 ($3.7 \cdot 10^{10}$ lists at $(8, 10)$).
- "*$\mathrm{exc} \le (\max_Q\lvert\Pi_Q\rvert - 1) + (\lvert\Pi(\Xi)\rvert - 1)$ over the five cross-ratio functions*" (the formula that a parameter count for nested periodic structures gives, and that I expected): false by mechanism 5 (592480 lists at $(12, 13)$ with excess 1 and no period, 80640 at $(9, 11)$ with excess 2) and by mechanism 4.
- "*Excess forces ramification at infinity*" (the four-member reading of note 17, Theorem 3.2): false, mechanism 2 has $\deg(\Xi \times \Xi') = 2\delta - 2$.

What survives in all 621 classes: **excess 3 or more always comes with a period of one of the eight functions, and the excess never exceeds the largest period group by more than 1 unless the curve itself is periodic.**

## 4. Conjecture Q

### 4.1 Statement

**Conjecture Q. [conjectured]** Let $D$ be a generic subspace and $\Xi$ a four-member curve (pairwise distinct coordinates, any field). Then
$$\mathrm{exc}(\Xi) \ \le\ \max_\chi\lvert\Pi(\chi)\rvert + 3\lvert\Pi(\Xi)\rvert - 2, \qquad \chi \in \{\xi_0, \xi_1, \xi_2, \xi_3, \Phi, \zeta_1, \zeta_2, \zeta_3\} .$$

**Lemma 4.1. [proved]** Q is equivalent to Q$_0$: *if $\Pi(\Xi) = 0$ then $\mathrm{exc}(\Xi) \le 1 + \max_\chi\lvert\Pi(\chi)\rvert$*. In particular Q asserts $\mathrm{exc} \le 2$ for a curve none of whose eight functions has a period.

*Proof.* $\Xi = \Xi_0 \circ L_\Pi$ with $\Pi = \Pi(\Xi)$, $L_\Pi(D)$ is generic (note 17, Lemma 4.1), $\Pi(\Xi_0) = 0$, $\lvert\Pi(\chi)\rvert = \lvert\Pi\rvert\lvert\Pi(\chi_0)\rvert$, and by Proposition 1.5 $\mathrm{exc} = \lvert\Pi\rvert\mathrm{exc}_0 + 2(\lvert\Pi\rvert - 1)$. $\square$

Consequence used below: $\mathrm{exc}(\Xi) + 2 \le 4\max_\chi\lvert\Pi(\chi)\rvert$. The constant 4 cannot be lowered (the class without periods and excess 2). The constant 2 would be the value if only periods existed.

How Q relates to P: for three members the excess is at most $\lvert\Pi(\xi)\rvert - 1$, there is one function, and no sporadic term. For four members the right-hand side has a sporadic term ($+1$ per coset of $\Pi(\Xi)$, on top of the $2$ per coset that a period of the curve explains) and a maximum over functions. I do not claim that $1$ is the right sporadic term for all $n$: it is the value at $n = 16$. The honest form of the conjecture for large $n$ is "$\mathrm{exc} + 2 \le C_4 \max_\chi\lvert\Pi(\chi)\rvert$ for an absolute constant $C_4$", and the data say $C_4 \ge 4$.

### 4.2 Evidence

**[checked, exhaustive]** Zero violations among the $4.05 \cdot 10^{10}$ four-member lists of section 3 (621 classes), with equality in the classes without periods of excess 2 and in mechanism 4.

**[checked]** Conics at $n = 32$ (`27_conics.c`, two bases): the six affinely independent points $0, b_1, \dots, b_5$ with every labelling by pair types (first label $01$, at most two points per type) and two more labelled points, $2.66 \cdot 10^7$ configurations, 99.99% of them with a unique conic, and every conic counted against all 32 points. The conics with $J \ge 10$ form one class: the lift through a period $\{0, a\}$ of a line with five pair points on 16 points ($J = 10$, $\mathrm{exc} = 2 = 2(\lvert\Pi\rvert - 1)$). The conics with $J = 9$ and no period are the types already present at $n = 16$ (nine pair points, $\Phi$ of degree 4 with $\nu = 9$; or seven pair points and a triple point). So on 32 points no conic without period has excess 2, and no conic at all has $J \ge 11$, among the conics determined by eight pair points six of which are affinely independent (not covered: conics with two triple points and at most seven pair points, and conics whose special points lie in a 16-point subspace, which are those of section 3). Zero violations of Q.

**[proved]** Cases of Q: degree one (Proposition 5.3: $\mathrm{exc} \le 1$, with equality iff $\Phi$ has a period). Curves all of whose six differences split over $D$ have every triple function of the form $\mu \circ L_U^q$ (Theorem 5.1).

**[proved, and checked at $n = 32$ by `27_grid.c`]** The grids. Let $U_1 \cap U_2 = 0$, $\lvert U_1\rvert = \lvert U_2\rvert$, and $P_1, P_1'$ cosets of $U_1$, $P_2, P_2'$ cosets of $U_2$, pairwise disjoint. The four sets $P_1^{(\prime)} \cup P_2^{(\prime)}$ share $e_1, \dots, e_{\lvert U_i\rvert - 1}$ (their locators are $(L_{U_1} + \alpha)(L_{U_2} + \beta)$), so they are the error sets of a strict-top list. Its curve is $(\lambda_1 Z_{P_2'} : \lambda_2 Z_{P_1'} : A)$ with $A = \beta L_{U_1} + \alpha L_{U_2} + c$, of degree $\lvert U_i\rvert$, with the four cosets as pair points: $J \ge 4\lvert U_i\rvert$ and $\mathrm{exc} \ge \lvert U_i\rvert - 2$. The triple functions ($\lambda Z_{P_2'}/Z_{P_1'}$, $\lambda Z_{P_2'}/A$ and so on) have no period, the curve has none, and the opposite ratios $\zeta_1 = \lambda Z_{P_2'}/Z_{P_2}$ and $\zeta_2 = \lambda' Z_{P_1'}/Z_{P_1}$ have the period groups $U_2$ and $U_1$. At $n = 32$ with two planes: $\delta = 4$, $J = 16$, $\mathrm{exc} = 2$, triple functions $(4, 8, 1)$, opposite ratios with period groups of sizes 4, 4, 2, and $\Phi$ of degree 8 with $\nu = 16$ and the period group $(U_1 + \langle a\rangle) \cap (U_2 + \langle b\rangle)$ of size 4, where $a, b$ are the differences of the two pairs of cosets (it is trivial in larger dimensions). So the opposite ratios are needed in Q, the excess of a curve without period is unbounded as $n$ grows, and Q holds for the grids with room ($\lvert U\rvert - 2 \le \lvert U\rvert + 1$).

**What the evidence does not cover.** Degrees above 2 at $n = 32$, everything at $n \ge 64$. The sporadic term could grow with $n$. And at $n = 16$ every statement of the form "there is a period group of index at most 16" is empty, so the data test the shape of Q and not its use in the windows (section 6.4).

## 5. What is proved

### 5.1 Split triples: Conjecture P when all roots are in $D$

**Theorem 5.1. [proved]** Let $D$ be generic, $F$ any field containing it, and $u_0 + u_1 + u_2 = 0$ pairwise coprime polynomials, not all constant, each of which splits into linear factors with roots in $D$ (multiplicities allowed). Then there are a subspace $U \le D$, a power of two $q$ and elements $\alpha_i, \lambda_i \in F$ with $u_i = \lambda_i(L_U + \alpha_i)^q$ for every nonconstant $u_i$. In particular $\xi = u_0/u_1 = \mu \circ L_U^q$ with $\mu$ of degree one, $\Pi(\xi) = U$, and $\nu(\xi) \le 3\lvert U\rvert \le 2\deg\xi + \lvert\Pi(\xi)\rvert$.

*Proof.* Write $u_i = \lambda_i\prod_{y \in D}(X - y)^{m_i(y)}$, the supports of the $m_i$ pairwise disjoint. Let $x, x'$ be roots of $u_2$. Then $u_0(x) = u_1(x)$ and $u_0(x') = u_1(x')$, so
$$\prod_y (x + y)^{m_0(y)}(x' + y)^{m_1(y)} = \prod_y (x' + y)^{m_0(y)}(x + y)^{m_1(y)} .$$
Every factor is a nonzero element of $D$, that is a nonzero linear form in $b_1, \dots, b_N$ over $\mathbb{F}_2$. These are irreducible and pairwise non-associate in the factorial ring $\mathbb{F}_2[b]$, so the two sides have the same multiset of factors: $\tau_x m_0 + \tau_{x'}m_1 = \tau_{x'}m_0 + \tau_x m_1$ with $(\tau_x m)(z) = m(z + x)$. So $m_0 - m_1$ is invariant under the translation by $x + x'$, and since the supports are disjoint so are $m_0$ and $m_1$. Let $U_i$ be the span of the differences of the roots of $u_i$. Then $m_j$ is $U_i$-periodic for $j \ne i$, and its support lies in one coset of $U_j$. If the three are nonconstant this gives $U_1 + U_2 \subseteq U_0$ and cyclically, so $U_0 = U_1 = U_2 = U$ and $m_i = \mu_i 1_{a_i + U}$, $u_i = \lambda_i(L_U + \alpha_i)^{\mu_i}$ with $\alpha_i = L_U(a_i)$ distinct. If $u_0$ is constant the same argument with $u_1, u_2$ gives $U_1 = U_2$. It remains to see that $\sum_i \lambda_i(Y + \alpha_i)^{\mu_i} = 0$ in $F[Y]$ forces $\mu_i = q$. Take $2^s$-th roots until some exponent is odd. Then the Wronskian $W$ of two of the three is nonzero, it is the same for each pair, it is divisible by $(Y + \alpha_i)^{\mu_i' - 1}$ for all $i$, and $\deg W \le \mu_i' + \mu_j' - 1$ for each pair, so every $\mu_i' \le 2$ (Mason-Stothers). The cases $(1, 1, 2)$ and $(1, 2, 2)$ are excluded by the coefficient of $Y^2$, the case with a constant term is the same computation, and $(1, 1, 1)$ remains. $\square$

Remarks. (i) This is the place method of notes 04 and 12 at the places of the pairs $\{0, a\}$, in the one situation where it loses nothing: with all roots in $D$ there are no unknown cofactors, and a valuation inequality becomes an identity between monomials. With cofactors $h_i$ of degree $\eta$ the relation at the roots of $u_2$ says that a rational function of degree $\eta$ interpolates the values $Z_{R_1}/Z_{R_0}$, which is a sum of monomials and not one, and unique factorization does not apply. (ii) It proves Conjecture P at the end opposite to the partial results of note 17: there derivations give ramification at infinity for any excess but no period, here $\nu = 3\deg\xi/q$ is as large as it can be and the period itself comes out. (iii) It fails on the real domain, where products of elements of $D$ are reduced modulo the field polynomial as soon as three factors are involved ($3(N - 1) > 63$).

**Corollary 5.2 (totally split four-member curves). [proved]** Let all six differences of a four-member curve on a generic $D$ split over $D$, $d_{ij} = \lambda_{ij}Z_{M_{ij}}$ with multisets $M_{ij}$ on $D$. Then for each of the four triples, after removing the common part of its three multisets (its triple points), the three remainders are $q$ times three cosets of one subspace, with $U$ and $q$ depending on the triple. Conversely, multisets with this property for the three triples through member 0 come from a curve iff one more identity holds: the ratios $\lambda_{01}/\lambda_{02}$, $\lambda_{02}/\lambda_{03}$, $\lambda_{03}/\lambda_{01}$, each read off as a quotient of products of elements of $D$ at a root of $d_{12}$, $d_{23}$, $d_{13}$, multiply to 1. That is again an identity of multisets in $D$. So totally split four-member configurations are classified by combinatorics in $\mathbb{F}_2^N$ (Proposition 5.3 is the case of degree one).

*Proof.* Theorem 5.1 for each triple, after division by the gcd. The fourth triple relation follows from the three through member 0, and each of these fixes the ratio of two of $\lambda_{01}, \lambda_{02}, \lambda_{03}$. $\square$

### 5.2 Degree one

**Proposition 5.3 (four lines). [proved]** Let $c_i = \alpha_i X + \beta_i$, $i = 0, \dots, 3$, be four polynomials of degree at most one over a field containing $D$. (i) On every subspace domain: if six distinct points $x_{ij} \in D$ satisfy $x_{01} + x_{23} = x_{02} + x_{13} = x_{03} + x_{12}$, there are four such lines with $c_i(x_{ij}) = c_j(x_{ij})$, so $J = 6 = 3\delta + 3$. (ii) On a generic subspace the converse holds: if the six pairwise intersections have distinct abscissae in $D$, the three sums are equal. So a four-member curve of degree one has $\mathrm{exc} \le 1$, with equality iff its special points are three cosets of some $\{0, s\}$ matched as opposite pairs, iff $\Phi = \Phi_0 \circ L_{\{0, s\}}$.

*Proof.* With $v_i = a_i(X - x_{0i})$ the conditions $v_i(x_{ij}) = v_j(x_{ij})$ determine the ratios $a_1/a_2$, $a_2/a_3$, $a_3/a_1$, and they are consistent iff
$$(x_{12} - x_{02})(x_{23} - x_{03})(x_{13} - x_{01}) = (x_{12} - x_{01})(x_{23} - x_{02})(x_{13} - x_{03}) .$$
(This is the condition that the six points are a quadrangular set, and the theorem of Desargues on the involution cut out on a line by the conics through four points.) (i) If the sums equal $s$ the two sides have the same three factors. (ii) Both sides are products of three nonzero linear forms in $b$, so the multisets agree. $x_{12} + x_{02}$ equals neither $x_{12} + x_{01}$ nor $x_{23} + x_{02}$ (the points are distinct), so it equals $x_{13} + x_{03}$, and then the remaining factors match in only one way. $\square$

The translation by $s$ sends the type $\{i, j\}$ to the complementary type. No permutation of the members does that: it is the involution of the pencil of conics and not a twisted period of the curve.

### 5.3 Sum relations

**Proposition 5.4. [proved, every subspace domain with $N \ge 2$]** Any number of $t$-sets $E_i \subseteq D$ with the same sum $s = \sum_{x \in E_i} x$ are the error sets of a list at $k = n - t - 1$, $T = n - t = k + 1$: $w = X^T + sX^{T-1}$ and $c_i = w - Z_{D \setminus E_i}$. Independent points allow $t$ members there. For four members ($t = 3$) the curve has $\mathrm{exc} = 1$, and at $(12, 13)$, $n = 16$, the sets need not have any other structure.

*Proof.* $e_1(D \setminus E_i) = \sum_{x \in D}x + s = s$. $\square$

This is the classical strict top at $T = k + 1$ (note 02), far below the windows. Its relevance here is that its twists and lifts are the lists without periods in section 3, and that it is the first member of the family "two sets share $e_1, \dots, e_{2^a - 1}$ if and only if their counts on every hyperplane are congruent modulo $2^a$" (Theorem W of note 02 and its converse): unions of equally many cosets of $U$ are the special case of depth $\lvert U\rvert - 1$. A statement in which "the depth of a common top", suitably defined for a list and invariant under twists, replaces $\lvert\Pi\rvert - 1$ would unify P, Q and the grids. I did not find the definition.

### 5.4 A four-member Frobenius-Euler identity

Let $F_0 = \mathbb{F}_2(b)(t_1, t_2, \dots)$ with the derivations $\partial_i = \partial/\partial b_i$ and $\partial_X$ as in note 17, section 3, and $\mathfrak{E}_q = X^q\partial_X + \sum_i b_i^q\partial_i$ for $q$ a power of two. $\mathfrak{E}_q(X - x) = (X - x)^q$ for $x \in D$.

**Theorem 5.5. [proved]** Let $\Xi = (v_1, v_2, v_3) \in F_0[X]^3$ be a four-member curve of degree $\delta$, $I$ its number of conditions at the points of $D$ (pair points 1, triple and double pair points 2), and $T_{q,q'} = \det(\Xi, \mathfrak{E}_q\Xi, \mathfrak{E}_{q'}\Xi)$. Then $\deg T_{q,q'} \le \Delta_q + \Delta_{q'} - \delta$ with $\Delta_q = \max(2\delta, 2\delta + q - 2)$, and $T_{q,q'}$ vanishes at every pair point and to order two at every triple or double pair point. Hence
$$I > \Delta_q + \Delta_{q'} - \delta \ \Longrightarrow\ \det(\Xi, \mathfrak{E}_q\Xi, \mathfrak{E}_{q'}\Xi) = 0 :$$
for $I \ge 3\delta + 1$ with $(q, q') = (1, 2)$, for $I \ge 3\delta + 3$ (any excess) with $(1, 4)$ and $(2, 4)$, and for $\mathrm{exc} \ge q + q' - 5$ in general ($2 \le q < q'$).

*Proof.* $Y_q = \Xi \times \mathfrak{E}_q\Xi$ has the components $X^q(v_jv_l' + v_lv_j') + \sum_i b_i^q(v_j\partial_iv_l + v_l\partial_iv_j)$, of degree $\le \max(2\delta - 2 + q, 2\delta)$ (the Wronskian of two polynomials of degree $\le \delta$ has degree $\le 2\delta - 2$ in characteristic two). $Y_q \times Y_{q'} = T_{q,q'}\,\Xi$, so $\deg T_{q,q'} + \delta \le \Delta_q + \Delta_{q'}$. Let $\ell$ be one of the six linear forms $y_i - y_j$ and $x \in D$ a root of $\ell(\Xi)$ of multiplicity $r$: $\ell(\Xi) = (X - x)^r g$ and $\ell(\mathfrak{E}_q\Xi) = \mathfrak{E}_q(\ell(\Xi)) = r(X - x)^{r - 1 + q}g + (X - x)^r\mathfrak{E}_q g$ is divisible by $X - x$. So one row of the determinant, in coordinates containing $\ell$, is divisible by $X - x$, and two rows are if $\Xi(x)$ lies on two of the six lines. $\square$

For three members the same argument gives note 17, Theorem 3.2 (the $2 \times 2$ determinant $\xi\,\mathfrak{E}_q\xi$-Wronskian vanishes when $\nu > 2\delta + q - 2$). The difference is the rank: three members get $\mathfrak{E}_q\Xi \parallel \Xi$, four members only get that $\Xi$ and its Frobenius-Euler derivatives span a space of rank at most two, that is a field of lines through the points of the curve that contains all these derivatives. If that field of lines is the pencil through one of the four points $p_l$, the triple function $\xi_l$ is killed by the $\mathfrak{E}_q$, which is mechanism 2. For a configuration with a unique solution, $\mathfrak{E}_1\Xi$ and $\mathfrak{E}_2\Xi$ are proportional to $\Xi$ over $F_0(X)$ **[proved, sketch]**: the scalings $b \mapsto \lambda b$ and, to first order in $\epsilon$, the maps $x \mapsto x/(1 + \epsilon x) = x + \epsilon x^2 + \dots$ send the configuration to the configuration of the subspace with basis $\lambda b$, respectively $b + \epsilon b^2$, they preserve degrees and incidences, and the kernel of a matrix of corank one has a derivative that depends only on the derivative of the matrix. So the first case with content is $(q, q') = (4, 8)$, $\mathrm{exc} \ge 7$. I have not derived a period from it.

**Proposition 5.6 (codimension two). [proved]** In the same setting let $f, f'$ be two affine functions $D \to \mathbb{F}_2$ with $H = \{f = 0\}$, $H' = \{f' = 0\}$ not parallel, and $\Theta_f = \sum_i f_i\partial_i\Xi + f_0\partial_X\Xi$. Then $\det(\Xi, \Theta_f, \Theta_{f'})$ has degree $\le 3\delta$ and vanishes at the special points in $H \cap H'$ with their multiplicities, so either it is zero or the affine subspace $H \cap H'$ of codimension two carries at most $3\delta$ of the $I$ conditions. (For three members the analogue is note 17, Lemma 3.1, with hyperplanes and $2\delta$, and there the degenerate alternative was resolved. Here it is not.)

*Proof.* As for 5.5, with $(\sum_i f_i\partial_i + f_0\partial_X)(X - x) = f(x)$. $\square$

### 5.5 Elementary facts valid on every domain

**Lemma 5.7. [proved]** (i) If $(L + 1)T \ge n + Lk - L + 1$ no $L + 1$ members of a list are collinear. In particular in the range $e_4 \ge -1$ no four members lie on a line $c_0 + F u$, so $\Xi$ is not constant. (ii) For $a \in D \setminus \Pi(\Phi)$: $\sum_{i=1}^{3}\lvert F_i \cap (F_i + a)\rvert \le 2\deg\Phi \le 4\delta - 2\sum_l m_l$, where $F_1 = R_{01} \cup R_{23}$, $F_2 = R_{02} \cup R_{13}$, $F_3 = R_{03} \cup R_{12}$, on every subspace domain. (iii) The same for each triple function (note 17, Proposition 3.4).

*Proof.* (i) Outside the at most $k - 1$ zeros of $u$ the values $c_0 + s_iu$ are pairwise distinct: $(L+1)T \le n + L(k - 1)$. (ii) The numerator of $\Phi(X + a) - \Phi(X)$ has degree $\le 2\deg\Phi$ and vanishes at $x$ when $x$ and $x + a$ are in the same fibre. $\square$

### 5.6 The "if" directions

**Proposition 5.8. [proved, every subspace domain]** Each of the following produces four-member curves with the stated $J$, hence lists by Lemma 1.3 and Proposition 1.5.

1. (Lift.) $\Xi_0 \circ L_U$: $J = \lvert U\rvert J_0$.
2. (Periodic triple and a fourth member.) Let $\xi_0$ on $D/U$ have $\nu_0 \le 2\delta_0 + 1$ points in three fibres, $u_i$ the lifted differences of three members $c_1, c_2, c_3$, of degree $\delta = \lvert U\rvert\delta_0$. Any $c_0$ of degree $\le \delta$ that takes, at $\delta + 1$ further points of $D$, the value of one of the $c_i$ gives $J = \lvert U\rvert\nu_0 + \delta + 1 = 3\delta + 2 + (\lvert U\rvert - 1)$ when $\nu_0 = 2\delta_0 + 1$: $\mathrm{exc} = \lvert U\rvert - 1$.
3. (Cremona.) The image of 2 under Proposition 2.1 has a periodic cross-ratio.
4. (Opposite ratios.) The grids of section 4.2: $\mathrm{exc} \ge \lvert U\rvert - 2$ with two period groups that meet in 0.
5. (Sum relations.) Proposition 5.4.

*Proof.* 1 is Proposition 1.5. 2: interpolation, $\delta + 1$ conditions on $\delta + 1$ coefficients. 3, 4, 5 are stated where they are proved. $\square$

## 6. A conditional list bound

### 6.1 The hypothesis

For the argument of note 17, Theorem 5.1, a period helps when it confines a member to an affine space of codewords of small dimension. That is the case for the triple functions and the opposite ratios, and not for the cross-ratio (section 6.6).

**Hypothesis H4($C$). [conjectured for $C = 4$]** For every four-member curve on a generic subspace,
$$\mathrm{exc}(\Xi) + 2 \ \le\ C \cdot \max\bigl\{\lvert\Pi(\chi)\rvert : \chi \in \{\xi_0, \xi_1, \xi_2, \xi_3, \zeta_1, \zeta_2, \zeta_3\}\bigr\} .$$

**[checked]** H4(4) holds for all classes of section 3 (the largest ratio is 4.00, in the class without periods, and 3.00 in the lifts of four lines, where only $\Phi$ has the larger period). H4(2) is the best one can hope for (the lift of a curve of excess 0 has ratio exactly 2). H4 is not a consequence of Q: a curve in which only the cross-ratio has a large period would satisfy Q and violate H4. By Proposition 2.1 such a curve is the Cremona image of mechanism 2. In the one case I worked out by hand (a periodic triple with a period group of size 4 and a fourth member through five of its twelve points) the image has $J = 12$ at degree 3, excess 1, because the points that should become triple points are roots outside $D$. **[heuristic]** I have no proof that this is always so, and in the data a nonconstant $\Phi$ never has a period group more than twice as large as the largest of the other seven.

### 6.2 The class lemma

Let $\mathcal{L} = L_{\Pi^\ast}(X)$ for a subspace $\Pi^\ast$ of size $\pi^\ast$, $\delta^\ast = \lfloor (k - 1)/\pi^\ast\rfloor$, and $A(r) = \prod_{i=1}^{r}\frac{n - k + i}{T - k + i}$, the bound of note 04, Theorem 1.2, for the number of list members in an affine space of codewords of dimension $r$.

**Lemma 6.1. [proved, every subspace domain]** Let $c_a \ne c_b$ be polynomials of degree $< k$. (i) The polynomials $c$ of degree $< k$ with $(c - c_a)/(c_b - c_a) \in F(\mathcal{L})$ lie in an affine space $c_a + \rho\cdot\{P(\mathcal{L}) : \deg P \le \delta^\ast\}$ that contains $c_a$ and $c_b$. (ii) For a third polynomial $c_c$, the $c$ with $(c - c_c)/(c_b - c_a) \in F(\mathcal{L})$ lie in $c_c + \rho\cdot\{P(\mathcal{L}) : \deg P \le \delta^\ast\}$. So a list has at most $A(\delta^\ast + 1)$ members in each of these sets.

*Proof.* (i) is in the proof of note 17, Theorem 5.1: with $u = c_b - c_a$ and $(c - c_a)/u = p(\mathcal{L})/q(\mathcal{L})$ in lowest terms, $q(\mathcal{L})$ divides $u$, the monic $q$ with this property have a largest element $q_u$, and $c - c_a = \rho\,(p\,q_u/q)(\mathcal{L})$ with $\rho = u/q_u(\mathcal{L})$. (ii) is the same with $c_c$ in the place of $c_a$. Constant ratios are included. $\square$

### 6.3 The theorem

**Theorem 6.3. [proved, conditional on H4($C$)]** Let $D$ be a generic subspace of any field, $T$ with $e_4 = 4T - n - 3k + 1 \ge 1$, $\pi^\ast$ the least power of two $\ge (e_4 + 2)/C$, $c = N - \log_2\pi^\ast$ and $\delta^\ast = \lfloor (k - 1)/\pi^\ast\rfloor$. Then every word has at most
$$3 + 24\binom{N}{c}_2\prod_{i=1}^{\delta^\ast + 1}\frac{n - k + i}{T - k + i}$$
codewords of degree $< k$ at agreement $\ge T$, and the same holds for interleaved words with any number of lanes (note 12, Proposition 1.1).

*Proof.* Let $M$ be the size of the list. No four members are collinear (Lemma 5.7), so every four members have a curve. By Lemma 1.3 and H4 every four members $\{a, b, c, d\}$ have one of the seven functions with a period group of size $\ge (e_4 + 2)/C$, hence containing a subspace $\Pi^\ast$ of size $\pi^\ast$ (constants included). If it is a triple function, some three of the four, say $a, b, c$, have $(c_c - c_a)/(c_b - c_a) \in F(L_{\Pi^\ast})$. By Lemma 6.1 (i), for a fixed pair $\{a, b\}$ and a fixed $\Pi^\ast$ there are at most $A(\delta^\ast + 1) - 2$ such $c$, so at most $B = \binom{N}{c}_2 A(\delta^\ast + 1)$ for a fixed pair, and the number of four-subsets of this kind is at most $\binom{M}{2}B(M - 3)$. If it is an opposite ratio, $(c_d - c_c)/(c_b - c_a) \in F(L_{\Pi^\ast})$ for a labelling, and by Lemma 6.1 (ii) for a fixed pair $\{a, b\}$ and a fixed $c$ there are at most $B$ such $d$: at most $\binom{M}{2}(M - 2)B$ four-subsets. So $\binom{M}{4} \le \binom{M}{2}(2M - 5)B$, that is $(M - 2)(M - 3) \le 12(2M - 5)B$ and $M \le 3 + 24B$. $\square$

### 6.4 Numbers, rate 1/2 and rate 1/4

`27_bounds.py`. At rate 1/2, $e_4 + 2 \approx (4\tau - 5/2)n$, so $n/\pi^\ast$ is the least power of two $\ge C/(4\tau - 5/2)$ (up to rounding). The script prints $N = 25, 26, 27, 28$; each unit of $N$ adds $c$ to the exponent, so only the two ends are tabulated.

| $\tau$, rate 1/2 | $C = 2$: $c$, $\delta^\ast$ | $N = 25$ | $N = 28$ | $C = 4$: $c$, $\delta^\ast$ | $N = 25$ | $N = 28$ |
| --- | --- | --- | --- | --- | --- | --- |
| $(0.6563, 0.6667]$ | 3, 3 | $2^{78.5}$ to $2^{78.9}$ | $2^{87.5}$ to $2^{87.9}$ | 4, 7 | $2^{103.0}$ to $2^{103.7}$ | $2^{115.0}$ to $2^{115.7}$ |
| $(0.6407, 0.6563]$ | 4, 7 | $2^{104.2}$ to $2^{104.9}$ | $2^{116.2}$ to $2^{116.9}$ | 5, 15 | $2^{134}$ to $2^{136}$ | $2^{149}$ to $2^{151}$ |
| $0.635$ | 5, 15 | $2^{137}$ | $2^{152}$ | 6, 31 | $2^{181}$ | $2^{199}$ |
| $0.630$ | 6, 31 | $2^{183}$ | $2^{201}$ | 7, 63 | $2^{257}$ | $2^{278}$ |

| $\tau$, rate 1/4 | $C = 2$: $c$, $\delta^\ast$ | $N = 25$ | $N = 28$ | $C = 4$: $c$, $\delta^\ast$ | $N = 25$ | $N = 28$ |
| --- | --- | --- | --- | --- | --- | --- |
| $(0.469, 0.5)$ | 3, 1 | $2^{75.4}$ to $2^{75.7}$ | $2^{84.4}$ to $2^{84.7}$ | 4, 3 | $2^{96.6}$ to $2^{97.4}$ | $2^{108.6}$ to $2^{109.4}$ |
| $0.46$ | 4, 3 | $2^{97.6}$ | $2^{109.6}$ | 5, 7 | $2^{121}$ | $2^{136}$ |
| $0.45$ | 5, 7 | $2^{122}$ | $2^{137}$ | 6, 15 | $2^{151}$ | $2^{169}$ |

At rate 1/4 the range where four members are the first forced excess is $(7/16, 1/2]$, and the bound is far above the $2^{27}$ members of the hyperplane family, which it must allow: any three hyperplanes $V, V', V''$ share a subspace $W$ of index at most 8, the differences of their members are $(\ell_V - \ell_{V'})(L_W)/X$ with linearized $\ell$, so their triple function is $W$-periodic (and constant when the three contain a common subspace of index 4), and they fall under Lemma 6.1.

Reading. With the budget of $2^{100}$ of note 09: under H4(2) the four-member method would allow thresholds down to $0.6563n$ at rate 1/2 for $N \le 28$ (about 178 queries instead of 218), and $0.469n$ at rate 1/4 (99 instead of 109). Under H4(4), the constant that the data require, it gives $2^{103}$ at $N = 25$ in the top of the window and nothing affordable at $N = 28$, and at rate 1/4 the range $(0.469, 0.5)$ at $N \le 25$ only. The constants are crude in the same way as in note 17 (inside a class only the dimension of the affine space is used).

The evidence for H4 in these ranges is thin, and I want to be explicit about it: at $n = 16$ the conclusion "a period group of size $\ge (\mathrm{exc} + 2)/4$" is sharp and true, but the windows need it for excess linear in $n$ with period index 8 to 32, and no computation here reaches a configuration of that kind that is not a lift from 16 points. What the data do show is the mechanism by which H4 could fail with a larger constant: curves without periods on $n_0 = 32$ or 64 points with excess 3 or more, whose lifts would have index $n_0$ at excess density $(\mathrm{exc}_0 + 2)/n_0$.

### 6.5 More members, the other windows, and the induction on $L$

Three members handle $\tau > (1 + 2\rho)/3$ (note 17), four members $(1 + 3\rho)/4 < \tau \le (1 + 2\rho)/3$, and in general $L + 1$ members are the first with forced excess for $\tau \in \bigl(\frac{1 + L\rho}{L + 1}, \frac{1 + (L - 1)\rho}{L}\bigr]$, where $e_{L+1}/n \le (1 - \rho)/L$. The argument of Theorem 6.3 is an induction step: given a structure statement H$_{L+1}$($C$) ("any $L + 1$ members with curve excess $\mathrm{exc}$ contain three or four members with a triple function or an opposite ratio of period $\ge (\mathrm{exc} + L - 1)/C$"), the same counting gives
$$\Lambda(T) \le 3 + \tfrac12 (L + 1)L(L - 1)^2\binom{N}{c}_2 A(\delta^\ast + 1), \qquad \pi^\ast \ge \frac{e_{L+1} + L - 1}{C} .$$
**[proved conditional on H$_{L+1}$($C$); H$_{L+1}$ is conjectured only by analogy for $L \ge 4$, nothing was computed]**. The best possible constant is $C = L - 1$ (a period of the whole curve gives excess $(L - 1)(\lvert\Pi\rvert - 1)$). With it, at the top of each range and in its middle:

| rate | members | range of $\tau$ inside the window | $N = 25$: top, middle | $N = 28$: top, middle |
| --- | --- | --- | --- | --- |
| 1/2 | 4 | $(0.6250, 0.6667]$ | $2^{78.5}$, $2^{104.5}$ | $2^{87.5}$, $2^{116.5}$ |
| 1/2 | 5 | $(0.6000, 0.6250]$ | $2^{108}$, $2^{143}$ | $2^{120}$, $2^{158}$ |
| 1/2 | 6 | $(0.5833, 0.6000]$ | $2^{147}$, $2^{202}$ | $2^{162}$, $2^{220}$ |
| 1/2 | 8 | $(0.5625, 0.5714]$ | $2^{216}$, $2^{323}$ | $2^{234}$, $2^{344}$ |
| 1/4 | 4 | $(0.4375, 0.5000)$ | $2^{54}$ (at $n/2$), $2^{75.7}$ | $2^{60}$, $2^{84.7}$ |
| 1/4 | 5 | $(0.4000, 0.4375]$ | $2^{78}$, $2^{101}$ | $2^{87}$, $2^{113}$ |
| 1/4 | 6 | $(0.3750, 0.4000]$ | $2^{103}$, $2^{129}$ | $2^{115}$, $2^{144}$ |
| 1/8 | 4 | $(0.3438, 0.3536)$ | $2^{114}$, $2^{136}$ | $2^{129}$, $2^{154}$ |
| 1/8 | 5 | $(0.3000, 0.3438]$ | $2^{76}$, $2^{97}$ | $2^{85}$, $2^{109}$ |
| 1/8 | 6 | $(0.2708, 0.3000]$ | $2^{98}$, $2^{119}$ | $2^{110}$, $2^{134}$ |
| 1/8 | 7 | $(0.2500, 0.2708]$ | $2^{121}$, $2^{146}$ | $2^{136}$, $2^{164}$ |
| 1/16 | 6 | $(0.2188, 0.2500)$ | $2^{96}$, $2^{115}$ | $2^{108}$, $2^{130}$ |
| 1/16 | 7 | $(0.1964, 0.2188]$ | $2^{97}$, $2^{116}$ | $2^{109}$, $2^{131}$ |
| 1/16 | 8 to 15 | $(0.1250, 0.1964]$ | $2^{117}$ to $2^{172}$ (tops) | $2^{132}$ to $2^{193}$ |

So the answer to the question about the induction: **in principle** it gives a bound $n^{c(\tau)}$ times a constant at every $\tau$ above the rate (a statement for each $L$, each conditional on its own structure conjecture), with $c(\tau) = \lceil\log_2(C n/e_{L+1})\rceil$ growing without bound as $\tau$ decreases to a threshold $(1 + L\rho)/(L + 1)$ from above and jumping by about one each time $L$ doubles. **In numbers** it does not reach the dyadic points: at rate 1/2 even the tops of the ranges cost $2^{108}$ for five members and more than $2^{200}$ at eight members ($\tau \le 4/7$), so $9/16$ and $17/32$ are far outside a budget of $2^{100}$. At the low rates the picture is better at the top of each range because $k$ is small compared with the period and the classes are affine spaces of dimension 1 or 2 ($2^{76}$ for five members at rate 1/8, $2^{96}$ for six at rate 1/16), but each of these rests on a structure statement for five to seven members that nobody has tested, and by the experience of this note (four members were already not what three members suggested) I would not rely on the extrapolated constants.

### 6.6 Why the cross-ratio is left out, and what a periodic cross-ratio does give

**[proved]** If $\Phi = \mathrm{cr}(c_a, c_b; c_c, c_d) \in F(\mathcal{L})$ and $u_1 = c_b - c_a$, $u_2 = c_c - c_a$, then
$$\frac{1}{c_d - c_a} = \frac{1}{u_2} + r(\mathcal{L})\Bigl(\frac{1}{u_2} - \frac{1}{u_1}\Bigr), \qquad c_d - c_i = \frac{w_i\,p_i(\mathcal{L})}{\sum_j c_j\,p_j(\mathcal{L})} \quad (i \in \{a, b, c\}),$$
with $w_i = \prod_{j \ne i}(c_j - c_i)$ and $p_a + p_b + p_c = 0$ pairwise coprime of degree $\le 2(k - 1)/\pi^\ast$. So the members $d$ with a periodic cross-ratio against a fixed triple are parametrized by one rational function of bounded degree, but they form an affine space only after the inversion $y \mapsto 1/(y - c_a)$, and the agreement with a word turns into the agreement of $r \circ \mathcal{L}$ with a word of values in $\mathbb{P}^1$, where two members of the class can agree on as many as $2\deg\Phi$ points. The counting of note 04, Theorem 1.2, needs fewer than $T$. What can be said: the denominator $N = \sum_j c_jp_j(\mathcal{L})$ divides each $w_ip_i(\mathcal{L})$, its roots are roots of the common factor of the base triple or triple points of $c_d$ with two of the base members, and its degree is at least $\deg w_a + \pi^\ast\deg p_a - (k - 1)$. So a cross-ratio class with a base triple of full degree forces at least $\delta_3 + \pi^\ast\deg p_a$ of the at most $3\delta_3$ roots of the three base differences to lie in at most $3\deg\Phi/\pi^\ast$ cosets of $\Pi^\ast$: **the base triple is itself nearly periodic.** That is a constraint on the triple and not a bound on the class, and it is the reason H4 is stated without $\Phi$.

## 7. What would make it unconditional, and the real domain

**On a generic subspace.** Three things are missing, in order.

1. *The four-member structure statement itself* (Q, or H4 with any constant). Theorem 5.1 shows that when nothing is hidden (all roots in $D$) the structure follows from unique factorization in two lines. The whole difficulty is the cofactors: roots of the differences outside $D$. Note 17 handles them for three members at infinity (derivations), note 12 at the places of subspaces (valuations), and neither sees the other's information. The four-member data sharpen what a proof must do: it must produce periods of single functions with different subspaces, and tolerate a sporadic excess that comes from linear relations and has no period. A proof of Q$_0$ for curves of degree 2 would already be new (the conic search of 4.2 is its numerical form).
2. *The growth of the sporadic term.* Q asserts it is 1. A construction of curves without any period and with excess growing with $n$ would refute Q and would show that H4 needs $C \to \infty$, that is no polynomial bound by this route. I looked for one in the families I know (sum relations at depth 3, that is sets congruent modulo 4; grids; twists) and found none: congruences modulo $2^{a+1}$ between small sets force flats of dimension $a + 1$ in their symmetric differences (minimum weight words of Reed-Muller codes), which are periods of opposite ratios. **[heuristic]**
3. *The classes with a periodic cross-ratio* (section 6.6), and for five and more members the analogue of everything.

A cheap and decisive computation that I could not do: all four-member curves of degree 3 and 4 on 32 points (the minimal configurations with $3\delta + 3$ conditions, up to $\mathrm{AGL}(5, 2) \times S_4$: of the order of $10^{9}$ to $10^{11}$ rank computations with orbit reduction). It would give the primitive curves with excess density in $(0, 1/6]$ on 32 points, which is exactly what decides the constant in the rate-1/2 window.

**On the real domain** $D = \mathrm{span}(1, x, \dots, x^{N-1}) \subset \mathrm{GF}(2^{64})$. What transfers without change: Theorem 1.1, Lemmas 1.3, 5.7, 6.1, Propositions 1.5, 2.1, 5.3 (i), 5.4, 5.8 (all "if" directions, so every list of section 3 and Corollary 1.6 exist on the real domain as soon as the specialization keeps the four members distinct), and the counting step of Theorem 6.3. What does not: Lemma 1.4 and everything that uses algebraic independence, that is Theorem 5.1, Proposition 5.3 (ii), Theorem 5.5, and the conjectures themselves. The mechanism of failure is visible in Theorem 5.1: an identity between products of $j$ elements of $D$ is an identity in $\mathbb{F}_2[x]$ only while $j(N - 1) < 64$, and even then the elements of $D$ are polynomials in $x$ that factor, so "equal products" no longer means "equal multisets" (identities such as $x \cdot (x^2 + x) = x^2 \cdot (x + 1)$). These are the non-generic coincidences of notes 13 and 19. **[checked]** `27_lists 12 13 1 2 1`, the real shape at $n = 16$ ($\mathrm{span}(1, x, x^2, x^3)$, translations as the only symmetries): 7034424 four-member lists against 4164160 on the generic domain, in 184 classes against 18. They contain triples that violate Conjecture P (triple functions with $(\deg, \nu, \lvert\Pi\rvert) = (2, 6, 1)$, $(3, 8, 1)$, $(4, 11, 1)$), and 43456 lists of excess 2 without any period, which do not exist generically at this point. (Q has no violation in this run. At this size, where the elements of $D$ are polynomials of degree at most 3 in $x$ and nothing is reduced, that says little about $N = 25$.) So the realistic form of a real-domain statement is the one of note 13: Q or H4 for all configurations outside an explicit exceptional set whose size is bounded by a count of the solutions of the corresponding multiplicative equations in $D$, and the conditional theorem would then carry the exceptional classes as an additive term. I did not attempt the count.

## 8. Answers to the brief

1. **Criterion.** Theorem 1.1, in the three forms asked for, with the exact dimension on independent points and the count $J \le L\delta + L - 1$.
2. **The sharp statement for four members.** Not found in closed form. Determined by computation at $n = 16$: the period group is replaced by the period groups of eight functions (four triple functions, the cross-ratio, three opposite ratios), which can be pairwise different and can all be trivial while the excess is 1 or 2. Conjecture Q bounds the excess by the largest of them plus three times the period of the curve minus two, holds in all $4.05 \cdot 10^{10}$ lists found at $n = 16$ and for the conics found at $n = 32$, and is sharp at $n = 16$. Twists in the sense of note 17 act inside each class (the curve is the invariant). Twisted periods of the whole curve do not occur as a mechanism, twisted periods of parts do (mechanism 5).
3. **Proved.** The "if" directions (5.8), the split case of P and of the four-member problem (5.1, 5.2), degree one (5.3), the Frobenius-Euler determinant (5.5), no four collinear and rigidity under translations (5.7), the conditional list bound (6.3) with numbers at $N = 25$ to 28, and the induction on $L$ (6.5: polynomial in principle, not within $2^{100}$ at $9/16$ or $17/32$).
4. **Unconditional, real domain.** Section 7.

## 9. Reproduction

Under `doc/whir_soundness_gap_notes/scripts/`, C with the system compiler, field arithmetic from `02_gf.h` ($\mathrm{GF}(2^{64})$ with the leanVM modulus), common code in `27_common.h`.

- `27_lists.c`: `cc -O2 -o 27_lists 27_lists.c -lpthread`, `./27_lists k T [seed] [threads] [real] [pairlo pairhi]`. All four-member lists at $n = 16$, class histogram with one example per class. Four threads: $(12, 13)$ 0.2 s, $(3, 7)$ 1 s, $(9, 11)$ 12 s, $(6, 9)$ 60 s, $(8, 10)$ 9 minutes in four runs over the rooted pairs $[0, 90), \dots, [270, 360)$ (each under 3 minutes; the histograms are concatenated). With `real` = 1 at $(12, 13)$: 4 minutes on two threads. `27_run.sh <bin dir> <out dir>` runs the five points and prints the summaries.
- `27_summary.py out.txt [full]`: the columns of the table in 3.1, the ratio of H4 and the check of Conjecture Q.
- `27_generalize.c`: `./27_generalize k T E0 E1 E2 E3 [seed] [tries]`. The smallest space of $\mathbb{F}_2$-relations between the special points under which the configuration still exists (section 3.2, mechanism 5).
- `27_lift.c`: `./27_lift k0 T0 E0 E1 E2 E3 [log2|U|] [seed]`. Corollary 1.6: lifts a 16-point list to $n = 16\lvert U\rvert$ and counts the agreements of the four members.
- `27_conics.c`: `./27_conics [seed] [part parts] [Jmin]`. Conics on 32 points (section 4.2), four parts of 6 s each.
- `27_grid.c`: `./27_grid [seed]`. The grid of section 4.2 at $n = 32$.
- `27_bounds.py`: the tables of 6.4 and 6.5.
- `27_results.txt`: the class tables of all runs quoted here (all classes for four of the five points, totals and the classes without periods for $(8, 10)$), and the outputs of the other programs.

## References

- [BGM] J. Brakensiek, S. Gopi, V. Makam. Generic Reed-Solomon Codes Achieve List-decoding Capacity. arXiv 2206.05256. (Used through the statements quoted in note 17, section 1. Not re-read.)
- Mason-Stothers theorem (the polynomial $abc$ theorem). Used in the proof of Theorem 5.1 in the form proved there.
- Notes 02 (Theorem W, Lemma 3), 04 (Theorem 1.2), 12 (Proposition 1.1), 13, 17, 18, 19 of this directory.
