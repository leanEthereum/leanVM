# 02. Computational exploration of lists beyond Johnson on subspace domains

Researcher 02. Everything here is about Reed-Solomon codes over $K' = \mathrm{GF}(2^m)$ evaluated on an $\mathbb{F}_2$-subspace $D$ of dimension $N$, $n = 2^N$, $k = \rho n = 2^\kappa$. Status tags: **[proved]** (proof given here), **[checked]** (numerically, sizes stated), **[conjectured]**. Scripts are `scripts/02_*`; section 10 says how to run them.

## 0. Summary

Conventions. "Genuine" means degree $< k$. "Slack $\ell$" means degree $\le k - 1 + \ell$ (the analysis degree $d$ of the main note, $\ell = 6$ at level 0). A common-top class at depth $t$ is a set of $T$-subsets of $D$ whose locators share the $t$ coefficients below the leading one, $e_1, \dots, e_t$. It is a list at agreement $T$ in degree $\le k - 1 + \ell$ exactly when $t \ge T - k - \ell$ (Lemma 1).

Main results.

1. **A criterion that turns common-top lists into combinatorics (Theorem W, proved).** Two multisets $c, c'$ on $D$ of equal mass with $n_\varphi(c) \equiv n_\varphi(c') \pmod{2^{a+1}}$ for every linear functional $\varphi$ on $D$ (equivalently, Walsh spectra congruent modulo $2^{a+2}$) share $e_1, \dots, e_{2^{a+1}-1}$, in every field and for every subspace $D$. In the formal model (basis of $D$ algebraically independent) the converse holds, so the classes are exactly the congruence classes, and they only refine when $t$ crosses a power of two. Checked exhaustively for $n = 16$ (all $T$, $t \le 7$) and $n = 32$ ($T \le 6$) on random domains in $\mathrm{GF}(2^{64})$.
2. **Rate 1/2: the full class at $5n/8$ has $56n - 392$ members (Theorem 5, proved, checked at $n = 32, 64, 128$).** For a subspace $U$ with $|U| = n/8$ the word $L_U^5$ agrees on $5n/8$ points with $56 + 448(n/8 - 1)$ polynomials of degree $\le n/2$, and the punctured word $(L_U^5 - c)/(X - p)$ agrees on $5n/8 - 1$ points with at least $35 + 280(n/8 - 1)$ genuine codewords. For $N = 25$ these are $2^{30.81}$ and $2^{30.13}$. This is the word of the height-2 tree family that note 01 takes from [DKTZ26], but the class is 2.7 times larger than the tree count $28(6 \cdot 2^{N-3} - 5)$: most members are unions of ten cosets of a varying hyperplane $W$ of $U$ that are not unions of two flats. On $n = 32$ the exhaustive oracle (all polynomials, not only common-top ones) finds exactly 1400 and 1323. The general form gives, at agreement $(1/2 + 1/M')n$, about $(n/M') \binom{2M'}{M'+2} / 2M'$ members: $2^{44.8}$ at $9n/16$, $2^{74.5}$ at $17n/32$.
3. **Above $5n/8$ at rate 1/2, simple common-top lists are bounded by 4 in the formal model (Proposition 6, proved), by 7 at exactly $5n/8$ genuine.** Exhaustive enumeration on $n = 16$ and $n = 32$ agrees (3, 3, 3, then 4 at $3n/4$ with slack). Words whose locators carry multiplicities (the padded hyperplanes of note 01) escape this bound, which is consistent with note 01: lists of size $L$ up to about $5/8 + O(L^{-1/2})$, but nothing that grows with $n$ at a fixed fraction above $5/8$.
4. **Rates 1/8 and 1/16: in the formal model the common-top frontier is exactly the flats (Proposition 6, proved).** Above $2\rho n$ the classes have at most 4 members at rate 1/8, at most 7 members for $T \in (n/8, 3n/16)$ and exactly 1 for $T \in [3n/16, n/4)$ at rate 1/16. Exhaustive at $n = 32$ agrees.
5. **The answer depends on $D$ only through small-field and small-depth effects.** Tables for $n = 16, 32$ on a random domain, on leanVM's shape $\mathrm{span}(1, x, \dots, x^{N-1})$, and in $\mathrm{GF}(32)$, $\mathrm{GF}(2^8)$: the leanVM shape has larger classes only at depths $t = 2$ and $t = 4$ (products $x^i x^j$ collide), small fields have pigeonhole lists of about $\binom{n}{T}/2^{mt}$. For the real domain ($N = 25$, $m = 64$) pigeonhole stops at $T/n \approx 0.516$, and no label space $L_W(D)$ of dimension $\ge 2$ lies in a multiple of $\mathrm{GF}(2^8)$ (checked on the real domains $N = 25, \dots, 28$, section 7), so the subfield route of [BKR10] is closed at these sizes.
6. **Common-top is not optimal among all words on small instances.** Annealing over arbitrary words at $n = 16$ on a random domain finds a list of 11 at $T = 10$, $k = 8$ (simple common-top: 7), of 16 at $T = 6$, $k = 4$ (7), and at $k = 2$ lists from tangent lines of a conic over a Sidon set (section 8, proved). Everything it found at rate 1/2 is explained by locators with multiplicities, and it found nothing above the simple common-top values at $T = 11, 12$.

Frontier observed per rate (agreement fraction where lists that grow with $n$ stop; list sizes for level 0 at $\mu = 30$, that is $\kappa = 24$, $N = 24 + R$):

| rate | Johnson | growing lists exist up to | list there | above it (what I know) |
| --- | --- | --- | --- | --- |
| 1/2 | 0.7071 | $5/8$ ($5n/8 - 1$ genuine, $5n/8 + \ell - 1$ with slack $\ell$) | $2^{30.1}$ genuine, $2^{30.8}$ at $5n/8$ with slack 1, $2^{27.8}$ at $5n/8 + 5$ with slack 6 | simple common-top $\le 4$ (formal model, proved); with multiplicities $L$ at $5/8 + O(L^{-1/2})$ (note 01); general words unknown |
| 1/4 | 0.5 | $1/2$ (flats) | $2^{26}$ | closed |
| 1/8 | 0.3536 | $1/4$ (flats) | $2^{51.4}$ | simple common-top $\le 4$ (formal model, proved); general words unknown |
| 1/16 | 0.25 | $1/8$ (flats) | $2^{76.6}$ | simple common-top $\le 7$, then 1 from $3n/16$ (formal model, proved); general words unknown |

Not settled: whether the real domain has arithmetic coincidences beyond the formal model at depth $t \approx n/8$, and whether words that are not polynomial locators have growing lists in the gaps. Section 9 lists what a larger computation could decide.

## 1. Setup

$D \cong \mathbb{F}_2^N$ through a basis $b_1, \dots, b_N$. For $S \subseteq D$, $Z_S(X) = \prod_{s \in S}(X - s) = \sum_j e_j(S) X^{|S|-j}$. For a subspace $V$, $L_V = Z_V$ is linearized. For a functional $\varphi \in D^\ast$ and a multiset $c : D \to \mathbb{Z}_{\ge 0}$, $n_\varphi(c) = \sum_{\varphi(s) = 1} c(s)$, and the Walsh transform is $\hat c(\varphi) = \sum_s c(s)(-1)^{\varphi(s)} = |c| - 2 n_\varphi(c)$.

**Lemma 1 (common top). [proved]** Let $\mathcal{S}$ be a family of $T$-subsets of $D$ sharing $e_1, \dots, e_t$ with $t \ge T - k - \ell$, and $R = X^T + \sum_{j \le t} e_j X^{T-j}$. Then $P_S = R - Z_S$ has degree $\le k - 1 + \ell$, agrees with the word $R|_D$ on $S$, and $S \mapsto P_S$ is injective. The same holds for multisets $c$ of mass $T$, with $Z_c = \prod (X - s)^{c(s)}$ and agreement on the support of $c$.

**Lemma 2 (complements). [proved]** $Z_S Z_{D \setminus S} = L_D = X^n + O(X^{n/2})$, so for $t \le n/2 - 1$ the tuple $(e_1, \dots, e_t)(S)$ determines $(e_1, \dots, e_t)(D \setminus S)$ and conversely. Classes at depth $t$ of $T$-sets and of $(n-T)$-sets correspond.

**Lemma 3 (lifting). [proved]** Let $W \subseteq D$ be a subspace, $\Lambda = L_W(D)$ (a subspace of dimension $N - \dim W$, $M = |\Lambda|$ "labels"). If a word $w' : \Lambda \to K'$ has $L$ polynomials of degree $< \rho M$ at agreement $j$, then $w' \circ L_W$ has the $L$ polynomials $P' \circ L_W$ of degree $< \rho n$ at agreement $j |W|$. So every list on a small domain of the form $L_W(D)$ lifts to all larger $n$ at the same rate and agreement fraction, with the same (constant) size. For lists coming from Theorem W the small domain can be any subspace, so they lift to every $D$.

**Lemma 4 (slack to genuine by puncturing). [proved]** If polynomials $P_S$ of degree $\le k - 1 + \ell$ agree with $w$ on sets $S$ that all contain a fixed $\ell$-set $A$, then with $I_A$ the interpolant of $w$ on $A$, the polynomials $(P_S - I_A)/Z_A$ have degree $\le k - 1$ and agree with $(w - I_A)/Z_A$ on $S \setminus A$. So a slack-$\ell$ list at agreement $T$ whose members share $\ell$ points is a genuine list at agreement $T - \ell$.

**Trivial lists. [proved]** For any domain and field with at least $L$ elements, a list of size $L = \lfloor (n - k + 1)/(T - k + 1) \rfloor$ exists at agreement $T$: fix a $(k-1)$-set $R$, take $P_i = c_i Z_R$ with distinct $c_i$, split $D \setminus R$ into $L$ blocks and let the word equal $P_i$ on block $i$. At rate 1/2 this is $L \approx 1/(2\tau - 1)$: 4 at $5/8$, 1024 only at $\tau = 1/2 + 2^{-11}$. Anything interesting is far above this.

## 2. Theorem W: Walsh congruence gives a common top

**Theorem W. [proved]** Let $c, c' : D \to \mathbb{Z}$ with $\sum c = \sum c'$ and $\hat c(\varphi) \equiv \hat c'(\varphi) \pmod{2^m}$ for all $\varphi$ (equivalently $n_\varphi(c) \equiv n_\varphi(c') \pmod{2^{m-1}}$). Then $\prod_s (1 + sZ)^{c(s)} \equiv \prod_s (1 + sZ)^{c'(s)} \pmod{Z^{2^{m-1}}}$ in $K'[[Z]]$, that is $e_j(c) = e_j(c')$ for all $j < 2^{m-1}$. This holds in every field of characteristic 2 and for every subspace $D$.

*Proof.* Work with indeterminates $B_1, \dots, B_N$, $\ell_s = \sum s_i B_i$ for $s \in \mathbb{F}_2^N$, and $\Pi(c) = \prod_s (1 + \ell_s)^{c(s)} \in \mathbb{F}_2[[B]]$. $\Pi$ is a homomorphism from $(\mathbb{Z}[\mathbb{F}_2^N], +)$ to units, the degree-$j$ part of $\Pi(1_S)$ specializes to $e_j(S)$ under $B_i \mapsto b_i$, so it is enough to show: if $\sum c = 0$ and $\hat c \equiv 0 \pmod{2^m}$ then $\Pi(c) \equiv 1$ modulo degree $\ge 2^{m-1}$.

(i) In the group ring write $[s]$ for group elements and $\varepsilon_A = \prod_{i \in A}([e_i] - [0])$ for nonempty $A \subseteq [N]$. These and $[0]$ are a $\mathbb{Z}$-basis, and the character $\varphi$ takes the value $(-2)^{|A|}$ on $\varepsilon_A$ if $A \subseteq \mathrm{supp}\,\varphi$ and 0 otherwise. Write $c = \sum_A \gamma_A \varepsilon_A$. Then $\hat c(1_A) = \sum_{B \subseteq A} \gamma_B (-2)^{|B|}$, and by induction on $|A|$, $2^m \mid \gamma_A 2^{|A|}$, so $2^{\max(0, m - |A|)} \mid \gamma_A$.

(ii) $\Pi(\varepsilon_A) \equiv 1$ modulo degree $\ge 2^{|A|-1}$. For $B \subseteq A$ of odd size and $\beta = 1_B$, reduce modulo the linear form $\ell_\beta$: then $\ell_s \equiv \ell_{s+\beta}$, so $\Pi(c) \bmod \ell_\beta$ depends only on the push-forward of $c$ to $\mathbb{F}_2^N / \langle\beta\rangle$. The push-forward of $\varepsilon_A$ is 0, because every character of the quotient is a $\varphi$ with $|\mathrm{supp}\,\varphi \cap B|$ even, so $B \not\subseteq \mathrm{supp}\,\varphi$ and $\varphi(\varepsilon_A) = 0$, and characters separate the integral group ring. Hence every homogeneous component of $\Pi(\varepsilon_A) - 1$ is divisible by $\ell_\beta$ for each of the $2^{|A|-1}$ odd subsets $B$. These are distinct linear forms, so the product divides, and a nonzero component has degree $\ge 2^{|A|-1}$.

(iii) $\Pi(c) = \prod_A \Pi(\varepsilon_A)^{\gamma_A}$. Raising to the power $2^j$ multiplies the degrees of all components by $2^j$ (Frobenius), so $\Pi(\varepsilon_A)^{\gamma_A} \equiv 1$ modulo degree $\ge 2^{|A| - 1 + \max(0, m - |A|)} \ge 2^{m-1}$. $\square$

(In topological terms $\Pi(1_S)$ is the total Stiefel-Whitney class of the sum of the characters in $S$, and the statement is that it depends only on the class of the representation modulo the $m$-th power of the augmentation ideal.)

**Converse in the formal model. [proved]** If $\Pi(c) \equiv \Pi(c')$ modulo degree $> t$ as formal series and $2^a \le t$, then $n_\varphi(c) \equiv n_\varphi(c') \pmod{2^{a+1}}$ for all $\varphi$: specialize $B_i \mapsto \varphi_i z$, which gives $(1+z)^{n_\varphi(c)} \equiv (1+z)^{n_\varphi(c')} \pmod{z^{t+1}}$, and $(1+z)^{2^a} = 1 + z^{2^a}$.

So in the formal model the classes at depth $t$, $2^a \le t < 2^{a+1}$, are exactly the classes of $(n_\varphi \bmod 2^{a+1})_\varphi$: they are the same for all $t$ in a dyadic interval. I call a concrete $D \subseteq K'$ *generic at depth $t$* when distinct formal tuples give distinct field values on the sets in question.

**[checked]** `02_walsh_check.py`: on a random basis in $\mathrm{GF}(2^{64})$ the partition of the $T$-subsets by $(e_1, \dots, e_t)$ equals the partition by $(n_\varphi \bmod 2^{a+1})_\varphi$ for $N = 4$, every $T$, $t \le 7$, and for $N = 5$, $T \le 6$, $t \le 5$. The exhaustive $n = 32$ table of section 3 has identical columns for $t \in \{2, 3\}$ and for $t \in \{4, \dots, 7\}$ on the random domain, as the theorem predicts.

Immediate families (all **[proved]** by Theorem W, each is a class in the formal model):

- Any two cosets of $d$-dimensional subspaces are congruent modulo $2^{d-1}$: depth $2^{d-1} - 1$. Removing the point 0 is free since $1 + 0 \cdot Z = 1$. This is the flat family of the lead notes.
- Any union of an even number of cosets of any $d$-dimensional subspace has all $n_\varphi \equiv 0 \pmod{2^d}$: all such sets of one size form a single class at depth $2^d - 1$ (for example 8742 sets of size 16 in $\mathbb{F}_2^5$ at depth 3, the unions of four cosets of 2-dimensional subspaces, found by the exhaustive run). It is not a list beyond rate, because the depth is too small for the size.
- Multisets: $1_H + 1_C$ for affine hyperplanes $H$ and a fixed padding $C$ are congruent modulo $n/4$ in $n_\varphi$, depth $n/4 - 1$. This is the padded-hyperplane family of note 01, with agreement $n/2 + |C \setminus H|$.

## 3. Exhaustive common-top tables

`02_ct16.py` (pure python) enumerates all subsets for $n = 16$; `02_ct32.c` does $n = 32$ by meet in the middle (two halves of 16 points, grouped by $e_1$, then refined coefficient by coefficient), about one minute on four cores per domain; `02_check_ct32.py` checks it against direct enumeration for $T \le 5$. Entry: the largest number of $T$-sets sharing $(e_1, \dots, e_t)$, with $t = T - k$ (degree $< k$) and $t = T - k - 1$ (degree $\le k$). Domains: "random" = random basis in $\mathrm{GF}(2^{64})$ (two seeds for $n = 16$, one for $n = 32$); "leanVM shape" = $\mathrm{span}(1, x, \dots, x^{N-1})$ in $\mathrm{GF}(2^{64})$ with the real modulus (identical numbers in $\mathrm{GF}(2^{12})$ and $\mathrm{GF}(2^{16})$ for $N = 5$); $\mathrm{GF}(2^N)$ = the whole field as domain; $\mathrm{GF}(2^8)$ = $\mathrm{span}(1, \dots, x^4)$ in $\mathrm{GF}(2^8)$. All entries **[checked]** exhaustively.

$n = 16$:

| rate | $T$ | $T/n$ | random, $< k$ | random, $\le k$ | leanVM shape, $< k$ | leanVM shape, $\le k$ | $\mathrm{GF}(16)$, $< k$ | $\mathrm{GF}(16)$, $\le k$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | 9 | 0.5625 | 715 | 11440 | 715 | 11440 | 715 | 11440 |
| 1/2 | 10 | 0.625 | 7 | 504 | 15 | 504 | 32 | 504 |
| 1/2 | 11 | 0.6875 | 3 | 3 | 3 | 9 | 3 | 18 |
| 1/2 | 12 | 0.75 | 1 | 4 | 1 | 4 | 1 | 4 |
| 1/4 | 5 | 0.3125 | 273 | 4368 | 273 | 4368 | 273 | 4368 |
| 1/4 | 6 | 0.375 | 7 | 504 | 15 | 504 | 32 | 504 |
| 1/4 | 7 | 0.4375 | 15 | 15 | 15 | 19 | 15 | 45 |
| 1/4 | 8 | 0.5 | 2 | 30 | 2 | 30 | 2 | 30 |
| 1/8 | 3 | 0.1875 | 35 | 560 | 35 | 560 | 35 | 560 |
| 1/8 | 4 | 0.25 | 4 | 140 | 8 | 140 | 20 | 140 |
| 1/8 | 5 | 0.3125 | 3 | 3 | 3 | 9 | 3 | 18 |
| 1/8 | 6 | 0.375 | 1 | 7 | 1 | 7 | 3 | 7 |

$n = 32$ (Johnson applies for $T > 21.9$, $15.0$, $9.8$, $5.7$ at rates 1/2, 1/4, 1/8, 1/16):

| rate | $T$ | $T/n$ | random, $< k$ | random, $\le k$ | leanVM shape, $< k$ | leanVM shape, $\le k$ | $\mathrm{GF}(32)$, $< k$ | $\mathrm{GF}(32)$, $\le k$ | $\mathrm{GF}(2^8)$, $< k$ | $\mathrm{GF}(2^8)$, $\le k$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | 17 | 0.531 | 17678835 | $\binom{32}{17}$ | 17678835 | $\binom{32}{17}$ | 17678835 | $\binom{32}{17}$ | 17678835 | $\binom{32}{17}$ |
| 1/2 | 18 | 0.562 | 2395 | 14732720 | 43559 | 14732720 | 460415 | 14732720 | 60743 | 14732720 |
| 1/2 | 19 | 0.594 | 1323 | 1323 | 1323 | 29865 | 10639 | 339235 | 1323 | 44119 |
| 1/2 | 20 | 0.625 | 7 | 1400 | 13 | 1400 | 250 | 7168 | 19 | 1400 |
| 1/2 | 21 | 0.656 | 3 | 3 | 7 | 7 | 23 | 186 | 10 | 10 |
| 1/2 | 22 | 0.688 | 3 | 3 | 3 | 6 | 3 | 18 | 3 | 10 |
| 1/2 | 23 | 0.719 | 3 | 3 | 3 | 3 | 3 | 3 | 3 | 3 |
| 1/2 | 24 | 0.750 | 1 | 4 | 1 | 4 | 1 | 4 | 1 | 4 |
| 1/4 | 10 | 0.312 | 513 | 2016144 | 6827 | 2016144 | 63015 | 2016144 | 8758 | 2016144 |
| 1/4 | 11 | 0.344 | 589 | 589 | 589 | 11748 | 3984 | 126003 | 589 | 16666 |
| 1/4 | 12 | 0.375 | 7 | 1400 | 13 | 1400 | 250 | 7168 | 19 | 1400 |
| 1/4 | 13 | 0.406 | 7 | 7 | 12 | 12 | 47 | 363 | 17 | 17 |
| 1/4 | 14 | 0.438 | 15 | 15 | 15 | 16 | 15 | 80 | 15 | 27 |
| 1/4 | 15 | 0.469 | 31 | 31 | 31 | 31 | 31 | 31 | 31 | 31 |
| 1/4 | 16 | 0.500 | 2 | 62 | 2 | 62 | 2 | 62 | 2 | 62 |
| 1/8 | 6 | 0.188 | 35 | 28336 | 157 | 28336 | 889 | 28336 | 169 | 28336 |
| 1/8 | 7 | 0.219 | 155 | 155 | 155 | 473 | 186 | 3317 | 155 | 546 |
| 1/8 | 8 | 0.250 | 4 | 620 | 8 | 620 | 20 | 620 | 12 | 620 |
| 1/8 | 9 | 0.281 | 3 | 3 | 6 | 6 | 15 | 40 | 9 | 9 |
| 1/8 | 10 | 0.312 | 3 | 3 | 3 | 6 | 3 | 18 | 3 | 10 |
| 1/8 | 11 | 0.344 | 3 | 3 | 3 | 3 | 3 | 5 | 3 | 3 |
| 1/8 | 12 | 0.375 | 1 | 7 | 1 | 7 | 1 | 7 | 1 | 7 |
| 1/16 | 3 | 0.094 | 155 | 4960 | 155 | 4960 | 155 | 4960 | 155 | 4960 |
| 1/16 | 4 | 0.125 | 8 | 1240 | 24 | 1240 | 40 | 1240 | 24 | 1240 |
| 1/16 | 5 | 0.156 | 7 | 7 | 7 | 39 | 10 | 197 | 7 | 42 |
| 1/16 | 6 | 0.188 | 1 | 35 | 2 | 35 | 4 | 47 | 2 | 35 |
| 1/16 | 7 | 0.219 | 1 | 1 | 2 | 2 | 5 | 8 | 3 | 3 |
| 1/16 | 8 | 0.250 | 4 | 4 | 4 | 8 | 4 | 20 | 4 | 12 |

Reading the tables.

- The random domain behaves as the formal model: every entry is explained by Theorem W and the structures of section 4.
- The leanVM shape differs from the random domain only where the depth is 2 or 4 (rows with $T - k \in \{2, 4\}$ or $T - k - 1 \in \{2, 4\}$): $e_2$ lies in $\mathrm{span}(1, \dots, x^{2N-2})$, of dimension $2N - 1$ instead of $N(N+1)/2$, and similarly for $e_4$, so formal classes merge. The increase is a small factor (13 against 7 at $T = 20$, $n = 32$) and does not grow from $n = 16$ to $n = 32$ at fixed $T/n$ (15, then 13, at $5/8$ genuine). At the real size the relevant depths are about $2^{22}$, where products wrap modulo the field polynomial, so I do not expect this effect to matter, but that is **[conjectured]**.
- Small fields have much larger classes, of the order of the pigeonhole average $\binom{n}{T}/2^{mt}$ (for example $\mathrm{GF}(32)$, $T = 20$, $t = 4$: average 215, maximum 250). This is the [BKR10] regime. It needs $m t \lesssim \log_2 \binom{n}{T}$.

## 4. Structures of the maximal classes (random domain)

`02_class_structure.py` describes one maximal class per $(T, t)$ from the dumps of `02_ct32` (period groups, affine spans, intersections). **[checked]** on $n = 16$ and $n = 32$; each family is **[proved]** by Theorem W or by a direct computation with $L_V$.

1. **Flats** (depth $2^{d-1} - 1$): all $d$-flats through 0 minus the point 0, translated: $T = 2^d - 1$, class size $\binom{N}{d}_2$ (155 at $T = 7$, 31 at $T = 15$). With slack 1, all affine $d$-flats: $2^{N-d}\binom{N}{d}_2$ (620, 62).
2. **Flats minus a common set**: $F \setminus A$, $F$ ranging over the $d$-flats containing a fixed set $A$ whose affine span has dimension $d_A$: $\binom{N - d_A}{d - d_A}_2$ members (7 at $T = 5, 12, 13$; 15 at $T = 14$ for $n = 32$). In terms of rate, with $A$ spanning a flat of dimension $d - 1$: $T = (2^i + 1)k - 1$ with $2^{R-i} - 1$ members, which meets the Johnson list-size bound up to a constant but is bounded in $n$.
3. **A flat plus a common set**: $H \cup C$, $H$ ranging over the affine hyperplanes disjoint from $C$: list $L$ at $T = n/2 + n/(L+1)$ at rate 1/2 (the 3 at $T = 21, 22, 23$ for $n = 32$). The same with the cosets of one subspace that miss $C$ (the 3 at $T = 9, 10, 11$ for $n = 32$ at depth 4 to 7).
4. **Cosets of one subspace**: the $2^{N-d}$ cosets of a fixed $d$-dimensional $V$ share everything down to the constant term of $L_V$ (4 at $T = 8$, $n = 32$, rate 1/8; 4 at $T = 3n/4$ with slack at rate 1/2 by complements).
5. **The glued coset unions of section 5**: 1400 at $T = 20$ (slack), and by puncturing 1323 at $T = 19$; 504 at $T = 10$ for $n = 16$.
6. At depth 2 or 3 and mid-size $T$ the classes are large without a short description (2395 at $T = 18$, 513 at $T = 10$): they are the classes of $(n_\varphi \bmod 4)_\varphi$, about $\binom{n}{T}/2^{N(N+3)/2}$ on average, a pigeonhole effect that only helps for $T - k = O(N)$.

Nothing else appears: in particular no class at $T > 5n/8$ (rate 1/2), $T > n/4$ (rate 1/8) or $T > n/8$ (rate 1/16) other than items 2 to 4.

## 5. The glued family at $5n/8$ and its general form

**Theorem 5. [proved]** Let $U \subseteq D$ be a subspace, $|U| = n/M'$, and $\rho = 2^{-R}$ with $g = \rho M' + 1$ an integer. For a hyperplane $W$ of $U$ let $\eta_W$ be the nonzero element of $L_W(U)$, so that $L_U = L_W^2 + \eta_W L_W$, and let $\Lambda_W = L_W(D)$ ($2M'$ labels). For every $2g$-subset $Y \subseteq \Lambda_W$ with $\sum_{y \in Y} y = g\,\eta_W$, the set $S = L_W^{-1}(Y)$ has $g\,n/M' = (\rho + 1/M')n$ points and
$$\deg\bigl(L_U^g - Z_S\bigr) \le \rho n .$$
So the single word $L_U^g$ agrees on $(\rho + 1/M')n$ points with one polynomial of degree $\le k$ per such pair $(W, Y)$. Sets from different $W$ coincide only if they are unions of cosets of $U$. The number of distinct sets is
$$\binom{M'}{g} + \Bigl(\frac{n}{M'} - 1\Bigr)\Bigl(\nu - \binom{M'}{g}\Bigr), \qquad \nu = \#\{Y \subseteq \mathbb{F}_2^{\log 2M'} : |Y| = 2g,\ \textstyle\sum Y = g\eta\} .$$

*Proof.* $Z_S = V(L_W)$ with $V(Y) = \prod_{y \in Y}(Y - y) = Y^{2g} + e_1 Y^{2g-1} + \dots$, and $L_U^g = (L_W^2 + \eta L_W)^g = L_W^{2g} + g\eta L_W^{2g-1} + \dots$. The condition $e_1 = g\eta$ makes $V(Y) - (Y^2 + \eta Y)^g$ a polynomial of degree $\le 2g - 2$ in $Y$, so $Z_S - L_U^g$ has degree $\le (2g-2)|W| = (g-1)|U| = \rho n$. If $S$ arises from $W \ne W'$ it is invariant under $W + W' = U$. A set invariant under $U$ with $g$ cosets has labels in pairs $\{y, y + \eta\}$, whose sum is $g\eta$, so each of the $\binom{M'}{g}$ unions of $g$ cosets of $U$ arises from every $W$. There are $|U| - 1 = n/M' - 1$ hyperplanes. $\square$

**Rate 1/2, $M' = 8$, $g = 5$.** $\nu = 504$ (10-subsets of $\mathbb{F}_2^4$ with a given nonzero sum), $\binom{8}{5} = 56$: the word $L_U^5$ has
$$56 + 448\,(n/8 - 1) = 56n - 392$$
polynomials of degree $\le n/2$ at agreement $5n/8$. For $N = 25$: $1{,}879{,}047{,}800 = 2^{30.81}$.

**Genuine variant. [proved]** By Lemma 4 with $A = \{p\}$: the word $(L_U^5 - L_U(p)^5)/(X - p)$ agrees on $5n/8 - 1$ points with a polynomial of degree $< n/2$ for each member through $p$. A fraction $10/16$ of the label sets contain the label of $p$: $35 + 280\,(n/8 - 1) = 35n - 245$ members, $2^{30.13}$ for $N = 25$.

**With slack $\ell$. [proved]** Fix a set $A$ of $j \le \ell - 1$ points inside one coset of $U$; the members avoiding that coset, each enlarged by $A$, agree with $L_U^5 Z_A$ on $5n/8 + j$ points in degree $\le n/2 + j$. Per hyperplane there are 77 such label sets, 21 of them invariant under $U$: $21 + 56(n/8 - 1)$ members, $2^{27.8}$ for $N = 25$, at agreement up to $5n/8 + \ell - 1$.

**Checks. [checked]**

- `02_glue58.py`: on $D = \mathrm{span}(1, \dots, x^{N-1})$ in $\mathrm{GF}(2^{64})$ with a random $U$, enumerates every member, checks $\deg(L_U^5 - Z_S) \le n/2$ and agreement exactly $5n/8$, and counts distinct sets: 1400 ($N = 5$, all members checked), 3192 ($N = 6$, all members checked in the first run), 6776 ($N = 7$, 347 members checked in full). Genuine variant: 875, 1995, 4235 members through $p$, degree $\le n/2 - 1$ checked.
- `02_confirm32.py`, with the exhaustive oracle of section 8 (all polynomials of the given degree, $n = 32$): the word $L_U^5$ has exactly 1400 polynomials of degree $\le 16$ at agreement $\ge 20$, all at agreement exactly 20. The punctured word has exactly 1323 polynomials of degree $< 16$ at agreement $\ge 19$: the 875 of the theorem and 448 more, for which $w - P$ has a double zero at $p$. I do not know how the extra 448 scale.
- The exhaustive table gives 1400 as the largest class of all at $(n, T) = (32, 20)$ with slack, and 504 at $(16, 10)$: the family is the maximum over all words of common-top type at these sizes.
- `02_glue_general.py`: sampled members for $(N, \rho, M') = (6, 1/2, 16)$, $(7, 1/2, 16)$, $(7, 1/2, 8)$, $(7, 1/2, 32)$, $(7, 1/4, 16)$, $(7, 1/8, 16)$: degree bound holds in every sample.

**The class is complete in the formal model. [proved, sketch]** Take complements (Lemma 2): sets $S'$ of size $3n/8$ congruent modulo $n/4$ in Walsh spectrum to a union of three cosets of $U$. In units of $n/8$ the spectrum is odd on the 8 functionals vanishing on $U$ (value 3 at $\varphi = 0$) and even elsewhere, and Parseval gives $\sum_\varphi v_\varphi^2 = 24$. So either the spectrum is supported on $U^\perp$ ($S'$ is a union of cosets of $U$), or the seven nonzero functionals of $U^\perp$ carry $\pm 1$ and exactly two functionals $\psi_1, \psi_2$ outside carry $\pm 2$. A $\{0,1\}$-valued function with that spectrum forces $\psi_1 + \psi_2 \in U^\perp$, so $S'$ is a union of cosets of $W = U \cap \ker\psi_1$, which is a member of the family. Hence no simple common-top construction on a generic domain beats $56n - 392$ for this word.

**Relation to note 01.** The word is the same as that of the height-2 decision-tree family of [DKTZ26] quoted in note 01 ($L_U^5 \equiv X^{n/2} L_U$ modulo degree $\le n/2$), whose supports number $28(6 \cdot 2^{N-3} - 5) = 21n - 140$. The class is larger: for $n = 16$ it has 504 members against 196 trees, for $n = 32$ 1400 against 532. For $N = 25$: $2^{30.81}$ against $2^{29.39}$. This matters for any budget argument that wants to sit at $2^{30}$ or $2^{31}$.

**Other parameters. [proved]** by the theorem:

| rate | $M'$ | agreement | per hyperplane $\nu$ | members for $N = 25$ |
| --- | --- | --- | --- | --- |
| 1/2 | 8 | $5n/8$ | 504 | $2^{30.8}$ |
| 1/2 | 16 | $9n/16$ | 14732720 | $2^{44.8}$ |
| 1/2 | 32 | $17n/32$ | $2.5 \cdot 10^{16}$ | $2^{74.5}$ |
| 1/4 | 4 | $n/2$ | 14 | $2n - 2$ (all affine hyperplanes: the slack flats) |
| 1/8 | 8 | $n/4$ | 140 | about $14n$, a subfamily of the slack flats |

At rates $\le 1/4$ the theorem only reproduces part of the flat family. At rate 1/2, $M' = 4$ gives $3n/4$ with 4 members, all invariant under $U$. So $M' = 8$, that is $5/8$, is the largest fraction this mechanism reaches.

## 6. Upper bounds for simple common-top classes in the formal model

Here a class is a family of $T$-sets (no multiplicities) sharing $e_1, \dots, e_t$ as formal polynomials, so by the converse of Theorem W all pairwise differences $f = 1_S - 1_{S'}$ have $\hat f \in 2^{a+2}\mathbb{Z}$, $\hat f(0) = 0$, and $\sum_\varphi \hat f(\varphi)^2 = n\,|S \triangle S'|$.

**Proposition 6. [proved]** In the formal model, with $t = T - k - \ell$ ($\ell = 0$ for genuine):

- (a) Rate 1/2, $t \ge n/8$ and $T > 5n/8$: every class has at most 4 members. At $T = 5n/8$ with $t = n/8$ (genuine): at most 7, attained.
- (b) Rate 1/8, $t \ge n/8$ (genuine: $T \ge n/4$) and $T < 3n/8$: at most 4 members.
- (c) Rate 1/16, $n/16 \le t < n/8$ (genuine: $n/8 \le T < 3n/16$): at most 8 members, at most 7 if $T > n/8$. For $n/8 \le t$ and $T < n/4$ (genuine: $3n/16 \le T < n/4$): exactly 1.

*Proof.* (a) The modulus is $n/2$ and $n|S \triangle S'| \le 2n(n - T) < 3n^2/4$, so $\hat f$ has at most two nonzero values, each $\pm n/2$. One is impossible ($\pm\chi/2$ is not integer valued), and so are three at $T = 5n/8$ (half-integer values), so $f = (\epsilon_a\chi_a + \epsilon_b\chi_b)/2 = 1_A - 1_B$ for two distinct cosets $A \subseteq S$, $B \subseteq S'$ of the codimension-2 subspace $\ker a \cap \ker b$. Fix $S_0$. Every other member is $S_0 - A_i + B_i$ with $B_i \subseteq D \setminus S_0$, a set of fewer than $3n/8$ points. Two distinct codimension-2 flats have union at least $3n/8$, so all $B_i$ are one flat $B$, the $A_i$ are distinct cosets of its direction inside $S_0$, at most 3. At $T = 5n/8$ two flats $B_i \ne B_j$ may fill $D \setminus S_0$ exactly; then $D \setminus S_0$ is three cosets of a codimension-3 subspace, there are 3 choices of $B$ and 2 of $A$ for each, 7 members in all, and the family $F \setminus A$ of section 4 attains it. (b) The same argument with $|S \triangle S'| \le 2T < 3n/4$: the flat $A_i \subseteq S_0$ is unique because $|S_0| < 3n/8$, and $B_i$ is one of the 3 other cosets. (c) The modulus is $n/4$ and $n|S \triangle S'| \le 2nT < 6(n/4)^2$. Integer values force four nonzero coefficients $\pm n/4$ on functionals summing to zero, so $f = 1_G - 1_{G'}$ for two cosets of a codimension-3 subspace. $S_0$ contains at most one such flat, and $G'$ is one of the other cosets, 7 choices, one fewer if $S_0$ meets another coset. In the last range the modulus is $n/2$ and $2nT < n^2/2$ allows at most one nonzero coefficient, which is impossible. $\square$

**[checked]** Exhaustive values on the random domain, $n = 32$: rate 1/2, $T = 20, \dots, 24$ genuine: 7, 3, 3, 3, 1 and with slack 1 at $T = 24$: 4. Rate 1/8, $T = 8, \dots, 11$: 4, 3, 3, 3. Rate 1/16, $T = 4, 5, 6, 7$: 8, 7, 1, 1. All within the bounds, the bounds 7, 4, 8, 7, 1 are attained.

What this does and does not say. It is a statement about formal coincidences of simple locators. It does not cover (i) domains that are not generic at depth $t$, (ii) locators with multiplicities, (iii) words that are not polynomial locators. For (ii), Theorem W applies to multisets and the padded hyperplanes $1_H + 1_C$ of note 01 give more: `02_padded_word.py` runs the exhaustive oracle on $w = X^{n/2} Z_C$, $C$ a codimension-2 flat minus a point, and finds, in degree $< n/2$: for $n = 16$, 12 polynomials at agreement 10 and 3 at 11; for $n = 32$, 122 at agreement 19, 28 at 20 and 3 at 23 **[checked]**. So at exactly $5n/8$ genuine the truth is at least about $n$ (not 7), and above $5n/8$ note 01's Parseval cap $5/8 + O(L^{-1/2})$ is the relevant bound for that mechanism. For (i) see the next section.

## 7. Dependence on the field and the domain

**Pigeonhole. [proved]** There are at most $2^{mt}$ values of $(e_1, \dots, e_t)$, so a class of size $\binom{n}{T}/2^{mt}$ exists. For $m = 64$, $N = 25$, rate 1/2 this is nontrivial only for $64(\tau - 1/2) < H(\tau)$, that is $\tau < 0.5156$. On leanVM's shape $e_1 \in D$ (25 bits) and $e_2 \in \mathrm{span}(1, \dots, x^{48})$ (49 bits), which changes nothing at this scale. In a label space $L_W(D)$ with $M$ labels the count is $\binom{M}{j}/2^{b}$ with $b$ the smaller of $64 t'$ and the formal count $\sum_{r \le a+1} \binom{\log M}{r}(a + 2 - r)$ for depth $t' < 2^{a+1}$; the best fractions this reaches are $9/16$ ($M = 16, 32, 64$) and $19/32$ ($M = 32$, 1323 genuine codewords, which is the punctured family of section 5). Pigeonhole never passes $5/8$.

**Subfield label spaces are not available on the real domain. [checked]** If a label space $\Lambda_W = L_W(D)$ of dimension $r$ were contained in $c\,F$ for a subfield $F = \mathrm{GF}(2^e)$ of $K$, every $e_i$ of a label set would cost $e$ bits instead of 64 and pigeonhole would reach about $1/2 + H/e$ (0.61 for $e = 8$). `02_dual_space.py` rules this out for $e = 8$ and every $r \ge 2$ on the real domains $N = 25, 26, 27, 28$ (real modulus), and for $e = 16$ at $N = 25$. The argument: for a hyperplane $H = \ker\varphi$ of $D$ put $u_\varphi = \prod_{x \in D \setminus H} x$ and $w_\varphi = 1/u_\varphi$. Then $\varphi \mapsto w_\varphi$ is $\mathbb{F}_2$-linear (**[checked]** by brute force for $N = 3, \dots, 6$, classical: the $w_\varphi$ are the roots of the adjoint of $L_D$), so $D^\star = \{w_\varphi\} \cup \{0\}$ is an $N$-dimensional subspace, and $(\Lambda_W)^\star = \{w_\varphi : \varphi|_W = 0\} \subseteq D^\star$ because $u_\varphi$ computed in $D$ equals the one computed in $\Lambda_W$ (**[proved]**: $L_H(a) = L_{L_W(H)}(L_W(a))$). If $\Lambda_W \subseteq cF$ then $(\Lambda_W)^\star \subseteq c'F$, so two elements of $D^\star$ have a ratio in $F \setminus \mathbb{F}_2$, that is $D^\star \cap \lambda D^\star \ne 0$ for some $\lambda \in F \setminus \mathbb{F}_2$. The script computes $D^\star$ and finds $D^\star \cap \lambda D^\star = 0$ for all 254 values of $\lambda \in \mathrm{GF}(2^8) \setminus \mathbb{F}_2$ at $N = 25, 26, 27, 28$, and for all 65534 values in $\mathrm{GF}(2^{16}) \setminus \mathbb{F}_2$ at $N = 25$. For $e = 16$ and $N = 26, 27, 28$ it finds 30, 60 and 282 values of $\lambda$ with a 1-dimensional intersection, the number expected for a random space: these are label spaces with 4 labels inside a multiple of $\mathrm{GF}(2^{16})$, too small to carry a list. $\mathrm{GF}(2^{32})$ was not tested (too many $\lambda$); by counting, label spaces of dimension 2 or 3 inside a multiple of it should exist, with at most 8 labels.

**A [BKR10]-type family and why it is absent here. [proved] for the formula, [conjectured] for the conclusion.** At rate 1/16 the natural family at the Johnson radius is: subspaces $V$ of codimension 2 sharing the second coefficient of $L_V$, $T = n/4 - 1$. With $L_D = L_V^4 + qL_V^2 + pL_V$ the second coefficient is determined by $q(V) = \sum_{\omega \in \Omega \setminus 0} 1/\omega$, where $\Omega = \{w_\varphi : \varphi|_V = 0\}$ is a 2-dimensional subspace of $D^\star$. So the class of $V$ is the set of planes $\{0, w_1, w_2, w_1 + w_2\} \subseteq D^\star$ on the cubic $w_1^2 + w_1w_2 + w_2^2 = q\,w_1w_2(w_1 + w_2)$. If $D^\star$ is a subfield of size $n$ this has about $n/6$ solutions per $q$ (Johnson allows $3n/8$): Johnson is tight at rate 1/16 for full-field Reed-Solomon codes. For an $N$-dimensional $D^\star$ in $\mathrm{GF}(2^{64})$ behaving like a random subspace the expected number of solutions per $q$ is $2^{2N - 64}$, that is $2^{-8}$ at $N = 28$ (level 0 at rate 1/16), so I expect no such class there; it would appear for $N > 32$. I did not enumerate the cubic on the real $D^\star$. Very low rates, where pigeonhole over $\mathrm{GF}(2^{64})$ itself succeeds, are treated in note 01.

## 8. General words, not only common-top

**Oracle.** `02_lists.c` counts, for a word $w$ on a domain of $n \le 64$ points, all polynomials of degree $< k$ by exact agreement, each once (from the $k$-subset of its first $k$ agreement points; cost $\binom{n - T + k}{k}$ interpolations). `climb` mode is simulated annealing over words: a move sets $w(x)$ to the value at $x$ of the interpolant of a random $k$-subset, biased to the agreement sets of the current near-list.

**Structured words. [checked]** (`02_words.py`, leanVM shape in $\mathrm{GF}(2^{64})$). For $n = 16$, $k = 8$: $x^9$ has 715 at agreement 9; $x^{10}$ has 51 at 9 and 4 at 10; $x^{11}, \dots, x^{14}$ have 40, 6, 15, 1 at agreement 9 and nothing above; pole words $x^j/(x - \beta)$, $\beta \notin D$, all $j$: nothing at agreement $\ge 9$; $1/L_V$ and $1/(L_V - c)$: at most 16 at agreement 9. For $n = 32$: $k = 4$, agreement $\ge 7$: only $x^7, x^{15}, x^{31}$ have lists (the 155 flats at agreement 7), and $1/(L_V - c)$ gives the 4 or 2 cosets of $V$; $k = 8$, agreement $\ge 13$: only $x^{15}$ and $x^{31}$ (the 31 flats at agreement 15) and the coset words; $k = 2$, agreement $\ge 4$: only the coset words. Monomials and pole words give nothing beyond the flat family.

**Annealing, $n = 16$. [checked]** (lower bounds only; three seeds, 30000 moves each, `02_climb_run.sh`, and two earlier trial runs on the leanVM shape that gave the 15 and the 18). Largest list found, against the simple common-top maximum of section 3:

| $k$ | $T$ | Johnson bound | random domain: found | common-top | leanVM shape: found | common-top |
| --- | --- | --- | --- | --- | --- | --- |
| 8 | 10 | none | 11 | 7 | 15 | 15 |
| 8 | 11 | 7 | 3 | 3 | 3 | 3 |
| 8 | 12 | 2 | 1 | 1 | 1 | 1 |
| 4 | 6 | none | 16 | 7 | 18 | 15 |
| 4 | 7 | 64 | 15 | 15 | 15 | 15 |
| 4 | 8 | 5 | 1 | 2 | 1 | 2 |
| 2 | 4 | none | 9 | 4 | 9 | 8 |
| 2 | 5 | 7 | 6 | 3 | 6 | 3 |

So simple common-top is not optimal on small instances (11 against 7, 16 against 7, 9 against 4, 6 against 3). The search is weak (it misses the list of 2 at $k = 4$, $T = 8$, and at $n = 32$ with 12000 moves it failed to find even the known common-top lists for $k = 4$, $T = 8, 9$, so I draw no conclusion from $n = 32$). What it found is explained as follows.

- $k = 8$, $T = 10$: the padded-hyperplane word of note 01 has 12 at agreement 10 and 3 at 11 (section 6), the same order as the 11 to 15 found. These are locators with multiplicities, covered by Theorem W.
- $k = 2$, $T = 5$: six lines pairwise meeting in distinct points, each point on exactly two lines. **Tangent lines over a Sidon set. [proved]** Let $A \subseteq D$ be a Sidon set (all sums $a + a'$, $a \ne a'$, distinct). The lines $P_a(X) = aX + a^2$ meet pairwise at $X = a + a'$, where both take the value $aa'$. So the word $w(a + a') = aa'$ has the $|A|$ lines $P_a$ at agreement $|A| - 1$. **[checked]** with the oracle (`02_sidon_lines.py`): $(n, |A|, T) = (16, 6, 5)$, $(32, 7, 6)$, $(64, 9, 8)$, in each case exactly $|A|$ lines at agreement $|A| - 1$, at or just above the Johnson radius $\sqrt n$. This is a list that is not of locator type: the list is a conic $a \mapsto P_a$ in the space of polynomials, and every point lies on exactly 2 members. It lives at rate $2/n$ and I found no analogue at constant rate: for a family $P_a = \sum_{i \le r} q_i(X) a^i$ every point lies on at most $r$ members, so $L\,T \le r\,n$, and at agreement $\tau n$ a list of size $L$ needs $r \ge \tau L$.
- $k = 4$, $T = 6$ and $k = 2$, $T = 4$: not analysed.

**Is common-top optimal?** No for small lists below the Johnson radius. For the question that matters (lists that grow with $n$ at a fixed fraction) I have no example of a growing list that is not a polynomial locator (with multiplicities), and at $T = 11, 12$ for $n = 16$, $k = 8$, the search found nothing above the common-top values 3 and 1. **[conjectured]**: at rate 1/2 the largest fraction with lists growing linearly in $n$ is $5/8$, for all words.

**Interleaving.** Not explored beyond this remark **[proved]**: the words of every construction above are $K$-valued, and a polynomial over the quadratic extension $E$ agreeing with a $K$-valued word on more than $k$ points has its second coordinate zero, so over $E$ these words have the same lists. A 2-interleaved list at agreement $T$ needs both coordinate lists with intersecting agreement sets, which only helps if each coordinate has lists at agreement about $(n + T)/2$, deep inside the Johnson regime for $T \ge 5n/8$.

## 9. Scaling, conjectures, and what a larger computation could settle

Scaling of each structure with $N$ at fixed rate $\rho = 2^{-R}$:

| structure | agreement | size | growth |
| --- | --- | --- | --- |
| flats, $R \ge 2$ | $2\rho n - 1$ ($2\rho n + \ell - 1$ with slack) | $\binom{N}{R-1}_2 \approx 2^{(R-1)(\kappa+1)}$ (times $2^{R-1}$ with slack) | $n^{R-1}$ |
| glued coset unions, $\rho = 1/2$ | $(1/2 + 1/M')n$, $M' \ge 8$ | $\approx (n/M')\binom{2M'}{M'+2}/2M'$ | linear in $n$, $56n - 392$ at $5/8$ |
| lifts (Lemma 3) of any small list | same fraction | constant | none |
| flat minus common set | $(2^i + 1)\rho n - 1$ | $2^{R-i} - 1$ | none |
| hyperplane plus common set, $\rho = 1/2$ | $n/2 + n/(L+1)$ | $L$ | none |
| padded hyperplanes (note 01), $\rho = 1/2$ | $5/8 + O(L^{-1/2})$ | $L$ | none at fixed fraction |
| pigeonhole | $T - k \le n H(\tau)/m$ | $\binom{n}{T}/2^{m(T-k)}$ | exponential, only for $\tau - \rho < H/m$ |
| Sidon tangent lines | $\sqrt n$, $k = 2$ | $\sqrt n$ | rate $\to 0$ |

Conjectures.

- **C1.** On leanVM's domains, for rate 1/2 and every $\epsilon > 0$, $\Lambda((5/8 + \epsilon)n)$ is bounded independently of $n$ (by $O(\epsilon^{-2})$). Evidence: Proposition 6 (formal model, simple locators), note 01's Parseval cap for padded hyperplanes, exhaustive common-top at $n = 16, 32$ on four domains, annealing at $n = 16$.
- **C2.** On leanVM's domains, for rates 1/8 and 1/16, $\Lambda(T)$ is bounded independently of $n$ for $T \ge (2\rho + \epsilon)n$. Evidence: Proposition 6 and the exhaustive tables. Weaker than C1: the gap is wide ($0.25$ to $0.354$, $0.125$ to $0.25$), no multiset or general-word search was run at these rates beyond $n = 16$, and at rate 1/16 the full-field code does have growing lists at the Johnson radius (section 7).
- **C3.** The class of $L_U^5$ on leanVM's domains is exactly the family of Theorem 5 ($56n - 392$ in degree $\le n/2$). Proved in the formal model, checked with the oracle at $n = 32$.

What I could not settle, and what would.

1. *Genericity of the real domain at depth about $n/8$.* The formal model needs distinct formal tuples to have distinct values in $\mathrm{GF}(2^{64})$. Counting says accidental coincidences are absent above $\tau = 0.516$, but a structured coincidence is not excluded. A test at a scale where wrapping occurs: $N = 6$ in $\mathrm{GF}(2^{16})$ or $N = 7$ in $\mathrm{GF}(2^{20})$ with the power basis, where $m/N$ is as in the real system. Exhaustive common-top at $n = 64$ needs $\binom{64}{24} \approx 2^{58}$ sets and is out of reach, but the classes above $5n/8$ can be searched through the moves of Proposition 6 (swap a codimension-2 flat) in a few CPU-hours. Not run.
2. *Multiset locators, exhaustively.* All multisets with multiplicities $\le 2$ on $n = 16$ are $3^{16} = 4.3 \cdot 10^7$ and would give the exact polynomial-locator maxima at $T = 10, 11, 12$ to compare with the annealing; a few minutes in C. Not run.
3. *General words at $n = 32$, rate 1/2.* One oracle call costs about a minute ($\binom{29}{16}$ interpolations), so annealing is not feasible with this oracle. An incremental oracle (update the list under a one-point change of the word) would make it feasible. Not built.
4. *The extra 448 genuine members at $n = 32$* (double zero at $p$): whether they grow like $n$. Running `02_confirm32.py` style at $n = 64$ is infeasible with the oracle; a direct enumeration of 38-sets through the Walsh criterion is feasible. Not run.
5. *Rates 1/8 and 1/16 for general words.* Only annealing at $n = 16$ ($k = 2$), which is the rate-1/8 instance and too small to say anything about growth.

## 10. Scripts

All under `scripts/`, prefix `02_`. C programs build with `cc -O2 -mcpu=native -o <out> <file>.c` (they include `02_gf.h`; NEON carry-less multiply for $\mathrm{GF}(2^{64})$, portable fallback otherwise). Nothing is installed; binaries and outputs were kept outside the repository.

| script | what it does | time |
| --- | --- | --- |
| `02_gf.py` | $\mathrm{GF}(2^m)$ arithmetic, subspace polynomials, locators, interpolation; self-tests | 1 s |
| `02_ct16.py m power\|random:<seed>` | exhaustive common-top table, $n = 16$ | 1 s |
| `02_ct32.c`, `02_ct32_run.sh`, `02_check_ct32.py`, `02_tables.py` | exhaustive common-top table, $n = 32$, with dumps of maximal classes; cross-check; markdown tables | 1 min per domain on 4 cores |
| `02_class_structure.py` | period groups, spans, intersections of dumped classes | 5 s |
| `02_walsh_check.py N [Tmax]` | Theorem W and its converse, exhaustively | 15 s ($N = 4$), a few minutes ($N = 5$, $T \le 6$) |
| `02_glue58.py N` | Theorem 5 at $5n/8$, slack and genuine, all members | 0.5 s, 5 s, 2 min for $N = 5, 6, 7$ |
| `02_glue_general.py N R mp samples` | Theorem 5, general parameters, sampled | seconds |
| `02_lists.c` | exhaustive list oracle (`profile`, `members`) and annealing (`climb`) | see section 8 |
| `02_confirm32.py`, `02_padded_word.py`, `02_words.py`, `02_sidon_lines.py` | oracle runs of sections 5, 6, 8 | up to 80 s each |
| `02_climb_run.sh`, `02_climb_analyze.py` | annealing batches and description of the words found | 6 min ($n = 16$) |
| `02_dual_space.py 25 check16` | $D^\star$ of the real domain and the subfield test | 15 s |
