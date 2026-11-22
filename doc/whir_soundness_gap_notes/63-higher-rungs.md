# 63. The higher rungs $H_4$, $H_5$ and the induction step (researcher 63, round 13)

Labels: **[proved]** with the proof here, **[checked]** by a script under `scripts/63_*` (sizes stated), **[conjectured]** or **[open]** otherwise. Setting and notation are those of note 57: $K$ of characteristic 2 with $q$ elements, $D$ of dimension $N$, $n = 2^N$, $k = \rho n$, windows $W_x = x + C$, $r = |C|$, mixed code $c_\mu$. Section 1 holds for every window set containing the centre; Section 7 records the negative result for local and stride windows, which I had found independently before the erratum reached me. From Section 2 on the windows are those of note 66 (a sparse graph with $d$ partners a position) and the proofs are written against the axioms (W1) to (W3).

## 0. Summary

1. **$H_4$ and $H_5$ are not proved.** What is proved is every stratum except one, under (W1), (W2) and one more graph constant (near interiors, $\gamma'_j$, Section 2). The open stratum, the same for every rank $u \ge 3$: affinely independent tuples whose primitive part has degree $m$ between $\frac{u-2}{u-1}k$ and $k$, is determined by its field of window relations (rigid), and has more than $(2k + m)/3$ (for $u = 3$) fully covered deficient windows that overlap heavily. The lead's cross-product argument for $u - 1$ short vectors has the same hole as soon as windows overlap: the cross product vanishes at every point that lies in two windows with different relations (5.4).
2. **Proved pieces (Sections 1, 3, 5).** (a) The weighted first moment (Proposition 1.2): a family of $q^N$ tuples satisfies $\sum_x (c_x - 1)_+ \le G_\lambda + \lambda(N + s)$ for every $\lambda$; thin families are exactly as dangerous as their free sum, and dependent tuples cost $\frac{t-1}{v}$ times the excess of a lower rung. (b) Free and paid agreements together close for $\gamma \le 2/t$ (Proposition 3.2); pure free configurations close with $d = 6, 7, 9, 10$ at rates 1/2 to 1/16 for all $t \le 16$ (note 60's bound with $\gamma$, table in 3.1). (c) The revealed-set lemma (Lemma 5.1): on at most $m + 1$ points Reed-Solomon values are free, and windows of rank at most $u - 1$ cost at least $|U| - \alpha_{u-1}$ dimensions whatever their overlaps; this settles the transversal range for $\gamma \le 1/u$. (d) Low degree $m \le \frac{u-2}{u-1}k$ needs no structure (Lemma 5.3). (e) Windows of rank one, in particular the deficiency-2 windows of a quadruple, close like pencils (Proposition 5.4). (f) Rigid tuples with $|J| \le (2k + m)/3$ close because a rigid tuple is determined by its relation field (Proposition 5.6).
3. **A lemma the lead asked for is false, harmlessly.** No bound "$\theta n$ deficient windows for every rank-3 tuple" follows from the axioms: a planted four-part graph satisfying (W2) with a random graph's $\gamma$ has a quadruple all of whose windows are deficient (5.5). It satisfies $H_4$ anyway, because the family is thin. So the open problem is a count of tuples, (CS$'_u$) in 5.6, not a bound on deficient windows; I propose a route through two graph properties (flexibility on a revealed set, rigidity by bootstrap percolation of determined points and lines) for which a first moment over the graph is available.
4. **Constants.** In the proved parts rung $t$ needs $\gamma \le 1/(t-1)$: $d = 9, 12, 14, 19$ for $t = 4, 5, 6, 8$ at rate 1/2 (7, 9, 10, 14 at rate 1/4), against $d = 6$ for the free part. The entropy slack is about $(2t - 1)/64$, twice the lead's, because the families are indexed by coincidence sets.
5. **Most dangerous family found.** For non-spanning windows: the leave-one-out quadruple with a spine (a conic composed with $L_G$, 7.2), free sum $1.75n$ against $3k = 1.5n$ at rate 1/2, and in general an excess of $(t-2)/n'$ on a quotient of $n'$ points. For the sparse random graph none of the structured families I tried comes near the bound (Sections 5.5, 7, 8); the danger is confined to the uncounted rigid stratum.
6. **Local and stride windows** (Section 7): recorded as broken; test families given.

## 1. Framework: exact ranks, types, and the weighted first moment

### 1.1 Local rank, deficiency, circuits

For $t$ distinct polynomials $P_0, \dots, P_{t-1}$ of degree below $k$ and sets $S_0, \dots, S_{t-1}$: $I_x = \{i : x \in S_i\}$, $c_x = |I_x|$, and for $I \subseteq [t]$ let $\rho_x(I)$ be the dimension of the affine span of the window vectors $(P_i|_{W_x})_{i \in I}$ in $K^{W_x}$ (so $\rho_x(I) = \dim \mathrm{span}\{(P_i - P_j)|_{W_x} : i, j \in I\}$). Step 1 of note 57 is: the probability that one word agrees with $c_\mu(P_i)$ on $S_i$ for all $i$ is exactly $q^{-\sum_x \rho_x(I_x)}$ **[proved, note 57]**. The *deficiency* is $\delta_x(I) = (|I| - 1)_+ - \rho_x(I) \ge 0$.

**Lemma 1.1 (structure of the deficiency) [proved].** (a) $\delta_x$ is nondecreasing in $I$. (b) The relation "$P_i = P_j$ on $W_x$" is an equivalence relation $\pi_x$ on $[t]$ (the *free partition* at $x$), it is the meet over $y \in W_x$ of the point partitions $\sigma_y$ ("$P_i(y) = P_j(y)$"), and $\rho_x(I) = 0$ iff $I$ lies in one class of $\pi_x$. (c) Choose an affine basis $B \subseteq I$ of the window vectors; every $i \in I \setminus B$ lies in exactly one minimal dependent set (circuit) $A_i \subseteq B \cup \{i\}$, and $\delta_x(I) = |I \setminus B|$. A circuit of size 2 is a free agreement of a pair, a circuit of size 3 a locally collinear triple (pencil deficiency), a circuit of size $s$ an $s$-tuple whose $s - 1$ differences have rank $s - 2$ on the window with every proper subfamily independent.

*Proof.* (a) Adding a member raises $|I|$ by one and the affine rank by at most one. (b) Equality of restrictions is transitive; $P_i = P_j$ on $W_x$ iff $i \sim j$ at every point of the window. (c) is the standard basis and fundamental circuit statement for the affine matroid of the window vectors. $\square$

So every unit of loss at a position is witnessed by a sub-tuple of size $s \le c_x$ that is minimally dependent on that window, and the sub-tuple with the agreement sets cut down to those positions is itself a realized configuration of rung $s$. This is the precise form of "the loss of a rung is capped by the lower rungs"; what it gives and what it does not give is in 1.4 and Section 5.

### 1.2 The curve and the braid arrangement

Put $d_i = P_i - P_0$ ($i = 1, \dots, u$, $u = t - 1$), $g = \gcd(d_1, \dots, d_u)$, $d_i = g a_i$, $m = \max \deg a_i \le k - 1 - \deg g$, and $\gamma = (a_1 : \dots : a_u) : \mathbb{P}^1 \to \mathbb{P}^{u-1}$, a map of degree $m$. The hyperplanes $H_{ij} = \{z_i = z_j\}$ and $H_{0i} = \{z_i = 0\}$ form the braid arrangement; its flats are indexed by the partitions $\sigma$ of $[t]$, $X_\sigma$ of codimension $\mathrm{rk}(\sigma) = t - |\sigma|$. Then **[proved, by definition]**: for $y \notin Z(g)$, $\sigma_y$ is the partition of the smallest flat containing $\gamma(y)$; on $Z(g)$ all members coincide. For a subset $I$ covering $x$, $\rho_x(I)$ is the rank of the matrix $(g(y)\,a_i(y) - g(y)\,a_{i_0}(y))_{i \in I,\ y \in W_x}$, so (away from zeros of $g$) the window is deficient for $I$ iff the $r$ points $\gamma(W_x)$, projected to the coordinates of $I$, lie in a proper linear subspace of that projection, and the deficiency is the codimension of their span. In this language the things that can make many windows deficient are:

1. **common zeros** (wildcards): $W_x \cap Z(g) \ne \emptyset$ lowers the number of effective window points; $W_x \subseteq Z(g)$ gives rank 0 for every $I$;
2. **flats** (free agreements): $\gamma(W_x) \subseteq X_\sigma$ gives the free partition $\pi_x \ge \sigma$; this is the case of circuits of size 2 and it is deterministic (probability 1);
3. **sub-pencils**: for a triple $\{i, j, l\}$ the projected window image is one point of $\mathbb{P}^1$, i.e. $\xi = (a_i - a_l)/(a_j - a_l)$ is constant on the window with a value outside $\{0, 1, \infty\}$ (the three special values are case 2);
4. **nets of rank 3 and more**: for a quadruple the window image lies on a line of $\mathbb{P}^2$ that is not a line of the arrangement and varies with $x$; in general the window image spans a proper subspace that is not a flat;
5. **composed maps**: $\gamma = \gamma' \circ \varphi$ with $\varphi$ of degree $e \ge 2$ (a function of $L_U$ when $\varphi$ is $U$-periodic). On a window where $\varphi$ takes $v$ values the image has at most $v$ points, so every $I$ has rank at most $v - 1$. For local windows inside cosets of $U$ this is the family (iv) of the brief ($v = 1$, rank 1 after multiplying by $g$; rank $s$ for $s$ independent twists $g_1, \dots, g_s$); for the cube window and a group-sum subspace $U$ of codimension $c$ it gives $v = c + 1$.

### 1.3 The local types for $t = 4$

A position covered by $c$ members has one of the following types (the affine matroid of $c$ window vectors, with coincidences). "Gain" is $\rho_x$, the exponent of $q^{-1}$ the position contributes; "loss" is $\delta_x$.

| $c$ | type | description | gain | loss | codimension of the type on an isolated window |
| --- | --- | --- | --- | --- | --- |
| 2 | 2a | generic | 1 | 0 | 0 |
| 2 | 2b | free pair ($d_{ij} = 0$ on $W_x$) | 0 | 1 | $r$ |
| 3 | 3a | generic | 2 | 0 | 0 |
| 3 | 3b | locally collinear, three distinct vectors (pencil) | 1 | 1 | $r - 1$ |
| 3 | 3c | one free pair, third distinct | 1 | 1 | $r$ |
| 3 | 3d | all three equal | 0 | 2 | $2r$ |
| 4 | 4a | generic | 3 | 0 | 0 |
| 4 | 4b | coplanar, no three collinear (a circuit of size 4) | 2 | 1 | $r - 2$ |
| 4 | 4c | three collinear, fourth off the line | 2 | 1 | $r - 1$ |
| 4 | 4d | one free pair, the three distinct vectors independent | 2 | 1 | $r$ |
| 4 | 4e | four distinct collinear vectors | 1 | 2 | $2(r - 1)$ |
| 4 | 4f | one free pair, three distinct collinear vectors | 1 | 2 | $2r - 1$ |
| 4 | 4g | two free pairs (classes 2 + 2) | 1 | 2 | $2r$ |
| 4 | 4h | a free triple and one more (classes 3 + 1) | 1 | 2 | $2r$ |
| 4 | 4i | all four equal | 0 | 3 | $3r$ |

**[proved: enumeration of affine matroids on at most four points; the codimension is that of "a $u' \times r$ matrix has rank at most $\rho$", $(u' - \rho)(r - \rho)$, intersected with the coincidence conditions.]** With labels there are 68 local types for $t = 4$ (5 with $c \le 1$, 12, 24, 27), so a union bound over all type patterns costs $\log_2 68 / 64 = 0.095$ in $\varepsilon_4$ where the sets alone cost $4/64$; for $t = 5$ there are a few hundred labelled types, about $0.13$ **[estimate]**. On an isolated window every type costs at least $r - \rho \ge r - t + 2$ times its loss, so $r \ge t - 1$ is the trivial necessary condition; the difficulty is entirely in overlapping windows (clusters) and in dependent conditions (non-transversality).

The global types of a quadruple are: G0 affinely independent ($\dim V = 3$, $q^{3k}$ tuples); G1 coplanar, no three collinear ($q^{2k + 2}$); G2 three collinear and one off ($q^{2k+2}$); G3 collinear ($q^{k+2}$). In G1 to G3 every position has loss at least $c_x - 1 - \dim V_x$ by dependence alone; these are handled by Corollary 1.4 below and never need more than the lower rungs.

### 1.4 The weighted first moment (how lower rungs and thin families enter)

For a tuple $P$ and $\lambda \ge 1$ put $G_\lambda(P) = \sum_x \max_{I \subseteq [t]} \bigl((|I| - 1) - \lambda\,\rho_x(I)\bigr)_+$. For a set $\mathcal F$ of tuples (modulo translation) with $|\mathcal F| \le q^{N}$ let $s(N)$ be the least $s \ge 0$ with $64\,s' \ge \log_2\binom{n}{\le N + s'} + t(N + s') + 130$ for all $s' \ge s$ (so $s(N) \le (tn + 130)/64$ always, and $s(N) = O(1)$ for $N = O(1)$).

**Proposition 1.2 [proved].** With probability at least $1 - 2^{-129}$ over $\mu$: every $P \in \mathcal F$ and every set system realized by a word satisfy $\sum_x \rho_x(I_x) < N + s(N)$, hence for every $\lambda \ge 1$
$$\sum_x (c_x - 1)_+ \ \le\ G_\lambda(P) + \lambda\,(N + s(N)).$$
*Proof.* The event "realized" only depends on the paid positions $\Pi = \{x : \rho_x(I_x) \ge 1\}$ and the sets $I_x$ there, and $|\Pi| \le R := \sum_x \rho_x(I_x)$. There are at most $\binom{n}{\le r}2^{tr}$ such data with $|\Pi| \le r$, each has probability at most $q^{-R}$, so the probability that some $P \in \mathcal F$ is realized with $R \ge N + s(N)$ is at most $\sum_{r \ge N + s}q^{N}\binom{n}{\le r}2^{tr}q^{-r} \le 2^{-129}$. Then $\sum_x (c_x - 1) = \sum_x ((c_x - 1) - \lambda\rho_x(I_x)) + \lambda R$. $\square$

Three choices of $\lambda$ carry everything below.

- $\lambda = 1$ (**fat families**): $G_1(P) = \sum_x \delta_x([t]) =: \Delta(P)$, the total defect. This is the union bound of note 57, and it needs the counting statement "$N + \Delta \le (t-1)k + \varepsilon n$".
- $\lambda = t - 1$ (**thin families**): $G_{t-1}(P) = F(P) := \sum_x (\text{largest class of } \pi_x - 1)$, the free sum. So a family with $N$ small is as dangerous as its free configurations and no more: $\sum_x (c_x - 1)_+ \le F(P) + (t-1)(N + s(N))$. Its non-free deficient windows, however many, do not matter.
- $\lambda = (t-1)/\bar r$ (**capped rank**): if $\rho_x(I) \ge \min(|I| - 1, \bar r)$ for all $x, I$ then $G_\lambda = 0$ and $\sum_x(c_x - 1)_+ \le \frac{t-1}{\bar r}(N + s)$. A family all of whose windows have rank at most $\bar r$ needs $N \le \bar r k$, not $N \le (t-1)k - \Delta$.

**Corollary 1.3 (dependent tuples reduce to lower rungs) [proved for $t = 4$ given the pencil lemma of rung 3].** A collinear quadruple ($N \le k + 2$) has $\sum_x (c_x - 1)_+ \le F + 3(k + 2 + s(k))$, and $F \le 3\,|\mathrm{int}\,Z(g)|$ is paid by the common zeros. A coplanar quadruple with pencil-deficient set $J$ (windows on which $d_1 \parallel d_2$) and free pattern $\phi$ lies in a family with $N \le 2k + 2 - \mathrm{cost}_3(J, \phi)$, where $\mathrm{cost}_3$ is the cost established at rung 3; with $\lambda = 3/2$, $G_{3/2} \le \tfrac32|J| + (\text{free terms})$, so $\sum_x (c_x - 1)_+ \le 3k + \tfrac32\bigl(|J| - \mathrm{cost}_3\bigr) + (\text{free excess}) + \tfrac32 s + 3$: one and a half times the excess of rung 3. The same computation for $t$ members spanning a space of dimension $v < t - 1$ gives $\frac{t-1}{v}$ times the excess of rung $v + 1$.

**Remark 1.4 (the amplification of a paid unit).** At a position with two free classes of sizes $a, b$ one paid unit merges them and raises $c_x - 1$ by $\min(a, b)$, up to $t/2$. So in mixed configurations the right free quantity is the rank sum $R(\pi) = \sum_x (t - |\pi_x|)$, not $F$: $\sum_x (c_x - 1)_+ \le R(\pi) + \sum_x \rho_x + \Delta^{\mathrm{nf}}$, with $\Delta^{\mathrm{nf}}$ the deficiency from circuits of size at least 3. This is used in Section 3.

## 2. The design of note 66, the axioms, and the constants

Windows $W_x = \{x, \pi_1(x), \dots, \pi_d(x)\}$, symbol $c(P)(x) = P(x) + \sum_l \mu_l(x)P(\pi_l(x))$. The coefficient of the centre is 1, so Step 1 becomes an inequality: for fixed polynomials and sets the probability over $\mu$ is $q^{-\sum_x \rho_x}$ if no $R_x$ contains a vector supported on the centre alone and 0 otherwise **[proved: $(1, \mu(x)) \perp R_x$ is an affine system in $\mu(x) \in K^d$ of rank $\rho_x$ or inconsistent]**. Everything in Section 1 holds with "at most".

Axioms of note 66: (W1) $|W_x| = d + 1$; (W2) $|\{x : W_x \subseteq Z\}| \le \gamma|Z|$ for $|Z| \le \varphi_0 n$; (W3) every point lies in at most $\Delta$ windows. Two more constants appear in the proofs below, both properties of the graph alone:

- (W2$_j$) **near interiors**: $|\{x \in D : |W_x \setminus Z| \le j\}| \le \gamma'_j\,|Z|$ for $|Z| \le \varphi_0 n$ (the centre may lie outside $Z$; $\gamma'_0 = \gamma$). These are the windows that $j$ wildcard points make deficient for free.
- the pair bound $\kappa := k + \varepsilon_2 n$ (rung 2, any window containing its centre): a position covered by all $t$ members is an agreement of two codewords, so every set of fully covered positions has at most $\kappa$ points. This caps every loss at fully covered positions and, unlike (W2) applied to fibres, does not degrade at low rates.

**First-moment values for a random $d$-out graph [checked, `63_gamma.py graph`, $n = 2^{25}$, failure probability $2^{-128}$].** $\gamma(d, \varphi)$ is the root of $D(\gamma \| \varphi^d) = H(\varphi)/\varphi$; $\gamma'_j$ the same with the mean rate $\varphi\Pr[\mathrm{Bin}(d, 1 - \varphi) \le j] + (1 - \varphi)\Pr[\mathrm{Bin}(d, 1-\varphi) \le j - 1]$.

| $d$ | $\gamma(d, \tfrac12)$ | $\gamma(d, \tfrac14)$ | $\gamma(d, \tfrac18)$ | $\gamma(d, \tfrac1{16})$ | $\gamma'_1(d, \tfrac12)$ | $\gamma'_2(d, \tfrac12)$ | $\gamma'_3(d, \tfrac12)$ | $\gamma'_4(d, \tfrac12)$ | $\gamma'_2(d, \tfrac14)$ | $\gamma'_3(d, \tfrac14)$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 6 | 0.498 | 0.348 | 0.290 | 0.259 | 0.976 | 1.564 | 2 | 2 | 1.033 | 1.829 |
| 8 | 0.368 | 0.254 | 0.212 | 0.191 | 0.670 | 1.111 | 1.631 | 2 | 0.593 | 0.961 |
| 9 | 0.323 | 0.223 | 0.187 | 0.168 | 0.565 | 0.932 | 1.412 | 1.864 | 0.476 | 0.733 |
| 10 | 0.286 | 0.198 | 0.167 | 0.150 | 0.483 | 0.785 | 1.209 | 1.676 | 0.394 | 0.579 |
| 12 | 0.232 | 0.162 | 0.137 | 0.124 | 0.367 | 0.572 | 0.879 | 1.285 | 0.288 | 0.394 |
| 14 | 0.194 | 0.136 | 0.116 | 0.105 | 0.290 | 0.433 | 0.649 | 0.958 | 0.224 | 0.291 |
| 16 | 0.165 | 0.118 | 0.100 | 0.091 | 0.238 | 0.340 | 0.493 | 0.717 | 0.182 | 0.228 |
| 24 | 0.103 | 0.076 | 0.065 | 0.060 | 0.133 | 0.171 | 0.220 | 0.287 | 0.102 | 0.118 |

The lead's 0.5, 0.35, 0.22 at $d = 6, 8, 12$ are 0.498, 0.368, 0.232. The worst density below 1/2 is 1/2 itself. Floor: $\gamma(\varphi) \ge 1/(d+1)$ for every graph (a union of windows contains them).

## 3. Free configurations under (W2): part (A)

**3.1 Pure free configurations.** Note 60, Proposition 3.7, uses the cube only through $|\mathrm{int}\,Z| \le (1 - \beta)|Z|$ for $|Z| < k$, so under (W2) with $\varphi_0 \ge \rho$: the free sum of $t$ members is at most $n\,\Phi\bigl(\gamma\rho\binom t2\bigr)$ **[proved, note 60]**. The largest $\gamma$ for which this closes rung $t$ **[checked, `63_gamma.py free`]**: "lit" below $(t-1)k$; "own" below the rung's budget $B_t = (t-1)k + tH(\alpha_t)n/64$; "asym" is $\alpha_t^2/\rho$, the long-list form $\sqrt{\rho\gamma} < \alpha_t$.

| $t$ | 1/2: lit, own, asym | 1/4: lit, own, asym | 1/8: lit, own, asym | 1/16: lit, own, asym |
| --- | --- | --- | --- | --- |
| 3 | 0.667, 0.724, 0.895 | 0.667, 0.729, 0.862 | 0.667, 0.781, 0.878 | 0.667, 0.867, 0.943 |
| 4 | 0.667, 0.706, 0.807 | 0.500, 0.541, 0.725 | 0.500, 0.573, 0.701 | 0.500, 0.624, 0.721 |
| 5 | 0.600, 0.645, 0.752 | 0.400, 0.461, 0.639 | 0.400, 0.453, 0.594 | 0.400, 0.488, 0.592 |
| 6 | 0.600, 0.637, 0.715 | 0.400, 0.448, 0.579 | 0.333, 0.374, 0.521 | 0.333, 0.401, 0.506 |
| 8 | 0.571, 0.607, 0.668 | 0.357, 0.391, 0.503 | 0.250, 0.278, 0.428 | 0.250, 0.295, 0.399 |
| 10 | 0.556, 0.590, 0.639 | 0.333, 0.372, 0.456 | 0.222, 0.264, 0.371 | 0.200, 0.233, 0.335 |
| 12 | 0.545, 0.579, 0.621 | 0.318, 0.349, 0.425 | 0.212, 0.245, 0.333 | 0.167, 0.193, 0.291 |
| 16 | 0.533, 0.567, 0.598 | 0.300, 0.330, 0.386 | 0.183, 0.210, 0.284 | 0.125, 0.152, 0.237 |

Reading with the table of Section 2 (the relevant density for (W2) is $\rho$): every rung up to $t = 16$ closes its pure free part with $d = 6$ at rate 1/2 ($\gamma = 0.498 \le 0.567$), $d = 7$ at rate 1/4 (0.294 against 0.330), $d = 9$ at rate 1/8 (0.187 against 0.210), $d = 10$ at rate 1/16 (0.150 against 0.152). With $d = 8$: all $t \le 16$ at rates 1/2 and 1/4, $t \le 15$ at rate 1/8, $t \le 12$ at rate 1/16.

**3.2 Free and paid agreements together.** By Remark 1.4 the pure free bound is not the statement the rung needs: a thin non-transversal family may also pay, and a paid unit is amplified by the free classes it merges. The following closes mixed configurations with a cruder constant.

**Proposition 3.2 [proved].** Assume (W2) with $\varphi_0 \ge \rho$. For a tuple let $T_e$ be the set of positions where the pair $e = \{i, j\}$ coincides on the whole window, $Y_e = \bigcup_{x \in T_e} W_x$, and $M$ the largest weight $\sum_{e \in T}|Y_e|$ of a spanning tree $T$ of the complete graph on $[t]$. With probability $1 - 2^{-128}$ every $t$ members with a realized set system satisfy
$$\sum_x (c_x - 1)_+ \ \le\ (t-1)k + \Bigl(\frac{\gamma t}{2} - 1\Bigr)M + \Delta^{\mathrm{nf}} + \tilde s, \qquad \tilde s \le \frac{(2t - 1)n + t\log_2 t + 130}{64}.$$
In particular for $\gamma \le 2/t$, tuples whose only deficiencies are free agreements satisfy $H_t$ with $\varepsilon_t = \tilde s/n$, whatever their dependence and however non-transversal their coincidence pattern.

*Proof.* The tuples (modulo translation) with $P_i = P_j$ on $Y_e$ for all $e$ form a linear space; along a spanning tree the differences $d_e$ are free coordinates and $d_e$ ranges over the polynomials vanishing on $Y_e$, so its dimension is at most $(t-1)k - M$ (MDS, $|Y_e| < k$). Proposition 1.2 for this family, union over the at most $t^{t-2}2^{(t-1)n}$ choices of the tree and its sets: $\sum_x \rho_x \le (t-1)k - M + \tilde s$. By Remark 1.4, $\sum_x (c_x - 1)_+ \le R(\pi) + \sum_x\rho_x + \Delta^{\mathrm{nf}}$. A spanning forest of $\pi_x$ has $t - |\pi_x|$ edges $e$ with $x \in T_e$, so $R(\pi) \le \sum_e |T_e| \le \gamma\sum_e|Y_e|$ by (W2) ($T_e \subseteq \mathrm{int}\,Y_e$). A uniformly random spanning tree contains each edge with probability $2/t$, so $M \ge (2/t)\sum_e |Y_e|$. $\square$

So mixed free and paid agreements are closed for $\gamma \le 2/t$: $t = 4$ with $d \ge 6$, $t = 5$ with $d \ge 8$ ($0.368 \le 0.4$), $t = 6$ with $d \ge 9$, $t = 8$ with $d \ge 12$ at rate 1/2 (the density is $\rho$, so lower rates need less: $t = 8$ with $d = 9$ at rate 1/4). Between $2/t$ and the "own" column of 3.1 the mixed case is open; I expect the truth to be the "own" column, the gap being the crude step $R(\pi) \le \sum_e|T_e|$. The entropy term $\tilde s$ is about twice the lead's $tH/64$: the family is indexed by the coincidence sets of a tree, and I do not see how to avoid paying for them in a union bound.

## 4. The counting statement, and where each stratum is treated

By Proposition 1.2 with $\lambda = 1$, rung $t$ for affinely independent tuples is implied by the following statement about Reed-Solomon tuples and the window graph, with no probability in it.

**(CS$_t$).** For every set system, the number of $t$-tuples (modulo translation, distinct members) whose total deficiency on it is at least $\Delta$ is at most $q^{(t-1)k - \Delta + e\,n}$, for set systems satisfying the lower rungs.

Deficiency units are circuits (Lemma 1.1), so (CS$_t$) is a statement about the simultaneous codimension of: free pairs (Section 3), pencil-deficient windows of sub-triples (rung 3), and for each $4 \le a \le t$ windows on which a sub-tuple of $a$ members has rank $a - 2$ or less. The new object at rung $t$ is the last one with $a = t$, at positions covered by all $t$ members: **windows on which the rank $u = t - 1$ tuple $(d_1, \dots, d_u)$ has rank at most $u - 1$.** Call the set of these windows $J$; $|J| \le \kappa$ by the pair bound. Write $d = g\,a$ with $a$ primitive of degree $m$; there are $q^{k - m}$ choices of $g$ (times the zero pattern of $g$, which is a wildcard question, Section 5.6). The strata of $a$:

| stratum | where | status under (W1) to (W3) |
| --- | --- | --- |
| low degree, $m \le \frac{u-2}{u-1}k - \frac{\varepsilon_2 n + u}{u - 1}$ | 5.2 | **proved**, no structure needed |
| $J$ small in closure: $|\bigcup_J W_x| \le m + 1$ (transversal range, overlaps allowed) | 5.1 | **proved** under (W2$_{u-1}$) with $\gamma'_{u-1} < 1$ |
| windows of rank 1 (for $u = 3$: deficiency 2) | 5.3 | **proved** for $d + 1 \ge 2(u-1)$ |
| unbalanced lattice with $u - 1$ short vectors, classes separated | 5.4 | **proved** |
| rigid tuple with $|J| \le (2k + m)/3$, or determined by the relation lines of at most $(k + m)/2$ windows ($u = 3$) | 5.5 | **proved** |
| rigid tuples of degree $m > k/2$ with more, heavily overlapping deficient windows | 5.5, 5.6 | **open**, reduced to a property of the graph |
| ranks $2, \dots, u - 2$ for $u \ge 4$ | 5.6 | **open**, same nature |

## 5. Deficient windows at rank $u = t - 1$: part (B)

Throughout: $a \in K[X]^u$ primitive of degree $m < k$, not contained in a hyperplane (the tuple is affinely independent), $J$ a set of windows on each of which the values $a(y)$, $y \in W_x$, span at most $u - 1$ dimensions, $Y(J) = \bigcup_{x \in J}W_x$. A *relation field* is a choice $\lambda_x \in \mathbb{P}^{u-1}$ with $\lambda_x \cdot a(y) = 0$ on $W_x$; a *class* is a maximal set of windows of $J$ with the same $\lambda$, connected through shared points; $p$ is the number of classes, $Y_C$ the closure of class $C$. The lattice $M(\lambda) = \{b \in K[X]^u : \lambda_x \cdot b(y) = 0\ \forall x \in J, y \in W_x\}$ has index $Q(\lambda) = \sum_{y}s_y$, $s_y = \dim\mathrm{span}\{\lambda_x : y \in W_x\}$, successive minima $e_1 \le \dots \le e_u$ with $\sum e_i = Q$, and the tuples of degree at most $m$ with this relation field form a space of dimension $\sum_i (m + 1 - e_i)_+$ **[standard: reduced bases of $K[X]$-lattices]**. For primitive $a$, $s_y \le u - 1$ everywhere.

### 5.1 The revealed-set lemma (transversal counting with overlapping windows)

**Lemma 5.1 [proved; brute force over GF(2) and GF(4) on seven small systems, `63_toy.py lemmaR`].** Let $U \subseteq D$ with $|U| \le m + 1$ and let $\alpha_{u-1}(U; J)$ be the largest size of a set $E \subseteq U$ with $|E \cap W_x| \le u - 1$ for every $x \in J$. The number of $a \in K[X]^u$ of degree at most $m$ with all windows of $J$ of rank at most $u - 1$ is at most
$$(d + 2)^{(u-1)|J|}\ q^{\,u(m+1) - (|U| - \alpha_{u-1}(U; J))}.$$
If moreover (W2$_{u-1}$) holds and $J_U = \{x \in J : W_x \subseteq U\}$, then $|U| - \alpha_{u-1}(U; J) \ge |J_U| / \gamma'_{u-1}$.

*Proof.* Reed-Solomon is MDS, so $a \mapsto (a(y))_{y \in U}$ is onto $(K^u)^U$ with fibres of $q^{u(m + 1 - |U|)}$ tuples; count value assignments. Order $U$. For each window let $B_x$ be the set of points of $W_x \cap U$ whose value is not in the span of the earlier values in the window: $|B_x| \le u - 1$, at most $(d+2)^{u-1}$ possibilities. Given all $B_x$, let $E$ be the set of points lying in $B_x$ for every window $x \in J$ through them. Then $|E \cap W_x| \le |B_x| \le u - 1$, so $|E| \le \alpha_{u-1}$; a point outside $E$ has a window in which its value lies in a span of dimension at most $u - 1$ fixed by earlier points, at most $q^{u-1}$ choices. For the second claim put $Z = U \setminus E$: every $x \in J_U$ has $|W_x \setminus Z| = |W_x \cap E| \le u - 1$. $\square$

**Corollary 5.2 (transversal range) [proved].** If $|Y(J)| \le m + 1$: cost minus loss of the deficiency-1 windows is at least $|J|\,(1/\gamma'_{u-1} - 1 - (u-1)\log_2(d+2)/64)$. The cruder count over relation fields ($q^{(u-1)|J|}$ fields, each point of $Y$ one independent condition by MDS) gives cost minus loss at least $|Y| - u|J| \ge |J|(1/\gamma - u)$, with no entropy term. So the transversal range closes if $\gamma(\rho) \le 1/u$ or $\gamma'_{u-1}(\rho) \le (1 + (u-1)\log_2(d+2)/64)^{-1}$:

| | $t = 4$ ($u = 3$) | $t = 5$ | $t = 6$ |
| --- | --- | --- | --- |
| rate 1/2: least $d$ by $\gamma \le 1/u$; by $\gamma'_{u-1}$ | 9; 10 | 12; 13 | 14; 16 |
| rate 1/4: least $d$ by $\gamma \le 1/u$; by $\gamma'_{u-1}$ | 7; 7 | 9; 9 | 10; 11 |

(**[checked]** with the first-moment constants of Section 2, $n = 2^{25}$.)

This is the rigorous form of "each deficient window costs at least $d + 2 - u$ conditions" when windows overlap: the true cost is larger, the proof extracts at least one condition a window, and that is all the rung needs. It answers the lead's warning (3): no disjoint subfamily is taken. The requirement $d \approx 2u + 3$ at rate 1/2 is above the target $d = 6$ to 8. For $u = 3$ and a graph with constant in-degree $d$ ($\Delta = d + 1$) a Potts-type count over relation fields, in which a point shared by two classes costs 2, lowers the requirement to $\gamma \le (d-1)/(2d - 1)$, that is $d \ge 7$ **[derived by the same method, not written out; treat as a sketch]**.

### 5.2 Low degree needs nothing

**Lemma 5.3 [proved].** There are at most $q^{k - m + u(m + 1)}$ tuples $g\,a$ with $a$ of degree $m$, so their cost is at least $(u - 1)(k - m) - u$; the loss from deficiency-1 windows at fully covered positions is at most $\kappa = k + \varepsilon_2 n$. Hence for $m \le \frac{u - 2}{u - 1}k - \frac{\varepsilon_2 n + u}{u-1}$ ($m \le k/2$ for quadruples, $2k/3$ for quintuples) these windows cost more than they lose, whatever their structure.

### 5.3 Windows of rank one (for $u = 3$: deficiency 2)

On such a window the curve $\gamma = [a]$ itself is constant. The clusters (connected sets of rank-one windows) have pairwise disjoint closures $Y_C$, each inside one fibre of $\gamma$, so $|Y_C| \le m$.

**Proposition 5.4 [proved].** Assume (W2) with $\gamma(\rho) \le \frac12 - \frac1{d+1}$ and $d + 1 \ge 2(u - 1)$. Then the rank-one windows $J^{(1)}$ at fully covered positions have loss minus cost at most $(u - 1)\varepsilon_2 n + 2u$.

*Proof.* The loss is $(u-1)|J^{(1)}| \le (u - 1)\min(\kappa, \gamma|Y|)$, $Y = Y(J^{(1)})$, by (W2) on each closure. The conditions are $a(y) \parallel w_C$ on $Y_C$: a lattice of index $(u-1)|Y|$. (i) Balanced: $q^{u(m+1) - (u-1)|Y| + (u-1)p}$ tuples, cost $(u-1)\sum_C(|Y_C| - 1) \ge (u - 1)|J^{(1)}|$ since $|Y_C| \ge |C|/\gamma \ge |C| + 1$. (ii) One short vector: $a$ is determined by the $w_C$, and $p \le |Y|/(d+1)$; if $|Y| \ge 2m + 1$, already by the $w_C$ of at most $\lceil (2m+1)/(d+1) \rceil$ clusters, because two primitive vectors of degree at most $m$ that are proportional at more than $2m$ points are proportional (their $2 \times 2$ minors have degree at most $2m$). Cost at least $(u-1)k + m(1 - \frac{2(u-1)}{d+1}) - 2u$. (iii) $s \ge 2$ short vectors of degrees $e_1 \le e_2 \le \dots$: any two are proportional at every point of $Y$, so $e_1 + e_2 \ge |Y|$ (else they are proportional), the solution space has dimension at most $s(m + 1 - |Y|/2)$, and the cost is at least $k + (u-2)(k-m) - (u - 1) + (u-1)|Y|(\frac12 - \frac1{d+1})$, against a loss of at most $(u - 1)\gamma|Y|$. $\square$

So the windows of deficiency 2 of a quadruple are easier than those of deficiency 1, as for pencils: the object that is constant on the window is the map $\gamma$ itself, whose fibres partition $D$. Clusters have a cheap description (their closures are disjoint), so no entropy beyond $2^n$ is paid.

### 5.4 Unbalanced lattices with $u - 1$ short vectors: the cross product

**Lemma 5.5 [proved].** Let $b_1, \dots, b_{u-1} \in M(\lambda)$ be independent over $K(X)$, $\nu$ their generalized cross product (the vector of signed maximal minors), $\nu = h\,\nu^\circ$ with $\nu^\circ$ primitive of degree $m^\circ \le \sum \deg b_i - \deg h$. Then: (a) $\nu^\circ \cdot b_i \equiv 0$; (b) for $x \in J$ and $y \in W_x$ with $h(y) \ne 0$: $[\nu^\circ(y)] = \lambda_x$; (c) if $\nu^\circ$ is constant, every combination of the $b_i$ lies in a fixed hyperplane (a dependent tuple); (d) otherwise the sets $F_\lambda = \{y \in D : [\nu^\circ(y)] = \lambda\}$ are pairwise disjoint with at most $m^\circ$ points, and $|Y_C| \le m^\circ + \deg h \le \sum\deg b_i$ for every class; (e) the tuples of degree at most $m$ orthogonal to $\nu^\circ$ number at most $q^{(u-1)(m+1) - \min(m^\circ, m+1)}$; (f) $\nu^\circ$ is determined by its values on more than $2m^\circ$ points.

*Proof.* (a) Cramer. (b) All $b_i(y)$ are orthogonal to $\lambda_x$, and they are independent iff $\nu(y) \ne 0$. (c), (d): a linear form vanishing at $\lambda$ and not identically on $\nu^\circ$ has at most $m^\circ$ zeros; $h$ has at most $\deg h$ zeros. (e) The syzygies of a primitive vector form a saturated lattice of rank $u - 1$ whose minimal degrees sum to $m^\circ$. (f) as in 5.3. $\square$

**Consequence [proved].** In the stratum with exactly $u - 1$ short vectors the deficient windows lie in the interiors of the fibres of $\nu^\circ$ up to the zeros of $h$, and the number of tuples $g\,a$ is at most $q^{\,k - m + (u-1)(m + 1) - m^\circ + (u-1)p_0}$ (the $u - 1$ short vectors are independent syzygies of degree at most $m$, so all minimal syzygy degrees are at most $m$ and (e) holds with $m^\circ$ itself), where $p_0$ is the number of classes needed to cover more than $2m^\circ$ points outside $Z(h)$ ($p_0 = p$ if there are not that many). If every class has at least $2(u-1)$ points outside $Z(h)$ and together they cover more than $2m^\circ$ such points, then $(u-1)p_0 \le m^\circ + u$, the cost is at least $k + (u - 2)(k - m) - 2u$, and loss minus cost is at most $\varepsilon_2 n + 2u$.

This is the lead's argument, with one correction and one caveat. **Correction:** cap the loss by the pair bound $\kappa$, not by (W2) on the fibres. "$\gamma n \le k$" needs $\gamma \le \rho$, which costs a large $d$ at low rates; $\kappa$ costs nothing and holds for every window shape. **Caveat:** $h$ vanishes exactly where the short vectors are dependent, and every point that lies in two classes with different relations is such a point (there $s_y \ge 2$, so all short vectors are proportional to the one admissible value). With heavily overlapping windows and many classes most points of $Y$ are of this kind, $\nu^\circ$ is prescribed on few points, and the count degenerates to $q^{k + (u-2)m + (u-1)p + O(u)}$, small enough only for few classes. So this stratum is closed when the classes are separated (no point in two classes) and it has otherwise the same open part as the rigid stratum of 5.5. In note 66's picture of almost disjoint windows this caveat is invisible; in a $d$-out graph every point lies in about $d + 1$ windows, and a dense $J$ is nothing like disjoint.

### 5.5 The rigid stratum for $u = 3$: what closes, what does not

$a$ is *rigid* for $J$ if it is, up to a scalar, the only tuple of degree at most $m$ with its relation field (one short vector, $e_2 > m$). The loss is $|J| \le \kappa$ and the family $\{g\,a\}$ has $N = k - m + \log_q\#\{a\}$; the rung needs $N + |J| \le 3k + \varepsilon n$, that is $\log_q \#\{a\} \le 2k + m - |J|$.

**Proposition 5.6 [proved].** The rigid stratum satisfies loss minus cost $\le O(1) + \varepsilon_2$-terms in each of the following cases.

1. $m \le k/2 - \varepsilon_2 n/2 - 2$ (Lemma 5.3).
2. $|Y(J)| \le m + 1$ (Corollary 5.2).
3. $|J| \le (2k + m - 1)/3$: a rigid tuple is determined by its relation field, so $\#\{a\} \le q^{2|J| + 1}$, with no entropy beyond the choice of $J$.
4. More generally, $a$ is determined by the relation lines of a subfamily $J_0 \subseteq J$ with $2|J_0| + |J| \le 2k + m - 1$. Example: $J_0$ covers at least $2m + 1$ points twice, with two different lines at each of them (there the value $[a(y)]$ is the intersection of the two lines, and $2m + 1$ values determine $a$).

In general only $\#\{a\} \le q^{\min(3m + 3,\ 2|J| + 1)}$ is available, which gives loss minus cost at most $\min(2m - k,\ k - m) + 3\varepsilon_2 n + 3 \le k/3 + 3\varepsilon_2 n$, attained at $m = 2k/3$, $|J| = \kappa$.

**The open region.** Affinely independent quadruples with primitive degree $k/2 < m < k$ whose fully covered positions contain more than $(2k + m)/3$ windows of rank exactly 2, not confined to $m + 1$ points, with no small determining subfamily. Equivalently: is $\dim\{a \in K[X]^3_{\le m} : a \text{ deficient on } J\} \le 2k + m - |J| + \varepsilon n$ for every $J$ with $(2k + m)/3 < |J| \le \kappa$? The transversal value of the left side is $3m + 3 - (d - 1)|J|$, negative by a wide margin, so the question is whether the conditions of $|J| \approx k$ windows on $3m$ coefficients can be dependent enough to leave a family of dimension above $2k + m - |J|$ (about $k + m$).

**Why the lemma the lead asks for is false, and why that does not matter [proved].** "A rank-3 tuple has at most $\theta n$ non-free deficient windows" cannot follow from (W1) to (W3). Take four parts of $n/4$ points, let each $x$ choose one other part at random and its $d$ partners at random in the union of the two: a union of two parts has interior fraction $1/3 + O(2^{-d})$, so (W2) holds with a $\gamma$ of the size of a random graph's at $d = 8$ (0.37) on these sets **[proved for unions of parts; estimate for other sets]**. If the parts are four fibres of a function $\varphi$ and $a = c \circ \varphi$ with $c$ a conic through the four points of $\mathbb{P}^2$ where three of the four members coincide (the leave-one-out quadruple of Section 7), every window is mapped to two points of the conic, so **every** window has rank at most 2. Nevertheless $H_4$ holds for this quadruple with room: the family is thin ($N = O(1)$), so by Proposition 1.2 with $\lambda = t - 1$ only its free sum matters, and that is about $n = 2k$ (each window lies in two parts, where exactly two members coincide). So deficient windows by themselves are harmless; what the rung needs is a count of tuples, and for tuples that are determined by few parameters the count is trivial. The open region is exactly where the tuple is determined by its relation field but the relation field has too many parameters to be counted naively.

**Other rigid families I checked [proved].** (i) $a = (1, X, L(X))$ with $L$ additive on a subspace domain: a line $\alpha + \beta s + L(s) = 0$ meets $a(D)$ in a coset of $U_\beta = \ker(L + \beta)\cap D$, the sets $U_\beta \setminus 0$ partition $D \setminus 0$, and a window is deficient iff all its differences lie in one $U_\beta$. The family has $\log_2 m + 1$ parameters: thin, harmless. (ii) Composed maps $a = c \circ \varphi$: thin unless $\varphi$ has few constraints, and then transversal. (iii) Class-structured tuples (a few combinations $f_C \in V$ vanishing on closures $Y_C$): cost $\sum_C (|Y_C| - 2)$ against a loss of at most $\gamma\sum_C|Y_C|$. None of them reaches the open region.

### 5.6 General $u$, wildcards, and the statement that would close everything

**Wildcards [proved for the extreme case].** A window with at most $u - 1$ points outside $Z(g)$ is deficient for free; there are at most $\gamma'_{u-1}|Z(g)|$ of them (W2$_{u-1}$) and $g$ pays $|Z(g)|$, so they close iff $\gamma'_{u-1} \le 1$, the constant of Lemma 5.1. Windows with fewer wildcards are deficient windows of the sub-windows $W_x \setminus Z(g)$ and all the counts above apply with smaller windows; I did not redo the constants.

**Intermediate ranks ($u \ge 4$, windows of rank $2, \dots, u - 2$) [open].** The window image lies in a flat of dimension between 1 and $u - 3$. Only rank one gives a partition of $D$ (5.3); for the others the situation is that of 5.5.

**Fewer than $u - 1$ short vectors [open; no induction found].** With $s \le u - 2$ short vectors the tuple satisfies $u - s \ge 2$ independent polynomial relations, but no map of bounded degree that is constant on the deficient windows comes out of them: completing the short vectors by long ones gives cross products of degree above $m$. Projection from a point of $\mathbb{P}^{u-1}$ lowers the rank by one and keeps deficient exactly the windows whose relation hyperplane contains the point, so an induction on the rank works when many relation hyperplanes are concurrent (few classes) and not otherwise. Induction on the degree through the common factor closes formally (a tuple $g\,a$ is counted through $a$) but each level adds $u$ to the excess and the depth is not bounded. So for general $u$ the proved part is: Lemma 5.1, Lemma 5.3, Proposition 5.4, Lemma 5.5, and the analogue of Proposition 5.6(3): a rigid tuple is determined by its relation field, $\#\{a\} \le q^{(u-1)|J| + 1}$.

**The statement to prove [conjectured].** *(CS$'_u$) For the window graph in use, every $m < k$ and every set $J$ of at most $\kappa$ windows: the number of primitive $a \in K[X]^u$ of degree $m$, not in a hyperplane, with rank at most $u - 1$ on every window of $J$, is at most $q^{\,(u-1)k + m - |J| + \varepsilon n}$.* With the common factor this is $N + |J| \le uk + \varepsilon n$, i.e. loss at most cost for the new circuits of rung $u + 1$. Lemma 5.1 proves it when $J$ fits in $m + 1$ points, Lemma 5.3 when $m \le \frac{u-2}{u-1}k$, Proposition 5.6 for rigid tuples with $|J| \le (2k + m)/3$ ($u = 3$).

**A route [sketch].** For a non-degenerate tuple the values $w_y = [a(y)]$ and lines $\lambda_x$ form a configuration of points and lines with incidences given by the window graph. Two mechanisms bound the number of tuples, and both are properties of the graph and of $J$ alone. *Flexible:* on a revealed set of $m + 1$ points the values are free and the incidences cost at least $|U| - \alpha_{u-1}$ (Lemma 5.1), up to $(u-1)|U|$ when points lie on several distinct lines. *Rigid:* once the lines of a seed of windows are fixed, a point on two fixed lines is determined, and a window with two determined points of different values has its line determined; if this threshold-2 bootstrap percolation from a seed of $\sigma$ windows determines $2m + 1$ values, then $\#\{a\} \le 2^n q^{2\sigma}$. (CS$'_3$) follows if for every $J$ one of the two mechanisms applies with the right constants, which is a statement about a random $d$-out graph and $2^{O(n)}$ combinatorial objects, so a first moment over the graph is available for it. A first moment over the graph against the tuples themselves is not: for a fixed tuple a window is deficient with probability about $\rho^{d-1}$, that is $d - 1$ bits a window, against 64 bits a coefficient, so it would need $d$ of order 100.

## 6. Conclusions for $H_4$, $H_5$ and the general rung: part (C)

**6.1 Assembly.** A tuple can carry several kinds of deficiency at once. The tool for adding their costs is the chain rule: **[proved]** given $P_0, \dots, P_{j-1}$, the sets, and the set $F$ of positions of $S_j$ at which $P_j$ adds nothing to the rank, the admissible $P_j$ form an affine space with direction $\{Q : Q|_{W_x} \in R^{<j}_x\ \forall x \in F\}$, where $R^{<j}_x$ is the span of the differences of the earlier members covering $x$; the total loss is $\sum_j |F_j|$. Each count of Section 5 can be read as a count of the last member given the others, with one reservation that I did not resolve in general: a bound that is uniform in the earlier members loses the credit for what the earlier members paid (zeros of an earlier difference on the windows of $F$ let the last member vary freely there), so the wildcard accounting of 5.6 has to be carried through the chain. **Status of the assembly: sketch.**

**6.2 Rung 4.**

**Theorem 6.1 [proved stratum by stratum; assembly as in 6.1; the pencil lemma of rung 3 is researcher 62's].** Assume (W1), (W2) with $\gamma(\rho) \le \min(\tfrac13, \tfrac12 - \tfrac1{d+1})$, $\gamma'_2(\rho) \le 1$, $d \ge 3$. Then with probability $1 - 2^{-126}$ over $\mu$ every four members of every list satisfy $\sum_x (c_x - 1)_+ \le 3k + \varepsilon_4 n$ with $\varepsilon_4 = \tfrac{7}{64} + \tfrac32\varepsilon_3^{\mathrm{exc}} + 2\varepsilon_2 + o(1)$ (the sum is the safe form; with a careful assembly it should be the maximum), **except possibly** for affinely independent quadruples in the open region of 5.5. Here $7/64$ is the entropy of Proposition 3.2, $\varepsilon_3^{\mathrm{exc}}$ the excess of rung 3 (Corollary 1.3), $2\varepsilon_2$ the rank-one windows (Proposition 5.4). Contributions: free and mixed free/paid (Proposition 3.2, needs $\gamma \le 1/2$); dependent quadruples (Corollary 1.3); rank-one windows (Proposition 5.4); rank-two windows in the transversal range (Corollary 5.2, needs $\gamma \le 1/3$), for $m \le k/2$ (Lemma 5.3), with two short vectors and separated classes (Lemma 5.5), rigid with $|J| \le (2k + m)/3$ (Proposition 5.6).

For a random $d$-out graph the hypotheses hold at rate 1/2 from $d = 9$ ($\gamma = 0.323$, $\gamma'_2 = 0.93$), at rate 1/4 from $d = 7$. **$H_4$ itself is not proved**: without the exception the best I can state is an excess of about $\rho/3$, which puts the threshold at Johnson's.

**6.3 Rung 5 and beyond.** The same strata with $u = 4$: free and mixed ($\gamma \le 2/5$), dependent quintuples (reduce to rungs 3 and 4 with factors 2 and 4/3), rank-one windows ($\gamma \le \tfrac12 - \tfrac1{d+1}$, $d \ge 5$), rank-three windows in the transversal range ($\gamma \le 1/4$, $d \ge 12$ at rate 1/2, 9 at rate 1/4), low degree $m \le 2k/3$, three short vectors with separated classes, rigid with $(u-1)|J| + |J| \le 3k + m$, i.e. $|J| \le (3k + m)/4$. **Open for $u = 4$:** the rigid and overlapping strata as for $u = 3$, and in addition windows of rank two (image on a line of $\mathbb{P}^3$), for which I have only Lemma 5.1 applied to the rank condition "at most 2" (the same proof gives exponent $u|U| - 2(|U| - \alpha_2)$) and the low-degree bound.

What each rung needs from the graph in the proved parts, at rate 1/2:

| rung $t$ | pure free (3.1) | free and paid (3.2): $\gamma \le 2/t$ | transversal range (5.1): $\gamma \le 1/(t-1)$ | least $d$, random graph |
| --- | --- | --- | --- | --- |
| 4 | 0.706 | 0.500 | 0.333 | 9 |
| 5 | 0.645 | 0.400 | 0.250 | 12 |
| 6 | 0.637 | 0.333 | 0.200 | 14 |
| 8 | 0.607 | 0.250 | 0.143 | 19 |
| 16 | 0.567 | 0.125 | 0.067 | 36 |

(**[checked, first-moment $\gamma(d, \tfrac12)$ of Section 2]**; the column $2/t$ alone needs $d = 6, 8, 9, 12, 21$; at rate 1/4 the last column is 7, 9, 10, 14, 27.)

The free part alone needs $d = 6$ at every rung. The growth of $d$ with $t$ in the other columns is a weakness of the proofs (the trivial count over relation fields, and the step $R(\pi) \le \sum_e |T_e|$), not of the code as far as I can see: the true cost of a deficient window is $d + 2 - u$ conditions and a sharp transversal count should need only $d \ge u + O(1)$ and $\gamma \le 1/2$. Proving that sharp count for overlapping windows is the same incidence-counting problem as (CS$'_u$).

**6.4 The general induction statement.** $H_{<t}$ implies $H_t$ if: (i) (CS$'_{t-1}$) of 5.6 for the new circuits; (ii) its analogues for windows of rank $2, \dots, t - 3$; (iii) the assembly of 6.1. The lower rungs enter in two places only: the pair bound caps every loss at fully covered positions by $\kappa$, and dependent tuples are thin families whose excess is that of a lower rung times $(t-1)/v$ (Corollary 1.3). The lead's mechanism "a position where a sub-tuple is locally dependent is an agreement of that sub-tuple, counted at its rung" is Lemma 1.1(c) and it is correct, but it does not cap the loss by itself: the first moment of the sub-tuple bounds its paid rank, not the number of its deficient windows (5.5). **Status: (i) open for every $u \ge 3$ in the rigid overlapping regime; (ii) open; (iii) sketch.**

## 7. Local and stride windows: the negative result, for the record

Found independently before the erratum of note 57 (Section 10) reached me; the families are of use as test cases for any window design.

**7.1 The obstruction [proved].** For members $P_i$ and any $\mu$, the word that takes at each position the symbol shared by the largest free class has $\sum_x (c_x - 1)_+ \ge F(P)$. So $H_t$ implies the deterministic inequality $F(P) \le (t-1)k + \varepsilon_t n$ for all tuples. If all windows lie in cosets of a subspace $U$ (or of any set of blocks on which some $\varphi$ is constant), then for $P_i = g\,Q_i(L_U)$ every coincidence set is a union of blocks and equals its interior, so $F$ is the plain Reed-Solomon value on the quotient.

**7.2 Families with free sum above $(t-1)k$ in plain Reed-Solomon on a subspace domain [proved; the second is checked by `63_toy.py planted`].**

- *Hadamard tuples* (rate 1/2): $P_\ell = v\,\ell(X)/X$ for $\mathbb{F}_2$-linear functionals $\ell$ with a common value $v$; for $t$ independent functionals the free sum is $n(\mathbb{E}\max(W, t - W) - 1)$, $W \sim \mathrm{Bin}(t, \tfrac12)$: excess over $(t-1)k$ of $0.25, 0.25, 0.4375, 0.4375, 0.594, 0.594$ times $n$ for $t = 3, \dots, 8$, growing like $\sqrt{t/2\pi}$.
- *Spine times a transversal pattern on a small quotient* (every rate): $P_i = g\,Q_i(L_G)$ with $|D/G| = n'$, $Q_i$ of degree at most $k' - 1$ satisfying $(t-1)k' - 1$ coincidence conditions on the quotient (a nonzero solution always exists; the pattern must be chosen so that the members are distinct and every condition enlarges a free class, as in the two cases below), $g$ of degree $k - 1 - (k'-1)|G|$ vanishing on other cosets. Free sum $(t-1)(k - 1) + (t - 2)|G|$: **excess $(t-2)/n'$**, because a polynomial in $L_G$ of degree $k' - 1$ has degree $(k'-1)|G|$, not $k'|G|$: each block returns one field element a member. Smallest cases: $t = 3$, lines on $n' = 4$ points, excess $1/4$ (this is the Hadamard triple); $t = 4$, the *leave-one-out quadruple* on $n' = 8$: $Q_i$ the quadratic through three of four prescribed points, so that at each of four cosets three members coincide, free sum $1.75n - O(N)$ against $3k = 1.5n$. In the language of 1.2 it is a conic composed with $L_G$, passing through the four triple points of the braid arrangement.

Checked: $N = 5, 6, 7$, GF($2^8$), rate exactly 1/2, degrees 15, 31, 63: with the local window (the $N - 3$ directions of $G$) free sum 47, 100, 209 and best-word sum 47, 100 to 103, 209 to 213 over five $\mu$, against $3k = 48, 96, 192$ (violated from $N = 6$); with the cube window free sum 0 and best-word sum 0 to 5; with random $d$-out windows ($d = 5, 6, 6$) free sum 0, 1, 3 and best-word sum at most 9.

**7.3 Consequences.** With local windows the excess is at least $1/4$ at rungs 3 and 4 at rate 1/2 and at least the Hadamard values above; rung 3 is then no better than Johnson, and in any case the ladder with local windows is the ladder of plain Reed-Solomon on the quotient, the open problem of notes 34 to 56. For stride windows the same families survive with the interior fraction of coordinate-periodic sets (note 57, Section 10, item 4, and note 60, Section 2). Any window design must be tested against these two families at every scale of quotient; a random $d$-out graph passes because a coset union of density $\varphi$ keeps a fraction about $\varphi^d$ of its windows.

## 8. Toy experiments for quadruples

Scripts: `scripts/63_lib.py` (fields GF($2^m$), $m \le 16$, linear algebra), `scripts/63_toy.py`, outputs `scripts/63_toy_output.txt`, `scripts/63_gamma_output.txt`.

**8.1 Planted structured quadruples** (7.2): see the numbers there. Types (i) common zeros and (iv) periodic families are the leave-one-out quadruple with its spine; with spanning windows nothing of it survives.

**8.2 Adaptive search with random $d$-out windows, one sampled $\mu$ [checked].** A cover pattern with $3k - 1$ units is imposed (each unit one linear condition on $(d_1, d_2, d_3) \in K^{3k}$), the kernel vector is taken and the quadruple is scored with its best word. This is the generic way to reach $3k - 1$ and it measures what comes on top.

| $q$ | $N$ | $k$ | $d$ | $3k$ | valid trials | score min, mean, max |
| --- | --- | --- | --- | --- | --- | --- |
| $2^8$ | 4 | 8 | 4 | 24 | 76 | 23, 23.09, 24 |
| $2^8$ | 5 | 16 | 5 | 48 | 95 | 47, 47.24, 49 |
| $2^8$ | 5 | 8 | 5 | 24 | 161 | 23, 23.37, 26 |
| $2^{16}$ | 5 | 16 | 5 | 48 | 47 | 47, 47.00, 47 |
| $2^{16}$ | 6 | 32 | 6 | 96 | 30 | 95, 95.00, 95 |

So the score is $3k - 1$ plus the $1/q$ term (up to $+3$ at $q = 2^8$, $+0$ at $q = 2^{16}$), as the first moment predicts; no structure appears at this size. Trials whose kernel vector had two equal members are discarded (they are lower rungs). This does not probe the open region of 5.5, which needs $n$ large against $d$ and a search over rigid tuples; I have no experiment for it.

**8.3 Lemma 5.1 by brute force [checked].** Seven systems (4 to 6 windows of 3 to 5 points on 5 to 9 points, $u = 2, 3$, $q = 2, 4$): $\log_q$ of the number of deficient assignments is 9.89, 15.12, 17.45, 7.16, 8.28, 10.82, 16.97 against exponents $u|U| - (|U| - \alpha)$ of 10, 15, 18, 7, 9, 12, 17; the bound with its pattern factor holds in all seven, and without the factor it is exceeded by at most $q^{0.16}$.

## 9. What I did not do

- I did not prove $H_4$ or $H_5$: the rigid overlapping stratum (5.5, 5.6) is open, and so is the lead's stratum with $u - 1$ short vectors when windows overlap (5.4). I found neither a proof of (CS$'_3$) nor a counterexample; the families I can construct are thin.
- The assembly of several deficiency types in one tuple (6.1) and the wildcard constants for windows with a few zeros of $g$ (5.6) are sketches. The Potts-type count that would lower $d$ from 9 to 7 at rung 4 is not written out.
- The pencil lemma of rung 3 is used as proved by researcher 62; Corollary 1.3 and Theorem 6.1 inherit its hypotheses and its excess.
- The constants $\gamma$, $\gamma'_j$ are first-moment values for a random $d$-out graph (a union bound over sets, $n = 2^{25}$); I did not verify (W3) or measure them on a sampled graph. The planted graph of 5.5 is analysed only on unions of parts.
- No experiment probes the open region: at toy size ($n \le 128$) windows of $d + 1$ points and tuples of degree near $k$ leave no room for it. The toy runs confirm the generic value $3k - 1$ and the free sums of the planted families, nothing more.
- Nothing here is formalized.
