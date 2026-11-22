# 62. The first rung of the ladder for window-mixed Reed-Solomon codes: what is proved, and where the sketch of note 57 section 9 fails (researcher 62, round 13)

Labels: **[proved]** a complete proof is in this note; **[checked]** verified numerically by a script of `scripts/62_*` (named each time); **[conditional]** proved from a named hypothesis; **[conjectured]** neither. Summary and answers to the brief are in section 0 (written last).

## 0. Summary

**The headline.** The first rung as sketched in note 57 section 9 is **false for local windows** and for every XOR window set that does not span the domain: there are explicit triples, for every $\mu$, with $u_2 n + 2u_3 n = 2k + m - 2$, $m$ any power of two with $2^{t'} \le m \le \min(n/4, k - 1)$ (Proposition N; checked at $n = 64$). The sketch fails at the words "up to zero-deficient positions". Following the lead's two notes sent during the work (note 57 section 10, note 66), the theorem is written for an **axiomatic window system** with expansion (W2): every set $Z$ of at most $\varphi_0 n$ points contains at most $\gamma|Z| + a_0$ whole windows. In that setting the pairs, the free part, the collinear triples, the exact count of configurations and the whole transversal range are **proved**; the non-transversal range is reduced to one counting statement (Hypothesis L) that I **did not prove**. So the first rung is at present a conditional theorem, with every other ingredient proved and its constants exact.

| | statement | status |
| --- | --- | --- |
| Theorem E (section 2) | random $d$-out graph: (W2) holds with failure $\le 2^{-129}$ and $\gamma(1/2) = 0.50, 0.37, 0.29$, $\gamma(1/4) = 0.35, 0.26, 0.20$ for $d = 6, 8, 10$ ($N = 20$ to 28; table for $N \ge 10$, $d = 4$ to 12) | proved, numbers checked |
| Theorem A (section 3) | pairs: two codewords agree on at most $k + e_2 - 1$ positions, $e_2/n = 0.0238, 0.0173, 0.0111, 0.0068$ for any window containing its centre, and $0.0156, 0.0130, 0.0089, 0.0056$ under (W2) with $\gamma \le 1/2$ (rates 1/2 to 1/16) | proved |
| Proposition N (section 4) | window-invariant polynomials: lists of plain Reed-Solomon on the quotient lift; periodic triples of weight $2k + m - 2$; with interior fraction $\iota$ the lift is harmless only for $\alpha \ge \iota\sqrt\rho$ and the three-wise inequality needs $\iota \le 2/3$ | proved, checked |
| Lemmas 5.1 to 5.3 | collinear triples have weight at most $2A_2$; first moment over the $\le 5^n$ cover patterns; free positions carry weight at most $3\gamma k + 3a_0$ | proved |
| Lemma 5.4, Proposition T | exact count $q^{(k'-e_1)_+ + (k'-e_2)_+}$ of the pairs satisfying a configuration; the sum over all transversal configurations with closure at most $\varphi_0 n$ is at most $q^{2k + 2a_0}(1 + q^{-(1-2\gamma)})^n$; complete at rates $\le 1/4$ when $\gamma(2\rho) < 1/2$ | proved, checked at toy size |
| Lemma 6.1 | non-transversal configurations: one pencil class, cost at least $k + e_1 + |Y_2|$, determined by its directions at $2e_1 + 1$ points, support inside interiors of fibres | proved |
| Hypothesis L (section 6) | the non-transversal configurations (and at rate 1/2 the transversal ones with closure above $\varphi_0 n$) contribute at most as much as the transversal ones | **not proved**; plan and obstacles in section 6 |
| Theorem H$_3$ (section 6) | under (W2) with $\gamma < 1/2$ and L: every triple has $u_2 n + 2u_3 n \le 2k + E_3$, and lists are at most $M_0 = \max(1/(1-\alpha), 3(\alpha + \alpha^2 - \Theta/n)/\mathcal{A})$ above $\alpha^2(3-\alpha) = (2k + E_3)/n$ | conditional on L |

**Constants of Theorem H$_3$** ($q = 2^{64}$, $N = 20$ to 28, $\gamma \le 0.40$; conditional on L):

| rate | $\varepsilon_2$ | $\varepsilon_3 = E_3/n$ | threshold $\alpha^*$ | queries | Johnson | $M_0$ at $\alpha^* + 0.01$ | least $d$ for the proved part |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | 0.0156 | 0.0363 | 0.6664 | 185 | 0.7071, 217 | 10 | 7 (Proposition T incomplete at this rate) |
| 1/4 | 0.0130 | 0.0299 | 0.4564 | 96 | 0.5000, 108 | 21 | 7 |
| 1/8 | 0.0089 | 0.0201 | 0.3173 | 66 | 0.3536, 73 | 30 | 5 |
| 1/16 | 0.0056 | 0.0125 | 0.2225 | 50 | 0.2500, 54 | 37 | 4 |

If L costs $0.02n$ more: 190, 98, 68, 53 queries. For local windows $t' = 6$ to 10: no theorem at all (only Theorem A(i)). For the cube: Theorem A with the sharp constant at every rate, the free part at rates $\le 1/4$, Proposition T at rate 1/16 only.

**Gaps.** (1) Hypothesis L: the count of non-transversal configurations with its entropy (support, common zeros, windows with one point outside the common zero set), and at rate 1/2 the transversal configurations with closure above $\varphi_0 n$; it probably needs a second expansion axiom for near-interior windows and small $\gamma$ (section 6). (2) Theorem E is for independent partner sets ($\Delta \approx 70$ to 90); a permutation design ($\Delta = d + 1$) is not covered. (3) No sampling experiment for the largest weight over all triples (section 8). (4) The tightness remark after Theorem A (codewords with $k + nH/64$ zeros exist) is not proved.

## 1. Window systems, the code, and the exact probability

**Setting.** $K$ is a finite field of characteristic 2 with $q$ elements, $D \subset K$ a set of $n$ points (in the application an $\mathbb{F}_2$-subspace with basis $b_0, \dots, b_{N-1}$, $n = 2^N$, $q = 2^{64}$), $1 \le k < n$, $\rho = k/n$, $K[X]_{<k}$ the polynomials of degree below $k$. A **window system** assigns to every $x \in D$ a window $W_x = \{x, \pi_1(x), \dots, \pi_d(x)\} \subseteq D$. For $T, Z \subseteq D$ write $N[T] = \bigcup_{x \in T} W_x$ (closure), $\partial T = N[T] \setminus T$, and $\mathrm{int}\,Z = \{x : W_x \subseteq Z\}$ (interior). Since $x \in W_x$: $T \subseteq \mathrm{int}\,N[T]$ and $\mathrm{int}\,Z \subseteq Z$. The axioms (note 66):

- **(W1)** every window has $r = d + 1$ distinct points;
- **(W2)** with parameters $(\varphi_0, \gamma, a_0)$: every $Z$ with $|Z| \le \varphi_0 n$ has $|\mathrm{int}\,Z| \le \gamma|Z| + a_0$ (the additive $a_0$ is needed for very small sets at failure probability $2^{-128}$, see section 2; $a_0 = 0$ for the cube);
- **(W3)** every point lies in at most $\Delta$ windows.

Examples: XOR windows $W_x = x + C$ for a set $C \ni 0$ of $r$ offsets in a subspace $D$ (the cube: $C = \{0, b_0, \dots, b_{N-1}\}$; local windows: $C = \{0, b_0, \dots, b_{t'-1}\}$); the random $d$-out graph of section 2.

**The code.** $\mu : D \times \{0, \dots, d\} \to K$, with $\pi_0(x) = x$, and $c_\mu(P)(x) = \sum_{l=0}^{d} \mu_l(x)\,P(\pi_l(x)) = \langle \mu_x, P|_{W_x}\rangle$, where $P|_{W_x} = (P(\pi_l(x)))_{l} \in K^{r}$. Two models: **model U**, all $\mu_l(x)$ uniform and independent (note 57); **model 1**, $\mu_0(x) = 1$ and the $\mu_l(x)$, $l \ge 1$, uniform and independent (note 66). $c_\mu$ is $K$-linear. For $d_* \in K[X]_{<k}$ let $Z(d_*) = \{x \in D : d_*(x) = 0\}$, $Z_\mu(d_*) = \{x : c_\mu(d_*)(x) = 0\}$, and $T(d_*) = \mathrm{int}\,Z(d_*)$, the **free zeros** of $d_*$.

**Lemma 1.1 (probability of a pattern). [proved]** Let $P_0, \dots, P_L$ be polynomials and $S_0, \dots, S_L \subseteq D$. For $x \in D$ let $I_x = \{i : x \in S_i\}$ and $R_x = \mathrm{span}_K\{(P_i - P_{i'})|_{W_x} : i, i' \in I_x\} \subseteq K^{r}$. The event "there is a word $w : D \to K$ with $c_\mu(P_i)(x) = w(x)$ for all $i$ and all $x \in S_i$" has probability exactly $q^{-\sum_x \dim R_x}$ in model U, and in model 1 either that or 0 (it is 0 exactly when some $R_x$ contains a vector supported on the centre coordinate alone).

*Proof.* A word exists iff for every $x$ the values $c_\mu(P_i)(x)$, $i \in I_x$, coincide, that is $\langle \mu_x, v\rangle = 0$ for all $v \in R_x$. The vectors $\mu_x$ are independent over $x$. Model U: $\mu_x$ is uniform in $K^r$ and the annihilator of $R_x$ has codimension $\dim R_x$. Model 1: $\mu_x = (1, \mu')$ with $\mu'$ uniform in $K^d$; the conditions $v_0 + \langle \mu', v'\rangle = 0$, $v \in R_x$, form an affine system of rank $\dim R_x'$ ($R_x'$ the projection of $R_x$ to the last $d$ coordinates); it is consistent iff the projection is injective on $R_x$, and then its solution set has codimension $\dim R_x$. $\square$

So in both models the probability is **at most** $q^{-\sum_x \dim R_x}$, a position with $R_x = 0$ is free (probability 1), and every first moment below holds in both models.

**Lemma 1.2 (zeros of one mixed codeword). [proved]** For fixed $d_* \ne 0$: $T(d_*) \subseteq Z_\mu(d_*)$ for every $\mu$, and the events $x \in Z_\mu(d_*)$, $x \notin T(d_*)$, are independent, each of probability $1/q$ (model U) or at most $1/q$ (model 1). *Proof.* Lemma 1.1 with $P_0 = 0$, $P_1 = d_*$, one position at a time. $\square$

**Lemma 1.3 (MDS count). [proved]** For $Y \subseteq D$ the polynomials of degree below $k$ vanishing on $Y$ form a space of dimension $(k - |Y|)_+$. Hence for $T \subseteq D$: $\#\{d_* \in K[X]_{<k} : T(d_*) \supseteq T\} = q^{(k - |N[T]|)_+}$. *Proof.* They are the multiples of $\prod_{y \in Y}(X - y)$ of degree below $k$; and $T(d_*) \supseteq T$ means that $d_*$ vanishes on $N[T]$. $\square$

**Lemma 1.4 (closures expand). [proved]** Under (W2), every $T$ with $|N[T]| \le \varphi_0 n$ has $|T| \le \gamma|N[T]| + a_0$; in particular the free zeros of a nonzero $d_*$ of degree below $k \le \varphi_0 n$ number at most $\gamma(k - 1) + a_0$. *Proof.* $T \subseteq \mathrm{int}\,N[T]$; and $|Z(d_*)| \le k - 1$. $\square$

## 2. The expansion lemma for the random $d$-out graph

**Model.** For every $x$ the partner set $\{\pi_1(x), \dots, \pi_d(x)\}$ is a uniformly random $d$-subset of $D \setminus \{x\}$, independently over $x$ (derived from the oracle; (W1) holds by construction).

**Theorem E (expansion). [proved; the numbers are checked, `62_expansion.py`]** Let $p_z = \binom{z-1}{d}/\binom{n-1}{d} \le (z/n)^d$. For every $\varphi_0 \le 1$, $\gamma$ and integer $a_0 \ge 0$, the probability over the graph that (W2) fails with parameters $(\varphi_0, \gamma, a_0)$ is at most
$$\mathrm{fail}(\varphi_0, \gamma, a_0) = \sum_{z = d+1}^{\lfloor \varphi_0 n\rfloor} \binom nz \Pr\bigl[\mathrm{Bin}(z, p_z) \ge \lfloor \gamma z + a_0\rfloor + 1\bigr] .$$
*Proof.* Fix $Z$ with $|Z| = z$. A point of $\mathrm{int}\,Z$ lies in $Z$, and $x \in Z$ is interior iff its $d$ partners fall in $Z \setminus \{x\}$: probability $p_z$, independently over $x$. So $|\mathrm{int}\,Z|$ is binomial with parameters $(z, p_z)$; sets with $z \le d$ have empty interior by (W1); sum over the $\binom nz$ sets. $\square$

As $n \to \infty$ the least admissible $\gamma$ tends to the root $\gamma_\infty(d, \varphi)$ of $D(\gamma \,\|\, \varphi^d) = H(\varphi)/\varphi$ (bits; the entropy of choosing $Z$ against the large deviation of its interior), increasing in $\varphi$. Least $\gamma$ with $\mathrm{fail} \le 2^{-129}$ (upper bounds, valid as stated; block-wise evaluation of the sum, tails by Chernoff and by the union over $g$-subsets):

| $\gamma$ at $\varphi_0 =$ | 1/16 | 1/8 | 1/4 | 1/2 | 3/4 | $\Delta$ of (W3) |
| --- | --- | --- | --- | --- | --- | --- |
| $d = 4$, $n \to \infty$ | 0.398 | 0.445 | 0.530 | 0.710 | 0.900 | |
| $d = 6$, $n \to \infty$ | 0.259 | 0.290 | 0.348 | 0.498 | 0.738 | |
| $d = 8$, $n \to \infty$ | 0.191 | 0.212 | 0.254 | 0.368 | 0.600 | |
| $d = 10$, $n \to \infty$ | 0.150 | 0.167 | 0.198 | 0.286 | 0.491 | |
| $d = 12$, $n \to \infty$ | 0.124 | 0.137 | 0.162 | 0.232 | 0.408 | |
| $d = 6$, $N = 25$ ($a_0 = 0$ / $a_0 = 16$) | 0.286 / 0.262 | 0.292 | 0.351 | 0.501 | 0.744 | 71 |
| $d = 8$, $N = 25$ | 0.192 | 0.214 | 0.256 | 0.371 | 0.604 | 80 |
| $d = 10$, $N = 25$ | 0.151 | 0.168 | 0.200 | 0.288 | 0.495 | 89 |
| $d = 6$, $N = 28$ | 0.286 / 0.261 | 0.292 | 0.351 | 0.500 | 0.744 | 72 |
| $d = 8$, $N = 28$ | 0.192 | 0.214 | 0.256 | 0.370 | 0.605 | 81 |
| $d = 10$, $N = 28$ | 0.151 | 0.168 | 0.200 | 0.288 | 0.496 | 90 |
| $d = 6$, $N = 16$ ($a_0 = 0$ / 16) | 0.333 / 0.258 | 0.333 / 0.291 | 0.352 | 0.503 | 0.748 | 69 |
| $d = 8$, $N = 16$ | 0.231 / 0.189 | 0.231 / 0.212 | 0.256 | 0.372 | 0.609 | 78 |
| $d = 6$, $N = 10$ ($a_0 = 0$ / 16) | 0.500 / 0.080 | 0.500 / 0.213 | 0.500 / 0.324 | 0.539 / 0.507 | 0.785 / 0.764 | 66 |
| $d = 8$, $N = 10$ | 0.333 / 0.000 | 0.333 / 0.125 | 0.333 / 0.221 | 0.399 / 0.368 | 0.646 / 0.625 | 74 |
| $d = 10$, $N = 10$ | 0.250 / 0.000 | 0.250 / 0.070 | 0.250 / 0.158 | 0.312 / 0.281 | 0.534 / 0.513 | 82 |

(Full table, $N \in \{10, 16, 20, 25, 28\}$, $d \in \{4, 6, 8, 10, 12\}$: `62_expansion_output.txt`.) Remarks. (i) The lead's estimates (0.5, 0.35, 0.22 at $d = 6, 8, 12$ for sets of density 1/2) are confirmed: 0.50, 0.37, 0.23. (ii) At $2^{-128}$ the purely multiplicative form fails for very small sets when $n$ is small (a few windows nested in each other have probability about $n^{-(d-2)j}$, not $2^{-128}$): with $a_0 = 0$ the constant at $N = 10$ is set by sets of a dozen points; an additive $a_0 = 16$ restores the asymptotic value. From $N = 20$ on $a_0 = 0$ costs nothing at densities $\ge 1/4$. (iii) (W3): with independent partner sets the in-degree is binomial of mean $d$, and $\Delta$ is 60 to 100 at $2^{-128}$ (least $j$ with $n\binom{n-1}{j}(d/(n-1))^j \le 2^{-129}$); a design in which every $\pi_l$ is a permutation has $\Delta = d + 1$ but is not covered by Theorem E as proved here (the interior events are then negatively correlated, which should only help; not checked). Nothing proved below uses $\Delta$. (iv) Sets of density above 1/2 expand badly ($\gamma(3/4) = 0.60$ at $d = 8$): this is what limits the transversal count at rate 1/2 (section 6).

## 3. Pairs: the distance of the mixed code

**Theorem A (pairs). [proved]** Let the window system satisfy $x \in W_x$ (nothing else), and let $\mu$ be drawn in model U or model 1. For an integer $e \ge 0$ put $a = k + e$. The probability that some nonzero $d_* \in K[X]_{<k}$ has $|Z_\mu(d_*)| \ge a$ is at most
$$\frac{q}{q-1}\; q^{-e-1} \sum_{T :\ |N[T]| \le k-1} q^{-|\partial T|}\binom{n - |T|}{a - |T|} .$$
Consequently, with $e_2$ the least $e$ such that $q^{e+1} \ge 2^{130}\binom{n}{k+e}\,\Xi$, where

- (i) for any window system, $\Xi = \sum_{j \le k-1}\binom{k+e}{j}$ $(\le 2^{k+e})$;
- (ii) under (W2) with $\varphi_0 \ge \rho$ and $\gamma \le 1/2$, $\Xi = (4a_0 + 1)\binom{k+e}{4a_0} + 2$ (so $\Xi = 3$ if $a_0 = 0$), for $k + e \le 2^{31}$,

we have, with probability at least $1 - 2^{-129}$ over $\mu$: **every two distinct codewords of the mixed code agree on at most $A_2 := k + e_2 - 1$ positions.** Call this event $G_2$.

*Proof.* $Z_\mu(d_*)$ depends only on the class of $d_*$ up to scalars. Fix $d_* \ne 0$ and $T = T(d_*)$; then $N[T] \subseteq Z(d_*)$, so $|T| \le |N[T]| \le k - 1 < a$. If $|Z_\mu(d_*)| \ge a$ there is $A' \subseteq Z_\mu(d_*) \setminus T$ with $|A'| = a - |T|$, and for a fixed such $A'$ the probability is at most $q^{-(a - |T|)}$ (Lemma 1.2). The number of classes with $T(d_*) \supseteq T$ is $(q^{k - |N[T]|} - 1)/(q - 1) \le \frac{q}{q-1}q^{k - |N[T]| - 1}$ (Lemma 1.3). Summing over $T$ and $A'$ gives the display, since $k - |N[T]| - 1 - (a - |T|) = -e - 1 - |\partial T|$. For (i) bound $q^{-|\partial T|} \le 1$ and use $\binom nj\binom{n-j}{a-j} = \binom na\binom aj$. For (ii): $N[T]$ has at most $k - 1 \le \varphi_0 n$ points, so $|T| \le \gamma|N[T]| + a_0$ (Lemma 1.4) and $|\partial T| \ge (|T| - a_0)/\gamma - |T| \ge |T| - 2a_0$, which is at least $|T|/2$ for $|T| \ge 4a_0$; so the sum is at most $\binom na\bigl[\sum_{j < 4a_0}\binom aj + \sum_j \binom aj q^{-j/2}\bigr] \le \binom na\bigl[4a_0\binom a{4a_0} + (1 + 2^{-32})^a\bigr]$. Finally $\frac q{q-1}2^{-130} \le 2^{-129}$. $\square$

**Constants [exact, `62_constants.py pairs`], $q = 2^{64}$.** $e_2/n$:

| | rate 1/2 | 1/4 | 1/8 | 1/16 |
| --- | --- | --- | --- | --- |
| (i) any window, $N = 20$ to 28 | 0.02378 | 0.01726 | 0.01109 | 0.00676 |
| (ii) under (W2), $N = 20$ to 28, $a_0 = 0$ or 16 | 0.01561 | 0.01299 | 0.00887 | 0.00561 |
| (i), $N = 10$ ($e_2 = 26, 19, 13, 8$) | 0.02539 | 0.01855 | 0.01270 | 0.00781 |
| (ii), $N = 10$, $a_0 = 0$ / $a_0 = 16$ | 0.0166 / 0.0215 | 0.0146 / 0.0176 | 0.0107 / 0.0127 | 0.0068 / 0.0078 |
| (ii), $N = 16$, $a_0 = 16$ | 0.01579 | 0.01315 | 0.00903 | 0.00575 |

So $\varepsilon_2 = (H(a/n) + a/n)/64$ in general (the lead's $(n + z)/64$) and $\varepsilon_2 = H(a/n)/64$ for an expanding window system: the free zeros then cost more than they give ($q^{-|\partial T|}$), and only the entropy of the agreement set is left.

**Remarks.** (1) The bound is of the right order and cannot be removed: the mixed code is a linear code of length $n$ and dimension $k$ over $K$ that is not MDS, and the expected number of pairs ($d_*$ up to scalars, set of $k + e$ zeros) is $\binom n{k+e}q^{-e-1}(1 + o(1))$ in model U, which is large for $e < nH/64 - 1$. So codewords with about $k + nH(\rho)/64$ zeros should be expected to exist **[conjectured: second moment not done]**, and every statement about triples must tolerate $2\varepsilon_2$ (section 5.1). (2) For every $\mu$ there are codewords with $k - 1$ zeros at prescribed positions (linear algebra). (3) Theorem A(i) holds for local windows too; it is the only part of note 57 section 9 that survives for them.

## 4. The negative fact: windows with a window-invariant polynomial (local and non-spanning XOR windows)

**Proposition N. [proved; (c) checked, `62_toy.py lift`]** Let $\ell$ be a polynomial of degree $m \ge 1$ that is constant on every window $W_x$ (a *window invariant*). For XOR windows $x + C$ with $W = \mathrm{span}_{\mathbb{F}_2}(C) \ne D$, every subspace polynomial $\ell = L_{W''}$, $W \subseteq W'' \subsetneq D$ a subspace, is one, with $m = |W''|$ (local windows of parameter $t'$: every $W'' \supseteq U_{t'}$, so $m = 2^j$ for every $t' \le j < N$). Then, for **every** $\mu$ (both models):

- (a) $c_\mu(g \cdot Q(\ell)) = Q(\ell) \cdot c_\mu(g)$ pointwise, for all polynomials $g$, $Q$.
- (b) (lists lift) Let $\nu = c_\mu(1)$ and $D' = \ell(D)$ (for $\ell = L_{W''}$: a subspace of $n/m$ points). For every word $w' : D' \to K$ and every $Q$ of degree below $k' = \lfloor (k-1)/m\rfloor + 1$ agreeing with $w'$ on a set $A' \subseteq D'$, the codeword $c_\mu(Q(\ell))$ agrees with the word $w = \nu \cdot (w' \circ \ell)$ on $\ell^{-1}(A')$. So every list of the plain Reed-Solomon code of degree below $k'$ on $D'$ at agreement $\alpha|D'|$ gives a list of the same size of the mixed code at agreement $\alpha n$ (for $\ell = L_{W''}$; the rate is $k'/|D'| \approx \rho$), and no position of it is paid for by $\mu$.
- (c) (the three-wise inequality fails) Let $\ell = L_{W''}$ with $m = |W''| \le n/4$, $m \le k - 1$, $k \le n - 2m + 1$. There are three affinely independent polynomials of degree below $k$ and a word with $u_2 n + 2u_3 n \ge 2k + m - 2$.

*Proof.* (a) $\ell(\pi_l(x)) = \ell(x)$, so $c_\mu(gQ(\ell))(x) = \sum_l \mu_l(x)g(\pi_l(x))Q(\ell(x))$. (b) is (a) with $g = 1$. (c) $\ell$ takes at least four values on $D$; let $0, c_1, c_2$ be three of them, with fibres $Q_0, Q_1, Q_2$ (cosets of $W''$, $m$ points each), and $t = c_2/(c_1 + c_2)$. The space of $g$ of degree below $k - m$ has dimension $k - m$, so there is $g \ne 0$ with $c_\mu(g) = 0$ on a prescribed set $S$ of $k - m - 1$ positions outside $Q_0 \cup Q_1 \cup Q_2$. Put $P_0 = 0$, $P_1 = g\ell$, $P_2 = t\,g(\ell + c_1)$; then $P_1 + P_2 = (1 + t)\,g(\ell + c_2)$, the degrees are below $k$, and $P_1, P_2$ are linearly independent. By (a), $c_\mu(P_1) = \ell\,c_\mu(g)$ and $c_\mu(P_2) = t(\ell + c_1)c_\mu(g)$. So: on $Q_0$, $c_\mu(P_0) = c_\mu(P_1) = 0$; on $Q_1$, $c_\mu(P_0) = c_\mu(P_2) = 0$; on $Q_2$, $c_\mu(P_1) = c_\mu(P_2)$; on $S$ all three vanish. The word equal to 0 outside $Q_2$ and to $c_\mu(P_1)$ on $Q_2$ gives $u_2 n + 2u_3 n \ge 3m + 2(k - m - 1)$. $\square$

**[checked]** At $n = 64$, $k = 32$, $K = \mathrm{GF}(2^8)$, local windows $t' = 2, 3$, $m = 4, 8, 16$, both models, random $\mu$: the triple has $u_2 n = 3m$, $u_3 n = k - m - 1$, weight exactly $2k + m - 2$ (66, 70, 78 against $2k = 64$). With the cube window the same triple has weight 0.

**Consequences.** (1) For local windows and every XOR window set that does not span $D$, statement (b) of the brief is false with any $\varepsilon_3 < m/n$, $m$ the largest admissible power of two: $\varepsilon_3 \ge 1/4 - 2/n$ at rate 1/2 and $\varepsilon_3 \ge \rho/2 - 2/n$ at rates 1/4 and below. With $\varepsilon_3 = \rho/2$ the three-wise threshold $\alpha^2(3 - \alpha) > 2.5\rho$ is 0.744 at rate 1/2, above the Johnson radius 0.707: nothing is left. (2) By (b), a list bound for the mixed code at agreement $\alpha$ implies the same bound for plain Reed-Solomon on the quotient domains $L_{W''}(D)$ of dimensions $1$ to $N - t'$, at the same rate and agreement: for a local window, statement (c) of the brief is the original open problem at dimension $N - t'$. (3) Windows of two or three points: an XOR window set of $r$ points spans at most $r - 1$ dimensions, so it spans $D$ only if $r \ge N + 1$; windows of 2 or 3 XOR offsets are local windows with $t' = 1, 2$ and fail by (c). (The reason given in note 57 section 9, "both positions of a pair share one window", is a second, weaker defect: a closed cluster, worth one field element per block; the periodic triples are worth $m$.) (4) Section 9 of note 57 fails exactly at the words "up to zero-deficient positions": on the three fibres the pair differences vanish on whole windows, these positions have rank 0 and are covered twice, and they are not triple covered, so $|J_3| \le u_3 n \le k + \varepsilon_2 n$ does not bound them.

**What an interior fraction $\iota$ gives. [proved]** Suppose instead that $\ell$ is constant on $W_x$ only for $x$ in a set $I_\ell$ (the positions whose window stays in the fibre of $\ell$), and that every fibre $F$ of $\ell$ has $|F \cap I_\ell| \ge \iota|F|$ (stride windows: $\iota = \mathrm{stay}$ of note 60, Proposition 2.1; a window system with (W2): $\iota \le \gamma$ for fibres of at most $\varphi_0 n$ points, up to $a_0$). Then (a) holds at the positions of $I_\ell$, and the same constructions give: (b$'$) a plain Reed-Solomon list on $D'$ at agreement $\alpha'$ lifts to a list of the mixed code at agreement at least $\iota\alpha' n$; so the mixed code can have a list bound at agreement $\alpha$ that plain Reed-Solomon is not known to have only if $\alpha/\iota$ is at or above the radius where the quotient code is under control (today the Johnson radius): **$\alpha \ge \iota\sqrt\rho$ is the region where the lift is harmless**, and for a rung with threshold $\alpha_t$ the window must have $\iota \le \alpha_t/\sqrt\rho$ on periodic sets (0.92 for $t = 3$ at rate 1/2, $\sqrt\rho$ at capacity). (c$'$) Choosing $S$ inside $I_\ell$ (possible if $\iota(n - 3m) \ge k - m - 1$) the triple has weight at least $3\iota m + 2(k - m - 1) = 2k + (3\iota - 2)m - 2$: **the three-wise inequality survives the periodic triples iff $\iota \le 2/3 + \varepsilon_3 n/(3m)$**, the "lose a third to the boundary" criterion of note 57 section 10, here as a necessary condition with its constant.

## 5. Triples: reductions, the free part, and the first moment

Throughout, a *triple* is three distinct polynomials $P_0, P_1, P_2$ of degree below $k$, a word $w$, and sets $S_i \subseteq \{x : c_\mu(P_i)(x) = w(x)\}$; $c_x = |\{i : x \in S_i\}|$, $U_3 = \{c_x = 3\}$, $U_2 = \{c_x = 2\} = U_2^{01} \sqcup U_2^{02} \sqcup U_2^{12}$ (by the pair covering $x$), $U = U_2 \cup U_3$. The **weight** is $\mathrm{wt} = \sum_x (c_x - 1)_+ = |U_2| + 2|U_3| = \sum_{i<j}|S_i \cap S_j| - |S_0 \cap S_1 \cap S_2|$. The statement to prove is $H_3(\Theta)$: every triple has $\mathrm{wt} \le \Theta$, with $\Theta = 2k + E_3$. The *pattern* of the triple is $\pi = (U_2^{01}, U_2^{02}, U_2^{12}, U_3)$.

### 5.1 Collinear triples

**Lemma 5.1. [proved]** On $G_2$, a triple with $P_2$ on the line through $P_0, P_1$ has $\mathrm{wt} \le 2A_2 = 2k + 2e_2 - 2$. *Proof.* $P_2 - P_0 = \lambda(P_1 - P_0)$ with $\lambda \ne 0, 1$, so all three differences are nonzero multiples of $d_* = P_1 - P_0$ and every $S_i \cap S_j$ lies in $Z_\mu(d_*)$, which has at most $A_2$ points. So $U \subseteq Z_\mu(d_*)$ and $\mathrm{wt} \le 2|U| \le 2A_2$. $\square$ This is attained up to the constant of Theorem A: the three codewords $c_\mu(P_0)$, $c_\mu(P_0 + d_*)$, $c_\mu(P_0 + \lambda d_*)$ agree simultaneously on all of $Z_\mu(d_*)$. So $E_3 \ge 2(\text{true pair excess})$ is forced: collinear triples need $2\varepsilon_2$, not $\varepsilon_2$ (the bound of note 57 section 9 happens to cover it, because its entropy term exceeds $\varepsilon_2$).

### 5.2 Affinely independent triples: patterns, ranks, the first moment

Let $d_1 = P_1 - P_0$, $d_2 = P_2 - P_0$ be linearly independent, and $d_{01} = d_1$, $d_{02} = d_2$, $d_{12} = d_1 + d_2$ (characteristic 2). Let $B = B(d) = Z(d_1) \cap Z(d_2)$ (in $D$). In Lemma 1.1: at $x \in U_2^{ij}$, $R_x$ is spanned by $d_{ij}|_{W_x}$, of dimension 1, or 0 if $x \in T(d_{ij})$; at $x \in U_3$, $R_x = \mathrm{span}(d_1|_{W_x}, d_2|_{W_x})$ has dimension $2 - \Delta_x$ with $\Delta_x = \Delta_x(d) = \dim\{(\alpha, \beta) \in K^2 : (\alpha d_1 + \beta d_2)|_{W_x} = 0\} \in \{0, 1, 2\}$; $\Delta_x = 2$ iff $x \in \mathrm{int}\,B$. Define
$$\mathrm{loss}(d, \pi) = \sum_{x \in U_3}\Delta_x(d) + \sum_{i<j}\bigl|U_2^{ij} \cap T(d_{ij})\bigr| .$$

**Lemma 5.2 (first moment for triples). [proved]** Let $\Pi(\Theta)$ be the set of patterns (four pairwise disjoint subsets of $D$) with $\mathrm{wt} = \Theta + 1$ and $|U_3| + |U_2^{ij}| \le A_2$ for all three pairs. Then
$$\Pr\bigl[G_2 \text{ and some affinely independent triple has } \mathrm{wt} > \Theta\bigr] \ \le\ \frac{q^{-(\Theta+1)}}{q - 1}\sum_{\pi \in \Pi(\Theta)}\ \sum_{d}\ q^{\mathrm{loss}(d, \pi)} ,$$
the inner sum over linearly independent pairs $d = (d_1, d_2) \in (K[X]_{<k})^2$.

*Proof.* Removing a position from one of the sets $S_i$ lowers the weight by 0 or 1, so a triple of weight above $\Theta$ contains one of weight exactly $\Theta + 1$ with the same polynomials and word. On $G_2$ its pattern has $|S_i \cap S_j| = |U_3| + |U_2^{ij}| \le A_2$. The existence of a word for given sets depends only on $(d_1, d_2)$ (Lemma 1.1 involves differences only) and is unchanged when $(d_1, d_2)$ is multiplied by a common nonzero scalar; its probability is at most $q^{-\sum_x \dim R_x} = q^{-\mathrm{wt}(\pi) + \mathrm{loss}(d, \pi)}$. Union bound over the patterns and the classes of pairs. $\square$

So $H_3(\Theta)$ for affinely independent triples follows, with failure probability at most $2^{-130}$, from: **for every $\pi \in \Pi(\Theta)$, $\ \sum_d q^{\mathrm{loss}(d,\pi)} \le q^{\Theta + 2}\,2^{-131}/|\Pi(\Theta)|$.** With no loss at all the left side is $q^{2k}$: the theorem is a statement about how often pencils are deficient.

### 5.3 The free part

**Lemma 5.3 (free positions). [proved]** Assume (W2) with $\varphi_0 \ge \rho$. For every pencil and every pattern, the positions of rank 0 (the free pair agreements $U_2^{ij} \cap T(d_{ij})$ and the free triple agreements $U_3 \cap \mathrm{int}\,B$) carry weight at most $\sum_{i<j}|T(d_{ij})| \le 3\gamma(k - 1) + 3a_0$; and $|\mathrm{int}\,B| \le \gamma|B| + a_0$.

*Proof.* $T(d_{ij}) = \mathrm{int}\,Z(d_{ij})$ with $|Z(d_{ij})| \le k - 1 \le \varphi_0 n$, and $\mathrm{int}\,B$ lies in all three sets $T(d_{ij})$, so a free triple position, of weight 2, is counted three times. $\square$

So with $\gamma < 2/3$ no triple violates $H_3$ by free agreements alone; by Proposition N(c$'$) the constant $2/3$ is sharp for window systems that have window-invariant polynomials on interiors. Note 60 has $\gamma = 0.69, 0.55, 0.47, 0.40$ for the cube at $N = 25$ and rates 1/2 to 1/16; the random $d$-out graph has $\gamma \le 0.50$ at every rate from $d = 6$ on (section 2).

### 5.4 Expanding the loss: configurations and their exact count

Fix a pattern $\pi$. A **configuration** is a family $\sigma = (\sigma_x)_{x \in D}$, $\sigma_x \in K^2$, with $\sigma_x$ arbitrary for $x \in U_3$, $\sigma_x \in K\epsilon_{ij}$ for $x \in U_2^{ij}$ ($\epsilon_{01} = (1,0)$, $\epsilon_{02} = (0,1)$, $\epsilon_{12} = (1,1)$) and $\sigma_x = 0$ outside $U$. A pair $d$ *satisfies* $\sigma$ if $(\sigma_{x,1}d_1 + \sigma_{x,2}d_2)|_{W_x} = 0$ for every $x$. By the definitions of $\Delta_x$ and $T(d_{ij})$, $q^{\mathrm{loss}(d,\pi)}$ is the number of configurations satisfied by $d$, so
$$\sum_d q^{\mathrm{loss}(d,\pi)} = \sum_\sigma \mathcal{N}(\sigma), \qquad \mathcal{N}(\sigma) = \#\{d \text{ linearly independent, satisfying } \sigma\} \le \mathcal{N}_{\mathrm{all}}(\sigma) := \#\{d \in (K[X]_{<k})^2 \text{ satisfying } \sigma\}. \tag{5.1}$$
For a configuration let $T = \{x : \sigma_x \ne 0\}$ (support), and for $y \in N[T]$ let $\Lambda_y = \mathrm{span}\{\sigma_x : x \in T,\ y \in W_x\} \subseteq K^2$. The conditions are: $\lambda \cdot (d_1(y), d_2(y)) = 0$ for all $y$ and $\lambda \in \Lambda_y$. Call $y$ of type 1 if $\dim\Lambda_y = 1$ (one linear condition at $y$) and of type 2 if $\Lambda_y = K^2$ (both $d_i$ vanish at $y$); $Y_1, Y_2$ the sets of such points, $N[T] = Y_1 \sqcup Y_2$, and $\mathrm{cost}(\sigma) = |Y_1| + 2|Y_2| \ge |N[T]|$. The *direction* of $x \in T$ is the class of $\sigma_x$ in $\mathbb{P}^1(K)$; a type-1 point sees one direction, a type-2 point at least two.

**Lemma 5.4 (exact count). [proved; checked, `62_toy2.py lattice`]** Let $k' = k - |Y_2|$. There are integers $0 \le e_1 \le e_2$ with $e_1 + e_2 = |Y_1|$, depending on $\sigma$ only, such that
$$\mathcal{N}_{\mathrm{all}}(\sigma) = q^{(k' - e_1)_+ + (k' - e_2)_+} .$$
If $e_2 \le k'$ (call $\sigma$ **transversal**) this is $q^{2k - \mathrm{cost}(\sigma)}$: the conditions are independent. This is the case whenever $|N[T]| \le k$. If $e_2 > k'$ (**non-transversal**) there is $v \in K[X]^2$ of degree $e_1$ such that the solutions are exactly the pairs $\Lambda_{Y_2} f\,v$ with $\deg f < k' - e_1$, where $\Lambda_{Y_2} = \prod_{y \in Y_2}(X - y)$.

*Proof.* A pair satisfies the type-2 conditions iff $d = \Lambda_{Y_2}d'$ with $d' \in (K[X]_{<k'})^2$, and then the type-1 conditions for $d$ and $d'$ coincide. Let $M \subseteq K[X]^2$ be the $K[X]$-module of all pairs satisfying the type-1 conditions (degree unrestricted); it contains $\Lambda_{Y_1}K[X]^2$. Let $v_1 \in M \setminus 0$ have minimal degree $e_1$ (degree of a pair: the larger of the two), and $v_2 \in M \setminus K(X)v_1$ minimal degree $e_2 \ge e_1$. (1) If $v \in M \cap K(X)v_1$ then $v \in K[X]v_1$: write $v = (f/h)v_1$ in lowest terms, $uf + wh = 1$; then $v_1/h = uv + wv_1 \in M$, so $\deg h = 0$ by minimality of $e_1$. (2) The leading coefficient vectors of $v_1, v_2$ are linearly independent over $K$: otherwise $v_2 - cX^{e_2 - e_1}v_1$ would be an element of $M \setminus K(X)v_1$ of smaller degree. (3) Hence $\deg(f_1v_1 + f_2v_2) = \max(\deg f_1 + e_1, \deg f_2 + e_2)$, and every $v \in M$ is such a combination: by induction on $\deg v$; if $v \in K(X)v_1$ use (1), otherwise $\deg v \ge e_2$, and subtracting the multiples $\alpha X^{\deg v - e_1}v_1 + \beta X^{\deg v - e_2}v_2$ that cancel the leading vector lowers the degree. So $\#\{v \in M : \deg v < j\} = q^{(j - e_1)_+ + (j - e_2)_+}$ for all $j$. (4) For $j \ge |Y_1|$ the type-1 conditions are independent on $(K[X]_{<j})^2$ (evaluation at $|Y_1| \le j$ points is onto), so $2j - e_1 - e_2 = 2j - |Y_1|$. Take $j = k'$. If $e_2 > k'$ only the multiples $fv_1$ remain. If $|N[T]| \le k$ the evaluation of $d \in (K[X]_{<k})^2$ at the points of $N[T]$ is onto $(K^2)^{N[T]}$, so the count is $q^{2k - \mathrm{cost}}$, which forces $e_2 \le k'$. $\square$

### 5.5 Transversal configurations

**Proposition T (transversal sum). [proved]** Assume (W2) with parameters $(\varphi_0, \gamma, a_0)$, $\gamma < 1/2$. For every pattern,
$$\sum_{\sigma \text{ transversal},\ |N[T]| \le \varphi_0 n} \mathcal{N}_{\mathrm{all}}(\sigma) \ \le\ q^{2k + 2a_0}\,\bigl(1 + q^{-(1 - 2\gamma)}\bigr)^{|U|},$$
and for $a_0 = 0$ the factor is $(1 + q^{-(1-2\gamma)/\gamma})^{|U|}$. Every transversal $\sigma$ has $|N[T]| \le \mathrm{cost}(\sigma) \le 2k$, so **if $\varphi_0 \ge 2\rho$ the sum is over all transversal configurations.**

*Proof.* There are fewer than $q^{2|T|}$ configurations with support $T$, each with $\mathcal{N}_{\mathrm{all}} = q^{2k - \mathrm{cost}} \le q^{2k - |N[T]|}$, and $|T| \le \gamma|N[T]| + a_0$ (Lemma 1.4) gives $2|T| - |N[T]| \le 2a_0 - (1 - 2\gamma)|N[T]| \le 2a_0 - (1 - 2\gamma)|T|$ (for $a_0 = 0$: $\le -(1/\gamma - 2)|T|$). Sum over $T \subseteq U$. A transversal count $q^{2k - \mathrm{cost}}$ is at least 1, so $\mathrm{cost} \le 2k$. $\square$

With $q = 2^{64}$: for $\gamma \le 0.40$ the factor is below $(1 + 2^{-32})^n \le 1.07$ ($a_0 = 0$); for $\gamma = 0.45$ it is $2^{0.01n}$ at most. So in the transversal range a pencil-deficient window never pays: a loss of at most 2 per window against at least $1/\gamma > 2$ conditions per window on average. This is the rigorous form of "Case A" of note 57 section 9, and it needs no cluster analysis and no (W3). What it does need is expansion up to density $2\rho$: **at rates 1/4 and below, $\gamma(2\rho) < 1/2$ holds for the random graph with $d \ge 7$ (rate 1/4), $d \ge 5$ (rate 1/8), $d \ge 4$ (rate 1/16), and for the cube only at rate 1/16 ($\gamma(1/8) = 0.47$, note 60). At rate 1/2 no window system has it** ($2\rho = 1$), and the transversal configurations whose closure exceeds $\varphi_0 n$ have to be treated with the non-transversal ones (section 6).

## 6. Non-transversal and large configurations: what is proved, and the statement that is not

**Lemma 6.1 (structure of non-transversal configurations). [proved]** Let $\sigma$ be non-transversal with $\mathcal{N}(\sigma) > 0$, and $v = (a, b)$, $e_1$, $k'$ as in Lemma 5.4. Then:

1. $e_1 < k'$, the polynomials $a, b$ are linearly independent over $K$, and $\mathcal{N}(\sigma) \le q^{k - |Y_2| - e_1}$: against $q^{2k}$ pairs, **the cost is at least $k + e_1 + |Y_2|$**, whatever the number of conditions.
2. Every direction has at most $e_1$ type-1 points: if $\Lambda_y = K\lambda$ for $y$ in a set $A$, the nonzero polynomial $\lambda_1 a + \lambda_2 b$ of degree at most $e_1$ vanishes on $A$.
3. $|Y_1| \ge e_1 + k' + 1 \ge 2e_1 + 2$, and $v$ is determined up to a factor in $K(X)^*$ by the directions at any $2e_1 + 1$ type-1 points: if $v' = (a', b') \ne 0$ of degree at most $e_1$ satisfies the same conditions there, then $ab' - a'b$, of degree at most $2e_1$, vanishes at these points (at each of them $v(y)$ and $v'(y)$ are both orthogonal to $\lambda_y$, hence proportional), so $ab' = a'b$.
4. Write $v = c_0\,(a^\circ, b^\circ)$ with $a^\circ, b^\circ$ coprime of degree $m^\circ \ge 1$, $\xi = a^\circ/b^\circ$, and $B_0 = Y_2 \cup (Z(c_0) \cap Y_1)$, so $|B_0| \le |Y_2| + e_1 - m^\circ$. For every $x \in T$ whose window is not inside $B_0$, $\xi$ is constant on $W_x \setminus B_0$, equal to the direction of $x$: the support lies in $\mathrm{int}\,B_0 \cup \bigcup_t \mathrm{int}(B_0 \cup F_t)$, $F_t$ the fibres of $\xi$ on $D \setminus B_0$, of at most $m^\circ$ points each.

*Proof.* 1: the solutions are $\Lambda_{Y_2}fv$; a linearly independent one needs $f \ne 0$ and $a, b$ independent. 2, 3: as stated, with $e_2 = |Y_1| - e_1 > k' > e_1$. 4: at a type-1 point $y \notin Z(c_0)$ of $W_x$ the condition reads $\lambda_x \cdot (a^\circ(y), b^\circ(y)) = 0$. $\square$

This is the correct core of "Case B" of note 57 section 9: the pencil is one object, its cost is $k$ plus its degree, and the directions are not free. Let $\mathcal{S}_L(\pi) = \sum \mathcal{N}(\sigma)$ over the configurations of $\pi$ that are non-transversal or have $|N[T]| > \varphi_0 n$ (the second kind exists only if $\varphi_0 < 2\rho$).

**Hypothesis L($\Theta$). [not proved]** For every $\pi \in \Pi(\Theta)$: $\ \mathcal{S}_L(\pi) \le q^{\Theta + 2}\,2^{-132}/|\Pi(\Theta)|$.

**Theorem H$_3$ (the first rung). [conditional on L; everything else proved]** Let the window system satisfy (W1) and (W2) with parameters $(\varphi_0, \gamma, a_0)$, $\varphi_0 \ge \rho$, $\gamma < 1/2$, and let $\mu$ be drawn in model U or model 1. Let $e_2$, $A_2$ be as in Theorem A(ii), $E_3$ the least integer $E \ge 2e_2 - 2$ with $q^{E + 2} \ge 2^{132}\,|\Pi(2k + E)|\,q^{2a_0}(1 + q^{-(1-2\gamma)})^n$ (write $E_T$ for the least $E \ge 0$ with this property, so $E_3 = \max(2e_2 - 2, E_T)$ when the inequality is monotone in $E$, as it is in all the cases computed), and $\Theta = 2k + E_3$. If L($\Theta$) holds, then with probability at least $1 - 2^{-128}$ over $\mu$: (a) any two distinct codewords agree on at most $A_2 = k + e_2 - 1$ positions; (b) every triple has $u_2 n + 2u_3 n \le \Theta$; (c) for every $\alpha$ with $\mathcal{A} := \alpha^2(3 - \alpha) - \Theta/n > 0$, every word has at most $M_0 = \max\bigl(1/(1 - \alpha),\ 3(\alpha + \alpha^2 - \Theta/n)/\mathcal{A}\bigr)$ codewords at agreement $\alpha n$.

*Proof.* (a) is Theorem A (failure $2^{-129}$). (b): collinear triples by Lemma 5.1 on $G_2$; affinely independent ones by Lemma 5.2, with $\sum_d q^{\mathrm{loss}} = \sum_\sigma \mathcal{N}(\sigma)$ (5.1) split into the transversal configurations with $|N[T]| \le \varphi_0 n$ (Proposition T: at most $q^{2k + 2a_0}(1 + q^{-(1-2\gamma)})^n \le q^{\Theta + 2}2^{-132}/|\Pi|$ by the choice of $E_3$) and $\mathcal{S}_L$; failure at most $2^{-130}$. (c): trim the agreement sets to $\lceil\alpha n\rceil$ positions; their triples still satisfy (b), which is the hypothesis $p_{ij} + p_{il} + p_{jl} - t_{ijl} \le c$ of note 44 Lemma 5.2 (`PeriodDescent.threewise_johnson`) with $c = \Theta$, $n_e = n$, $\varrho = \Theta/2n$. $\square$

**Why L is open, exactly.** For a non-transversal $\sigma$ the count is small ($k + e_1 + |Y_2|$ against a loss $|T|$), but three things have to be controlled together, and I did not complete the argument:

1. *The loss.* $|T \cap U_3| \le |U_3| \le A_2 - \max_{ij}|U_2^{ij}|$ (this is the legitimate use of the pair bound in note 57), and the double-covered part of the support lies in the three *named* directions $\epsilon_{ij}$; by Lemma 6.1(4) and (W2) it has at most $\gamma(|A_{ij}| + |B_0|) + a_0$ points in direction $\epsilon_{ij}$, $A_{ij}$ its type-1 points. With gain $= \mathrm{wt} - \mathrm{loss}$ and $\mathrm{wt} = 2|U_3| + |U_2|$, the requirement gain $+$ cost $\ge 2k +$ entropy becomes, after eliminating $|U_3|$: $\ E_3 + 1 \ge 2\,(\text{entropy}) + \sum_{ij}\varsigma_{ij} - 2\,(\text{cost} - k)$, $\varsigma_{ij}$ the named double-covered support. Note the factor 2 on the entropy: a non-transversal pencil with all its triple positions deficient behaves like a pair (gain 1 for weight 2), exactly as the collinear triples do.
2. *The number of configurations behind one pencil class.* By Lemma 6.1(3) the directions on components (sets of windows chained through type-1 points) covering $2m^\circ + 1$ points outside $B_0$ determine $\xi$, hence all other directions. If the named components are taken first (their directions are known) and the others have at least 2 points outside $B_0$, at most $(2m^\circ + 1 - \sum|A_{ij}|)_+/2 + 1$ free directions are needed, the cost stays at least $k + |B_0| + \sum|A_{ij}|/2 - 3/2$, and item 1 closes with $\sum\varsigma_{ij} \le \gamma\sum|A_{ij}| + 3\gamma|B_0|$ as soon as $\gamma \le 2/3$: **$E_3 + 1 \ge 2\,(\text{entropy}) + 3$.** Not controlled: (i) windows with exactly one point outside $B_0$ (deficient automatically, each a component with one point): they need a bound $|\{x : |W_x \setminus Z| \le 1\}| \le \gamma_1|Z|$, a second expansion axiom (it follows from (W3) with $\gamma_1 = \Delta/d$, useless for $\Delta \approx 70$; for the random graph a first moment as in Theorem E would give it); (ii) the entropy of the support $T$ and of $B_0$ inside the count ($|U|$ and $|B_0|\log_2(en/|B_0|)$ bits, doubled), which the slack $(2 - 3\gamma)|B_0| + (1 - \gamma)\sum|A_{ij}|$ absorbs only for small $\gamma$ (I estimate $\gamma \lesssim 0.3$, so $d \ge 10$ at rate 1/2).
3. *Rate 1/2 only:* transversal configurations with $|N[T]| > \varphi_0 n$. Their cost is at least $\varphi_0 n$ and each direction class has closure at most $k$, but the crude count of directions ($q^{|T|}$) is not enough; the components argument of item 2 is needed here too.

So the theorem as stated is conditional; what the argument above indicates for L is $E_3 \approx 2\varepsilon_2 n$ to $2(\varepsilon_2 + |U|/64n)\,n$, the same order as $E_T$. **I do not claim L.** Section 7 gives the constants with $E_3 = \max(2e_2 - 2, E_T)$ and with an allowance of $0.02n$ for L.

## 7. Constants, thresholds, queries, list sizes

**The number of patterns.** $|\Pi(\Theta)| \le (n + 1)^3\max\binom{n}{u_3, s, s, s}$ over $2u_3 + 3s = \Theta + 1$, $u_3 + s \le A_2$ (the multinomial is Schur-concave in the three pair parts). At rate 1/2 the maximum is essentially unconstrained, $5^n$ ($\log_2 5/64 = 0.0363$); at lower rates the weight constraint cuts it down. This replaces the lead's $3H(a)$ bits a position ($0.043$ at rate 1/2) and is exact: the entropy is that of the cover pattern, not of three sets.

**Table [exact for the proved part, `62_triples.py`; conditional on L as a whole].** $q = 2^{64}$, (W2) with $\gamma \le 0.40$, $a_0 = 0$; queries $= \lceil 108/\log_2(1/\alpha)\rceil$ (the count of note 57), $\alpha^*$ the root of $\alpha^2(3 - \alpha) = (2k + E_3)/n$. The numbers are the same to four digits for $N = 20$ to 28.

| rate | $e_2/n$ (Thm A) | $E_T/n$ | $E_3/n$ | $\alpha^*$ | queries | Johnson radius, queries | $M_0$ at $\alpha^* + 0.005$, $+0.01$ | with $0.02n$ more for L: $\alpha^*$, queries |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | 0.01561 | 0.03625 | 0.03625 | 0.6664 | 185 | 0.7071, 217 | 19, 10 | 0.6739, 190 |
| 1/4 | 0.01299 | 0.02989 | 0.02989 | 0.4564 | 96 | 0.5000, 108 | 40, 21 | 0.4658, 98 |
| 1/8 | 0.00887 | 0.02007 | 0.02007 | 0.3173 | 66 | 0.3536, 73 | 58, 30 | 0.3296, 68 |
| 1/16 | 0.00561 | 0.01249 | 0.01249 | 0.2225 | 50 | 0.2500, 54 | 71, 37 | 0.2388, 53 |

(Without any excess the thresholds are $\tau_3 = 0.6527, 0.4421, 0.3045, 0.2117$.) $E_T$ exceeds $2e_2$ at every rate, so the collinear triples are not the binding case. The list constant is small as soon as the agreement is a query or two above the threshold: $M_0 \le 3(\alpha + \alpha^2 - \Theta/n)/\mathcal{A}$, about $0.1/\text{margin}$ at rate 1/2.

**Which window systems qualify [proved part].** Theorem A(ii) and Lemma 5.3 need $\gamma(\rho) \le 1/2$; Proposition T covers all transversal configurations iff $\gamma(2\rho) < 1/2$, and the table needs $\gamma \le 0.40$ there (at $\gamma = 0.45$ add $0.0001$ to $E_3/n$). From section 2, $N = 25$:

| | rate 1/2 | 1/4 | 1/8 | 1/16 |
| --- | --- | --- | --- | --- |
| needs | $\gamma(1/2) < 1/2$ for the free part; Proposition T incomplete | $\gamma(1/2) < 1/2$ | $\gamma(1/4) < 1/2$ | $\gamma(1/8) < 1/2$ |
| random graph $d = 6$ | 0.501: fails by $10^{-3}$ | 0.501: fails | 0.351 | 0.292 |
| $d = 8$ | 0.371 | 0.371 | 0.256 | 0.214 |
| $d = 10$ | 0.288 | 0.288 | 0.200 | 0.168 |
| cube (note 60) | 0.69: pairs only with $\Xi \le 2$ (see below) | 0.69 at density 1/2: fails | 0.55 at density 1/4: fails | 0.47 at density 1/8: holds |

Odd degrees (same script, $N = 25$): $\gamma(1/2) = 0.428$ at $d = 7$, $\gamma(1/4) = 0.426$ at $d = 5$, $\gamma(1/8) = 0.449$ at $d = 4$. So the least degree for which everything proved here applies is $d = 7$ at rates 1/2 and 1/4, $d = 5$ at rate 1/8, $d = 4$ at rate 1/16 (for these the factor of Proposition T is below $2^{10^{-4}n}$, less than $2 \cdot 10^{-6}n$ field elements in $E_3$). **Cube corollary:** Theorem A(ii) holds for the cube with $\Xi \le 2$ at every rate and $N \le 28$ (its proof only needs $q^{1/\gamma - 1} \ge 2(k + e)$, true for $\gamma \le 0.69$); Lemma 5.3 gives free weight below $2k$ only for $\gamma < 2/3$, that is at rates 1/4 and below; Proposition T holds for the cube at rate 1/16 only. At rate 1/2 the cube does not even pass the free part ($3 \cdot 0.69 > 2$; with disjointness of the three fibres the free weight is at most $0.69\,n < 2k$ only when there is no common factor, note 60 section 3.6).

**Smaller domains (later levels).** For $N = 16$: $E_3/n = 0.0367, 0.0304, 0.0206, 0.0130$ with $a_0 = 16$ (the term $q^{2a_0}$ costs $32$ field elements, $0.0005n$). For $N = 10$ with $a_0 = 16$ it costs $0.031n$ and the thresholds rise to $0.678, 0.472, 0.338, 0.250$ (193, 100, 69, 55 queries; no gain at rate 1/16); with $a_0 = 0$ and $d = 8$ (then $\gamma(1/2) = 0.399$ at $N = 10$) one gets $E_3 = 38, 31, 21, 14$ field elements ($E_3/n = 0.0371, 0.0303, 0.0205, 0.0137$) and the queries of the main table, 185, 96, 66, 50. So at small sizes the multiplicative form of (W2) with a slightly larger $d$ is better than an additive allowance.

## 8. Numerical checks

All scripts are in `scripts/`, pure Python, seconds each; outputs in `62_*_output.txt`.

| script | what is checked | result |
| --- | --- | --- |
| `62_toy.py prob` | Lemma 1.1: exhaustive enumeration of $\mu$ over $\mathrm{GF}(4)$, $n = 4$, windows of 2 points, 12 random patterns of three polynomials and three sets; model U ($4^8$ values of $\mu$) and model 1 ($4^4$) | exact equality with $q^{-\sum\dim R_x}$ in model U, and with that or 0 (centre-only criterion) in model 1 |
| `62_toy.py lift` | Proposition N at $n = 64$, $k = 32$, $\mathrm{GF}(2^8)$, local windows $t' = 2, 3$, $m = 4, 8, 16$, both models: the identity $c_\mu(gL) = L\,c_\mu(g)$ and the weight of the periodic triple | weight $= 2k + m - 2$ exactly (66, 70, 78; $u_2 n = 3m$, $u_3 n = k - m - 1$); with the cube window the identity fails and the same triple has weight 0 |
| `62_toy.py pairs` | Theorem A at toy size: all $16^4$ codewords over $\mathrm{GF}(16)$, $n = 16$, $k = 4$, cube and local windows ($t' = 1, 2$), 3 samples of $\mu$ each | largest number of zeros 5 to 7: above the MDS value $k - 1 = 3$ by about $nH(\rho)/\log_2 q = 3.2$ (Remark 1 of section 3), below the first-moment bound 8 (form (i) at failure $1/2$) |
| `62_toy2.py lattice` | Lemma 5.4: 300 random window systems and configurations over $\mathrm{GF}(16)$, $n = 12$, windows of 3 or 4 points: the dimensions of the solution spaces in every degree, $e_1 + e_2 = |Y_1|$, and the count with type-2 points for $k = 3, 5, 7$ | all equal; 331 transversal and 569 non-transversal cases |
| `62_toy2.py tr` | the bound of Proposition T for one support, by brute force over all $8^6$ pairs: $\mathrm{GF}(8)$, $n = 8$, $k = 3$, windows of 2 points, pattern $U_3 = D$ | for every $T$ with $|N[T]| \le k$: $\sum_{\sigma} \mathcal{N}(\sigma) \le q^{2k + 2|T| - |N[T]|}$; beyond ($|N[T]| > k$) the bound fails by up to $q^{0.74}$ and $\sum_d q^{\mathrm{loss}} = q^{7.8}$ against $q^6$: with 2-point windows nothing expands, as expected |
| `62_expansion.py` | Theorem E: $\gamma(d, \varphi)$ at failure $2^{-129}$ | section 2 |
| `62_constants.py pairs`, `62_triples.py` | $e_2$, $|\Pi|$, $E_T$, $E_3$, thresholds, queries, $M_0$ | sections 3 and 7 |

**Not done:** the brief asked for an estimate, by sampling $\mu$, of the largest $u_2 + 2u_3$ over all triples at toy size. Exhaustive search over pencils needs $q^{2k}$ pairs with $q \ge n$ (the domain lives in $K$), and at the sizes where it is feasible ($n \le 16$, $k \le 4$, $q = 16$) the first-moment excess $n/\log_2 q$ is as large as $k$, so the experiment cannot distinguish $2k + \varepsilon n$ from anything; I did the deterministic constructions (Proposition N) and the exact counting identities instead. A meaningful experiment needs a search heuristic for deficient pencils at $q \ge 2^{16}$, $n \ge 64$, which I did not write.

## 9. Answers to the remaining questions of the brief

### 9.1 Windows of 2 or 3 points

XOR windows: fail deterministically (section 4, consequence 3): an XOR window of $r$ offsets spans at most $r - 1$ dimensions, the subspace polynomial of any larger proper subspace is a window invariant, and periodic triples have weight $2k + m - 2$. Graph windows with $d = 1$ or 2 partners: no window invariant in general, but the two proved ingredients both fail. (i) Free part: $\gamma_\infty(d, 1/2)$ is the root of $D(\gamma\,\|\,2^{-d}) = 2$ bits, which is above $2/3$ for $d \le 4$ ($0.86, 0.71, 0.59$ at $d = 3, 4, 5$) and has no root below 1 for $d \le 2$ ($D(1\,\|\,2^{-d}) = d \le 2$): some half-size sets are almost entirely interior. (ii) Transversal count: a deficient window gives a loss of up to 2 (in the expansion: $q^2$ configurations) for at most $d + 1$ conditions, so $d + 1 > 2$ is necessary even when no two windows meet, and with windows meeting, $1/\gamma > 2$ is what is needed; for 2-point windows the brute-force sum $\sum_d q^{\mathrm{loss}}$ is $q^{7.8}$ against $q^6$ at toy size (`62_toy2.py tr`). The least $d$ for which sections 3 to 5 apply is 7 at rates 1/2 and 1/4, 5 at rate 1/8, 4 at rate 1/16 (section 7).

### 9.2 What the same mechanism needs for $t = 4$ (not proved; for researcher 63)

Target: $H_4$: $\sum_x (c_x - 1)_+ \le 3k + E_4$ for every four members; lists are constant above $g_4(\alpha) = 4\alpha - 1 + (1 - \alpha)^4 = 3\rho + E_4/n$ (Proposition J of note 61).

1. **Lower rungs force $E_4 \ge 3e_2$ and more.** Four collinear members agree simultaneously on $Z_\mu(d_*)$: weight $3A_2$. Coplanar quadruples (affine rank 2) are a rank-2 first moment with six named directions $(1,0), (0,1), (1,1), (\alpha,\beta), (\alpha+1,\beta), (\alpha,\beta+1)$; a position covered by all four has weight 3 and rank at most 2, so the excess is at least $3/2$ of the entropy of $U_4$. They do not follow from $H_3$ by averaging (the average over the four sub-triples only gives $\mathrm{wt}_4 \le \frac12\sum\mathrm{wt}_3 \le 4k + 2E_3$).
2. **Patterns.** Cover types: 6 pairs, 4 triples, 1 quadruple, 1 for the rest: at most $12^n$ patterns, $\log_2 12/64 = 0.056$ per position before the weight constraint (against $0.036$ for $t = 3$).
3. **Free part.** Six zero sets of fewer than $k$ points; with (W2), $\sum_x (c_x^{\mathrm{free}} - 1)_+ \le 5\gamma k + O(a_0)$ (note 66), so $\gamma < 3/5$ suffices; note 60's linear program gives the sharp form.
4. **Transversal count.** Configurations $\sigma_x \in K^3$, a subspace $\Lambda_y \subseteq K^3$ at every point, $\mathrm{cost} = \sum_y \dim\Lambda_y \ge |N[T]|$, count $q^{3k - \mathrm{cost}}$ when the three successive minima of the rank-3 lattice are at most $k'$ (Lemma 5.4 generalizes verbatim: $\sum e_i = \sum_y \dim\Lambda_y$ over the points with $\dim\Lambda_y \le 2$, count $q^{\sum(k' - e_i)_+}$). The crude count of Proposition T then needs $3|T| \le |N[T]|$: **$\gamma < 1/3$ up to density $\min(1, 3\rho)$**, in general $\gamma < 1/(t-1)$ up to density $(t-1)\rho$. At rate 1/4 that is $\gamma(3/4) < 1/3$, which needs $d \ge 15$ ($\gamma_\infty(d, 3/4) = 0.343, 0.316, 0.293$ for $d = 14, 15, 16$); at rate 1/8, $\gamma(3/8) < 1/3$, $d \ge 8$ ($\gamma_\infty = 0.351, 0.303$ for $d = 7, 8$). So for $t = 4$ already the crude count is not enough at rates 1/2 and 1/4 with $d \le 10$, and the refined count (directions are constant on components; a window of deficiency $j$ costs $j(d + 1 - 3 + j)$ conditions, not $d + 1$ per vector) is needed in the transversal range too.
5. **Non-transversal configurations.** Two kinds: $e_3 > k' \ge e_2$ (solutions $f_1v_1 + f_2v_2$, cost at least $k + e_1 + e_2$; the cross product $v_1 \times v_2$ is a map to $\mathbb{P}^2$ of degree at most $e_1 + e_2$ that is constant on the deficient windows) and $e_2 > k'$ (solutions $fv_1$, cost at least $2k + e_1$; the quadruple is a "pair in disguise"). The analogue of Lemma 6.1(3) is: $2e_1 + 1$ points carrying two conditions determine $v_1$ up to a factor (the $2 \times 2$ minors of $(v_1, v_1')$ vanish there), and $2(e_1 + e_2) + 1$ points carrying one condition $\lambda_y$ determine $v_1 \times v_2$ up to a factor (it is parallel to $\lambda_y$ there) **[proved by the same argument, not written out]**; the analogue of Hypothesis L has in addition the named sub-pencils (four triples, six pairs), whose losses are capped by $H_3$ and $H_2$, and each cap brings its own factor on the entropy ($3/2$ and $3$ for all positions deficient of rank 2 and 1).
6. **New axiom.** The near-interior bound $|\{x : |W_x \setminus Z| \le j\}| \le \gamma_j|Z|$ for $j = 1, 2$ (windows that are deficient because all but $j$ of their points are common zeros), which Hypothesis L already needs for $j = 1$.

### 9.3 Errors found in note 57 section 9

1. **Zero-deficient positions dropped** ("gain ... up to zero-deficient positions"). Fatal for local windows: Proposition N(c), weight $2k + m - 2$. (Acknowledged in note 57 section 10 while this note was being written; Proposition N gives the exact construction, its numerical confirmation, and the sharp constant $\iota \le 2/3$.)
2. **"$|J_3| \le u_3 n \le k + \varepsilon_2 n$ caps the loss."** It caps the triple-covered deficient positions only. The double-covered free positions are capped by expansion (Lemma 5.3), and in the non-transversal case they enter the balance with the named fibres (section 6, item 1).
3. **Case A, "the number of pairs $(a, b)$ with the pattern is $q^{2m+2-|Y|+p}$ exactly (balanced lattice)" for $|Y| \le 2m + 1$.** Not exact and not an upper bound in general: the lattice is balanced iff $e_2 \le m + 1$, which $|Y| \le 2m + 1$ does not imply (a direction class with more than $m$ points, or a short vector of degree $e_1 < |Y| - m - 1$, unbalances it). The correct statement is Lemma 5.4, and the correct criterion that is easy to check is $|N[T]| \le k$ (for the pair) rather than $|Y| \le 2m + 1$.
4. **Case A, "a cluster costs nothing unless it equals its own closure ... at most one field element per block".** For the cube and for graphs this is replaced by Proposition T, which is simpler and needs no cluster analysis; but it needs $\gamma < 1/2$ up to density $2\rho$, which local windows do not have (and the cube has only at rate 1/16).
5. **Case B, "loss minus cost is at most $\varepsilon_2 n + 2$".** The first moment for a non-transversal pencil with all triple positions deficient has gain 1 per unit of weight 2, so the excess is twice the entropy, not $\varepsilon_2 n$ (section 6, item 1). Also "$p_0 \le (2m + 2)/r + 1$ clusters" assumes clusters are full windows; windows partly inside the common zero set give clusters of 2 points ($p_0$ up to $m + 1$) and of 1 point (automatic deficiency).
6. **Entropy "$3H(a)$".** The union bound is over cover patterns, $5^n$ at most with the weight fixed, not over three sets: $0.036$ instead of $0.043$ at rate 1/2, much less at low rates (section 7). This one is in the lead's favour.
7. **"Windows of 8 or 9 neighbouring points and no isoperimetric input."** False on both counts: the window must expand ($\gamma \le 1/2$ at density $\rho$ for the free part and the pairs' sharp constant, $\gamma < 1/2$ at density $2\rho$ for the transversal count).
