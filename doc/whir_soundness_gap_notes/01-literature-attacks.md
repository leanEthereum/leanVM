# 01. Literature and known attacks

Researcher 01. Scope: the attack side (large lists and correlated-agreement failures below the Johnson threshold for Reed-Solomon codes on $\mathbb{F}_2$-subspace domains), and its transfer to $D_{\kappa,R} \subset K = \mathrm{GF}(2^{64})$, $n = 2^N$, code over $E$. Notation as in the lead notes: $K_0 := 2^\kappa = \rho n$ (to avoid a clash with the field $K$), genuine codewords have degree $< K_0$, the analysis degree is $d = K_0 - 1 + \ell$, $T$ is an agreement count, $\binom{N}{c}_2$ is a Gaussian binomial.

Every statement carries one of four tags. **[proved]**: the proof is in this note. **[checked]**: verified by `scripts/01_checks.py` on the sizes stated. **[conjectured]**: heuristic. **[quoted]**: a theorem of a paper I obtained and read, with the proof read but not reproduced here.

## 0. Findings in one page

1. **Rate 1/2 moves from 9/16 to 5/8.** The height-two case of the decision-tree construction of [DKTZ26, Lemma 6.9 and the remark after Thm. 6.10] gives, on every additive domain, $M_2(N) = 28\,(6 \cdot 2^{N-3} - 5)$ sets of size $5n/8$ whose locators share every coefficient above degree $n/2$. For $N = 25$ this is $2^{29.4}$ polynomials of degree $\le n/2$ agreeing with the one word $X^{n/2} L_W$ on $5n/8$ points, or $2^{29.4}$ genuine codewords (degree $< n/2$) at agreement $5n/8 - 1$. The Proximity Prize ignores it because the prize needs families above $2^{64}$. With the budget $2^{10}$ the floor at rate 1/2 is $t \ge 160$ (was 131). **[proved]**, **[checked]** at $N = 7$.
2. **Nothing is known between $5n/8$ and $n/\sqrt2$ at rate 1/2**, on any binary domain, for lists that grow with $n$. [DKTZ26, Section 8] and [Zhu26, Section 7] both state it as open (their dense-domain constructions also stop at $5/8$). The only gain I found is a second-order one: padding hyperplanes with a set of biased Fourier spectrum gives $2^{10}$ codewords at $T/n \approx 0.628$ ($t \ge 161$), and a Parseval bound caps that mechanism at $5/8 + \sqrt{3/(64L)}$ for lists of size $L$. **[proved]**, **[checked]**.
3. **Family sizes at the frontier are small, and that matters for the cost model.** At rate 1/2 the $5n/8$ family has $2^{29.4}$ members, at rate 1/4 the Johnson-tight family has $2n - 2 \approx 2^{26}$. I do not expect unions of flats to do better at these agreements (Section 3.3). So a list budget of $2^{31}$ at rate 1/2 would not be contradicted by any known construction above $9n/16$ (where the family is $2^{102.7}$).
4. **Low rates: flats ($2\rho n$) are the frontier for $\rho \ge 1/16$ at $N \approx 25$.** The classical route above $2\rho n$ is the pigeonhole of [BKR06] on a locator coefficient, and each coefficient costs 64 bits on our domain. It gives $T = 4\rho n$ only when $\binom{N}{R-2}_2 \gg 2^{64}$: lists of $2^{42.7}$ at $\rho = 1/128$, $2^{25.7}$ at $\rho = 1/64$, about $2^{6.6}$ at $\rho = 1/32$ and nothing at $\rho \ge 1/16$ (for $N = 25$). Johnson would be reached at rate 1/16 only for $N \ge 33$. These lists are non-constructive. **[proved]**.
5. **The Gold construction of [DKTZ26] does have solutions on sparse domains, in the number a random model predicts.** The paper only says its counting hypothesis fails for leanVM. On the analogue $\mathrm{span}(1, \dots, x^{d-1}) \subset \mathrm{GF}(2^{16})$ I count 82, 1411 and 22979 rank-4 solutions for $d = 8, 9, 10$ against predictions 85.8, 1414.1, 22961.9. Extrapolated to our domain: about $2^{30.5}$ ($N = 25$) to $2^{34.5}$ ($N = 26$) codewords at rate 1/4 and agreement $3n/8$. This never beats flats in agreement, but it sets the list size just below the rate-1/4 threshold. **[checked]** on the analogue, **[conjectured]** on $D_{\kappa,R}$.
6. **For the affine combiner, pole pairs and lists are the same object**, with degree bound $d + 1$ on the list side, and the "coefficient reading" MCA attacks of [DKTZ26, Thm. 4.1] and [BCHKS25, Cor. 1.7] (Johnson at rate 1/16 for a scalar combiner) port only as isolated bad points, error $M/|E|^2$. **[proved]** for the port, no general impossibility.
7. **No upper bound beyond Johnson applies to subspace domains.** All positive results need large characteristic, random or specially constructed evaluation points, or go a constant number of positions beyond Johnson (Section 5).

## 1. Sources

Obtained and read (PDF text under the session scratchpad, `papers/`):

- [DKTZ26] Dao, Kominers, Thaler, Zheng, [ECCC TR26-237](https://eccc.weizmann.ac.il/report/2026/237/), revision 1 (2 Nov 2026), 68 pages. Read in full except Sections 5.7 to 5.9 and Appendix A, where I read the statements only.
- [Zhu26] M. Zhu, Superpolynomial Lists for Reed-Solomon Codes over Binary Extension Fields, [arXiv:2610.15815](https://arxiv.org/abs/2610.15815). Sections 1, 2, 5.4, 6, 7.
- [ABF26] Arnon, Boneh, Fenzi, [ePrint 2026/680](https://eprint.iacr.org/2026/680). ePrint refuses non-browser clients (HTTP 403). I read the **April 2026 version** from the Wayback Machine (snapshot 20260430), Sections 3.2, 4.3, 5 and 6.4. The July 2026 revision (which adds an attack estimate and an MCA lower bound, per its ePrint abstract) was **not obtained**.
- [BKR06] Ben-Sasson, Kopparty, Radhakrishnan, FOCS 2006 version ([pdf](https://sites.math.rutgers.edu/~sk1233/rsld.pdf)). Theorem 2.1 and corollaries.
- [GR05] Guruswami, Rudra, STOC 2005 ([pdf](https://www.cs.cmu.edu/~venkatg/pubs/papers/rs-limits.pdf)). Theorems 1 and 3.
- [BCHKS25] ECCC TR25-169, Theorem 1.6 and Corollary 1.7 and their proof idea only.
- [CWYZ26] ePrint 2026/2863 (local copy), Sections 1.2 and 6.
- [Jo26] ePrint 2026/1432, [Gab26] ePrint 2026/2048, [DKT26] ePrint 2026/2056 (Wayback copies), [AGG26] ECCC TR26-262, [GYXK26] arXiv:2607.10572, [CGGGRZ26] arXiv:2610.31922: abstracts and main statements only.
- Proximity Prize: `bettercodes/flight.txt` (writeups, each truncated at about 2 kB by the site) and `repo/ProximityPrize/SubmissionBinaryUpper/` (doc comments of `Solution.lean`, `LabelFamily.lean`, `PrescribedTop.lean`).

Not obtained: [JH01] Justesen and Høholdt (IEEE, paywalled). What I say about it is second-hand, from [ABF26, Thm. 3.14], [BKR06, Section 2.1] and [DKTZ26, Section 1.2], and is marked as such.

## 2. Framework

### 2.1 Lists and pole pairs are the same thing for the affine combiner

**Lemma A (pole pair). [proved]** Let $w : D \to E$ be any word and $C_1, \dots, C_L$ distinct polynomials of degree $\le d + 1$, with $C_i = w$ on $S_i \subseteq D$, $|S_i| \ge T$. Fix a pole $\beta_0 \notin D$ and put $f_0(x) = 1/(x - \beta_0)$, $f_1(x) = w(x)/(x - \beta_0)$. For every $i$ and every $\beta \in E$, with $\alpha = C_i(\beta_0) + \beta\beta_0$, the fold $f_1 + (\alpha + \beta x) f_0$ agrees on $S_i$ with the polynomial $P_{i,\beta} = \beta + (C_i(X) - C_i(\beta_0))/(X - \beta_0)$ of degree $\le d$. No polynomial of degree $\le d$ agrees with $f_0$ on more than $d + 1$ points.

*Proof.* $f_1 + (\alpha + \beta x) f_0 = \beta + (w(x) + \alpha + \beta\beta_0)/(x - \beta_0)$, and on $S_i$ the numerator is $C_i(x) + C_i(\beta_0)$ (characteristic two), divisible by $X - \beta_0$. If $G$ of degree $\le d$ agrees with $f_0$ at $x$ then $x$ is a root of $(X - \beta_0) G - 1$, nonzero of degree $\le d + 1$. $\square$

So each value $C_i(\beta_0)$ is a line of $|E|$ bad pairs $(\alpha, \beta)$, and the pure affine MCA error at agreement $T > d + 2$ is at least $\#\{C_i(\beta_0)\} / |E|$. Two members collide for at most $d + 1 - |S_i \cap S_j|$ poles, so averaging over the $2^{64} - n$ poles of $K \setminus D$ ([DKTZ26, Lemma 3.19]) leaves at least $L - (d+1)\binom{L}{2}/(2^{64} - n)$ distinct values: all but $2^{19}$ of them for $L = 2^{30}$, $d \approx 2^{24}$. Poles in $E \setminus K$ lose nothing.

Conversely every pole-pair family in the literature is of this form ($w$ is the common top $R$, $C_i$ the corrections). Consequences:

- The two columns the brief asks for differ only in the degree bound: genuine lists need $\deg C_i < K_0$, the list $\Lambda$ of the problem statement allows $\deg C_i \le d$, and the pole pair allows $\deg C_i \le d + 1 = K_0 + \ell$. This settles the question at the end of Section 4.2 of the main document: the degree slack is usable, and the witness of the fold has degree $\le d$.
- Words over $K$ are enough. All words below are polynomials over $K$ evaluated on $D \subset K$, so they are admissible level-0 oracles, and the pole can be taken in $K \setminus D$. The remark of [DKTZ26, Section 7] that words over a subfield containing the domain confine the exceptional *scalar* challenges to that subfield does not protect the affine combiner: the bad set $\{\alpha + \beta\beta_0 = \gamma\}$ is a full line of $E^2$ for $\gamma, \beta_0 \in K$.

**Lemma B (a bad line with a repeated support is a pole pair). [proved]** Suppose $(\alpha_0, \beta_0') + t(\alpha_1, \beta_1)$ is bad for two values $t \ne t'$ with the same agreement set $S$: $f_1 + (\alpha_0 + \beta_0' x) f_0 + t(\alpha_1 + \beta_1 x) f_0 = P_t$ on $S$, likewise for $t'$. Then on $S$, $(\alpha_1 + \beta_1 x) f_0 = G := (P_t - P_{t'})/(t - t')$, so $f_0 = G/(\alpha_1 + \beta_1 x)$ and $f_1 = P_t - t G - (\alpha_0 + \beta_0' x) G/(\alpha_1 + \beta_1 x)$: the pair is a pole pair on $S$ with pole $\alpha_1/\beta_1$ (or a pair of polynomials of degree $\le d + 1$ if $\beta_1 = 0$). So an attack on pure affine MCA that is not of the pole shape must use a different agreement set for every challenge on a line, or have no bad lines at all.

### 2.2 The half-flat law for unions of flats

**Lemma C ([DKTZ26, Lemma 6.1], list form). [proved]** Let $w_0$ be a power of two, $W \subseteq D$ any set, and $A \subseteq D \setminus W$ a disjoint union of affine flats, each of size $\ge 2w_0$, with $|A| = T_0$. Then $L_A = X^{T_0} + G_A$ with $\deg G_A \le T_0 - w_0$, and the word $X^{T_0} L_W$ agrees with $C_A := L_W G_A$, of degree $\le T_0 - w_0 + |W|$, exactly on $W \cup A$.

*Proof.* A flat $v + V$ with $|V| = 2^s$ has locator $L_V(X) + L_V(v) = X^{2^s} + (\text{degree} \le 2^{s-1})$, since $L_V$ is linearized. In the product of the flats' locators every term other than $X^{T_0}$ uses a lower term of some factor, losing at least $w_0$. And $X^{T_0} L_W + C_A = L_W L_A$ vanishes exactly on $W \cup A$. $\square$

With degree bound $K_0 = T_0 - w_0 + |W|$ the agreement is $T = T_0 + |W| = K_0 + w_0$. So **every union-of-flats family sits exactly half a flat above the degree**, and families differ only in how many sets there are. The genuine variant removes one point from $W$ (degree $\le K_0 - 1$, agreement $T - 1$). Lemma C with $W = \emptyset$ and one flat is the flats family of the lead notes; with trees it is [DKTZ26, Thm. 6.10]; the prize's 106.24 certificate is a mixed-size instance.

Since $2w_0 \le n/2$ for a proper flat, $T \le K_0 + n/4$, and the larger the flats the fewer the sets. At rate 1/2: hyperplanes ($w_0 = n/4$) give $T = 3n/4$, above Johnson, but only the 3 affine hyperplanes disjoint from a codimension-2 subspace $W$ (the Johnson bound allows 4 there); codimension-2 flats ($w_0 = n/8$) give $5n/8$ with $\Theta(n)$ sets; codimension 3 gives $9n/16$ with $\Theta(n^4)$.

## 3. The constructions

### 3.1 Flats ([BKR06], [BGKS20], [DKTZ26, Thm. 4.7], lead notes)

**[proved]** (Lemma C, one flat, $W = \emptyset$.) For every affine flat $F \subseteq D$ of size $2K_0$, $X^{2K_0} - L_F$ has degree $\le K_0$ and agrees with the word $X^{2K_0}$ exactly on $F$. So $\Lambda(2\rho n) \ge 2^{R-1}\binom{N}{R-1}_2$ in degree $\le K_0$, and $\binom{N}{R-1}_2$ genuine codewords at $2\rho n - 1$ (linear subspaces, divide by $X$, as in the lead notes). At $R = 2$ this is $2n - 2$ affine hyperplanes at $T = n/2$.

[DKTZ26, Thm. 4.7] **[quoted]** adds an exact classification at rate 1/4 on every proper affine binary domain: for the pair $f = \sqrt{\lambda/(x - \beta)}$, $g = 1/(x - \beta)$ ($\lambda = L_D'$), the scalar challenges with agreement $n/2$ are exactly the $2n - 2$ hyperplane challenges, $\mathrm{agr}(f) \le 3n/8 - 1$, common agreement $n/4$. The proof shows that a monic $F$ of degree $n/2$ with all roots in $D$ and $\deg(F^2 - L_D) \le n/2$ satisfies $L_D = F^2 - cF$, hence is additive up to a constant ([DKTZ26, Lemma 3.10]). This is the only kind of exact upper bound at the Johnson threshold I found for subspace domains (Section 5).

### 3.2 The subspace-polynomial pigeonhole ([BKR06, Thm. 2.1])

**[quoted]** [BKR06, Thm. 2.1]: for a prime power $q$ and $0 \le u \le v \le m$ there are a word $w(x) = x^{q^v} + \sum_{u < i < v} \alpha_i x^{q^i}$ on $\mathbb{F}_{q^m}$ and at least $q^{(u+1)m - v^2}$ polynomials of degree $q^u$ agreeing with it on $q^v$ points. Field size $q^m$, domain the whole field, rate $q^{u-m}$, agreement $q^{v-m}$. The proof takes the $v$-dimensional subspaces and pigeonholes on the $v - u - 1$ locator coefficients between the top and degree $q^u$.

**Transfer. [proved]** For $c \ge 1$, $u \ge 0$ with $c + u + 1 = R$, a subspace $V \le D$ of codimension $c$ has $L_V = X^{T} + a_1 X^{T/2} + \dots + a_u X^{T/2^u} + (\text{degree} \le K_0)$ with $T = 2^{N-c} = 2^{u+1} K_0$ and $a_i \in K$. Some key $(a_1, \dots, a_u) \in K^u$ is shared by at least $\binom{N}{c}_2 / 2^{64u}$ subspaces, and the $2^c$ cosets of each share it too (a translation changes only the constant term). Hence
$$\Lambda(2^{u+1}\rho n) \ \ge\ 2^{c}\binom{N}{c}_2 \big/ 2^{64u}, \qquad c = R - u - 1,$$
in degree $\le K_0$, and $\binom{N}{c}_2/2^{64u}$ genuine codewords at one point fewer. The exponent is about $c(N - c) + c + 1.6 - 64u$. This is the whole cost of sparsity: on $\mathbb{F}_{2^m} = D$ the same count has $m$ in place of 64. Johnson-tight lists ($2^{u+1}\rho = \sqrt\rho$, $R = 2u + 2$) need $(u+1)(N - u) \gtrsim 64u$: $N \ge 33$ at rate 1/16. This is consistent with [BCHKS25, Thm. 1.6], whose domain is a random subspace of size about $q^{(1+\epsilon)/\tau}$ at rate $2^{-(\tau+2)}$.

**[checked]** The keys behave as uniform: among 6000 random codimension-2 subspaces of the 10-dimensional analogue in $\mathrm{GF}(2^{16})$, 277 pairs share $a_W$ against 274.6 expected. The 1023 hyperplanes have 1023 distinct $a_H$, as they must.

The members are not explicit: exhibiting $L$ subspaces with a common 64-bit key costs about $2^{64}/\text{(multiplicity)}$ work per member. The statement is still a valid upper certificate (the prize's `PrescribedTop.exists_big_fiber` is of this kind), and any proof of a list bound must respect it.

**Padded variant. [proved]** Take the family for $(R + 1, u)$, so degree $\le K_0/2$ and flats of density $2^{-c}$, $c = R - u$, and multiply the word and the codewords by $L_B$ for a subspace $B$ of size $K_0/2$ in general position ($B + V = D$, which holds for all but a $2^{c - N + R + 1}$ fraction of the directions, [DKTZ26, Lemma 5.14]). Degree $\le K_0$, agreement $n\,(2^{-c} + 2^{-R-1}(1 - 2^{-c}))$. For $u = 1$ this is $(2.5 - \rho)\rho n$ with about $2^{R-1}\binom{N}{R-1}_2/2^{64}$ members.

### 3.3 Unions of flats with padding: decision trees ([DKTZ26, Section 6])

**[quoted]** [DKTZ26, Thm. 6.10]: for $h \ge 3$, every binary additive $D$ of dimension $N \ge 2^h - 1$ in a field of size $q > n$, at rate 1/2 there is one pair with common agreement exactly $n/2$ and at least $\min(M_h(N)/2, q/n)$ distinct scalar challenges at agreement $(1/2 + 2^{-h-1})n$, where $M_h(N) = \Theta_h(n^{2^h - h - 1})$ counts the supports of height-$h$ decision trees (balanced Boolean functions that test $h$ independent linear functionals on each path, $2^h - 1$ in total) avoiding a fixed subspace $W$ of size $n/2^{h+1}$. $M_2(N) = 28(6 \cdot 2^{N-3} - 5)$ and $M_3(N) = 71680(6w-5)(w-1)(w-2)(w-4)$, $w = n/16$. The paper notes that the same proof works at $h = 2$, agreement $5/8$, and dismisses it because $M_2 = \Theta(n)$ gives too few challenges for a 192-bit field.

**Transfer. [proved], [checked]** By Lemma C with $T_0 = n/2$, $w_0 = n/2^{h+1}$ and $|W| = w_0$: the word $X^{n/2} L_W$ agrees with $L_W(L_A - X^{n/2})$, of degree $\le n/2$, on the $n/2 + w_0$ points of $W \cup A$, for each of the $M_h(N)$ supports $A$. For our budgets $h = 2$ is the relevant case:

- $h = 2$: $T = 5n/8$, $M_2(25) = 2^{29.4}$. A support is $\{s = 0, a = 1\} \cup \{s = 1, b = 1\}$ for independent functionals $s, a, b$, that is two disjoint codimension-2 flats in different directions.
- $h = 3$: $T = 9n/16$, $M_3(25) = 2^{102.7}$. $h = 4$: $T = 17n/32$, $M_4(25) = 2^{262.5}$.

Checked for $N = 7$ in $\mathrm{GF}(2^{16})$: exhaustive enumeration finds exactly $2548 = M_2(7)$ supports avoiding $W$; for 40 of them $\deg(L_W L_A - X^{n/2} L_W) = n/2$ exactly (so these are not genuine codewords), the agreement with the one word is exactly $80 = 5n/8$, the variant with $W \setminus \{0\}$ has degree $n/2 - 1$ and agreement $5n/8 - 1$, and the pole pair of Lemma A folds to agreement $5n/8$ with a polynomial of degree $< n/2$ for random $\beta$ on each line.

**Is $2^{29.4}$ the end of this family at $5n/8$?** Within unions of flats, a set at $T = n/2 + n/8$ and degree $n/2$ is either two disjoint codimension-2 flats avoiding a padding set of size $n/8$ (a tree support or a hyperplane, [DKTZ26, Section 2.4]) or one codimension-2 flat avoiding a padding set of size $3n/8$, by the arithmetic of Lemma C **[proved]**. The second kind gives about $2^N$ flats when the padding lies in a hyperplane. For a subspace $W$ the count of tree supports is exactly $M_2(N) \approx 21 \cdot 2^N$ **[quoted]**, **[checked]** at $N = 6, 7$. Whether another $n/8$-set $W$ is avoided by more tree supports is **[conjectured]** not to be the case: at $N = 6$ a hill climb over 8-subsets (`scripts/01_tree_padding.py`) never exceeds $1204 = M_2(6)$, reached only at affine flats, and tree functions vanishing on a whole codimension-2 subspace number only $3 \cdot 2^N - 12$ **[checked]** at $N = 6$. So I expect the union-of-flats family at $5n/8$ to be $\Theta(n)$ with constant about 21 per word.

**Other rates. [proved]** The simplest instance of Lemma C at rate $2^{-R}$: fix a hyperplane $H_0$, a padding set $W \subset H_0$ of size $K_0(1 - 2^{-j})$, and take all affine flats of size $2^{1-j} K_0$ inside $D \setminus H_0$. Agreement $K_0(1 + 2^{-j})$, count $2^{R+j-2}\binom{N-1}{R+j-2}_2$. At rate 1/4 and $j = 1$ a sharper count over the 7 hyperplanes through a codimension-3 subspace $W$ gives $7 \cdot 2^N - 35$ flats at $T = 3n/8$ (**[checked]** at $N = 6$: 413).

### 3.4 Hyperplanes with a biased padding set (a small gain above 5/8)

**[proved]** Let $B \subset D$ be any set of size $n/4$ and $H = \{a \cdot x = c\}$ an affine hyperplane. By Lemma C the word $X^{n/2} L_B$ agrees with $L_B(L_H - X^{n/2})$, of degree $\le n/2$, exactly on $H \cup B$, of size $n/2 + n/4 - |B \cap H| = 5n/8 + |\hat B(a)|/2$ for the better choice of $c$, where $\hat B(a) = \sum_{x \in B} (-1)^{a \cdot x}$. By Parseval $\sum_{a \ne 0} \hat B(a)^2 = 3n^2/16$, so at most $3/(64\epsilon^2)$ directions reach $T \ge (5/8 + \epsilon)n$: this mechanism gives lists of size $L$ at most at $5/8 + \sqrt{3/(64L)}$, that is $0.6318$ for $L = 2^{10}$ and $0.6250$ for $L = 2^{26}$.

**[checked]** Taking $B$ as a union of cosets of a codimension-12 subspace, with labels $\{(x, y) \in \mathrm{GF}(2^6)^2 : \text{the two low bits of } xy \text{ are } 11\}$ (1008 of 4096 labels, Walsh values $\pm 16$ and $\pm 48$), 1008 directions have $|\hat B(a)| = 48n/4096$, so 1008 codewords at $T/n = 0.6289$. Random $B$ on a 14-dimensional quotient gives $2^{10}$ codewords at $0.6281$. The identity itself was checked for $N = 8$ on 10 hyperplanes with a random $B$.

This is a second-order effect ($t \ge 161$ instead of 160 at budget $2^{10}$), but it shows that the threshold for a given list budget is a smooth function of the budget near $5/8$, not a step.

### 3.5 Gold sets ([DKTZ26, Section 5], [Zhu26])

**[quoted]** [DKTZ26, Thm. 5.1]: $D \subseteq \mathbb{F}_{2^m}$ additive of dimension $N$, $2 \le t \le \lfloor N/2 \rfloor$, $\iota = 1$ for even $N$ and $0$ for odd, and $\Delta = m - t(m - N + \iota) \ge 1$. Then the word $\sqrt{\lambda x}$ ($\lambda = L_D'$) has at least $2^{2t}(2^\Delta - 1)\binom{\lfloor N/2 \rfloor}{t}_4$ codewords of degree $T/2 < n/4$ at agreement $T = n/2 - n/2^{t+1}$, and there is a pole pair with common agreement $n/4$ and at least half as many scalar challenges (up to a collision term). The agreement sets are the level sets of quadratic Boolean functions of polar rank $2t$ whose alternating matrix $A$ satisfies the $t - 1$ *Gold moment equations* $M_k(A) = \sum_{i<j} A_{ij}(\omega_i\omega_j^{2^k} + \omega_j\omega_i^{2^k}) = 0$ in $\mathbb{F}_{2^m}$, where $\omega_i$ are the labels of the coordinates (square roots of the linear coefficients of their linearized polynomials). Such a set $E$ has $L_E = U^2 + cX$, so $\sqrt{\lambda/c}\,U$ agrees with $\sqrt{\lambda x}$ on $E$. On dense domains ($m - N$ bounded) this gives $n^{\Omega(\log n)}$ codewords at rate 1/4 and agreement $1/2 - o(1)$ (Cor. 5.2), and by padding with a subspace of size $n/4$, at rate 1/2 and agreement $5/8 - 3/2^{t+3}$ (Cor. 5.15). [Zhu26, Thm. 5.17] obtains the same lists on full fields from minimum-weight words of extended BCH codes, with the envelope $\alpha^\ast(1/2) = 5/8$, $\alpha^\ast(2^{-j}) = 2^{1-j}$ for $j \ge 3$.

[DKTZ26, Section 5.1] observes that for leanVM $m = 64$ and $\Delta < 1$ for every $t \ge 2$, so the theorem does not apply, and Section 8 lists sparse domains as open ("the Gold moment equations still define valid candidates").

**Transfer. [checked] on an analogue, [conjectured] on $D_{\kappa,R}$.** The hypothesis $\Delta \ge 1$ is only what the Delsarte-Goethals counting needs. The equations are $64(t-1)$ $\mathbb{F}_2$-linear conditions on alternating matrices, and there are about $2^{2tN - 2t^2 - t}$ of rank $2t$, so a random model predicts $\#\{\text{rank } 2t\}/2^{64(t-1)}$ solutions, each giving $2^{2t}$ codewords. For $t = 2$ the equation says that two planes of labels have the same product of nonzero elements. On $\mathrm{span}(1, \dots, x^{d-1}) \subset \mathrm{GF}(2^{16})$ (also $m \ge 2d$, $\Delta < 1$) the script finds 82, 1411, 22979 rank-4 solutions for $d = 8, 9, 10$ against 85.8, 1414.1, 22961.9 predicted, and verifies one solution end to end for each $d$ (level set of size $3n/8$, locator of the form $U^2 + cX$, a codeword of degree $3n/16$ agreeing with $\sqrt{\lambda x}$ on exactly $3n/8$ points). Predicted on our domain, in $\log_2$ of the number of codewords:

| $N$ | $t = 2$ ($T = 3n/8$) | $t = 3$ ($T = 7n/16$) | $t = 4$ ($T = 15n/32$) |
| --- | --- | --- | --- |
| 25 | 30.5 | 7.5 | none |
| 26 | 34.5 | 13.5 | none |
| 27 | 38.5 | 19.5 | none |
| 28 | 42.5 | 25.5 | 4.5 |

These are rate-1/4 lists (degree $< n/4$), genuine, on the fixed word $\sqrt{\lambda x}$. Padded to rate 1/2 they sit at $17/32$ and $37/64$, below the tree family. So Gold does not move any threshold on our domain, but it is the best estimate of the list size just below the rate-1/4 threshold: about $2^{34.5}$ at $3n/8$ for the level-0 domain ($N = 26$), more than the $2^{28.8}$ of the explicit flat families there.

### 3.6 Coefficient-reading MCA attacks do not port to the affine combiner

**[quoted]** [DKTZ26, Thm. 4.1]: $D \subseteq B \subsetneq F$ additive, $n = 16K_0$. For $\theta \in F \setminus B$ the pair $f = X^{8K_0-1} + \theta X^{4K_0-1}$, $g = X^{2K_0-1}$ has common agreement $2K_0 - 1$ and exactly $(n-1)(n-2)/6$ scalar challenges $z_W = a_W^3 + b_W^2 + \theta a_W$ at agreement $n/4 - 1$, one per codimension-2 subspace $W$ with $L_W = X^{4K_0} + a_W X^{2K_0} + b_W X^{K_0} + \dots$, from $L_W^2 + (a_W^2 + \theta) L_W = X^{8K_0} + \theta X^{4K_0} + z_W X^{2K_0} + (\text{degree} \le K_0)$. This is at the exact Johnson threshold of rate 1/16, on every additive domain, and our fields satisfy the hypothesis with $B = K$, $F = E$. For a scalar combiner over $E$ it would give error $2^{2N - 130.6}$, far above $2^{-118}$. [BCHKS25, Cor. 1.7] is the earlier, domain-specific version, and [BGKS20, Lemma 3.3] the hyperplane version at rate 1/8 ($f = X^{n/2}$, $g = X^{n/4}$), ported to arbitrary additive domains in [CWYZ26, Prop. 6.3].

**Transfer. [proved] for the direct port.** These attacks put the varying locator coefficient *into the challenge* and keep it out of the codeword, which is how they beat the list frontier ($n/4$ against $n/8$ at rate 1/16). With the affine combiner and $f_0 = X^{2K_0-1}$ the fold is $f_1 + \alpha X^{2K_0-1} + \beta X^{2K_0}$, and the witnesses exist only at $\beta = 0$, $\alpha = z_W$: $M$ isolated points, error $M/|E|^2$. Multiplying the locators by a linear factor $X + c$ to use $\beta$ as well moves $c$ into the top coefficients, which must be fixed. By Lemma B, a full line of bad challenges needs either the pole shape, which puts all varying coefficients back below degree $d + 1$ (a list), or a different agreement set for each challenge. I found no construction of the second kind and no proof that none exists. This is consistent with [CWYZ26, Thm. 4.10]: above Johnson the affine error is of order $1/|E|$, and the scalar counterexamples there (Prop. 6.1 to 6.3) do not apply.

### 3.7 Generic counting

**[proved]** (the "prescribed top" family of the prize's 122.33 certificate, and the capacity bound of [ABF26, Lemma 3.7].) The $T$-subsets $J \subseteq D$ have locators in $K[X]$; the $r = T - K_0$ coefficients between degrees $K_0$ and $T - 1$ take at most $2^{64r}$ values, so some class has $\ge \binom{n}{T}/2^{64r}$ members and the word $L_{J_0}$ agrees with each $L_{J_0} - L_J$ on $T$ points. This gives lists of any size $2^b$, $b \le 40$, at $T/n = \rho + r/n$ with $r/n = 0.0156, 0.0130, 0.0089, 0.0056, 0.0034, 0.0012$ for $\rho = 1/2, \dots, 1/32, 1/128$ ($N = 25$): always below flats. It is the reason capacity cannot be reached with a 64-bit word alphabet at level 0, and nothing more.

### 3.8 Classical and near-capacity results

- [GR05] **[quoted]**: the number of polynomials over $\mathbb{F}_{q^m}$ of degree $\le (q^m-1)/(q-1)$ with values in $\mathbb{F}_q$ on the whole field is $q^{2^m}$ (Thm. 1), which shows that list *recovery* with input lists of size $\lceil n/k \rceil$ needs super-polynomial output (Thm. 3). Its list-decoding consequences are at vanishing rate. Not applicable at our rates.
- [JH01] **[not obtained]**: per [BKR06] it gives super-polynomial lists for $K_0 = n^\delta$ at agreement about $n^\delta$, and per [DKTZ26] lists of linear size at the Johnson radius. [ABF26, Thm. 3.14] quotes a form with block length $j + 1$. I cannot say more.
- [CS25], [KKH26], [DG25] **[quoted from abstracts and from ABF26, Thm. 4.16, 4.17]**: counterexamples within $O(1/\log n)$ of capacity, in every characteristic. Irrelevant below Johnson by a constant.
- [GYXK26] **[quoted, abstract]**: a list-decoding counterexample of size $L$ gives MCA error $\ge \lceil (L+1)q/(q+L) \rceil / q$ for a code that differs in one evaluation point. Lemma A is the Reed-Solomon case without changing the code.
- [ABF26, April version, Section 6.4] **[quoted]**: Lemma 6.10, the one-round reduction (Construction 6.9) has error $\le \varepsilon_{\mathrm{mca}}(C, \delta) + |\Lambda(C^{\equiv 2}, \delta)|/|F|$. Definition 6.11, the winning set $\Omega$. Lemma 6.12, if $|F| > \binom{|\Lambda(C^{\equiv 2},\delta)|}{2}$ the error is at least $|\Lambda|/(|F| + |\Lambda| - 1)$: choose the claim vector $v$ so that list members have distinct claim values, pick $(\mu_1, \mu_2)$ off the list, and each member wins for one $\gamma$. Lemma 6.13, the error is at least $\varepsilon_{\mathrm{ca}}(C, \delta)$ (zero claim). Remark 6.14, no attack reaching $\varepsilon_{\mathrm{mca}}$ rather than $\varepsilon_{\mathrm{ca}}$ is known. Lemma 6.12 is the scalar analogue of the lead's "each member has its own conic". Beyond Johnson the survey lists as known limits only [BKR06], [GHSZ02], [JH01] for lists and [BCHKS25, Cor. 1.7], [BGKS20, Lemma 3.3] for CA in characteristic two, and stresses that the latter leave prime fields with smooth domains open. It predates [DKTZ26] and [Zhu26].

### 3.9 The Proximity Prize binary upper track

Profile: $n = 2^{21}$, rate 1/2, $\mathrm{GF}(2^{64})^3$, scalar combiner, so a certificate needs more than $2^{64}$ winning challenges. Progression (from the writeups): 122.33 bits, generic prescribed top (Section 3.7), $T = n/2 + 32743$; 116.81, a coset pencil (unions of 67 of the 128 cosets of a fixed $W$ plus the core $W \setminus 0$, top coefficients $e_1, e_2$ of the label locator fixed by pigeonhole); 114.11, 68 cosets with $(e_1, e_2, e_3)$ fixed at a cost of 35 bits instead of 192 (the writeup's explanation is cut off in the payload; presumably because the labels form a 7-dimensional $\mathbb{F}_2$-space); 106.25, the height-3 trees of [DKTZ26] at $9n/16$; 106.24, the same one level down on the labels of a 64-point fibration, with a 63-point core and a non-tree family of $2^{65.7}$ label sets (three cosets and three flats, `LabelFamily.lean`), $T = 9n/16 + 63$.

What transfers: the pole pair (Lemma A), mixed-size unions (Lemma C), and the remark that characteristic two makes several top coefficients cheaper than 64 bits each when the sets are unions of cosets of one subspace. What does not: the size requirement. In prize units $5n/8$ would be 86.8 bits but has only $2^{25.4}$ members at $n = 2^{21}$.

## 4. Transfer: the table

Largest agreement $T/n$ at which I can exhibit a family of the given size, for $N = 25$ ($n = 2^{25}$) at every rate. Each cell gives $T/n$, then $\log_2$ of the family size, then the construction. Degree $\le K_0$ throughout (so these are lists for $\Lambda$ and pole-pair families at once, Lemma A). **Genuine codewords: the same cell with one agreement point fewer**, and with the factor $2^c$ of affine translates removed for flats (Sections 3.1 to 3.3). "ph" marks non-constructive pigeonhole families.

| $\rho$ | Johnson $\sqrt\rho$ | size $\ge 2^{10}$ | size $\ge 2^{26}$ | size $\ge 2^{40}$ |
| --- | --- | --- | --- | --- |
| 1/2 | 0.7071 | 0.628 (10.0, biased padding); 0.625 (29.4, $h = 2$ trees) | 0.625 (29.4) | 0.5625 (102.7, $h = 3$ trees) |
| 1/4 | 0.5 | 0.5 (26.0, hyperplanes: $2n - 2$) | 0.375 (27.8, flats beside $W$); 0.5 as soon as $N \ge 26$ | 0.3125 (47.4, flats in a coset) |
| 1/8 | 0.3536 | 0.25 (49.4, flats) | 0.25 | 0.25 |
| 1/16 | 0.25 | 0.125 (70.6, flats) | 0.125 | 0.125 |
| 1/32 | 0.1768 | 0.0771 (25.7, padded ph); 0.0625 (89.7, flats) | 0.0625 | 0.0625 |
| 1/128 | 0.0884 | 0.03125 (42.7, ph, $4\rho$) | 0.03125 | 0.03125 |

Status: the rate-1/2 and rate-1/4 cells and all flats cells are **[proved]** and explicit; the 0.628 cell is **[proved]** with the set $B$ **[checked]** ($2^{10}$ members at 0.6281, 1008 at 0.6289); the "ph" cells are **[proved]** existence statements.

Remarks on the table.

- Dependence on $N$. Flats and trees scale as shown in Section 3. The pigeonhole cells move fast: each unit of $N$ adds $c$ bits. At rate 1/32 the unpadded $4\rho n = n/8$ family has $2^{6.6}, 2^{9.6}, 2^{12.6}$ members for $N = 25, 26, 27$. At rate 1/16 the padded family at $(2.5\rho - \rho^2)n = 0.152n$ has $2^{6.6}$ members for $N = 25$ and $2^{15.6}$ for $N = 28$, the level-0 size at that rate. At rate 1/8 the pigeonhole gives nothing above flats for $N \le 28$ (exponent $-8.6$ for the padded family at $N = 28$).
- Query floors $\lceil 108/\log_2(n/T) \rceil$ at budget $2^{10}$: rate 1/2, 161 (160 from the $5/8$ tree family alone) against 218 deployed; rate 1/4, 108 against 109; rate 1/8, 54 against 73; rate 1/16, 36 (40 at $N = 28$) against 55; rate 1/32, 30 against Johnson 44; rate 1/128, 22 against Johnson 31.
- At budget $2^{31}$ or more the rate-1/2 floor from known families falls back to 131 ($9n/16$), and the rate-1/4 threshold $n/2$ is no longer certified unsafe for $N \le 29$ (the hyperplane family has $2^{N+1} - 2$ members): the next families are at $3n/8$ ($2^{27.8}$ explicit at $N = 25$, about $2^{30.5}$ to $2^{34.5}$ by the Gold prediction, Section 3.5) and $5n/16$ ($2^{47.4}$).
- The rate-1/4 row does not contradict the lead notes: the gap is closed for budgets below $2n - 2$.

**Answers to the two open targets.** Rate 1/2, between $9n/16$ and $n/\sqrt2$: yes, $5n/8$ with $2^{29.4}$ members, and $0.628n$ with $2^{10}$; nothing known in $(0.632, 0.7071)$ beyond constant-size lists (3 codewords at $3n/4$). Low rates, between $2\rho n$ and $\sqrt\rho\,n$: only the 64-bit pigeonhole, which reaches $4\rho n$ at $\rho \le 1/64$ and roughly $2.5\rho n$ at $\rho = 1/32$ and (for $N = 28$) $1/16$, and the Gold prediction at rate 1/4 below the threshold. For pure MCA with a scalar combiner the answer would be different (Johnson at rate 1/16, Section 3.6).

## 5. Upper bounds and positive results beyond Johnson

None applies to $\mathbb{F}_2$-subspace domains. What exists:

- **Johnson / Guruswami-Sudan**, every field and domain: the proven side today.
- **A constant number of positions beyond Johnson**, every field and every evaluation set: [Jo26] proves at most $O_{r,h}(K_0^6)$ bad scalar parameters at $h$ positions beyond the exact Johnson boundary, at rate $1/r$. Relative gain $O(1/n)$. [DKTZ26, Thm. 4.1] shows the count is at least quadratic there on additive domains.
- **Large characteristic only**: [BCPZZ26] (prime fields, $q \ge C n$), [Jer26] (prime $q \ge n$, or characteristic $> \max(k-1, B_\epsilon)$), [DKT26] (first-order threshold $a_1(\rho) < \sqrt\rho$, list $O(n/\eta^2)$, scalar MCA $O(n^2/(q\eta^4))$), [Gab26] (linear lists at a constant below Johnson, characteristic $> k$). All differentiate the interpolant and need the characteristic to exceed its degree (or $k$), which excludes binary fields. [CWYZ26, Section 1.2] announces a slightly-beyond-Johnson affine bound "using the one derivative interpolator" by analogy with these, without a characteristic claim; I would not count on it for binary fields.
- **Other evaluation points in characteristic two**: random points reach capacity ([GZ23], [AGL24] with $q \ge n + k\,2^{O(1/\epsilon^2)}$, [GG25] for proximity gaps); [AGG26] gives explicit points over extension fields of polynomial size (subspace designs), binary included; [CGGGRZ26] deterministic quasi-polynomial constructions. None of these point sets is an additive subgroup, so none supports the additive NTT. [DKTZ26, Section 8] poses exactly this as open: an explicit family of binary domains with fast encoding and beyond-Johnson gaps.
- **Generic reductions**: [GCXK25] ([ABF26, Thm. 5.1]), list size $L$ at radius $\delta$ gives MCA at $1 - \sqrt{1 - \delta + \eta}$ with error $O(L^2 n/(\eta|F|))$, a square-root loss; [KTZ26], general linear codes have gaps up to the 1.5-Johnson radius and no further. Neither gets beyond Johnson for Reed-Solomon.
- **Exact classifications at Johnson on subspace domains**: [DKTZ26, Thm. 4.7] (rate 1/4, exactly $2n - 2$ challenges at $n/2$) and Thm. 4.1 parts 2 and 3 (rate 1/16, exactly $(n-1)(n-2)/6$ at $n/4 - 1$, none at $n/4$). They hold for one specific pair each, and rest on the lemma that an inner factor of an additive polynomial under an additive outer polynomial is additive. They are the only upper bounds I found that use the subspace structure.

On the negative side, for lists growing with $n$: dense additive domains have $n^{\Omega(\log n)}$ codewords at $1/2 - o(1)$ at rate 1/4 and at $5/8 - o(1)$ at rate 1/2 ([DKTZ26, Cor. 5.2, 5.15], [Zhu26]); every additive domain has the families of Section 4. Between these and $\sqrt\rho$ nothing is known in either direction.

## 6. What to try next

1. **Decide the list budget before anything else.** The frontier families are small ($2^{29.4}$ at rate 1/2 and $5n/8$, $2^{26}$ to $2^{27}$ at rate 1/4 and $n/2$). A proof target of the form $\Lambda(T) \le 2^{b}$ with $b \approx 32$ to $36$ and $T$ just above $9n/16$ (rate 1/2) or just above $3n/8$ (rate 1/4) is not excluded by anything in the literature. Conversely a target with $b \le 29$ is dead at $5n/8$.
2. **Classify the sets of size $5n/8 < T < n/\sqrt2$ with a locator gap, at toy sizes.** The exact question: for $D$ of dimension 6 to 9 in a field with no small subfield containing it, list all $T$-sets $S$ with $L_S = (\text{fixed top}) + (\text{degree} \le n/2)$ in classes of size $\ge 3$. Equivalently, find binary words of weight $2(T - |S_i \cap S_j|)$ whose two halves have locators agreeing in the top $T - n/2$ coefficients. Unions of flats are exhausted (Section 3.3), so anything found is new, and an empty answer at toy size would guide a proof.
3. **Extend the additive-composition classification** ([DKTZ26, Lemma 3.10, Thm. 4.7]) from one word to all words at rate 1/4, $T$ slightly below $n/2$, and to the word $X^{n/2}L_W$ at rate 1/2 above $5n/8$. It is the only proof technique in sight that sees the subspace.
4. **Exhibit a Gold solution on the real domain.** One collision among the plane products $\omega_a\omega_b(\omega_a + \omega_b)$ of the 25- or 26-dimensional label space (a 64-bit birthday over $2^{49}$ planes, so about $2^{32}$ evaluations and a sort) gives an explicit rank-4 solution and 16 codewords at $3n/8$, and confirms the prediction of Section 3.5 where it matters. Needs compiled code and several GB.
5. **Exploit the 64-bit key structure.** The prize's observation that $(e_1, e_2, e_3)$ of a label set costs 35 bits, not 192, suggests looking for families on our domain whose keys live in a small $\mathbb{F}_2$-space, which would make the pigeonhole of Section 3.2 cheaper than 64 bits per coefficient and push low rates above $2\rho n$ at $N \approx 25$.
6. **Non-pole MCA for the affine combiner.** By Lemma B this needs a family of agreement sets indexed by a line of challenges, all distinct. Translation ($x \mapsto x + a$, $a \in D$) is the one symmetry that preserves $D$ and acts on $\alpha + \beta x$; a family closed under it is the natural candidate. Low priority: the claim-bound analysis of the main document removes pure MCA anyway.

## 7. Reproduction

`scripts/01_checks.py` (pure Python, under 5 seconds in total): `A` the height-2 trees at $N = 7$ (count, degrees, agreements, genuine variant, pole pair under the affine fold); `B` hyperplane coefficients and the collision statistics of $a_W$ at $N = 10$; `C` the biased-padding identity at $N = 8$ and the Walsh spectra; `D` the Gold moment equation on sparse analogues ($d = 8$; call `check_D(9)`, `check_D(10)` for the other two); `E` the family sizes used in Section 4 and the Gold predictions. `scripts/01_tree_padding.py` (about 20 seconds) is the padding-set check of Section 3.3 at $N = 6$. Field $\mathrm{GF}(2^{16})$ with modulus $x^{16} + x^{12} + x^3 + x + 1$, domain $\mathrm{span}(1, \dots, x^{d-1})$.

## References

- [ABF26] G. Arnon, D. Boneh, G. Fenzi. Open Problems in List Decoding and Correlated Agreement. ePrint 2026/680 (April 2026 version read).
- [AGG26] O. Alrabiah, R. Goyal, V. Guruswami. Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding. ECCC TR26-262.
- [BCHKS25] E. Ben-Sasson, D. Carmon, U. Haböck, S. Kopparty, S. Saraf. On Proximity Gaps for Reed-Solomon Codes. ECCC TR25-169.
- [BGKS20] E. Ben-Sasson, L. Goldberg, S. Kopparty, S. Saraf. DEEP-FRI. ITCS 2020.
- [BKR06] E. Ben-Sasson, S. Kopparty, J. Radhakrishnan. Subspace Polynomials and List Decoding of Reed-Solomon Codes. FOCS 2006.
- [CGGGRZ26] A. Chatterjee, S. Ghosh, Z. Guo, R. Gurjar, R. Raj, Z. Zhang. Deterministic Constructions of Reed-Solomon Codes Beyond the Johnson Bound. arXiv:2610.31922.
- [CWYZ26] A. Chiesa, G. Weissenberg, E. Yogev, K. Z. Zheng. Affine Combiners for Reed-Solomon Proximity Gaps. ePrint 2026/2863.
- [DKT26] Q. Dao, S. D. Kominers, J. Thaler. Reed-Solomon Codes Beyond Johnson. ePrint 2026/2056.
- [DKTZ26] Q. Dao, S. D. Kominers, J. Thaler, K. Z. Zheng. Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields. ECCC TR26-237, revision 1.
- [Gab26] A. Gabizon. Linear list size bounds for Reed-Solomon beyond the Johnson radius. ePrint 2026/2048.
- [GR05] V. Guruswami, A. Rudra. Limits to List Decoding Reed-Solomon Codes. STOC 2005.
- [GYXK26] Y. Gao, H. Yang, Y. Xu, H. Kan. List-Decoding Counterexamples Yield Lower Bounds on Mutual Correlated Agreement Error. arXiv:2607.10572.
- [JH01] J. Justesen, T. Høholdt. Bounds on list decoding of MDS codes. IEEE Trans. Inf. Theory 47 (2001). Not obtained.
- [Jo26] S. Jo. Reed-Solomon Mutual Correlated Agreement Beyond the Johnson Radius. ePrint 2026/1432.
- [Zhu26] M. Zhu. Superpolynomial Lists for Reed-Solomon Codes over Binary Extension Fields. arXiv:2610.15815.
- Cited through the above only: [BCPZZ26], [Jer26], [GZ23], [AGL24], [GG25], [GCXK25], [KTZ26], [CS25], [KKH26], [DG25], [GHSZ02].
