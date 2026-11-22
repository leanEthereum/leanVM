# 07. Protocol redesign: combiners and round structure

Researcher 07. Scope: changes to the fold and to the round structure of Annex B, with for each a verdict, the math, and the cost. Notation as in `doc/whir_soundness_gap.md` and `00-lead-notes.md`: $q = |E| = 2^{128}$, a level has domain $D$ of size $n$, analysis degree $d$, threshold $A$, $\ell$ fold rounds, and $t = \lceil 108/\log_2(n/(A-1)) \rceil$ queries. Statuses: **[proved]** (proof in this note), **[checked]** (numerically, sizes given), **[sketch]** (argument outlined, not written out in full), **[conjectured]**, **[quoted]**. Nothing here is machine-checked.

## 0. Findings in one page

1. **No change of combiner helps.** A combiner of any degree $r$ in $x$ (quadratic included), a multi-lane combiner, or one fold of several lane variables at once all keep the two terms that bind today, (pole pairs)$/q$ and $2L/q$. Only the already negligible $n^2/q^2$ improves, to $(n/q)^{r+1}$. The pole pair collapses every combiner that is polynomial in $x$ onto one scalar, so each bad scalar is a hyperplane of challenges. The affine combiner is the right degree. **[proved]** for the lower bounds, **[sketch]** for the upper bound.
2. **Mutual correlated agreement is not needed at all. A list bound is enough.** If the prover answers $s$ out-of-domain evaluations of the two halves *before* the fold challenge, and these claims are folded individually (never batched into the running claim before the challenge), then for all but a $4\Lambda^3 q^6 \epsilon^s / K_0^3$ fraction of the points, and whatever the prover answers, fewer than $K_0$ of the $q^2$ challenges give a folded word with a close codeword that satisfies the folded claims (when no close pair satisfied the claims before the round), for any $K_0 \ge 2.72\,q$. Here $\Lambda$ is the list size at the threshold and $\epsilon \approx d/q$. The proof is Schwartz-Zippel, Markov and counting: no interpolation, no Hensel lifting, no Johnson hypothesis. It holds at every threshold, beyond Johnson included. **[proved]** (Theorem 3), **[checked]** by brute force on $\mathrm{GF}(2^5)$, where a pole-pair word with a close codeword at 992 of 1024 challenges lets one answer vector win exactly $q = 32$ of them.
3. **Consequences for the error terms.** The fold round's error becomes $K_0/q^2$, with no list factor and no pole-pair factor. Batching becomes $(J-1)/q$, with no list factor, because the answers pin one list member. Lists enter only through the point message, cubed, against $\epsilon^s$: each extra point buys about 35 more bits of list at level 0. With 12 points at level 0 and 8 or 9 at the later levels, lists of $2^{40}$ are affordable everywhere; with 14 and 10 or 11, lists of $2^{100}$. Cost at $\mu = 30$: about 3 to 4 KiB of proof, $s$ inner products over the stack fused into one pass at commit time, and nothing measurable for the verifier. **[proved]** for the lemma, **[sketch]** for the round-by-round composition.
4. **What remains is exactly one statement per level: `ListBound` at the lowered threshold, with $L$ up to $2^{40}$ or $2^{100}$ instead of $2^{10}$.** Nothing about challenges. Whether that bound holds below Johnson on our subspace domains is open (note 01, section 5); the known families leave room (rate 1/2: nothing known between $0.632\,n$ and $0.707\,n$, and only $2^{29.4}$ members at $5n/8$). With the counting bound $\binom{n}{d+1}/\binom{A}{d+1}$ the last level of every ladder is provable today near capacity (15 queries to 9), which is small but exercises the whole mechanism (**[proved]** up to the composition sketch of section 3.4).
5. **The present protocol cannot be re-analysed this way.** With one out-of-domain point batched into the running claim, the same method gives an error of order $\Lambda (\mu/q)^{1/6}$. So the gain needs a protocol change. **[proved]**.
6. **Round structure.** Queries cannot move before the next commitment. Fewer variables per level, a steeper rate schedule and one level fewer move the proof by 2 to 8 percent at Johnson thresholds; these are parameter questions for note 08. Grinding buys $1/b$ queries per bit at $b$ bits per query, so it only pays at level 0.

Ranked shortlist in section 7.

## 1. What I verified of the lead's facts

- **Queries per level. [checked]** `scripts/07_deep_fold_params.py`, table 1: with the Johnson threshold $A = \lfloor\sqrt{nd}\rfloor + 1 + \ell$ the formula gives 217, 55, 31, 22, 17, 14 at rate 1/2 against the deployed 218, 55, 32, 23, 18, 15, and is within one query everywhere except the last one or two levels at rates 1/4 to 1/16 (two above). Capacity would halve every count: 109, 28, 16, 11, 9, 7.
- **Lists enter the fold round as $L/q$. [proved]** in Annex B, event $B_2$ of `lem:fold-list`: each list pair has a nonzero residual of degree 2 in $(\alpha, \beta)$, hence at most $2q$ zeros.
- **Pole collapse. [proved]** and extended to every degree in section 2.1; **[checked]** on $\mathrm{GF}(2^5)$ for $r = 1, 2, 3$ (test T3).
- **One refinement of the main document's 4.3** (found independently; note 03, section 3.4, has the complete case analysis). "With a nonzero weight each line keeps at most two escapes" holds for all but a constant number of lines, not for all. **[proved]** for one line: take $f_0 = 1/(x - \beta_0)$ and $f_1 = G$ a codeword. No pair is close to $(f_0, f_1)$, so every claim $c$ is violated. On the line $\alpha = \beta\beta_0$ the fold is the codeword $G + \beta$, and the folded claim holds identically in $\beta$ if the prover sends $v_G = g_0$, $s_0 = w_0 + \beta_0(g_1 + c)$, $s_1 = s_0 + w_0 + w_1 + \beta_0 v_F$, with $g_\iota = \langle W_\iota, G\rangle$, $w_\iota = \langle W_\iota, 1\rangle$ and $v_F$ free (three coefficient equations, four free values). So $\Gamma \ge 1/q$ for every weight, which is the term $\ell_B/q$ of the affine MCA bound and is harmless. For a family of $N$ parallel pole lines the prover's remaining freedom wins one line in general and at most two points on each other line, so $\Gamma \approx 1/q + 2N/q^2$ **[conjectured]** in general, computed for the pole shape.

## 2. Combiners

### 2.1 Higher degree: $C_\alpha(x) = \alpha_0 + \alpha_1 x + \dots + \alpha_r x^r$

Fold $f_1 + C_\alpha(x) f_0$ with $r + 1$ challenges; an honest $f_0$ has degree at most $d - r$, the degree grows by $r$ per round, and the prover sends about $2r + 2$ values per round for the claim.

**Lower bound, every $r \ge 1$. [proved]** For $x_0 \in E \setminus D$,
$$\frac{C_\alpha(x)}{x - x_0} = \frac{C_\alpha(x) - C_\alpha(x_0)}{x - x_0} + \frac{C_\alpha(x_0)}{x - x_0},$$
and the first term is a polynomial of degree $r - 1$, a codeword. So with $f_0 = 1/(x - x_0)$ the fold depends on $\alpha$ only through the scalar $\gamma = C_\alpha(x_0)$, up to a codeword. With $f_1 = 0$ the fold is a codeword on the hyperplane $C_\alpha(x_0) = 0$, a $1/q$ fraction of the challenges, while $f_0$ agrees with no polynomial of degree at most $d$ on more than $d + 1$ points. With $f_1 = w/(x - x_0)$ and a list of $N$ codewords around $w$ (note 01, Lemma A), each list member gives one hyperplane $C_\alpha(x_0) = \gamma_i$: pure MCA error at least about $N/q$, exactly as for $r = 1$. The same identity applies to any combiner whose coefficient is a polynomial in $x$ with coefficients linear in the challenges, in particular to a multi-lane combiner $\sum_u c_u(x) f_u$ (all lanes with the same pole: one linear condition $\sum_u c_u(x_0) g_u = 0$) and to several lane variables folded at once with a tensor of affine factors.

**List members. [proved]** A list pair with a false claim has a nonzero residual polynomial in the challenges, of degree 2 (the lane variable of the weight is evaluated at $\alpha_0$, as today). It vanishes on a hypersurface: at most $2/q$ of the challenges for any $r$. The term $2L/q$ is unchanged.

**Upper bound. [sketch]** The three counts of [CWYZ26, Section 4] go through with $Y = C_\alpha(X)$. Excluded challenges: still at most $D^2$ in number, since distinct $\alpha$ give distinct factors $Y - C_\alpha(X)$. Persistent pairs: a polynomial pair needs $r + 1$ accidental agreements to pin $\alpha$ (hyperplanes with Vandermonde normals $(1, x, \dots, x^r)$), giving $\binom{n}{r+1}$ challenges with agreement loss $r$; a rational pair with a denominator of degree 1 keeps a subspace of dimension $r$, that is $q^r$ challenges. Nonpersistent: algebraic sets of dimension $r + 1$, giving $O(n^{r+1})$. Altogether
$$\varepsilon^{(r)} \le \frac{\ell_B}{q} + O_{\rho,\eta}\!\left(\frac{n^{r+1}}{q^{r+1}}\right), \qquad \text{agreement loss } r .$$
The leading term is the one we have. [CWYZ26, Section 7] gets $q^{-k}$ for Reed-Muller codes only because there a denominator is a linear form in $k$ variables and keeps a subspace of dimension 1 out of $k + 1$; in one variable a denominator of degree 1 always keeps codimension 1.

**Verdict: does not help.** At $q = 2^{128}$ and $n \le 2^{28}$ the improved term is already below $2^{-200}$ for $r = 1$. It allows no smaller field (the floor $1/q$ per pole pair and $2/q$ per list member is in the field of the challenges) and no fewer grinding bits (the 7 fold bits pay for $(\ell_B + 2L)/q$). It costs $r$ coordinates of agreement per round, more prover values, and a higher degree slack.

### 2.2 Other shapes

- **Rational in $x$**, for example a factor $1/(x - \gamma)$ with $\gamma$ random: an honest fold is a codeword only if the numerator vanishes at $\gamma$, so this is the DEEP quotient $(f_0(x) - y)/(x - \gamma)$ with a claimed value $y$. It is a way to carry an out-of-domain claim inside the word instead of in the running claim. WHIR carries claims as weights, so the content of this idea is section 3. **[proved]** equivalence in effect, no separate gain.
- **Lane-dependent scalars** (a different scalar per lane, no $x$): the scalar combiner, MCA error $\Omega(n/q)$ [CWYZ26, Prop. 6.1]. Worse.
- **Several lane variables in one round**: same per-variable errors (a hybrid over the variables, as [CWYZ26, Thm. 5.2]), and the round message grows like $5^k$ coefficients for $k$ variables. Worse.
- **Challenges from an extension $E' \supset E$**, $|E'| = q^e$: every $1/q$ above becomes $1/q^e$, so lists of $2^{60}$ to $2^{70}$ fit the batching and OOD budgets at $e = 2$. But every later level's oracle and all arithmetic after the first challenge live in $E'$ (32-byte values: about 37 KiB more leaf data at $\mu = 30$, rate 1/2, and field products three to four times dearer), and it proves nothing new beyond Johnson. Section 3 gets the same effect on the list terms for bytes instead of field size. **Does not help.**

## 3. Lists made harmless, and the fold without MCA

### 3.1 Why a list member costs $1/q$ today, and what two unbatched claims do

Today every claim is batched into one running claim before the fold challenge. A list pair $U$ that violates it has one residual equation of degree 2 in $(\alpha, \beta)$: a conic, $2q$ challenges. The same happens at batching: one polynomial in $\lambda$ per list member.

**Lemma 0 (list members with $s$ unbatched point claims). [proved]** Let the prover have answered $s \ge 2$ evaluation claims at distinct points $\zeta_1, \dots, \zeta_s$ with values $(y^F_i, y^G_i)$ for the two halves, folded individually as $P(\zeta_i) = y^G_i + (\alpha + \beta\zeta_i)\,y^F_i$. A pair $U = (F, G)$ with $\delta_i := (F(\zeta_i) - y^F_i,\ G(\zeta_i) - y^G_i)$ satisfies folded claim $i$ exactly when $\delta^G_i + (\alpha + \beta\zeta_i)\,\delta^F_i = 0$. If $\delta_i \ne 0$ this is a line of slope $\zeta_i$ or the empty set. So: a pair wrong at two points wins at most one challenge; a pair wrong at exactly one point wins at most a line; a pair right at all points must violate the running claim and wins at most $2q$. If every $s - 1$ of the points separate the list (failure probability at most $s\binom{L}{2}\epsilon^{s-1}$), there are at most $s$ pairs of the second kind and one of the third. Explained escapes: at most $((s + 2)\,q + L)/q^2$.

So with unbatched claims a list member escapes on a point, not a curve, which is the "$4L/q^2$ instead of $L/q$" of the brief. Lemma 0 is subsumed by Theorem 3 below and is stated only to answer the brief's question on its own.

### 3.2 The DEEP fold lemma

**Setting.** $D \subseteq E$ of size $n$, $h \ge 1$ lanes, words $f_0, f_1 : D \to E^h$, integers $d + 1 < A \le n$. For a challenge $c = (\alpha, \beta)$ put $a_c(X) := \alpha + \beta X$, $w_c := f_1 + a_c f_0$, and let $\mathcal{L}(c)$ be the $h$-tuples of polynomials of degree at most $d$ that agree with $w_c$ on at least $A$ points. Let $\Lambda \ge |\mathcal{L}(c)|$ for all $c$. Let $\mathcal{L}_{\mathrm{pair}}$ be the pairs $(F, G)$ with $\deg F \le d - 1$, $\deg G \le d$ that agree with $(f_0, f_1)$ on at least $A - 1$ common points.

A *point* is $z = (r, \zeta) \in E^{\log_2 h} \times E$, with the functional $\mathrm{ev}_z(P) := \sum_u \mathrm{eq}(r, u)\,P_u(\zeta)$ on tuples. For a scalar polynomial $a$, $\mathrm{ev}_z(aP) = a(\zeta)\,\mathrm{ev}_z(P)$. For a nonzero tuple $Q$ of degree at most $d + 1$, $\Pr_z[\mathrm{ev}_z(Q) = 0] \le \epsilon := (d + 1 + \log_2 h)/q$ (Schwartz-Zippel, total degree).

The verifier draws $s$ independent points $z_1, \dots, z_s$; the prover answers $m = (y^F_i, y^G_i)_{i \le s}$; then $c$ is drawn. A pair $(c, P)$ is *$m$-consistent* if $\mathrm{ev}_{z_i}(P) = y^G_i + a_c(\zeta_i)\,y^F_i$ for all $i$. (Honestly $y^F_i = \mathrm{ev}_{z_i}(F)$, $y^G_i = \mathrm{ev}_{z_i}(G)$, and the fold $G + a_c F$ is $m$-consistent for every $c$, exactly, high parts included.)

**Lemma 1 (dependency). [proved]** For three pairs $(c_j, P_j)$ with distinct challenges put $L_1 := a_{c_2} + a_{c_3}$, $L_2 := a_{c_1} + a_{c_3}$, $L_3 := a_{c_1} + a_{c_2}$ and $Q := L_1 P_1 + L_2 P_2 + L_3 P_3$, a tuple of degree at most $d + 1$ that depends on the three pairs only.
(a) If the three pairs are $m$-consistent for one $m$, then $\mathrm{ev}_{z_i}(Q) = 0$ for all $i$.
(b) If $Q = 0$ (the triple is *dependent*), then with the rational tuples $F := (P_1 + P_2)/L_3$ and $G := P_1 + a_{c_1} F$ we have $P_j = G + a_{c_j} F$ for $j = 1, 2, 3$.

*Proof.* In characteristic two $L_1 + L_2 + L_3 = 0$ and $L_1 a_{c_1} + L_2 a_{c_2} + L_3 a_{c_3} = 2(a_{c_1}a_{c_2} + a_{c_1}a_{c_3} + a_{c_2}a_{c_3}) = 0$. (a): $\mathrm{ev}_{z_i}(Q) = \sum_j L_j(\zeta_i)\,(y^G_i + a_{c_j}(\zeta_i)\,y^F_i) = 0$. (b): $P_2 = P_1 + L_3 F = G + (a_{c_1} + L_3) F = G + a_{c_2} F$, and $L_3 P_3 = L_1 P_1 + L_2 P_2 = (L_1 + L_2) G + (L_1 a_{c_1} + L_2 a_{c_2}) F = L_3 (G + a_{c_3} F)$ with $L_3 \ne 0$. $\square$

**Lemma 2 (a class is a line, a crossing set, or a list pair). [proved]** Let $W'$ be a set of pairs $(c, P_c)$ with distinct challenges and $P_c \in \mathcal{L}(c)$, containing two elements with which every other element is dependent. Let $(F, G)$ be the rational pair of Lemma 1(b), so $P_c = G + a_c F$ on $W'$.
(i) If $|W'| > q$, then $F$ and $G$ are polynomial tuples with $\deg F \le d - 1$, $\deg G \le d$.
(ii) If moreover $|W'| > \binom{n}{2}$, then $(F, G) \in \mathcal{L}_{\mathrm{pair}}$.

*Proof.* (i) For two elements, $P_c + P_{c'} = (a_c + a_{c'})\,F$ is a polynomial tuple of degree at most $d$, and $a_c + a_{c'}$ is a nonzero polynomial of degree at most 1. If some component of $F$ is not a polynomial, its denominator in lowest terms divides every $a_c + a_{c'}$, so it is $X - x_0$ and all challenges of $W'$ satisfy $\alpha + x_0\beta = \text{const}$: a line, $|W'| \le q$. If $F$ is a polynomial tuple and all challenges share $\beta$, again a line. Otherwise some $a_c + a_{c'}$ has degree 1, so $\deg F \le d - 1$, and $G = P_c + a_c F$ has degree at most $d$. (ii) Let $Z := \{x \in D : F(x) = f_0(x),\ G(x) = f_1(x)\}$. For $(c, P_c) \in W'$ and $x \notin Z$, $P_c(x) = w_c(x)$ means $(G - f_1)(x) = a_c(x)\,(f_0 - F)(x)$ in $E^h$, which forces $(f_0 - F)(x) \ne 0$ and fixes the scalar $\alpha + \beta x$. Two such points $x \ne x'$ determine $c$. So at most $\binom{n}{2}$ challenges have two agreement points outside $Z$, and some element of $W'$ has at most one: $|Z| \ge A - 1$. $\square$

**Theorem 3 (DEEP fold). [proved]** Let $K_0 \ge 30$. Over the choice of $z_1, \dots, z_s$, except with probability at most
$$\varepsilon_{\mathrm{pt}} := \frac{4\,\Lambda^3 q^6\,\epsilon^s}{K_0^3},$$
the following holds for every answer vector $m$ and every set $W$ of $m$-consistent pairs $(c, P_c)$ with distinct challenges, $P_c \in \mathcal{L}(c)$ and $|W| \ge K_0$: there is $W' \subseteq W$ with $|W'| \ge 0.74\,|W|$ on one rational pair as in Lemma 2. In particular, if $0.74\,K_0 > \max(q, \binom{n}{2})$, the pair $(F, G)$ is in $\mathcal{L}_{\mathrm{pair}}$, is consistent with the answers ($\mathrm{ev}_{z_i}(F) = y^F_i$, $\mathrm{ev}_{z_i}(G) = y^G_i$), and $P_c = G + a_c F$ on $W'$.

*Proof.* Let $\mathcal{T}$ be the set of all pairs $(c, P)$ with $P \in \mathcal{L}(c)$, so $|\mathcal{T}| \le \Lambda q^2$; it is fixed by $(f_0, f_1)$. Let $N(z)$ be the number of ordered triples of $\mathcal{T}$ with distinct challenges that are not dependent and have $\mathrm{ev}_{z_i}(Q) = 0$ for all $i$. The points are independent and $Q \ne 0$ does not depend on them, so $\mathbb{E}[N] \le \Lambda^3 q^6 \epsilon^s$, and by Markov $N(z) < K_0^3/4$ except with probability $\varepsilon_{\mathrm{pt}}$. Assume $N(z) < K_0^3/4$ and let $W$ be as stated, $K := |W| \ge K_0$. By Lemma 1(a) every triple of $W$ has $\mathrm{ev}_{z_i}(Q) = 0$, so fewer than $K^3/4$ ordered triples of $W$ are not dependent, and some ordered pair of elements has fewer than $K^2/(4(K - 1))$ non-dependent third elements. Let $W'$ be that pair with the elements dependent with it: $|W'| > K - K^2/(4(K-1)) \ge 0.74\,K$. Lemma 2 applies. For the consistency of $(F, G)$ with $m$: for each $i$ the elements of $W'$ with one value of $a_c(\zeta_i)$ lie on a line, so two elements have different values, and the two equations $\mathrm{ev}_{z_i}(G) + a_c(\zeta_i)\,\mathrm{ev}_{z_i}(F) = y^G_i + a_c(\zeta_i)\,y^F_i$ give the claim. $\square$

**Corollary 4 (the fold round, with its claim). [proved]** Suppose no pair of $\mathcal{L}_{\mathrm{pair}}$ that is consistent with the answers satisfies the running claim $(W, c)$. Let $K_0 \ge 2.72\,q$ and $\binom{n}{2} \le 2q$. For points outside the exceptional set of Theorem 3, and for every answer vector and every round message $(v_G, v_F, \sigma_0, \sigma_1)$, fewer than $K_0$ challenges $c$ have some $P \in \mathcal{L}(c)$ that is $m$-consistent and satisfies the folded running claim. So the fold challenge errs with probability at most $K_0/q^2$.

*Proof.* Otherwise Theorem 3 gives $(F, G) \in \mathcal{L}_{\mathrm{pair}}$, consistent with the answers, whose fold satisfies the folded running claim on $|W'| \ge 0.74\,K_0 > 2q$ challenges. But $(F, G)$ violates the running claim, so by the argument of `lem:fold-list` the residual is a nonzero polynomial of degree 2 in $(\alpha, \beta)$, with at most $2q$ zeros. $\square$

Remarks.

- **No list factor and no pole-pair factor in the fold error.** A pole pair wins its one line and no more, because the answers at the points are the values of one rational pair. A family of $N$ pole pairs, which breaks pure MCA with error $N/q$, costs the same $1/q$ as one: the prover must choose which member to answer for before the challenge.
- **No Johnson hypothesis.** The threshold $A$ is arbitrary. The only input from the code is $\Lambda$.
- **Agreement loss one, degree bound unchanged.** The explaining pair has degrees $(d - 1, d)$ and agreement $A - 1$, exactly as in `thm:mca-affine`, so the thresholds $A - (\ell - j)$ and the level degree $d = 2^\kappa - 1 + \ell$ stay as they are. This is where the affine combiner is used (Lemma 2(ii)): with a scalar combiner the lines of different points coincide, and one needs an agreement loss $a$ to get $(n/a)/q$ (section 3.6).
- **Why the points must be univariate in the coefficient variable.** A claim of Annex B weighs only the low part. A multilinear point would give $Q$'s low part zero and say nothing of its high part, and the answer for $XF$ would be a third free value. Evaluation of the whole polynomial at $\zeta$ commutes with the fold exactly ($(XF)(\zeta) = \zeta F(\zeta)$), which gives two answers per point and Lemma 1 as stated. The weight $(\mathrm{novel}_v(\zeta))_v$ is the column weight of `lem:colweight` at a point outside $D$, so it is as MLE-friendly as a query's.
- **Relation to the literature.** This is the DEEP argument of [BGKS20] (sample outside the domain, then count collinear triples of close codewords), with three changes: several independent points, so the Schwartz-Zippel term is $\epsilon^s$ and the final error is of order $1/q$ instead of a cube root; the affine combiner, so no factor $n$; and the bookkeeping for a claim-carrying fold. STIR and WHIR use out-of-domain samples to pin a list member but still invoke correlated agreement for the fold. I state the [BGKS20] comparison from memory, **[quoted]** without recheck.

### 3.3 Numerical check

`scripts/07_deep_fold_check.py` (pure python, about 35 seconds). $E = \mathrm{GF}(2^5)$, $D = \mathrm{span}(1, x, x^2, x^3)$, $n = 16$, $d = 3$, $A = 6$, so $A^2 = 36 < nd = 48$: beyond Johnson, with lists of up to 13 codewords. For four pairs of words it computes the full list of every one of the 1024 challenges, then all dependency classes through 500 random anchors (T1), then the exact maximum over answer vectors at two points and its refinement at three and four points outside $D$ (T2). **[checked]**:

| word | challenges with a close codeword | largest class explained by a pair of $\mathcal{L}_{\mathrm{pair}}$ | largest other class | most challenges one answer vector wins, $s = 2, 3, 4$ |
| --- | --- | --- | --- | --- |
| random | 1024 | none | 60 | 63 to 65, 60, 60 |
| pair planted on $A - 1 = 5$ points | 1022 | 302 | 62 | 303 to 304, 302, 302 |
| pole pair, random numerator | 1024 | none | 32 | 20 to 64, 10 to 32, at most 32 |
| pole pair on $w = x^8$ (30 flats) | 992 | none | 32 | 32, 32, at most 32 |

Lemma 2 held for every class found: classes with a pole lie on one line ($\le q = 32$), and no unexplained polynomial class exceeds $\binom{n}{2} = 120$ (the classes of 60 are pairs agreeing on 4 common points, whose folds reach 6 only at the crossings of two of the 12 remaining lines, at most 66). From three points on, what one answer vector wins is exactly the largest class. The last row is the instance where pure MCA fails on 97 percent of the challenges. At this size $\epsilon = 1/8$ per point, so the probability bound of Theorem 3 is not what is being tested; the structure is. In the real setting a point falls in $D$ with probability $n/q$; the toy samples them outside $D$ to match.

### 3.4 A protocol that uses it

Two variants; both keep the affine fold, the running claim and the level structure.

**Variant P (points fixed per level, carried unbatched). Recommended.** Changes to Protocol B.1:

1. After each commitment the verifier sends $s$ points $z_i = (r_i, \zeta_i) \in E^{\ell} \times E$ instead of one multilinear point, and the prover answers $s$ scalars $y_i$, honestly $\mathrm{ev}_{z_i}$ of the committed tuple. At level 0 these are the commit-time points of `crate::ood`, so the outer protocol faces one pinned candidate as today.
2. In fold round $j$ the prover sends, with its four values for the running claim, one scalar per point: the value $y^F_i$ of the first half. The second half's value follows from the carried value: $v_i = (1 - r_{i,j})\,y^F_i + r_{i,j}\,y^G_i$ (the coordinate $r_{i,j}$ is zero with probability $1/q$, charged to the point message). After the challenge, $v_i \leftarrow y^G_i + (\alpha_j + \beta_j\zeta_i)\,y^F_i$. The point claims are never batched inside their level.
3. At the end of the level each point claim reads $P^{(i,\ell)}(\zeta_i) = v_i$ on the one folded polynomial. With the high part $\phi^{(i)}$, sent with the next commitment as today, it becomes the low-part claim $\langle W_{\zeta_i}, f^{(i+1)}\rangle = v_i - \hat W_\kappa(\zeta_i)\sum_s \phi_s\,\mathrm{novel}_s(\zeta_i)$ and joins the residual and consistency claims that $\lambda_{i+1}$ batches. The order of messages is today's: commit, points, answers, then queries with $\lambda$.

**Variant F (fresh points every round).** $s$ fresh points and $2s$ answers per round; the previous round's point claims are batched into the running claim by a $\lambda$ sent after the new answers. Fewer points ($s = 6$ at level 0), one more verifier message per round, about the same bytes.

**Round-by-round argument. [sketch]** Invariant inside a level: no member of the current list satisfies the running claim together with all carried point claims. Level entry: the answers pin at most one member $U^\ast$ of the new list (separation, probability of failure $\binom{\Lambda}{2}\epsilon^s$); the two cases of today's query argument show that $U^\ast$ violates the residual claim, a converted point claim or a consistency claim, except with probability $((A-1)/n)^t$; then $\lambda$ makes it violate the batch except with $(J - 1)/q$. No union over the list is needed, because the other members stay wrong on the unbatched point claims. Fold round: Corollary 4, where "consistent with the answers" for a pair of round $j$ means it satisfies the carried point claims, so by the invariant it violates the running claim. In variant P the points are not fresh for rounds $j \ge 2$, since the word of round $j$ depends on the earlier challenges; because the points and the challenges are independent, a nested Markov argument fixes this: call the points good for a word if they are outside the exceptional set of Theorem 3 and at most a $\tau$ fraction of the next challenges lead to a word for which they are not good, recursively. Then the points are bad with probability at most $2\,\varepsilon_{\mathrm{pt}}\,\tau^{-(\ell-1)}$, and each fold challenge errs with at most $K_0/q^2 + \tau$. Errors:

| message | today (`thm:rbr`) | variant P |
| --- | --- | --- |
| points after a commitment | $\binom{L}{2}\mu/q$ | $2\cdot 4\Lambda^3q^6\epsilon^s K_0^{-3}\,\tau^{-(\ell-1)} + \binom{\Lambda}{2}\epsilon^s$ |
| level 0 batching | $(J_0 - 1)L_0/q$ | $(J_0 - 1)/q$ |
| fold $(\alpha, \beta)$ | $\varepsilon_{\mathrm{aff}} + 2L/q$ | $K_0/q^2 + \tau$ |
| queries and next batching | $((A-1)/n)^t + (J - 1)L'/q$ | $((A-1)/n)^t + (t + s + 1)/q$ |
| tail | $2/q$ | $2/q$ |

What is not done: the composition is not written out as a full proof, knowledge soundness (the extractor) is not examined, and nothing is formalized.

### 3.5 Parameters and costs

From `scripts/07_deep_fold_params.py` (tables 2, 2b, 3), $\mu = 30$, rate 1/2 ladder, $K_0 = 2^8 q$ and $\tau = 2^{-120}$ (fold message $2^{-119}$, inside the present 7-bit grind), point message $2^{-111}$ (inside the 15-bit OOD grind). The condition is $s\,\log_2(1/\epsilon) \ge 3\log_2\Lambda + 474 + 120(\ell - 1)$. **[checked]** arithmetic.

| list bound $\Lambda$ | points per level $s$ (levels 0 to 5) | scalars sent, fold rounds and points | bytes |
| --- | --- | --- | --- |
| today | 1 multilinear point per level | 110 | 1.7 KiB |
| $2^{8}$ (Johnson-size lists) | 11, 8, 8, 8, 8, 7 | 272 | 4.2 KiB |
| $2^{40}$ | 12, 9, 9, 9, 8, 8 | 299 | 4.7 KiB |
| $2^{70}$ | 13, 10, 10, 10, 9, 9 | 331 | 5.2 KiB |
| $2^{100}$ | 14, 11, 11, 10, 10, 10 | 358 | 5.6 KiB |

One more point buys $\log_2(1/\epsilon)/3$ bits of list: 34.7 at level 0, 41 at the last level. Variant F with $s = 6$ per round: 4.9 KiB, lists up to $2^{48}$ at level 0.

- **Prover.** For each point, the 64 per-lane values $U_u(\zeta_i)$ at commit time: one inner product of the stack against the tensor weight $\mathrm{novel}_v(\zeta_i)$ per point, $s$ of them fused into one pass over memory ($2^{30}$ products $K \times E$ per point at $\mu = 30$; today's single OOD point is one such pass). Every later answer of the level is these 64 values folded with the challenges: no further pass. Later levels are $2^{6}$ times smaller. I did not measure it; I expect a low single-digit percentage of the proof.
- **Verifier.** Per point about $2\kappa + 2\ell$ field products (the $\hat W_b(\zeta)$, the weight at the final point, the per-round update), 55 points instead of 6: a few thousand products, against 25 to 29 Keccak permutations and about 130 products per level-0 query.
- **Grinding.** The fold round could do without its grind ($K_0 = 2.72\,q$ and $\tau = 2^{-126}$) for about one more point per level; keeping the 7 bits is what lets $K_0$ be $2^8 q$ and $\tau$ be $2^{-120}$.
- **Formal proof.** `FoldRoundBound` and the files `AffineCombiner*.lean` (interpolation, Hensel lifting, the factor count) are replaced by Lemmas 1 and 2 and Theorem 3: polynomial identities, divisibility by a polynomial of degree 1, root counting, Markov. The state function gains the nested condition on the points. `SafeLevel` becomes `list : ListBound P.dom P.deg (P.thr 0 - 1) L` plus one arithmetic inequality in $L$, $s$ and $d$.

### 3.6 What remains to be proven, and what it would buy

**Only the list bound.** With variant P a level is safe at threshold $A$ as soon as $\Lambda(A - \ell) \le 2^{b}$ for the $b$ its points pay for. No statement about challenges is left. The open question of the main document, section 3.2, loses its items 1 and 3 and keeps `ListBound`, with $L$ up to $2^{40}$ or $2^{100}$.

**Is that provable on our domains?** Not by me, and not from the literature (note 01, section 5: no upper bound beyond Johnson applies to subspace domains). What the larger budget changes is where the known families bite (note 01, section 4, $N = 25$), from `07_deep_fold_params.py`, table 4:

| rate | deployed $t$ | a proof of this would give | $t$ | level-0 bytes saved (rough) |
| --- | --- | --- | --- | --- |
| 1/2 | 218 | $\Lambda \le 2^{40}$ just above $0.632\,n$ (no family known between there and Johnson) | 164 | 57 KiB |
| 1/2 | 218 | $\Lambda \le 2^{40}$ at $5n/8$ (known family $2^{29.4}$) | 160 | 62 KiB |
| 1/2 | 218 | $\Lambda \le 2^{110}$ at $9n/16$ (known family $2^{102.7}$) | 131 | 92 KiB |
| 1/4 | 109 | $\Lambda \le 2^{40}$ at $3n/8$ (known $2^{27.8}$, predicted up to $2^{34.5}$) | 77 | 36 KiB |
| 1/4 | 109 | $\Lambda \le 2^{70}$ at $5n/16$ (known $2^{47.4}$) | 65 | 50 KiB |
| 1/8 | 73 | $\Lambda \le 2^{70}$ at $n/4$ (flats, $2^{49.4}$) | 54 | 20 KiB |
| 1/16 | 55 | $\Lambda \le 2^{100}$ at $n/8$ (flats, $2^{70.6}$) | 36 | 23 KiB |

Every right-hand statement is **[conjectured]** at best; the table says which list statements are worth attacking, and that with a budget of $2^{40}$ or more the rate-1/4 threshold $n/2$ is no longer "closed" by the $2^{26}$ flats. Later levels gain in the same proportion (every level at capacity would be 180 KiB of queries against 348).

**What is provable today: the last level. [proved]** A tuple of degree at most $d$ is determined by any $d + 1$ of its agreement points, so $\Lambda(A) \le \binom{n}{d+1}/\binom{A}{d+1}$ for every word and any number of lanes. At the last level of the $\mu = 30$, rate 1/2 ladder ($\kappa = 4$, $n = 2^{20}$, $d = 19$) this is $2^{241}$ at 12 bits per query, which 13 points pay for (1.0 KiB), and the level takes 9 queries instead of 15 (4.7 KiB of queries saved); at 14 bits per query, 8 queries. One level earlier ($d = 259$) the bound is $2^{1700}$ and more, and the points cost more than the queries save. So this is a net 1 percent of the proof: not worth deploying alone, but a complete instance of a level proven beyond Johnson, with every hypothesis discharged.

**Other codes (for note 06). [proved]** for the lemma's shape, **[sketch]** for the rest. Theorem 3 uses of the code only that codewords are polynomial tuples on an evaluation set, so it holds verbatim for a punctured Reed-Solomon code (any subset of a subspace). For an arbitrary linear code with a scalar combiner $f_1 + \alpha f_0$ and any family of random linear functionals with $\Pr[\mathrm{ev}(Q) = 0] \le \epsilon$ for $Q \ne 0$ (a multilinear point: $\epsilon = \kappa/q$), the same three lemmas give: no poles ($F = (P_1 + P_2)/(\alpha_1 + \alpha_2)$ is a codeword), bad points with probability $4\Lambda^3q^3\epsilon^s/K_0^3$, and a fold error $K_0/q$ with $K_0 \approx 1.36\,n/a$ at the price of an agreement loss $a$ per round (each $x$ outside the common agreement set repairs one $\alpha$, so a challenge needs $a$ repairs unless the pair already agrees on $A - a$ points). With $a = n/2^{10}$ per round the error is $2^{10.5}/q$ and the threshold moves by 0.1 percent of $n$ per round. So any code with a provable list bound and an interleaved, foldable encoding gets a fold soundness proof from its list bound alone, without a proximity-gap theorem of its own. Note 06 shows that the known capacity-achieving codes lose on leaf size, so the case that matters is the first one: plain Reed-Solomon on another evaluation set.

### 3.7 Why the present protocol cannot be re-analysed this way

**[proved]** Today the single out-of-domain claim is batched into the running claim, and the round message has four free values plus the free OOD answer: five unknowns, one equation per winning challenge. A dependency needs six pairs and gives one vanishing condition at one point, so the moment bound is $(\Lambda q^2)^6 (\mu/q) / K_0^6$, which is below 1 only for $K_0 \gtrsim \Lambda\,q^{2 - 1/6}$: an error of order $\Lambda (\mu/q)^{1/6}$. More grinding cannot repair an exponent. The gain needs the answers to be more numerous than the prover's degrees of freedom and independent of them: several points, unbatched.

### 3.8 Relation to notes 03 and 06

- **Note 03, sections 7.5 and 7.6.** Note 03 finds that a second running claim with its own four scalars per round does not give a worst-case bound: the prover can aim both residuals of a chosen candidate at a common line, degenerate weights give $L/q$ back, and a proof would need an enlarged candidate set and a genericity invariant charged to the message that fixes the weights. Theorem 3 is that proof for a particular choice of the extra claims. (a) An evaluation of the whole polynomial at $\zeta$ has no free scalars besides the answers, because the value of $XF$ is $\zeta$ times the value of $F$; a wrong member's residual at point $i$ is a line of slope $\zeta_i$, and the lines of two points never coincide. (b) The pseudo-candidates of note 03 are the rational pairs of Lemma 1, and they need not be put in the candidate set: Lemma 2 shows that each wins a line or a crossing set. (c) The genericity invariant is "the points are outside the exceptional set", charged to the point message. (d) More than two claims are needed: the third-moment bound needs $q^3\epsilon^s$ far below 1, so at least five fresh points, or 11 to 12 carried through the six folds of level 0.
- **Note 03, Proposition 4** (the coset pole pair caps any analysis through $\Gamma$ at $g_f + 3 = 10$ bits per query). It does not cap Corollary 4. On the line of label $\gamma$ the fold is the constant $\beta$, which is $G_\gamma + a_c F$ for $F = 1/(X - \beta_0)$ and $G_\gamma = \gamma/(X - \beta_0)$, so the answers $y^G_i = \gamma/(\zeta_i - \beta_0)$ name the line, and one answer vector wins one line. This is what lets the last level run at 12 to 14 bits per query in section 3.6.
- **Note 03, verdict 7** (grinding buys list budget up to about $2^{20}$). Points buy it with bytes instead: about 35 bits of list per point, 80 to 112 bytes each.
- **Note 06, section 7, item 1** asks for beyond-Johnson lists and MCA for plain Reed-Solomon on a structureless coset union. With Theorem 3 the lists alone suffice, on any evaluation set. Note 06's free change of its section 6.2 (coset labels with no additive relation, which removes the flats) composes with variant P unchanged and is then worth more: with the flats gone, the families that remain at low rates are the coset unions, with floors 65, 41, 32 at rates 1/4, 1/8, 1/16 instead of 108, 54, 36.

## 4. Round structure and order

Numbers from `scripts/07_deep_fold_params.py`, table 7: a rough model (Johnson thresholds without slack, pruned paths approximated), $\mu = 30$, rate 1/2. Note 08, section 4, has the validated model and the exact numbers (for example 8.2 percent for 32 lanes at level 0, where this table says 7); where they differ, note 08 is right. The table is here only to answer the brief's question on the round structure.

| change | queries per level | query bytes | later levels' codeword bytes over level 0's | verdict |
| --- | --- | --- | --- | --- |
| deployed (fold 6, then 4; domain shrinks by $2^3$, then 2) | 217, 55, 31, 22, 17, 14 | 345 KiB | 0.48 | |
| level 0 folds 4 | 217, 109, 44, 28, 20, 16, 14 | 348 KiB | 0.49 | no gain, a larger level-0 tree |
| level 0 folds 5 | 217, 73, 37, 25, 19, 15 | 319 KiB | 0.48 | 7 percent smaller (8.2 in note 08, section 4.3), level-0 tree twice the leaves at half the size |
| first domain reduction $2^2$ | 217, 44, 28, 20, 16, 13 | 334 KiB | 0.97 | 3 percent for twice the later encoding |
| no later domain reduction | 217, 55, 28, 19, 14, 11 | 341 KiB | 1.25 | no |
| later levels fold 5 | 217, 55, 28, 19, 14 | 353 KiB | 0.47 | no |
| residual of $2^8$ coefficients, one level fewer | 217, 55, 31, 22, 17 | 334 + 4 KiB | 0.47 | 2 percent; needs the guest's `RESIDUAL_MAX_LOG <= INITIAL_FOLDING_FACTOR` lifted |

- **Queries before the next commitment: unsound. [proved]** If the query points are known before $f^{(i+1)}$ is committed, the prover chooses a message satisfying the $t$ consistency equations and the residual claim, which are $t + 1$ linear conditions on $2^{\kappa}$ unknowns. The order commit, then queries, is forced.
- **One out-of-domain point per fold round**: by itself (batched as today) it changes nothing; unbatched and in number it is section 3 (variant F).
- **Fewer variables per level, more levels; steeper rate schedule**: the table. Within the Johnson regime the ladder is on a flat optimum, and level 0 has two thirds of the bytes whatever the later levels do.
- **Level 0 dominates** (231 of 348 KiB at rate 1/2), so any analysis gain should be spent there first; a threshold lowered at level 0 only, with points at level 0 only, already gives the savings of the table in 3.6.

## 5. Grinding

**[checked]** table 6 of the script. At $b$ bits per query one more bit of query grinding saves $1/b$ queries at that level and doubles that level's grinding work. At Johnson thresholds, rate 1/2: 2.0 queries (2.1 KiB) per bit at level 0, then 0.5, 0.29, 0.2, 0.15, 0.13 queries (0.42 KiB down to 0.10 KiB) at the later levels. At rate 1/16 level 0 gets 0.5 queries per bit. So extra query grinding is worth considering at level 0 only: four more bits there ($2^{21}$ expected hashes instead of $2^{17}$, once per proof) save 8 queries, 2.4 percent of the proof at rate 1/2. The fold, batching and OOD grinds do not bind the query count (the test `fold_grinding_is_the_least_that_costs_no_queries` says so for the fold; with section 3 the fold grind is not needed at all). The trade is linear in bits against exponential in work, so it cannot replace an analysis gain. Note 08, section 4.1, has the exact table (level 0 at 20, 24, 28 bits: 2.0, 4.3, 6.7 percent) and note 03, section 5, the cost of the other grinds.

## 6. Other ideas considered

- **Bundling evaluation points into leaves (folded Reed-Solomon style). Does not help.** Note 06, section 2, treats this in full; I reached the same conclusion by a shorter route. **[proved]** A leaf holding the evaluations on a coset of a subspace is the interleaved code we already have (the coset values and the lanes at $y = W_k(x)$ determine each other). A leaf holding $(f(x), f(\gamma x), \dots)$ with $\gamma$ of order above the degree is not a set of lanes: a linear combination of the $f(\gamma^i x)$ has the degree of $f$, so there is nothing to fold, and the only repair is to carry all lanes at each of the $m$ points, a leaf $m$ times larger (note 06, Lemma 2.1). With $\gamma$ of small order $e$ the subcode of polynomials in $X^e$ is constant on leaves, so the lists are those of plain Reed-Solomon.
- **Full columns at the points** (send all $2^\ell$ lane values at each point at commit time instead of one value per round): same soundness as variant P, 768 scalars at level 0 instead of 84. No.
- **Two thresholds** (a list bound only above $A^+ > A$, queries at $A$): a member at agreement $T$ that gets lucky still passes the queries with probability $(T/n)^t$, so the list bound is needed down to about $A(1 + 0.7/t)$, a shift of 0.3 percent. No gain. **[proved]** by that estimate.
- **Pinning with more commit-time points but keeping the CWYZ fold** (Lemma 0 only): removes $L$ from batching, OOD and the explained part of the fold, so lists of $2^{60}$ fit; but the unexplained part still needs `thm:mca-affine`, which stops at Johnson, where we already are within one query. No gain alone.

## 7. Ranked shortlist

| # | proposal | kind | queries (level 0, $\mu = 30$) | cost | status |
| --- | --- | --- | --- | --- | --- |
| 1 | **DEEP fold, variant P**: $s$ univariate out-of-domain points per commitment (12 at level 0, 8 or 9 after), carried unbatched through the level, one scalar per point per round | protocol change | unchanged by itself; with a list bound $2^{40}$ at the stated agreement: rate 1/2, 218 to 164 or 160; rate 1/4, 109 to 77; with $2^{70}$ to $2^{110}$: rate 1/2 to 131, rate 1/4 to 65, rate 1/8 to 54, rate 1/16 to 36 | +3 to 4 KiB, $s$ fused inner products at commit, a few thousand verifier products; replaces the MCA proof by an elementary one | lemma **[proved]**, **[checked]** at toy size; composition **[sketch]**; the list bounds **[conjectured]** |
| 2 | Same mechanism at the last level only, with the counting list bound | protocol change | last level 15 to 9 (or 8) | net about 3.7 KiB saved, 1 percent | **[proved]** end to end up to the composition sketch; not worth deploying alone |
| 3 | Level-0 query grind of 21 bits | parameter | 218 to 210 at rate 1/2 | $2^{21}$ expected hashes once per proof | **[checked]** arithmetic; note 08, section 4.1, is the reference |
| 4 | Level 0 folds 5 variables; residual $2^8$ | parameter (and guest change for the residual) | same level-0 count, 8 and 2 percent fewer bytes | larger level-0 tree; guest constraint | note 08, sections 4.3 and 4.5, is the reference |
| none | Pure re-analysis of the present fold | re-analysis | none found | | section 3.7: the present message structure gives at best $\Lambda(\mu/q)^{1/6}$ |
| rejected | quadratic or higher combiners, multi-variable folds, challenges in a larger field, bundled leaves, queries before the commitment | | | | sections 2, 4, 6 |

**The single most promising direction** is proposal 1 together with a list bound. It turns the research goal from "a proximity-gap theorem beyond Johnson on additive binary domains", which [DKTZ26] shows fails in its pure form at the error we need and which nobody knows how to prove in a claim-bound form, into "a list-size bound of $2^{40}$ to $2^{100}$ below Johnson", a statement about the code alone, with a budget $2^{30}$ to $2^{90}$ times more forgiving than the main document's $2^{10}$. It also makes the protocol indifferent to the code: for any evaluation set with provable lists below Johnson (the one theorem note 06, section 7, still hopes for, now without its MCA half), the fold needs no new theorem (sections 3.6 and 3.8). Since the change has to land in two provers, three verifiers and `formal/`, I would not land it before one such list bound exists; I would write the full round-by-round proof and its Lean statement first, because it is short and it fixes what the list researchers have to deliver.

## 8. Reproduction

- `python3 doc/whir_soundness_gap_notes/scripts/07_deep_fold_check.py`: tests T0 (identities of Lemma 1), T3 (pole collapse for $r \le 3$), and T1, T2 on four words. About 35 seconds, 4 processes.
- `python3 doc/whir_soundness_gap_notes/scripts/07_deep_fold_params.py`: tables 1 to 7. Instant.

## References

As in the main document and note 01, plus:

- [BGKS20] E. Ben-Sasson, L. Goldberg, S. Kopparty, S. Saraf. DEEP-FRI: Sampling Outside the Box Improves Soundness. ITCS 2020.
- [ACFY24a], [ACFY24b] G. Arnon, A. Chiesa, G. Fenzi, E. Yogev. STIR (ePrint 2024/390) and WHIR (ePrint 2024/1586).
