# 75. Referee report on notes 73 and 74, and on note 68 Section 11

Referee 75, round 17. Scope: note 74 (Lemma 2.3, Theorem 4.2, Corollary 4.3, then Theorem 4.4 and Proposition 6.1 if time), note 68 Section 11 (the averaging consequence and the linear program), note 73 (Lemmas 2.1, 4.1, 4.2, Theorem 5.1). Rule applied: a statement is "confirmed" only if every step was re-derived here or checked by an independent exact computation; otherwise "not confirmed" with the first step that could not be verified. Scripts are `scripts/75_*`.

Status: complete. Every verdict below was reached by re-deriving the proof and, where a computation is named, by code written for this report.

## 0. Verdict table

| # | statement | verdict | first unverified step, error, or restriction | independent check performed |
|---|---|---|---|---|
| 1 | Note 74, Lemma 2.3 (derivative lemma), with its Hasse variants | **confirmed** | none. Needs one private bottom twiddle per leaf (T2) | re-derived in every characteristic (Section 1) |
| 2 | Note 74, Theorem 4.2 (one functional per leaf, genuine implies independent rows) | **confirmed** for T2, algebraically independent twiddles, any number of trees | none in the proof. **False for T1** from four members on (explicit counterexample, Section 3.4). Says nothing about twiddles in GF($2^{64}$) | proof re-derived (Section 2); exhaustive at $(2,8)$, $(2,16)$, $(4,16)$; 5.9 million sampled patterns at $k = 2..16$, $n = 16..64$, rates 1/2 to 1/16, 3 to 5 members; 0 violations (Section 3) |
| 3 | Note 74, Corollary 4.3 ($Q_t$: at most $(t-1)k - 1$ coincidence leaves; weight at most $Lk - 1 + \sum (c_x - 2)_+$; sub-lists) | **confirmed**, same scope | none. At rate 1/2, $Q_t$ is vacuous for $t \ge 4$ | every genuine kernel turned into encoded codewords and counted; 2.6 million lifted lists and all staircase sub-lists: the bound is reached and never exceeded (Sections 3.2, 3.3, 6.3) |
| 4 | Note 68 Section 11, thresholds 0.3276, 0.2051, 0.1237, 0.0416 (and 0.7071, 0.5000, 0.0072) | **confirmed** to the digits given | the script solves a grid primal, a lower estimate; the upper bound needs a dual | dual certificates on 4.2 million points with a Lipschitz margin (Section 4.2) |
| 5 | Note 68 Section 11, derivation "$\mathbb E[h_j(\theta)] \le j\rho$" | **not confirmed as written; correct in the limit; gap closed here** | first step that fails for a finite list: sub-lists are sampled without replacement, so the constraint is hypergeometric, not comparable with $h_j$ | Lemma R1, Proposition R2 (proved, Section 4.1); finite program with exact rational certificates up to $M = 1025$ (Section 4.3) |
| 6 | Explicit list bound below Johnson for the generic tree code at rates $\le 2^{-3}$ (asked of the referee) | **proved here, conditional only on row 3** | T2 and generic twiddles only | table of Section 4.3; at most $(1 - \tau^*)/(\rho\eta)$ codewords at $\tau^* + \eta$ |
| 7 | Note 73, Lemma 2.1 (one level, with the probability bound (c)) | **confirmed** | none; T1 and T2 alike | re-derived (Section 5.1) |
| 8 | Note 73, Lemmas 3.1, 3.2, 4.1, 4.2, the prefix code and its Kraft sum | **confirmed** | none | re-derived; Kraft sum enumerated on four tiny trees (Sections 5.2, 5.4) |
| 9 | Note 73, Theorem 5.1 (distance with an MDS top) and its table | **confirmed** | none; one cosmetic remark on the "main term" column | constants recomputed from the text: 5.340, 5.677 (rate 1/2, $J = 4$, $n = 2^{19}, 2^{25}$), 3.058, 3.243 (rate 1/4), five more entries, all equal to the table; GF($2^8$), $n = 16$, all subsets, 4.8 million codes: no violation (Sections 5.3, 5.4) |
| 10 | Note 74, Theorem 4.4 (three members: weight at most $5k/2 - 2$, attained) | **confirmed**, scope of row 3 | none | re-derived; lifted lists reach exactly $5k/2 - 2$ at six sizes; the finite program at $M = 3$ gives the same value (Sections 6.1, 6.3) |
| 11 | Note 74, Proposition 6.1 (one-sided staircase) | **confirmed** (any tree code with an MDS top) | none | re-derived; re-encoded at 15 (size, split) pairs, 12 of them not used by the author, up to 40000 members each (Sections 6.2, 6.3) |

**Headlines.** (a) The foundation (rows 2, 3) holds, for T2 only: in T1 four codewords can coincide on $3k + k/2 - 1$ leaves at every rate up to 1/4, by Desargues' involution theorem in characteristic 2. (b) On that foundation there is a list bound below the Johnson radius at every rate $2^{-3}$ or less, with lists already below $2^{10}$ within $1.3 \cdot 10^{-4}$ of the threshold (Section 4.3); at rate $2^{-3}$ it needs only the MDS property and $Q_4$, and $Q_3$ alone already gives 0.3297 against Johnson's 0.3536 (Section 4.5). (c) None of this is yet a statement about twiddles in GF($2^{64}$): note 73's theorem (row 9) is the only random statement, it is about one codeword, and it is correct.

## 1. Note 74, Lemma 2.3 (derivative lemma)

**Verdict: confirmed (re-derived), for T2 only, as stated.** Re-derivation. $F = K_1(t_x : x \text{ a leaf})$ is a purely transcendental extension of $K_1$, so $\partial_j = \partial/\partial t_j$ is a $K_1$-linear derivation of $F$ in every characteristic (the quotient rule extends it from $K_1[t]$; clearing denominators is not needed). $U_x$ has a basis over $K_1$, so $\partial_j$ acts on $U_x \otimes_{K_1} F$ coefficientwise and preserves it. Applying $\partial_j$ to $\sum_x u_x \otimes z_x = 0$ gives $\sum_x \partial_j u_x \otimes z_x + u_j \otimes (0,1) = 0$, since $\partial_j z_x = (0, \delta_{xj})$. So $u_j \otimes (0,1) = -\sum_x \partial_j u_x \otimes z_x$ is a combination of rows of $R$ with coefficients $\partial_j u_x$, which vanish where $u_x$ vanishes: it is supported in the support of the relation. Then $u_j \otimes (1, 0) = u_j \otimes z_j - t_j\, u_j \otimes (0,1) \in R$ as well. Nothing in this uses the characteristic: the only derivative taken of a non-constant of $K_1$ is $\partial_j t_j = 1$. The Hasse-derivative variants are not used by Theorem 4.2; they are also correct: by the Leibniz rule $D_j^{(a+1)}(u_x \otimes z_x) = D_j^{(a+1)} u_x \otimes z_x + \delta_{xj}\, D_j^{(a)} u_j \otimes (0,1)$ since $D_j^{(b)} z_j = 0$ for $b \ge 2$, and $D_i D_j$ applied to the relation gives the mixed statement. In characteristic 2 the iterated formal derivative $\partial_j^2$ is identically zero, so the Hasse form is the only one with content beyond first order.

Two remarks. (i) The lemma needs one private bottom parameter per leaf. In T1 the two leaves of a pair have $z_{p0} = (1, s_p)$, $z_{p1} = (1, s_p + 1)$ and the derivative in $s_p$ gives only $(u_{p0} + u_{p1}) \otimes (0,1) \in R$; the note says so itself (end of Theorem 4.4). (ii) "Every solution kills $u_j$ in both slices" is over any extension field: membership of a vector in the row space does not depend on the field.

## 2. Note 74, Theorem 4.2 and Corollary 4.3: audit of the proof

**Proof re-derived step by step; no gap found for T2 with algebraically independent twiddles.** (Verdict line after the computations of Section 3.) The steps, as I checked them.

1. *Genuine is field independent.* "$\mathcal S$ is genuine for $\lambda$" says $\lambda \otimes K^k \not\subseteq$ row space, a rank statement, so it does not matter over which extension field the solutions are taken, and the messages of a list may depend on the twiddles. For a list of distinct codewords with differences $d_l = m_l - m_0$ and a pair $(a, b)$ agreeing at $x$, $\lambda_x = e_a - e_b$ has $\lambda_x^T M = m_a - m_b \ne 0$, so the list's own $M$ witnesses genuineness for every row kept. Only the rows kept need it; pairs that occur at no leaf are not constrained.
2. *Base case $v = 0$* (repetition code of length $2^r$, any $r$): each row is $\lambda_x$ itself, every solution has $\lambda_x^T M = 0$, so genuineness forces $X = \emptyset$. Correct, and it is where "distinct" is used.
3. *Step.* $\lambda_x \otimes g_x = (\lambda_x \otimes g_p) \otimes z_x$ with the line $U_x = \langle \lambda_x \otimes g_p \rangle$ defined over $K_1 = K_0(\text{upper twiddles})$, nonzero because $\lambda_x \ne 0$ and $g_p$ has first entry 1. Lemma 2.3 applied to a relation with $u_x = c_x\, \lambda_x \otimes g_p$, $c_x \ne 0$: $(\lambda_x \otimes g_p) \otimes (0,1) \in R_T$, hence $U_x \otimes F^2 \subseteq R_T$ for each $x$ in the union $T$ of the supports, $R_T = U_T \otimes F^2$, and $|T| > 2 \dim U_T$ since $T \ne \emptyset$ carries a relation. Correct.
4. *Push up.* All solutions have both slices orthogonal to $U_T$. One leaf $x(p)$ kept per pair meeting $T$: at least $|T|/2 > \dim U_T$ rows $\lambda_p \otimes g_p$, all inside $U_T$, so dependent; the upper system is genuine for each $\lambda_p$ because a solution with $\lambda^T M \ne 0$ has a slice with $\lambda^T M_b \ne 0$; the upper code is the generic tree code with $v - 1$ layers, the same number of trees and twiddles independent over the same $K_0$. The induction hypothesis is contradicted. Correct. When the two leaves of a pair carry different $\lambda$ only one is kept, which is all the count needs.
5. *Corollary 4.3.* (a) one pair per coincidence leaf, then step 1; $|X| = Lk - \dim \mathcal S \le Lk - 1$ because $M \ne 0$. (b) $w = |X| + \sum_x (c_x - 2)_+$. (c) is (a) for the sub-list. Correct. Note that (a) is about coincidences of the codewords themselves (any two members equal at a leaf, several groups allowed), which is stronger than the pattern version relative to a word.

**Scope, stated plainly.** The theorem is about a field of transcendence degree at least the number of twiddles ($2n - 2^{r+1}$ in T2). It says nothing yet about twiddles drawn from GF($2^{64}$): for $t = 2$ the random statement is note 73's distance theorem, which holds only up to a slack $\varepsilon_0 n$, so the random analogue of $Q_t$ can at best be "at most $(t-1)k - 1 + \varepsilon_t n$". **It does not hold for T1** (Section 3.4: an explicit counterexample to $Q_4$ at every $k$ at rate 1/4, by Desargues' involution theorem in characteristic 2).

## 3. Note 74, Theorem 4.2 and Corollary 4.3: independent exact computation, and the verdict

Code: `scripts/75_gf.h` (GF($2^{64}$) written from scratch, self-tested against a bitwise multiplier), `scripts/75_qt.c`, driver `scripts/75_qt_run.sh`, output `scripts/75_qt_output.txt`. It shares nothing with the author's `74_thmA.c` and tests a different consequence: besides the theorem's own event (kernel genuine for every pair used, rows dependent), every genuine kernel is turned into a list, the $t$ codewords are encoded by a butterfly encoder that does not use the generator rows, and the leaves where two members coincide are counted on the whole code and on every sub-list. Twiddles are uniform in GF($2^{64}$), redrawn every few thousand patterns. Rank and genuineness of a pattern are decided by minors of degree at most about $(t-1)k\,v$ in the twiddles, so the outcome for random twiddles equals the generic outcome except with probability about $2^{-57}$ a pattern: a violation seen here would, up to that probability, be a counterexample to the generic statement, and zero violations is evidence for it on the patterns tried, not a proof.

### 3.1 Exhaustive, one draw of the twiddles (all patterns with $|X| = (t-1)k$, one pair per leaf, every pair on at most $k - 1$ leaves; a pattern with a pair on $k$ leaves is not genuine because the code is MDS)

| variant | $(k, n)$ | $t$ | patterns | rank deficient | violations |
|---|---|---|---|---|---|
| T2 | (2, 8) | 4 | 20160 | 0 | 0 |
| T2 | (2, 8) | 5 | 1814400 | 0 | 0 |
| T2 | (2, 16) | 4 | 5765760 | 0 | 0 |
| T2 | (4, 16) | 3 | 21621600 | 0 | 0 |
| T1 | (4, 8) | 3 | 1680 | 0 | 0 |
| T1 | (4, 16) | 3 | 21621600 | 0 | 0 |
| T1 | (2, 8) | 4 | 20160 | 192 | **192** |

A sub-pattern of a pattern carrying a list carries it, so "no square pattern carries a list" is $Q_t$ at that size. In T2 every one of these square systems has full rank.

### 3.2 Sampled patterns, T2 (uniform, recursive block structure, sibling copies; $|X| \in [(t-1)k - 2, (t-1)k + 1]$; three quarters repaired so that no pair exceeds $k - 1$ leaves)

| $(k, n)$ | rate | $t$ | patterns | rows dependent | lists built | lists with exactly $(t-1)k - 1$ coincidence leaves | more |
|---|---|---|---|---|---|---|---|
| (4, 16), (4, 32), (4, 64) | 1/4, 1/8, 1/16 | 3 | 600000, 600000, 400000 | 177684, 175652, 116512 | 261001, 262442, 175260 | 126247, 127283, 84694 | 0 |
| (8, 32), (8, 64) | 1/4, 1/8 | 3 | 400000, 300000 | 119181, 88347 | 180138, 135966 | 88970, 67192 | 0 |
| (16, 64), (16, 32), (8, 16) | 1/4, 1/2, 1/2 | 3 | 60000, 100000, 400000 | 17684, 7380, 31754 | 27688, 45499, 176572 | 13697, 22354, 87035 | 0 |
| (4, 16), (4, 32), (4, 64) | 1/4, 1/8, 1/16 | 4 | 600000, 600000, 400000 | 204344, 199457, 131505 | 220057, 223224, 150137 | 102308, 103405, 69566 | 0 |
| (8, 32), (8, 64), (2, 16) | 1/4, 1/8, 1/8 | 4 | 300000, 200000, 600000 | 111809, 71208, 189552 | 108444, 75404, 235801 | 51464, 35763, 114848 | 0 |
| (4, 32) | 1/8 | 5 | 300000 | 115299 | 94597 | 42300 | 0 |

Theorem violations (genuine and dependent): 0 in all 5.9 million patterns. No list had a coincidence leaf outside its pattern once the pattern had $(t-1)k - 1$ leaves, which is the sharp form of the corollary. (At rate 1/2 with $t = 4$ the bound $3k - 1$ exceeds $n$ and the test is vacuous; that row is omitted.)

### 3.3 Lifted lists $A \otimes B$ of note 69, T2, every split level, top list built with $(t-1)k_{\rm up} - 1$ block coincidences, $B$ with $2^i - 1$ zeros on random leaves

1.98 million lists at $(k, n) \in \{(4,16), (4,32), (4,64), (8,32), (8,64), (16,32), (16,64)\}$, $t = 3, 4$, and $(8, 32)$, $t = 5$: the largest number of coincidence leaves is exactly $(t-1)k - 1$ at every size with $n \ge (t-1)k$, reached by 20 to 55 percent of the lists, never exceeded. This is as it must be: $2^i((t-1)k_{\rm up} - 1) + 2^i - 1 = (t-1)k - 1$, so **the lifted lists saturate $Q_t$ exactly** when the zeros of $B$ avoid the coincidence blocks; they are the extremal objects of the corollary, not counterexamples to it.

### 3.4 T1: $Q_4$ is false (proved here, and found by the sampler without help)

Take $k = 2$, three sibling pairs with points $\{\alpha, \alpha + 1\}, \{\beta, \beta + 1\}, \{\gamma, \gamma + 1\}$, and the four lines $f_0 = 0$, $f_1 = (\beta + \gamma + 1)(y + \alpha)$, $f_2 = (\alpha + \gamma + 1)(y + \beta)$, $f_3 = (\alpha + \beta + 1)(y + \gamma)$. Then $f_0 = f_i$ at $\alpha, \beta, \gamma$, and $f_1 = f_2$ at $\gamma + 1$, $f_1 = f_3$ at $\beta + 1$, $f_2 = f_3$ at $\alpha + 1$ (each equality is the same product on both sides, for instance $f_1(\gamma + 1) = (\beta + \gamma + 1)(\alpha + \gamma + 1) = f_2(\gamma + 1)$; behind it, the $3 \times 3$ system for the slopes has determinant $2ABC = 0$ in characteristic 2, which is Desargues' involution theorem for the involution $y \mapsto y + 1$ that pairs siblings in T1). The slopes are distinct and nonzero because the three pairs are distinct. Four distinct codewords, six coincidence leaves, against $3k - 1 = 5$. Lifting at split level $v - 1$ gives, at every $k$ and every rate at most 1/4, four codewords with $3k + k/2 - 1$ coincidence leaves (measured: 13 at $(4, 16)$, 27 at $(8, 32)$). Five lines at $k = 2$ reach 8 coincidence leaves against 7 (exhaustive at $n = 8$: 11520 of 1814400 square patterns carry a list; a quadrilateral of four of the lines on three sibling pairs, plus one line). For three members no violation was found in T1: exhaustive at $(4,8)$ and $(4,16)$, 1.66 million sampled patterns at $(4,16)$, $(4,32)$, $(4,64)$, $(8,16)$, $(8,32)$, $(8,64)$, $(16,64)$, 420000 lifted lists; $Q_3$ for T1 is neither proved nor refuted here.

**Verdict on Theorem 4.2 and Corollary 4.3: confirmed** for variant T2 with algebraically independent twiddles, any number of trees, any $t$: proof re-derived in full (Section 2), independent exact checks at sizes the author did not use (above). **Restrictions that the consumers of the statement must carry:** (i) T2 only; it is false for T1 from $t = 4$ on; (ii) a statement over a field of large transcendence degree, not over GF($2^{64}$) with random twiddles, where at best a version with a slack can hold; (iii) at rate 1/2 the properties $Q_t$, $t \ge 4$, are vacuous and $Q_3$ only says that three codewords cannot have a coincidence at every leaf.

## 4. Note 68 Section 11: the averaging consequence, and an explicit finite list bound

### 4.1 What the averaging gives exactly, for a finite list

Let $M = L + 1$ distinct codewords each agree with a word $y$ on at least $\tau n$ leaves, $c_x$ the number of members agreeing with $y$ at leaf $x$, so $\sum_x c_x \ge M \tau n$. For a sub-list $T$ of $j + 1$ members, every leaf with $|C_x \cap T| \ge 2$ is a coincidence leaf of $T$, so $Q_{j+1}$ gives $\#\{x : |C_x \cap T| \ge 2\} \le jk - 1$. Averaging over the $\binom{M}{j+1}$ sub-lists, which is sampling $j + 1$ members **without replacement**:

$$\frac1n \sum_x H_j(c_x; M) \le j\rho - \frac1n, \qquad H_j(c; M) = \Pr[\mathrm{Hyp}(M, c, j+1) \ge 2], \qquad j = 1, \dots, M - 1. \tag{F}$$

**Gap in the lead's statement (closed below).** Note 68 writes $\mathbb E_\mu[h_j(\theta)] \le j\rho$ with the binomial $h_j$ and $\theta = c_x/M$, and says itself that this is the limit of large lists. For a finite list the inequality with $h_j$ is false in general: the two functions are not comparable pointwise ($H_1(c; M) = \theta (c-1)/(M-1) < \theta^2 = h_1(\theta)$, while for $(j+1)\theta > 1$ the hypergeometric puts less mass on $\{0, 1\}$ and $H_j > h_j$), and since $H_1 < h_1$ a finite list can sit above the limit threshold. A code of finite length has no "unboundedly many" codewords, so the limit statement needs a quantitative passage. Here is one.

**Lemma R1 (referee; proved here).** For $0 \le j \le J < M$ and $J \le c \le M$: $H_j(c; M) \ge h_j\big(\tfrac{c - J}{M - J}\big)$. *Proof.* Draw the $j + 1$ members one at a time. Whatever the history, after $d \le j$ draws with $i \le d$ hits the next draw is a hit with probability $(c - i)/(M - d) \ge (c - d)/(M - d) \ge (c - J)/(M - J)$, because $d \mapsto (c - d)/(M - d)$ is non-increasing for $c \le M$. So the number of hits stochastically dominates $\mathrm{Bin}(j + 1, (c - J)/(M - J))$, and $\Pr[\cdot \ge 2]$ is monotone. $\square$

**Proposition R2 (referee; proved here, conditional on $Q_2, \dots, Q_{J+1}$ only).** Let $\tau^*_J(\rho) = \sup\{\mathbb E_\mu[\theta] : \mu \text{ a probability measure on } [0,1],\ \mathbb E_\mu[h_j(\theta)] \le j\rho,\ j = 1..J\}$. If $M > J$ distinct codewords of a code with $Q_2, \dots, Q_{J+1}$ each agree with one word on at least $\tau n$ leaves, then
$$\tau \;\le\; \tau^*_J + (1 - \tau^*_J)\,\frac{J}{M}, \qquad\text{so for } \tau > \tau^*_J:\quad M \;\le\; \max\Big(J,\ \frac{J\,(1 - \tau^*_J)}{\tau - \tau^*_J}\Big).$$
*Proof.* Put $\theta'_x = \max(0, (c_x - J)/(M - J)) \in [0, 1]$ and let $\mu'$ be its distribution over leaves. By R1 (and $h_j(0) = 0$) and (F), $\mathbb E_{\mu'}[h_j] \le \frac1n \sum_x H_j(c_x; M) \le j\rho$ for $j \le J$, so $\mathbb E[\theta'] \le \tau^*_J$. And $c_x / M \le J/M + (1 - J/M)\,\theta'_x$ in both cases. $\square$

Constraints with $j\rho \ge 1$ are vacuous, so $\tau^*_J = \tau^* := \tau^*_{\lceil 1/\rho \rceil - 1}$ for all larger $J$, and with $J = \lceil 1/\rho \rceil - 1 < 1/\rho$: **a list at agreement $\tau^* + \eta$ has at most $(1 - \tau^*)/(\rho\,\eta)$ members, for every length $n$.** This is the same shape as the Johnson bound's $(\tau - \rho)/(\tau^2 - \rho)$ ($J = 1$).

### 4.2 The limit thresholds, certified (`scripts/75_lp.py`, output `scripts/75_lp_output.txt`)

The lead's `68_lp_twise.py` solves the primal program on a grid of 2001 values of $\theta$. Restricting the measure to a grid can only lower the supremum, so its output is a **lower** estimate of $\tau^*$, not the upper bound the argument needs. I recomputed with a dual certificate: multipliers $\lambda_0, \lambda_j \ge 0$ with $\lambda_0 + \sum_j \lambda_j h_j(\theta) \ge \theta$ on all of $[0,1]$ (checked on 4.2 million points with the Lipschitz constant $1 + \sum_j (j+1)\lambda_j$ covering the gaps), which gives $\tau^* \le \lambda_0 + \rho \sum_j j \lambda_j$.

| rate | $2^{-1}$ | $2^{-2}$ | $2^{-3}$ | $2^{-4}$ | $2^{-5}$ | $2^{-7}$ | $2^{-10}$ |
|---|---|---|---|---|---|---|---|
| grid primal (lower) | 0.7071068 | 0.5000000 | 0.3275817 | 0.2050547 | 0.1236565 | 0.0416499 | 0.0072336 |
| certified dual (upper) | 0.7071071 | 0.5000004 | 0.3275822 | 0.2050553 | 0.1236572 | 0.0416508 | 0.0072347 |
| note 68 | 0.7071 | 0.5000 | 0.3276 | 0.2051 | 0.1237 | 0.0416 | 0.0072 |
| Johnson $\sqrt\rho$ | 0.7071 | 0.5000 | 0.3536 | 0.2500 | 0.1768 | 0.0884 | 0.0313 |
| active constraints $j$ | 1 | 1 | 1, 3 | 1, 2, 6 | 1, 2, 3, 11, 12 | 7 values up to 47 | 12 values |

**The lead's seven thresholds are confirmed to the four digits given.** At rates 1/2 and 1/4 the value is exactly the Johnson radius (at 1/4 the point mass at $\theta = 1/2$ is feasible: $h_2(1/2) = 1/2$, $h_3(1/2) = 11/16 \le 3/4$). For small $\rho$ the threshold behaves like $\rho \ln(1/\rho)$ plus a multiple of $\rho$ (the density $\rho\, d\theta/\theta^2$ on $[\rho, 1]$ is nearly feasible because $\int_0^\infty (1 - e^{-s}(1+s))\, s^{-2}\, ds = 1$): 7.4 times capacity at $2^{-10}$, against 32 times for Johnson. This asymptotic is a remark, not checked beyond the table.

### 4.3 The finite program, solved with exact certificates, and the table asked for

For a list of $M$ members the constraints (F) are linear in the fractions $x_c$ of leaves with $c_x = c$, $c = 0..M$. Let $\tau_M(\rho)$ be the value of the program "maximize $\sum_c (c/M) x_c$ subject to $\sum_c x_c = 1$ and (F) without the $-1/n$". **A list of $M$ distinct codewords at agreement $\tau n$ forces $\tau \le \tau_{M'}$ for every $M' \le M$** (sub-lists keep their agreement); so above $\tau_M$ the list has at most $M - 1$ members, for every $n$. The script solves the program with HiGHS, rounds the dual to rationals and re-checks dual feasibility at every $c$ in exact rational arithmetic (hypergeometric tails as ratios of binomials), so each number below is a proved upper bound on $\tau_M$, equal to the float optimum to six digits. $\tau_M$ is decreasing over the values of $M$ computed.

| $M$ (list $\le M - 1$ above the value) | 3 | 4 | 6 | 8 | 16 | 32 | 64 | 128 | 256 | 400 | 1025 | limit $\tau^*$ | Johnson $\sqrt\rho$ |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| rate $2^{-3}$ | 0.4375 | 0.3855 | 0.3480 | 0.3398 | 0.3351 | 0.3317 | 0.3297 | 0.3287 | 0.3281 | 0.3280 | 0.32771 | 0.32759 | 0.35355 |
| rate $2^{-4}$ | 0.3855 | 0.3178 | 0.2573 | 0.2324 | 0.2113 | 0.2089 | 0.2070 | 0.2061 | 0.2056 | 0.2054 | 0.20518 | 0.20506 | 0.25000 |
| rate $2^{-7}$ | 0.3399 | 0.2585 | 0.1780 | 0.1385 | 0.0811 | 0.0552 | 0.0449 | 0.0425 | 0.0421 | 0.0420 | 0.04176 | 0.04166 | 0.08839 |
| rate $2^{-10}$ | 0.3342 | 0.2511 | 0.1681 | 0.1267 | 0.0649 | 0.0343 | 0.0193 | 0.0122 | 0.0090 | 0.0080 | 0.007334 | 0.007235 | 0.03125 |

(Values rounded up; the limit column is the upper end of the certified bracket. The Johnson bound for the same $M$, $\tau \le (1 + \sqrt{1 + 4(M-1)(M-2)\rho})/(2(M-1))$, is in the output file; it is larger at every entry, for example 0.4065 against 0.3398 at rate $2^{-3}$, $M = 8$.) Empirically $M(\tau_M - \tau^*)$ tends to about 0.13, 0.12, 0.11, 0.10 at the four rates, so the list at $\tau^* + \eta$ is about $0.1/\eta$; Proposition R2 proves $(1 - \tau^*)/(\rho\,\eta)$, the right shape with a worse constant.

**Smallest agreement above which every list has at most $\Lambda$ members** (generic tree code T2, conditional only on Corollary 4.3). $\Lambda = 2^{10}$: exact certificate at $M = 1025$. $\Lambda = 2^{20}$: dual of the program at $M = 2^{20} + 1$ found on a subsample of $c$ and checked at every $c = 0..M$ in floating point (the same routine reproduces the exact value at $M = 1025$ to $10^{-7}$). $\Lambda = 2^{40}$: Proposition R2 ($J/M < 2^{-30}$) and monotonicity.

| rate | capacity $\rho$ | $\Lambda = 2^{10}$ | $\Lambda = 2^{20}$ | $\Lambda = 2^{40}$ | limit $\tau^*$ (certified bracket) | Johnson $\sqrt\rho$ | Johnson at $\Lambda = 2^{10}$ |
|---|---|---|---|---|---|---|---|
| $2^{-3}$ | 0.125000 | 0.32771 | 0.327582 | 0.327582 | [0.3275817, 0.3275822] | 0.353553 | 0.353869 |
| $2^{-4}$ | 0.062500 | 0.20518 | 0.205055 | 0.205055 | [0.2050547, 0.2050553] | 0.250000 | 0.250367 |
| $2^{-7}$ | 0.007813 | 0.04176 | 0.041651 | 0.041651 | [0.0416499, 0.0416508] | 0.088388 | 0.088835 |
| $2^{-10}$ | 0.000977 | 0.007334 | 0.007234 | 0.007234 | [0.0072336, 0.0072347] | 0.031250 | 0.031727 |

The three columns differ only in the fourth digit: the list is already below $2^{10}$ within $1.3 \cdot 10^{-4}$ of the threshold, so for the application the threshold is the whole story and the budget of $2^{300}$ is irrelevant here.

### 4.4 Plain answer

**Yes.** Conditional only on Corollary 4.3, which Section 2 confirms, the generic tree code (T2, algebraically independent twiddles) of rate $2^{-3}$ or less has, around every word (with symbols in any extension field), at most $(1 - \tau^*)/(\rho\,\eta)$ codewords at agreement $\tau^* + \eta$, with $\tau^* = 0.3276, 0.2051, 0.0417, 0.0073$ at rates $2^{-3}, 2^{-4}, 2^{-7}, 2^{-10}$, all strictly below the Johnson radius; at the Johnson radius itself the list has at most 5, 6, 14, 35 members at these rates (the first $M$ with certified $\tau_M < \sqrt\rho$ is 6, 7, 15, 36; `scripts/75_lp_johnson_point.py`). At rates 1/2 and 1/4 it gives exactly Johnson and nothing more. **Verdict on note 68 Section 11: thresholds confirmed. The derivation is a correct limit heuristic with two gaps, both closed here: the passage from a finite list (hypergeometric) to the limit (binomial), by R1 and R2; and the direction of the numerical bound (a grid primal is a lower estimate), by the dual certificates.**

What this is not. (i) Not a statement about T1: $Q_4$ fails there (Section 3.4), so T1 needs its own, weaker, constants or a proof that the failure is confined to sibling involutions. (ii) Not a statement about twiddles in GF($2^{64}$): the generic code lives over a field of transcendence degree about $2n$. A random version needs $Q_t$ with a slack, "at most $(t-1)k + \varepsilon_t n$", for the $t$ in the dual support (Section 4.5), and then the program reads $\mathbb E[H_j] \le j\rho + \varepsilon_j$; at rate $2^{-3}$ this is four codewords, at rate $2^{-10}$ the support goes up to $j = 375$, and note 73's method (one codeword, $t = 2$) addresses neither. (iii) Not the true threshold. $Q_t$ counts each leaf once and the lifted lists saturate it (Section 3.3), so its constants cannot be improved; $\tau^*$ is what these counts give on average over sub-lists, and a lower threshold needs $Q_t$ on chosen sub-lists or information that is not a coincidence count. Whether lists exist near $\tau^*$ is open: the known ones (staircases) sit at $\rho + 1/N$.

### 4.5 Which $Q_t$ the thresholds actually use (computed; the dual supports of Section 4.2)

The optimal multipliers of the limit program are supported on few constraints, so the threshold needs few of the properties: at rate $2^{-3}$ only $j \in \{1, 3\}$, that is **the MDS property and $Q_4$** ($\tau^* = \lambda_0 + \rho\lambda_1 + 3\rho\lambda_3$ with $\lambda_0 = 0.11659$, $\lambda_1 = 0.48113$, $\lambda_3 = 0.40228$); at $2^{-4}$, $j \in \{1, 2, 6\}$ ($Q_2, Q_3, Q_7$); at $2^{-5}$, $j \le 12$; at $2^{-7}$, $j \in \{1, 2, 4, 11, 12, 46, 47\}$; at $2^{-10}$, $j \in \{1, 2, 3, 4, 6, 13, 14, 31, 32, 92, 93, 375\}$, roughly a geometric progression of ratio 3 up to $0.37/\rho$. Three consequences. (i) A random-twiddle version at rate $2^{-3}$ needs a robust form of $Q_4$ only: four codewords, not hundreds. (ii) $Q_4$ is exactly the property that fails for T1 (Section 3.4: $3k + k/2 - 1$ coincidence leaves at every rate up to 1/4), so for T1 the constraints $j \ge 3$ must be replaced by whatever T1 really satisfies, which is not known. (iii) **$Q_3$ alone is already below Johnson at rates $2^{-3}$ and less**, and $Q_3$ was not refuted for T1 (Section 3.1). Certified upper bounds on $\tau^*_J$, the threshold that uses only $Q_2, \dots, Q_{J+1}$, printed to five digits (`scripts/75_lp_fewJ_output.txt`; Proposition R2 then bounds the list by $J(1 - \tau^*_J)/\eta$ at $\tau^*_J + \eta$):

| rate | $J = 1$ (Johnson) | $J = 2$ ($Q_3$) | $J = 3$ ($Q_4$) | $J = 4$ | $J = 7$ | $J = 15$ | all $j$ |
|---|---|---|---|---|---|---|---|
| $2^{-2}$ | 0.50000 | 0.50000 | 0.50000 | | | | 0.50000 |
| $2^{-3}$ | 0.35355 | 0.32968 | 0.32758 | 0.32758 | 0.32758 | | 0.32758 |
| $2^{-4}$ | 0.25000 | 0.22106 | 0.21161 | 0.20695 | 0.20506 | 0.20506 | 0.20506 |
| $2^{-5}$ | 0.17678 | 0.15227 | 0.13912 | 0.13358 | 0.12550 | 0.12366 | 0.12366 |
| $2^{-7}$ | 0.08839 | 0.07402 | 0.06534 | 0.05937 | 0.05146 | 0.04458 | 0.04165 |
| $2^{-10}$ | 0.03125 | 0.02574 | 0.02243 | 0.02017 | 0.01614 | 0.01216 | 0.00723 |

For small $\rho$ the column $J$ behaves like $\sqrt{2\rho/(J+1)}$ while $J \ll 1/\sqrt\rho$ (a point mass, $h_J(\theta) \approx \binom{J+1}{2}\theta^2$). If T1 satisfied $Q_3$ and, for $t \ge 4$, only the measured $(t-1)k + k/2 - 1$, the program would give 0.3297, 0.2115, 0.1263, 0.0425 at rates $2^{-3}, 2^{-4}, 2^{-5}, 2^{-7}$ (`scripts/75_lp_t1.py`; hypothetical, the T1 maxima are not known beyond $k = 2$, where five lines reach 8 coincidence leaves against 7, exhaustive at $n = 8$).

## 5. Note 73: the distance theorem

### 5.1 Lemma 2.1 (one level)

**Verdict: confirmed (re-derived).** (a) Both children of $p \in Y$ present and $t_{p,0} \ne t_{p,1}$ give $\alpha_p = \beta_p = 0$, so $N_{j+1}(Z) = S$; $e_{j+1}(Z) = (2|Y| + |D|) - 2k_j + (2\,\mathrm{null}_j(Y) - |D| + G) = 2e_j(Y) + G$. (b) $|D|$ conditions on a space of dimension $2\,\mathrm{null}_j(Y)$ give $0 \le G \le |D|$; if the label is tight some condition is not identically zero on $N_j(Y)^2$, so $G \le |D| - 1$, and $S \ne 0$. (c) On "tight and $\dim S = \delta$", $S$ minus the $d$ proper subspaces $\{\beta_p = 0\}$ has at least $q^\delta(1 - d/q)$ points, each of which determines the realized vector $(t_p)_{p \in D}$ as $\alpha_p/\beta_p$ and lies in the deterministic set $W_{(t_p)}$; the $W_\sigma$ are disjoint subsets of $N_j(Y)^2$, so at most $q^{m - \delta}/(1 - d/q)$ vectors $\sigma$ have $|W_\sigma| \ge q^\delta(1 - d/q)$; the sets $\Sigma_\delta$ are nested, so "tight and $\dim S \ge \delta$" is inside $\{(t_p) \in \Sigma_\delta\}$. All steps check.

*Probability space.* $S$ and tightness depend on the fresh level only through the used twiddles $(t_{p, c(p)})_{p \in D}$, one per node of $D$. Each is uniform on $K$ (in T1 both $t_{p,0}$ and $t_{p,0} + 1$ are; in T2 the marginal of a uniform ordered pair of distinct elements is uniform), distinct nodes are independent, and the level is independent of $T_j$. So the vector is uniform on $K^D$ given $T_j$ **in T1 and in T2 alike**; the correlation inside a pair never enters because a half pair uses one of its two twiddles and a full pair uses only $t_{p,0} \ne t_{p,1}$. The hypothesis $|D| < q$ is all that is needed. Nothing here depends on the characteristic except the sign in $t_p = \alpha_p/\beta_p$.

### 5.2 Lemmas 3.1, 3.2 (flat chains), 4.1 (top-down conditioning), 4.2 (good event), and the prefix code

**Verdict: confirmed (re-derived), all four.**

*Flats (3.1, 3.2).* For a flat $Z$ of $T_{j+1}$ with nullity at least 1 and $p$ a half pair, the absent child's functional is not identically zero on $N_{j+1}(Z) = S$ while the present child's is; if $\beta_p \equiv 0$ on $S$ both would vanish. So the label $(F, H, c)$ is tight. If $p \notin F$ had $g_p \equiv 0$ on $N_j(F)$, both children of $p$ would vanish on $S \subseteq N_j(F)^2$ and lie in the flat. So $F$ is a flat with nullity at least 1 and the chain exists with no rounding. The bookkeeping $\mathcal E_{j+1} = \mathcal E_j + u_{j+1} G_j$, $\mathcal N_{j+1} = \mathcal N_j - u_{j+1}(d_j - G_j)$, the Abel summation $\mathcal E_v = \sum_j \omega_j \Gamma_j$ with $\omega_j = u_{j+1} - u_{j+2}$, and the budget $\sum_i u_{i+1} d_i \le k - u_J|Z_J| + \mathcal E_v - 1$ (from $\mathcal N_v \ge 1$ and $e_J(Z_J) = 0$, which is the only use of "the top is MDS") are correct.

*Step from flats to arbitrary leaf sets.* The closure of $Z$ has the same null space and at least as many leaves, so its excess $|Z| - k + \mathrm{null}$ is at least that of $Z$; it is a flat. Correct, and no count of flats is needed since the union bound is over all prefix labels.

*Lemma 4.1.* For a fixed prefix label the sets $Z_i$ are deterministic. $\sum_i G_i \ge \Gamma$ implies $G_i \ge g_i$ for one of the $\binom{\Gamma + j - J}{j - J}$ compositions of $\Gamma$ into $j - J + 1$ nonnegative parts. $B_i$ = "label $i$ tight and $G_i \ge g_i$" is a function of the twiddles of levels up to $i + 1$, and Lemma 2.1(c) bounds $\Pr[B_i \mid T_i]$ by $q^{-g_i}/(1 - n/q)$ for every value of $T_i$, so peeling from the finest level gives the product, with at most $L$ factors $1/(1 - n/q)$. No independence between levels or between labels is used. Correct.

*Prefix code and its Kraft sum.* For any $\lambda_i > 0$ and $c_i = \log_2(1 + 2^{1 - \lambda_i})$: $\sum_{D \subseteq P_i \setminus Z_i,\ c} 2^{-\lambda_i |D| - m_i c_i} = (1 + 2 \cdot 2^{-\lambda_i})^{m_i}\, 2^{-m_i c_i} = 1$ for each fixed $Z_i$, so the levels sum out one by one from the finest, and the top gives $\sum_{Z_J} 2^{-\lambda'_J |Z_J|}(1 + 2^{-\lambda'_J})^{-n_J} = 1$. Equality holds for every truncation $j$ and for any positive multipliers; the recursion $\lambda_i = \lambda + C_{i+1}/2$ is needed only in Theorem 5.1. Correct (also checked by enumeration, Section 5.4).

*Lemma 4.2.* $\Pr[A(\pi_j, \Gamma^*)] \le \chi\, 2^{\kappa_j(\Gamma^*) - 64\Gamma^*} \le 2^{-w(\pi_j)} p/L$ by the definition of $\Gamma^*$; Kraft and the $L$ truncations give $p$. $\Gamma^*$ exists because $\Gamma \mapsto 64\Gamma - \kappa_j(\Gamma)$ increases without bound (increment at least $64 - \log_2 L$). On the good event a tight prefix has $\Gamma_j \le \Gamma^* - 1$, hence $(\star)$, including $\Gamma_j = 0$ provided $p < L$. Correct.

### 5.3 Theorem 5.1 (distance of the random tree code with an MDS top)

**Verdict: confirmed (re-derived; constants recomputed).** Derivation checked line by line. Multiply $(\star)$ by $\omega_j \ge 0$ ($\omega_{v-1} = 1$ keeps the inequality strict) and sum: the left side is $64\,\mathcal E_v - \sum_j \omega_j \kappa_j(\Gamma_j)$ by Lemma 3.2(3), the code lengths give $u_{J+1}(\lambda'_J|Z_J| + n_J \log_2(1 + 2^{-\lambda'_J}) + \log_2(L\chi/p)) + \sum_i u_{i+1}(\lambda_i d_i + m_i c_i)$ because $\sum_{j \ge i} \omega_j = u_{i+1}$. Step 1: $u_{i+1} m_i = \tfrac12(n - u_i|Z_i|)$ and $\sum_{i > i'} c_i = C_{i'+1}$. Step 2: $\lambda_i - C_{i+1}/2 = \lambda$. Step 3 is the nullity budget. Step 4: the coefficient of $|Z_J|$ is $u_{J+1}(\lambda'_J - 2\lambda - C_J) = 0$. Step 5: $\Gamma_j \le \mathcal E_v/u_{j+1} = \varepsilon n_{j+1}$ and $\omega_j/u_{J+1} = 2^{-(j-J+1)}$ for $j \le v - 2$, $2^{-(L-1)}$ for $j = v - 1$. Collected and divided by $n$ ($u_{J+1} n_J = n/2$, $u_{J+1}/n = 1/n_{J+1}$) this is $(64 - \lambda)\varepsilon < M(\lambda) + (\log_2(L/p) + \log_2\chi + c_\kappa(\varepsilon))/n_{J+1}$, as stated, with $\log_2 \chi \le L\, 2^{-37.4} < 2^{-32}$ for $n \le 2^{26}$. The fixed-point step needs only $\varepsilon \le 1 = \varepsilon^{(0)}$ and $\Psi$ nondecreasing. Items 1 to 3 follow as written (item 3: $D = \emptyset$ at the finer levels keeps $\mathcal E$ and $\mathcal N$).

What the theorem does and does not assume. Random: the twiddle pairs of levels $J + 1$ to $v$ only. Fixed and arbitrary: $T_J$, of which only "$e_J(Y) = 0$ when $\mathrm{null}_J(Y) \ge 1$" is used. T1 and T2 have the same constants because only (P1) to (P3) are used. The union bound is over all prefix labels (Kraft), so no structure of the flats is assumed. I found no error.

*Constants, recomputed from the text of Sections 4 and 5* (`scripts/75_eps0.py`, written without reading `73_eps0.py`; $p = 2^{-130}$, $\lambda$ on a grid of step 0.01):

| case | $64\varepsilon_0$ recomputed | best $\lambda$ | note 73 |
|---|---|---|---|
| rate 1/2, $J = 4$, $n = 2^{19}$ | 5.340 | 3.20 | 5.34 |
| rate 1/2, $J = 4$, $n = 2^{25}$ | 5.677 | 3.72 | 5.68 |
| rate 1/4, $J = 4$, $n = 2^{19}$ | 3.058 | 4.90 | 3.06 |
| rate 1/4, $J = 4$, $n = 2^{25}$ | 3.243 | 5.44 | 3.24 |
| rate 1/2, $J = 5$, $n = 2^{22}$ | 4.325 | 3.51 | 4.33 |
| rate 1/2, $J = 8$, $n = 2^{22}$; rate 1/4, $J = 8$, $n = 2^{22}$ | 3.139; 1.924 | 3.30; 4.91 | 3.14; 1.92 |
| rate 1/2, $J = 10$, $n = 2^{19}$; rate 1/4, $J = 10$, $n = 2^{25}$ | 2.617; 1.903 | 2.59; 5.03 | 2.62; 1.90 |

All nine agree to the digits printed. One presentational remark: the column "$M(\lambda)/(64 - \lambda)$ alone" of the note's table is evaluated at the $\lambda$ of one fixed $J$ (5), so it is not the main term of the other columns to the second digit (for $J = 4$, $n = 2^{19}$ I get 3.06 against the 2.99 printed); nothing depends on it.

### 5.4 Independent toy check of Theorem 5.1 (`scripts/75_toy.c`, `75_eps0.py`, `75_kraft.py`)

Field GF($2^8$), $n = 16$, top $T_J$ a random tree code conditioned on being MDS (every $k_J$-subset checked), lower levels random. For each code every subset $Z$ of the 16 leaves is visited and $E = \max\{|Z| - \mathrm{rk}(Z) : \mathrm{rk}(Z) < k\}$ recorded. The theorem with 64 replaced by 8 and $\chi = (1 - n/q)^{-L}$ gives, for each integer $s$, a bound on $\Pr[E \ge s]$ (the largest $p$ with $\varepsilon_0(p)\, n \le s$, best $\lambda$).

| case | $s$ | theorem: $\Pr[E \ge s] \le$ | measured T1 | measured T2 |
|---|---|---|---|---|
| rate 1/2, $k = 8$, $J = 2$ (one random level), 200000 codes | 3 | $2^{-7.84} = 4.4 \cdot 10^{-3}$ | $8.0 \cdot 10^{-5}$ | $1.5 \cdot 10^{-4}$ |
| | 4 | $2^{-15.8}$ | 0 | 0 |
| rate 1/2, $k = 8$, $J = 1$ (two random levels), 200000 codes | 4 | $2^{-2.02} = 0.25$ | $2.5 \cdot 10^{-4}$ | $4.6 \cdot 10^{-4}$ |
| | 5 | $2^{-5.88} = 1.7 \cdot 10^{-2}$ | 0 | $1.5 \cdot 10^{-5}$ |
| | 6 | $2^{-9.76}$ | 0 | 0 |
| rate 1/4, $k = 4$, $J = 1$ (one random level), 2000000 codes | 2 | $2^{-0.63} = 0.65$ | $1.6 \cdot 10^{-2}$ | $3.3 \cdot 10^{-2}$ |
| | 3 | $2^{-8.09} = 3.7 \cdot 10^{-3}$ | $8.2 \cdot 10^{-5}$ | $1.6 \cdot 10^{-4}$ |
| | 4 | $2^{-15.9} = 1.6 \cdot 10^{-5}$ | 0 | $2.5 \cdot 10^{-6}$ |

No violation. Where both sides are measurable the bound is loose in probability by a factor 6 to 55 with one random level and 500 to 1100 with two (one to two units of excess), which is the looseness the author describes and attributes to Lemma 2.1(c). The largest number of zeros of a nonzero codeword is $k - 1 + E$ in every code, as it must be. T1 shows about half the defect frequency of T2 at every $s$: in T1 a coincidence of used twiddles for sides $c$ is the same event as for the complementary sides (add 1 to all), so the labels come in pairs with identical events; the union bound does not see this, the theorem is the same for both. The Kraft sum of the prefix code equals 1 to twelve digits by enumeration of all labels on four tiny trees, for the note's multipliers and for arbitrary positive ones (`75_kraft_output.txt`).

## 6. Note 74, Theorem 4.4 and Proposition 6.1 (item 4)

### 6.1 Theorem 4.4 (three members: weight at most $5k/2 - 2$, attained)

**Verdict: confirmed (re-derived; T2 generic only).** Upper bound. With $t$ leaves where all three agree with the word and $n_2$ where exactly two do, $w = n_2 + 2t$. Each of the three differences is a nonzero codeword, so it has at most $k - 1$ zeros, and a triple leaf is a zero of all three: $n_2 + 3t \le 3k - 3$. Corollary 4.3(a): $n_2 + t \le 2k - 1$. Hence $w \le \min(3k - 3 - t,\ 2k - 1 + t) \le 5k/2 - 2$, with equality only at $t = k/2 - 1$, $n_2 = 3k/2$. Correct; the only input beyond MDS is $Q_3$, so the theorem inherits the scope of Corollary 4.3 (T2, generic). Attainment. Split level $v - 1$: three lines of the top $[N, 2]$ code meeting pairwise over three distinct blocks give $n_2 = 3 \cdot k/2$, and $B$ with $k/2 - 1$ zeros in a fourth block gives $t = k/2 - 1$; this needs $N = 2n/k \ge 4$, that is $n \ge 2k$, as stated. Independent check: the finite program of Section 4.3 at $M = 3$ returns $(1 + 5\rho/2)/3$ exactly (0.4375 at rate $2^{-3}$), the same two constraints; and the lifted three-member lists of `75_qt` (mode F) have pattern weight exactly $5k/2 - 2$ at their best (Section 6.3). The consequence "three codewords at $3n/4 - 1$ are optimal at rate 1/2" follows: $3a \le n + w$ gives $a \le 3n/4 - 2/3$.

### 6.2 Proposition 6.1 (one-sided staircase)

**Verdict: confirmed (re-derived, and re-encoded mostly at sizes the author did not use).** Derivation. Inside one block the map from the lower factor $B \in K^{2^i}$ to its values on the block is a bijection (one tree, distinct twiddles at every node), so there is a $B \ne 0$, unique up to a scalar, vanishing on $2^i - 1$ chosen leaves of $q_0$. Put $y = \beta_q\, B$ on each block $q \ne q_0$ and $y = 0$ on $q_0$. For a $k_{\rm up}$-subset $S$ of the other blocks, the top code being MDS, there is one top codeword $A_S$ with $A_S(q) = \beta_q$ on $S$, and $A_S \otimes B$ agrees with $y$ on the $k_{\rm up} 2^i = k$ leaves of $S$ and on the $2^i - 1$ zeros in $q_0$: agreement $k + n/N - 1$. For generic $\beta$ the interpolants are pairwise distinct, so there are $\binom{N-1}{k_{\rm up}}$ members. The variant with $f$ free blocks hands $f n/N + 1$ leaves to $M$ members, $\lfloor (fn/N + 1)/M \rfloor$ each. Correct. The statement is a lower bound on list sizes for every tree code whose top is MDS (and, as the note says, for Reed-Solomon on a subspace); it needs neither T2 nor generic twiddles beyond distinctness of the interpolants.

### 6.3 Computations for 6.1 and 6.2 (`scripts/75_qt.c` modes F and O, `75_qt_run2.sh`, output `75_qt_output2.txt`; GF($2^{64}$), T2)

*Theorem 4.4, attainment.* Lifted three-member lists at every split level, pattern weight $\sum_x (\text{largest group of equal members} - 1)$ computed from the encoded codewords: the largest weight over 650000 lists is exactly $5k/2 - 2$ at each size, 8 at $(4, 16)$, 18 at $(8, 16)$, $(8, 32)$, $(8, 64)$, 38 at $(16, 32)$, $(16, 64)$, never more.

*Proposition 6.1.* All members built by interpolation and encoded by butterflies (first 40000 in lexicographic order where there are more):

| $(k, n)$ | rate | split: blocks $N$, $k_{\rm up}$ | members | agreement, min = max | $k + n/N - 1$ |
|---|---|---|---|---|---|
| (8, 32) | 1/4 | 16, 4 / 8, 2 | 1365 / 21 | 9 / 11 | 9 / 11 |
| (16, 64) | 1/4 | 32, 8 / 16, 4 / 8, 2 | 40000 of $7.9 \cdot 10^6$ / 1365 / 21 | 17 / 19 / 23 | 17 / 19 / 23 |
| (8, 64) | 1/8 | 32, 4 / 16, 2 | 31465 / 105 | 9 / 11 | 9 / 11 |
| (4, 32) | 1/8 | 16, 2 | 105 | 5 | 5 |
| (16, 32) | 1/2 | 16, 8 / 8, 4 / 4, 2 | 6435 / 35 / 3 | 17 / 19 / 23 | 17 / 19 / 23 |
| (32, 64) | 1/2 | 32, 16 / 16, 8 / 8, 4 / 4, 2 | 40000 of $3.0 \cdot 10^8$ / 6435 / 35 / 3 | 33 / 35 / 39 / 47 | 33 / 35 / 39 / 47 |

No singular interpolation, no two equal members (all pairs among the first 3000), the member counts are $\binom{N-1}{k_{\rm up}}$, and every member has exactly the predicted agreement. The counts 21 at $3/8 - 1/n$ and 1365 at $5/16 - 1/n$ (rate 1/4), 35 and 6435 (rate 1/2) are those of the note. As a further test of Corollary 4.3 on structured lists, 20000 random sub-lists of 3, 4 and 5 members were drawn from each staircase: the number of coincidence leaves never exceeds $(t-1)k - 1$, and reaches it for $t = 3$ on the staircases with $k_{\rm up} = 2$ (7 at $(4, 32)$, 15 at $(8, 32)$ and $(8, 64)$, 31 at $(16, 32)$ and $(16, 64)$, 63 at $(32, 64)$).

## 7. Reproduction

All scripts are in `scripts/`, run from that directory; C needs only `cc`, Python is `/usr/bin/python3` with numpy and scipy.

| file | what it does | time |
|---|---|---|
| `75_gf.h` | GF($2^{64}$) arithmetic, rank, reduced echelon form, kernel; self-test | |
| `75_qt.c`, `75_qt_run.sh` -> `75_qt_output.txt` | Theorem 4.2 and Corollary 4.3 of note 74: exhaustive (E), sampled (S), lifted lists (F); T1 and T2 | 10 min, 4 cores |
| `75_qt_run2.sh` -> `75_qt_output2.txt` | one-sided staircases (O), pattern weights of lifted three-member lists, T1 at $k = 2$, T1 with three members | 5 min, 4 cores |
| `75_lp.py` -> `75_lp_output.txt` | limit program with dual certificates; finite program with exact rational certificates; Proposition R2; the table of Section 4.3 | 2 min |
| `75_lp_johnson_point.py`, `75_lp_t1.py`, `75_lp_fewJ.py` (each with its `_output.txt`) | list size at the Johnson radius; hypothetical T1 thresholds; thresholds from $Q_2..Q_{J+1}$ only | 1 to 3 min each |
| `75_eps0.py` -> `75_eps0_output.txt` | $\varepsilon_0$ of note 73 from its formulas, for $q = 2^{64}$ and for the toy field | seconds |
| `75_kraft.py` -> `75_kraft_output.txt` | Kraft sum of note 73's prefix code by enumeration of labels | seconds |
| `75_toy.c`, `75_toy_run.sh` -> `75_toy_output.txt` | Theorem 5.1 of note 73 over GF($2^8$), $n = 16$: every subset of leaves, 200000 codes a case | 9 min, 4 cores |
