# 42. Referee of note 36 (random evaluation points), and the multi-parent count

Researcher 42 (round 6), hostile referee of `36-proven-evaluation-sets.md`, then an attempt at the regularization lemma that note 36 leaves open. Notation is that of note 36: a field $F$ with $q$ elements, a sampling set $S$ of $m$ elements, $a = (a_1, \dots, a_n)$ a uniformly random tuple of distinct elements of $S$, polynomials of degree $< k$ ($k$ is the analysis dimension), $h = k - 1$, $\lambda = \log_2(m/h)$, $\rho = k/n$, $\tau = A/n$, $B_T(d) = \Pr[\mathrm{Bin}(T, d) \ge 2]$, queries $= \lceil 108/\log_2(1/\tau)\rceil$. Statuses: **[proved]** (a proof in note 36 that I rechecked line by line, or a proof given here; the proofs given here are by one researcher and unrefereed), **[checked]** (numerically, sizes given), **[lit]** (read in the cited paper), **[estimate]**, **[heuristic]**, **[conjectured]**.

## 0. Verdict

1. **Theorem B of note 36 is correct.** Every step holds as written: the averaging lemma, the count of Lemma B1, the inclusion of the bad event in a union of star events, the tilted union bound, the treatment of interleaved and $E$-valued words, of the degree slack and of distinct points (section 1, **[proved]**). I found no gap in the proof. The statement can even be strengthened for free: the same thresholds hold, to five decimals, with the list bound $2^{32}$ in place of $2^{64}$ (**[checked]**).
2. **The tables of note 36 are valid and slightly conservative.** My own implementation of the final inequality, with an exact convex envelope, continuous tilts and a 60-digit re-evaluation, gives at level 0 with points in $K$: $\tau = 0.68391, 0.46214, 0.30757, 0.20037$ at rates $1/2$ to $1/16$ (198, 97, 64, 47 queries), against $0.6844, 0.4622, 0.3079, 0.2007$ (198, 98, 64, 47) in note 36. Every entry of note 36 that I recomputed is above mine, by at most $0.0007$ in $\tau$. Two query counts change, both in favour of the theorem: 97 instead of 98 at level 0, rate $1/4$, and 12 instead of 13 at level 4 with points in $K$ (section 2, **[checked]**).
3. **The toy check of note 36 has no power, and a check with power cannot be made on $\Pr[\mathrm{Bad}]$ itself.** At sizes that can be enumerated the union bound of the theorem is above 1 whenever lists exist. What can be tested with power is the quantity the proof bounds, the expected number of bad configurations. On honest lists (complete 5-laterals: five lines through ten random abscissas over $\mathbb{F}_p$) the observed expectation is $0.49, 0.68, 0.81, 0.95$ times the prediction of Lemma B1 at $p = 53, 101, 211, 499$, where the prediction is $3193, 564, 101, 16$: the lemma holds and is asymptotically tight there. Exhaustively over all $5^n$ patterns of three members and all point tuples ($\mathbb{F}_{11}$ to $\mathbb{F}_{17}$, $n \le 7$, $k \le 3$) there is no violation (section 3, **[checked]**).
4. **Proposition 7.2 (the generic-rank theorem fails on coset unions) is correct**, with a simplification: the whole agreement hypergraph of its example is $(k'+1)$-weakly-partition-connected, no sub-hypergraph is needed. On nine explicit examples over $\mathrm{GF}(2^8)$ the reduced intersection matrix has full column rank at random points and corank exactly 1 on every coset union tried (section 3.4, **[proved]** and **[checked]**).
5. **The description of Ferber, Kwan and Sauermann is accurate** (section 4, **[lit]**), with two omissions in the quoted hypotheses that do not matter at our sizes.
6. **Theorem A was not refereed line by line.** Its only use with points in $K$ is negative, and with points in $E$ it is dominated by cost. Its two lemmas are correct; its main proof leans on "Lemmas 3.2 to 3.8 of [AGGLZ] hold verbatim" with a modified bank, which I did not verify. The number $0.6388$ should be read as unrefereed.
7. **The regularization lemma of note 36, section 6, as stated, is false, and the corrected statement stays open; a weaker multi-parent theorem is proved here.** (a) The count generalizes cleanly (Lemma M, **[proved]**, **[checked]** exactly at three and four members). (b) The list budget can be spent exactly as the brief hoped: one pigeonhole step costs a factor $n(n+1)$ of the list and makes one overlap count the same for all remaining members (Lemma R, **[proved]**); this removes the Jensen obstruction, because the caps become deterministic. (c) With two such steps, Theorem C (**[proved]**, numbers **[checked]**): for random points of $K$ and a list bound $2^{180}$, $\tau = 0.6811, 0.4567, 0.3007, 0.1950$ at level 0, that is **195, 96, 63, 46 queries** against 198, 97, 64, 47 for Theorem B. (d) The values 184, 83, 52, 38 of note 36 are reproduced as a heuristic on regular lists; a better reading of the same count gives 169, 78, 50, 36, still a heuristic. (e) "As good as independent sets of the same density" fails: a list of independent sets with two coordinate densities has, at rate $1/8$, a count that is worse than the regular one by $0.38n$ bits for every tuple, up to fluctuations of order $\sqrt{bn}$ (section 5.5, **[checked]**); the effect on the thresholds is $0.0002$, so the right benchmark is the worst product profile, and at rates $1/2$ and $1/4$ no two-point profile beats the regular one. (f) What blocks the remaining gap (195 proved against 184 or 169 heuristic) is identified: upper bounds on the overlaps between leaves inside the region covered once by the parents, for which the only handle is the pairwise bound $h$.
8. **One claim of note 36 is too strong**: "at level 0 the budget cannot buy more inside these proofs" (its verdict 3 and section 5.3). Theorem C is a first-moment proof of the same kind in which a budget of $2^{180}$ moves $\tau$ in the third decimal. A second mechanism, choosing the best tuple instead of an average one, is worth $\Theta(\sqrt{bn})$ bits on random-like lists and not $O(tb)$ (**[estimate]**, section 5.6).
9. **Cost and independence** (section 6). The proof uses the joint near-uniformity of all labeled points, about $0.9n$ of them and up to $n$; $t$-wise independence is useless and independence between blocks gives exactly Theorem B$_w$. No evaluation set with an NTT-like encoder satisfies the hypotheses. The estimate of 50 to 100 level-0 NTTs for multipoint evaluation is plausible and, if anything, optimistic.

## 1. Theorem B, step by step

| step of note 36 | verdict | remark |
| --- | --- | --- |
| Lemma 1 (averaging, section 3.1) | correct | Needs $\varphi \ge 0$ and $M \ge t$. The sets may repeat as long as the members are distinct. The conditioning step is right: $\mathbb{E}\Phi \le \mathbb{E}[\Phi \mid \text{no repetition}] + \Pr[\text{repetition}]\,n\varphi_{\max}$. |
| Canonical labeling, event $E_T$ (4.1) | correct | The word disappears because every labeled condition is an equality between two members. |
| Lemma B1 | correct | The proof counts pairs (point tuple, $(g_j)$) and divides by the number of tuples, so it bounds the expected number of bad configurations, which is what section 3 tests. The proof gives the factor $m^n/(m)_n$, at most $e^{n^2/(m-n)}$. When some $c_j \ge k$ the event is empty. |
| Inclusion $\mathrm{Bad}(A, M) \subseteq \bigcup_{T : \Psi(T) \ge \Psi_0} E_T$ (4.2) | correct | $\bar\varphi = \psi$ is right: $\alpha(t-1)d^2 + \beta(1-d)B_{t-1}(d)$. The members chosen by Lemma 1 are distinct polynomials and $c_j = \lvert I_1 \cap I_j\rvert \le h$, so no cap is needed: this is what makes the star linear. |
| Tilted union bound | correct | $q^{-W_\mathsf{D}}2^{-\lambda g} \le 2^{-\Psi_0}q^{-s_\mathsf{D}W_\mathsf{D}}2^{-s_\mathsf{C}\lambda g}$ on the class, and the sum over all labelings is the $n$-th power of $(1 + q^{-s_\mathsf{D}})^{t-1} + \binom{t-1}{2}2^{-s_\mathsf{C}\lambda}$ (**[checked]** exactly at $t = 3$). |
| Final formula | correct | $\varphi_{\max} = \max(\alpha(t-1), \beta)$ would do; immaterial. |
| Convexity | correct | $\psi'' = 2\alpha T + \beta T(T-1)(1-d)^{T-2}(1 - (T+1)d)$ with $T = t - 1$: one sign change down and one up at most, so $\psi^{cc}$ is $\psi$ outside one interval and a chord on it. At level 0 ($t \le 12$) $\psi$ is convex and $\psi^{cc} = \psi$. |
| Degree slack | correct | $k = 2^\kappa + \ell$ is used as the dimension throughout; nothing else depends on $\ell$. |
| Distinct points | correct | Handled by the count over injective tuples; the term $n^2/((m-n)\ln 2)$ is $2^{-14}$ bits at level 0. |
| Theorem B' (points of $E \setminus K$) | correct | A polynomial over $K$ vanishing at $c$ pairwise non-conjugate points of $E \setminus K$ lies in a space of $2^{128(k/2 - c)}$ elements, and has at most $h/2$ roots in $S$. |
| Corollary 4.3 (interleaved, $E$-valued) | correct | The combination must avoid $\binom t2$ proper subspaces of $F^L$, possible since $\binom t2 q^{L-1} < q^L$. An $E$-valued polynomial at points of $K$ is two $K$-lanes with the same agreement columns. No loss. |
| Theorem B$_w$ (4.3) | correct (proof read, table T6 not recomputed) | The probability of a coset of type $\mathsf{C}$ is bounded below by a sum over its points of a function of $d_i$, and the pattern function itself is in $[0, \beta]$, so Lemma 1 applies. |
| Numerical method of `36_bounds.py` | correct with changes | The envelope is taken on a uniform grid of 1000 points and lowered by the largest second difference over 8. This is not an error bound when $\psi''$ varies inside a cell, which happens for $t \ge 100$ (levels 4 and 5; at level 5 $\tau$ itself is below the first grid point). The printed values are nevertheless valid: all are above the exact thresholds (section 2). |
| Section 7, "it holds for $\nu$-wise independent points with $\nu \approx 0.90n$" | correct with changes | The union bound runs over all labelings of weight at least $\Psi_0$, and these can label every coordinate, so the proof as written uses $n$-wise independence. A version for $\nu < n$ would have to drop labels and pay for it. Harmless: the note draws no consequence. |
| Section 5.3, "the budget cannot buy more at level 0 inside these proofs" | false as stated | See verdict 8 and section 5. |

Two remarks on what the theorem is. First, Lemma B1 pays $\log_2 q$ for every dimension of a member that the centre does not pin, and gets back only $\lambda = \log_2(m/h)$ for a shared point outside the centre, because it counts "at most $h$ roots". A shared point is also a linear condition on the two members, worth $\log_2 q$ while they still have freedom. Using shared points that way is exactly the multi-parent count (section 5), and it is where the missing 24 bits a coordinate are. Second, the theorem is an existence statement over the set and a statement about the first moment over patterns: Proposition 7.1 of note 36 (correct) says that such a proof needs about $2.9n$ bits of seed at level 0.

## 2. Thresholds recomputed

`scripts/42_theoremB.py`, nothing shared with `36_bounds.py`. The envelope is exact (bisection on the common slope of the two convex branches). The tilts are optimized continuously and $t$ over all integers up to 24 (level 0) or a geometric list up to 1024 (later levels). The threshold is the fixed point of "optimize at $\tau$ (cold over all $t$, then warm over the nearby $t$), bisect in $\tau$ at fixed parameters". The reported $\tau$ is rounded up to five decimals (six at the short codes) and the bound is re-evaluated there in 60-digit decimal arithmetic with a supporting-line certificate: any line below $\psi$ bounds $\psi^{cc}$ from below, and the minimum of $\psi$ minus the line is located by the convexity structure and cross-checked on a scan of 40000 points. In every row the float and the 60-digit values agree to the printed digit, and two units of the last digit below the threshold the best bound found is positive. List size $2^{64}$, failure $2^{-100}$. All **[checked]**.

Level 0, $k = 2^{24} + 6$:

| rate | Johnson | points in $K$: mine | note 36 | points in $E$, code over $E$: mine | note 36 | Theorem B': mine | note 36 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | 0.7071, 217 | **0.68391, 198** ($t = 4$) | 0.6844, 198 | 0.66482, 184 ($t = 4$) | 0.6654, 184 | 0.43679, 91 | 0.4368, 91 |
| 1/4 | 0.5000, 109 | **0.46214, 97** ($t = 5$) | 0.4622, **98** | 0.43679, 91 ($t = 5$) | 0.4368, 91 | 0.28014, 59 | 0.2803, 59 |
| 1/8 | 0.3536, 73 | **0.30757, 64** ($t = 7$) | 0.3079, 64 | 0.28014, 59 ($t = 8$) | 0.2803, 59 | 0.17390, 43 | 0.1742, 43 |
| 1/16 | 0.2500, 55 | **0.20037, 47** ($t = 10$) | 0.2007, 47 | 0.17390, 43 ($t = 12$) | 0.1742, 43 | 0.10395, 34 ($t = 18$) | 0.1043, 34 |

The 98 of note 36 at rate $1/4$ is an accident of its coarser optimization: 97 queries need $\tau \le 0.462204$, the exact threshold is $0.46214$, and `36_bounds.py` returns $0.46224$ (its unrounded values at level 0 are $0.68444, 0.46224, 0.30787, 0.20067$).

All sizes, points in $K$, $k = \rho n + 6$ (the threshold moves with $n$ at a fixed rate because $\lambda = 64 - \log_2 h$ does):

| $n$ | rate 1/2 | 1/4 | 1/8 | 1/16 |
| --- | --- | --- | --- | --- |
| $2^{25}$ | 0.68391, 198 | 0.46074, 97 | 0.30441, 63 | 0.19566, 46 |
| $2^{26}$ | 0.68488, 198 | 0.46214, 97 | 0.30599, 64 | 0.19721, 47 |
| $2^{27}$ | 0.68584, 199 | 0.46354, 98 | 0.30757, 64 | 0.19878, 47 |
| $2^{28}$ | 0.68681, 200 | 0.46494, 98 | 0.30917, 64 | 0.20037, 47 |

Later levels of the $\mu = 30$, $R = 1$ ladder ($k = 2^{24-4i} + 4$, $n = 2^{25-i}$):

| level, rate | Johnson | points in $K$: mine | note 36 (its unrounded value) | points in $E$: mine | note 36 |
| --- | --- | --- | --- | --- | --- |
| 1, $2^{-4}$ | 0.2500, 55 | 0.19411, 46 ($t = 10$) | 0.1946, 46 | 0.17111, 43 ($t = 12$) | 0.1714, 43 |
| 2, $2^{-7}$ | 0.0884, 31 | 0.04185, 24 ($t = 31$) | 0.0425, 24 | 0.03488, 23 ($t = 32$) | 0.0350, 23 |
| 3, $2^{-10}$ | 0.0313, 22 | 0.008700, 16 ($t = 80$) | 0.0089, 16 | 0.007160, 16 ($t = 80$) | 0.0073, 16 |
| 4, $2^{-13}$ | 0.0111, 17 | 0.001844, **12** ($t = 192$) | 0.0020 (0.001973), **13** | 0.001501, 12 ($t = 224$) | 0.0016, 12 |
| 5, $2^{-16}$ | 0.0043, 14 | 0.000455, 10 ($t = 448$) | 0.0005 (0.000515), 10 | 0.000367, 10 ($t = 512$) | 0.0004, 10 |

Differences from note 36: none that weakens it. Its values are upper bounds of the exact thresholds, by at most $0.0006$ at level 0 and by up to 13% of $\tau$ at levels 4 and 5 (coarse grids in $t$, in the tilts and in the envelope, and a bisection of 15 steps). The sum over the six levels with points in $K$ is 306 queries against 356 at Johnson (307 in note 36).

The list size. The term $\binom t2 n(\alpha(t-1) + \beta)/M$ is below one bit as soon as $M \ge 2^{40}$ at level 0. Running the same search with $M = 2^{48}, 2^{40}, 2^{36}, 2^{32}$ gives the four level-0 thresholds unchanged to five decimals (**[checked]**, `42_theoremB.py listsize`). So Theorem B proves H_K$(\tau, 32)$ on a random set, inside the default budget of the protocol.

Not recomputed: Theorem A (tables T3, T4), Theorem B$_w$ (T6), the subset-of-a-subspace table T7, the encoding costs.

## 3. Tests

### 3.1 Why a frequency test of $\Pr[\mathrm{Bad}]$ has no power, and what has

The bound of Theorem B is $q^{(t-1)k}2^{-\Psi_0}Z^n$ with $Z \ge 2^{t-1}$ before tilting: at $n = 10$ and $t = 5$ the pattern factor alone is about $10^{10}$, so the bound is below 1 only for fields so large that the event never occurs in a simulation. This is not a defect of the test design: the theorem is nontrivial only when $n$ is large. Note 36 says the same of its own check ("the bound is rarely below the trivial one except where it is zero"). A second obstacle: for three members the patterns that honest lists produce have weight $W_\mathsf{D} + g \le 3h < 2k$ unless $k \ge 4$, so for lines and conics Lemma B1 is never below 1 on a feasible pattern, and $\Pr[E_T]$ is exactly 0 on every pattern where it is.

Each inequality of the chain can be tested separately, and the one that carries the theorem is Lemma B1 read as it is proved: the expected number of pairs (labeling, tuple of polynomials) that are bad. That number is neither 0 nor trivial on honest configurations.

### 3.2 Honest lists: complete 5-laterals (**[checked]**, `scripts/42_lateral.c`)

Lines ($k = 2$) over $\mathbb{F}_p$, $n = 10$ random distinct abscissas, agreement $A = 4$, list size 5. **[proved]** Five distinct lines agreeing with one word on four columns each: the lines agreeing at a column are concurrent there and two lines meet once, so $\sum_i\binom{r_i}{2} \le 10$ with $\sum_i r_i \ge 20$ forces $r_i = 2$ at every column. Hence $\mathrm{Bad}(4, 5)$ holds exactly when the ten abscissas are those of the ten intersection points of five lines, no word has six such lines, and the decision is exhaustive: enumerate the bijections from pairs of lines to columns and solve for the slopes. A bijection is the canonical star labeling of the ordered list, with $W_\mathsf{D} = 4$ and $g = 6$, so Lemma B1 predicts that the expected number of pairs (bijection, four lines $g_2, \dots, g_5$) is at most $10!\,p^{-2}\,p^{10}/(p)_{10}$. Each solvable bijection carries exactly $p - 1$ tuples of lines (scaling).

| $p$ | samples | $\Pr[\mathrm{Bad}(4,5)]$ observed | expected configurations, observed | predicted by Lemma B1 | ratio |
| --- | --- | --- | --- | --- | --- |
| 53 | 20000 | 0.218 | 1573 | 3193 | 0.49 |
| 101 | 60000 | 0.0311 | 381 | 564 | 0.68 |
| 211 | 200000 | 0.00323 | 81.5 | 101.2 | 0.81 |
| 499 | 1300000 | 0.000255 | 15.2 (331 hits, $\pm 6\%$) | 15.96 | 0.95 |

The prediction is in the window asked for ($16$ to $3000$ expected configurations), the observation is below it in every row and tends to it. A count wrong by a factor $p$, or by a factor $h$ per shared point, or a missing factor for distinctness, would show. The ratio tends to 1 because for lines the count of the proof is an exact count up to degenerate cases. For $k > 2$ the lemma is looser by design: it allows $h$ roots where a typical difference has about one.

### 3.3 All patterns of three members, exhaustively (**[checked]**, `scripts/42_toy.c`, `scripts/42_toy_check.py`)

For $(p, n, k) = (13, 6, 2), (17, 6, 2), (11, 6, 2), (11, 7, 2), (11, 6, 3)$: every point tuple (normalized by the affine symmetry), every pair $(g_2, g_3)$, every one of the $5^n$ patterns (15625 or 78125). The program computes $\Pr[E_T]$ and the expected number of pairs satisfying $T$, exactly. Results: the counts depend only on the numbers of labels of each kind (exchangeability, 0 violations); the expected number of configurations never exceeds Lemma B1, with the exact factor $m^n/(m)_n$ and with the value 0 when a member has $k$ zeros (0 violations in the five runs); it never exceeds Lemma M of section 5 either, for every reading of the pattern and both orders of the members. In the window $[0.01, 100]$ of the prediction at most one count vector with a nonzero expectation exists in each run: $(1,1,1,0)$ for lines, expected $p - 1$ against $p \cdot p^n/(p)_n$ (12 against 50.8 at $p = 13$, 16 against 46.0 at $p = 17$, 10 against 58.6 at $p = 11$, $n = 6$, outside the window at $n = 7$), and $(2,2,2,0)$ for $k = 3$, expected 1.27 against 21.3 for Lemma B1 and 10.7 for Lemma M. So this run establishes validity over all patterns, including the infeasible ones, and has little to say on tightness; 3.2 does.

The same program, with exhaustive enumeration of all words over $\mathbb{F}_{11}$, $n = 6$, lines: the largest list at agreement 3 is 4 for 2160 of the 3024 normalized point tuples and 3 for the others; at agreement 4 it is 1. A list of 4 is a complete quadrilateral; its star patterns have weight 3, where the bound is $p$: nothing to test, as said in 3.1.

Lemma 1 on explicit irregular families (two populations, cores, a two-point profile, nested populations; $n \le 40$, $M \le 40$, $t = 3, 4$): the exact maximum over all ordered tuples is above the bound in all 75 cases (`scripts/42_lemmas_check.py`). At these sizes the correction $\binom t2 n\varphi_{\max}/M$ is large, so this test is weak; the lemma is a two-line averaging and I rely on the proof.

### 3.4 Proposition 7.2 on concrete examples (`scripts/42_coset_rank.py`)

**[proved]** A simplification of the statement. In the example of note 36 ($t = m_0 + 2$ cosets of a subspace with $w$ elements, dimension $k' + 1 = w m_0 + 1$, member $\gamma_0$ agreeing with the word $L_U^{m_0+1}$ exactly on the cosets $\gamma \ne \gamma_0$) the agreement hypergraph has $w$ copies of the edge $[t] \setminus \{\gamma_0\}$ for each $\gamma_0$. For a partition with $r$ parts of which $s$ are singletons, $\sum_e(\lvert P(e)\rvert - 1) = w(t(r-1) - s)$, and $w(t(r-1) - s) \ge (w(t-2) + 1)(r-1)$ because $s \le r - 1$ when $r < t$ and $w(t-2) \ge t - 1$ when $r = s = t$. So the whole hypergraph is $(k'+1)$-weakly-partition-connected and [AGGLZ] Lemma 2.4 is not needed.

**[checked]** For $(w, m_0) \in \{2\} \times \{1, 2, 3, 5\} \cup \{4\} \times \{1, 2, 3\} \cup \{8\} \times \{1, 2\}$ over $\mathrm{GF}(2^8)$, 20 random choices of the coset representatives each: the members $G_{\gamma_0} \circ L_U$ have degree at most $k'$, are distinct, agree with the word exactly as claimed, and give a nonzero kernel vector of the reduced intersection matrix; the weak partition connectivity, computed over all partitions of $[t]$, is at least $k' + 1$ (equal to it for $w = 2$); the matrix has full column rank $(t-1)(k'+1)$ at 20 random point sets with the same edges and rank exactly $(t-1)(k'+1) - 1$ on every coset union. The smallest instance: $w = 2$, $m_0 = 1$, six points in three cosets $\{c, c+1\}$, three polynomials of degree at most 2, pairwise equal on one coset; $f_1 - f_2$, $f_2 - f_3$, $f_1 - f_3$ are multiples of the three quadratics $L_U - v_\gamma$, which span a space of dimension 2 on a coset union and 3 at generic points.

## 4. The paper of Ferber, Kwan and Sauermann

arXiv 2012.10584v2, fetched with `curl` into the scratchpad directory `papers42`, read completely as a PDF (9 pages). **[lit]**

- Theorem 3 as quoted in note 36 (agreement $3ch/n$, list $\lfloor n/(ch)\rfloor$, failure $q^{-h/4}$, $c \ge 5$, $h \le q^{-1/c}m$, $3ch < n \le \sqrt{\log_2 q\cdot c/8}\,h$): accurate, with two omissions: the second term of the minimum, $e^{h/(4c^3)}(c/2)h$, and "$q$ sufficiently large with respect to $c$" (used for $n/m < 1/2$ and $2n^2/m < h\log_2 q/12$). Neither binds at our sizes.
- "$(mq)^z$ choices for the points and the word values on a determining set of $z$ coordinates; $2^{n(L+1)}$ set systems against $q^{-h/2}$": accurate (proof of Theorem 4, with $Z \subseteq M$ a random subset of the coordinates in at least two sets, $\lvert Z \cap I_t\rvert > h$; proof of Theorem 3).
- "$\log_2 q \ge 648c^3 \ge 81000$ to beat Johnson": correct ($3c\rho < \sqrt\rho$ and $1/\rho \le \sqrt{\log_2 q\cdot c/8}$).
- What Theorem B changes, as claimed: the code is linear, so the members are counted through their differences from the centre and the $q^{\lvert Z\rvert}$ word values disappear; the list is not taken whole but a star of $t$ members is extracted by averaging, which requires a large list where [FKS] bound it by $n/(ch)$; the union bound over set systems is tilted. I add: [FKS] hold for any code of distance $m - h$, Theorem B needs linearity; and the model of randomness is the same (a uniform tuple of distinct positions).

So "a sharpened form of the counting argument of [FKS]" is a fair description. It is a different theorem, not a corollary.

## 5. The multi-parent count

### 5.1 The count, in general

A **labeling** $T$ of an ordered tuple of $t$ members gives each coordinate one of: nothing; $\mathsf{F}(p, U)$ with $1 \le p < t$ and $\emptyset \ne U \subseteq \{p+1, \dots, t\}$ ("free": the point is unconstrained, and each $j \in U$ uses $f_j(a_i) = f_p(a_i)$); $\mathsf{R}(p, p', U)$ with $p < p'$ and $U \subseteq \{p'+1, \dots, t\}$ ("root": $f_p(a_i) = f_{p'}(a_i)$, and each $j \in U$ uses $f_j(a_i) = f_p(a_i)$). Let $c_j(T)$ be the number of coordinates whose label has $j \in U$ (the **units** of member $j$), $g(T)$ the number of $\mathsf{R}$ labels (the **roots**), and $E_T$ the event that pairwise distinct $f_1, \dots, f_t$ of degree $< k$ satisfy all these equalities.

**Lemma M (sequential count). [proved]** $\Pr[E_T] \le \dfrac{m^n}{(m)_n}\,q^{\sum_{j \ge 2}(k - c_j(T))_+}\,(h/m)^{g(T)}$.

*Proof.* Take $f_1 = 0$ (the event is invariant under a common translation). Count pairs $(a, (f_j)_{j \ge 2})$. Choose the points of the $\mathsf{F}$ coordinates, at most $m$ ways each. For $j = 2, \dots, t$ in turn: the points of the coordinates $\mathsf{R}(p, j-1, U)$ are roots of $f_p - f_{j-1}$, a nonzero polynomial already determined, at most $h$ ways each; then $f_j$ has prescribed values at the $c_j$ points of the coordinates with $j \in U$, all chosen by now (an $\mathsf{F}(p, U)$ point from the start with $p < j$, an $\mathsf{R}(p, p', U)$ point since step $p' + 1 \le j$) and distinct: at most $q^{(k - c_j)_+}$ polynomials. Finally the $\mathsf{R}(p, t, \emptyset)$ points are roots, the unlabeled points are free. Divide by the number $(m)_n$ of tuples. $\square$

Lemma B1 is the case where every $\mathsf{F}$ has $p = 1$ and every $\mathsf{R}$ has $U = \emptyset$. Lemma 6.1 of note 36 (which I checked: correct) is the reading "$\mathsf{F}$ if the second member of the coordinate is at most $r$, $\mathsf{R}$ otherwise". **[checked]** For three members, where the labels with the same meaning are $\mathsf{F}(1,\{2\}) \sim \mathsf{R}(1,2,\emptyset)$, $\mathsf{F}(2,\{3\}) \sim \mathsf{R}(2,3,\emptyset)$, $\mathsf{F}(1,\{2,3\}) \sim \mathsf{R}(1,2,\{3\})$, the exact expected number of configurations is below the smallest bound over all readings and both orders, for all patterns, in the five exhaustive runs of 3.3. For four members over $\mathbb{F}_7$ (lines, $n = 5$, all 23 labels): exact expectations for 3000 random labelings and for all 15504 multisets of five labels from the alphabet of Theorem C below, no violation (`scripts/42_lemmaM_t4.py`).

The best reading for a given tuple (**[proved]**, by an exchange argument, since $\log_2 q > \lambda$): let $z_j = \lvert I_j \cap (I_1 \cup \dots \cup I_{j-1})\rvert$ and $u_j$ the number of points of $I_j$ whose second member is $j$. Member $j$ takes $\min(z_j, k)$ units and turns $\min(u_j, (z_j - k)_+)$ of the points whose second member it is into roots. The exponent is $\log_2 q\sum_j(k - z_j)_+ - \lambda\sum_j\min(u_j, (z_j - k)_+)$. It is at most that of Lemma 6.1 for every $r$.

The difficulty named in note 36 is real and is the cap: $\alpha\min(z_j, k) + \beta\min(u_j, (z_j - k)_+)$ is concave in the pattern counts, so the average over tuples is below the value at the average tuple, and Lemma 1 gives nothing.

### 5.2 Spending the list: exact regularity

**Lemma R (one pigeonhole step). [proved]** Let $\mathcal{L}$ be $N \ge 2$ subsets of $[n]$ and $X \subseteq [n]$ nonempty with $\lvert I \cap X\rvert = y$ for every $I \in \mathcal{L}$. Then there are $I^\ast \in \mathcal{L}$, an integer $v \ge y^2/\lvert X\rvert - y/(N-1) - 1$, and at least $(N-1)/(n(n+1))$ members $I \ne I^\ast$ with $\lvert I \cap I^\ast \cap X\rvert = v$.

*Proof.* With $m_i$ the number of members containing $i$, $\sum_{I \ne I'}\lvert I \cap I' \cap X\rvert = \sum_{i \in X}m_i(m_i - 1) \ge N^2y^2/\lvert X\rvert - Ny$ by Cauchy-Schwarz. So some $I^\ast$ has $\sum_{I \ne I^\ast}v_I \ge (N-1)\mu$ with $v_I = \lvert I \cap I^\ast \cap X\rvert \in [0, y]$ and $\mu \ge y^2/\lvert X\rvert - y/(N-1)$. If $G$ is the set of $I$ with $v_I \ge \mu - 1$ then $(N-1)\mu \le \lvert G\rvert y + (N-1)(\mu - 1)$, so $\lvert G\rvert \ge (N-1)/y$, and the values on $G$ take at most $y + 1$ values. $\square$

**[checked]** on 15 explicit families, two successive steps (`42_lemmas_check.py`).

This is the regularization the brief asked for, in its simplest form: for a factor $n(n+1)$ of the list, about $2\log_2 n \le 56$ bits, one overlap count becomes the same number for every remaining member, and that number is at least what independent sets would give. After the step nothing about that count is random any more, so a cap on it is a deterministic statement and Jensen is not needed. A budget of $2^{1000}$ pays for 16 steps at level 0. What a step cannot do is make two counts regular with one choice of $I^\ast$ that is good for both: only one linear combination can be guaranteed above its average. That is the limit met in 5.4.

### 5.3 Theorem C: two parents

Members: a centre $I_1$, a second parent $I_2$, leaves $3, \dots, t$. Let $B^{cc}_T$ be the convex envelope of $B_T$ on $[0,1]$ ($B_T$ up to the point $a_T$ of tangency from $(1,1)$, the chord after it).

**Theorem C. [proved]** Let $t \ge 4$, $s_\mathsf{D}, s_\mathsf{C} \in (0,1)$, $\alpha = (1 - s_\mathsf{D})\log_2 q$, $\beta = (1 - s_\mathsf{C})\lambda$, $x = q^{-s_\mathsf{D}}$, $y = 2^{-s_\mathsf{C}\lambda}$, and $M \ge 2^{64}(n(n+1))^2 + (n+1)^2$. For integers $c_1, c_2$ put $z = c_1 + c_2$, $x_2 = n - 2A + c_1$, $y_2 = A - z$ and
$$\Psi_C(c_1, c_2) = \alpha\bigl(c_1 + (t-2)\min(z, k)\bigr) + \beta\bigl((z - k)_+ + x_2\,B^{cc}_{t-2}(y_2/x_2)\bigr),$$
and let $\Psi_0$ be the minimum of $\Psi_C$ over $A^2/n - 2 \le c_1 \le h$ and $(A - c_1)^2/(n - A) - 2 \le c_2 \le \min(A - c_1, h)$. Then
$$\log_2\Pr[\mathrm{Bad}(A, M)] \le (t-1)k\log_2 q - \Psi_0 + n\log_2 Z_C + \beta\binom{t-2}{2}\frac{n}{2^{64}} + \frac{n^2}{(m-n)\ln 2},$$
$$Z_C = (1+x)^{t-1} + (1+x)^{t-2} - 1 + 2y(1+x)^{t-3} + \binom{t-2}{2}y.$$

*Proof.* Take $M$ members and subsets $I$ of size $A$ of their agreement sets; two of them share at most $h$ points. Lemma R with $X = [n]$ gives $I_1$, a value $c_1 \ge A^2/n - 2$ and a class $\mathcal{L}_1$ of at least $(M-1)/(n(n+1))$ members with $\lvert I \cap I_1\rvert = c_1$. Lemma R on $\mathcal{L}_1$ with $X = [n] \setminus I_1$, where every member has $A - c_1$ points, gives $I_2 \in \mathcal{L}_1$, a value $c_2 \ge (A - c_1)^2/(n - A) - 2$ and a class $\mathcal{L}_2$ of at least $2^{64}$ members with $\lvert I \cap I_2 \setminus I_1\rvert = c_2$. Since $I_2 \in \mathcal{L}_1$, the region $X_2 = [n] \setminus (I_1 \cup I_2)$ has $x_2$ points, and every member of $\mathcal{L}_2$ has exactly $z$ points in $I_1 \cup I_2$ and $y_2$ in $X_2$. Lemma 1, applied to the traces of $\mathcal{L}_2$ on $X_2$ with the pattern function "at least two members", gives $t - 2$ distinct leaves with at least $x_2B^{cc}_{t-2}(y_2/x_2) - \binom{t-2}{2}x_2/2^{64}$ points of $X_2$ in two of them.

Label as follows. A point of $I_1$ is $\mathsf{F}(1, U)$, a point of $I_2 \setminus I_1$ is $\mathsf{F}(2, U)$, with $U$ the members that use it. Member 2 uses its $c_1 \le h$ points of $I_1$. If $z \ge k$: leaf 3 uses $k$ of its $z$ points of $I_1 \cup I_2$, among them all those of $I_1 \cap I_2$ (there are at most $h < k$ of them), and the other $z - k$, which then lie in exactly one parent $p$, become $\mathsf{R}(p, 3, U)$: they are not used by member 2, so they can be roots of $f_p - f_3$. Each later leaf uses any $k$ of its $z$ points of $I_1 \cup I_2$; all are available to it, free or roots of an earlier pair. If $z < k$ every leaf uses its $z$ points and nothing is a root there. A point of $X_2$ in at least two leaves is $\mathsf{R}(j, j', \emptyset)$ for the two smallest. All units are at most $k$, so by Lemma M the event has probability at most $\frac{m^n}{(m)_n}q^{(t-1)k - \sum_j c_j(T)}(h/m)^{g(T)}$, with $\alpha\sum_jc_j(T) + \beta g(T) \ge \Psi_C(c_1, c_2) - \beta\binom{t-2}{2}n/2^{64} \ge \Psi_0 - \beta\binom{t-2}{2}n/2^{64}$ whatever $c_1, c_2$ the list produced. The union bound over all labelings in this alphabet with units at most $k$ and weight at least that is tilted as in Theorem B; $Z_C$ is the sum of $x^{\text{units}}y^{\text{roots}}$ over the labels: $\mathsf{F}(1, U)$, $\mathsf{F}(2, U)$, $\mathsf{R}(1, 3, U)$, $\mathsf{R}(2, 3, U)$, $\mathsf{R}(j, j', \emptyset)$. $\square$

How it works, at rate $1/2$, $\tau = 0.681$, $t = 4$: the centre and the second parent cost $(\rho - \tau^2)\log_2 q$ once instead of $t - 1$ times, because the leaves have $z \approx (\tau^2 + \tau^2(1-\tau))n > k$ points in the two parents and are pinned for nothing; the price is $k$ units a leaf in the tilt and a larger alphabet. The minimum over $(c_1, c_2)$ is the adversary: he may give more overlap than independent sets would, never less.

**Numbers. [checked]** (`scripts/42_multiparent.py`; the minimum over $(c_1, c_2)$ on a grid of $161 \times 243$ points with the two kinks added, re-evaluated on $641 \times 963$; the two grids differ by at most $10^{-5}$ bits a coordinate, against margins of at least $3 \cdot 10^{-3}$ at the printed $\tau$, which is rounded up to four decimals.) Level 0, $k = 2^{24} + 6$, list bound $2^{180}$, failure $2^{-100}$:

| rate | Theorem B, points in $K$ | **Theorem C, points in $K$** | Theorem B, points in $E$ | Theorem C, points in $E$ |
| --- | --- | --- | --- | --- |
| 1/2 | 0.6839, 198 | **0.6811, 195** ($t = 4$) | 0.6648, 184 | 0.6519, 175 ($t = 5$) |
| 1/4 | 0.4621, 97 | **0.4567, 96** ($t = 5$) | 0.4368, 91 | 0.4138, 85 ($t = 6$) |
| 1/8 | 0.3076, 64 | **0.3007, 63** ($t = 6$) | 0.2801, 59 | 0.2644, 57 ($t = 6$) |
| 1/16 | 0.2004, 47 | **0.1950, 46** ($t = 7$) | 0.1739, 43 | 0.1761, 44 ($t = 7$) |

The gain is larger with points in $E$ because there a unit is worth 128 bits against 104 for a root. A list bound of $2^{180}$ costs four DEEP points more than $2^{40}$ by the rule $2^{35(s-10)}$ of the brief, about 0.8% of proving time and 450 bytes a level, for three queries: this is a proof of concept for the use of the budget, not an engineering gain. Later levels were not computed.

### 5.4 What is still missing, precisely

On a regular list every leaf $j$ has a surplus $z_j - k$ of points and turns it into roots; Theorem C gives this to one leaf. For the others the points must be new: in the region covered once by the parents and not used by an earlier leaf. The number of new points is $\lvert I_j \cap E\rvert$ minus overlaps with earlier leaves inside $E$, and the proof needs an **upper** bound on those overlaps. Averaging gives lower bounds on overlaps. The only upper bound is the pairwise one: two members share at most $h$ points, while independent sets share $\tau^2n$, so the total excess overlap of two leaves is at most $(\rho - \tau^2)n$, but it can all sit in $E$. Carrying this through (regularize $\lvert I \cap I_1 \cap I_2\rvert$ by a pigeonhole, then one step that bounds the overlap with leaf 3 in $E$ from above by $h$ minus the Cauchy-Schwarz lower bounds in the other regions) gives leaf 4 about $(z - k) + y_2^2/x_2 - c_1/4$ new points, $0.04n$ at rate $1/2$ where the surplus is $0.10n$, at the cost of one leaf in the roots of $X_2$ (**[estimate]**; not carried out). Each further leaf needs a further step and gets less. I do not see how to reach the regular value this way: an adversary who correlates the leaves inside $E$ as much as the pairwise bound allows is not excluded by anything in the argument, and I could not exclude him by another count either.

The general object is a game: at each step the adversary chooses the distribution of the new overlap counts subject to their averages being at least the independent values and to the pairwise bound, and the prover picks a popular class. With one count per step the value is a one-dimensional minimum, which is Theorem C. With several counts per step the adversary can anti-correlate them, the value is the quasi-convex envelope of the continuation, and I did not solve it.

### 5.5 The lemma as stated is false: two densities

Note 36 asks for: every list of $2^b$ sets contains an ordered $t$-tuple whose count $\log_2 q\sum_j(k - c_j)_+ - \lambda g$ is at most its value for independent sets of density $\tau$. Take a list of independent random sets in which a fraction $w_1$ of the coordinates has density $d_1$ and the rest $d_2$, with mean $\tau$ and $w_1d_1^2 + w_2d_2^2 \le \rho$ (so that pairs share fewer than $k$ points). Every tuple has the same type up to fluctuations, so the count of every tuple is the value at this profile, and the profile enters through averages of non-convex functions of the density.

**[checked]** (`42_multiparent.py`, part 3; grid of 60 by 60 two-point profiles; points in $K$.) I first reproduce table T5 of note 36 with my own code: $0.6650, 0.4046, 0.2341, 0.1333$ (184, 83, 52, 38) with points in $K$ and $0.6183, 0.3487, 0.1900, 0.1013$ (156, 72, 46, 33) with points in $E$, as printed there. Then, at $\tau$ equal to the regular threshold plus $0.002$:

| rate | count | regular exponent, at $(t, r)$ | largest exponent over two-point profiles | worst profile |
| --- | --- | --- | --- | --- |
| 1/2 | note 36 | $-0.303$ at $(6, 3)$ | $-0.303$ | the regular one |
| 1/4 | note 36 | $-0.313$ at $(9, 3)$ | $-0.313$ | the regular one |
| 1/8 | note 36 | $-0.428$ at $(15, 5)$ | $-0.296$ | 13.4% of the coordinates at density 0.071, the rest at 0.262 |
| 1/16 | note 36 | $-0.672$ at $(24, 7)$ | $-0.654$ | 12.2% at 0.032, the rest at 0.150 |
| 1/2, 1/4, 1/8 | greedy reading of 5.1 | $-0.322$, $-0.433$, $-0.546$ | the same | the regular one |
| 1/16 | greedy reading | $-0.734$ at $t = 24$ | $-0.730$ | 34.6% at 0.044, the rest at 0.171 |

At rate $1/8$, $\tau = 0.2361$, $(t, r) = (15, 5)$ the count alone is $-11.868n$ bits for independent sets of density $\tau$ and $-11.486n$ for the two-density list: every tuple of that list is worse than the regular benchmark by $0.38n$ bits. So the lemma fails as stated, as a statement for all $n$ with $b = o(n)$. Two qualifications. (i) The damage is small: the smallest $\tau$ at which every two-point profile has a negative exponent is $0.2343$ against $0.2341$, and unchanged to four decimals in the other rows. The right benchmark is the worst product profile, and at rates $1/2$ and $1/4$ that is the regular one, among two-point profiles on this grid. (ii) At our sizes the fluctuations are not negligible against $0.38n$: the best of $2^b$ candidates gains about $\sqrt{2b\ln 2\cdot n\,v}$ points on a count of variance $v$ a coordinate, which at $n = 2^{27}$, $v = 0.1$ is $0.016n$ bits per member for $b = 64$ and $0.065n$ for $b = 1000$ (**[estimate]**); with 4 to 14 members that matter this is below the defect for $b = 64$ and comparable to it for $b = 1000$. So for a small budget the two-density list defeats the lemma at actual sizes, and for $b = 1000$ the question is quantitative and not decided by this example.

The same table says where the heuristic stands: with the better reading of 5.1 the regular thresholds would be $0.6416, 0.3827, 0.2210, 0.1250$, that is **169, 78, 50, 36 queries** with points in $K$ (149, 70, 45, 33 with points in $E$). **[heuristic]**: regular lists only, with the entropy of the regular pattern distribution as the pattern count, as in note 36. A theorem would have to pay for every type the selection can be forced into, not for the regular one.

### 5.6 A second use of the budget (not proved)

Section 5.3 of note 36 argues that a list of $2^b$ members can return at most $tb$ bits by a Markov argument on the number of bad patterns, hence nothing at level 0. That accounting is right for that argument. But the list is used through Lemma 1, which takes an average tuple, and a list of $2^b$ random-like sets contains tuples that are better than average by $\Theta(\sqrt{bn})$ in every count, which is worth $\log_2 q\cdot\Theta(\sqrt{bn})$ bits and not $O(tb)$. For the star of Theorem B at level 0, rate $1/2$, $b = 1000$ this is about $0.7$ bit a coordinate, about $0.003$ in $\tau$ (**[estimate]**: $\sqrt{2 \cdot 3b\ln 2 \cdot n}$ points of $W_\mathsf{D}$ at 64 bits each, against a slope of 260 bits per unit of $\tau$), the same order as Theorem C. Whether every list, and not only a random one, contains such a tuple is a question about codes near the Plotkin point: a constant-weight code with $2^b$ words must contain two words closer than average by about $\sqrt{bn}$ up to logarithms, by the linear programming bound (**[conjectured]** here: I did not check the constant-weight statement in the literature and did not prove the extension to stars). I flag it because it is the natural way to spend $b = 1000$ where exact regularity (5.2) spends $56$ bits a step.

### 5.7 Status

| item | status |
| --- | --- |
| Lemma 6.1 of note 36 | correct **[proved]** |
| Lemma M (general count), best reading | **[proved]**, **[checked]** at three and four members |
| Lemma R (the budget buys exact regularity, 56 bits a step) | **[proved]** |
| Theorem C (two parents): 195, 96, 63, 46 queries at level 0, points in $K$, list $2^{180}$ | **[proved]**, numbers **[checked]** |
| table T5 of note 36 (184, 83, 52, 38) | reproduced, **[heuristic]** |
| greedy reading on regular lists (169, 78, 50, 36) | **[heuristic]** |
| "as good as independent sets of the same density" | false as stated (two densities, rates $1/8$ and $1/16$); harmless in size |
| "as good as the worst product profile" | open; the obstruction is 5.4 |
| budget through large deviations, $\sqrt{bn}$ | **[conjectured]** |

## 6. Independence, fast encoders, cost

**What Theorem B uses.** For each labeling $T$ in the class, the count of Lemma B1 needs: the points of the $\mathsf{D}$ coordinates arbitrary, and then each $\mathsf{C}$ point confined to at most $h$ values out of about $m$ given all the points chosen before it. In probabilistic terms: every $\mathsf{C}$ point has conditional min-entropy about $\log_2 m$ given the $\mathsf{D}$ points and the other $\mathsf{C}$ points, for every $T$. At level 0, rate $1/2$ a typical $T$ has $0.66n$ points of the first kind and $0.24n$ of the second, and the class contains labelings with all $n$ coordinates labeled. So:

- $t$-wise independence ($t = 4$ to $12$) gives nothing: the event $E_T$ couples a constant fraction of the coordinates.
- Independence between blocks with dependence inside is exactly Theorem B$_w$: a block contributes one factor $hw/m$ however many of its points are shared, and note 36 is right that the worst case is real (agreement sets that are unions of blocks, $g_j - g_{j'}$ a polynomial in $L_U$). I see no way around it inside a first moment: the points of a block are affine images of one random variable.
- Full independence of the labeled points is what is used; it could be relaxed to "almost uniform given the others" with a loss equal to the entropy deficiency, nothing more.

**Is there an evaluation set with a fast encoder that satisfies this?** Not that I can find, and Proposition 7.1 of note 36 explains why it is unlikely: a first moment over $2^{2.9n}$ nonempty pattern events needs $2.9n$ bits of entropy in the set, that is at least $n/22$ independent field elements at level 0. Every set with a quasi-linear encoder that I know of is a union of cosets of a large subspace or the image of a subspace under a fixed map, with at most $64 \cdot 2^R$ or $64N$ random bits. A union of $n/w$ cosets with $w \le 22$ has the entropy, but then Theorem B$_w$ applies and gives nothing at level 0 for any $w \ge 2$ (table T6 of note 36, not recomputed), and its encoder is a multipoint evaluation of length $n/w$ repeated $w$ times, no cheaper in order of magnitude. Theorem C does not change this: it uses the points in the same way.

**The cost estimate of note 36, section 8** (plausibility only). The count is internally consistent: a remainder tree over $k$ points with precomputed subproduct transforms costs $2(j+2)$ multiplications a point at the level of nodes of $2^{j+1}$ points, hence $\kappa^2 + 3\kappa$ a point against $\kappa/2$ for the additive NTT, a factor $2\kappa + 6 = 54$ at $\kappa = 24$, doubled if the middle product needs transforms of double size. Multipoint evaluation at arbitrary points is $\Theta(\log n)$ times a multiplication of size $n$ in every algorithm I know, so the factor $\Theta(\kappa)$ over the NTT is structural and the constant 2 to 4 is the optimistic end: it assumes a middle product in the additive-FFT basis that the note says it did not design, and it ignores the memory traffic of a 6 GiB tree read once per lane in a prover that is bandwidth-bound. I would read "53 to 106" as "at least 50, probably more than 100 in time". The conclusion of note 36 (the level-0 gain of 9% of the queries does not pay for it; only the last two levels have a defensible cost) stands, and the two corrections of section 2 (97 at rate $1/4$, 12 at level 4) do not change it.

## 7. Errors and gaps found in note 36

1. Section 0, verdict 3, and section 5.3: "at level 0 the budget cannot buy more inside these proofs", "[proved] as an accounting". False as a statement about first-moment proofs with a star or multi-parent count: Theorem C uses $2^{180}$ to move $\tau$ by $0.003$ to $0.007$ at level 0. The Markov accounting itself is right.
2. Section 6: the missing lemma is stated with the wrong benchmark (independent sets of the same density). It fails for lists with two coordinate densities at rates $1/8$ and $1/16$; the correction costs $0.0002$ in $\tau$.
3. Table T5 is optimistic for a second reason, stated in the note only implicitly: it counts the patterns of the regular type, where a theorem must count every type it can be forced into. And it is pessimistic for another: the greedy reading of the same count gives 169 where T5 gives 184.
4. Table of section 0 and T1: 98 queries at rate $1/4$ should be 97; T2: 13 queries at level 4 with points in $K$ should be 12. All printed $\tau$ are valid upper bounds, loose by up to $0.0006$ at level 0 and 13% at levels 4 and 5.
5. Section 5.1, "lowered by the largest second difference over 8, which bounds the error of the grid": not a bound for $t \ge 100$, where $\psi''$ varies by a factor two inside a cell of the grid. No printed value is affected.
6. Section 7, "$\nu$-wise independent points with $\nu \approx 0.90n$": the class of the union bound contains labelings with up to $n$ labeled coordinates.
7. Section 2, the hypotheses of [FKS] Theorem 3: two omitted conditions (section 4 here), immaterial.
8. Proposition 7.2: the appeal to [AGGLZ] Lemma 2.4 is unnecessary (section 3.4 here).
9. Theorem A: not verified. The sentence "Their Lemmas 3.2 to 3.8 hold verbatim" carries the proof.
10. Section 4.1, the toy check: as the note says itself, no power. Section 3 here replaces it.

None of these touches the statement or the proof of Theorem B.

## 8. Reproduction

All in `scripts/`, standard library Python 3 and a C compiler; `42_results.txt` holds the outputs.

- `42_theoremB.py [quick|level0|later [i ...]|listsize]`: section 2. Level 0 and all sizes about 5 minutes, the later levels about 25 minutes on one core.
- `42_toy.c` (build with `cc -O2`), run as `42_toy p n k [lists]`, output read by `42_toy_check.py`: section 3.3. Under a minute for the five runs.
- `42_lateral.c`, run as `42_lateral p samples seed`: section 3.2. About 1 ms a sample.
- `42_coset_rank.py`: section 3.4, 2 seconds.
- `42_lemmas_check.py`: Lemma 1 and Lemma R on explicit families, 15 seconds.
- `42_lemmaM_t4.py`: Lemma M with four members, exact, one minute.
- `42_multiparent.py [quick]`: Theorem C, the heuristics and the two-point profiles, about 8 minutes.
- `42_run.sh`: builds the C programs in a temporary directory and runs everything on four cores.

## References

- [AGGLZ] O. Alrabiah, Z. Guo, V. Guruswami, R. Li, Z. Zhang. Random Reed-Solomon codes achieve list-decoding capacity with linear-sized alphabets. arXiv 2304.09445. Not reread here.
- [FKS] A. Ferber, M. Kwan, L. Sauermann. List-decodability with large radius for Reed-Solomon codes. arXiv 2012.10584v2. Read completely.
