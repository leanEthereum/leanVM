# 36. Evaluation sets with a proven list bound: random points, explicit constants, cost

Researcher 36 (round 5). The question of the brief: in the DEEP-fold framework only a list bound is needed, the list budget is huge and the evaluation set is free, so is there an evaluation set for which a list bound below the Johnson radius is already a theorem, at our sizes and at failure probability $2^{-100}$?

Notation. $F$ is a finite field with $q$ elements, $S \subseteq F$ a sampling set with $m$ elements, $a = (a_1, \dots, a_n)$ a uniformly random $n$-tuple of distinct elements of $S$ ($n \le m/2$). The code is $\{(f(a_i))_i : f \in F[X], \deg f < k\}$; throughout $k$ stands for the analysis dimension $2^\kappa + \ell$ (degree at most $2^\kappa - 1 + \ell$), $\rho = k/n$, $h = k - 1$, $\lambda = \log_2(m/h)$. $\mathrm{Bad}(A, M)$ is the event that some word $y \in F^n$ has at least $M$ polynomials of degree $< k$ agreeing with it on at least $A$ coordinates. $\tau = A/n$. $B_T(d) = \Pr[\mathrm{Bin}(T, d) \ge 2] = 1 - (1-d)^T - Td(1-d)^{T-1}$. Queries are $\lceil 108/\log_2(1/\tau)\rceil$ as in the brief. Statuses: **[lit]** read in the cited paper (section 1 says how much), **[proved]** proof in this note, **[checked]** numerically (sizes given), **[estimate]**, **[heuristic]** (no proof, stated as such).

## 0. Verdict

1. **Yes: there is an evaluation set with a proven list bound below Johnson, with points in $K$, at every rate and every level.** For $n$ uniformly random distinct points of $K$, with probability at least $1 - 2^{-100}$ over the points, no word has $2^{64}$ polynomials of the analysis degree at agreement $\tau n$, for the $\tau$ of the table below (Theorem B, **[proved]**, section 4; numbers **[checked]** by `scripts/36_bounds.py`). This is H_K$(\tau, 64)$ of the brief for that random $D$, for interleaved words over $E$ as well (Corollary 4.3). It is the first instance of H_K below Johnson for all words on any domain in this project. It is an existence statement over the choice of the set: nothing certifies a given set.
2. **The proof that works is not the one the brief pointed at.** The generic-points line (Brakensiek, Gopi, Makam; Guo, Zhang; Alrabiah, Guo, Guruswami, Li, Zhang) gives nothing with points in $K$, even with every constant redone (Theorem A, section 3): the exponent at the Johnson agreement is $+0.29n$ to $+0.35n$ bits where a negative value is needed, and the sampling set would have to have $2^{69}$ to $2^{77}$ elements. It does win for points in $E$ at rates 1/2 and 1/4. What works with points in $K$ is the counting argument of Ferber, Kwan and Sauermann, sharpened in three ways (linearity removes the count of word values, a star of $t$ members, tilted union bound), Theorem B. Its printed form is vacuous for us (it needs $\log_2 q \ge 81000$ to beat Johnson, section 2).
3. **The large list budget is used, and at level 0 it cannot buy more inside these proofs.** Both theorems pick $t \le 1024$ members out of a list of $2^{64}$ by averaging (Lemma 1), which is what turns the generalized Singleton radius into a radius that reaches Johnson at $t = 2$. Beyond that the budget is useless at levels 0 to 2: a first moment over the agreement patterns of $t$ members costs between $0.3n$ and $5.6n$ bits, a list of $2^b$ members could return at most $tb$ bits by Markov, and $tb \ll n$ (section 5.3). Only at the last levels, where $n \le 2^{22}$ and $t$ is in the hundreds, is $tb$ comparable to the pattern term; I did not exploit this.
4. **Cost kills it where it matters.** Both proofs need the points to be independent, coordinate by coordinate (section 7): at level 0 the union bound runs over about $2^{3n}$ patterns, so the evaluation set must carry about $3n$ bits of entropy that the proof can use, at most $\lambda \le 64$ per independent point. Every cheap structured set fails: unions of cosets of size $w$ with random representatives divide the gain by $w$ and are proven only for $w \le 16$ at the last levels and for no $w \ge 2$ at level 0 (Theorem B$_w$, table T6); a random subset of a subspace $2^c$ times larger needs $c \ge 8$ to 16 (T7); and the generic-rank theorem behind Theorem A is false on every coset union (Proposition 7.2). Independent points mean a multipoint-evaluation encoder: 53 to 106 times the multiplications of today's level-0 NTT (**[estimate]**, section 8), for 9% fewer level-0 queries. At the last two levels the encoder costs about one level-0 NTT in total and saves 8 queries, under 2% of the proof.
5. **What a stronger proof of the same kind would give** (**[heuristic]**, section 6): a multi-parent version of Theorem B, valid on lists whose members overlap like independent sets, would give 184, 83, 52, 38 queries at level 0 with points in $K$. The count is proved (Lemma 6.1); what is missing is a lemma that every large list contains a tuple as good as a regular one, and this is exactly where a budget of $2^{1000}$ could be spent (pigeonhole on intersection profiles).

**Table of step 2** (level 0 of the $\mu = 30$ profile, $k = 2^{24} + 6$, failure probability $2^{-100}$, list size $2^{64}$; each cell is the smallest proven $\tau$ and its query count; "none" means nothing below Johnson). **[proved]** (Theorems A, B, B'), numbers **[checked]**.

| rate | Johnson | points in $K$, $m = 2^{64}$: Theorem A | points in $K$: Theorem B | points in $E$, code over $E$: best of A, B | points in $E \setminus K$, lanes over $K$ (Johnson is $\sqrt{\rho/2}$): Theorem B' |
| --- | --- | --- | --- | --- | --- |
| 1/2 | 0.7071, 217 | none (0.7150; exponent $+0.317n$ at Johnson; needs $m \ge 2^{69}$) | **0.6844, 198** ($t = 4$) | 0.6388, 168 (A, $t = 6$) | 0.4368, 91 (Johnson 0.5, 109) |
| 1/4 | 0.5000, 109 | none (0.5118; $+0.348n$; $m \ge 2^{70}$) | **0.4622, 98** ($t = 5$) | 0.4224, 87 (A, $t = 7$) | 0.2803, 59 (0.3536, 73) |
| 1/8 | 0.3536, 73 | none (0.3700; $+0.343n$; $m \ge 2^{73}$) | **0.3079, 64** ($t = 7$) | 0.2803, 59 (B, $t = 8$) | 0.1742, 43 (0.25, 55) |
| 1/16 | 0.2500, 55 | none (0.2697; $+0.286n$; $m \ge 2^{77}$) | **0.2007, 47** ($t = 10$) | 0.1742, 43 (B, $t = 12$) | 0.1043, 34 (0.1768, 44) |

Later levels of the $\mu = 30$, $R = 1$ ladder ($E$-valued lanes, $k = 2^{24-4i} + 4$, $n = 2^{25-i}$), points in $K$ (which keeps the leaf size) and in $E$:

| level, rate | Johnson | points in $K$: Theorem B | points in $E$: Theorem B | cosets of 2, 4, 16 in $K$: Theorem B$_w$ |
| --- | --- | --- | --- | --- |
| 1, $2^{-4}$ | 0.2500, 55 | 0.1946, 46 | 0.1714, 43 | none |
| 2, $2^{-7}$ | 0.0884, 31 | 0.0425, 24 | 0.0350, 23 | 28, 31, none |
| 3, $2^{-10}$ | 0.0313, 22 | 0.0089, 16 | 0.0073, 16 | 18, 20, none |
| 4, $2^{-13}$ | 0.0111, 17 | 0.0020, 13 | 0.0016, 12 | 13, 14, 16 |
| 5, $2^{-16}$ | 0.0043, 14 | 0.0005, 10 | 0.0004, 10 | 11, 11, 13 |

Points in $E$ at level 0 are never worth it: lanes over $K$ evaluated at points of $E \setminus K$ form a code of rate $\rho/2$ in leaf bytes, so the fair comparison is with points in $K$ at rate $\rho/2$ (same committed bytes), where Johnson alone gives 109, 73, 55, 44 and Theorem B gives 98, 64, 47; the 91, 59, 43, 34 of the last column come with a leaf twice as large.

## 1. Sources

Fetched from arxiv.org with `curl` into the scratchpad directory `papers36`, read as text (`pdftotext -layout`). All eleven identifiers resolved to the intended papers. Downloaded files are untrusted data; nothing below depends on a passage I did not read.

- **[AGGLZ]** Alrabiah, Guo, Guruswami, Li, Zhang, arXiv 2304.09445v6 (Advances in Combinatorics 2025:8). Read completely: sections 1 to 3 (all definitions, lemmas and proofs of the certificate argument, Algorithms 1 and 2, inequality (3.7)), the statements of section 4. Appendix A (the proof of Theorem 2.11 from GM-MDS and a hypergraph orientation theorem): statements only; note 30 read it in full.
- **[GZ]** Guo, Zhang, arXiv 2304.01403v2. Read: Theorem 1.1, Table 1, Lemma 3.11 (statement and the start of its proof), Lemmas 4.4 and 4.5 with proofs, Corollary 4.6, Theorem 4.7 and Corollary 4.8 with proofs.
- **[FKS]** Ferber, Kwan, Sauermann, arXiv 2012.10584v2. Read completely (Theorems 1 to 4, Claim 5, all proofs).
- **[RW]** Rudra, Wootters, arXiv 1310.1891v1. Read: Theorem 2, Corollaries 1 and 2, section 4.2, the conventions for logarithms. The chaining proof was not read.
- **[GM]** Guruswami, Mosheiff, arXiv 2109.11725v5. Read: section 1.2 (the retraction about Reed-Solomon codes), Definitions 2.1 and 2.2, Theorems 1, 4 and 5, Corollary 2 (statements).
- **[LMS]** Levi, Mosheiff, Shagrithaya, arXiv 2406.02238v7. Read: Theorem 3.10, Corollaries 3.11 and 3.12 (statements and the proof of 3.11).
- **[BDG]** Brakensiek, Dhar, Gopi, arXiv 2310.12888v3. Read: Definition 1.3, Theorems 1.4 to 1.6 (informal statements), Example 1.1 and the remarks on field size.
- **[BDGZ]** Brakensiek, Dhar, Gopi, Zhang, arXiv 2310.12898. Read: abstract and Theorem 1.3 (informal).
- **[PP]** Putterman, Pyne, arXiv 2303.17554v2. Read: Theorems 1.2, 1.3, 1.5 (statements). Binary codes and zero-error list recovery; not applicable.
- **[GLSTW]** Guo, Li, Shangguan, Tamo, Wootters, arXiv 2011.04453v2: abstract only (exponentially large fields; superseded by [FKS] and [AGGLZ]).
- **[BGM]** Brakensiek, Gopi, Makam, arXiv 2206.05256v4: downloaded, not reread; I use it only through [AGGLZ] Theorem 2.11. Note 30 lists what it read there.

Not obtained and not used: Shangguan and Tamo; Goldberg, Shangguan and Tamo; anything later than these.

## 2. The printed theorems at our sizes

**[lit]** statements, **[checked]** evaluation (`scripts/36_literature.py`; $k = 2^{24}$, $n = k/\rho$, field of $2^{64}$ or $2^{128}$ elements). Entries are the smallest agreement $\tau = 1 - \text{radius}$ the statement gives.

| statement | requirement, as printed | which step of the proof produces it | rate 1/2, $2^{64}$ | rate 1/2, $2^{128}$ | rates 1/4, 1/8, 1/16 at $2^{128}$ |
| --- | --- | --- | --- | --- | --- |
| [AGGLZ] Thm 1.1: radius $\frac{L}{L+1}(1-\rho-\varepsilon)$, list $L \ge 2$, failure $2^{-Ln}$ | $q \ge n + k\,2^{10L/\varepsilon}$ | a rounding of inequality (3.7) | none | 0.795 | 0.628, 0.545, 0.503 |
| [AGGLZ] inequality (3.7) itself at $2^{-100}$ | $2^{(L+2)n}\binom nr 2^{(L+1)r}\bigl(\frac{Lk}{q-n}\bigr)^r \le 2^{-100}$, $r = \lfloor \varepsilon n/2\rfloor$ | $2^{(L+2)n}$ agreement hypergraphs; $\binom nr 2^{(L+1)r}$ certificates; half of the deletion budget $\varepsilon n$ is the bank, half the faults; a fault has probability $(t-1)k/(q-n)$ | 0.835 | 0.7047 | 0.504, 0.400, 0.348 |
| [GZ] Thm 4.7, failure $2^{-(c-2)n}$ | $q \ge 2^{L(L+c)/\varepsilon}Ln(k-1) + n$, $c > 2$ | only $\varepsilon n/(t-1)$ faults (the deletion lemma 3.11 is by weight), $n^r$ certificates | 0.850 | 0.735 | 0.569, 0.487, 0.446 |
| [LMS] Cor 3.12, failure $2^{-\eta n}$ | $q \ge 2^{2(L+1)(L+1+\eta)/\varepsilon}\,k\,(4(L+1))^{4(L+1)}/\varepsilon$ | $\varepsilon n/(2b)$ faults, $b = L+1$, and $(4b)^{4b}$ | none | 0.802 | 0.677, 0.615, 0.578 |
| [FKS] Thm 3 ($h = k-1$): agreement $3ch/n$, list $\lfloor n/(ch)\rfloor$, failure $q^{-h/4}$ | $c \ge 5$, $h \le q^{-1/c}m$, $3ch < n \le \sqrt{\log_2 q \cdot c/8}\,h$ | $(mq)^{z}$ choices for the points and the word values on a determining set of $z$ coordinates; $2^{n(L+1)}$ set systems against $q^{-h/2}$ | none | none | none |
| [RW] Cor 2: agreement $5\varepsilon$, list $1/\varepsilon$, constant probability | $n \ge 2C_0\log_2(q^k)\log_2^5(1/\varepsilon)/\varepsilon$, $C_0$ unspecified | chaining | none | none | none |
| [GM] Thms 1, 4, 5 | $n/\log n \ge \omega(q^{2b})$ (Thms 1, 4) or $\omega(q^{L+1})$ (Thm 5), bias or distance defect at most about $q^{-b}$, $b = L+1$ | written for constant $q$ | none | none | none |

Johnson is 0.7071, 0.5, 0.3536, 0.25. So with printed constants nothing is below Johnson, with one exception by a hair: [AGGLZ]'s own inequality (3.7), points in $E$, rate 1/2, 0.7047. Note 06 evaluated only the first line. Three exact reasons for the vacuous rows. [FKS]: $3c\rho < \sqrt\rho$ and $1/\rho \le \sqrt{\log_2 q\cdot c/8}$ with $c \ge 5$ force $\log_2 q \ge 648c^3 \ge 81000$ (**[proved]**, two lines). [RW]: $5\varepsilon < \sqrt\rho$ with $\rho \le \varepsilon/(2C_0\log_2 q\log_2^5(1/\varepsilon))$ forces $\varepsilon \le 2^{-37.9}$ and $\rho \le 2^{-71}$ at $C_0 = 1$, the most favourable reading; the probability is a constant, not $2^{-100}$. [GM]: with $q = 2^{64}$ and $L \ge 1$ the hypotheses need $n \gg 2^{128}$ (Theorem 5) or $n \gg 2^{256}$ (Theorems 1 and 4), and the paper itself withdraws the application to Reed-Solomon codes (its section 1.2: the distance requirement is "impossible to achieve whenever $q$ is larger than $n$").

[BDG] and [BGM] are statements about algebraically independent points (one independent generic point per coordinate), with no field-size bound of use here; they enter through [AGGLZ] Theorem 2.11. [BDGZ] is the same trade-off for algebraic-geometry codes, field size $\exp(O(L/\varepsilon))$: a different code, not foldable, no better exponent.

## 3. Theorem A: rank certificates with every constant redone

### 3.1 Two lemmas

**Lemma 1 (averaging). [proved]** Let $I_1, \dots, I_M \subseteq [n]$ have size $A$ each, $d_i = |\{j : i \in I_j\}|/M$, and let $\varphi$ assign a real number in $[0, \varphi_{\max}]$ to each membership pattern in $\{0,1\}^t$. For an ordered $t$-tuple $J$ of distinct indices let $\Phi(J) = \sum_i \varphi(\text{pattern of } i \text{ in } (I_j)_{j \in J})$. Put $\bar\varphi(d) = \mathbb{E}\,\varphi$ under $t$ independent Bernoulli$(d)$ bits, and let $\bar\varphi^{cc}$ be the largest convex function below $\bar\varphi$ on $[0,1]$. Then some $J$ has
$$\Phi(J) \ \ge\ n\,\bar\varphi^{cc}(A/n) - \binom t2\frac{n\,\varphi_{\max}}{M}.$$

*Proof.* Draw $j_1, \dots, j_t$ independently and uniformly from $[M]$. The bits of coordinate $i$ are independent Bernoulli$(d_i)$, so $\mathbb{E}\Phi = \sum_i\bar\varphi(d_i) \ge \sum_i\bar\varphi^{cc}(d_i) \ge n\bar\varphi^{cc}(A/n)$ by Jensen, since $\sum_i d_i = A$. A repetition has probability at most $\binom t2/M$, and conditioned on no repetition the tuple is uniform over tuples of distinct indices, so that conditional expectation is at least $\mathbb{E}\Phi - \binom t2 n\varphi_{\max}/M$. $\square$

This is the only place where a large list is used. With $\varphi = (|e| - 1)_+$ (the weight of a hyperedge) $\bar\varphi(d) = td - 1 + (1-d)^t$ is convex, so $t$ of the members have agreement hypergraph of weight at least $n(t\tau - 1 + (1-\tau)^t) - 1$ once $M \ge t^3n$, against $n(t\tau - 1)$ for an arbitrary $t$-subset. At $t = 2$ the weight is $\tau^2n$: two members agreeing on more than $k$ points, the Johnson bound. As $t \to \infty$ it is the capacity condition. The generalized Singleton bound for lists of size $t - 1$ is the case without the term $(1-\tau)^t$.

**Lemma 2 (exact weight). [proved]** Let $H$ be a hypergraph on $t \ge 2$ vertices with $\sum_e \mathrm{wt}(e) \ge (t-1)\kappa$. Then there are $s \ge 2$ vertices $V^\ast$ and a hypergraph $H^\ast$ on $V^\ast$ with $e^\ast_i \subseteq e_i \cap V^\ast$ for every $i$, no edge of size one, total weight exactly $(s-1)\kappa$, that is $\kappa$-weakly-partition-connected.

*Proof.* Induction on $t$. Remove vertices from edges one at a time (each removal lowers the weight by one) until the weight is exactly $(t-1)\kappa$, and empty the edges of size one. Let $V'$ be inclusion-minimal with $|V'| \ge 2$ and $\sum_e\mathrm{wt}(e \cap V') \ge (|V'|-1)\kappa$. If $V' = V$ the hypergraph is $\kappa$-weakly-partition-connected by the computation (2.3) of [AGGLZ] (which uses only minimality). Otherwise apply the induction hypothesis to the induced hypergraph on $V'$. $\square$

### 3.2 Statement

**Theorem A. [proved]** (after [AGGLZ] Lemma 3.1 and Theorem 1.1). Let $t \ge 3$, $M \ge t^3n$, $W^\ast = \lceil n(t\tau - 1 + (1-\tau)^t)\rceil - 1$ with $\tau = A/n$, $\kappa = \lfloor W^\ast/(t-1)\rfloor$ and $D = \kappa - k \ge 1$. For each $s \in \{3, \dots, t\}$ let $T_s = 2^s - s - 1$ and choose integers $b_s \ge 0$, $r_s \ge 1$ with $T_sb_s + r_s - 1 \le D$, and put $\mu_s = \lceil r_s/(b_s+1)\rceil$. Then
$$\Pr[\mathrm{Bad}(A, M)] \ \le\ \sum_{s=3}^{t} N_s\,\frac{\mu_s^{r_s}}{r_s!}\Bigl(\frac{(s-1)\kappa\,(k-1)}{m-n+1}\Bigr)^{r_s}, \qquad N_s \le \min_{x > 0}\ Z_s(x)^n\,x^{-(s-1)\kappa}, \quad Z_s(x) = 1 + \sum_{j=2}^{s}\binom sj x^{j-1}.$$

*Proof.* Take $M$ members of a list and subsets $I_j$ of size $A$ of their agreement sets. By Lemma 1 some $t$ of them have weight at least $W^\ast \ge (t-1)\kappa$, and by Lemma 2 there are $s$ of them and a subhypergraph $H^\ast$ of their agreement hypergraph, $\kappa$-weakly-partition-connected, of weight exactly $(s-1)\kappa$. Its rows are true equations between distinct polynomials, so $\mathrm{RIM}_{H^\ast}(a)$ has a nonzero kernel vector ([AGGLZ] Lemma 2.8). For $s = 2$ this is impossible: the matrix is a Vandermonde matrix with $\kappa \ge k$ rows at distinct points. So $\mathrm{Bad}$ implies that for some $s \ge 3$ and some $H$ in the family $\mathcal{F}_s$ of such hypergraphs on $[s]$ the matrix $\mathrm{RIM}_H(a)$ is not of full column rank.

*One hypergraph.* $H \in \mathcal{F}_s$ is $(k + D)$-weakly-partition-connected, so deleting any $D$ edges leaves a $k$-weakly-partition-connected hypergraph ([AGGLZ] Lemma 2.14) whose matrix has full column rank over $F(X_1, \dots, X_n)$ ([AGGLZ] Theorem 2.11, **[lit]**). Run Algorithms 1 and 2 of [AGGLZ] with two changes: the bank holds the $b_s$ largest unused indices of each of the $T_s$ types of size at least two (types of size at most one have no rows), and the certificate has $r_s$ entries. Their Lemmas 3.2 to 3.8 hold verbatim because $|B \cup \{i_1, \dots, i_{\ell-1}\}| \le T_sb_s + r_s - 1 \le D$. In their Lemma 3.9 two refresh indices differ by at least $b_s + 1$ (same proof), so a certificate is a sequence of $r_s$ distinct indices made of at most $\mu_s$ increasing runs: at most $\mu_s^{r_s}$ orderings of a given set. In their Lemma 3.11 the determinant of $M_j$ has degree at most $(|e_i| - 1)(k-1)$ in $X_i$ (it has at most $|e_i| - 1$ rows containing $X_i$, each of degree $k - 1$), so a certificate with index set $G$ has probability at most $\prod_{i \in G}p_i$, $p_i = (|e_i|-1)(k-1)/(m-n+1)$. Summing, the failure probability for $H$ is at most $\mu_s^{r_s}e_{r_s}(p) \le \mu_s^{r_s}(\sum_ip_i)^{r_s}/r_s!$, and $\sum_i p_i = \mathrm{wt}(H)(k-1)/(m-n+1)$ with $\mathrm{wt}(H) = (s-1)\kappa$. With $b_s = 0$ every index is a refresh index and this is the count of [GZ].

*The number of hypergraphs.* An element of $\mathcal{F}_s$ is a sequence of $n$ edges, each empty or one of the subsets of $[s]$ of size $j \ge 2$ (weight $j - 1$), of total weight $(s-1)\kappa$. For every $x > 0$ their number is at most $Z_s(x)^n x^{-(s-1)\kappa}$. $\square$

What changed against [AGGLZ], and what each change is worth at level 0, rate 1/2, points in $E$: Lemma 1 (the term $(1-\tau)^t$); faults $r \approx 0.98D$ instead of $D/2$ (a bank of 2% of the budget suffices because a run costs only $\log_2\mu_s \approx 11$ bits a fault against $\lambda = 104$); $\sum_ip_i$ in place of $n\max_i p_i$ (a factor $(\rho + \varepsilon)^{r}$); the count $N_s$ in place of $2^{sn}$ (5.63 bits a coordinate instead of 6 at $s = 6$). Together 0.7047 becomes 0.6388. The structural loss that remains: a fault kills up to $s - 1$ rows for one factor $k/m$, so the exponent is $\varepsilon n\lambda$ against $sn$ bits of patterns and $\tau - \rho \gtrsim 2\sqrt{(1-\rho)/\lambda}$. That is why $\lambda = 40$ (points in $K$) is not enough and $\lambda = 104$ is.

## 4. Theorem B: star counting

### 4.1 The count

Fix $I_1, \dots, I_t \subseteq [n]$. For $i \in [n]$ let $S_i = \{j \ge 2 : i \in I_j\}$. A **labeling** $T$ gives each coordinate one of: nothing; $\mathsf{D}_S$ for a nonempty $S \subseteq \{2, \dots, t\}$; $\mathsf{C}_{jj'}$ for $2 \le j < j' \le t$. The canonical labeling of $(I_j)$ is $\mathsf{D}_{S_i}$ if $i \in I_1$ and $S_i \ne \emptyset$, $\mathsf{C}_{jj'}$ with $j < j'$ the two smallest elements of $S_i$ if $i \notin I_1$ and $|S_i| \ge 2$, nothing otherwise. $W_\mathsf{D}(T) = \sum_{i : \mathsf{D}_S}|S|$ and $g(T)$ is the number of $\mathsf{C}$ labels. $E_T$ is the event that there are pairwise distinct $f_1, \dots, f_t$ of degree $< k$ with $f_j(a_i) = f_1(a_i)$ for $i$ labeled $\mathsf{D}_S$, $j \in S$, and $f_j(a_i) = f_{j'}(a_i)$ for $i$ labeled $\mathsf{C}_{jj'}$.

**Lemma B1. [proved]** $\Pr[E_T] \le e^{n^2/(m-n)}\,q^{(t-1)k - W_\mathsf{D}(T)}\,(h/m)^{g(T)}$.

*Proof.* The event is invariant under subtracting $f_1$ from all members, so count pairs $(a, (g_j)_{j \ge 2})$ with $g_j = f_j - f_1$ nonzero and pairwise distinct. Choose $a_i$ for the $\mathsf{D}$ coordinates: at most $m$ ways each. Then $g_j$ is a nonzero polynomial of degree $< k$ vanishing at the $c_j$ distinct points $a_i$ with $j \in S$: none if $c_j \ge k$, at most $q^{k - c_j}$ otherwise, and $\sum_jc_j = W_\mathsf{D}(T)$. Now every member is determined, and for a coordinate labeled $\mathsf{C}_{jj'}$ the point $a_i$ is a root of the nonzero polynomial $g_j - g_{j'}$: at most $h$ ways. The other coordinates have at most $m$ ways. The number of tuples of distinct points is at least $m^n(1 - n/m)^n \ge m^ne^{-n^2/(m-n)}$. $\square$

[FKS] count $m^{|Z|}q^{|Z|}$ for the points and the word values on a set $Z$ that determines every member. Linearity removes the word: the values on the $\mathsf{D}$ coordinates are those of $f_1 = 0$.

**[checked]** `scripts/36_star_check.py`: exhaustive count of the bad tuples against the bound for 115 random set systems over $\mathbb{F}_5$ and $\mathbb{F}_7$ ($k \in \{2, 3\}$, $n \in \{4, 5\}$, $t \in \{3, 4\}$), no violation. At these sizes the bound is rarely below the trivial one except where it is zero, so this checks the direction of the statement and not its tightness.

### 4.2 Statement

**Theorem B. [proved]** Let $t \ge 2$, $M \ge t$, $s_\mathsf{D}, s_\mathsf{C} \in (0, 1)$, $\alpha = (1 - s_\mathsf{D})\log_2 q$, $\beta = (1 - s_\mathsf{C})\lambda$, and
$$\psi(d) = \alpha(t-1)d^2 + \beta(1-d)B_{t-1}(d),$$
with convex envelope $\psi^{cc}$ on $[0,1]$. Then, with $\tau = A/n$,
$$\log_2\Pr[\mathrm{Bad}(A, M)] \ \le\ (t-1)k\log_2 q - n\psi^{cc}(\tau) + \binom t2\frac{n(\alpha(t-1) + \beta)}{M} + n\log_2\Bigl((1 + q^{-s_\mathsf{D}})^{t-1} + \binom{t-1}{2}2^{-s_\mathsf{C}\lambda}\Bigr) + \frac{n^2}{(m-n)\ln 2}.$$

*Proof.* Take $M$ members and subsets $I_j$ of size $A$ of their agreement sets. Apply Lemma 1 to the pattern function $\varphi = \alpha|S_i|\,[i \in I_1] + \beta\,[i \notin I_1, |S_i| \ge 2]$, for which $\bar\varphi = \psi$ (the first member plays $I_1$): some $t$ distinct members, in some order, have a canonical labeling $T$ with $\Psi(T) := \alpha W_\mathsf{D}(T) + \beta g(T) \ge \Psi_0 := n\psi^{cc}(\tau) - \binom t2n(\alpha(t-1)+\beta)/M$, and $E_T$ holds. So $\Pr[\mathrm{Bad}] \le \sum_{T : \Psi(T) \ge \Psi_0}\Pr[E_T]$ over all labelings. For such $T$, $q^{-W_\mathsf{D}}2^{-\lambda g} \le 2^{-\Psi_0}\,q^{-s_\mathsf{D}W_\mathsf{D}}2^{-s_\mathsf{C}\lambda g}$, and the sum of the right side over all labelings is a product over coordinates: $2^{-\Psi_0}\bigl(\sum_{S \subseteq \{2..t\}}q^{-s_\mathsf{D}|S|} + \binom{t-1}2 2^{-s_\mathsf{C}\lambda}\bigr)^n$. Lemma B1 gives the rest. $\square$

**[checked]** the averaging step for this $\psi$: for 400 random column-count profiles ($n \le 200$, $M \le 1000$, $t \le 16$) the exact expectation over tuples without replacement is at least the bound of Lemma 1 (`36_star_check.py`).

How it works. The cost is $(\rho - \tau^2)\log_2 q$ bits a coordinate for each member after the first (the dimension the centre does not pin down; zero at Johnson), the gain is $\lambda$ for each coordinate outside the centre that two members share, and the patterns cost at most $\log_2(2^{t-1} + \binom{t-1}2)$ bits a coordinate, less with the tilts. At rate 1/2, $t = 4$, $\tau = 0.685$, points in $K$: cost $3 \cdot 0.031 \cdot 64 = 5.9$, gain $40 \cdot 0.315 \cdot 0.765 = 9.6$, patterns at most 3.46. At low rate $t$ grows like $1/\tau$ and $\tau$ falls to a small multiple of $\rho$ (5 times at level 2, 9 at level 3), which is the regime of [FKS] with usable constants.

**Theorem B' (points of $E \setminus K$, polynomials over $K$). [proved]** Let $S$ contain one element of each conjugate pair of $E \setminus K$, $m = (2^{128} - 2^{64})/2$. For polynomials over $K$ of degree $< k$ evaluated at $n$ random distinct points of $S$, Theorem B holds with $(t-1)k\log_2q$ replaced by $(t-1)\cdot 64k$, $\log_2 q = 128$ in $\alpha$ and in the last logarithm, and $\lambda = \log_2\bigl((2^{128} - 2^{64})/(k-1)\bigr)$. *Proof.* A polynomial over $K$ vanishing at $c$ pairwise non-conjugate points of $E \setminus K$ is divisible by $c$ distinct irreducible quadratics, so these form a space of dimension $k - 2c$ over $K$, with $2^{64(k-2c)} = 2^{128(k/2 - c)}$ elements; a nonzero one has at most $(k-1)/2$ roots in $S$. The rest is unchanged. $\square$ This is Theorem B for a code of rate $\rho/2$: the lanes are $K$-valued and each symbol is two words of $K$.

**Corollary 4.3 (interleaved words, $E$-valued lanes on points of $K$). [proved]** In Theorems A and B, $\mathrm{Bad}$ may be replaced by: some interleaved word, with any number of lanes over $F$, has $M$ tuples of polynomials agreeing with it on $A$ columns. For $E$-valued lanes on points of $K$ the theorems apply with $F = K$. *Proof.* The members and their agreement sets enter the proofs only through the sets $I_j$ until $t$ of them are chosen. For those $t$ tuples a linear combination of the lanes with coefficients in $F$ keeps them pairwise distinct as soon as $\binom t2 < |F|$ (each pair excludes a hyperplane of coefficient vectors), and the combined polynomials agree with the combined word on the same columns. An $E$-valued polynomial on points of $K$ is two $K$-valued lanes. $\square$ No factor is lost, in the list or in the probability.

### 4.3 Unions of cosets with random representatives

**Theorem B$_w$. [proved]** Let $U \subseteq F$ be a fixed $\mathbb{F}_2$-subspace with $w$ elements, $S_0$ a set of $m/w$ representatives of distinct cosets, and let the domain be $\bigcup_{\gamma \le n/w}(c_\gamma + U)$ with $(c_\gamma)$ uniform over tuples of distinct elements of $S_0$. Then the bound of Theorem B holds with $\lambda$ replaced by $\lambda_w = \lambda - \log_2 w$, with
$$\psi_w(d) = \alpha(t-1)d^2 + \beta\Bigl(\frac{(1-d)B_{t-1}(d)}{w} - d\bigl(1 - (1-d)^{t-1}\bigr)\Bigr),$$
the pattern term replaced by $\frac nw\log_2\bigl((1 + q^{-s_\mathsf{D}})^{(t-1)w} + w\binom{t-1}2 2^{-s_\mathsf{C}\lambda_w}\bigr)$ and the last term by $(n/w)^2/((m - n)/w \cdot \ln 2)$.

*Proof.* Label cosets instead of coordinates. A coset is of type $\mathsf{D}$ if one of its points lies in $I_1$ and in another member; then all such points carry their sets $S$. Otherwise it is of type $\mathsf{C}$ if one of its points is shared by two members, and one such point and pair are designated. In the count of Lemma B1 a representative of type $\mathsf{D}$ is free and its points are distinct points at which the differences vanish; a representative of type $\mathsf{C}$ satisfies $(g_j - g_{j'})(c + u) = 0$ for the designated $u$, at most $h$ values out of $m/w$. One representative gives one factor $hw/m$ however many of its points are shared: this is the loss. For the averaging, the probability that a coset is of type $\mathsf{C}$ is at least $\max_u\Pr[u \text{ shared outside } I_1] - \sum_u\Pr[u \in I_1 \text{ and in another member}]$, at least the average over $u$ of the first minus the sum of the second, which is a sum over coordinates of a function of $d_i$, and Lemma 1 applies to it. $\square$

The worst case is real: agreement sets that are unions of whole cosets give exactly one factor per coset.

## 5. Results

### 5.1 Tables

All from `scripts/36_bounds.py`, reproduced in `scripts/36_results.txt`. The thresholds are found by bisection; the bounds are monotone in $\tau$ on the ranges used (**[checked]** on a grid for five rows). The envelope $\psi^{cc}$ is computed on a grid of 1000 points and lowered by the largest second difference over 8, which bounds the error of the grid. $M = 2^{64}$, tilts and $t \le 1024$ from fixed grids, so the true optima of the theorems are slightly better.

T1 and T2 are in section 0. T3, the sampling-set size (level 0, points and coefficients in a field of $2^b$ elements): $\tau$ of Theorem A, then of Theorem B.

| rate | $b = 48$ | 64 | 80 | 96 | 128 | 192 | 256 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 (0.7071) | 0.773, 0.697 | 0.715, 0.684 | 0.687, 0.677 | 0.666, 0.672 | 0.639, 0.665 | 0.609, 0.659 | 0.593, 0.656 |
| 1/4 (0.5) | 0.590, 0.479 | 0.512, 0.462 | 0.480, 0.452 | 0.456, 0.445 | 0.422, 0.437 | 0.384, 0.429 | 0.363, 0.425 |
| 1/8 (0.3536) | 0.455, 0.327 | 0.370, 0.308 | 0.343, 0.297 | 0.322, 0.289 | 0.292, 0.280 | 0.256, 0.271 | 0.235, 0.267 |
| 1/16 (0.25) | 0.357, 0.221 | 0.270, 0.201 | 0.247, 0.190 | 0.229, 0.183 | 0.206, 0.174 | 0.178, 0.166 | 0.161, 0.162 |

Theorem A reaches the Johnson agreement itself from $m = 2^{69}, 2^{70}, 2^{73}, 2^{77}$ at rates 1/2 to 1/16 (**[checked]**). Theorem B depends weakly on the field: its cost and its gain both scale with the field, only the pattern term does not. Theorem A keeps improving with the field, slowly ($\tau - \rho \sim 1/\sqrt\lambda$).

### 5.2 The margin of the generic-points line with points in $K$

T4 (**[checked]**): $\log_2$ of the bound of Theorem A at the Johnson agreement, best $t$: $+0.317n$, $+0.348n$, $+0.343n$, $+0.286n$ bits at rates 1/2 to 1/16, all at $t = 3$. The inequality that fails is $r\,(\lambda - \log_2(e\mu\,\mathrm{wt}/r)) > \log_2N_3$ with $r \le D \approx (\tfrac{3\tau^2 - \tau^3}{2} - \rho)n$: at rate 1/2 the left side is about $0.073n \cdot 30 = 2.0n$ bits against $2.3n$.

### 5.3 What the list budget buys, and what it does not

Both theorems bound $\Pr[\mathrm{Bad}]$ by the expected number of bad agreement patterns of $t$ members, and the list enters once: Lemma 1 needs $M \ge t^3n$ to choose the $t$ members, which is why the statement is "fewer than $2^{64}$" and not "at most $t - 1$". This is the modification the brief asked for (a weaker conclusion on the list size against a better radius), and without it the two theorems stop at the generalized Singleton radius of $t - 1$.

Could a list of $2^b$ members buy more? It contains $\binom Mt$ bad $t$-subsets, so a Markov argument on the number of bad patterns could divide the bound by at most $2^{tb}$, and only if distinct tuples are shown to give distinct patterns, which I did not prove. The pattern terms, $\log_2N_t$ or $n\log_2Z$ at the optimal tilts, are (**[checked]**): $5.63n$ bits for Theorem A at level 0 ($t = 6$, points in $E$); for Theorem B with points in $K$, $2.90n$ at level 0 ($t = 4$), $2.28n$ at level 1 ($t = 10$), $0.35n$ at level 3 ($t = 80$), $0.084n$ at level 5 ($t = 384$). With $b = 1000$ the ratio $tb$ over the pattern term is $4 \cdot 10^{-5}$ at level 0, $3 \cdot 10^{-4}$ at level 1, 5% at level 3 and above 1 at level 5. So at levels 0 to 2 the budget cannot move $\tau$ beyond the fourth decimal in these proofs (**[proved]** as an accounting of these proofs, not as a lower bound on all proofs), and at the last levels, where the theorems already give 10 to 16 queries, it might buy a query or two (**[estimate]**, not pursued). Choosing the members better than on average is the content of section 6.

A proof that pays less than one bit per coordinate and member at level 0 would have to avoid the first moment over patterns. The volume bound gives lists of size $2^{\Omega(n)}$ for $\tau < \rho + H(\tau)/\log_2 q$ (the brief's $\rho + 1/64$), so the gap between what is proved here and what could be true for random points is large: at rate 1/2, 0.684 against roughly 0.52.

## 6. Beyond the star: the multi-parent count (not a theorem)

In Theorem B every member is tied to the centre only, and pays $(\rho - \tau^2)\log_2q$. In a list of independent-looking sets the third member already shares $\tau(2\tau - \tau^2)n$ points with the first two, more than $k$ at rate 1/2 for $\tau > 0.6$: it could be determined at no cost.

**Lemma 6.1 (sequential count). [proved]** Let $(I_1, \dots, I_t)$ be ordered and $1 \le r \le t$. Call a coordinate free if its second member (in the order) has index at most $r$. Let $c_j = |I_j \cap (I_1 \cup \dots \cup I_{j-1})|$ for $j \le r$, and for $j > r$ let $c_j$ be the number of points of $I_j$ that lie in at least two earlier members. Let $g$ be the number of coordinates with at least two members that are not free. Then the probability that distinct members with these agreements exist is at most $e^{n^2/(m-n)}\,q^{\sum_{j \ge 2}(k - c_j)_+}(h/m)^g$.

*Proof.* Process $j = 2, \dots, t$ with $f_1 = 0$. At step $j \le r$ choose the points of the coordinates whose second member is $j$ (free, $m$ ways each); every point of $I_j$ in an earlier member is now chosen, and $f_j$ takes prescribed values at $c_j$ distinct points: at most $q^{(k - c_j)_+}$ polynomials. At step $j > r$ choose the points of the non-free coordinates whose third member is $j$: each is a root of the difference of its first two members, both determined, at most $h$ ways; then $f_j$ takes prescribed values at the $c_j$ points of $I_j$ in at least two earlier members (all chosen by now). At the end the non-free coordinates with exactly two members are roots of a known difference, $h$ ways, and the rest are free. $\square$

**What is missing.** A lemma that every list of $2^b$ sets contains an ordered $t$-tuple for which $\log_2q\sum_j(k - c_j)_+ - \lambda g$ is at most its value for independent sets of density $\tau$. Lemma 1 does not give it: $(k - c)_+$ is convex in $c$, so Jensen goes the wrong way, and a list made of two populations with different overlaps defeats the average. Such lists are denser sub-instances and should be easier, not harder, but turning this into a proof needs a regularization: classify the members by their intersection sizes with the members already chosen, keep the largest class (this costs a constant factor of the list per step, which is where a budget of $2^{1000}$ would be spent), and use the constraint that two members share fewer than $k$ points. I did not carry this out.

**[heuristic]** T5: the threshold at which the count of Lemma 6.1, evaluated on a regular list (every coordinate in a $\tau$ fraction of the members, independently) and added to the entropy of the pattern distribution, becomes negative, optimized over $t \le 400$ and $r$. No theorem.

| | level 0, rates 1/2, 1/4, 1/8, 1/16 | levels 1 to 5 |
| --- | --- | --- |
| points in $K$ | 0.665 (184), 0.405 (83), 0.234 (52), 0.133 (38) | 37, 20, 14, 11, 10 queries |
| points in $E$ | 0.618 (156), 0.349 (72), 0.190 (46), 0.101 (33) | 33, 18, 13, 11, 10 queries |
| Theorem B, points in $K$, for comparison | 198, 98, 64, 47 | 46, 24, 16, 13, 10 |

So the most a completed proof of this kind could reach at level 0, rate 1/2, with points in $K$ is about 184 queries: it would not change the verdict on cost.

## 7. How much independence the proofs use

**Theorem A** uses three things. (i) [AGGLZ] Theorem 2.11: a determinant is nonzero as a polynomial in $n$ independent variables, one per coordinate. (ii) Their Lemma 3.11: conditioned on all earlier points, each point is uniform on at least $m - n$ values. The events $E_j, F_j$ of a certificate depend on every point up to index $i_j$, not only on the $r$ certificate coordinates, so $r$-wise independence is not enough: the proof uses the full sequential independence. (iii) Exchangeability of coordinates of equal type, which holds for any hypergraph.

**Theorem B** uses: two members agree on at most $h$ points of $S$; evaluations at distinct points are independent conditions; and, in Lemma B1, that the points of the labeled coordinates are jointly uniform (the points of the $\mathsf{C}$ coordinates uniform given those of the $\mathsf{D}$ coordinates). The unlabeled coordinates play no role. So it holds for $\nu$-wise independent points with $\nu$ the largest number of labeled coordinates, about $\bigl(\tau(1 - (1-\tau)^{t-1}) + (1-\tau)B_{t-1}(\tau)\bigr)n$: $0.90n$ at level 0, rate 1/2, and $0.16n$ at level 3. A family with that much independence has no structure an encoder could use, so this observation buys nothing.

**Proposition 7.1 (entropy needed by a first moment). [proved]** If the evaluation set is a function of a seed of $\sigma$ bits, every nonempty event has probability at least $2^{-\sigma}$. A proof of the form $\Pr[\mathrm{Bad}] \le \sum_T\Pr[E_T] \le 2^{-100}$ therefore has at most $2^{\sigma - 100}$ nonempty events $E_T$: all other patterns must be shown impossible for every set of the family. The patterns that Theorems A and B sum over number $2^{cn}$, with $c$ from 0.08 (Theorem B at level 5) to 2.9 (Theorem B at level 0) and 5.6 (Theorem A at level 0). $\square$

So a family with fewer than about $cn$ random bits (a union of $2^{R+a}$ cosets of a subspace with random representatives has $64 \cdot 2^{R+a}$; a random subspace has $64N$) can only be handled by a deterministic theorem about almost all patterns, of the kind note 30 looked for. It is not a matter of constants.

**Proposition 7.2 (the generic-rank theorem is false on coset unions). [proved]** Let $U \subseteq F$ be a subspace with $w \ge 2$ elements, $m_0 \ge 1$, $k' = wm_0$, and let the domain contain $m_0 + 2$ cosets $c_\gamma + U$. Then for every choice of the representatives there are $t = m_0 + 2$ distinct polynomials of degree at most $k'$ and a word whose agreement hypergraph has weight at least $(t-1)(k'+1)$. Hence some subhypergraph is $(k'+1)$-weakly-partition-connected and its reduced intersection matrix, of full column rank over $F(X_1, \dots, X_n)$ by [AGGLZ] Theorem 2.11, is rank-deficient identically in the representatives.

*Proof.* $L_U$ is constant on each coset, with distinct values $v_\gamma$. Let $y = L_U^{m_0+1}$ and, for each $\gamma_0$, let $G_{\gamma_0}$ of degree at most $m_0$ interpolate $v \mapsto v^{m_0+1}$ at the $v_\gamma$, $\gamma \ne \gamma_0$. The polynomials $G_{\gamma_0}\circ L_U$ have degree at most $k'$, are distinct, and each agrees with $y$ on $m_0 + 1$ cosets. Every point of the $m_0 + 2$ cosets lies in $t - 1$ agreement sets, so the weight is $w\,t(t-2)$, and $w\,t(t-2) - (t-1)(w(t-2) + 1) = w(t-2) - (t-1) \ge 0$ for $w \ge 2$, $t \ge 3$. [AGGLZ] Lemma 2.4 gives the subhypergraph and Lemma 2.8 the kernel vector. $\square$

This is the coset-union family of the main document read as a rank statement, and it holds down to cosets of two points. Its slack is $(w(t-2) - (t-1))/(t-1) < w$ per unit of connectivity, so it refutes Theorem 2.11 on coset unions but not a robust version in which more than $w$ coordinates may be deleted; no such version is proved. So Theorem A does not extend to coset unions as it stands, for any coset size, and Theorem B does, at the price of Theorem B$_w$.

**Random subset of a larger subspace.** Theorem B applies with $S$ the subspace: $m = 2^cn$, so $\lambda = R + c$ instead of 40. T7 (**[checked]**): nothing below Johnson for $c \le 12$ at rate 1/2, $c \le 8$ at rates 1/4 and 1/8, $c \le 4$ at rate 1/16; the first gains are one or two queries, at $c = 16$ (rate 1/2), $c = 12$ (rates 1/4 and 1/8), $c = 8$ (rate 1/16). The encoder would be an NTT $2^c$ times longer.

**Random subspace, random coset representatives of a large subspace.** Outside both proofs by Proposition 7.1, and by Proposition 7.2 for Theorem A.

## 8. Encoding cost

**Today** (Annex D, Proposition `prop:ntt`): $\tfrac12\kappa n$ multiplications and $\kappa n$ additions per lane.

**Independent points** (**[estimate]**, `scripts/36_cost.py`; a multiplication count, not a measurement). The points are public and fixed, so the subproduct tree and its transforms are precomputed. Each lane is $n/k$ batches of $k$ points, each a remainder tree in which the step from a node of $2^{j+1}$ points to a child is one middle product, $2^{j+1}(j+2)$ multiplications with additive transforms of size $2^{j+1}$, or twice that if the middle product needs transforms of double size (I did not design the characteristic-two middle product). Per point about $\kappa^2 + 3\kappa$ to $2\kappa^2 + 6\kappa$ multiplications against $\kappa/2$: a factor $2\kappa + 6$ to $4\kappa + 12$. For $\kappa \le 5$ Horner is cheaper ($2^\kappa$ per point).

| level | $\kappa$ | share of level-0 words (note 08) | random points, times the level's own NTT | in level-0 NTTs | cosets of 4 | cosets of 16 | precomputed tree |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | 24 | 1 | 53 to 106 | 53 to 106 | 45 | 38 | 6.0 GiB |
| 1 | 20 | 1/4 | 45 to 89 | 11 to 22 | 37 | 30 | 2.5 GiB |
| 2 | 16 | 1/8 | 37 to 72 | 4.6 to 9.1 | 29 | 22 | 1.0 GiB |
| 3 | 12 | 1/16 | 28 to 55 | 1.8 to 3.5 | 20 | 13 | 0.38 GiB |
| 4 | 8 | 1/32 | 20 to 37 | 0.6 to 1.2 | 11 | 4 | 0.12 GiB |
| 5 | 4 | 1/64 | 8 | 0.12 | 2 | not applicable | 0.03 GiB |

The tree is read once per lane, 64 times 6 GiB at level 0 against a few passes over 16 GiB today, and the prover is memory-bandwidth bound, so the time ratio at level 0 is probably worse than the multiplication ratio. For scale: in the run quoted by note 24 the level-0 commitment (encode, stores and Merkle hashing) is 92 ms of a 450 ms proof.

**Cosets of size $w = 2^c$ with random representatives** (the base-$L_U$ expansion of the brief): $f = \sum_j f_j L_U^j$ with $\deg f_j < w$, so on $c_\gamma + U$ the polynomial is $\sum_j f_j b_\gamma^j$ with $b_\gamma = L_U(c_\gamma)$: $w$ multipoint evaluations with $k/w$ coefficients at $n/w$ points, then one transform of size $w$ per coset, after a change of basis. The gain over independent points is the factor $(\kappa - c)(\kappa - c + 3)/(\kappa(\kappa+3))$ only. Note 06's Fact A (a union of $2^R$ cosets of the message subspace with arbitrary representatives costs the same NTT as today) is the case $w = k$, which Proposition 7.1 puts out of reach.

**Verifier.** Unchanged in kind: the column weights $\prod_b\widehat W_b(x)^{u_b}$ are defined for any $x$ and cost $O(\kappa)$ by the chain of Lemma `lem:chain` (note 06, Fact A). The verifier must know the queried point: $x_i$ derived from the seed and $i$, one Keccak permutation per query natively and in the guest, on top of the path. The generation must output distinct points (resample the seed on a collision, probability $2^{-15}$ at level 0), and a hash in place of true randomness makes the list bound a statement in the random-oracle model for the seed expansion. The list size $2^{64}$ costs one DEEP point over the $2^{40}$ budget (13 instead of 12 at level 0, note 11).

## 9. Verdict per rate and level

Is there an evaluation set with a proven list bound below the Johnson radius at failure probability $2^{-100}$?

| where | answer | threshold, queries (Johnson) | prover cost | proof size |
| --- | --- | --- | --- | --- |
| level 0, rate 1/2 | yes, random points of $K$, Theorem B, list $2^{64}$ | 0.684, 198 (217) | level-0 encode times 53 to 106 | about $-19$ KiB of 333, plus one Keccak a query |
| level 0, rate 1/4 | yes, same | 0.462, 98 (109) | same factor | about $-10\%$ of level 0 |
| level 0, rate 1/8 | yes, same | 0.308, 64 (73) | same | about $-12\%$ of level 0 |
| level 0, rate 1/16 | yes, same | 0.201, 47 (55) | same | about $-15\%$ of level 0 |
| level 0, any cheap structured set (coset unions of any size, subset of a subspace up to $2^8$ times larger) | no | none | | |
| level 0, points in $E$ | yes (0.639, 168 at rate 1/2 for the code over $E$), dominated: the leaf doubles | | worse than points in $K$ | larger than today |
| levels 1 to 3 | yes, random points of $K$ | 46, 24, 16 (55, 31, 22) | 11 to 22, 4.6 to 9.1, 1.8 to 3.5 level-0 NTTs | $-22$ queries, about $-17$ KiB |
| levels 4 and 5 | yes, random points of $K$; also cosets of 2 to 16 | 13, 10 (17, 14); cosets of 4: 14, 11 | 0.6 to 1.2 and 0.12 level-0 NTTs; cosets of 4: 0.34 and 0.04 | $-8$ queries, about $-6$ KiB (1.8%) |

At every level together the proof would shrink by about 13% (49 queries of 356) for an encoder 50 to 100 times slower. The only piece with a defensible cost is the last two levels, for under 2%. As a matter of soundness theory the answer to the brief's question is yes; as an engineering option it is dominated by lowering the rate (rate 1/4 with Johnson: 109 queries for twice the encode).

What would change this:

1. A deterministic statement for a structured family (Proposition 7.1 says nothing else can work): for instance Lemma B1's two inputs, distance and independent conditions, hold on every domain, and the only random input of Theorem B is the uniformity of the shared points. A structured domain on which, for every pattern, the shared points still have few solutions is a statement about the solutions of $(g_j - g_{j'})(a_i) = 0$ with the $a_i$ tied by the structure, and Theorem B$_w$ shows the loss is exactly the number of points tied to one random variable.
2. The regularization lemma of section 6, for a further 7% at level 0.
3. Nothing of this kind reaches the neighbourhood of capacity at level 0: the pattern count caps it (section 5.3).

## 10. Reproduction

- `scripts/36_bounds.py`: Theorems A, B, B', B$_w$ and the heuristic of section 6; tables T1 to T7; about 30 seconds (`quick` for a first row of each).
- `scripts/36_literature.py`: section 2.
- `scripts/36_cost.py`: section 8.
- `scripts/36_star_check.py`: Lemma B1 on toy fields and Lemma 1 for $\psi$; a few seconds.
- `scripts/36_results.txt`: the output of the four scripts.

## References

- [AGGLZ] O. Alrabiah, Z. Guo, V. Guruswami, R. Li, Z. Zhang. Random Reed-Solomon codes achieve list-decoding capacity with linear-sized alphabets. arXiv 2304.09445v6.
- [BDG] J. Brakensiek, M. Dhar, S. Gopi. Generalized GM-MDS: polynomial codes are higher order MDS. arXiv 2310.12888v3.
- [BDGZ] J. Brakensiek, M. Dhar, S. Gopi, Z. Zhang. AG codes achieve list-decoding capacity over constant-sized fields. arXiv 2310.12898.
- [BGM] J. Brakensiek, S. Gopi, V. Makam. Generic Reed-Solomon codes achieve list-decoding capacity. arXiv 2206.05256v4.
- [FKS] A. Ferber, M. Kwan, L. Sauermann. List-decodability with large radius for Reed-Solomon codes. arXiv 2012.10584v2.
- [GLSTW] Z. Guo, R. Li, C. Shangguan, I. Tamo, M. Wootters. Improved list-decodability and list-recoverability of Reed-Solomon codes via tree packings. arXiv 2011.04453v2.
- [GM] V. Guruswami, J. Mosheiff. Punctured low-bias codes behave like random linear codes. arXiv 2109.11725v5.
- [GZ] Z. Guo, Z. Zhang. Randomly punctured Reed-Solomon codes achieve the list decoding capacity over polynomial-size alphabets. arXiv 2304.01403v2.
- [LMS] M. Levi, J. Mosheiff, N. Shagrithaya. Random Reed-Solomon codes and random linear codes are locally equivalent. arXiv 2406.02238v7.
- [PP] A. Putterman, E. Pyne. Pseudorandom linear codes are list decodable to capacity. arXiv 2303.17554v2.
- [RW] A. Rudra, M. Wootters. Every list-decodable code for high noise has abundant near-optimal rate puncturings. arXiv 1310.1891v1.
