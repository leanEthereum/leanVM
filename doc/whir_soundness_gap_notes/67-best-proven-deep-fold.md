# 67. The best DEEP-fold configuration proven today, against the best proven configuration of today's protocol

Researcher 67, round 14. Scripts: `scripts/67_*`. Nothing outside this file and those scripts was written.

Labels used throughout: **proved** (a mathematical proof is given or cited from the committed paper `doc/deep_fold/`), **exact in the model** (an exact evaluation of a stated parameter model, not a measurement of an implementation), **measured** (taken from a run of the code in `crates/`), **estimated** (a cost model or an extrapolation).

## 0. Verdict

**The DEEP fold with proven list bounds is not better than configuration C by a useful margin, and on the user's own criteria it is worse.** Its best proven configuration (32 lanes, A's level-0 query grind, C's ladder with a retuned tail, Johnson thresholds at every level of dimension 500 or more, the counting bound at the last one or two levels, points on the ladder schedule) has an opening 1.6 to 6.0 percent smaller than C (4 to 9 KiB; 1.5 to 4.6 percent against today's protocol on its own best ladder), a recursive verifier whose cost for the opening is 2 to 9 percent higher than C's (estimated; a tie at an unreachable floor for the cost of a point), and a prover about 2 percent slower (estimated from measured kernels), for a new protocol in both provers, the three verifiers and `formal/`. At equal prover time C recovers another half percent on both counts. The reason is structural and **proved** in section 1: every bound that uses only the distance of the code (Johnson, counting, and the shortened Johnson bound that interpolates them) leaves every level of dimension above a few hundred on the Johnson radius, where today's analysis already sits within one query, so the DEEP fold's gain is confined to the last one or two tiny levels while its points are paid at every level. The single result that would change this is a list bound below the Johnson radius at level 0 (for instance $2^{40}$ at agreement $0.66\,n$ at rate $1/2$: 10 to 12.5 percent below C in bytes and 4 to 7 percent in guest cost). A list bound for the small codes of the last levels, or a counting bound sharper by a factor of eight in the exponent, would not: 2 to 4 percent at the large sizes, with a slower guest (section 4).

Opening in KiB and guest cycle-equivalents of the opening, full stack (**exact in the model** for bytes; cycle-equivalents **estimated**; sections 2 and 3 define the rows and give queries, points, Keccak counts and prover cost):

| $\mu$, rate | today | C (proven, today's protocol) | T\*: today's protocol, best ladder | P: the paper's DEEP instance | D+C: DEEP with C's knobs | D\*: best proven DEEP, bytes | Dc: best proven DEEP, guest |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 24, 1/2 | 260.4, 181.4k | 224.9, 157.6k | 223.1, 157.0k | 252.1, 184.5k | 216.9, 163.6k | 215.9, 163.6k | 217.8, 161.0k |
| 28, 1/2 | 313.7, 218.4k | 276.1, 192.1k | 273.6, 192.8k | 306.4, 225.5k | 269.2, 202.9k | 267.7, 198.5k | 273.6, 197.5k |
| 30, 1/2 | 335.9, 226.9k | 297.1, 200.1k | 296.8, 199.7k | 332.0, 234.7k | 292.7, 211.3k | 292.3, 211.3k | 295.1, 208.8k |
| 24, 1/4 | 169.9, 115.2k | 156.1, 105.4k | 153.9, 104.5k | 163.6, 120.3k | 147.6, 112.0k | 146.8, 112.2k | 156.3, 108.9k |
| 28, 1/4 | 207.7, 133.4k | 192.3, 123.1k | 189.4, 121.7k | 201.7, 141.7k | 186.1, 134.2k | 184.0, 130.1k | 190.7, 128.4k |
| 30, 1/4 | 222.6, 146.3k | 206.5, 134.6k | 206.2, 134.2k | 220.0, 155.3k | 202.3, 146.1k | 202.3, 146.1k | 209.0, 143.5k |

What is new here beyond the paper's own sentence that the unconditional instance "is not a reason to deploy it": the comparison is against C and not against today (the paper's instance is 5 to 12 percent *larger* than C); the DEEP fold is optimized over its ladder, schedule and grinds and combined with C's knobs; one elementary list bound is added (Proposition 1.2, item 4) and shown to be worth one query a level; and the guest and prover costs are put next to the bytes.

## 1. Every proven list bound the DEEP-fold theorem can use

Notation as in the paper: a level has $n$ columns, $2^\ell$ lanes, analysis degree $d = 2^\kappa - 1 + \ell$, rate $2^{-R}$ ($n = 2^{\kappa + R}$), and one free threshold $A_0 = A^{(i,0)}$; the queries see $A_{\mathrm{end}} = A_0 + \ell$. Theorem 5.2 needs one number per level, a bound $L$ on the list of every interleaved word (any number of lanes, values in $E$) at agreement $A_0$ and degree $d$, and $L$ enters row M0 only, where points pay for it.

**Lemma 1.1 (lists are packings).** **[proved]** Let $U_1, \dots, U_L$ be distinct tuples of polynomials of degree at most $d$ over any field containing the domain, each agreeing with one interleaved word on a set $S_i$ of at least $A \ge d + 1$ columns. Then $|S_i \cap S_j| \le d$ for $i \ne j$. *Proof.* On $S_i \cap S_j$ both tuples equal the word, so in a lane where they differ a nonzero polynomial of degree at most $d$ vanishes on $S_i \cap S_j$. $\square$

So $L \le P(n, A, d)$, the largest number of $A$-subsets of an $n$-set with pairwise intersections of at most $d$ elements (shrink each $S_i$ to $A$ elements; intersections do not grow and, as $A > d$, the sets stay distinct). Every bound below is a bound on $P$: it holds for every lane count and every coefficient field at once, and needs none of the interleaving reductions of the paper's section 6.1.

**Proposition 1.2.** **[proved]** (classical for constant-weight codes; the proofs are two double counts)

1. *Unique decoding.* If $2A > n + d$ then $P = 1$. (Two sets meet in at least $2A - n > d$ elements.)
2. *Johnson* (the paper's Theorem 2.2). If $A^2 > nd$ then $P \le \lfloor n(A - d)/(A^2 - nd) \rfloor$.
3. *Shortening.* For $d \ge 1$, $P(n, A, d) \le \lfloor \tfrac{n}{A} P(n-1, A-1, d-1) \rfloor$, and $P(n, A, 0) = \lfloor n/A \rfloor$. *Proof.* Let $\deg(x)$ be the number of sets through $x$. The sets through $x$, with $x$ removed, are $(A-1)$-subsets of $n - 1$ elements meeting pairwise in at most $d - 1$, so $\deg(x) \le P(n-1, A-1, d-1)$, and $\sum_x \deg(x) = LA$. $\square$
4. *Shortened Johnson.* For every $0 \le j \le d$ with $(A - j)^2 > (n - j)(d - j)$,
$$P(n, A, d) \le \Bigl\lfloor \tfrac{n}{A} \Bigl\lfloor \tfrac{n-1}{A-1} \cdots \Bigl\lfloor \tfrac{n-j+1}{A-j+1} \Bigl\lfloor \tfrac{(n-j)(A-d)}{(A-j)^2 - (n-j)(d-j)} \Bigr\rfloor \Bigr\rfloor \cdots \Bigr\rfloor \Bigr\rfloor .$$
The case $j = 0$ is Johnson. The case $j = d$ is the **counting bound** with floors, at most the paper's $\binom{n}{d+1} / \binom{A}{d+1} = \prod_{i=0}^{d} \frac{n-i}{A-i}$, valid for every $A \ge d + 1$.

The condition of item 4 is linear in $j$: $(A-j)^2 - (n-j)(d-j) = A^2 - nd + j\,(n + d - 2A)$. So below the Johnson radius the least admissible $j$ is $j_0 = \lfloor (nd - A^2)/(n + d - 2A) \rfloor + 1$, and the bound is about $(n/A)^{j_0}$ times a Johnson factor of at most $n(A-d)$. With $A = \theta n$ and $d = \rho n$, $j_0 / n \approx (\rho - \theta^2)/(1 - 2\theta + \rho)$: zero at the Johnson radius $\theta = \sqrt\rho$ and $\rho$ at capacity, where it is the counting bound. Item 4 is not in the paper, which uses only $j = 0$ and $j = d$; it is the "sharper counting bound" the brief asks about, and it is elementary. It interpolates between the two and is never worse than either.

**What is not available.** **[status of the night's research, not re-derived here]** No bound on $P$-free quantities (that is, using more of the Reed-Solomon code than its distance) is proved below the Johnson radius on leanVM's domains for all words. The bounds above use the distance alone. For the distance alone there is little more to find: random $A$-subsets meet in about $A^2/n$ elements, so for $A^2 \le (1 - \epsilon)\,nd$ and growing $d$ the packing number $P(n, A, d)$ is exponential in $d$ (**standard, not re-proved here**), and a real improvement must use the code.

**Cost of a list in points.** **[exact in the model]** Row M0 of Theorem 5.2 with the paper's constants ($K_0 = 2^9 q$, $\tau = 2^{-119}$, 15-bit grind) needs $s \log_2(1/\varepsilon) \ge 3 \log_2 L + 1062$ for $\ell = 6$, $+ 943$ for $\ell = 5$, $+ 824$ for $\ell = 4$ (one batch), with $\log_2(1/\varepsilon) = 104$ to $123$. `scripts/67_model.py` evaluates the row as an exact integer inequality and reproduces the paper's table of points (section 7.1) and its two ladders entry for entry (`selftest`).

### 1.1 The smallest proven threshold as a function of the points spent

**[exact in the model]** (`scripts/67_bounds.py`, full output for rates 1/2 to 1/16 and $\mu = 24, 26, 28, 30$ in `scripts/67_bounds_output.txt`). For each level of the deployed ladder: the points and queries at the Johnson threshold, then, for $s$ points in one batch, the queries at the least threshold $A_0 \ge d + 2$ whose best proven list bound $s$ points pay for, with $\log_2(n / A_0)$ (the bits a query gives, up to the $\ell$ columns of loss; capacity is $\log_2(n/(d+1))$) and the bound that gives it: J Johnson, S shortened Johnson, C counting. Query grind 17 bits.

Rate 1/2, $\mu = 30$:

| level $(\kappa, \ell)$ | $\log_2 n$ | $d + 1$ | Johnson: points, queries | $s = 12$ | $s = 16$ | $s = 24$ | $s = 32$ | $s = 48$ | $s = 64$ | $s = 96$ | $s = 128$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 (24, 6) | 25 | 16777222 | 11, 217 | 217 (0.500 S) | 217 (0.500 S) | 216 (0.500 S) | 216 (0.500 S) | 216 (0.500 S) | 216 (0.500 S) | 216 (0.500 S) | 216 (0.500 S) |
| 1 (20, 4) | 24 | 1048580 | 8, 55 | 54 (2.000 S) | 54 (2.000 S) | 54 (2.000 S) | 54 (2.000 S) | 54 (2.000 S) | 54 (2.000 S) | 54 (2.001 S) | 54 (2.001 S) |
| 2 (16, 4) | 23 | 65540 | 8, 31 | 31 (3.500 S) | 31 (3.501 S) | 31 (3.502 S) | 31 (3.502 S) | 31 (3.504 S) | 31 (3.505 S) | 31 (3.509 S) | 31 (3.512 S) |
| 3 (12, 4) | 22 | 4100 | 8, 22 | 22 (5.005 S) | 22 (5.010 S) | 22 (5.021 S) | 22 (5.031 S) | 22 (5.052 S) | 22 (5.074 S) | 22 (5.120 S) | 21 (5.167 S) |
| 4 (8, 4) | 21 | 260 | 8, 17 | 17 (6.572 S) | 17 (6.649 S) | 16 (6.825 S) | 16 (7.039 S) | 15 (7.677 S) | 13 (8.964 S) | 9 (12.743 C) | 9 (12.972 C) |
| 5 (4, 4) | 20 | 20 | 7, 14 | 10 (10.825 C) | 8 (15.608 C) | 8 (15.608 C) | 8 (15.608 C) | 8 (15.608 C) | 8 (15.608 C) | 8 (15.608 C) | 8 (15.608 C) |

Rate 1/2, $\mu = 24$:

| level $(\kappa, \ell)$ | $\log_2 n$ | $d + 1$ | Johnson: points, queries | $s = 12$ | $s = 16$ | $s = 24$ | $s = 32$ | $s = 48$ | $s = 64$ | $s = 96$ | $s = 128$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 (18, 6) | 19 | 262150 | 10, 217 | 217 (0.500 S) | 216 (0.500 S) | 216 (0.500 S) | 216 (0.500 S) | 216 (0.501 S) | 216 (0.501 S) | 216 (0.501 S) | 216 (0.502 S) |
| 1 (14, 4) | 18 | 16388 | 8, 55 | 54 (2.002 S) | 54 (2.004 S) | 54 (2.008 S) | 54 (2.011 S) | 54 (2.019 S) | 54 (2.027 S) | 53 (2.043 S) | 53 (2.059 S) |
| 2 (10, 4) | 17 | 1028 | 8, 31 | 31 (3.528 S) | 31 (3.556 S) | 30 (3.613 S) | 30 (3.674 S) | 29 (3.809 S) | 28 (3.963 S) | 25 (4.355 S) | 23 (4.905 S) |
| 3 (6, 4) | 16 | 68 | 7, 22 | 20 (5.484 S) | 18 (6.240 S) | 12 (9.492 C) | 11 (9.891 C) | 11 (9.891 C) | 11 (9.891 C) | 11 (9.891 C) | 11 (9.891 C) |
| 4 (2, 4) | 15 | 8 | 7, 18 | 10 (11.830 C) | 10 (11.830 C) | 10 (11.830 C) | 10 (11.830 C) | 10 (11.830 C) | 10 (11.830 C) | 10 (11.830 C) | 10 (11.830 C) |

Reading. (i) At every level of dimension $d + 1 \ge 4100$, no number of points that anyone would send moves the threshold off the Johnson radius: 128 points buy $0.002$ to $0.17$ bits a query, at most one query. The one query that the shortened bound does buy at such levels (217 to 216, 55 to 54) comes from the integer rounding of the query count, for 1 to 13 extra points. At dimension 1028 ($\mu = 24$, level 2), 128 points buy 1.4 bits (31 to 23 queries), which costs more bytes than it saves. (ii) At dimension 260 the counting-type bounds reach capacity with about 96 points, and 68 with 24 to 32. (iii) At dimension 8 to 36 they reach capacity with 10 to 22 points, and the queries are halved: $\log_2(n/A)$ goes from $R/2$ to nearly $R$. (iv) Unique decoding never helps: it needs the same points as Johnson to within one (the term $L^3 q^6/\Theta$ of row M0 does not vanish at $L = 1$) and more queries, 1.2 times as many at rate $1/2$ and $R/2$ times as many at low rates.

**When counting beats Johnson.** **[estimated, a rule fitted to the exact tables]** One more point pays for about $\lambda / 3 \approx 37$ bits of list ($\lambda = \log_2(1/\varepsilon)$), and just below the Johnson radius the shortened bound costs $j_0 \log_2(n/A)$ bits with $j_0 \approx 2\sqrt\rho\,\delta/(1-\sqrt\rho)^2$ for $\delta$ columns below the radius. This gives about $24000\,(1 - \sqrt\rho)^2 / (k R^3)$ queries saved per point near the radius, for a level of dimension $k = d + 1$ and rate $2^{-R}$, improving towards capacity. A point costs 2 to 5 scalars (32 to 80 bytes) and a later-level query 0.55 to 0.8 KiB, so the bound pays in bytes when $k R^3 \lesssim 2 \cdot 10^5$: dimension up to about 50 at $R = 16$, 90 at $R = 13$, 270 at $R = 9$. The exact search of section 2 agrees: counting is chosen at every level with $\kappa \le 7$ that occurs in the ladders of section 3 ($R$ between 9 and 16), and at no level with $\kappa \ge 8$.

## 2. Optimizing the DEEP-fold protocol under those bounds

### 2.1 The model

`scripts/67_model.py` evaluates the rows of Theorem 5.2 as exact integer inequalities with the paper's constants ($K_0 = 2^{g_f + 2} q$, $\tau = 2^{-(126 - g_f)}$, so that a fold message is $2^{-125}$ after a $g_f$-bit grind; $g_f = 7$ unless said), a point schedule per level (one batch, or the ladder that gives round $j$ the least count its prefix of row M0 allows), a query grind per level, any ladder, and for each level the choice among the Johnson threshold and every lower threshold with a bound of section 1 (one candidate per query count, up to 128 points). Bytes, Keccak counts and guest query cycles are note 08's cost model (`08_retuning/costs.py`, validated there against measured proofs of today's protocol) with the stream of Protocol D, as in note 11. Standing assumption (S2), $A_0 \ge d + 2$, is enforced. Status of what the model rests on: Theorem 5.2 is **proved** in the paper, and machine-checked for one batch per level in an abstract model; the composition for a ladder schedule is proved by hand only (the paper's status line). The byte and Keccak counts of the DEEP-fold stream are **exact in the model** of a protocol that is not implemented. Checks: the paper's table of points and its two ladders, note 08's 335.9 KiB for today, and the paper's 332.0 KiB for its instance at $\mu = 30$ (`selftest`; the model gives 332.0 with one batch, with 8 queries and 14 points at the last level where the paper prints 7 and 15, because the paper's instance takes $A_0 = d + 1$ there, outside (S2) as stated, and with 54 queries and 10 points at level 1 where the paper has 55 and 8, by the shortened bound).

Guest cost is counted in **cycle-equivalents** **[estimated]**: note 08's fitted cycles per query, plus 8 for each KECCAK step of the guest (Merkle paths with the deployed cap rule, and the transcript, which absorbs every point scalar), plus the points at note 11's count of field products (three a held point a round, the conversion and the terminal weight, or one evaluation of the final polynomial at the last level) at two cycles a product and 20 a point, the ratio note 08 fitted on the query path. A second column counts the points at one cycle a product and nothing else, a floor no guest can reach. Prover cost of the points **[estimated from measured kernels]**: note 24's units (a fused first batch of $s$ points $0.9 + 0.45 s$ OOD evaluations, a later point 0.37, the conversion 0.083 a point, later levels pro rata of their size), 0.34 percent of `Prove` a unit at rate $1/2$, net of today's OOD evaluations; this is 0.15 to 0.2 percent a level-0 point, the brief's figure.

### 2.2 The search

`scripts/67_search.py` (output in `scripts/67_search_output.txt`): every ladder with $2^{k_0}$ lanes at level 0, $k_0 \in \{4, 5, 6\}$, a domain reduction of 3 or 4 after it, later folds in $\{3, 4, 5\}$ (the last two levels also 2), later reductions 1 or 2 (the last also 0), leaves of at most 64 words, and a final polynomial of $2^{\kappa} + \ell$ coefficients with $\kappa \le k_0$ (today's rule `RESIDUAL_MAX_LOG <= INITIAL_FOLDING_FACTOR`), kept when its encoding is within C's budget against today (NTT work x1.05, Merkle permutations x1.15): 3130, 10519 and 18545 ladders at $\mu = 24, 28, 30$. Each is evaluated for the DEEP fold (levels chosen for bytes, and for cycle-equivalents) and for today's protocol with note 08's model, so that each protocol is compared at its own best ladder (T* below), with the deployed grinds and with A's (level-0 query grind $\max(17, \mu - 6)$). **[exact in the model]**

What comes out:

- **The level-0 knobs are the same for both protocols.** Every winner has 32 lanes and a reduction of 3, as C. The DEEP fold adds nothing there: level 0 has dimension $2^{18}$ to $2^{25}$ and sits on the Johnson radius whatever is spent (section 1.1). A's query grind is worth the same 2 queries a bit at rate $1/2$.
- **Freedom in the fold schedule is worth under one percent.** The DEEP fold's error rows do not depend on the level's size, so any ladder is admitted, where today's analysis has an interpolation floor at small levels (note 08, section 7.3). The best DEEP ladders differ from C's only in the last two levels (a last fold of 5 or 3, sometimes one level fewer), and beat the DEEP fold on C's own ladder by 0.0 to 1.1 percent of the opening. Today's protocol gains as much from the same freedom: its best ladder T* is 0.1 to 1.5 percent below C.
- **The final polynomial.** With counting at the last level a query there is cheap, and the search prefers a last level of dimension 11 to 37. Lifting the cap on the final polynomial to $\kappa = 6$ gives 212.9 KiB against 215.9 at $\mu = 24$, rate $1/2$ (`67_search_output_24_free.txt`), and gives today's protocol 220.5 against 223.1: the same 3 KiB for both.

### 2.3 Where the proven gain comes from

**[exact in the model]** (`scripts/67_whatif.py`, part 1.) On C's ladder with A's level-0 grind, queries per level and the opening against C:

| $\mu$, rate | C (today's analysis) | DEEP, Johnson only | DEEP, Johnson and counting | DEEP, all bounds of section 1 |
| --- | --- | --- | --- | --- |
| 24, 1/2 | 215 73 37 25 20 | 215 73 37 25 19, +0.9% | 215 73 37 13 10, -3.0% | 214 72 36 13 10, -3.6% |
| 24, 1/4 | 108 55 32 23 19 | 108 55 31 22 18, +0.6% | 108 55 31 11 9, -4.8% | 107 54 31 11 9, -5.5% |
| 28, 1/2 | 207 73 37 25 19 16 | 207 73 37 25 19 15, +0.9% | 207 73 37 25 10 8, -1.7% | 206 72 36 24 10 8, -2.5% |
| 28, 1/4 | 104 55 32 22 18 15 | 104 55 31 22 17 14, +0.6% | 104 55 31 22 9 8, -2.6% | 103 54 31 22 9 8, -3.2% |
| 30, 1/2 | 203 73 37 25 19 16 | 203 73 37 25 19 15, +0.9% | 203 73 37 25 19 8, -0.4% | 202 72 36 24 18 8, -1.5% |
| 30, 1/4 | 102 55 32 22 18 15 | 102 55 31 22 17 14, +0.5% | 102 55 31 22 17 7, -1.4% | 101 54 31 22 17 7, -2.0% |

1. **No list or correlated-agreement factor in the fold error: 0 or 1 query a level, 1 to 3 an opening.** Today's analysis, with A's list grinds, is already within one query of the Johnson limit at every level and exactly on it at level 0 (the table; note 08, section 7.1, has the same for the deployed grinds). Removing the slack saves one query on the last one to three levels and nothing on level 0. The points that buy this (39 to 49 of them, 174 to 216 scalars on the ladder schedule, 2.7 to 3.4 KiB) cost more than the queries saved: at Johnson thresholds alone the DEEP fold is 0.5 to 0.9 percent larger than C. This confirms the paper's sentence that its Corollary 5.3 "changes the proof and not the cost".
2. **Counting at the last levels: 7 to 12 queries on each level of dimension at most 132.** At $\mu = 30$ that is one level (16 to 8, or 15 to 7 queries), at $\mu = 24$ and 28 two (25 and 20 to 13 and 10; 19 and 16 to 10 and 8), since a ladder whose size is 0 modulo 4 ends on dimensions 132 and 12 where $\mu = 30$ ends on 516 and 36. This is the whole gain of the paper's own instance, and it is why the gain is largest at $\mu = 24$ and 28 and at low rates, where the last levels are a larger share of the opening.
3. **The shortened Johnson bound: one more query on two to five levels**, for at most 3 more points each, 0.6 to 1.1 percent of the opening. It is the only new mathematics in this note and it is small.

### 2.4 The DEEP-only knobs

**[exact in the model]** ($\mu = 30$, rate $1/2$, C's ladder; `67_whatif.py`, last table.)

| knob | effect |
| --- | --- |
| ladder schedule instead of one batch | 314 scalars instead of 357 for the same points 12 11 9 9 8 20: 0.7 KiB, 0.2 percent |
| fold grind 12 or 17 bits instead of 7 (smaller $\tau^{-1}$ and $q^6/\Theta$ in row M0) | 3 fewer points, 12 to 15 scalars: under 0.1 percent |
| point grind 20 bits instead of 15 | 1 point, 3 scalars |
| points beyond the theorem's minimum at a level (to lower its threshold) | section 1.1: pays only at dimension below about 150 |
| per-round loss $A^{(i,j)} = A_i - (\ell_i - j)$ | forced by the class trichotomy lemma of the paper's section 4.4 (one column a round); at most one query on the last level, as today |
| batching grind 7 bits instead of 13 or 14 | $2^{13}$ permutations saved out of $2^{20}$ to $2^{24}$: nothing |

None of these moves the opening by half a percent. The DEEP fold's protocol-level freedom is real but has nothing large to act on while level 0 stays at the Johnson radius: level 0 is a half to two thirds of the bytes and its queries are untouched.

## 3. Comparison

`scripts/67_compare.py`, output in `scripts/67_compare_output.txt`. Full stacks. Rows:

- **today**, **A**, **B**, **C**: today's protocol at the deployed constants and at note 08's three configurations (**proven**, Annex B; numbers **exact in the model** of note 08, which is validated against the Rust search and measured proofs).
- **T\***: today's protocol on its best ladder of the search of section 2.2, with A's grinds (**proven**; the ladder is written as folds/reductions, so `54443/3111` is 32 lanes, then folds of 4, 4, 4, 3, with domain reductions 3, 1, 1, 1).
- **P**: the paper's DEEP-fold instance as printed (section 7.2, "with no new theorem"): deployed ladder and grinds, one batch, Johnson everywhere but counting where it gives fewer bytes. Reproduced with the script that made the paper's table (`11_deep_fold_whir.py`).
- **D0**: the same ladder and grinds with this note's bounds and the ladder schedule.
- **D+C**: the DEEP fold with the knobs of C that apply: 32 lanes, A's level-0 query grind, C's ladder. (A's batching and OOD grinds have no counterpart: the DEEP fold has no list term outside row M0.)
- **D\***, **Dc**: the DEEP fold on its best ladder for bytes, and for guest cycle-equivalents, with A's level-0 grind.

All DEEP rows are **proven** in the sense of section 2.1 (Theorem 5.2 with the list bounds of Proposition 1.2) and **exact in the model** for a protocol that is not implemented. Guest cycle-equivalents and the prover's share for the points are **estimated** as in section 2.1. Prover columns: NTT work and Merkle permutations against today, expected grinding permutations of the opening ($\log_2$), and the points' share of `Prove`.

**$\mu = 24$, rate 1/2** (percentages: against today / against C)

| configuration | queries per level | points per level | opening, KiB | guest Keccak | guest cycle-eq | same, point floor | prover: NTT, Merkle, grind ($\log_2$ perms), points |
| --- | --- | --- | --- | --- | --- | --- | --- |
| today | 218 55 32 23 20 | 1 OOD each | 260.4 (+0.0% / +15.8%) | 5748 | 181.4k (+0.0% / +15.1%) | 181.4k (+15.1% C) | x1.00, x1.00, 19.66, +0.0% |
| A | 215 55 32 23 | 1 OOD each | 247.4 (-5.0% / +10.0%) | 5408 | 176.8k (-2.6% / +12.2%) | 176.8k (+12.2% C) | x0.98, x0.98, 19.84, +0.0% |
| B | 218 73 37 25 20 | 1 OOD each | 226.6 (-13.0% / +0.8%) | 5778 | 159.0k (-12.4% / +0.9%) | 159.0k (+0.9% C) | x1.04, x1.13, 19.66, +0.0% |
| C | 215 73 37 25 20 | 1 OOD each | 224.9 (-13.6% / +0.0%) | 5734 | 157.6k (-13.1% / +0.0%) | 157.6k (+0.0% C) | x1.04, x1.13, 20.11, +0.0% |
| T* 54443/3111 | 215 73 37 25 20 | 1 OOD each | 223.1 (-14.3% / -0.8%) | 5720 | 157.0k (-13.5% / -0.4%) | 157.0k (-0.4% C) | x1.04, x1.14, 20.11, +0.0% |
| P (paper) | 217 55 31 11 10 | 10 8 8 26 9 | 252.1 (-3.2% / +12.1%) | 5530 | 184.5k (+1.7% / +17.1%) | 178.8k (+13.4% C) | x1.00, x1.00, 19.65, +1.9% |
| D0 | 216 54 31 11 10 | 13 9 8 26 9 | 250.5 (-3.8% / +11.4%) | 5499 | 184.3k (+1.6% / +17.0%) | 178.1k (+13.0% C) | x1.00, x1.00, 19.65, +2.3% |
| D+C | 214 72 36 13 10 | 12 9 8 37 11 | 216.9 (-16.7% / -3.6%) | 5537 | 163.6k (-9.9% / +3.8%) | 156.1k (-0.9% C) | x1.04, x1.13, 19.86, +2.4% |
| D* 54443/3111 | 214 72 36 13 10 | 12 9 8 37 11 | 215.9 (-17.1% / -4.0%) | 5530 | 163.6k (-9.8% / +3.8%) | 156.0k (-1.0% C) | x1.04, x1.14, 19.86, +2.4% |
| Dc 54453/3111 | 215 72 36 13 9 | 9 9 8 24 10 | 217.8 (-16.4% / -3.2%) | 5502 | 161.0k (-11.3% / +2.2%) | 155.2k (-1.5% C) | x1.04, x1.13, 19.86, +1.8% |

**$\mu = 24$, rate 1/4** (percentages: against today / against C)

| configuration | queries per level | points per level | opening, KiB | guest Keccak | guest cycle-eq | same, point floor | prover: NTT, Merkle, grind ($\log_2$ perms), points |
| --- | --- | --- | --- | --- | --- | --- | --- |
| today | 109 44 28 21 18 | 1 OOD each | 169.9 (+0.0% / +8.9%) | 4318 | 115.2k (+0.0% / +9.3%) | 115.2k (+9.3% C) | x1.00, x1.00, 19.66, +0.0% |
| A | 108 44 28 21 | 1 OOD each | 158.9 (-6.5% / +1.8%) | 4025 | 112.0k (-2.8% / +6.2%) | 112.0k (+6.2% C) | x0.98, x0.98, 19.84, +0.0% |
| B | 109 55 32 23 19 | 1 OOD each | 156.7 (-7.8% / +0.4%) | 4373 | 106.0k (-8.0% / +0.5%) | 106.0k (+0.5% C) | x1.04, x1.13, 19.66, +0.0% |
| C | 108 55 32 23 19 | 1 OOD each | 156.1 (-8.1% / +0.0%) | 4352 | 105.4k (-8.5% / +0.0%) | 105.4k (+0.0% C) | x1.04, x1.13, 20.11, +0.0% |
| T* 54443/3111 | 108 55 32 23 18 | 1 OOD each | 153.9 (-9.4% / -1.4%) | 4330 | 104.5k (-9.3% / -0.8%) | 104.5k (-0.8% C) | x1.04, x1.14, 20.11, +0.0% |
| P (paper) | 109 44 28 10 9 | 10 8 8 28 10 | 163.6 (-3.7% / +4.8%) | 4163 | 120.3k (+4.4% / +14.1%) | 114.3k (+8.4% C) | x1.00, x1.00, 19.65, +1.5% |
| D0 | 108 44 27 10 9 | 12 8 8 28 10 | 161.8 (-4.8% / +3.6%) | 4118 | 119.5k (+3.8% / +13.4%) | 113.4k (+7.6% C) | x1.00, x1.00, 19.65, +1.7% |
| D+C | 107 54 31 11 9 | 11 9 8 43 11 | 147.6 (-13.1% / -5.5%) | 4159 | 112.0k (-2.8% / +6.2%) | 104.2k (-1.1% C) | x1.04, x1.13, 19.86, +1.7% |
| D* 54443/3111 | 107 54 31 11 9 | 11 9 8 43 12 | 146.8 (-13.6% / -6.0%) | 4157 | 112.2k (-2.6% / +6.5%) | 104.2k (-1.1% C) | x1.04, x1.14, 19.86, +1.7% |
| Dc 5555/310 | 108 54 27 9 | 9 10 9 15 | 156.3 (-8.0% / +0.1%) | 3950 | 108.9k (-5.5% / +3.3%) | 104.2k (-1.2% C) | x1.04, x1.09, 19.59, +1.5% |

**$\mu = 28$, rate 1/2** (percentages: against today / against C)

| configuration | queries per level | points per level | opening, KiB | guest Keccak | guest cycle-eq | same, point floor | prover: NTT, Merkle, grind ($\log_2$ perms), points |
| --- | --- | --- | --- | --- | --- | --- | --- |
| today | 218 55 32 23 18 16 | 1 OOD each | 313.7 (+0.0% / +13.6%) | 7883 | 218.4k (+0.0% / +13.7%) | 218.4k (+13.7% C) | x1.00, x1.00, 19.92, +0.0% |
| A | 207 55 32 22 18 | 1 OOD each | 293.0 (-6.6% / +6.1%) | 7354 | 207.5k (-5.0% / +8.0%) | 207.5k (+8.0% C) | x0.99, x0.99, 22.27, +0.0% |
| B | 218 73 37 25 19 16 | 1 OOD each | 283.7 (-9.6% / +2.7%) | 8005 | 198.3k (-9.2% / +3.2%) | 198.3k (+3.2% C) | x1.03, x1.13, 19.92, +0.0% |
| C | 207 73 37 25 19 16 | 1 OOD each | 276.1 (-12.0% / +0.0%) | 7783 | 192.1k (-12.0% / +0.0%) | 192.1k (+0.0% C) | x1.03, x1.13, 22.33, +0.0% |
| T* 544433/31111 | 207 73 37 25 19 17 | 1 OOD each | 273.6 (-12.8% / -0.9%) | 7839 | 192.8k (-11.7% / +0.4%) | 192.8k (+0.4% C) | x1.03, x1.14, 22.33, +0.0% |
| P (paper) | 217 55 31 22 9 8 | 11 8 8 8 28 10 | 306.4 (-2.3% / +11.0%) | 7687 | 225.5k (+3.3% / +17.4%) | 218.0k (+13.5% C) | x1.00, x1.00, 19.91, +2.1% |
| D0 | 216 54 31 22 9 8 | 15 9 8 8 28 10 | 304.7 (-2.9% / +10.4%) | 7648 | 225.6k (+3.3% / +17.4%) | 217.5k (+13.2% C) | x1.00, x1.00, 19.91, +2.7% |
| D+C | 206 72 36 24 10 8 | 12 9 9 8 44 11 | 269.2 (-14.2% / -2.5%) | 7613 | 202.9k (-7.1% / +5.6%) | 193.3k (+0.6% C) | x1.03, x1.13, 22.27, +2.4% |
| D* 54455/3110 | 206 72 36 24 8 | 12 9 9 9 22 | 267.7 (-14.7% / -3.0%) | 7325 | 198.5k (-9.1% / +3.3%) | 190.5k (-0.8% C) | x1.04, x1.12, 22.22, +2.4% |
| Dc 54555/3110 | 207 72 36 22 8 | 10 9 10 9 15 | 273.6 (-12.8% / -0.9%) | 7348 | 197.5k (-9.6% / +2.8%) | 191.1k (-0.5% C) | x1.03, x1.11, 22.22, +2.0% |

**$\mu = 28$, rate 1/4** (percentages: against today / against C)

| configuration | queries per level | points per level | opening, KiB | guest Keccak | guest cycle-eq | same, point floor | prover: NTT, Merkle, grind ($\log_2$ perms), points |
| --- | --- | --- | --- | --- | --- | --- | --- |
| today | 109 44 28 21 17 15 | 1 OOD each | 207.7 (+0.0% / +8.0%) | 5213 | 133.4k (+0.0% / +8.4%) | 133.4k (+8.4% C) | x1.00, x1.00, 19.92, +0.0% |
| A | 104 44 28 21 17 | 1 OOD each | 193.0 (-7.1% / +0.3%) | 4839 | 127.4k (-4.6% / +3.5%) | 127.4k (+3.5% C) | x0.99, x0.99, 22.27, +0.0% |
| B | 109 55 32 23 18 15 | 1 OOD each | 196.8 (-5.3% / +2.3%) | 5414 | 126.3k (-5.3% / +2.6%) | 126.3k (+2.6% C) | x1.03, x1.13, 19.92, +0.0% |
| C | 104 55 32 22 18 15 | 1 OOD each | 192.3 (-7.4% / +0.0%) | 5292 | 123.1k (-7.7% / +0.0%) | 123.1k (+0.0% C) | x1.03, x1.13, 22.33, +0.0% |
| T* 54455/3110 | 104 55 32 22 16 | 1 OOD each | 189.4 (-8.8% / -1.5%) | 5054 | 121.7k (-8.8% / -1.1%) | 121.7k (-1.1% C) | x1.04, x1.12, 22.27, +0.0% |
| P (paper) | 109 44 28 20 8 7 | 11 8 8 8 31 11 | 201.7 (-2.9% / +4.9%) | 5025 | 141.7k (+6.2% / +15.1%) | 134.0k (+8.8% C) | x1.00, x1.00, 19.91, +1.6% |
| D0 | 108 44 27 20 8 8 | 14 8 9 8 31 10 | 200.3 (-3.6% / +4.2%) | 5001 | 141.7k (+6.2% / +15.2%) | 133.6k (+8.5% C) | x1.00, x1.00, 19.91, +2.0% |
| D+C | 103 54 31 22 9 8 | 11 9 8 8 48 11 | 186.1 (-10.4% / -3.2%) | 5124 | 134.2k (+0.6% / +9.0%) | 124.6k (+1.3% C) | x1.03, x1.13, 22.27, +1.7% |
| D* 54455/3111 | 103 54 31 22 8 | 11 9 8 9 22 | 184.0 (-11.4% / -4.3%) | 4885 | 130.1k (-2.5% / +5.7%) | 122.3k (-0.6% C) | x1.02, x1.10, 22.22, +1.7% |
| Dc 55545/3111 | 103 54 27 18 8 | 11 10 10 8 15 | 190.7 (-8.2% / -0.8%) | 4802 | 128.4k (-3.8% / +4.3%) | 121.9k (-0.9% C) | x1.01, x1.06, 22.22, +1.7% |

**$\mu = 30$, rate 1/2** (percentages: against today / against C)

| configuration | queries per level | points per level | opening, KiB | guest Keccak | guest cycle-eq | same, point floor | prover: NTT, Merkle, grind ($\log_2$ perms), points |
| --- | --- | --- | --- | --- | --- | --- | --- |
| today | 218 55 32 23 18 15 | 1 OOD each | 335.9 (+0.0% / +13.1%) | 8173 | 226.9k (+0.0% / +13.4%) | 226.9k (+13.4% C) | x1.00, x1.00, 19.92, +0.0% |
| A | 203 55 32 22 18 15 | 1 OOD each | 320.6 (-4.6% / +7.9%) | 7820 | 215.5k (-5.0% / +7.7%) | 215.5k (+7.7% C) | x1.00, x1.00, 24.09, +0.0% |
| B | 218 73 37 25 19 16 | 1 OOD each | 308.3 (-8.2% / +3.8%) | 8409 | 208.9k (-7.9% / +4.4%) | 208.9k (+4.4% C) | x1.03, x1.13, 19.92, +0.0% |
| C | 203 73 37 25 19 16 | 1 OOD each | 297.1 (-11.6% / +0.0%) | 8101 | 200.1k (-11.8% / +0.0%) | 200.1k (+0.0% C) | x1.03, x1.13, 24.09, +0.0% |
| T* 544444/31110 | 203 73 37 25 19 15 | 1 OOD each | 296.8 (-11.6% / -0.1%) | 8085 | 199.7k (-12.0% / -0.2%) | 199.7k (-0.2% C) | x1.04, x1.14, 24.09, +0.0% |
| P (paper) | 217 55 31 22 17 7 | 11 8 8 8 8 15 | 332.0 (-1.2% / +11.7%) | 8005 | 234.7k (+3.5% / +17.3%) | 227.7k (+13.8% C) | x1.00, x1.00, 19.91, +2.1% |
| D0 | 217 54 31 22 17 8 | 11 10 8 8 8 14 | 331.3 (-1.4% / +11.5%) | 7992 | 234.7k (+3.4% / +17.3%) | 227.6k (+13.7% C) | x1.00, x1.00, 19.91, +2.0% |
| D+C | 202 72 36 24 18 8 | 12 11 9 9 8 20 | 292.7 (-12.9% / -1.5%) | 7930 | 211.3k (-6.8% / +5.6%) | 202.2k (+1.1% C) | x1.03, x1.13, 24.07, +2.5% |
| D* 544444/31110 | 202 72 36 24 18 7 | 12 11 9 9 8 22 | 292.3 (-13.0% / -1.6%) | 7918 | 211.3k (-6.8% / +5.6%) | 202.0k (+0.9% C) | x1.04, x1.14, 24.07, +2.5% |
| Dc 544445/31111 | 203 73 36 24 18 8 | 10 8 9 9 8 15 | 295.1 (-12.1% / -0.6%) | 7936 | 208.8k (-8.0% / +4.3%) | 201.5k (+0.7% C) | x1.03, x1.12, 24.07, +2.0% |

**$\mu = 30$, rate 1/4** (percentages: against today / against C)

| configuration | queries per level | points per level | opening, KiB | guest Keccak | guest cycle-eq | same, point floor | prover: NTT, Merkle, grind ($\log_2$ perms), points |
| --- | --- | --- | --- | --- | --- | --- | --- |
| today | 109 44 28 21 17 15 | 1 OOD each | 222.6 (+0.0% / +7.8%) | 6000 | 146.3k (+0.0% / +8.7%) | 146.3k (+8.7% C) | x1.00, x1.00, 19.92, +0.0% |
| A | 102 44 28 21 17 15 | 1 OOD each | 215.4 (-3.3% / +4.3%) | 5802 | 140.7k (-3.8% / +4.5%) | 140.7k (+4.5% C) | x1.00, x1.00, 24.09, +0.0% |
| B | 109 55 32 23 18 15 | 1 OOD each | 213.0 (-4.3% / +3.1%) | 6166 | 139.6k (-4.6% / +3.7%) | 139.6k (+3.7% C) | x1.03, x1.13, 19.92, +0.0% |
| C | 102 55 32 22 18 15 | 1 OOD each | 206.5 (-7.2% / +0.0%) | 5961 | 134.6k (-8.0% / +0.0%) | 134.6k (+0.0% C) | x1.03, x1.13, 24.09, +0.0% |
| T* 544444/31110 | 102 55 32 22 18 14 | 1 OOD each | 206.2 (-7.4% / -0.1%) | 5948 | 134.2k (-8.3% / -0.3%) | 134.2k (-0.3% C) | x1.04, x1.14, 24.09, +0.0% |
| P (paper) | 109 44 28 20 16 7 | 11 8 8 8 8 15 | 220.0 (-1.2% / +6.6%) | 5872 | 155.3k (+6.1% / +15.4%) | 148.3k (+10.1% C) | x1.00, x1.00, 19.91, +1.6% |
| D0 | 109 44 27 20 16 7 | 11 8 9 8 8 15 | 218.6 (-1.8% / +5.8%) | 5841 | 154.7k (+5.7% / +14.9%) | 147.7k (+9.7% C) | x1.00, x1.00, 19.91, +1.5% |
| D+C | 101 54 31 22 17 7 | 12 11 8 8 8 22 | 202.3 (-9.1% / -2.0%) | 5800 | 146.1k (-0.1% / +8.5%) | 137.0k (+1.8% C) | x1.03, x1.13, 24.07, +1.9% |
| D* 544444/31111 | 101 54 31 22 17 7 | 12 11 8 8 8 22 | 202.3 (-9.1% / -2.0%) | 5800 | 146.1k (-0.1% / +8.5%) | 137.0k (+1.8% C) | x1.03, x1.13, 24.07, +1.9% |
| Dc 545445/31111 | 102 55 31 20 16 7 | 10 8 9 8 8 13 | 209.0 (-6.1% / +1.2%) | 5799 | 143.5k (-1.9% / +6.6%) | 137.0k (+1.7% C) | x1.02, x1.11, 24.07, +1.5% |

### 3.1 Reading the tables

Against C, the best proven DEEP-fold configurations (**exact in the model** for bytes and Keccak, **estimated** for cycles and prover share):

| $\mu$, rate | D\*: opening | D\*: guest cycle-eq (point floor) | Dc: opening | Dc: guest cycle-eq (point floor) | T\*: opening, cycle-eq | points, share of `Prove` |
| --- | --- | --- | --- | --- | --- | --- |
| 24, 1/2 | -4.0% | +3.8% (-1.0%) | -3.2% | +2.2% (-1.5%) | -0.8%, -0.4% | +1.8 to +2.4% |
| 24, 1/4 | -6.0% | +6.5% (-1.1%) | +0.1% | +3.3% (-1.2%) | -1.4%, -0.8% | +1.5 to +1.7% |
| 28, 1/2 | -3.0% | +3.3% (-0.8%) | -0.9% | +2.8% (-0.5%) | -0.9%, +0.4% | +2.0 to +2.4% |
| 28, 1/4 | -4.3% | +5.7% (-0.6%) | -0.8% | +4.3% (-0.9%) | -1.5%, -1.1% | +1.7% |
| 30, 1/2 | -1.6% | +5.6% (+0.9%) | -0.6% | +4.3% (+0.7%) | -0.1%, -0.2% | +2.0 to +2.5% |
| 30, 1/4 | -2.0% | +8.5% (+1.8%) | +1.2% | +6.6% (+1.7%) | -0.1%, -0.3% | +1.5 to +1.9% |

1. **Proof size.** With proven bounds only, the DEEP fold on its best ladder is 1.6 to 6.0 percent smaller than C (4 to 9 KiB), and 1.5 to 4.6 percent smaller than today's protocol on its own best ladder T\*. The gain is largest at small commitments and at rate $1/4$, and it comes from the last one or two levels (section 2.3). Without C's knobs the DEEP fold is far behind C: the paper's instance P is 4.8 to 12.1 percent larger than C, and D0 3.6 to 11.5 percent. So the comparison that matters is D+C against C, and the DEEP fold adds 1.5 to 5.5 percent to what C already gives.
2. **Recursive verifier.** It gets slower, not faster. The opening has 12 to 31 fewer queries, nearly all on small late levels (roughly 200 cycles and 15 to 20 KECCAK steps each), and 43 to 83 points, each of which is 40 to 160 field products in the guest, plus 200 to 450 more scalars through the transcript. At the fitted two cycles a product the guest's cycle-equivalents for the opening rise by 3.3 to 8.5 percent against C at the byte-optimal configuration, and by 2.2 to 6.6 percent when the levels and the ladder are chosen for the guest. At the unreachable floor of one cycle a product and nothing else the two protocols tie, within $-1.5$ and $+1.8$ percent. The Keccak count alone falls by 2 to 8 percent.
3. **Prover.** The points add 1.5 to 2.5 percent of `Prove` on top of C's cost (central estimate from note 24's measured kernels, whose own range is a factor of two either way). The same time spent by C on one more bit of level-0 query grind buys 2 queries at rate $1/2$ and 1 at rate $1/4$: $-0.5$ and $-0.4$ percent of the opening, and $-0.6$ and $-0.5$ percent of guest cycle-equivalents (**exact in the model**; the grind of $2^{\mu - 6}$ permutations is about 1.5 percent of `Prove`, note 08's **estimate**). At equal prover time the DEEP fold's byte advantage over C is therefore 1 to 5.5 percent and its guest penalty 3 to 9 percent.

**Verdict of the comparison.** The DEEP fold with proven bounds is not a practical improvement over configuration C. It trades 1.6 to 6 percent of the opening for a recursive verifier that is 2 to 9 percent slower on the opening and a prover that is about 2 percent slower, and the user's requirement is a smaller proof with a recursive verifier that is not slower at equal or lower prover time. No DEEP-fold configuration in the search meets all three against C.

## 4. What single proven result would change the verdict

Everything in this section is **hypothetical**: each row assumes a statement nobody has proved, and prices it with the same model (`scripts/67_whatif.py`, part 2; C's ladder, A's level-0 grind; opening and guest cycle-equivalents against C).

| assumed result | 24, 1/2 | 24, 1/4 | 28, 1/2 | 28, 1/4 | 30, 1/2 | 30, 1/4 |
| --- | --- | --- | --- | --- | --- | --- |
| none (proven, D+C) | -3.6%, +3.8% | -5.5%, +6.2% | -2.5%, +5.6% | -3.2%, +9.0% | -1.5%, +5.6% | -2.0%, +8.5% |
| (a) a fold lemma at the floor of the paper's state function: $s = 1 + \lceil (110 + 2 \log_2 L)/\lambda \rceil$ points, 3 or 4 at a Johnson level instead of 8 to 12 | -4.7%, -1.4% | -7.2%, -1.6% | -3.7%, +0.1% | -4.9%, +0.8% | -2.4%, +0.1% | -3.3%, +0.6% |
| (b) a counting bound with a quarter of the exponent, $L \le (\binom{n}{d+1}/\binom{A}{d+1})^{1/4}$ | -5.3%, +8.8% | -7.2%, +15.2% | -2.5%, +3.3% | -3.9%, +4.8% | -1.9%, +6.1% | -3.3%, +9.5% |
| (b') the same with an eighth | -7.0%, +2.6% | -9.8%, +6.0% | -3.9%, +6.7% | -5.3%, +12.5% | -2.4%, +4.3% | -4.1%, +6.3% |
| (a) and (b), levels chosen for the guest | -4.6%, -2.7% | -7.5%, -4.2% | -3.3%, -0.9% | -5.1%, -1.9% | -1.4%, +0.0% | -2.8%, -0.4% |
| (c) a list of $2^{40}$ at level 0 at agreement $0.66\,n$ (rate $1/2$) or $7n/16$ (rate $1/4$), the paper's rows | -12.5%, -6.9% | -12.4%, -2.6% | -11.1%, -4.6% | -9.5%, +1.6% | -9.9%, -4.2% | -8.4%, +0.6% |

1. **Only a list bound at level 0 changes the verdict.** Result (c) puts the opening 8 to 12.5 percent below C and, at rate $1/2$, the guest 4 to 7 percent below C, with everything else as proven today. It is the result the night's research could not reach on leanVM's domain, and the list may be as large as $2^{100}$ at the cost of two more points. At rate $1/4$ the threshold $7n/16$ is not low enough to pay for the points in the guest; the next dyadic step, $3n/8$ (72 to 76 level-0 queries), would be: 14 to 18 percent of the opening and 5 to 10 percent of guest cycle-equivalents below C. At rate $1/2$ a bound at $0.64\,n$ gives 13 to 15.5 percent and 8 to 10 percent.
2. **A list bound for the small codes of the last levels does not.** The codes in question are the Reed-Solomon codes of dimension 132 to 2052 at rates $2^{-6}$ to $2^{-12}$ (the one or two levels before the last). Even a counting bound sharper by a factor of four or eight in the exponent, which nothing known gives, is worth 2 to 10 percent of the opening, 2 to 4 percent at $\mu = 28$ and 30 and rate $1/2$, and it makes the guest slower still, because the lists it leaves are paid in points (44 to 99 at one level). The shortened Johnson bound of Proposition 1.2 is the sharpening that the distance alone gives, and section 1.1 shows how little it moves.
3. **A sharper fold lemma repairs the guest and little else.** If the points could be brought to the floor of the paper's state function (its section 7.4: three points where the theorem has eleven; the paper says the triple count and the discount of the potential are where the loss is), the DEEP fold at proven list bounds would tie C in the guest and keep its 2.4 to 7 percent in bytes. That is a proof about the protocol, not about the code, so it is not blocked by the list problem; but the paper's own floor argument shows that this state function cannot go below it, and no proof at the floor exists. At Johnson thresholds the affine correlated-agreement theorem of Annex B may be usable as an input (the paper's remark that a weak correlated-agreement bound removes the factor $q^3$ is conjectural only below the Johnson radius), which would give about 9, 7, 6, 6, 6 points by the paper's count; that refinement is not written, and by row (a) even its limit is a tie.

So the answer to the brief's question 4: the one result that would make the DEEP fold worth adopting is the paper's hypothesis $\mathrm{HK}$ (its list problem, section 6.1) at level 0, for instance every $K$-valued word on the level-0 domain at rate $1/2$ having at most $2^{39}$ polynomials of degree at most $2^\kappa - 1 + \ell$ at agreement $0.66\,n$ (the interleaving reductions, which are machine-checked, then give $2^{40}$ for all lanes). Nothing about the last levels, and no sharper counting, comes close.

## 5. What adoption would cost

**[estimated, from reading the paper and `AGENTS.md`; nothing was built]** Protocol D is specified in the paper and implemented nowhere in `crates/` or `formal/`. Adopting it is a protocol change, which by the repository's rule lands in both provers, the three verifiers and `formal/` together:

- **Both provers.** The commitment answers $s_0$ points in place of one multilinear OOD value (a fused pass over the stack that must return the per-lane evaluations, note 24); each fold round sends $4 + \bar s_j$ scalars; each level boundary answers the next level's points on $E$-valued lanes and converts the old ones into weights (dense tensors over $2^\kappa$ coefficients, note 24 item 6). The outer protocol changes too: today the OOD claim joins the claims to be opened, in Protocol D the point claims are carried and never batched.
- **Three verifiers.** The carried update of the paper's protocol each round (one squaring and two products a held point), the conversion at each boundary, the evaluation of the final polynomial at every point of the last level, and the terminal weight with one more term a point. In the guest this is new code on every opening arm, for every stack size and rate it admits.
- **Formal.** `formal/` proves knowledge soundness of today's verifier. The paper's Lean development (`doc/deep_fold/lean`) proves the round-by-round statement for an abstract model with one batch per level; by the paper's own list it does not cover the ladder schedule's composition, the identities that make the real encoder an instance of the model, completeness, Fiat-Shamir with grinding, Merkle commitments, or the outer protocol, and its instances without a list hypothesis are in the unique-decoding range. The Johnson bound, the counting bound and Proposition 1.2 would have to be connected to it. The statement in `formal/Statement/` and its differential tests would be rewritten.
- **The documents.** Annex B, the query tables, the wire format and the sidecar's and bindings' proof handling.

Configuration C, by comparison, is three grind constants and the lane count of level 0. The lane count is also a change in both provers, the three verifiers and `formal/` (note 08), but inside the existing protocol and its existing proof. T\* is C with another ladder.

## 6. Limits of this note

- The DEEP-fold numbers are outputs of a parameter model of an unimplemented protocol. The model's shared parts (ladder, Merkle bytes, sponge, guest query cycles) are note 08's, validated there; the DEEP stream is note 11's accounting with schedules added, and it reproduces the paper's 332.0 KiB.
- Guest cycles of a point are **estimated** from a product count at two cycles a product and are the least certain input; the verdict on the guest was therefore also computed at a floor of one cycle a product, where the protocols tie and the DEEP fold still does not win.
- The prover's share for the points is note 24's central value, whose stated range is 1.0 to 3.3 percent for twelve level-0 points; C's encoding cost is note 08's (NTT work x1.03 to x1.05, Merkle permutations x1.13).
- The search covers ladders within C's encoding budget, lanes 16 to 64 at level 0, later folds 2 to 5, and a final polynomial capped as today. Ladders with more encoding, other level-0 rates and partly filled stacks were not searched; on a partly filled stack every 32-lane configuration loses part of its byte advantage over today (note 08), the DEEP rows and C alike.
- Ladder schedules are covered by the paper's hand proof of Theorem 5.2 and not by its Lean composition. With one batch the DEEP rows grow by 0.2 percent.
- Proposition 1.2, item 4, was not machine-checked. It is two double counts, and `67_model.py` checks on small cases that it never exceeds the counting bound.
- Not done: a search with the fold and point grinds as free knobs (section 2.4 bounds their effect at 0.1 percent), rates $1/8$ and $1/16$ in the comparison (section 1.1 has their thresholds; the pattern is the same, with a larger share for the last levels), and any implementation.

## 7. Reproducing

All under `doc/whir_soundness_gap_notes/scripts/`, standard library only, four cores.

| script | what it does | time |
| --- | --- | --- |
| `67_model.py` | the model; run alone it is the self-test | 1 s |
| `67_bounds.py [mu ...]` | section 1.1 (`67_bounds_output.txt`) | 10 s |
| `67_search.py [--free-residual] [mu ...]` | section 2.2 (`67_search_output.txt`, `67_search_output_24_free.txt`) | 15 s at $\mu = 24$, one to two minutes each at 28 and 30 |
| `67_compare.py` | section 3 (`67_compare_output.txt`) | 3 s |
| `67_whatif.py` | sections 2.3, 2.4 and 4 (`67_whatif_output.txt`) | 2 s |
