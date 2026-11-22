# 69. Random tree codes: experiments and attacks

Researcher 69, round 15, 2026-11-21. Object: the random tree code of note 68, Section 3. Status tags: **proved** (argument written here, not refereed), **exact at the stated size** (exhaustive or exact linear algebra at that size), **measured** (random sampling or search, sizes stated), **estimated**, **conjectured**. Scripts are `scripts/69_*`; each prints the numbers quoted here and their outputs are saved next to them.

## 0. Summary

**Yes: I found a structural deficiency, and it is an attack on the target theorem, not a small-field accident.** The generic tree code (T1 or T2, twiddles fully generic, GF($2^{64}$)) is MDS but not higher-order MDS, from the smallest size on ($k = 4$, $n = 8$, three codewords, weight 8 against the generalized Singleton 7), while Reed-Solomon at random points matches a uniformly random matrix on every one of the 57 million patterns scanned exhaustively ((4,8) with three and four members, (8,16) and (4,16) with three). Every deficiency found is a lift: codewords $A_l \otimes B$ with a common lower factor $B$, where the $A_l$ form a list of the small top code on the blocks, a block agreement is worth a whole block of leaves, and the zeros of $B$ are shared by all members. It scales linearly in $n$: explicit lists, checked by exact linear algebra up to $n = 256$, give at rate 1/2 three codewords at agreement $3n/4 - 1$, four at $0.695 n$, five at $0.672 n$, eight at $0.637 n$, 70 just below $9n/16$ and 12870 just below $17n/32$; at rate 1/4 four at $0.496 n$, five at $0.465 n$, 28 just below $11n/32$. So a list bound $L$ between 3 and 7 needs a slack of $4/64$ to $5/64$ over $(1 + L\rho)/(L+1)$ at both rates, more than the $2/64$ the lead says a practical win allows; part (b) of the target theorem of note 68 is false for small $L$, and only very large lists (about $10^2$ to $10^4$) could still buy room. The same lists exist for today's Reed-Solomon code on a subspace, so the tree code is not worse than today's code on anything found (it has fewer deficient patterns), and T1 is measurably worse than T2 when used at the top layers. For zero patterns the lead's predictions hold: a planted coincidence at depth $j$ wastes exactly one block of $n/2^{j+r}$ leaves, no coincidence of another kind and none wasting more was found (exhaustive at (8,16) over GF($2^8$) and GF($2^{16}$)), and the distance defect over a small field is of the same order as a random linear code's; but its tail is heavy (relative distance $1/4$ with probability about $2^{-62}$ over a 64-bit field), so part (a) cannot hold with probability $2^{-130}$ and the top codes must be checked rather than trusted. **Not tested:** any upper bound (all list values are lower bounds from explicit lists; the searches over top codes of length 8 and 16 are heuristic), exhaustive scans beyond $n = 16$ or beyond four members, lists of more than eight members other than the balanced family, rates other than 1/2 and 1/4, a dedicated transfer-matrix attack, and the protocol's use of a list bound.

Status by task (details in the sections):
- Task 1 (Section 2): encoder, generator and the subspace specialization agree; the generic tree code is MDS; singular minors over a small field at rate $c/|F|$, $c$ between 1 and 3. **exact at the stated sizes / measured.**
- Task 2 (Section 4): table of deficiencies, exhaustive at four sizes and sampled at four more. **exact at the stated sizes.**
- Task 3 (Section 6): searches over GF($2^8$), GF($2^{16}$), GF($2^{64}$) against Reed-Solomon on a subspace, at random points and a random linear code, with exact first moments; an 8-bit field hides the structural defect at these lengths. **measured.**
- Task 4 (Sections 5, 7, 9): the lifting lemma and its lists. **proved mechanism, exact checks at the stated sizes; the optimum over top patterns is measured.**
- Task 5 (Section 10): T1 against T2 and four mixed variants. **exact counts at the stated sizes, measured lifted values.**
- The lead's two requests (Sections 6 and 8) and the compiler warning (end of Section 8: no reported number changed).

## 1. Conventions

Field $F$ of characteristic 2. Message table $m \in F^{2^v}$, $k = 2^v$, leaves $j \in \{0,1\}^{v+r}$, $n = 2^{v+r}$, rate $\rho = 2^{-r}$. Twiddles $t_i(p, b)$ for layer $i < v$, prefix $p = (j_{v+r-1}, \dots, j_{i+1})$, $b = j_i$. Variant T2: $t_i(p,0) \ne t_i(p,1)$ uniform. Variant T1: $t_i(p,1) = t_i(p,0) + 1$. Row of leaf $j$: $\bigotimes_i (1, x_i(j))$ with $x_i(j) = t_i(p_i(j), j_i)$. A block at layer $i$ is the set of $2^i$ leaves sharing the bits $j_{v+r-1}, \dots, j_i$; the top $r$ bits select the tree.

For a list of $L+1$ members and a word, $c_x$ is the number of members agreeing with the word at leaf $x$, and the weight of the configuration is $\sum_x (c_x - 1)_+$. A code whose every $L+1$ distinct codewords and every word satisfy weight $\le Lk - 1$ is called LD-MDS($L$) below (the generalized Singleton bound, attained by random linear codes over large fields).

## 2. Task 1: encoder, Reed-Solomon specialization, singular minors

Scripts: `scripts/69_gf.h` (GF($2^8$) and GF($2^{16}$) by tables, GF($2^{64}$) = $\mathbb F_2[x]/(x^{64}+x^4+x^3+x+1)$ by carry-less multiplication), `scripts/69_tree.h` (twiddles, generator, butterfly encoder, rank), `scripts/69_t1_encoder.c`, `scripts/69_t1_run.sh`, output `scripts/69_t1_output.txt`.

**Encoder (exact at the stated sizes).** The butterfly network $(u, w) \mapsto (u + t_i(p,0) w, u + t_i(p,1) w)$, top layer first, equals the generator matrix with rows $\bigotimes_i (1, x_i(j))$ on a random message: 0 mismatches at every size run ($k = 4$ to $32$, $n = 8$ to $64$, the three fields, T1 and T2).

**Subspace specialization (exact at the stated sizes).** For a random $\mathbb F_2$-independent basis $\beta_0, \dots, \beta_{v+r-1}$, leaf $j \mapsto y_j = \sum_l j_l \beta_l$ and $x_i(j) = \hat W_i(y_j)$ ($\hat W_i$ the subspace polynomial of $\langle \beta_0, \dots, \beta_{i-1} \rangle$ normalized to 1 at $\beta_i$): the twiddles satisfy $t_i(p,1) = t_i(p,0) + 1$ at every node (so the specialization lies in variant T1, hence in T2), and the column space of the generator equals that of the Vandermonde matrix on the $y_j$ (rank of $[G \mid V]$ equal to $k$) at $(k, n, F) = (8, 16, 2^{64})$, $(16, 64, 2^{64})$, $(16, 32, 2^{16})$, $(8, 32, 2^8)$. Every $k \times k$ minor tested of the specialization is nonsingular (all 12870 minors at $(8,16)$ on 20 bases). So every $k \times k$ minor is a nonzero polynomial in the twiddles in both variants: **the generic tree code is MDS (proved in note 68, confirmed here).**

**Singular minors for random twiddles (measured).** Fraction of singular $k \times k$ minors times $|F|$ (a uniformly random matrix gives about 1):

| $(k, n)$ | variant | GF($2^8$) | GF($2^{16}$) | GF($2^{64}$) |
|---|---|---|---|---|
| (4, 8), all 70 minors | T2 | 2.08 | 3.2 | |
| (4, 8), all 70 minors | T1 | 1.93 | 2.9 | |
| (4, 16), all 1820 minors | T2 | 1.65 | 1.49 | |
| (8, 16), all 12870 minors | T2 | 3.35 | 0.99 | 0 of 257400 |
| (8, 16), all 12870 minors | T1 | 2.11 | 1.16 | |
| (16, 32), random minors | T2 / T1 | 2.04 / 2.24 | 1.15 / 1.48 | 0 of 400000 (T1) |
| (32, 64), random minors | T2 | 2.46 | 0.49 | 0 of 100000 |
| (8, 32), random minors | T2 | 1.39 | 2.13 | |

The GF($2^{16}$) entries at $n \ge 32$ rest on 3 to 13 singular minors each. Reading: a minor is singular with probability $c/|F|$ with $c$ between 1 and about 3, the number of components of its determinant; nothing is singular over the 64-bit field. Over a small field the tree code is therefore not MDS, like a random linear code and unlike Reed-Solomon; Section 3 says what baseline that imposes.

## 3. Lead's reading guidance (received during the run) and how it is addressed

The lead asked for two things, recorded here as received. (1) Do not compare a small-field tree code against exact MDS: a tree code is expected to have a Singleton defect of about $n/\log_2|F|$ at every list order from coarse block patterns (one vanishing minor of a top code wastes a whole block of leaf constraints), so the baseline over GF($2^8$) and GF($2^{16}$) is a uniformly random linear code over the same field, and Reed-Solomon at random points; over a 61 or 64 bit field at toy length no defect is expected except by planted coincidences. (2) Test planted coincidences: (a) two top-level twiddles equal across trees (predicted: a $k/2$-dimensional family vanishing on $k$ leaves), (b) one vanishing $4 \times 4$ minor of the top $[8,4]$ code (predicted: a $k/4$-dimensional family vanishing on $k$ leaves), (c) the same one or two levels lower; confirm or refute that one coincidence at depth $j$ wastes exactly one block of $n/2^{j+r}$ constraints, and look for coincidences that waste more or are not of the form "a minor of a top code vanishes".

Where each is answered: the same-field baselines are in Section 6 (direct list sizes), the planted coincidences in Section 8. One caveat on (1), established in Sections 4 and 5: at list order $L + 1 \ge 3$ the tree code has a defect over the 64-bit field with fully generic twiddles and no coincidence at all. It is a defect of the generalized Singleton bound, not of the distance, and it is shared with Reed-Solomon on a subspace.

## 4. Task 2: higher-order MDS at toy size (exact at the stated sizes, GF($2^{64}$))

Scripts: `scripts/69_pat.h` (incidence system, feasibility), `69_t2_exh.c` with `69_t2_run_exh.sh` (exhaustive), `69_t2_classify.py` (orbits), `69_t2_file.c` (kernel profiles), `69_t2_samp.c` with `69_t2_run_samp.sh` (sampled). Outputs `scripts/69_t2_*_output.txt`.

**Method.** A pattern gives each leaf an agreement class (a set of at least two members, or nothing). Unknowns $d_1, \dots, d_L \in F^k$ ($d_0 = 0$); a leaf $x$ of class $C$ gives the equations $g_x (d_l - d_{l_0}) = 0$, $l \in C \setminus \{l_0\}$, $l_0 = \min C$: $\sum_x (c_x - 1)_+$ equations, the weight. Codes, one random instance each over GF($2^{64}$): **U** uniform generator matrix, **R** Reed-Solomon at random points, **T2**, **T1**, **S** Reed-Solomon on a random $\mathbb F_2$-subspace (the tree code with subspace twiddles). The deficiency of a pattern for a code is rank(U) minus rank(code). A pattern is *feasible* for a code if the kernel contains a point with $0, d_1, \dots, d_L$ pairwise distinct (tested exactly: no pair collapses on the whole kernel), that is if the pattern carries a genuine list. "Balanced" is the largest minimum agreement over members that the pattern gives, leaves without a class being handed to one member each. Exhaustive scans take one pattern per orbit of the tree automorphisms (swap the two children of any node, swap trees), under which the generic ranks of U, R, T1, T2 are invariant; S is not invariant, so its column counts representatives only, except in the first row which scans all $5^8$ patterns.

| $(k, n)$, members | patterns | code | deficient patterns (largest deficiency) | largest weight of a feasible pattern ($Lk - 1$ is the generalized Singleton bound) | largest balanced agreement |
|---|---|---|---|---|---|
| (4, 8), 3 | all 390625 | U, R | 0 | 7 = $Lk - 1$ | 5 |
| | | T2, T1 | 48 (1) | 8 | 5 |
| | | S | 336 (1) | 8 | 5 |
| (4, 8), 4 | 4747821 orbits (all) | U, R | 0 | 11 = $Lk - 1$ | 4 |
| | | T2 | 1740 (1), of which 1164 carry a list | 12 | **5** |
| | | T1 | 1743 (1), 1167 carry a list | 12 | **5** |
| | | S | 3762 (1), 2629 carry a list | 12 | **5** |
| (8, 16), 3 | 26357430 orbits (all) | U, R | 0 | 15 = $Lk - 1$ | 10 |
| | | T2 | 945 (2) | **18** | **11** |
| | | T1, S (on the 945) | 945 | | |
| (4, 16), 3, rate 1/4 | 26357430 orbits (all) | U, R | 0 | 7 = $Lk - 1$ | 7 |
| | | T2, T1 | 27 (1) | 8 | **8** |
| | | S (on the 27) | 27 | | |

**Findings.**
- **Reed-Solomon at random points has no deficiency at all** on any of the 57 million patterns: its rank equals the uniform matrix's everywhere (exact at these sizes; consistent with generic Reed-Solomon codes being higher-order MDS).
- **The generic tree code is not higher-order MDS, with no coincidence among the twiddles, over the 64-bit field.** Smallest example ($k = 4$, $n = 8$, three members, weight $8 = Lk$, rank 7 for T1, T2 and S against 8 for U and R): leaves in tree order `. 012 | 01 01 | 02 02 | 12 12`, that is three sibling pairs carrying the three two-member classes and one leaf of the fourth pair where all three agree. Written out with top twiddles $a_0..a_3$ (one per pair) and bottom twiddle $s_x$ of the triple leaf: $m_0 = 0$, $m_1 = \alpha (X_1 - a_1)(X_0 - s_x)$, $m_2 = \beta (X_1 - a_2)(X_0 - s_x)$ with $\alpha (a_3 - a_1) = \beta (a_3 - a_2)$, so that $m_1 - m_2 \propto (X_1 - a_3)(X_0 - s_x)$. Three distinct codewords with agreements $(5, 5, 5)$ plus one free leaf, weight 8 against the bound 7.
- **Every deficiency found has this form (exact at these sizes).** In all 945 deficient orbits at (8,16) and all 27 at (4,16) the kernel consists of lists $m_l = A_l \otimes B$ with a common lower factor $B$ (the profile test of `69_t2_file.c`: the upper slices of all $d_l$ span a line at some split level). At (4,8) with four members, all 1164 orbits that carry a list for T2 and none for U contain three members sharing a lower factor, and the only minimal orbit is the three-member example above; the other 576 rank-deficient orbits carry only collapsed solutions (two equal members).
- T1 has three more orbits than T2 at (4,8), four members: `01 23 | 0123 0123 | 02 13 | 12 03` and its two relabelings, a common *upper* factor and a four-member list of the bottom code $\{\alpha + \beta s\}$ on the points $s_p, s_p + 1$ (Sections 9 and 10). S has all the tree code's deficiencies and 1465 more orbits of its own at this size.
- At (4,8) four members, (8,16) three members and (4,16) three members the tree code has a list whose **minimum** agreement exceeds the generalized Singleton value: 5 against 4, 11 against 10, 8 against 7.

**Sampled patterns at larger sizes (measured; `69_t2_samp_output.txt`).** Weights within 2 of $Lk$; U is the reference; "new lists" are patterns that carry a list for the code and none for U.

| $(k, n)$, members | generator (samples each) | T2 deficient / new lists | R | S deficient |
|---|---|---|---|---|
| (8, 16), 4 | random leaves (100000) | 0 / 0 | 0 | 6 |
| | sibling pairs split between classes (100000) | 0 / 0 | 0 | 5 |
| | unions of blocks, level 1 / level 2, with up to 3 edited leaves | 270 / 205 and 391 / 192 | 0 | 296 and 396 |
| | tree 0 in blocks, tree 1 scattered | 16 / 13 | 0 | 26 |
| | blocks of mixed levels | 84 / 34 | 0 | 85 |
| (16, 32), 3 | random leaves, sibling pairs split (30000 each) | 0 / 0 | 0 | 0 |
| | blocks at level 1 / 2 / 3 | 60, 197, 231 (largest deficiency 4) | 0 | 61, 232, 231 |
| (16, 32), 4 | random leaves, sibling pairs split (20000 each) | 0 / 0 | 0 | 0 |
| | blocks at level 1 / 2 / 3 | 21, 111, 123 (largest deficiency 3) | 0 | 22, 115, 123 |
| (8, 32), 3, rate 1/4 | random leaves, sibling pairs split (30000 each) | 0 / 0 | 0 | 0 |
| | blocks at level 1 / 2 | 17, 59 | 0 | 18, 59 |

T1 equals T2 on all of these up to 2 patterns. Reading: the tree code's deficient patterns are block-aligned; a pattern scattered over leaves, or one that splits sibling pairs between classes, is never deficient in the sample; R is never deficient. At (16,32) a second kind of kernel appears that the exhaustive sizes are too small to show: 13 of the 196 lists at four members and about 18 at three members have no three members sharing a lower factor; their differences lie in $C_{\rm up} \otimes W$ with $W$ a two-dimensional space of lower factors (profile `2,2,3` or `2,2,4` in `69_t2_file.c`), for instance `02 02 02 02 | . . . . | . . . . | 012 . 012 012 | 012 . 012 012 | 01 01 01 01 | 01 12 12 12 | 012 012 012 012` (rank 31 against 32). Section 5 explains both kinds by one mechanism.

## 5. The mechanism: the tree code is an interleaved top code at every level (proved), and what it costs

**Structure (proved, elementary).** Fix a split level $i$, $k_{\rm up} = k/2^i$, $N = n/2^i$ blocks. Write $m = \sum_f A_f \otimes e_f$ with slices $A_f \in F^{k_{\rm up}}$, $f \in \{0,1\}^i$. The top code $C_{\rm up}$ is the tree code of the top $v - i$ layers on the $N$ blocks; the bottom code $C_{\rm low}$ has rows $\bigotimes_{i' < i} (1, x_{i'}(j))$ on the $n$ leaves, dimension $2^i$. Then $c_j = \sum_f A_f(\mathrm{block}(j))\, \beta_f(j)$ with $\beta_f(j)$ the $f$-th entry of the bottom row of $j$: on block $p$ the codeword is $T_p\,(A_f(p))_f$, $T_p$ the invertible bottom transform of that block. For every subspace $W \subset F^{2^i}$ of lower factors, $C_{\rm up} \otimes W$ is a subcode in which a leaf $x$ acts through the functional $\mathrm{ev}_x|_W$ only. Both codes are MDS for generic twiddles (specialize to Reed-Solomon).

**Lifting lemma (proved).** Let $A_0, \dots, A_L$ be distinct codewords of $C_{\rm up}$ and $w_{\rm up}$ a word on the blocks, with block agreement sets $S^{\rm up}_l$, and let $B \ne 0$ be a codeword of $C_{\rm low}$ with zero set $Z$ (any $2^i - 1$ leaves can be prescribed). Then $m_l = A_l \otimes B$ are distinct, and with $w_j = w_{\rm up}(\mathrm{block}(j)) B_j$ the agreement set of $m_l$ is (the leaves of the blocks of $S^{\rm up}_l$) $\cup\ Z$. So a block agreement of the top code is worth $2^i$ leaves, and the $2^i - 1$ zeros of $B$ are common to all members: weight $L$ each at no cost in rank. The same holds verbatim for Reed-Solomon on a subspace ($A(\hat W_i(y)) B(y)$), and not for Reed-Solomon at random points, which has no blocks.

**Consequences.**
- (proved, given a top list at its generalized Singleton weight $L k_{\rm up} - 1$ that leaves $2^i - 1$ leaves outside every class) weight $2^i (L k_{\rm up} - 1) + L(2^i - 1) = Lk - 1 + (L - 1)(2^i - 1)$. Exact at the stated sizes: 8 at (4,8) and 18 at (8,16), three members, as in the table of Section 4. The excess over the generalized Singleton bound is linear in $k$ ($i = v - 1$ gives $(L-1)(k/2 - 1)$).
- (proved) **Staircase.** Take $w_{\rm up}$ generic and $a = k_{\rm up}$: every $k_{\rm up}$-subset of blocks interpolates one $A_S$, so there are $\binom{N}{k_{\rm up}}$ members, each agreeing on $k$ leaves plus the zeros of $B$ outside its blocks, about $(1 - \rho)(2^i - 1)$ of them when the zeros are spread: **$\binom{k_{\rm up}/\rho}{k_{\rm up}}$ codewords at agreement $\rho + \rho(1-\rho)/k_{\rm up} - O(1/n)$, for every $k_{\rm up} = 2^j$.** At rate 1/2: 6 codewords below agreement $5/8$, 70 below $9/16$, 12870 below $17/32$, $6.0 \cdot 10^8$ below $33/64$. At rate 1/4: 28 below $11/32$, 1820 below $19/64$. A code at the generalized Singleton bound has at most 4, 8, 16, 32 (rate 1/2) and 8, 16 (rate 1/4) just below those agreements. The list size at agreement $\rho + \varepsilon$ is at least $2^{(1-\rho) H(\rho)/\varepsilon\,(1 - o(1))}$, not $O(1/\varepsilon)$.
- (measured, by encoding, `scripts/69_t4_product.c`, `69_t4_output.txt`, random T2 twiddles over GF($2^{64}$), the same counts for T1, for S, and over GF($2^{16}$) and GF($2^8$)):

| $(k, n)$ | $k_{\rm up}$ | members | smallest agreement | generalized Singleton value for that many members |
|---|---|---|---|---|
| (16, 32) | 2 | 6 | 19 | 18 |
| (32, 64) | 2 / 4 | 6 / 70 | 39 / 35 | 37 / 32 |
| (64, 128) | 4 / 8 | 70 / 200 of the 12870 | 71 / 66 | 64 / 64 |
| (128, 256) | 4 / 8 | 70 / 2000 of the 12870 | 143 / 135 | 129 / 128 |
| (16, 64), rate 1/4 | 2 | 28 | 21 | 17 |
| (32, 128), rate 1/4 | 2 / 4 | 28 / 1820 | 43 / 35 | 35 / 32 |

- **Effect on the target theorem of note 68 (b) (proved lower bounds on $\varepsilon$).** "No word has more than $L$ codewords at agreement $\tau_L + \varepsilon$" is false for the generic tree code at rate 1/2 unless $\tau_L + \varepsilon \ge 5/8$ for $L \le 5$ and $\ge 9/16$ for $6 \le L \le 69$ and $\ge 17/32$ for $70 \le L \le 12869$. For $L = 8$ this asks $\varepsilon \ge 0.0069 = 0.44/64$ (harmless); for $L = 16$ it asks $\varepsilon \ge 0.033 = 2.1/64$: every list bound between 7 and 69 buys the same threshold $9/16$. (This bullet counts balanced top lists only; Section 7 shows that unbalanced lifts force much more at small $L$.) The honest targets at rate 1/2 are $(\tau, L) = (9/16 + \varepsilon, \approx 70)$ and $(17/32 + \varepsilon, \approx 1.3 \cdot 10^4)$; at rate 1/4, $(11/32 + \varepsilon, \approx 28)$ and $(19/64 + \varepsilon, \approx 1820)$.
- **Lower factors of dimension two and more (proved mechanism, measured instances).** In $C_{\rm up} \otimes W$ a set $S$ of leaves whose functionals $\mathrm{ev}_x|_W$ are proportional costs one equation per pair of members and gives $|S|$ agreements; $W$ can be chosen with a group of up to $2^i - \dim W + 1$ such leaves for each of several groups (for $\dim W = 2$: $W = \langle b, b' \rangle$ with $b$, $b'$ each vanishing on $2^i - 1$ chosen leaves). The count of equations gives weight at most about $Lk + (L-1)2^i - 2L$ for $\dim W = 2$, no better than the rank-one family (estimated). So the deficient patterns are far more numerous than the rank-one ones, but every one seen gains at most about $L \cdot 2^i$ leaves over the lifted top list.

## 6. Task 3 and the lead's point (1): direct list sizes over small fields, against same-field baselines

Scripts: `69_t3_climb.c`, `69_t3_run.sh` (output `69_t3_output.txt`), `69_first_moment.py` (exact first moments, output `69_first_moment_output.txt`), `69_zero.c` (output `69_zero_output.txt`).

**Search (measured; every entry is a lower bound found by a heuristic).** Hill-climb on the pattern, keeping a kernel point with pairwise distinct members, from block-structured starts trimmed to feasibility; 2 code draws per entry, 40 to 300 restarts each. Entries are "balanced agreement, weight"; for two members the weight is the number of zeros of a nonzero codeword. gS is the generalized Singleton value; FM is the exact first-moment threshold of a uniformly random linear code over the same field (largest value with expectation at least 1).

| $(k, n)$, members, field | gS | FM (random linear) | T2 | T1 | S | R | U |
|---|---|---|---|---|---|---|---|
| (16,32), 2, $2^8$ | 23, 15 | zeros 18 | 25, 18 | 24, 17 | 23, 15 | 23, 15 | 24, 17 |
| (16,32), 2, $2^{16}$ | 23, 15 | zeros 16 | 24, 16 | 24, 16 | 23, 15 | 23, 15 | 24, 16 |
| (32,64), 2, $2^8$ | 47, 31 | zeros 38 | 51, 39 | | 47, 31 | 47, 31 | 49, 34 |
| (32,64), 2, $2^{16}$ | 47, 31 | zeros 34 | 48, 32 | | 47, 31 | 47, 31 | 48, 32 |
| (8,32), 2, $2^8$ / $2^{16}$ | 19, 7 | zeros 10 / 8 | 21, 10 / 20, 8 | | 19, 7 | 19, 7 | 20, 9 / 20, 8 |
| (16,32), 3, $2^8$ | 21, 31 | 23 | 23, 39 | 24, 40 | 23, 38 | 22, 34 | 22, 35 |
| (16,32), 3, $2^{16}$ | 21, 31 | 22 | 23, 37 | 22, 34 | 23, 37 | 21, 32 | 21, 32 |
| (16,32), 3, $2^{64}$ | 21, 31 | 21 | 23, 37 | | 23, 38 | | 21, 31 |
| (32,64), 3, $2^8$ | 42, 63 | 48 | 43, 66 (47, 77 by transfer) | | 47, 77 | 43, 67 | 43, 66 |
| (32,64), 3, $2^{16}$ | 42, 63 | 45 | 42, 64 (47, 77 by transfer) | | 47, 77 | 42, 64 | 42, 64 |
| (8,32), 3, $2^8$ / $2^{16}$ | 15, 15 | 18 / 16 | 17, 20 / 16, 16 | | 16, 18 / 16, 16 | 16, 18 / 16, 16 | 17, 19 / 16, 16 |
| (16,32), 4, $2^8$ | 19, 47 | | 22, 59 | 23, 60 | 20, 51 | 20, 51 | 20, 51 |
| (16,32), 4, $2^{64}$ | 19, 47 | | 19, 47 (20, 54 by construction) | | 20, 50 | | 19, 47 |
| (16,32), 6, $2^{64}$ | 18, 79 | | 18, 80 (19, 85 by construction) | | 18, 80 | | 18, 79 |

Reading, with the caveats that matter:
- **The search is weak beyond three members and at $n = 64$**: it missed lists that Section 5 and Section 7 construct (marked "by construction" or "by transfer": the pattern the search found for S at (32,64) is a rank-one lift, and `69_t2_file.c` confirms it is feasible for T2 and T1 over the 64-bit field with the same rank). The T2 column is therefore not evidence that T2 is better than S.
- **Over the 64-bit field** the tree code and Reed-Solomon on a subspace exceed the uniform matrix (23 against 21 at (16,32), three members); the uniform matrix and Reed-Solomon at random points sit at the generalized Singleton value. This is the structural defect of Section 5, not a small-field effect.
- **Over GF($2^8$) the random linear code is itself far from the generalized Singleton value**: its exact first-moment threshold for three members at (32,64) is 48, above the $3n/4 - 1 = 47$ of the tree code's lifted triple. At these lengths an 8-bit field hides the structural defect; a 16-bit field shows it at three members (23 against FM 22 at (16,32); 47 against FM 45 at (32,64)).

**Zero sets (the lead's prediction of a defect near $n/\log_2|F|$).** Exact first moment for the uniformly random code: largest zero set $k - 1 + e$ with $e/n = 0.094$ to $0.109$ over GF($2^8$) ($n = 32$ to 128) and $0.031$ to $0.055$ over GF($2^{16}$), none over GF($2^{64}$) at $n \le 64$. Tree code T2, zeros forced by vanishing minors of its top codes (`69_zero.c`: all minors of the top codes up to 20000, a sample of 20000 per level beyond; a lower bound): over GF($2^8$) the mean excess is $0.079 n$ at $n = 64$ (100 draws: $n/16$ in 78, $n/8$ in 20, $n/4$ in 2), $0.074 n$ at $n = 128$, $0.066 n$ at $n = 256$, $0.070 n$ at (32,128); over GF($2^{16}$), $0.019 n$ at $n = 64$ and 128 (sampling misses most minors of the deep levels there). The climb found 39 zeros for T2 at (32,64) over GF($2^8$) against FM 38 for the random code. **So the tree code's distance defect is the same multiple of $1/\log_2 |F|$ as the random linear code's in a typical draw (measured), and Reed-Solomon at random points has none.** The difference is the tail: the tree code's defect is $n/2^{j+r}$ with probability about $c \binom{2^{j+r}}{2^j}/|F|$ ($c$ between 1 and 3, Section 2), for instance relative distance $1/4$ instead of $1/2$ with probability $2^{-62}$ over a 64-bit field at rate 1/2, and a defect of $n/8$ with probability about $2^{-57}$. Part (a) of the target theorem of note 68 cannot hold with probability $2^{-130}$ over twiddles in $K$ for any $\varepsilon_0 < 1/4$. Since the code is fixed once per size, the cure is to check the top codes rather than to bound a probability: verifying that the top codes up to $[32, 16]$ are MDS is $6 \cdot 10^8$ determinants (estimated), after which the remaining coincidences waste at most $n/64$.

## 7. Lists of three to eight members: the thresholds that decide the proposal (the lead's second message)

The lead reported that the practical win needs a list bound $L \ge 3$ at slack $\varepsilon \le 2/64$ over $\tau_L = (1 + L\rho)/(L+1)$, and asked for evidence at $L + 1 = 4$ and 5 members. **The answer is negative at both rates: the lifted lists force a slack of about $4/64$ to $5/64$ for every $L$ from 3 to 7, with generic twiddles over the 64-bit field.**

**Why Section 5's balanced staircase understated it (proved mechanism).** The members of a lifted list need not have equal block agreement. The zeros of the common lower factor $B$ (one block's worth, $2^i - 1$ leaves) are worth one agreement to every member whose blocks they avoid, so they are placed where the weak members gain; and leaves no class uses are handed to the weakest member. Two examples on the top $[4,2]$ code at rate 1/2 (blocks are half-trees, classes written per block):
- `12 | 02 | 01 | .`: three lines meeting pairwise on three blocks, all zeros of $B$ in the fourth. **Three codewords at agreement $3n/4 - 1$**, the unique-decoding radius, where the generalized Singleton value is $2n/3$. In Reed-Solomon terms: $0$, $(W - c_2) B$ and $\gamma (W - c_3) B$ with $B$ vanishing on all but one point of the coset $W = c_1$.
- `123 | 03 | 02 | 01`: three concurrent lines and a transversal, zeros of $B$ split over the last three blocks. **Four codewords at agreement $2n/3 - 1$** ($\tau_3 = 5/8$).

**Method (measured; exact rank checks at the sizes stated).** `69_t3_climb.c` with a lift argument scores a pattern of a small top tree code (T2, random twiddles, GF($2^{64}$)) by the balanced agreement of its lift by 5 bottom layers, zeros placed by a leximin greedy; the top $[4,2]$ code is searched exhaustively, the others by climbing (`69_lift_run.sh`, output `69_lift_output.txt`). The top code is itself a tree code, so nested lifts are included. Every best pattern was then lifted by 3 layers with an independent script (`69_lift.py`) and checked by exact linear algebra at $n = 32$ to 128 (`69_lift_verify2.sh`, output `69_lift_verify2_output.txt`): rank, a kernel point with pairwise distinct members, and the codewords of that point recomputed from the generator. **All 24 are genuine lists for T2; none exists for the uniform matrix or for Reed-Solomon at random points; all but one exist for T1 and for Reed-Solomon on a subspace.** The values are lower bounds on the tree code's lists: the search over $[8, \cdot]$ and $[16, \cdot]$ is heuristic.

| members $M$ | rate 1/2: best agreement found (top code, $n$) | $\tau_{M-1}$ | slack forced on $L = M - 1$ | rate 1/4: best agreement found (top code, $n$) | $\tau_{M-1}$ | slack forced on $L = M - 1$ |
|---|---|---|---|---|---|---|
| 3 | 0.746 ($[8,4]$, 256); limit $3/4$ | 0.667 | 5.1/64 | 0.539 ($[8,2]$, 256) | 0.500 | 2.5/64 |
| 4 | 0.695 ($[8,4]$, 256) | 0.625 | **4.5/64** | 0.496 ($[8,2]$, 256) | 0.4375 | **3.7/64** |
| 5 | 0.672 ($[8,4]$, 256) | 0.600 | **4.6/64** | 0.465 ($[8,2]$, 256) | 0.400 | **4.2/64** |
| 6 | 0.652 ($[8,4]$, 256) | 0.583 | 4.4/64 | 0.445 ($[8,2]$, 256) | 0.375 | 4.5/64 |
| 7 | 0.645 ($[8,4]$, 256) | 0.571 | 4.7/64 | 0.422 ($[8,2]$, 256) | 0.357 | 4.1/64 |
| 8 | 0.637 ($[8,4]$, 256) | 0.5625 | 4.8/64 | 0.410 ($[8,2]$, 256) | 0.344 | 4.2/64 |

Exact checks at smaller length (balanced agreement of the verified list, with the generalized Singleton value in parentheses): rate 1/2, $(k, n) = (32, 64)$: 47 (42), 44 (39), 42 (38), 41 (37), 40 (36), 40 (35) for $M = 3, \dots, 8$; $(64, 128)$: 95 (85), 89 (79), 85 (76) for $M = 3, 4, 5$; rate 1/4, $(16, 64)$: 34 (31), 31 (27), 29 (25), 28 (23), 26 (22), 25 (21); $(32, 128)$: 63 (55) for $M = 4$ and 58 (51) for $M = 5$. At $n = 256$ (`69_lift_verify3.sh`, T2 and S, exact rank and codewords recomputed): rate 1/2, 178, 172 and 163 for $M = 4, 5, 8$ (generalized Singleton values 159, 153, 143); rate 1/4, 127 and 119 for $M = 4, 5$ (111, 102). The four-member list at rate 1/2 is `. 0123 | 123 12 | 02 023 | 013 01` on the top $[8,4]$ code: the three-member list at $3/4$ on the half-trees, which has agreement to spare, plus a fourth codeword interpolated through four quarter-trees.

**Consequences.**
- At rate 1/2 a list bound $L = 3$ needs agreement above $0.695$, $L = 4$ above $0.672$, $L = 7$ above $0.637$; the Johnson radius is $0.707$. At rate 1/4: $L = 3$ above $0.496$, $L = 4$ above $0.465$, $L = 7$ above $0.410$; Johnson is $0.5$. Small lists buy little room below Johnson on a tree code. Large lists do buy room (Section 5: 70 at $9/16$, 12870 at $17/32$; $L$ between about 100 and $10^4$ is the range where a tree code could still gain, if nothing worse exists there).
- **None of this distinguishes the tree code from today's Reed-Solomon code on a subspace**, which has the same lists. They are lists of the current code between capacity and Johnson, and they bound from below what any proof for that code can claim: for instance four codewords at $0.695 n$ and eight at $0.637 n$ at rate 1/2.
- A code without block structure escapes: Reed-Solomon at random points has none of these lists (rank equal to the uniform matrix on every pattern above). The randomness of a tree code sits inside the blocks, and the lists live on the blocks.

## 8. The lead's point (2): planted coincidences, and the search for other kinds

Scripts: `69_coinc_plant.c` (output `69_coinc_plant_output.txt`), `69_coinc_exh.c` with `69_coinc_run.sh` (output `69_coinc_exh_output.txt`).

**Planted, over GF($2^{64}$) (exact at the stated sizes).** Depth $j$ means the top code of the top $j$ layers, $[2^{j+r}, 2^j]$ on blocks of $k/2^j$ leaves.

| planted coincidence | sizes | nullity on the $k$ leaves of the planted blocks | prediction |
|---|---|---|---|
| (a) two equal top twiddles in different trees (depth 1) | (16,32) T2 and T1 | 8 | $k/2$: confirmed |
| (b) one vanishing $4 \times 4$ minor of the top $[8,4]$ code (depth 2) | (16,32), (32,64) | 4, 8 | $k/4$: confirmed |
| (c) one vanishing minor at depth 3 and 4 | (16,32), (32,64), (64,128) | 2; 4 and 2; 8 and 4 | $k/2^j$: confirmed |
| rate 1/4, depth 2 and 3 | (16,64) | 4, 2 | confirmed |

In each case 40000 leaf sets $Z$ (unions of random blocks of random levels, half of them inside the planted blocks, plus random leaves) were tested for $\min(|Z|, k) - \mathrm{rank}(G_Z)$: **no set wastes more than one block of $n/2^{j+r}$ leaves** (measured). Two refinements. First, one algebraic coincidence can make several minors vanish: two equal twiddles of layer $v - 2$ in different half-trees $h, h'$ give the top form $(X_{v-2} - t)(X_{v-1} - a_{h''})$ for every other half-tree $h''$, so one equation among the twiddles kills $2^{r+1} - 2$ minors of the top $[2^{r+2}, 4]$ code at once (proved; the likely source of the 75 leaf sets whose rank differs from the single-minor prediction at depth 2, not checked set by set). Each wastes one block on its own union and they do not add up on any set tested. Second, in T1 a coincidence between two nodes of one layer is automatically double ($t(p,1) = t(p,0) + 1$ on both sides), again without wasting more than one block on one set.

**Exhaustive classification over small fields at (8,16) (exact per draw; 60000 draws each).** For every draw, all 12870 leaf sets of size 8, all 70 minors of the top $[8,4]$ code on sibling pairs and the 6 of the top $[4,2]$ code on quads. A top minor of nullity $\nu$ at block size $b$ forces nullity $b\nu - |\bigcup P \setminus Z|$ on $Z$.

| | GF($2^8$) T2 | GF($2^8$) T1 | GF($2^{16}$) T2 | GF($2^{16}$) T1 |
|---|---|---|---|---|
| singular minors of the top $[4,2]$ code, rate times $|F|$ | 0.68 | 0.68 | 1.09 | 1.09 |
| singular minors of the top $[8,4]$ code, rate times $|F|$ | 1.93 | 1.91 | 2.47 | 2.65 |
| of these, not forced by the $[4,2]$ level: nullity 1 / nullity 2 or more | 15314 / 0 | 15090 / 0 | 56 / 0 | 68 / 0 |
| leaf sets singular with no top minor involved, rate times $|F|$ | 1.026 | 1.016 | 0.996 | 1.030 |
| of these with nullity 2 | 598 of 3.1 million | 484 | 0 of 11737 | 0 |
| leaf sets with a forced nullity: exactly as forced / one more / two more | 4790019 / 11692 / 0 | 4752698 / 14264 / 0 | 27550 / 0 / 0 | 28330 / 0 / 0 |

Reading (measured): every singular set of leaves is either forced by a vanishing minor of a top code with exactly the predicted nullity, or is a leaf-level coincidence of nullity 1 at the rate $1/|F|$ of a random matrix. "One more than forced" occurs at rate $0.6/|F|$ to $0.8/|F|$ among forced sets and nullity 2 at rate about $10^{-6}$ over GF($2^8$) and never over GF($2^{16}$): both are two independent coincidences, not one coincidence wasting more. **For zero patterns (list order 2) I found no coincidence that wastes more than one block and none that is not a vanishing minor of a top code.** What is not of that form is the list-order defect of Sections 4, 5 and 7, which needs no coincidence at all.

**The compiler warning.** `69_coinc_exh.c` line 40 had `1ull << FB`, which is a shift by the word size only when the file is compiled with the default `FB = 64`; the program is built with `-DFB=8` and `-DFB=16` only (`69_coinc_run.sh`), where the shift is by 8 or 16. It is replaced by `gf_order()` (a loop, in `69_gf.h`), as is the same expression in a dead branch of `69_t1_encoder.c`; all nine programs now compile for the three fields with no warning other than unused names. Both programs were rerun with the same seeds: **the outputs are byte-identical (0 differing lines), no reported number changed.**

## 9. Task 4: attacks that use the structure, and their best excess against $\sum_x (c_x - 1)_+ \le Lk$

| attack | what it gives | best excess reached | status |
|---|---|---|---|
| Rank-one tensors $A_l \otimes B$ (codewords are products; $B$ vanishes on $2^i - 1$ chosen leaves, $A_l - A_{l'}$ on blocks) | Sections 5 and 7 | weight $Lk - 1 + (L-1)(2^i - 1)$ with a top list at its own bound: 8 at (4,8), 18 at (8,16) against $Lk = 8$, 16 (exhaustive optimum, three members); 78 against 64 at (32,64); 228 against 192 at (64,128) with four members, 300 against 256 with five, 260 against 224 at (32,64) with eight. In agreement: the table of Section 7 | proved mechanism, exact checks |
| Messages supported on few top-variable slices, that is differences in $C_{\rm up} \otimes W$ with $\dim W = 2$ | leaves whose functionals on $W$ are proportional come in groups at the price of one | no more than the rank-one family in the instances found at (16,32) (rank 31 against 32 at weight 32, and 30 against 32); the count of equations gives at most about $Lk + (L-1) 2^i - 2L$ | measured instances, estimated bound |
| Families whose partial evaluations at a block are proportional | this is the rank-one family read on one block: the partial evaluations of all members at a block are multiples of $T_p B$ | as the first row | proved |
| Common upper factor $A \otimes B_l$ ($A$ vanishes on $k_{\rm up} - 1$ blocks, the $B_l$ form a list of the bottom code) | nothing for T2: the bottom code is generic at the leaf level and the bound $L 2^i (k_{\rm up} - 1) + L 2^i - 1 = Lk - 1$ is the generalized Singleton one. For T1 the bottom code $\{\alpha + \beta s\}$ on the points $s_p, s_p + 1$ has a four-member list of weight 6 (`01 23 | 02 13 | 12 03`, an identity of characteristic 2), which gives weight $Lk$ exactly | 1 (T1 only; exhaustive at (4,8), four members) | exact at that size |
| Words built from the transfer matrix between two trees (patterns aligned with one tree and scattered in the other) | sampled in Section 4 (generator "tree 0 in blocks, tree 1 scattered"): 16 deficient of 100000 at (8,16), 1 of 30000 at (16,32), all of the rank-one kind; nothing specific to the transfer matrix was found, and no dedicated construction was tried | none beyond the first row | measured; a dedicated attack is not tested |
| Zero patterns under coincidences | Section 8: one coincidence, one block | $k/2^j$ zeros per coincidence at depth $j$ | exact at the stated sizes |

The first row is the only attack that scales, and it scales linearly in $n$.

## 10. Task 5: variants

Outputs: `scripts/69_t2_exh_5a_4_8_4_output.txt`, `69_t2_exh_5b_8_16_3_output.txt`, `69_t2_exh_5c_8_16_3_output.txt` (exhaustive over the orbits of the tree automorphisms; for a code with subspace layers the generic rank is not invariant under them, so its counts are over representatives), and the lifted searches of Section 7 rerun with T1 and S top codes (`scripts/69_t5_lift_output.txt`, reproduced by `69_bin/t3_climb_64 2 1 L kind 400 500 seed 2 5` and `69_bin/t3_climb_64 1 2 3 kind 400 500 77 2 5` after `69_lift_run.sh` has built the binary).

| variant (layers bottom to top) | deficient orbits at (4,8), 4 members | deficient orbits at (8,16), 3 members | largest weight, largest balanced agreement at (8,16) | lifted 4-member list, rate 1/2 (top $[8,4]$) | lifted 4-member list, rate 1/4 (top $[8,2]$) |
|---|---|---|---|---|---|
| U, R | 0 | 0 | 15, 10 | none | none |
| T2 | 1740 | 945 | 18, 11 | 0.695 | 0.496 |
| T1 | 1743 | 945 on T2's (not scanned alone) | | 0.695 | **0.527** |
| top layer subspace, rest T2 (`2S`, `22S`) | 1740 | 945 | 18, 11 | | |
| bottom layer subspace, rest T2 (`S2`, `S22`) | 3762 | 963 | 18, 11 | | |
| only the bottom layer random (`2SS`) | | 1670 | 18, 11 | | |
| only the top layer random (`SS2`) | | 1981 | 18, 11 | | |
| S, all layers subspace | 3762 | 945 on T2's (not scanned alone) | | 0.695 (5 members: 0.684 against 0.672 for T2) | **0.527** |

Reading.
- **T1 against T2 (measured, with a proved mechanism).** T1 has every deficiency of T2. Its own come from the relation $t(p,1) = t(p,0) + 1$: four affine functions of one twiddle variable taking the values $s_p, s_p + 1$ on three nodes carry the pattern `01 23 | 02 13 | 12 03` (weight 6 against the bound 5: with the three nodes at $s_A, s_C, s_D$ the six equations reduce to $g_1 [(s_C + s_D)(s_D + s_A) + (s_A + s_D)(s_D + s_C)] = 0$, which holds identically in characteristic 2; the bottom-layer instance is the T1 example of Section 4, exact at that size). At the bottom layer this costs one leaf. At the top layers the same identity is a defect of the top code and lifts with the block size: at rate 1/4 the top $[8,2]$ code of T1 gives four codewords at $0.527 n$ against $0.496 n$ for T2, the same as Reed-Solomon on a subspace. The T1 pattern on the top $[8,2]$ code is `01 23 | 03 12 | . . | 02 13`: rank 5 for T1 and for the subspace code, rank 6 (no list) for T2 and the uniform matrix (exact at that size), and 18000 restarts on the T2 top code do not improve on $0.496$. **T1 is worse than T2 by about $2/64$ in agreement at four members and rate 1/4; at rate 1/2 the searches show no difference for four and five members.** If a tree code is used, the top layers should be T2 (one more multiplication a butterfly on few nodes); T1 below costs $O(1)$ leaves in what was tested.
- **Only the bottom layers random, the rest the subspace specialization (proved how it fails).** The top code is then Reed-Solomon on the quotient subspace, a block agreement is worth $2^a$ leaves, and the lifting lemma of Section 5 applies with that top code: every list of today's code at length $n/2^a$, structural or not, lifts to the variant with the zeros of the lower factor on top. The bottom randomness never enters a block-aligned pattern. So the variant has at least the lists of today's code at every length $n/2^a$; measured, 1670 deficient orbits against 945 at (8,16) with one random layer, and the lifted values of the S row. It is not worse than T2 at the two smallest sizes when only one top layer is subspace (`2S`, `22S`: identical counts), because a top $[4,2]$ code has no room for a subspace-specific list of three or four members.
- **Only the top layers random.** Block-aligned lists are those of T2. The subspace layers below add lists inside blocks (common upper factor times a list of the bottom code, which is Reed-Solomon of dimension $2^a$ on the whole domain): 1981 deficient orbits against 945 at (8,16), 3762 against 1740 at (4,8), the same count as the full subspace code there. No larger maximum at these sizes; not tested beyond.

## 11. What was not tested, and reproduction

Not tested: (i) any upper bound: nothing here shows that the lifted lists are the worst lists of a tree code, and the searches over the top codes $[8, \cdot]$ and $[16, \cdot]$ are heuristic, so every list value is a lower bound; (ii) exhaustive scans beyond $n = 16$ and beyond four members at $n = 8$ (five members at $n = 8$ is $2.6 \cdot 10^9$ orbits); (iii) lists of more than eight members other than the balanced family of Section 5; (iv) rates other than 1/2 and 1/4; (v) $E$-valued words (the rank is a rank over $K$, so nothing new is expected); (vi) a dedicated attack through the transfer matrix between two trees; (vii) the first moment for four or more members; (viii) the protocol: these are lists around a word, and how the DEEP fold consumes a list bound is not examined here; (ix) fields of odd characteristic.

Reproduction, from `doc/whir_soundness_gap_notes/scripts`: `69_t1_run.sh`; `69_t2_run_exh.sh v r L kinds tag` (for instance `2 1 3 U21RS 4_8_4`, `3 1 2 U2R 8_16_3`, `2 2 2 U21R 4_16_3`), then `69_bin/t2_file` and `69_t2_classify.py` on `69_tmp/def_<tag>.txt` (the lists for (8,16), (4,16) and the full (4,8) scan are kept as `69_t2_def_*.txt`); `69_t2_run_samp.sh`; `69_t3_run.sh`; `69_t4_run.sh`; `69_lift_run.sh`, `69_lift_verify.sh`, `69_lift_verify2.sh`, `69_lift_verify3.sh`; `69_coinc_run.sh`; `python3 69_staircase.py`; `python3 69_first_moment.py`. Each run is under fifteen minutes on four cores; binaries go to `69_bin/`, intermediate pattern lists to `69_tmp/` (regenerable, not needed to read the note).
