# Note 78: lift-free variants of the tree code (V1 leaf mixing, V2 index change), experiments and attacks

Status: IN PROGRESS. The first paragraph (verdict in words) is written last and replaces this line.

Labels used: proved / exact at the stated size / measured / estimated / conjectured. Scripts: `scripts/78_*`.

## 0. Setup and definitions

Researcher 78, round 18, 2026-11-21. Object: the two constructions of note 68 Section 13. Conventions of note 69 Section 1: field GF($2^{64}$) = $\mathbb F_2[x]/(x^{64}+x^4+x^3+x+1)$ (`scripts/69_gf.h`), message table $m \in K^{2^v}$, $k = 2^v$, leaves $j \in \{0,1\}^{v+r}$, $n = 2^{v+r}$, the top $r$ bits of $j$ select the tree, T2 twiddles (every node its own pair). A pattern gives each leaf a class of members; weight $= \sum_x (c_x - 1)_+$; the generalized Singleton bound (gS) for $L+1$ members is weight $\le Lk - 1$; a pattern is deficient for a code if its incidence system has smaller rank than for a uniform matrix U; it carries a list if the kernel has a point with pairwise distinct members.

**Codes.** U: uniform generator matrix. T2: plain tree code, rows $g_j = \bigotimes_i (1, x_i(j))$. **V1($d$, any)**: rows $g'_x = g_x + \sum_{a=1}^d \mu_{x,a}\, g_{\pi_a(x)}$, $\pi_a$ independent uniformly random permutations of the $n$ leaves, $\mu_{x,a}$ uniform nonzero. **V1($d$, cross)**: the same with $\pi_a$ uniform among the permutations that send every tree to another tree (a uniformly random nonzero XOR shift of the tree index, then a uniformly random bijection between the two trees, for each tree). **V2($M$)**: tree $t$ has rows $g^{(t)}_j[e] = g_j[M_t e]$, $M_0 = I$, $M_t \in \mathrm{GL}_v(\mathbb F_2)$; at rate 1/2 there is one matrix $M = M_1$. **V1 on V2**: the V1 mixing applied to the V2 codeword. Named matrices: `id`, `rev` (bit reversal), `rot` (cyclic rotation $e_i \to e_{i+1}$), `sw<i>` (transposition of bits $i$, $i+1$), `up` ($(Me)_i = e_i + e_{i+1}$, the lead's "add bit $i+1$ to bit $i$"), `dn` (its transpose). Code: `scripts/78_var.h`.

**Facts used to read the experiments (proved here, elementary; each is checked numerically below).**
- (P1) V1 is $A \cdot C$ with $C$ the tree code and $A = I + \sum_a D_a P_a$ sparse. For generic $\mu$: two members $l, l'$ agree at $x$ in V1 iff their tree codewords agree at $x$ and at every partner $\pi_a(x)$ (an agreement that is not of this kind costs one coincidence in $\mu_{x,\cdot}$, probability $1/q$). So the V1 pattern of an encoded list is, leaf by leaf, the common refinement of the tree partitions at $x, \pi_1(x), \dots, \pi_d(x)$. This is what Experiment 4 computes exactly.
- (P2) V1 on a set closed under the partner maps is the tree code on that set: if $\pi_a(S) \subseteq S$ for all $a$, the V1 rows of $S$ span the tree rows of $S$ (generic $\mu$), and a tree pattern whose classes are constant on the orbits inside $S$ is equivalent to the same V1 pattern. On a path $x_1 \to x_2 \to \dots \to x_m$ of one permutation ($d = 1$) the V1 rows of $x_1..x_{m-1}$ lie in the span of the tree rows of $x_1..x_m$: one leaf lost per path.
- (P3) **V2 with a bit permutation $M = P_\sigma \ne I$ is not MDS, and for bit reversal or a rotation by $v/2$ its relative distance tends to 0.** The message $\prod_i (X_i - a_i)$ is $\prod_i (Y_{\sigma(i)} - a_i)$ for the second tree. With $i_0 = \sigma^{-1}(v-1) \ne v - 1$: $a_{v-1}$ = a top twiddle of tree 0 and $a_{i_0}$ = a top twiddle of tree 1 give a family of dimension $k/4$ vanishing on $k/2 + k/2 = k$ leaves. For bit reversal with $v$ even, $A(X_{\rm up}) B(X_{\rm low})$ is $B^{\rm rev}(Y_{\rm up}) A^{\rm rev}(Y_{\rm low})$: $A$ vanishing on $\sqrt k - 1$ blocks of tree 0 and $B^{\rm rev}$ on $\sqrt k - 1$ blocks of tree 1 is a nonzero codeword with $2k - 2\sqrt k$ zeros among $n = 2k$.
- (P4) More generally for $M \in \mathrm{GL}_v(\mathbb F_2)$ with $u = e_{v-1}$: if $(Mu)_{v-1} = 0$ and $(M^{-1}u)_{v-1} = 0$, the conditions "vanish on the half tree $x_{v-1} = t$ of tree 0 and on the half tree $y_{v-1} = s$ of tree 1" are $4$ equations of rank 3 on each coset of $\langle u, M^{-1}u \rangle$, so a family of dimension $k/4$ vanishes on $k$ leaves: not MDS.
- (P5) If $M$ is block diagonal for the split at level $i$ (it preserves both the low bits and the high bits), every lift at level $i$ survives in V2. If $M$ only preserves the low bits $V_i$ (block triangular, as `up` at every level), products $A \otimes B$ stay products in tree 1 only for $B$ invariant under the shifts $M_{lu} M_{uu}^{-1} f_{\rm up}$: for `up`, $B = (1 + X_{i-1}) B''$, a lower-factor space of dimension $2^{i-1}$ instead of $2^i$. So `up` keeps lifts with about half the common zeros.

**Baselines.** Every table has the columns U and T2 computed by the same program on the same patterns.

## 1. Experiment 1: implementations and encoder check

Scripts: `scripts/78_var.h` (all variants behind one spec string: `U`, `T2`, `T2:d<D><p>` for V1 with $D$ partners of type `a` any, `x` cross tree, `f` cross tree without 2-cycles, and the deliberately bad types `s` sibling, `b` inside the half tree, `c` one $n$-cycle; `T2:M<names>` for V2; both tokens for V1 on V2), `scripts/78_e1_check.c`, output `scripts/78_e1_output.txt`.

**Encoder (exact at the stated sizes).** Encoder = index change of the table per tree ($c_0[tk + M_t e] = m_e$), the butterfly network of note 69, then the mixing $c'(x) = c(x) + \sum_a \mu_{x,a} c(\pi_a(x))$. Against the generator matrix on 20 random messages at $(k, n) = (4,8), (8,16), (16,32), (32,64), (64,128), (4,16), (16,64), (64,256)$: 0 mismatches in 11680 symbols for each of the 21 specs run (U, T2, V1 with $d = 1, 2, 3$ of types a and x, V1 $d = 1$ of types f, s, b, c, V2 with `id`, `rev`, `rot`, `up`, `dn`, `sw0`, the three-matrix list `up/dn/rev` at rate 1/4, and V1 on V2 twice). V2 with `id` is T2. The generator has rank $k$ in every case.

**Partner maps (measured, these draws).** Uniform permutations: a fraction $1/2^r$ of the partners lie in the leaf's own tree, and there are fixed points and 2-cycles at the expected rate (about one fixed point and one leaf pair in a 2-cycle per permutation, whatever $n$). Cross-tree permutations have no fixed point but still about one 2-cycle each ($x \to y \to x$); type `f` rejects those. By (P2) a fixed point or a 2-cycle is a place where V1 is locally the plain tree code, so at toy size the count of deficient patterns depends on the draw; Sections 3 and 5 report cycle types with the counts.

## 2. Experiment 2: MDS

Scripts: `scripts/78_e2_mds.c`; outputs `scripts/78_e2_output.txt` (V1, named V2, V1 on V2) and `scripts/78_e2_gl_output.txt` (every matrix of $\mathrm{GL}_2$, $\mathrm{GL}_3$, $\mathrm{GL}_4$).

**V1 is MDS (proved for generic parameters by $\mu \to 0$; exact at the stated sizes for random parameters over GF($2^{64}$)).** Singular $k \times k$ minors, all minors at $(4,8)$ (200 draws), $(4,16)$ (100 draws), $(8,16)$ (20 draws), $2 \cdot 10^6$ random minors at $(16,32)$ (4 draws):

| code | (4,8) | (4,16) | (8,16) | (16,32) random |
|---|---|---|---|---|
| U, T2 | 0 of 14000 | 0 of 182000 | 0 of 257400 | 0 of $2 \cdot 10^6$ |
| V1, $d = 1, 2, 3$, any and cross (six codes) | 0 | 0 | 0 | 0 |
| V2 `up`, V2 `dn` | 0 | 0 (at rate 1/4: $M, M^2, M^3$) | 0 | 0 |
| V1 ($d = 1$, cross) on V2 `up` | 0 | 0 | 0 | 0 |
| V1 ($d = 1$, cross) on V2 `rev` | 28 (14 draws of 200) | 16 (8 draws) | 55 (9 draws of 20) | 56 (all 4 draws) |
| V1 ($d = 1$, any) on V2 `rev` | 22 (9 draws) | 1 | 27 (9 draws) | 43 (all 4 draws) |
| V1 ($d = 1$, cross) on V2 `sw0` | 18 (9 draws) | 18 (9 draws) | 0 | 0 |
| V2 with the list `up/dn/rev` at rate 1/4 | | 400 (all 100 draws) | | |

**V2 is not MDS in general: exactly which $M$ fail (exact at the stated sizes: every minor up to the child swaps of both trees, a singular minor re-tested on two more twiddle draws; all singular minors found are singular in all three draws, that is identically zero).**

| $v$, $(k, n)$ | matrices | MDS | not MDS | canonical minors per matrix |
|---|---|---|---|---|
| 2, (4, 8) | 6 | 5 | 1 (the swap) | 8 |
| 3, (8, 16) | 168 | 123 | 45 | 65 |
| 4, (16, 32) | 20160 | 13707 | 6453 | 5329 |

- **Every bit permutation other than the identity fails** (5 of 5 at $v = 3$, 23 of 23 at $v = 4$), confirming (P3): bit reversal has 2576 identically zero canonical minors of 5329 at $v = 4$, the rotation 1202, the transpositions `sw0`, `sw1`, `sw2` 18, 20 and 198. Smallest witness at every size: a block of 2 leaves of one tree and all but 2 leaves of the other.
- **Every $M$ with $M_{v-1,v-1} = 0$ and $(M^{-1})_{v-1,v-1} = 0$ fails** (1 of 1, 36 of 36, 4686 of 4686), confirming (P4). These are 73 percent of the failures at $v = 4$; the other 1767 have no description here.
- **Every $M$ whose top principal minors are all nonsingular (the $j \times j$ blocks on the top $j$ bits, $j = 1..v$; equivalently $M = $ lower unitriangular times upper unitriangular for the order of the levels) is MDS: 4096 of 4096 at $v = 4$, 64 of 64 at $v = 3$** (exact at these sizes; **conjectured** for all $v$). This class contains `up`, `dn`, all 127 unitriangular matrices and every transvection $I + E_{ij}$. The MDS set is closed under inverse (it must be: swap the trees) and under transpose (observed, 13707 of 13707). 9611 further matrices are MDS at $v = 4$.
- **V1 on top does not repair a V2 that is not MDS** (table above): a V2 codeword with many zeros keeps the zeros whose partners are zeros, and at toy size that is still at least $k$ in a fraction of the draws.

Consequence for the rest of the note: V2 is run with $M$ = `up` (sparsest non-permutation, verifier cost one product per level), `dn`, and at $(4,8)$, $(8,16)$ with every MDS matrix.

## 3. Experiment 3: higher-order MDS scans

Script: `scripts/78_e3_scan.c` (rank of the incidence system of note 69 Section 4 for a list of codes on the same patterns; the reference is U; a pattern is deficient for a code if its rank is below U's; feasibility = a kernel point with pairwise distinct members). Symmetries: V1 has none of the tree, so its scans are over ALL patterns, reduced only by the relabelings of the members (valid for every code; counts are given in patterns); V2 keeps the child swaps inside each tree but not the swap of the trees, so its scans take one pattern per orbit of the child swaps and every ordered pair of trees.

### 3.1 $(k, n) = (4, 8)$, three and four members, ALL patterns (exact at this size)

Outputs: `scripts/78_e3_4_8_output.txt`.

| code | 3 members, all $5^8 = 390625$ patterns: deficient | largest weight of a list (gS: 7), balanced | 4 members, all $12^8 = 429981696$ patterns: deficient | largest weight of a list (gS: 11), balanced |
|---|---|---|---|---|
| U | 0 | 7, 5 | 0 | 11, 4 |
| T2 | 48 (all carry a list) | 8, 5 | 65088 (47232 carry a list, 18240 lists of weight $\ge Lk$) | 12, 5 |
| V1, $d = 1, 2, 3$, any | **0** | 7, 5 | **0** | 11, 4 |
| V1, $d = 1, 2, 3$, cross | **0** | 7, 5 | **0** | 11, 4 |
| V2 `up`, `dn`, and the two elements of order 3 (`#7`, `#14`): all four MDS matrices of $\mathrm{GL}_2$ other than the identity | **0** | 7, 5 | **0** | 11, 4 |
| V1 ($d = 1$, cross) on V2 `up` | **0** | 7, 5 | **0** | 11, 4 |
| V1 with the partner = the sibling leaf, or inside the half tree (deliberately bad, 3 members only) | 48, the same as T2 | 8, 5 | | |

The T2 column reproduces note 69 (48 patterns; note 69 counts 1740 tree orbits at four members, here 65088 patterns in 2736 relabeling orbits). The three-member scan was repeated on 20 more seeds, each with fresh twiddles, partner maps and coefficients, for ten V1 codes ($d = 1, 2, 3$ any and cross, $d = 1$ cross without 2-cycles, $d = 1$ one $n$-cycle, V1 on V2 `up` and `dn`): **0 deficient patterns in all 200 code draws** (54 of the 200 first partner maps have a fixed point), T2 48 every time. The last row confirms (P2): a partner map that respects the blocks gives back the lifts, so "far" is doing the work.

### 3.2 $(k, n) = (8, 16)$, three members, V2: all patterns up to the child swaps (exact at this size)

Outputs: `scripts/78_e3_8_16_output.txt`, the 582 patterns deficient for some V2 code in `scripts/78_e3_8_16_deficient_V2.txt`; kernel profiles by `scripts/78_profile.c`. 52707600 patterns ($7260^2$: one per orbit of the child swaps inside each tree, every ordered pair of trees; T2's count is twice note 69's 945 because the swap of the trees is not used).

| code | deficient patterns | of which carry a list | lists of weight $\ge Lk = 16$ | largest weight of a list (gS: 15) | largest balanced agreement (gS value 10) |
|---|---|---|---|---|---|
| U | 0 | | 0 | 15 | 10 |
| T2 | 1890 (largest deficiency 2) | 1890 | 1794 | 18 | 11 |
| V2 `up` | **36** | 36 | 36 | **16** | 10 |
| V2 `dn` | **36** | 36 | 36 | **16** | 10 |
| V2 `ud` (= `up` times `dn`, rows `010 101 110`) | **0** | | 0 | 15 | 10 |
| V2 `#85` (rows `101 010 001`, MDS, not in the class of Section 2) | **528** (largest deficiency 2) | 528 | 492 | **17** | **11** |

- **V2 is not higher-order MDS for `up` or `dn`, already at three members and $n = 16$.** Example for `up`: tree 0 `02 02 02 02 | 12 12 12 12`, tree 1 `. . . 012 | 01 01 012 012`, weight 16, rank 15. All 36 kernels have the same profile: in tree 1 the differences share a lower factor at level 1, in tree 0 they span a two-dimensional space of lower factors at level 2. This is the family of (P5): `up` preserves the low bits at every level and keeps the lifts whose lower factor lies in a space of half the dimension. The scan at $(4, 8)$ could not see it.
- **`ud` has none.** It preserves neither the low bits nor the high bits at any level.
- **MDS does not imply anything here**: `#85` is MDS and has 528 deficient patterns and a list one leaf above the gS value. So a V2 matrix has to be chosen by a scan like this one, not by the MDS test.
- Not done: the other 119 MDS matrices of $\mathrm{GL}_3$ (about 4 core-minutes each).

### 3.3 $(k, n) = (8, 16)$, three members, V1: $10^6$ patterns per generator (measured)

V1 has no symmetry and $5^{16}$ patterns is out of reach, so, as the brief says, samples: six generators, $10^6$ patterns each, the same patterns for every code (output `scripts/78_e3_8_16_sample_output.txt`). g0: random leaves and classes, weight within 2 of $Lk$; g1: unions of blocks at one level with up to 3 edited leaves; g2: blocks of mixed levels; g3: tree 0 in blocks, tree 1 scattered; g4: classes constant along runs $x, \pi(x), \pi^2(x), \dots$ of the first partner map of the first V1 code; g5: a block pattern with zeros intersected with its pull-back by the partner maps (the shape (P1) gives to an encoded lift).

| generator | U | T2 deficient (lists of weight $\ge Lk$) | V1 $d = 1$ any, cross; $d = 2$ any, cross; $d = 3$ cross; V1 ($d = 1$, cross) on V2 `ud` |
|---|---|---|---|
| g0 | 0 | 0 | 0 for each |
| g1 | 0 | 1721 (1560) | 0 for each |
| g2 | 0 | 677 (578) | 0 for each |
| g3 | 0 | 611 (592) | 0 for each |
| g4, g5 | 0 | 0 | 0 for each |

Largest weight of a list: 18 for T2, 15 = $Lk - 1$ for U and for every V1 code; largest balanced agreement 11 for T2, 10 for the others. **No deficient pattern for any V1 code in $6 \cdot 10^6$ patterns** (measured; one draw of each code).

### 3.4 $(k, n) = (4, 16)$, rate 1/4, three members

Output: `scripts/78_e3_4_16_output.txt`.

**V2 (exact at this size: all $120^4 = 207360000$ patterns up to the child swaps inside each tree).** At $v = 2$ no V2 code at rate 1/4 is MDS with four pairwise different matrices: $\mathrm{GL}_2(\mathbb F_2) \cong S_3$, the swap is the only non-MDS quotient, and every set of four elements has two whose quotient is the swap (proved by inspection of $S_3$). So two trees must share a matrix, and the lifts between those two trees are the tree code's.

| code | deficient patterns | largest weight of a list (gS: 7) | largest balanced agreement (gS value 7) |
|---|---|---|---|
| U | 0 | 7 | 7 |
| T2 | 204 | 8 | 8 |
| V2, trees `id, c, c^2, id` ($c$ of order 3, spec `T2:M#7`) | **6** | 8 | 8 |
| V2, trees `id, up, id, up` | **12** | 8 | 8 |

**V1 (measured: the six generators of 3.3, $10^6$ patterns each).** T2: 2, 86, 57, 93, 0, 0 deficient patterns (largest weight 8, balanced 8). V1 $d = 1$ any and cross, $d = 2$ any and cross, $d = 3$ cross, and V1 ($d = 1$, cross) on V2 `#7`: **0 deficient in $6 \cdot 10^6$ patterns each**, largest weight of a list 7, balanced 7.

### 3.5 Summary of Experiment 3

The count is **zero for V1 in every scan** (exhaustive at $(4, 8)$: 207 code draws with three members, 7 with four; $6 \cdot 10^6$ sampled patterns at $(8, 16)$ and at $(4, 16)$, one draw of each of six codes). For V2 the count is zero at $(4, 8)$ for all four MDS matrices and **not zero at $(8, 16)$** for three of the four matrices scanned (`up` 36, `dn` 36, `#85` 528, `ud` 0), and not zero at $(4, 16)$.

## 4. Experiment 4: the known lifted lists under the variants

Scripts: `scripts/78_e4_lists.c`, `scripts/78_e4_run.sh` (6 seconds), output `scripts/78_e4_output.txt`. Every list is built as a list of MESSAGES on a T2 tree (a kernel point of the T2 incidence system of a lifted pattern, or the staircase's $A_S \otimes B$), then encoded by each variant on the same twiddles. The word is free: per leaf the members are partitioned by their symbol, the weight of the best word is $\sum_x (\text{largest class} - 1)$, and the same is computed for sub-lists.

**Certificate used for the large lists (proved).** Let $r_S$ be the number of leaves at which member $S$ shares its symbol with another member of the list. For a sub-list $T$ put $E(T) = W_T - ((|T| - 1)k - 1)$, $W_T$ the weight of the best word for $T$; $T$ is beyond the gS weight iff $E(T) > 0$. Adding a member $S$ changes $E$ by at most $r_S - k$, and $E$ of one member is 1. So if at most one member has $r_S \ge k$, no sub-list of two or more members is beyond the gS weight, for any word. (For T2 the staircase has $r_S = k + n/N - 1$ for every member.)

**Small lists: the 52 lifted lists of note 69 (3 to 8 members; top patterns $[4,2]$, $[8,4]$, $[16,8]$ lifted to $n = 64, 128, 256$ at rate 1/2, and $[8,2]$, $[16,4]$ lifted to $n = 256$ at rate 1/4). Exact at these sizes: every sub-list, every word.**

| code | lists with a sub-list of 3+ members beyond the gS weight | largest excess of a sub-list of 3+ members over the gS weight |
|---|---|---|
| T2 | 52 of 52 | +165 |
| V1 $d = 1$ any / cross | 0 / 0 | $-18$ / $-25$ |
| V1 $d = 2$ any / cross | 0 / 0 | $-40$ / $-39$ |
| V1 $d = 3$ any / cross | 0 / 0 | $-49$ / $-50$ |
| V2 `up`, `dn`, `ud` | 0, 0, 0 | $-14$ each |
| V1 ($d = 1$, cross) on V2 `up` | 0 | $-63$ (no two members share a symbol anywhere) |
| V2 `cr` (bit 0 := top bit, top bit := top + bit 0, the other bits untouched) | **7 of 52** | **+47** |

**Staircases (exact at these sizes).** Entry: `cert(r)` = certified dead by the criterion above with largest $r_S = r$; `M@a` = a sub-list of $M$ members with balanced agreement $a$ above its gS value.

| list ($n$, $k$, $N$, members) | T2 | V1 $d=1$ any / cross | V1 $d=2$ any / cross | V1 $d=3$ any / cross | V2 `up` = `dn` = `ud` | V2 `cr` |
|---|---|---|---|---|---|---|
| one-sided (64, 32, 8, 35) | 35@39 | cert(27) / cert(25) | cert(17) / cert(16) | cert(13) / cert(11) | cert(31) | not certified, none found |
| balanced (64, 32, 8, 70) | 70@35 | cert(24) / cert(24) | cert(16) / cert(15) | cert(10) / cert(12) | cert(32) | not certified, none found |
| one-sided (64, 32, 16, 6435) | all@35 | cert(27) / cert(25) | cert(18) / cert(18) | cert(13) / cert(11) | cert(31) | **16@34** |
| one-sided (128, 64, 8, 35) | 35@79 | cert(54) / cert(52) | cert(36) / cert(33) | cert(25) / cert(24) | cert(63) | **10@71** |
| balanced (128, 64, 8, 70) | 70@71 | cert(45) / cert(46) | cert(28) / cert(29) | cert(19) / cert(16) | cert(64) | not certified, none found |
| one-sided (128, 64, 16, 6435) | all@71 | cert(49) / cert(47) | cert(33) / cert(31) | cert(24) / cert(22) | cert(63) | **34@66** |
| one-sided (256, 128, 8, 35) | 35@159 | cert(106) / cert(99) | cert(72) / cert(69) | cert(47) / cert(48) | cert(127) | not certified, none found |
| balanced (256, 128, 8, 70) | 70@143 | cert(88) / cert(87) | cert(53) / cert(52) | cert(31) / cert(37) | cert(128) | not certified, none found |
| one-sided (256, 128, 16, 6435) | all@143 | cert(92) / cert(93) | cert(57) / cert(63) | cert(40) / cert(38) | cert(127) | **33@132** |
| one-sided, 4 free blocks (256, 128, 16, 64) | 64@144 | cert(85) / cert(84) | cert(49) / cert(49) | cert(32) / cert(32) | cert(63) | not certified, none found |
| rate 1/4, one-sided (256, 64, 16, 1365) | all@79 | cert(35) / cert(51) | cert(16) / cert(35) | cert(8) / cert(7) | cert(63) ($M, M^2, M^3$) | **81@67** |
| rate 1/4, balanced (256, 64, 8, 28) | 28@87 | cert(29) / cert(20) | cert(10) / cert(8) | cert(2) / cert(7) | cert(64) | **11@82** |

Reading.
- **V1 kills every known list, at every size, with a wide margin (exact).** The largest number of leaves at which a member still shares its symbol with another is $0.83\,k$ at $n = 256$ for $d = 1$ (106 of 128; (P1) predicts about $(\rho + 1/N)^2 n + $ fluctuations), $0.56\,k$ for $d = 2$, $0.37\,k$ for $d = 3$. The margin of $d = 1$ at rate 1/2 is not large: $r_S/k \approx 2(\rho + 1/N)^2$ at rate 1/2, which is $0.78$ at $N = 8$ and would exceed 1 for a member of density above $0.707$, for instance the three-member list at $3/4$; there the certificate would not apply and the exact enumeration decides: it is dead too (the three-member list at $3n/4 - 1$ has V1 weight 41 against the gS bound 63 at $n = 64$, and over the 52 lists the best sub-list is 18 below the gS weight), because a leaf counts only when the same pair of members agrees at the leaf and at its partner.
- **V2 with `up`, `dn` or `ud` kills them too**, but only just in the certificate's terms: tree 0 is a plain tree, so a member keeps its tree-0 agreements ($r_S$ up to $k - 1$, and $k$ for the one member that interpolates all of tree 0). Nothing here says V2 `up` is lift-free: these message lists are not adapted to it. Section 5 builds the adapted ones.
- **V2 `cr` is not lift-free**: an index change that leaves most bits untouched keeps products in the untouched variables. At rate 1/4 its powers also repeat ($M^3 = I$), so two trees read the table identically. Any V2 matrix must mix every level, and at rate 1/4 the $M_t M_s^{-1}$ must all do so.
- V1 on V2 leaves no shared symbol at all for these lists.

## 5. Experiment 5: attacks

### 5.2 (b) Structured candidates for V1

**Sets closed under the partner maps (proved, (P2); exact checks in Section 3.1).** On a closed set V1 is the tree code, so a tree list whose classes are constant on the orbits survives. With the partner = the sibling leaf, or a permutation inside each half tree, the scan of Section 3.1 gives back all 48 deficient patterns of T2. For a uniformly random permutation the leaves in cycles of length at most $\ell$ number about $\ell$ in expectation whatever $n$, and a longer cycle crosses blocks of every class, so closed sets carry $O(1)$ leaves of any block-aligned list: nothing at $n \ge 64$. The scans with fixed points and 2-cycles present (54 of 200 partner maps at $(4,8)$) show no deficient pattern either.

**Product messages on unions of blocks adapted to the partner maps (exact maximum of a combinatorial bound, measured over partner draws).** Script `scripts/78_e5_adapted.py`, output `scripts/78_e5_adapted_output.txt`. By (P1) a lift $A_l \otimes B$ encoded by V1 has at leaf $x$ the class $C'(x) \cap C'(\pi_1 x) \cap \dots$, with $C'(x)$ the class of the block of $x$ in the top list, or all members at a zero of $B$. So the largest V1 weight of a lift at a scale of $N$ blocks is a maximum over top patterns and zero sets that depends on the partner maps only. The script maximizes it knowing the partner maps: every top pattern at $N = 4$ for 3 and 4 members, hill climbing otherwise, the $2^i - 1$ zeros on the best path $x, \pi x, \pi^2 x, \dots$ and then moved leaf by leaf; the top pattern is only required to have pairs sharing at most $k_{\rm up} - 1$ blocks and top weight at most note 74's conjectured maximum, so the value is an upper bound for lifts. Result, as the best weight divided by $Lk$ (a lift beyond gS needs a ratio of at least 1), over 6 partner draws ($d = 1$) or 4 ($d = 2$), 3 to 5 members, $N = 4, 8, 16$:

| $(k, n)$ | V1 $d = 1$ any | V1 $d = 1$ cross | V1 $d = 2$ cross |
|---|---|---|---|
| (32, 64) | 0.75 to 0.87 | 0.56 to 0.84 | 0.34 to 0.54 |
| (64, 128) | 0.72 to 0.82 | 0.55 to 0.83 | 0.38 to 0.50 |
| (128, 256) | 0.70 to 0.81 | 0.57 to 0.80 | 0.34 to 0.47 |
| (64, 256), rate 1/4 | 0.53 to 0.69 | 0.48 to 0.70 | |

**No adapted lift reaches the gS weight; the best is 13 percent below it at $n = 64$ and 19 percent below at $n = 256$ for $d = 1$, about half for $d = 2$** (the largest values are at the finest scale tried, $N = 16$, where the adversary has the most freedom to follow the partner map). Scales finer than $N = 16$ were not run; there a set of blocks strung along a path of the partner map has one leaf per block with its partner inside, that is about one agreement per top condition plus the random share, against the $2^i$ a lift needs (estimated).

**Messages supported where the mixing is degenerate.** The only degeneracies of the mixing at a leaf are a partner equal to the leaf or in a 2-cycle with it (covered above) and a zero coefficient, which the construction excludes. A planted coincidence makes whole groups of leaves proportional on a family: Section 5.3.

### 5.2 bis (b) Structured candidates for V2: products for both variable systems (proved mechanism, exact checks)

**The mechanism.** In characteristic 2 the table of a multilinear polynomial is an element of the group algebra $K[\mathbb F_2^v]$ (monomial $X^e \leftrightarrow e$), a product of polynomials in disjoint variables is the product in that algebra, and tree 1 of V2 reads the image under the algebra automorphism induced by $M$. So a product stays a product whenever the supports can be rearranged: for a subgroup $S \subseteq R = V_i \cap M^{-1}V_j$ ($V_i$ the low $i$ bits, $U_i$ the others) with $M U_i \subseteq U_j + MS$, every message $A(X_{\rm up}) \cdot \mathbb 1_S \cdot B_1$ ($B_1$ supported on $R$) is $A \otimes B$ for tree 0 at level $i$ and $A' \otimes B'$ for tree 1 at level $j$: a lift with $|R|/|S| - 1$ prescribable common zeros (a tree code has $2^i - 1$). `scripts/78_e5_products.py` enumerates these families. For `up` and `dn` it finds a lower-factor space of dimension $2^{i-1}$ at every level $i$ (half of the tree code's); for `ud` dimension 1 at level 2, $2^{v-3}$ at the top level when $v$ is odd, nothing at the other levels up to $v = 5$. **Every $M$ with $M_{v-1,v-1} = (M^{-1})_{v-1,v-1} = 1$ has such a family at the top level with lower factors of dimension at least $2^{v-3}$** (proved: $R$ has dimension at least $v - 2$ and $S = \langle u + M^{-1}u \rangle$, $u = e_{v-1}$, works), and a matrix with both entries 0 is not MDS (P4): only the matrices with exactly one of the two entries equal to 1 can avoid a top-level family. Of the 13707 MDS matrices of $\mathrm{GL}_4$, 5466 have no family of this kind with lower-factor dimension 2 or more; but the enumeration is not complete: `cr` is one of the 5466 and Section 4 shows it keeps lists (products of three factors, top and bottom variables against the middle ones).

**An adapted staircase for V2 `up`, checked by encoding (exact at the stated sizes).** `scripts/78_e5_v2stair.c`, output `scripts/78_e5_v2stair_output.txt`: lower factor $B$ with $B_e = B_{\bar e}$ ($\bar e$ = all $i$ low bits complemented) and $2^{i-1} - 1$ zeros in one block, the top code read off the encoder (the block values are constant on blocks in both trees: 0 exceptions), members = interpolants of a random block word through the $k_{\rm up}$-subsets of the other $N - 1$ blocks.

| $(k, n)$ | $N$ | members | agreement of every member | gS value | the tree code's one-sided staircase |
|---|---|---|---|---|---|
| (32, 64) / (64, 128) / (128, 256) | 8 | 35 | 35 / 71 / 143 $= k + n/16 - 1$ | 32 / 65 / 131 | 39 / 79 / 159 |
| (64, 128) / (128, 256) | 16 | 6435 | 67 / 135 $= k + n/32 - 1$ | 64 / 128 | 71 / 143 |

**So V2 `up` has $\binom{N-1}{N/2}$ codewords at agreement $\rho + 1/(2N) - 1/n$: the staircase of the tree code with the excess over capacity halved**, that is $\log_2 \Lambda \approx 1/(2\varepsilon)$ instead of $1/\varepsilon$ at rate 1/2. The same $B$ gives no product family for `dn` or `ud` (control: block values not constant), which have their own invariant spaces.

**Small lists of V2 beyond gS at growing size (exact rank checks, `scripts/78_lift.py` and `78_e3_scan` in file mode).** The 36 deficient patterns of `up` at $(8, 16)$ lifted by 2, 3, 4 layers with $2^{i-1} - 1$ common zeros: three codewords of weight 66 at $(32, 64)$ (gS 63), 134 at $(64, 128)$ (gS 127), 270 at $(128, 256)$ (gS 255), with rank deficiency 3, 5, 6 (so 2, 4, 5 more constraints can be added); balanced agreement 42, 85, 171 against gS values 42, 85, 170. **`ud` is deficient on the same patterns at $(64, 128)$** (deficiency 2, a list of weight 134 against 127) and not at $(32, 64)$ or $(128, 256)$: the clean exhaustive scan of `ud` at $(8, 16)$ does not extend to all sizes. Rank-one tensors $\prod_i (X_i - a_i)$ are the tree code's full products; with an MDS $M$ they cannot have $k$ zeros, and they give lists only through the families above. Functions $e \mapsto c^{\ell(e)}$ of a linear form $\ell$ are not products for either tree unless $\ell$ is a coordinate (in characteristic 2 a product needs $c^2 = 1$), and were not pursued.

### 5.3 (c) Planted coincidences in the top twiddles (exact at the stated sizes)

Script: `scripts/78_e5_coinc.c`, output `scripts/78_e5_coinc_output.txt`. As in note 69 Section 8: depth 1 = two equal top twiddles in trees 0 and 1; depth $j \ge 2$ = one vanishing minor of the top code of the top $j$ layers on $2^j$ random blocks (for V2 `up` the top code is read through the action of $M$ on the top bits). $F$ is the family that vanishes on the $k$ planted leaves in the unmixed code. "Waste" of a leaf set $Z$ is $\min(|Z|, k) - \mathrm{rank}$. Three searches: the set $Z'$ where all of $F$ vanishes in the variant; $Z'$ plus the largest groups of leaves whose functionals on $F$ are proportional (they cost $F$ one condition together), up to $k$ leaves; 40000 random leaf sets (unions of blocks, partner closures, subsets of $Z'$, random leaves).

Largest waste found, depth 1, at $(k, n) = (16, 32)$ / $(32, 64)$ / $(64, 128)$ / $(128, 256)$, and at rate 1/4 $(32, 128)$:

| code | $\dim F$ | waste at rate 1/2 | at $(32, 128)$ |
|---|---|---|---|
| T2 | $k/2$ | 8 / 16 / 32 / 64 = $k/2$ | 16 |
| V1 $d = 1$ any | $k/2$ | 4 / 7 / 14 / 30 $\approx k/4$ | 0 |
| V1 $d = 1$ cross | $k/2$ | 3 / 7 / 15 / 31 $\approx k/4$ | 8 (the shift pairs trees 0 and 1 in this draw) |
| V1 $d = 1$ cross, no 2-cycles | $k/2$ | 3 / 8 / 14 / 31 $\approx k/4$ | 0 |
| V1 $d = 2$ any, cross; $d = 3$ cross | $k/2$ | 0 / 0 / 0 / 0 | 0 |
| V2 `up` | $k/4$ | 4 / 8 / 16 / 32 = $k/4$ | 8 |
| V2 `ud` | 0, $k/8$, 0, $k/8$ | 0 / 4 / 0 / 16 | 4 |
| V1 ($d = 1$, cross) on V2 `up` | $k/4$ | 0 / 0 / 0 / 0 | 0 |

Depth 2, 3, 4 (same sizes): T2 wastes one block ($k/2^j$), V2 `up` half a block ($k/2^{j+1}$), every V1 code and V1 on V2 nothing.

- **V1 with $d = 1$ halves the waste of the worst coincidence, it does not remove it (proved mechanism, exact checks).** With $B$ the $k$ planted leaves: $F$ ($\dim k/2$) vanishes in V1 on $Z' = B \cap \pi^{-1}B$, about $k/2$ leaves; and for $x \in B$ with $y = \pi(x) \notin B$ and $\pi(y) \in B$, the two V1 leaves $x$ and $y$ both read $F$ through the single functional $c \mapsto c(y)$. There are about $k/4$ such pairs: $Z' \cup$ pairs has $k$ leaves and nullity $k/4$. The random search missed this (it found 2 to 7). So for V1 $d = 1$ the event "two equal top twiddles across trees" still costs relative distance $1/8$ at rate 1/2 (T2: $1/4$): the top of a V1 code must be checked like a tree code's. For $d = 2$ the same count gives no waste ($|Z'| \approx k/4$ and too few proportional groups), and none was found.
- **V2 `up` keeps half of every coincidence** (the lower-factor space of (P5) has half the dimension), at every depth. **V2 `ud` keeps a quarter at depth 1 when $v$ is odd and nothing when $v$ is even**: its two-sided products at the top level exist only for odd $v$ (`scripts/78_e5_products.py` finds a lower-factor space of dimension $2^{v-3}$ at level $v - 1$ for $v = 5$ and none for $v = 4$). So no V2 matrix tested is product-free at every $v$.

## 6. Verdict table

(pending)

## 7. Reproduction

From `doc/whir_soundness_gap_notes/scripts`, with note 69's headers (`69_gf.h`, `69_tree.h`, `69_pat.h`, `69_lin.h`), its `69_lift.py` and `69_lift_output.txt` present. Build: `mkdir -p 78_bin 78_tmp; for f in e1_check e2_mds e3_scan e4_lists e5_climb e5_coinc e5_v2stair profile; do cc -O2 -DFB=64 78_$f.c -o 78_bin/$f; done`. Binaries and `78_tmp/` are not needed to read the note. Every run is under fifteen minutes on four cores.
- Experiment 1: `78_bin/e1_check 1 U T2 T2:d1a ...` (the 21 specs of `78_e1_output.txt`).
- Experiment 2: `78_bin/e2_mds all 2 1 200 <specs>`, `all 2 2 100`, `all 3 1 20`, `rand 4 1 4 500000 <specs>` (`78_e2_output.txt`); `78_bin/e2_mds gl v part nparts list` for $v = 2, 3, 4$ (four parts at $v = 4$, about three minutes; `78_e2_gl_output.txt`).
- Experiment 3: `78_bin/e3_scan full 2 1 2 0 1 <seed> out U T2 <specs>` (three members, seeds 1 to 21), `full 2 1 3 <part> 4 31 ...` (four members, four parts, 5 minutes), `trees 3 1 2 <part> 4 41 out U T2 T2:Mup T2:Mdn T2:Mud 'T2:M#85'` (12 minutes), `sample:250000 3 1 2 <part> 4 61 ...`, `trees 2 2 2 <part> 4 71 out U T2 'T2:M#7' T2:Mup` (14 minutes), `sample:250000 2 2 2 <part> 4 62 ...`; kernel profiles `78_bin/profile 3 1 41 T2:Mup <pattern file>`.
- Experiment 4: `./78_e4_run.sh` (6 seconds).
- Experiment 5: `./78_e5_run.sh small`, `./78_e5_run.sh large` (adaptive search); `python3 78_e5_adapted.py v r d a|x nseeds`; `python3 78_e5_products.py v up dn ud ...` and `python3 78_e5_products.py all4 78_e2_gl_output.txt`; `78_bin/e5_v2stair v r lo want seed T2:Mup`; `python3 78_lift.py members lo nzeros` then `78_bin/e3_scan file:<lifted> ...`; `78_bin/e5_coinc v r depth seed <specs>`. `78_mat.py` prints the packed code and the structure flags of a named matrix.
