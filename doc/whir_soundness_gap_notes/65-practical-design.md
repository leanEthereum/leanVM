# 65. Is there a practical window-mixed design? (round 13, researcher 65)

Status of this file: complete. Every statement carries a label: proved, checked (by a script named next to it), measured (a number taken from a measurement in another note, named), estimated (a model, with its inputs named).

## 0. Verdict

**No version of the window-mixed code beats the proven knobs by a useful margin, even if every statement its proof needs were established; the practical options with proven security are note 08's re-tuning and the rate.** The best provable case is note 66's oracle-random window graph with the ladder proved to rung 8 and 7 partners a position: the opening at rate 1/2 goes from 335.9 to 248.3 KiB (-26%) for +13 to +23% of proving time (3 to 9 more if the extractor needs fold grinds), the prover must hold the level's codeword, and the recursive verifier is 2% slower (6% faster if level 0 alone is mixed, at 255.8 KiB), and that only if the window weights are delegated to a small GKR (designed and counted in Section 1.3: 3.5 KiB and 3 to 5 thousand cycles a level); without the delegation it is 59% slower. At the same prover time the proven knobs give -23% of the opening, and at +32 to +52% they give -34% and a recursive verifier a third faster, which no mixed row approaches. Rungs 4 and 5 (-16%, -20%) sit below and on the proven curve. The reason is structural, not a matter of tuning: a partner that the expansion proof can treat as uniform is a function of about $N$ fresh oracle bits, and decoding them costs the guest 38 cycles a partner, more than the weight chain the delegation removes; the cheaper windows fail on the proof side (a public pool of offsets has no proof of the expansion axiom by the first moment; the Margulis, Gabber and Galil maps have a proved interior fraction of 0.88 where at most 0.6 is needed; local windows with a crude count for the lifted lists need a structure theorem harder than the ladder and 15 partners, the price of the rate). One measured fact goes the other way and is worth keeping: on the Apple machine uniformly random partner rows cost the prover the same as strided ones (0.07 to 0.13 of the encode's field work a partner), so the prover does not need a structured graph. **Proven options, full $2^{30}$ commitment:** configuration C of note 08 (297.1 KiB, -11.6%, about -16% of guest query cycles, about 3% of prover work, available as a parameter change); rate 1/4 at level 0 only (232.1 KiB, -30.9%, +22 to +35%); rate 1/4 (222.6 KiB, -33.7%, recursion -36%, +32 to +52%); C at rate 1/4 (206.5 KiB, -38.5%, about -46% of guest query cycles). The mixed code would become a modest win only with a window graph that nobody has: fewer than 8 partners, a proved interior fraction below about 0.55, and partners computable from the position's index without oracle bits (Section 4). Labels for this paragraph: byte counts are exact in note 61's model; prover time and guest cycles are estimates from measured parts (Sections 1 and 3); the proven options' figures are note 08's (exact in its model) and note 61's (measured).

Scope after the lead's two notes of the day: no conjecture-based option is considered; the design under evaluation is note 66's (windows from a sparse graph, $d$ partners a position, coefficients $\mu$ from the oracle), with the cube and the local windows kept only as reference points. Scripts: `scripts/65_mix_bench.c` (access patterns, output in `65_mix_bench_output.txt`), `scripts/65_expansion.py` (the constants of axiom (W2), output in `65_expansion_output.txt`), `scripts/65_net.py` (the net tables, built on `61_params.py` and `61_ladder.py`, output in `65_net_output.txt`). Notation is note 61's: level 0 at $\mu = 30$ has $\kappa = 24$ message variables, $N = \kappa + R$ index bits, $n = 2^N$ positions; a level-0 query costs the guest about 735 cycle-equivalents today (554 cycles and 22.6 `KECCAK` steps at 8).

## 1. The cost side

### 1.1 Prover: the access pattern does not matter much; the number of partners does

**[measured, `65_mix_bench.c`, Apple M4 Max, standalone kernel, load average 7 to 9, best of 3]** Same buffer and same reference transform as note 61 ($2^{20}$ to $2^{22}$ rows of 40 words of $K$, products accumulated unreduced, one reduction a word). Three ways of choosing $d = 8$ partner rows: note 61's strided $x \oplus 2^j$; uniformly random rows (indices from a cheap hash, software prefetch 16 rows ahead); a product structure (8 random far blocks of $2^8$ or $2^{12}$ rows a block, a random row inside each).

| rows, threads | NTT-shaped transform | strided | uniformly random rows | far blocks and local rows |
| --- | --- | --- | --- | --- |
| $2^{20}$, 1 | 317 ms | 0.46 | 0.73 | 0.58 |
| $2^{20}$, 4 | 75 ms | 0.83 | 0.78 | 0.63 |
| $2^{21}$, 4 | 177 to 242 ms | 0.77 to 1.06 | 0.79 to 0.92 | 0.66 to 0.87 |
| $2^{22}$, 4 | 643 ms | 0.66 | 0.65 | 0.57 |
| $2^{21}$, 4, $d = 5$ | 239 ms | 0.55 | 0.50 | 0.46 |

(ratios to the transform of the same line.) So on this machine, with prefetch, a random partner row costs what a strided one costs once four threads share the memory: **0.07 to 0.13 of the level's encode field work a partner**, whatever the pattern (note 61 had 0.05 to 0.09 for strided access under a lighter load). The product structure is 10 to 20 percent cheaper, not a different regime. Not measured: the pool's 15 threads, any x86 machine (smaller second-level cache, 4 KiB pages unless the allocator's huge pages hold), rows of 64 words. A row is a Merkle leaf of 320 to 512 bytes, so one miss buys five to eight cache lines; that is why random access is affordable here.

**Added proving time [estimate from measured parts; shares of `Prove` = 590 ms on the 900-signature benchmark at rate 1/2; note 61's split: encode field work 57 to 77 ms at level 0, 75 to 99 ms at levels 0 and 1].**

| item | basis | $d = 5$ | $d = 8$ |
| --- | --- | --- | --- |
| mixing, levels 0 and 1 | $d \times$ (0.07 to 0.13) $\times$ (75 to 99 ms) | 26 to 64 ms, 4.4 to 10.9% | 42 to 103 ms, 7.1 to 17.5% |
| oracle (graph and $\mu$), one Keccak-f a position, levels 0 and 1 | note 61 | 22 to 31 ms, 4 to 5% | the same |
| points, 11 and 8 instead of one out-of-domain point | note 24 | 14 ms, 2.3% | the same |
| total | | **11 to 18%** | **13 to 25%** |
| fold grinds for an efficient extractor at $2^{-125}$ (note 61, 4.4), if required | | 3 to 9% | 3 to 9% |

The whole codeword of a mixed level must be held while it is mixed (note 61, 7.1): 16 GiB at $\mu = 30$ and rate 1/2, which the experimental prover on x86 does not keep today. Fusing with the NTT does not apply to this design: no partner is in the row's own cache block.

### 1.2 Guest and verifier: what a partner costs

The guest computes a query's weight at the terminal point $\varrho$ as $\prod_{k<\kappa}(d_k + W_k(x))$ with the recurrence $W_{k+1} = W_k (W_k + \text{const})$ (`residual_query` in `guests/lean_ethereum.py`): about four operations a variable, 7.6 cycles a variable in note 08's fit with the high part, 145 cycles a query at $\kappa = 24$. The instruction set has `XOR`, `MUL`, `DEREF`, `JUMP`, `KECCAK`: an addition, a product and a table read are one cycle each. Cost of one partner $y$ of a queried position $x$, by what the guest knows about $y$ **[counts proved from the formulas; cycle figures are estimates, not a compiled guest]**:

| partner | what the guest does | cycles a partner, $\kappa = 24$ |
| --- | --- | --- |
| $x \oplus \beta_j$, cube direction (note 61) | $j + 1$ changed factors, shared suffix | $2(j+1) + 4$; 756 for all 25 |
| $x \oplus c$, $c$ in a public pool with the constants $d_k + W_k(c)$ tabulated | $\kappa$ additions, $\kappa$ products, plus decoding the pool index from the oracle (6 to 8 bits) | about 60 |
| unrelated position from the oracle | decode $N$ bits (38 cycles, the cost of decoding a query position today), build the point, a full chain | about 140 |
| any of them, with the delegated evaluation of 1.3 | decode, one table sum, two products | about 25 (pool), about 53 (unrelated) |

Two facts decide everything below. First, the weight of a partner is a product over all $\kappa$ variables as soon as its offset has a high coordinate (note 61, 7.2), so a direct evaluation costs at least $2\kappa$ cycles a far partner, and $d = 8$ far partners cost 500 to 1130 cycles on a 735-cycle query. Second, once the product is delegated, what is left is the cost of turning oracle bits into a position: about 1.5 cycles a bit with the guest's window decomposition. A partner that is uniformly random among $2^{25}$ positions needs 25 fresh bits, and nothing delegates the decoding.

### 1.3 Delegating the window weights: a design concrete enough to count

**What is delegated.** At a mixed level with $Q$ queries the verifier needs $V = \sum_{q,l} M_{q,l} \prod_{k<\kappa} (d_k + W_k(y_{q,l}))$, where $y_{q,0} = x_q$ is the queried position, $y_{q,1..d}$ its partners, $M_{q,l} = \lambda^q \mu_{q,l}$ and $\mu_{q,0} = 1$. Every input is public, so this is the outsourcing of a public computation: no commitment, no new assumption.

**Protocol [design; soundness is the standard GKR argument for a product tree, nothing new to prove about the code].** Index the terms by $t = (q, l) \in \{0,1\}^a$, $a = \lceil\log_2 Q\rceil + \lceil\log_2(d+1)\rceil$, pad the factors to 32 with ones and the terms with $M = 0$. The prover sends $V$. Five layers of a binary product tree follow, each one sumcheck of degree 3 ($\mathrm{eq} \cdot F_{\text{left}} \cdot F_{\text{right}}$, the top one with $M$ in place of $\mathrm{eq}$), with $a, a+1, \dots, a+4$ rounds, two claimed values and one merging challenge between layers. It ends with one claim on the multilinear extension of the leaves at a point $(r_q, r_l, r_k)$, which the verifier evaluates itself. Because $W_k$ is additive in the index bits $y_i$ of a position, $\sum_k \mathrm{eq}(r_k, k) W_k(y) = \sum_i y_i \Omega_i$ with $\Omega_i = \sum_{k \le i} \mathrm{eq}(r_k, k) W_k(\beta_i)$: $N(N+1)/2$ products once a level, then five tables of 32 sums for 5-bit windows, then five table reads a position. This holds for any partner, XOR-related to $x$ or not.

**Counts [proved from the design; cycles estimated].**

| quantity | value |
| --- | --- |
| rounds, scalars, bytes a mixed level | $5a + 10$ rounds, $3(5a+10) + 11$ scalars: 70 rounds and 3.5 KiB at $Q \le 256$, $d \le 15$; 65 rounds and 3.2 KiB at $d \le 7$ |
| soundness error | $3/\lvert E\rvert = 2^{-126.4}$ a round, $1/\lvert E\rvert$ a merge: inside $2^{-125}$ with no grind |
| guest, fixed a level | rounds at 30 to 40 cycles and a third of a `KECCAK` step each, $\Omega$ and its tables (about 1150), the $\mathrm{eq}$ tables (300 to 550): **3 to 5 thousand cycle-equivalents** |
| guest, a query | $2(d+1) + 3$ for $\widetilde M$, $13(d+1)$ for the leaves, one `KECCAK` step for the oracle while $d(N + 64) \le 1088$, plus the decoding of the partners; minus the chain it replaces, $7.6\kappa - 37 = 145$ |
| prover | about $2^{18}$ products of $E$ a level: under 1 percent of `Prove` **[estimate]** |

**What it gives, a level-0 query at $\kappa = 24$, $N = 25$ [estimate], against 735 today:**

| window | direct evaluation | delegated |
| --- | --- | --- |
| cube, 25 partners (no oracle bits for positions) | +756 | about -60 |
| $d = 8$ uniformly random partners (25 oracle bits each) | about +1130 | **+305** (+41%) |
| $d = 5$ uniformly random partners | about +710 | **+146** (+20%) |
| $d = 8$ partners from a public pool of 64 to 256 offsets | about +500 | +81 (+11%) |

So the delegation does remove the recursion penalty of every window whose partners are a fixed function of the position (the cube would even become cheaper than today's query), and it cuts the penalty of oracle-random partners four times, down to the cost of decoding them: 38 cycles each, 304 a query at $d = 8$, more than the chain the delegation removes. That last part is not a detail of this design. A partner that the proof of (W2) can treat as uniform must be a function of about $N$ fresh oracle bits, and the guest pays for every bit it turns into a table index. Applied to today's protocol alone (no mixing, the high part kept as it is) the delegation would save about 6 percent of the level-0 query cycles for 2.5 KiB a level **[estimate]**: not worth a protocol change by itself.

## 2. The protection side

Axiom (W2) of note 66: every set $Z$ of at most $\varphi_0 n$ positions has at most $\gamma |Z|$ interior points (points whose whole window lies in $Z$). The free configurations of the ladder are excluded when $\gamma \le 1/2$ at rate 1/2 (note 66's crude bound, any rung) or when $\Phi(\gamma\rho\binom t2) \le g_t(\alpha_t)$ (note 60's Proposition 3.7 read as a threshold, rung by rung; for large $t$ it tends to $\sqrt{\rho\gamma} \le \alpha_t$). Constants below are from `65_expansion.py` **[checked]** unless marked.

### 2.1 Which realizations of "d partners" satisfy (W2) by an argument we have

| realization | $\gamma$ at density 1/2, 1/4 | by what argument | prover, a partner | guest, a partner (delegated) |
| --- | --- | --- | --- | --- |
| (a) $d$ uniformly random positions from the oracle | $d = 4$: 0.716, 0.531; $d = 6$: 0.500, 0.349; $d = 8$: 0.369, 0.254; $d = 12$: 0.232, 0.162 | note 66's first moment over the $2^n$ sets: exact, $2^{-128}$ from $n = 2^{20}$ on **[checked: E1]** | 0.07 to 0.13 of the encode's field work **[measured]** | 53 (38 of them decoding) |
| (b) $x \oplus c$, $c$ one of $p$ public offsets, $d$ of them chosen by the oracle a position | subspaces: $s^d$ with $s$ the largest share of the pool in a hyperplane, 0.05 to 0.32 at $d = 8$ for $p = 256$ to 64 **[estimate: E4]**; all sets: nothing useful for $p$ below about 2000 | the first moment fails: a point is interior with probability (its share of pool neighbours in $Z$)$^d$, not $\varphi^d$, and the union over $2^n$ sets needs that below about $2^{-4}$ on the $\gamma|Z|$ most favourable points of every $Z$; the spectral bound gives that only for pools of small bias, thousands of offsets **[proved: the obstruction; E4]** | as (a) | 25 |
| (c) product: $d$ random far blocks a block, a random row inside each | block unions: as (a) with $n$ the number of blocks, so 0.41 instead of 0.37 at $2^{10}$ blocks; all sets: open (a two-level large deviation) | block level proved by the same first moment **[checked: E1 at $n = 2^{10}, 2^{12}$]** | 10 to 20% below (a) **[measured]** | as (a): the position still takes $N$ oracle bits |
| Margulis, Gabber and Galil maps on index pairs, 8 partners | at most 0.877, 0.826 | Tanner's bound with $\lambda \le 5\sqrt2/8$ **[proved given the eigenvalue bound, which I quote from memory]** | strided, as measured | about 28 (index arithmetic, no oracle bits) |
| cube, 25 partners | 0.69, 0.55 (note 60, Harper) | exact | 25 partners | 2 (no oracle bits) |
| low $t'$ directions (local window) | 1 for unions of blocks | none: Section 2.3 | $t'$ partners | 2 |

Reading. (i) Only (a) has a proof of (W2) with the constants the ladder needs, and it is the realization with the most oracle bits a partner. (ii) The pool is what the guest wants and what the first moment cannot certify. The obstruction is not the hyperplanes (a pool of 128 to 256 random offsets handles those, and a pool taken from a code of relative distance 0.35 handles them with margin) but the sets that are neither subspaces nor generic, for which one would need a robust vertex-isoperimetric inequality on the Cayley graph of the pool. I do not know one with usable constants. (iii) The product structure buys the prover 10 to 20 percent and nothing for the guest; since random rows already cost what strided rows cost, it is not worth a harder lemma. (iv) Explicit expanders have proved constants that are far too weak: an interior fraction of 0.877 where the ladder needs at most 0.6 to 0.7, that is an interior loss of 0.12 against 0.31 for the 25-cube and 0.63 for the random graph with 8 partners (the vertex-expansion constants of the original papers, $(2 - \sqrt3)/4$ for five maps, give less still). A Ramanujan graph of degree 12 to 16 would give 0.47 to 0.38 by Tanner with no oracle bits for the positions, but I know no such family on $2^N$ points with index maps the guest can evaluate cheaply. (v) A fixed XOR pool used in full by every position (a Cayley graph) reaches $\gamma \le 0.40$ by Tanner when the pool code has all weights in $[p/4, 3p/4]$, which needs $p$ of about 100 to 140 offsets at $N = 25$: four to five times the cube's prover cost.

**The product structure in more detail [proved for the three closed families; the constant is E1 at block level].** With one far block a block, the far map is a random functional graph on the blocks and any union of its components is closed: $\gamma = 1$. With $d$ far blocks a block but the partner at the same row inside each, every set defined by the row index alone (the same subset of every block) is closed: $\gamma = 1$ again. So the product needs both $d$ distinct far blocks a block and a fresh random row a position inside each. Then a union of blocks of density $\varphi$ has interior fraction at most $\gamma(d, \varphi, n'')$ with $n''$ the number of blocks (0.406 at $d = 8$ and $2^{10}$ blocks, against 0.369), a set with the same density in every block behaves as in the random graph, and the sets in between need a large-deviation bound on two scales that I did not prove.

**The pool in more detail [estimate: E4].** For $p$ random offsets in $\mathbb{F}_2^{25}$ the worst hyperplane holds a share $s \approx 1/2 + \sqrt{N \ln 2 / 2p}$ of them: 0.87, 0.76, 0.68, 0.63 at $p = 64, 128, 256, 512$ (a pool of 32 can lie in a hyperplane entirely), leaving $s^8 = 0.32, 0.11, 0.05, 0.03$ of a hyperplane coset interior at $d = 8$. A pool built from a binary code of length $p$, dimension $N$ and relative distance $\delta$ has $s = 1 - \delta$ exactly. For sets that are not subspaces the union bound over the $2^n$ sets needs the $\gamma |Z|$ points of $Z$ with the largest share of pool neighbours inside $Z$ to have a share of at most about 0.7 on geometric average (at $d = 8$, $\gamma = 1/2$), and the only general tool, Chebyshev with the bias of the pool, gives that from a bias of about 0.14, that is $p$ of about 2000 random offsets, at which size the tables that made the pool cheap for the guest cost more than the queries.

### 2.2 The smallest d a rung can use

The rank needs $d \ge t - 1$. The expansion needs $\gamma(d, \rho) \le 1/2$ at rate 1/2 and about $\rho$ below (note 66's crude bound), or $\Phi(\gamma\rho\binom t2) \le g_t(\alpha_t)$ (note 60's Proposition 3.7 read as a threshold) **[checked: E2]**:

| rate | rung | crude bound | note 60's bound |
| --- | --- | --- | --- |
| 1/2 | 4, 5, 8 | $d = 7, 7, 7$ | $d = 5, 5, 7$ |
| 1/4 | 4, 5, 8 | $d = 9, 9, 9$ | $d = 4, 5, 7$ |

So whether the proofs of researchers 62 and 63 go through note 60's sharp bound or through the crude one decides between 5 and 7 partners at rungs 4 and 5, which is the difference between a recursive verifier that is about as fast as today's and one that is slower (Section 3).

### 2.3 Local windows with a crude count for what they leave unprotected: not a candidate

The brief's item 2 asked whether a window spanning only the low $t'$ directions (cheap for the verifier: $t'(t'+1)/2$ changed factors, and with the delegation 2 cycles a partner) could be rescued by bounding the lists it leaves unprotected, those of plain Reed-Solomon on the quotient $D'' = D/W$ of $n'' = 2^{N - t'}$ points, by the count $\binom{n''}{k''}/\binom{A''}{k''}$.

**The count [checked: N1 of `65_net.py`; points from note 61's `points_needed` for a list of 16 times the count].**

| rate, agreement | $n'' = 64$ | 256 | 512 | 1024 | 2048 | 4096 |
| --- | --- | --- | --- | --- | --- | --- |
| 1/2, 0.6133 (rung 5) | $2^{34}$, 11 points | $2^{145}$, 15 | $2^{292}$, 19 | $2^{587}$, 27 | $2^{1178}$, 44 | $2^{2359}$, 78 |
| 1/2, 0.5777 (rung 8) | $2^{42}$, 12 | $2^{171}$, 15 | $2^{342}$, 20 | $2^{685}$, 30 | $2^{1371}$, 50 | $2^{2745}$, 90 |
| 1/4, 0.3546 (rung 8) | $2^{31}$, 11 | $2^{127}$, 14 | $2^{255}$, 18 | $2^{511}$, 25 | $2^{1024}$, 40 | $2^{2050}$, 70 |

So the count is affordable (at most about 30 points a level, 4 percent of proving time and 2 KiB) for quotients of at most $2^{10}$ points, that is for windows of $t' \ge N - 10 = 15$ directions at level 0.

**Why it does not assemble into a theorem with what we have.**

1. **[proved]** Every polynomial of degree below $k$ is uniquely $\sum_{j < 2^{t'}} g_j(L_W(X)) X^j$ with $\deg g_j < k''$, so Reed-Solomon on $D$ is the $2^{t'}$-fold interleaved Reed-Solomon code on $D''$ up to an invertible map on each column, and the mixing is one more map inside each column. Two members whose columns coincide at a point of $D''$ have equal symbols on the whole block, for every $\mu$.
2. **[proved, note 57 Section 10]** Hence the ladder inequality $H_t$ is false for a local window whenever plain Reed-Solomon on $D''$ has $t$ codewords that violate it: (W2) fails with $\gamma = 1$ on unions of blocks. The statements of researchers 62 and 63 cannot be adapted by changing constants.
3. **What survives of their proofs:** the probabilistic half. With $\kappa_x$ the number of distinct restrictions to the window of $x$ among the members covering $x$, the first moment gives $\sum_x (\kappa_x - 1)_+ \le (t - 1)k + \varepsilon_t n$ for any window containing 0, with the same proof (modulo the count of deficient windows, which becomes a count of rank drops of an interleaved code, block by block).
4. **What would have to replace the deterministic half [target, not proved, and I do not think it is close]:** a two-scale statement of the form "every list of the mixed code at agreement $an$ is covered by at most $M_0$ families, each of which is, block by block, a list of the interleaved code on $D''$ for one word with weights (a block may be split among several column values, the weights summing to at most $1 + \eta$) at agreement $(a - \eta) n''$", which gives lists of at most $M_0\, n''$ times the count above. It does not follow from item 3 by convexity: Proposition J needs a bound on the cover counts $c_x$, item 3 bounds only $\kappa_x$, and a lifted list has $\kappa_x = 1$ everywhere. To split a list into families one needs the first moment stratified by the coincidence pattern of the columns, that is the number of $t$-tuples of interleaved codewords with prescribed rank drops, which is the counting theorem note 57 Section 7 already lists as open; and zero sets that fill blocks only partly bring the isoperimetry of the $t'$-cube back inside each block, with the cube's constants that note 60 found too weak.
5. **And the cost would not be worth it [estimate].** Fifteen partners a position cost the prover 1.05 to 1.95 times the level's encode field work (Section 1.1; partners inside a cache block are not cheaper in note 61's measurement), plus the oracle and 27 to 30 points: 22 to 44 percent of proving time, the price of halving the rate.

So for local windows the answer to the brief's question is: the lifted configurations do break the $t$-wise inequalities, what replaces them is a structure theorem that is harder than the ladder, and even granted it the design costs what the rate costs. Dropped.

## 3. The net

Model: note 61's Protocol D' and ladder levels (`61_ladder.build`: plain fold with a 12-bit grind, constant lists, points 11 8 8 7 7 12 against one out-of-domain point a level today), a level mixed where that saves bytes (levels 0 and 1, and level 2 at rung 8), the delegation's 3.2 to 3.5 KiB a mixed level included, uniformly random partners priced by Section 1, $d$ either 8 (note 66's choice) or the least value of Section 2.2. Full commitment of $2^{30}$. Recursion is note 61's metric (guest cycles of the queries and points plus 8 a `KECCAK` step) against today's at the same rate. Prover time is in percent of today's proving time at rate 1/2 (Section 1.1; a halving of the rate is +32 to +52, measured in note 61); the 3 to 9 percent of fold grinds that an efficient extractor may need are not included. **[N2, N3 of `65_net.py`: byte counts exact in note 61's model; cycles and prover time estimated.]**

**Rate 1/2 (today: 218 queries at level 0, 335.9 KiB).**

| option | status | level-0 queries | opening, KiB | recursion | prover added |
| --- | --- | --- | --- | --- | --- |
| configuration C of note 08 | proven, a parameter change | 203 | 297.1 (-11.6%) | -16% of guest query cycles | about +3%, and a 24-bit grind |
| rate 1/4 at level 0 only ($r_0 = 4$, note 08) | proven | 109 | 232.1 (-30.9%) | not modelled | +22 to +35% |
| rate 1/4 | deployed | 109 | 222.6 (-33.7%) | -36% | +32 to +52% |
| C at rate 1/4 | proven | 102 | 206.5 (-38.5%) | -46% of guest query cycles | +35 to +56% |
| mixed, rung 4, $d = 8$ | needs $H_4$ | 166 | 283.2 (-15.7%) | +18% delegated, +90% direct | +13 to +25% |
| mixed, rung 4, $d = 5$ | needs $H_4$ through note 60's bound | 166 | 282.8 (-15.8%) | +3% delegated, +51% direct | +11 to +18% |
| mixed, rung 5, $d = 8$ | needs $H_5$ | 154 | 269.2 (-19.9%) | +12% delegated, +78% direct | +13 to +25% |
| mixed, rung 5, $d = 5$ | needs $H_5$ through note 60's bound | 154 | 268.7 (-20.0%) | -3% delegated, +42% direct | +11 to +18% |
| mixed, rung 8, $d = 8$ | needs $H_8$ | 137 | 249.0 (-25.9%) | +7% delegated, +71% direct | +13 to +25% |
| mixed, rung 8, $d = 7$ | needs $H_8$ | 137 | 248.3 (-26.1%) | +2% delegated, +59% direct | +13 to +23% |
| mixed, rung 8, $d = 7$, level 0 alone | needs $H_8$ | 137 | 255.8 (-23.8%) | -6% delegated | +11 to +19% |
| C and mixed rung 5, $d = 5$ | estimate: the two savings multiplied | about 143 | about 238 (-29%) | about -18% | +14 to +21% |
| C and mixed rung 8, $d = 7$ | estimate: multiplied | about 128 | about 220 (-35%) | about -14% | +16 to +26% |

Points a level in every mixed row: 11 8 8 7 7 12 (10 at level 0 on rung 8), where today has one out-of-domain point a level. A level-0 query costs the guest 735 cycle-equivalents today; mixed and delegated, 881 at $d = 5$, 987 at $d = 7$, 1040 at $d = 8$; mixed and direct, 1440 to 1860. Were a pool provable (it is not, Section 2.1), the delegated column would read 0, -5 and -9 percent at rungs 4, 5, 8 with $d = 8$.

**Rate 1/4 (today: 109 queries, 222.6 KiB, +32 to +52% of prover time against rate 1/2).**

| option | level-0 queries | opening, KiB | against rate 1/4, against today's rate 1/2 | recursion against rate 1/4, delegated | prover added against rate 1/2 |
| --- | --- | --- | --- | --- | --- |
| mixed, rung 4, $d = 4$ | 88 | 200.7 | -9.8%, -40.2% | +7% | +49 to +82% |
| mixed, rung 5, $d = 5$ | 82 | 192.9 | -13.3%, -42.6% | +7% | +51 to +86% |
| mixed, rung 8, $d = 7$ | 73 | 181.2 | -18.6%, -46.1% | +14% | +55 to +95% |
| rate 1/8, deployed | 73 | 180.7 | -18.8%, -46.2% | better than rate 1/4 | about +97 to +150% |

**Against the same prover time spent on proven knobs.** Between C (+3%, -11.6%) and $r_0 = 4$ (+22 to +35%, -30.9%) the proven options give about -20 percent of the opening at +14 percent of prover time and -23 at +18, by interpolation. The mixed code gives -16 (rung 4), -20 (rung 5) and -26 (rung 8) at those costs: below the proven curve, on it, and three points above it. Stacked on C, rung 8 gives about 220 KiB at +16 to +26 percent, where C with $r_0 = 4$ gives about 214 KiB (estimate: 232.1 less the 7 to 8 percent C saves at rate 1/4) at +25 to +38 percent. On recursion the proven options win everywhere: lowering the rate removes a third of the guest's query work, while the mixed code moves it by between -6 and +18 percent. At rate 1/4 the mixed code at rung 8 matches rate 1/8 in bytes at about 60 percent of its prover cost and loses to it on recursion; that is the one regime where it buys bytes the rate does not sell cheaper, and it is the regime where the codeword it must hold in full is already twice the size.

## 4. What would have to be proved for the best row, and what it would still not give

The only row above the proven curve is rung 8 with $d = 7$ on the oracle-random graph. Its hypotheses, exactly:

1. **Expansion [note 66's lemma; constants checked here, E1].** With probability $1 - 2^{-128}$ over the graph, every set of at most $\rho n$ positions has at most $\gamma(d, \rho)\,|Z|$ interior points: 0.427 at $d = 7$, rate 1/2; 0.295 at rate 1/4; valid from $n = 2^{20}$, and with a loss of 0.01 to 0.04 down to $2^{10}$ points.
2. **$H_8$ and $H_2$ [target; researchers 62 and 63].** With probability $1 - 2^{-128}$ over the graph and $\mu$, for every word and every 8 list members with agreement sets of $A$ positions each, $\sum_x (c_x - 1)_+ \le 7k + (8\,n H(A/n) + 130)/64$; and the same for pairs. This needs, beyond the pencil case that note 66 sketches: the count of deficient windows for every rank up to 7, including the unbalanced lattices with fewer than $u - 1$ short vectors (note 66 calls it the open algebra); the affinely dependent tuples; and the free configurations through note 60's Proposition 3.7 with the graph's $\gamma$ in place of the cube's, which holds at $d \ge 5$ at rate 1/2 **[checked: E2]** (the crude bound would need $d \ge 7$ anyway).
3. **Theorem D' of note 61 [proved by hand there, not formalized]** for the plain fold, with the lanes through the paper's Proposition 6.2, and either a decoder for the extractor or its fold grinds (3 to 9 percent of proving time).
4. **The delegated weights [standard].**

With all of it: 248.3 KiB instead of 335.9, a recursive verifier within a few percent of today's, +13 to +23 percent of proving time, a codeword held in memory, and a change of code, fold, oracle and extractor in two provers, three verifiers and `formal/`. Proving only $H_4$ or $H_5$ buys nothing that configuration C and the rate do not already sell at the same price. Reaching rung 16 would not help either: it gives 221.1 KiB in note 61's table, about 231 with the delegation's bytes, which is what rate 1/4 at level 0 only gives (232.1), and it needs at least 15 partners, +20 to +40 percent of proving time, which is what that knob costs.

**What would change the verdict.** A window graph with three properties at once: a proved interior fraction of at most about 0.55 for sets of density 1/2, fewer than about 8 partners, and partners that are a fixed cheap function of the position's index (no oracle bits to decode). The delegation would then make a mixed query about as cheap as today's query, and the recursion metric would improve by 14 to 22 percent at rungs 5 to 8 (the points and the fixed cost of the delegation keep it from following the query count) **[estimate: the model of Section 3 with 0 to 13 cycles to locate a partner]**. That would be a real, if modest, gain over the proven curve: the bytes of rung 8 and two thirds of the rate's recursion gain at about half the rate's prover cost. The oracle-random graph has the first two and not the third; the cube has the third only; explicit expanders have the last two and a proved constant of 0.88; a full Cayley graph on a pool has the first and third and 100 or more partners. I know no construction with all three.

## 5. Limits of this note

- Guest cycles are counts of operations priced with note 08's fitted constants (38 cycles to decode a position, 7.6 a variable of the weight chain, 8 a `KECCAK` step); no guest was written. If decoding a partner cost 20 cycles instead of 38, the delegated recursion figures of Section 3 would improve by 8 to 11 points (rung 8 with $d = 7$: -9 percent instead of +2; rung 5 with $d = 5$: -10 instead of -3) **[checked with the same model]**, which does not change the comparison with the rate.
- The prover figures come from a standalone kernel at four threads on a loaded Apple machine and from note 61's split of the commitment span. The pool's 15 threads, x86, and the cost of holding a level-0 codeword that the experimental prover does not keep today are unmeasured.
- The rows "C and mixed" multiply two savings computed separately; the model was not rebuilt with 32 lanes. The recursion of $r_0 = 4$ was not modelled.
- The eigenvalue bound $5\sqrt2$ of the 8-regular Margulis graph is quoted from memory (Gabber and Galil 1981); the conclusion only needs that it is far above 0.6.
- The obstruction for pools is an obstruction for the first-moment argument, not a proof that pools violate (W2). For the product structure only unions of blocks were treated.
- I did not check any of the statements of researchers 62 and 63, nor note 60's Proposition 3.7 beyond using it as stated. The conjecture-based option of the original brief was dropped at the user's ruling and is not quantified.
