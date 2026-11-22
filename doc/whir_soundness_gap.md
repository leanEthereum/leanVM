# The WHIR soundness gap in leanVM

How far can leanVM's WHIR query counts go down? This note states the question as one number per WHIR level, an agreement threshold, with a proven side (a threshold at which soundness is proved) and an attack side (a threshold at which the protocol is broken). The research goal is to close the interval between the two. It is about the protocol of Annex B of `doc/leanvm` and its Lean proof in `formal/lean_vm/LeanVM/Protocol/Whir/Sound`. The working notes behind every claim are in `doc/whir_soundness_gap_notes/` (start with `09-round1-synthesis.md`); each statement there is marked proved, checked numerically or conjectured.

## 1. Why one number per level sets the queries

A level of WHIR has an agreement threshold $A$ out of a block length $n$. Its query message has error $((A-1)/n)^t$ for $t$ queries (Annex B, `thm:rbr`). With the 17-bit query grind and the $2^{-125}$ target, a level needs

$$t = \left\lceil \frac{108}{\log_2\bigl(n/(A-1)\bigr)} \right\rceil .$$

So the whole question is how small $A$ can be. For a code of rate $\rho$:

| regime | threshold $A/n$ | bits per query |
| --- | --- | --- |
| Johnson (what we prove today) | $\sqrt\rho$ | $\tfrac12\log_2(1/\rho)$ |
| capacity (a hard limit) | $\rho$ | $\log_2(1/\rho)$ |

The deployed counts (`crates/verifier/src/whir.rs`, `WHIR_QUERIES`) are within one to seven queries of the Johnson limit per opening, so nothing is left inside the Johnson regime. Capacity at rate $\rho$ gives exactly what Johnson gives at rate $\rho^2$.

## 2. The setting

- Fields: $K = \mathbb{F}_2[x]/(x^{64}+x^4+x^3+x+1)$ and $E = K[y]/(y^2+xy+1)$, $|E| = 2^{128}$.
- Domain: $D_{\kappa,R} \subset K \subset E$ is the $\mathbb{F}_2$-span of $1, x, \dots, x^{\kappa+R-1}$: an additive subgroup of $n = 2^{\kappa+R}$ points.
- Code: polynomials over $E$ of degree below $k = 2^\kappa$ evaluated on $D_{\kappa,R}$, interleaved over any number of lanes. A level with $\ell$ fold rounds analyses every round at the degree bound $d = 2^\kappa - 1 + \ell$; a cheating prover can use that slack.
- Fold: the affine combiner of [CWYZ26]: lanes $(f_0, f_1)$ become $f_1 + (\alpha + \beta x) f_0$ for $(\alpha, \beta) \leftarrow E^2$.
- Ladder (`derive_config`): level 0 has $\ell = 6$ and rate $2^{-R}$ for $R \in \{1,2,3,4\}$; each later level has $\ell \le 4$ and a rate $2^{-3}$ lower than the one before. Level 0 dominates: most queries, and $2^6$ lanes per opened leaf.
- Budgets: every verifier message has error at most $2^{-125}$ after its grind (7 bits for a fold round, 13 for level 0's batching, 15 for an OOD point, 17 for a query message).

## 3. The problem

Let $\Lambda(T)$ be the largest number of polynomial tuples of degree at most $d$ agreeing with one interleaved word on at least $T$ points.

### 3.1 What makes a threshold unsafe

An attack under Fiat-Shamir is a path through the rounds; it costs between the maximum and the sum of its per-message costs $2^g/p$ ($g$ grinding bits, $p$ escape probability), and it ends with a query round against a codeword that agrees with the committed word on some $T$ points, costing $2^{17}(n/T)^t$.

A list of $L$ codewords at agreement $T$ lets the prover switch to a member that satisfies a false claim at the first fold round, with probability about $L/|E|$, by a table lookup. So a list at agreement $T$ breaks the protocol when the threshold is at or below $T$ and $L > 2^{g+3}$. Lists below the threshold are harmless, because the query round alone already costs the full $2^{125}$. At rate 1/4 this attack is real as soon as level 0 has 107 queries or fewer (we deploy 109).

Grinding cannot pay for big lists: a budget of $2^{16}$ costs 1.24 times today's grinding work, $2^{20}$ costs 8 times, $2^{26}$ about 450 times.

### 3.2 What a proof needs today

Today's analysis is safe at $A$ when, with $L = \Lambda(A - \ell)$: the fold rounds have $2L/|E| + \Gamma_{\mathrm{un}} \le 2^{-118}$, where $\Gamma_{\mathrm{un}}$ is the density of challenges whose fold has a close polynomial not explained by a close pair (mutual correlated agreement); level 0's batching has $513\,L/|E| \le 2^{-112}$; and the OOD point has $\binom{L}{2}\nu/|E| \le 2^{-110}$. The binding list budget is about $2^7$. Beyond the Johnson radius no bound on $\Lambda$ or on $\Gamma_{\mathrm{un}}$ is known, and $\Gamma_{\mathrm{un}}$ is provably large for pole-pair words.

### 3.3 The reduced problem

A protocol change, the DEEP fold (`07-protocol-redesign.md`, Theorem 3; proved on paper, toy-checked, under independent review), removes $\Gamma_{\mathrm{un}}$ and the list factors: the prover answers $s$ univariate out-of-domain evaluations of the two halves before each level's fold challenges, and these claims stay unbatched through the level. The fold round's error becomes about $2.72/|E|$ at any threshold. Estimated prover cost: a few percent of proving time (each point is one more pass of the kind the level-0 OOD evaluation already does).

What remains is a statement about the code alone:

> **ListBound$(\rho, \tau, b)$:** every interleaved word on $D$ has at most $2^b$ polynomial tuples of degree at most $d$ within agreement $\tau n$,

with $b$ as large as 40 to 100 (about 35 bits per extra point). A lower certificate is a proof of ListBound at some $\tau < \sqrt\rho$. An upper certificate is an explicit word with a list above the budget.

## 4. What is known (level 0, $\mu = 30$)

| rate | proven: deployed $t$ | largest $T/n$ with a list $\ge 2^{10}$ | attack floor $t$ | status |
| --- | --- | --- | --- | --- |
| 1/2 | 218 | $5/8$ ($2^{30.8}$ members); $0.629$ (about $2^{10}$) | 160 | open on the proof side |
| 1/4 | 109 | $1/2$ (flats, $2^{26}$) | 108 | closed on subspace domains |
| 1/8 | 73 | $1/4$ (flats, $2^{51}$) | 54 | open |
| 1/16 | 55 | $1/8$ (flats, $2^{77}$) | 36 | open |

- **Flats.** For a subspace $V \subseteq D$ of size $2k$, the locator $L_V$ is linearized, so $x^{2k-1}$ agrees with a codeword on $V \setminus \{0\}$, for every such $V$. At rate 1/4 this is $n - 1$ codewords at agreement $n/2 - 1$, exactly the Johnson radius.
- **Rate 1/2.** The word $L_U^5$ with $|U| = n/8$ agrees on $5n/8$ points with $56n - 392$ polynomials of degree at most $n/2$ (unions of flats; from the height-two trees of [DKTZ26], found three times independently, and the full list of that word at $n = 32$). Above $5n/8$ only a family of about $2^{10}$ at $0.629n$ is known. Nothing is known between $0.63n$ and $n/\sqrt2$ on any binary domain.
- **Rigidity on generic domains.** If the basis of $D$ is algebraically independent, families of sets whose locators share their top have at most $1/(2\tau - 1)^2$ members above $5n/8$ at rate 1/2, and at most 11 and 8 in the windows at rates 1/8 and 1/16 (three independent proofs). Two sets share $e_1, \dots, e_{2^{a+1}-1}$ exactly when their Walsh spectra agree modulo $2^{a+2}$.
- **The real domain is not generic.** Nothing is proved there for all words. At toy sizes its lists exceed the generic ones by a small bounded factor, and a 64-bit field is small enough for non-generic families of about $2^{30}$ at rate 1/4, $T = 3n/8$ (predicted).
- **No positive result beyond Johnson** in the literature applies to binary subspace domains: the known ones need characteristic above the degree, or random or specially built non-additive points.

Over the whole opening at $\mu = 30$, reaching the attack floors would give about 0.70, 0.80, 0.66, 0.60 times today's bytes at rates 1/2, 1/4, 1/8, 1/16.

## 5. What does not help

- Higher-degree combiners ($\alpha + \beta x + \gamma x^2$ and beyond), multi-lane combiners, challenges in a field larger than $E$: every polynomial combiner collapses onto one scalar under a pole pair, and the binding terms are unchanged.
- Folded Reed-Solomon and other capacity-achieving codes with bundled symbols: provable today, but a leaf carries 64 lanes times the folding parameter, so bytes and hashes grow by an order of magnitude; squaring the level-0 rate dominates them. Multiplicity codes in characteristic 2 are interleaved Reed-Solomon in disguise.
- Counting with pairwise intersections, pinning points, restricted Guruswami-Sudan interpolation, folded-style interpolation along translations (see `04-list-bounds-beyond-johnson.md`, section 4, for the full list of dead ends).

## 6. What is available without new mathematics

A validated model of the parameter search (`08-parameter-retuning.md`; it reproduces `WHIR_QUERIES` at all 60 shapes) gives, for the opening at rate 1/2 and a full stack:

- constants only (`RESIDUAL_MAX_LOG = 6`, a level-0 query grind of $\max(17, \mu - 6)$ bits, batch grind 14, OOD grind 16): 5 to 7% fewer bytes, paid in grinding time;
- 32 lanes at level 0 (`INITIAL_FOLDING_FACTOR = 5`): 8 to 13% fewer bytes on a full stack, a shape change in both provers, the three verifiers and `formal/`.

At rates 1/4 and below, the domain can be any union of cosets of the message subspace at the same NTT cost and with Annex B unchanged; with additively independent representatives the flats family at rate 1/4 drops from $2^{26}$ members to 3. This proves nothing, but it reopens rate 1/4 (attack floor about 65).

## 7. Relation to the Proximity Prize

[better.codes](https://better.codes/?track=binary-lower) (repository `proximity-prize/proximity-prize`) runs Lean-checked lower and upper tracks for the toy reduction of [ABF26, §6] on a "leanVM code geometry" profile, which is our tree at `2e6fe21d` (September 2026): a 192-bit field, a scalar combiner, 64 lanes, $n = 2^{21}$, rate 1/2. Its records are 64.00 bits on the lower track (exactly Johnson) and 106.24 on the upper track. It needs families of more than $2^{64}$ bad challenges where we need $2^{10}$, which is why its upper track stops at $9n/16$ and ours reaches $5n/8$.

## References

- [ABF26] G. Arnon, D. Boneh, G. Fenzi. Open Problems in List Decoding and Correlated Agreement. 2026.
- [CWYZ26] A. Chiesa, G. Weissenberg, E. Yogev, K. Z. Zheng. Affine Combiners for Reed-Solomon Proximity Gaps. Cryptology ePrint Archive, Paper 2026/2863.
- [DKTZ26] Dao, Kominers, Thaler, Zheng. Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields. ECCC TR26-237.
- [BKR10] E. Ben-Sasson, S. Kopparty, J. Radhakrishnan. Subspace polynomials and limits to list decoding of Reed-Solomon codes. IEEE Trans. Inf. Theory, 2010.
