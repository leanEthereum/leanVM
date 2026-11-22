# 61. Window-mixed codes: the protocol and its cost, with Theorem M as a hypothesis

Researcher 61, round 12. Scope: everything about the protocol and the cost of note 57's proposal, assuming its list bound (Theorem M) and nothing about how it is proved. Labels: **[proved]** by hand in this note (short proofs, given in full), **[paper]** proved or machine-checked in `doc/deep_fold/` (I say which), **[checked]** numerically by a script of this note, **[measured]** wall time on the swarm's machine with the conditions stated, **[estimate]**, **[hypothesis]**. Scripts: `scripts/61_params.py` (all tables; output in `61_params_output.txt`), `scripts/61_toy_checks.py` (five checks; output in `61_toy_checks_output.txt`), `scripts/61_ladder.py` (section 9; output in `61_ladder_output.txt`), `scripts/61_mix_bench.c` (mixing kernel; output in `61_mix_bench_output.txt`), `scripts/61_bench_output.txt` (the traced runs of the real prover). Sections 1 to 8 are about note 57 as it stood in its sections 1 to 6 (Theorem M, lists $q^{L-1}$, the 26-point cube window); section 9 treats the ladder with constant lists that the lead added as its section 8 while this note was being written, and changes the verdict in one case. No file outside `doc/whir_soundness_gap_notes/` was written; the benchmark binary was the one already built in `target/`.

Notation is that of the paper and of note 57: $K = \mathrm{GF}(2^{64})$, $E = \mathrm{GF}(2^{128})$, $q = |E|$ unless said otherwise, level $i$ has $\ell_i$ fold rounds, message size $2^{\kappa_i}$, rate $2^{-R_i}$, $N_i = \kappa_i + R_i$, $n_i = 2^{N_i}$ positions, $k_i = 2^{\kappa_i}$. The window of a position $x$ is $x + C$, $C = \{0, \beta_0, \dots, \beta_{N-1}\}$, $r = N + 1$, and the mixed symbol is $e_x(P) = \sum_{c \in C} \mu(x, c) P(x + c)$.

## 0. Summary

1. **The protocol does not go through as note 57 states it, for four reasons, three of them fixable.** (a) The affine fold $G + (\alpha + \beta X)F$ of Annex B does not commute with the mixing, and no column-wise twist can: a code with one symbol a position that is closed under such a twist is a generalized Reed-Solomon code (section 2). The fold must be the plain $G + \alpha F$, whose error is tight at $n / ((t + 1)q)$ a round for a loss of $t$ columns. With $t = n/2^{13}$ and a 12-bit grind this is free for soundness (section 4). (b) The paper's reductions from interleaved words to single $K$-valued words with a factor 2 need a list below $2^{63}$ or an agreement above $(n + 3d)/4$. Theorem M's list is $2^{64(L-1)}$ and its agreement is below that threshold for $L \ge 4$, so neither applies; what the protocol needs is the bound for $E$-valued words with up to 64 lanes. I give a reduction that uses Theorem M at several $L$ at once (Proposition I', section 5); it costs about twice the list exponent, hence about 1.7 times the points. (c) The extractor of the paper decodes one error on a known set. With the plain fold it must decode $t$ errors on a known set in a code with no known decoder; an efficient extractor at $2^{-125}$ needs fold grinds of about $\log_2 n - 2$ bits (3 to 9 percent of proving time), or one accepts a round-by-round knowledge error of $2^{-113}$ to $2^{-116}$ on the fold messages with the 12-bit grind (section 4.4). (d) Not fixable for the cube window: a query's weight is a sum of $r$ column weights and costs the verifier at least $\kappa(\kappa + 1)/2 + R\kappa$ field products where today it costs $\kappa$, for every spanning set of XOR offsets (section 7.2). In the recursive verifier this is more than the queries saved. Windows of a few index strides are cheaper and more local (section 9.4).
2. **The modified theorem (Theorem D', section 4).** For Protocol D' (plain folds, no degree slack, no high part, one weighted claim a query with a window weight), round-by-round soundness holds with the errors of the paper's Theorem 5.2 except the fold row, which becomes $(K_0 - 1)/q + \tau$ with $K_0 > M = \max(2, \lfloor n/(t+1) \rfloor)$, and the point row, where $q^6$ becomes $q^3$. Its only hypothesis on the code is the list bound for interleaved words at $A_i - \ell_i t$; knowledge soundness and the $K$-rationality of the level-0 candidate need in addition the code's agreement bound, which is Theorem M at $L = 1$. Lemma F' is simpler than the paper's Lemma 4.10 (no rational functions, no poles) and holds for every linear code.
3. **Parameters (exact, section 6).** With the list bound by Proposition I' and the same $L$ at every mixed level, full commitment of $2^{30}$ elements:

| level-0 rate | today: queries, KiB | best $L$ | queries (levels 0, 1) | points (levels 0, 1) | opening, KiB | against today | frontier of note 38 | gap at level 0 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | 218, 335.9 | 17 | 123, 36 | 68, 67 | 235.2 | -30.0% | 114 | +8% |
| 1/4 | 109, 222.6 | 16 | 64, 32 | 66, 63 | 173.0 | -22.3% | 57 | +12% |
| 1/8 | 73, 180.7 | 16 | 45, 30 | 68, 65 | 152.1 | -15.8% | 38 | +18% |
| 1/16 | 55, 158.7 | 17 | 36, (31) | 72, (8) | 138.1 | -13.0% | 28 | +29% |

   The byte optimum is flat from $L = 11$ to 23. $L = 31$ is outside Theorem M ($L \le N - 2$). No $L$ lowers the recursive verifier's work below today's: the estimate is +23 to +73 percent.
4. **Cost.** Prover, on the 900-signature benchmark at rate 1/2 **[measured]**: commitments are 32 percent of `Prove`, about half of it field work and half hashing **[derived]**. A mixing kernel costs 0.9 to 1.3 times the encode's field work at one and four threads **[measured, standalone kernel]**, and deriving $\mu$ costs one Keccak-f a position, a quarter of the commitment's hashing. With the 61 and 60 points of the list bound, the total is +27 to +39 percent of proving time **[estimate from measured parts]**, up to +59 percent if the mixing is bound by memory at all threads. Lowering the rate from 1/2 to 1/4 costs +32 to +52 percent and gives a smaller opening (222.6 KiB against 236.7).
5. **Verdict for Theorem M with the cube window.** Not worth doing, even if Theorem M is proved. At equal prover cost the mixed code at rate $\rho$ gives about the opening of plain Reed-Solomon at rate $\rho/2$, which is deployed and proved; it makes the verifier and the recursion slower; and it changes the code, the fold, the extractor and the oracle in both provers, the three verifiers and `formal/`. The one place where it buys something not available otherwise is below the lowest deployed rate.
6. **The ladder with constant lists (note 57 section 8; section 9 here).** The exact finite inequality is Proposition J: a list of $M$ members at agreement $A$ forces $tA - n + [(n - \mathrm{rem})\binom{M - m_0}{t} + \mathrm{rem}\binom{M - m_0 - 1}{t}]/\binom{M}{t} \le B_t(A)$ with $MA = nm_0 + \mathrm{rem}$. The lead's thresholds are confirmed to four digits. One column above the threshold the list is already at most about $nt$; a list of 1000 costs at most 0.035 percent of the columns more, a list of 32 at most 1.05 percent. Every such list is below $2^{63}$, so the paper's Proposition 6.2 gives all lanes with a factor 2: obstacle (b) disappears and the points stay at the paper's Johnson counts, 11, 8, 8. Openings at $\mu = 30$, rate 1/2: 300.4, 276.8, 262.7, 239.8, 221.1 KiB at $t = 3, 4, 5, 8, 16$ (-10.6, -17.6, -21.8, -28.6, -34.2 percent), each 3 to 7 percent of the opening below Theorem M at $L = t - 1$. The verdict then depends on the window alone. With the cube window it is again a wash against halving the rate, and the recursion is 24 to 71 percent worse. With $t$ partners at index distances $2^j$ spread over the scales, if such windows carry the proof, rungs 4 to 8 at rate 1/2 would give 18 to 29 percent of the opening for 5 to 16 percent of proving time and leave the recursion within -2 to +6 percent **[estimate]**: that is the one version worth its complexity, and it turns on researcher 60's question. The verifier's cost of a partner is the scale of its offset, so cheap windows are local windows; obstacles (a) and (c) stay.

## 1. What the paper uses of the code

I went through sections 2 to 6 of the paper and the Lean sources. "Abstract" means stated for any code or any set of tuples; "RS" means the statement or its Lean form uses evaluation at points of a set $D \subseteq K$ or the degree of a product.

| statement | Lean | uses of the code | under the mixed code |
| --- | --- | --- | --- |
| Lemma 4.4 (E1 to E4), the point functional | `evL_add`, `evL_halves`, `evL_mul`, `card_evL_zero_le` | none: it is about polynomial tuples and points of $E^2$ | unchanged; (E3) is needed only for constants $a$ |
| Lemma 4.6 (determinant) | `Delta_eq_det`, `isFoldL_unique`, `DeltaL_eq_zero_iff`, `card_nondep_triples_ge` | none, but written for $a_c = \alpha + \beta X$ and classes of rational functions | holds with $a_c = \alpha$; $F = (P_1 + P_2)/(\alpha_1 + \alpha_2)$ is a polynomial tuple outright |
| Lemma 4.7 (trichotomy) | `class_trichotomy`, `class_poly_of_card_gt`, `card_agrL_outside_le`, `exists_nearL` | RS: poles, degrees of products, and "two columns determine $c$" through the position $x$ in $a_c(x)$ | cases (a), (b) disappear; (c) becomes a pigeonhole with a loss (Lemma F') |
| Theorem 4.9 (counting) | `lemmaF_exc`, `exists_big_class` (abstract in `Counting.lean`) | the list bound of the folds; $|\mathcal{T}| \le Lq^2$ | $|\mathcal{T}| \le Lq$ |
| Lemma 4.10 (fold round) | `lemmaF_round`, `fold_transition` | Lemma 4.7; linearity of the weight | Lemma F' |
| Lemma 4.11 (pinning) | `lemmaP`, `pinned_unique` | the list bound only | unchanged |
| Lemma 4.12 (potential) | `pot_step`, `potT_step`, `levelPot_step`, `ladderPot_step` | the list bound of the folds | unchanged |
| M1 (batching) | `batch_transition` | none beyond the list | unchanged |
| M3, M4 (queries) | `query_transition`, `final_transition` | RS: a query claim is the evaluation functional `leval (x q)`; the high part | the functional becomes $e_x$; no high part |
| level 0 is over $K$ (section 5.4) | none | RS: Lagrange interpolation on $d + 1$ agreement columns | the agreement bound of the code and $\mu \in K$ (section 4.3) |
| Lemma 5.5, Theorem 5.6 (near tuples, descent) | `nearT_unique`, `descent_step`, `NearT.fold_eq` | RS: two polynomials of degree $\le d$ that agree on $d + 1$ points are equal; one-error decoding | the agreement bound $d_\mu$; $t$-error decoding (section 4.4) |
| Theorem 6.1 (tree bound) | `interleave_listBound`, `AgreeLE`, `ListBound` | abstract: any code with an agreement bound | verbatim, with $d_\mu$ |
| Proposition 6.2 (projection) | `descent`, `GenListBound` | abstract: any code with a generator matrix over $K$ | verbatim, but its hypothesis $2L \le |K|^s$ fails for $s = 1$ |
| Proposition 6.3 (two lanes) | `listBound_prod` | abstract | verbatim; Proposition I' is its induction on lanes |
| Hypothesis 6.4, the bridge | `rs_descent₁`, `lemmaF_exc_of_HK`, `protocolD_sound_of_HK` | RS | to be restated with `GenListBound` |

So the fold-round lemma and the two query transitions are where Reed-Solomon enters, and the distance of the code is needed in three places: the uniqueness of near tuples (knowledge soundness), the $K$-rationality of the level-0 candidate (the interface with the outer protocol), and the interleaving reductions (`AgreeLE`). Plain soundness needs the list bound alone, as in the paper.

## 2. Obstacle 1: the affine fold does not commute with the mixing

**Fact 2.1 [proved].** Let $F, G$ have degree $< k$. Then $e_x(G + \alpha F) = e_x(G) + \alpha e_x(F)$, and $e_x(G + (\alpha + \beta X)F) = e_x(G) + (\alpha + \beta x) e_x(F) + \beta \sum_{c \in C} \mu(x, c)\,c\,F(x + c)$. *Proof.* Linearity, and $(x + c)F(x + c) = xF(x + c) + cF(x + c)$. $\square$

The last sum is the symbol of $F$ in another mixed code (coefficients $c\,\mu(x, c)$), which the verifier cannot compute from the opened column. So the verifier's fold $Z_1[x] + (\alpha + \beta x)Z_0[x]$ of honest lanes is not the codeword of the folded polynomial. It is not a codeword of the mixed code of one more degree either **[checked, C1 of `61_toy_checks.py`: 50 random pairs over $\mathrm{GF}(2^8)$, $n = 16$]**, and the smallest code that contains the mixed code and its multiples by $x$ has dimension $\min(n, 2k)$ **[checked, C1]**, where for Reed-Solomon it has dimension $k + 1$.

**Fact 2.2 [proved].** Let position functionals $e_x$ on $K[X]_{\le d}$ and a function $\lambda$ on the positions satisfy $\lambda(x)\,e_x(F) = e_x(XF)$ for all $F$ of degree $< d$. Then $e_x(F) = e_x(1)\,F(\lambda(x))$: the code is a generalized Reed-Solomon code. *Proof.* $e_x(X^j) = \lambda(x)^j e_x(1)$ by induction. $\square$

More generally a column-wise fold with a verifier-fixed slope $\lambda(x)$ is complete only if $\lambda \cdot \mathcal{C} \subseteq \mathcal{C}'$ for a code $\mathcal{C}'$ of about the same dimension, and for a window whose offsets span the domain a function that is constant on every window is constant. A multiplier that commutes with the mixing exists exactly when the windows stay inside blocks, and then the code contains the periodic subcode that note 57 section 4 rules out. The two requirements (windows that span, a fold with position-dependent slopes) exclude each other. Committing the extra moments $\sum_c \mu(x, c)\,c^j P(x + c)$ would restore the affine fold at the price of $1 + \ell/2 = 4$ times the level-0 leaf. So:

> **the mixed code must be folded with the plain combiner $G + \alpha F$, $\alpha \in E$.**

Annex B (`sec:affine-intuition`) recalls why the affine fold was introduced: with the plain fold each bad column has one repairing challenge, which the prover chooses, so a word that agrees with a pair of codewords on $A - 1$ columns folds to agreement $A$ for up to $n - A + 1$ challenges, and "tolerating the loss of a few coordinates does not help". The next section shows that tolerating the loss of many does, at no cost in queries.

## 3. Protocol D'

Protocol D of the paper with these changes. Each level $i$ has a code given by position functionals $e^{(i)}_x$, $x \in D_i$: either evaluation (a Reed-Solomon level) or the window-mixed $e^{(i)}_x(P) = P(x) + \sum_{j < N_i} \mu_i(x, j)\,P(x + \beta_j)$ with $\mu_i(x, j) \in K$ public (section 5.3; the coefficient of $P(x)$ is normalized to 1, which costs nothing, see 5.3). Every lane of a level is encoded with the same functionals.

1. **Commit.** As in Protocol D: the root of $Z^{(0)}$, $Z^{(0)}[u, x] = e^{(0)}_x(P^{(0,0)}_u)$, then $s^{(0)}$ points $z_m = (\theta_m, \zeta_m) \in E^2$ and the answers $y_m = \mathrm{ev}^{(0)}_{z_m}(P^{(0,0)})$. The point functional is the paper's: it evaluates polynomials, outside the domain, and does not see the code.
2. **Fold round $j$ of level $i$.** The prover sends $v_G = \langle W_0, G\rangle$, $v_F = \langle W_0 + W_1, F\rangle$ and one $\varphi_m = \mathrm{ev}^{(j)}_{z_m}(F)$ a point. The verifier sends $\alpha \leftarrow E$. Both set $W \leftarrow (1 + \alpha)W_0 + \alpha W_1$, $c \leftarrow v_G + \alpha(v_G + c) + \alpha^2 v_F$, $v_m \leftarrow v_m + (\theta_m^{2^{j-1}} + \alpha)\varphi_m$, and the prover folds $P \leftarrow G + \alpha F$. Two scalars a round instead of four, and degrees do not grow: $d^{(i)} = 2^{\kappa_i} - 1$ in every round.
3. **Level boundary.** $P^{(i,\ell_i)}$ has degree $< 2^{\kappa_i}$ and is the next message: there is no high part and no conversion term. The prover commits $Z^{(i+1)}$ and answers its points. The verifier sends $w_i$ positions and $\lambda_{i+1}$, opens the columns, folds each with the plain fold to $w^{(i)}(x)$, and batches the residual claim, the point claims $(W_{\zeta_m}, v_m)$ and one claim $(W^{(i)}_x, w^{(i)}(x))$ a query, where $W^{(i)}_x := W_x + \sum_j \mu_i(x, j)\,W_{x + \beta_j}$ at a mixed level and $W_x$ at a Reed-Solomon level. A query is still one weighted claim and one power of $\lambda_{i+1}$; its weight is a sum of $r$ tensor weights.
4. **Last level.** The prover sends the $2^{\kappa_i}$ coefficients of $P = P^{(i,\ell_i)}$; the verifier checks $P(\zeta_m) = v_m$ and $w(x) = e_x(P)$ at its queries, then the tail.
5. **Grinds.** 15 bits before points, 17 before queries, 7 before $\lambda_0$, and $g_f$ before a fold challenge, with $g_f = 12$ below (the deployed affine fold has 7).

**Completeness [proved; checked, C2].** The paper's proof with $\beta = 0$: by (E2), $v = \theta^{2^{j-1}}\varphi + \mathrm{ev}^{(j)}_z(G)$, so $\mathrm{ev}^{(j)}_z(G + \alpha F) = v + (\theta^{2^{j-1}} + \alpha)\varphi$; the claim update is the expansion of $\langle (1 + \alpha)W_0 + \alpha W_1, G + \alpha F\rangle$ with $c = \langle W_0, F\rangle + \langle W_1, G\rangle$; and the verifier's folded column is $e_x$ of the folded polynomial by Fact 2.1. C2 runs one level (four lanes, two rounds, three points, random weights) on a mixed code over $\mathrm{GF}(2^8)$: 20 honest runs, every column queried, all identities hold.

A Reed-Solomon level may keep the affine fold of Protocol D; the tables below use the plain fold everywhere, which is one protocol and loses nothing measurable.

## 4. Soundness

### 4.1 The fold round for any linear code

Fix a level: positions $D$ ($n$ of them), degree bound $d$, functionals $e_x$, a word $Z$ with halves $Z_0, Z_1$ and lane variables $u_j, \dots, u_\ell$, its plain folds $Z_\alpha = Z_1 + \alpha Z_0$, lists $\Lambda(Z; A)$ of polynomial tuples of degree $\le d$ whose encoding agrees with $Z$ on at least $A$ columns, and $L$ a bound on $|\Lambda(Z_\alpha; A)|$ over all $\alpha$. Candidates are pairs $(\alpha, P)$, $P \in \Lambda(Z_\alpha; A)$; the class of a pair of tuples $(F, G)$ is $\{(\alpha, P) : P = G + \alpha F\}$; $\Delta = (\alpha_2 + \alpha_3)P_1 + (\alpha_1 + \alpha_3)P_2 + (\alpha_1 + \alpha_2)P_3$, of degree $\le d$. For an integer $t \ge 0$, a *$t$-near tuple* of $P$ is a tuple of degree $\le d$ that agrees with $Z$ on all but at most $t$ columns of the agreement set of $P$ with $Z_\alpha$.

**Lemma F' [proved].** Let $t \ge 0$, $M \ge \max(2, \lfloor n/(t+1) \rfloor)$, $K_0 > M$, $\Theta = K_0(K_0 - 1)(K_0 - M)$, and let $\mathrm{Exc}_j(Z)$ be the set of point tuples $\mathbf{z}$ for which at least $\Theta$ ordered triples of candidates with pairwise different challenges have $\Delta \ne 0$ and $\mathrm{ev}^{(j)}_{z_m}(\Delta) = 0$ for all $m$.

1. For $s$ independent uniform points, $\Pr[\mathbf{z} \in \mathrm{Exc}_j(Z)] \le L^3 q^3 \epsilon^s / \Theta$ with $\epsilon = (d + 2^\ell - 2^j)/q$.
2. Let $\mathbf{z} \notin \mathrm{Exc}_j(Z)$, $(W, c^\circ)$ a weighted claim, $v_1, \dots, v_s \in E$, $B$ a predicate. Suppose every $U \in \Lambda(Z; A - t)$ with $B(U)$ and $\mathrm{ev}^{(j-1)}_{z_m}(U) = v_m$ for all $m$ has $\langle W, U\rangle \ne c^\circ$. Then for every prover message $(v_G, v_F, \varphi_1, \dots, \varphi_s)$ fewer than $K_0$ challenges $\alpha$ admit a $P \in \Lambda(Z_\alpha; A)$ with (p) $\mathrm{ev}^{(j)}_{z_m}(P) = v_m + (\theta_m^{2^{j-1}} + \alpha)\varphi_m$ for all $m$, (w) $\langle (1 + \alpha)W_0 + \alpha W_1, P\rangle = v_G + \alpha(v_G + c^\circ) + \alpha^2 v_F$, (b) every $t$-near tuple of $P$ satisfies $B$.

*Proof.* (1) $|\mathcal{T}| \le Lq$, a triple with $\Delta \ne 0$ vanishes at $s$ independent points with probability at most $\epsilon^s$ by (E4), and Markov. (2) As in the paper, with $y^F_m = \varphi_m$, $y^G_m = v_m + \theta_m^{2^{j-1}}\varphi_m$: two candidates with different challenges lie in exactly one class, three lie in one class iff $\Delta = 0$, and three candidates satisfying (p) have $\mathrm{ev}_{z_m}(\Delta) = 0$ (the paper's Lemma 4.6 with constant $a_k$; `Counting.lean` is abstract). So if $K_0$ challenges were as stated, some class $(F, G)$ would hold more than $M$ of the chosen candidates (`exists_big_class`). $F$ and $G$ are polynomial tuples of degree $\le d$. Put $\delta^F_m = \mathrm{ev}_{z_m}(F) + y^F_m$, $\delta^G_m = \mathrm{ev}_{z_m}(G) + y^G_m$; (p) for an element of the class reads $\delta^G_m + \alpha\delta^F_m = 0$. If some $(\delta^F_m, \delta^G_m) \ne 0$ this has at most one solution: at most 1 element. Otherwise $(F, G)$ satisfies the carried claims. Let $\mathcal{A}$ be the set of columns where $(F, G)$ agrees with $(Z_0, Z_1)$. At a column $x \notin \mathcal{A}$ where $G + \alpha F$ agrees with $Z_\alpha$, $(e_x(G) + Z_1[x]) = \alpha\,(e_x(F) + Z_0[x])$ as vectors over the lanes and the right vector is not zero, so $x$ determines $\alpha$: each column outside $\mathcal{A}$ serves at most one challenge. Hence at most $\lfloor (n - |\mathcal{A}|)/(t + 1) \rfloor \le M$ elements of the class have more than $t$ agreement columns outside $\mathcal{A}$. As the class holds more than $M$ chosen candidates, one of them has at most $t$: then $|\mathcal{A}| \ge A - t$, $U = (F, G) \in \Lambda(Z; A - t)$ and $U$ is a $t$-near tuple of it, so $B(U)$ by (b), so $\langle W, U\rangle \ne c^\circ$ by hypothesis. Then (w) minus its honest expansion for $U$ is a polynomial of degree at most 2 in $\alpha$ whose constant term and coefficient of $\alpha$ do not both vanish (the paper's computation): at most 2 elements satisfy (w), a contradiction with more than $M \ge 2$. $\square$

The lemma uses nothing of the code: no distance, no injectivity. Its error is tight: for a pair that agrees on $|\mathcal{A}|$ columns, a planted word repairs $A - |\mathcal{A}|$ columns for each of $\lfloor (n - |\mathcal{A}|)/(A - |\mathcal{A}|) \rfloor$ challenges and never more **[checked, C3: four shapes on a mixed code over $\mathrm{GF}(2^8)$, the planted word attains the bound, 120 random words stay below it]**. This is the attack of Annex B's intuition paragraph with the repaired columns grouped by $t + 1$, so $n/((t+1)q)$ is the true error of a plain fold round at a loss of $t$, on any code.

**The trade between loss and grind [exact, T5 of the script].** Take $K_0 = 2^{g_f + 2}$, $M = 2^{g_f + 1}$, $\tau = 2^{-(126 - g_f)}$: the fold message has error below $2^{g_f - 125}$, and $t + 1 = \lceil n/M \rceil$. At level 0 of the $2^{30}$ commitment at rate 1/2 ($n = 2^{25}$): $g_f = 7$ loses $6t/n = 2.3$ percent of the columns over the six rounds and 9 queries (134 instead of 125 at $L = 15$); $g_f = 12$ loses 0.07 percent and no query; the 26 fold grinds of the opening then cost $2^{16.7}$ permutations, against $2^{19.9}$ for all grinds today. The few levels whose threshold is a few dozen columns (the counting bound at the last level) take $g_f = 16$.

### 4.2 The theorem

Thresholds $A^{(i,j)} = A_i - t_i(\ell_i - j)$, degree $d^{(i)} = 2^{\kappa_i} - 1$, $\epsilon_i = (2^{\kappa_i} + 2^{\ell_i} - 2)/q$.

**Hypothesis $\mathsf{LB}'_i(L_i)$.** For every $0 \le m \le \ell_i$, every word with $m$ lane variables and values in $E$ on the positions of level $i$ has at most $L_i$ tuples of degree $\le d^{(i)}$ whose encoding agrees with it on at least $A^{(i,0)}$ columns.

**Theorem D' [proved, given the paper's Theorem 5.2 and Lemma F'].** Assume $\ell_i \ge 1$, $M_i \ge \max(2, \lfloor n_i/(t_i + 1) \rfloor)$, $K_{0,i} > M_i$, $0 < \tau < 1$ and $\mathsf{LB}'_i(L_i)$ for every level. Then Protocol D' is round-by-round sound with errors

| | message | error |
| --- | --- | --- |
| M0 | first points of level $i$ (one batch of $s_i$) | $\bigl[\binom{L_i}{2} + \frac{L_i^3 q^3}{\Theta_i}\sum_{j < \ell_i}\tau^{-j}\bigr]\epsilon_i^{s_i}$ |
| M1 | $\lambda_0$ | $(J_0 - 1)/q$, or $(J_0 + 1)/q$ with the ring-switching scalars |
| M2 | fold challenge | $(K_{0,i} - 1)/q + \tau$; $(K_{0,i} - 1)/q$ in the last round of a level |
| M3 | queries of a level $i$ other than the last | $((A_i - 1)/n_i)^{w_i} + (s_i + w_i)/q$ |
| M4 | queries of the last level | $((A_i - 1)/n_i)^{w_i}$ |
| M5 | tail round | $2/q$ |

*Proof.* The state function and the transitions of the paper's section 5 with: Lemma F' in M2 (its hypothesis is the invariant at $A^{(i,j-1)} = A^{(i,j)} - t_i$); in M0 the bound $L^3q^3\epsilon^{\bar s_j}/\Theta$ for each term of the potential; in M3 the polynomial $P^\ast = \mathcal{P}_{g^\ast}$ itself (no high part), Case 1 unchanged, and in Case 2 a query with $e_x(P^\ast) \ne w^{(i)}(x)$ violates the query claim because $\langle W^{(i)}_x, g^\ast\rangle = e_x(\mathcal{P}_{g^\ast})$ by linearity of $e_x$ in the evaluations; in M4 the check $w(x) = e_x(P)$. Pinning, batching and the tail do not see the code. $\square$

With $g_f = 12$ the point row reads $s_i \log_2(1/\epsilon_i) \ge 3b + 1023$ for $\ell = 6$ and $3b + 795$ for $\ell = 4$, $b = \log_2 L_i$ **[checked: the exact rational test of `61_params.py` agrees with the first law at $b = 40, 75, 110, 896, 2700$ and with the second at $b = 896, 1871$]**, against $3b + 1062$ and $3b + 824$ in the paper.

### 4.3 Where the distance of the mixed code is needed

Let $d_\mu$ be the largest number of positions on which two distinct codewords agree (the paper's `AgreeLE`). The mixed code is not MDS: a codeword vanishes for free on the interior of the zero set of its polynomial and at every other position with probability $1/q_K$, so $d_\mu \approx k + nH(\rho)/64$.

**Fact 4.1 [proved].** If Theorem M holds at $L = 1$ with agreement $A_1$, then $d_\mu \le 2A_1 - n$. *Proof.* If two distinct codewords agree on $s$ positions, a word that follows one on half of the other positions and the other on the rest agrees with each on at least $s + \lfloor (n - s)/2 \rfloor$, which must be below $A_1$. $\square$

At level 0 this gives $d_\mu/n \le 0.5247, 0.2795, 0.1557, 0.0936$ at rates 1/2 to 1/16; the first-moment count of codewords with many zeros (the rank-one case of note 57's Key Lemma, same status as its Step 5) gives $0.5156, 0.2630, 0.1339, 0.0681$ **[exact arithmetic, T2]**. Uses:

- **Level 0 is over $K$ [proved].** A member $U = U' + yU''$ of the level-0 list ($U', U''$ over $K$, $E = K \oplus yK$) agrees with $K$-valued lanes on $A^{(0,0)}$ columns; since $\mu \in K$ and $D \subseteq K$, the encoding of $U''$ vanishes there, so $U'' = 0$ as soon as $A^{(0,0)} > d_\mu$. This replaces the Lagrange argument and is why the level-0 coefficients must lie in $K$ (they must anyway, or the level-0 leaf doubles).
- **Uniqueness of near tuples.** Two $t$-near tuples on a set $S$ agree on $|S| - 2t$ columns, so (S2) becomes $A^{(i,0)} \ge d_\mu + 2t_i + 1$; the same count gives that a near tuple folds back to the tuple it was decoded from. Both hold at every row of the tables.
- **The interleaving reductions** (section 5).

### 4.4 Knowledge soundness and the extractor

Theorem 5.6 of the paper goes through with $t$-near tuples: the relativised invariant is preserved with the same errors, and an accepting run that preserved it yields, by the descent, a chain of unique $t$-near tuples down to level 0 **[proved, by the paper's argument and 4.3]**. What changes is the extractor as an algorithm, and leanVM's formal statement has it as a compiled program with a proved running time (`formal/statement.tex`: it "decodes the previous round's word with at most one error on the columns where the current tuple agrees with the word", cost about $2^{2\mu + 7}$).

- **Decoding with no error** on a known set is a linear system of $k$ equations in the $k$ coefficients of each lane, dense in any basis I know: Gaussian elimination, $k^3$, where Reed-Solomon interpolation is $k^2$.
- **Decoding $t$ errors** on a known set is syndrome decoding of a code with no known structure to exploit. Information-set decoding succeeds with probability about $(1 - k/|S|)^t$ a trial: $11^{-t}$ at rate 1/2 and $a = 0.55$. I found no algebraic decoder: the Berlekamp-Welch linearization fails because the error locator at $x$ multiplies $P$ at $x + c$ (the same reason as Fact 2.1). **[open]**
- A typical accepting run has no repaired column at all: a challenge repairs more than $t_E$ columns with probability at most $n/((t_E + 1)q)$ an attempt. So an extractor that decodes at most $t_E$ errors fails with that probability a fold round, whatever loss $t$ the soundness analysis tolerates.

Consequences **[derived]**. With $g_f = 12$ and an efficient extractor ($t_E = 1$, one syndrome match), every message is at $2^{-125}$ for soundness, and a level-0 fold message is at $n/(2q)\,2^{-12}$ for knowledge soundness: $2^{-116}$ at $n = 2^{25}$, $2^{-113}$ at $n = 2^{28}$. To hold the efficient extractor to $2^{-125}$ the fold grind must be $\log_2 n - 1 - \log_2(t_E + 1)$ bits: 23 bits at level 0 for $t_E = 1$ at $n = 2^{25}$. The work is proportional to $n$, about $5n/(t_E + 1)$ permutations over the opening against 4 to 5 $n$ for the level-0 Merkle tree: at the benchmark's shape 5.2 million permutations for $t_E = 1$ and 2.6 million for $t_E = 3$, that is 6 to 9 and 3 to 4.5 percent of `Prove` at the measured 100 to 142 million permutations a second **[estimate]**. Since a valid hash-based signature exists for every message, leanVM's claim is a knowledge claim and cannot fall back on plain soundness. This is the third obstacle; it has a price, not a solution.

## 5. The list bound the protocol needs, and the randomness

### 5.1 Interleaved words

**Theorem M [hypothesis, note 57].** For $L \le N - 2$ and the least integer $A$ with $64((L + 1)A - n - Lk) \ge (L + 1)\,nH(A/n) + 130$: except with probability $2^{-128}$ over $\mu$, no word $D \to K$ has $L + 1$ affinely independent polynomials of degree $< k$ whose mixed codewords agree with it on at least $A$ positions each. So single $K$-valued words have at most $2^{64(L-1)}$ list members.

The protocol needs $\mathsf{LB}'$: words with values in $E$ and up to $2^{\ell}$ lanes, that is up to $m = 2^{\ell + 1} = 128$ lanes over $K$ at level 0. The folds are $E$-valued even at level 0, so the hypothesis is never about single $K$-valued words.

- **The projection bound does not apply.** Proposition 6.2 needs twice the list bound to be at most $|K|^s$ for an $s$-lane hypothesis; with a single-lane list of $2^{64(L-1)}$ and $s = 1$ it fails for every $L \ge 2$. The lead's fact 3 of the round-5 brief ("a loss of at most a factor 2") rests on it or on $A > (n + 3d)/4$, which here reads $a > 0.6435$ at rate 1/2 and fails for $L \ge 3$.
- **A direct first-moment proof for interleaved words is not a corollary of note 57's.** For $m$ lanes the event at a position is that $\mu(x, \cdot)$ is orthogonal to the span of the coordinates of all differences, of dimension up to $\min(r, m(|I_x| - 1))$: the conditions saturate at $r = N + 1$ while the number of configurations grows like $q^{mkL}$, and the entropy of the set systems is not divided by $m$. With $m = 2$, $L = 15$, $r = 26$ the union bound already fails on configurations whose members share one agreement set **[derived]**. Such configurations are excluded by the distance, not by the first moment, so a direct proof must condition on it. I did not find the right statement; a hypothetical bound $2^{64(L-1)}$ for all lanes is the column "direct" below.
- **The paper's tree bound applies verbatim** (`interleave_listBound`, any code with `AgreeLE`): the interleaved list is at most $\sum_{k \le \min(b, r')}\binom{b}{k}(\Lambda - 1)^k$, a power $r' = 2$ to 4 of the single-lane bound. Column "tree".
- **A better reduction uses Theorem M at several $L$:**

**Proposition I' [proved].** Let a code have agreement bound $d$, let $\Lambda_1(A)$ bound its single-lane lists at agreement $A$ and $N_m(A)$ the lists of its $m$-lane words. Then for $A > d$: $N_m(A) \le N_{m-1}(A) + (\Lambda_1(A) - 1)\,N_{m-1}(2A - d)$. *Proof.* Project a list member on its first $m - 1$ lanes: a member of the $(m-1)$-lane list at $A$. The fibre of a prefix has at most $\Lambda_1(A)$ elements, and if it has two, their agreement sets (inside the prefix's, each of size $\ge A$) share at most $d$ columns, so the prefix agrees on at least $2A - d$. $\square$ This is the paper's Proposition 6.3 (`listBound_prod`, machine-checked) applied to the product of the $(m-1)$-lane code with the code. **[checked, C4: exhaustive lists of 328 cases of random binary codes with two and three lanes, 122 of them with a single-lane list above one.]**

Unrolled with $A_j = d_\mu + 2^j(A - d_\mu)$ and $L_j$ the least $L$ for which (1) holds at $A_j$: $N_m(A) \le \binom{m + J - 1}{J}\prod_{j < J} 2^{64(L_j - 1)}$, $J$ the first index with $L_J = 1$. So the code hypothesis of Theorem D' at a mixed level is: **Theorem M for the same $\mu$ at the pairs $(L_j, A_j)$, $j < J$, and at $L = 1$ with its own agreement $A_1$** (at most six instances; the last gives the agreement bound by Fact 4.1 and covers $A_J \ge A_1$). The closed form follows from the recursion by the hockey-stick identity; the script evaluates the recursion itself. At level 0, rate 1/2 **[exact, T2]**:

| $L$ | $A/n$ | profile $L_0, L_1, \dots$ | $\log_2$ list: direct, profile, tree | points $s_0$: direct, profile, tree |
| --- | --- | --- | --- | --- |
| 4 | 0.6150 | 4, 2, 1 | 192, 269, 385 | 16, 18, 21 |
| 7 | 0.5779 | 7, 4, 2, 1 | 384, 658, 1152 | 21, 29, 44 |
| 11 | 0.5571 | 11, 6, 3, 1 | 640, 1106, 1924 | 29, 42, 66 |
| 15 | 0.5468 | 15, 9, 5, 2, 1 | 896, 1751, 3588 | 36, 61, 114 |
| 23 | 0.5364 | 23, 15, 8, 4, 2, 1 | 1408, 3036, 7045 | 51, 98, 214 |

The other rates differ by a point or two. With the first-moment distance in place of Fact 4.1 the profile at $L = 15$ is 15, 7, 3, 1 and $s_0 = 51$. Note 57's "36 points at $L = 15$" is the direct column; what is available from Theorem M as stated is 61.

### 5.2 Where $\mu$ comes from

- **A fixed public seed** (a tag, the level's shape, the position): the code is one object for all proofs. In the random-permutation model of `formal/` (the adversary's code is fixed before $\pi$ is sampled, the verifier's calls are counted) "the code satisfies its list bounds" is an event over $\pi$ of probability at least $1 - 6 \cdot 2^{-128}$ a level shape, charged once and not multiplied by the adversary's attempts. The $\mu$-calls are permutation calls on fixed inputs, domain-separated from the transcript's duplex; lazy sampling keeps every other answer uniform, and the calls ($2^{25}$ to $2^{29}$ for one code) enter the indifferentiability term $Q^2/2^{508}$ without changing it. The paper's Lean model needs nothing new: its `Level.OK.listBound` is a hypothesis on a fixed code.
- **A seed bound to the statement or the transcript** is one more verifier message of error $6 \cdot 2^{-128}$, below the target with no grind. It is sound, and it buys nothing: the prover derives $\mu$ at every position in both cases, the verifier at the queried ones, and the error is now paid on each of the adversary's attempts. Use the fixed seed.
- **In `formal/`**, the end theorem would carry the term for a bad code, and discharging it means formalizing Theorem M's proof on top of `Common.keccak256_transfer`, or keeping "the code built from $\pi$ is good except with probability $2^{-128}$" as an explicit hypothesis of the statement.

### 5.3 How much randomness, and what structure

- **Normalizing $\mu(x, 0) = 1$ is free [proved].** For a subspace $R \subseteq K^C$ of dimension $\delta$, the vectors $(1, \mu')$ orthogonal to $R$ form an affine space that is empty or of codimension $\delta$: the probability is at most $q_K^{-\delta}$, which is all the union bound uses. So $N$ random coefficients a position.
- **One Keccak-f a position for $N \le 25$, two for $N = 26$ to 28.** The 25 words of $\pi(\text{tag}, \text{shape}, x)$ on distinct inputs are uniform without replacement; this is a direct call of the permutation, which the model and the guest's `KECCAK` opcode already have. A queried position costs the verifier and the guest the same one or two calls.
- **A short seed expanded by cheap arithmetic cannot carry the first-moment proof [proved].** In a family of $2^S$ codes every probability is a multiple of $2^{-S}$, and the proof bounds each of about $q_K^{Lk}$ configurations by $q_K^{-\sum_x \dim R_x}$, below $2^{-128} q_K^{-Lk}$. A configuration can meet that bound only if it is impossible for every seed or $S \ge 64Lk$. So the argument needs at least $L\rho$ field elements of oracle output a position (7.5 at $L = 15$, rate 1/2), whatever the construction. Pairwise or $r$-wise independence across positions is far from enough: the bad event constrains about $n/2$ positions jointly.
- **Fewer than $r$ random elements a position** ($\mu(x, \cdot) = A\,t_x$ with $t_x \in K^{r'}$, $L \le r' < r$) changes the exact probability to $q^{-\dim A^{\mathsf T}R_x}$ and adds the kernel of $A^{\mathsf T}$ to the deficiency of note 57's Step 2; it would save nothing here, since one call already gives 25 words.
- **A subfield halves the gain.** With $\mu \in \mathrm{GF}(2^{32})$ a condition defined over the subfield costs $2^{-32}$, the pigeonhole term becomes $H(a)/32$ and $a$ rises by 1.5 points. Coefficients in $E$ would lower it by 0.8 point but make the level-0 symbols $E$-valued (twice the leaf). At later levels, where lanes are $E$-valued anyway, $E$ coefficients lower $a$ and double the list's bits; under Proposition I' they never win in bytes **[exact, script]**.

## 6. Parameters

All from `61_params.py`, exact but for inequality (1) itself, which is evaluated in double precision against its 130-bit margin (replacing $2^{nH}$ by $\binom{n}{A}$ moves $A$ by at most one column). Grinds 17 (queries), 12 (fold), 15 (points), 7 (batching). The model of the opening is note 08's and note 11's, validated there against the deployed query table and measured proofs; Protocol D' is not implemented.

**Inequality (1) at level 0, $\mu = 30$ [exact, T1].** Queries with the loss of the 12-bit fold grind.

| rate | $L = 4$ | 7 | 11 | 15 | 23 | 31 (not admitted) | today | frontier |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2, $A/n$ | 0.6150 | 0.5779 | 0.5571 | 0.5468 | 0.5364 | 0.5312 | 0.7071 | 0.5156 |
| 1/2, queries | 155 | 137 | 129 | 125 | 121 | 119 | 218 | 114 |
| 1/4, $A/n$ | 0.4153 | 0.3585 | 0.3267 | 0.3108 | 0.2949 | 0.2869 | 0.5 | 0.263 |
| 1/4, queries | 86 | 74 | 68 | 65 | 62 | 61 | 109 | 57 |
| 1/8, $A/n$ | 0.3140 | 0.2470 | 0.2095 | 0.1907 | 0.1718 | 0.1623 | 0.3536 | 0.1339 |
| 1/8, queries | 65 | 54 | 48 | 46 | 43 | 42 | 73 | 38 |
| 1/16, $A/n$ | 0.2630 | 0.1907 | 0.1502 | 0.1298 | 0.1093 | 0.0991 | 0.25 | 0.0681 |
| 1/16, queries | 57 | 46 | 40 | 37 | 34 | 33 | 55 | 28 |

Note 57's three values at rate 1/2 are confirmed (0.616, 0.578, 0.547; its 124 queries at $L = 15$ is 125 with the exact query term). The gap to the frontier at $L = 15$ is 10, 14, 21 and 32 percent at the four rates, and at $L = 23$, the largest admitted at $N = 25$, it is 6, 9, 13 and 21 percent. $L = 31$ needs windows of at least 34 offsets ($L \le r - 3$). At rate 1/16, $L = 4$ is worse than today. The pigeonhole term is 0.0155 at rate 1/2 and 0.0087 at rate 1/16.

**The whole opening, $\mu = 30$, list bounds by Proposition I' [exact, T3].** A level is mixed where that gives fewer bytes than the best Reed-Solomon level (Johnson, or the counting bound at the last level); in practice levels 0 and 1. "M" mixed with coefficients in $K$, "J" Johnson, "C" counting.

| rate | $L$ | queries per level | points per level | codes | KiB | against today | against the paper's Johnson instance |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | today | 218 55 32 23 18 15 | one OOD | | 335.9 | | |
| | paper, Johnson | 217 55 31 22 17 7 | 11 8 8 8 8 15 | | 332.0 | -1.2% | |
| | Reed-Solomon, plain fold | 217 55 31 22 17 8 | 11 8 8 7 7 12 | J J J J J C | 331.1 | -1.4% | -0.3% |
| | 4 | 155 55 31 22 17 8 | 18 8 8 7 7 12 | M J J J J C | 271.3 | -19.2% | -18.3% |
| | 7 | 137 46 31 22 17 8 | 29 26 8 7 7 12 | M M J J J C | 249.3 | -25.8% | -24.9% |
| | 11 | 129 40 31 22 17 8 | 42 42 8 7 7 12 | M M J J J C | 239.5 | -28.7% | -27.9% |
| | 15 | 125 37 31 22 17 8 | 61 60 8 7 7 12 | M M J J J C | 236.7 | -29.5% | -28.7% |
| | 23 | 121 35 31 22 17 8 | 98 99 8 7 7 12 | M M J J J C | 238.3 | -29.1% | -28.2% |
| 1/4 | today | 109 44 28 21 17 15 | | | 222.6 | | |
| | 7 | 74 42 28 20 16 8 | 29 26 8 7 7 12 | M M J J J C | 184.5 | -17.1% | -16.1% |
| | 15 | 65 33 28 20 16 8 | 61 60 8 7 7 12 | M M J J J C | 174.0 | -21.8% | -20.9% |
| | 23 | 62 30 28 20 16 8 | 103 106 8 7 7 12 | M M J J J C | 176.6 | -20.6% | -19.7% |
| 1/8 | today | 73 37 25 19 16 15 | | | 180.7 | | |
| | 7 | 54 37 25 19 15 8 | 29 8 8 7 7 12 | M J J J J C | 159.1 | -12.0% | -10.9% |
| | 15 | 46 31 25 19 15 8 | 61 60 8 7 7 12 | M M J J J C | 152.9 | -15.4% | -14.4% |
| 1/16 | today | 55 32 23 18 16 14 | | | 158.7 | | |
| | 7 | 46 31 22 17 14 8 | 29 8 8 7 7 12 | M J J J J C | 144.8 | -8.8% | -5.4% |
| | 15 | 37 31 22 17 14 8 | 65 8 8 7 7 12 | M J J J J C | 138.5 | -12.8% | -9.5% |

Levels 2 and later stay Reed-Solomon: at rate $2^{-7}$ and below the term $(1 - \rho)/(L + 1)$ leaves the mixed code little or nothing under the Johnson radius, and the points cost more than the queries saved. The later levels' rates and sizes are those of Annex B: $R_i = R_0 + 3i$, $n_i = 2^{24 + R_0 - i}$.

**Best $L$ [exact, T4].** For bytes, by reduction: direct (hypothetical) $L = 22, 21, 23, 23$ with 228.4, 165.6, 144.1, 132.2 KiB (-32.0, -25.6, -20.3, -16.7 percent); Proposition I' $L = 17, 16, 16, 17$ with 235.2, 173.0, 152.1, 138.1 KiB (-30.0, -22.3, -15.8, -13.0 percent); the machine-checked tree bound $L = 10, 10, 11, 10$ with 244.3, 181.0, 156.6, 142.5 KiB (-27.3, -18.7, -13.4, -10.2 percent). An opening byte at rate 1/2: about 1.03 KiB a level-0 query, 112 bytes a level-0 point. For the recursive verifier the best choice is no mixed level at all (section 7.2); among mixed configurations the least bad is level 0 only with $L = 13$ to 19.

**The benchmark's shape [exact, T8]** ($\mu = 26$, 40 of 64 lanes): today's opening is 240.4 KiB at rate 1/2 and 162.9 at rate 1/4; mixed at rate 1/2 it is 170.9 KiB at $L = 15$ (-28.9 percent).

## 7. Cost

### 7.1 Prover

**Where the time goes today [measured].** `leanvm-bench --prover experimental aggregate --xmss 900 --log-inv-rate 1 --tracing`, Apple M4 Max, four runs at load average 2.5 to 5, spans in ms (`61_bench_output.txt`): `Prove` 574 to 619; level-0 `NTT` span 116 to 136 (20 to 22 percent), which in the experimental prover holds the encode, the leaf hashing and the Merkle tree (its `Merkle` span is the 0.8 microseconds of `finish`); the four later commitments 40 to 44, 17 to 19, 7.3 to 8.6 and 3.3 to 4.0; all commitments about 190, 32 percent of `Prove`. The stable prover splits the tree off: level-0 `NTT` 94.6 (encode and leaves), `Merkle` 14.8 for $2^{21} - 1$ nodes, that is 142 million permutations a second.

**The split [derived from the above].** Level 0 hashes 3 permutations a leaf and 1 a node, $2^{23}$ in all: 59 ms at that throughput, so the encode's field work is 57 to 77 ms, 10 to 13 percent of `Prove`, and the hashing about 10 percent. Over all levels: field work about 16 percent, hashing about 16 percent. The error of this split is that of using one hashing throughput for both provers and all levels, perhaps 20 percent.

**The mixing kernel [measured, `61_mix_bench.c`, standalone, load average 4 to 7].** A buffer of $2^{20}$ or $2^{21}$ rows of 40 words of $K$ (the benchmark's level-0 codeword is $2^{21}$ rows), against a depth-first transform of the additive NTT's shape on the same buffer (one product a butterfly, one layer a pass above the cache, where the real code takes three). The mixing accumulates the $N$ products of a word unreduced and reduces once.

| kernel | one thread, $2^{20}$ rows | four threads, $2^{20}$ rows | four threads, $2^{21}$ rows |
| --- | --- | --- | --- |
| NTT-shaped transform | 320 ms | 75 ms | 191 ms |
| mix, all $N$ partners, one pass | 1.10 | 2.39 | 2.65 |
| mix, all $N$ partners, five streams at a time | 0.87 | 1.33 | 1.33 |
| mix, 16 partners spread over the cube | 0.88 | 1.15 | 1.20 |
| mix, 9 partners spread over the cube | 0.45 | 0.69 | 0.68 |

(ratios to the transform of the same column.) By carry-less multiplications the mix is cheaper than the transform (one a word and partner against three a butterfly); what it pays is memory: $N$ strided read streams, more than the prefetcher follows at once, hence the grouped variant. I did not run it at the pool's 15 threads (the brief's four-core limit); the real encode is itself bound by memory there, so I take 0.9 to 1.33 as measured and 2.5 as a pessimistic bound.

**Added time at rate 1/2, benchmark shape [estimate from the measured parts].**

| item | basis | ms | share of `Prove` (590 ms) |
| --- | --- | --- | --- |
| mixing, levels 0 and 1, $r = N + 1$ | 0.9 to 1.33 times 75 to 99 ms of field work | 68 to 132 (250 at factor 2.5) | 12 to 22% (42%) |
| deriving $\mu$, levels 0 and 1 | $3 \cdot 2^{20}$ permutations at 100 to 142 million a second | 22 to 31 | 4 to 5% |
| points: 61 and 60 instead of one OOD | note 24: 2.7 percent gross for 12 at level 0, linear | about 70 | 12% |
| total | | 160 to 233 (351) | 27 to 39% (59%) |
| fold grinds for an efficient extractor at $2^{-125}$, $t_E = 3$ or 1 | section 4.4 | 19 to 52 | 3 to 9% |

For smaller windows, were they admissible, the mixing line scales with the partners: at level 0 alone, 9 to 17 percent for $r = 22$ (here $N = 21$; $r = 26$ at $\mu = 30$ costs the same a word and partner), 7 to 13 percent for $r = 17$ and 4 to 7 percent for $r = 10$, with the same factor 2.5 as pessimistic bound. With XOR offsets fewer than $N$ cannot span the domain, so $r = 17$ and 10 would need other translations, which the verifier pays for (7.2).

**Fusing with the NTT.** The encode finishes a block of at most $2^{14}$ words in cache and hands it to the leaf hasher. The partners $x + \beta_j$ with $j$ below the block's row bits (about 8) are in that block and could be added there. The others, 13 at the benchmark's size and 17 at $\mu = 30$, lie in other blocks, which are finished at other times, and a leaf cannot be hashed before all its partners exist. So the mix is a second pass over a stored Reed-Solomon codeword (in groups of a few directions, as measured), with the leaf hashing moved into it; only the in-block directions fuse. It cannot be an in-place butterfly network: composing butterflies along the directions gives symbols that depend on $2^{\text{depth}}$ evaluations, and a symbol must be a sum of $r$. Consequence for memory: the whole level-0 codeword must be held (671 MB at the benchmark, 16 GiB at $\mu = 30$ and rate 1/2, 128 GiB at rate 1/16). The stable prover holds it already; the experimental prover, where `primitives::REBUILD_OVER_STORE` holds (x86), does not keep a large level-0 codeword (`Codeword::Nothing` in its `pcs/src/whir.rs`) and recomputes the rows a query opens, and it would lose that.

**Against lowering the rate [measured, loaded machine, alternating runs].** Rate 1/4 doubles every commitment span (level 0: 262 to 295 ms against 131 to 154) and `Prove` goes from 692 to 1130 ms to 1050 to 1580 ms, a ratio of 1.5 on the fastest runs; from the spans of the light-load runs the increase is 190 ms, 32 percent.

### 7.2 Verifier and guest

**The window weight [proved, lower bound; checked, C5].** At the terminal point $\varrho$ the weight of a position $y$ is $\prod_{k < \kappa}(1 + \varrho_k + \varrho_k\widehat W_k(y))$, and $\widehat W_k$ is additive and vanishes exactly on $U_k = \langle\beta_0, \dots, \beta_{k-1}\rangle$. So the partner $x + c$ changes factor $k$ if and only if $c \notin U_k$, and since the offsets must generate the domain, at least $N - k$ of them lie outside $U_k$. Any set of spanning XOR offsets therefore changes at least $\sum_{k < \kappa}(N - k) = \kappa(\kappa + 1)/2 + R\kappa$ factors a query, and the cube directions attain it ($x + \beta_j$ changes the factors $k \le j$, the others are a shared suffix product). That is 324 products of $E$ a level-0 query at $\mu = 30$, rate 1/2, where today's weight is 24, plus the constants $\varrho_k\widehat W_k(\beta_j)$ once a level. Translations that are not XORs cost a full chain each (about $4\kappa$ products): four such partners already cost more than the whole cube. At the last level a mixed query would evaluate the final polynomial at $r$ points; no table uses a mixed last level.

**Native verifier [formula counts, T7].** At rate 1/2, $L = 15$: Keccak-f calls 10130 to 7242 (-28.5 percent, including 162 for $\mu$), field products 85422 to 125942 (+47 percent, 51230 of them window products). The whole proof verifies in 9 to 13 ms today **[measured]**; I expect no gain **[estimate]**.

**Recursive verifier [estimate].** Note 08 measured 478 cycles a level-0 query in a 2-to-1 recursion and estimated a `KECCAK` step at 8 cycles of proving cost; its fitted formula gives 554 cycles and 22.6 steps a level-0 query at $\mu = 30$, about 735 cycle-equivalents. A mixed query adds one or two steps for $\mu$ and, at two cycles a changed factor (one addition, one product) and four a partner, about 750 cycles: 1490 cycle-equivalents. So 125 mixed queries cost 186 thousand where 218 queries cost 160 thousand, and the 121 points of levels 0 and 1 add about 37 thousand. With the model's totals (cycles plus 8 a step, T3 and T4): +36 to +38 percent at rate 1/2, +54 at 1/4, +73 at 1/8, +49 at 1/16 for the byte-optimal configurations; with level 0 alone mixed, +23, +31, +40 and +49 percent. At one cycle a changed factor, the most favourable count, level-0-only mixing at rate 1/2 about breaks even. The plain-fold Reed-Solomon instance is +3 to +7 percent (its points), as the paper says of Protocol D. So the answer to "which $L$ minimizes recursive verifier work" is none: the queries saved are worth less than the window weights. Delegating the weight evaluation to a small sumcheck over (query, partner, variable) could cut it several times; I did not design it.

### 7.3 Complexity added

- **Both provers.** A second pass over the level's codeword with the hashing moved into it, the derivation of $\mu$, the stored codeword, the plain fold (which removes the multiplication by $X$ in the novel basis and two scalars a round), the points of Protocol D, and at query time the rebuild of a mixed row from $r$ rows.
- **Three verifiers.** The $\mu$ oracle, the window weights, the plain fold and the points, in `crates/verifier`, the Lean verifier and the guest; the guest grows, and it is compiled to a fixed point on its own size.
- **The paper's Lean development** (12,200 lines; 9,500 outside `Constructions`). Verbatim: `DeepFold/Counting.lean`, `Protocol/Potential.lean`, `Soundness/RBR.lean`, `Interleave/Basic.lean`, `Tree.lean`, `Closed.lean`, `TwoLanes.lean`, `Projection.lean`, and `lemmaP` up to the definition of the list. To generalize, with a family of position functionals `pos : X → K[X] →ₗ[K] K` in place of `D : Finset K` and `eval`, and a challenge in `K` in place of `K × K`: `aff`, `Cand`, `CandL`, `Cons`, `ConsL`, `Delta`, `DeltaL`, `IsFoldL`, `agr`, `agrL`, `agrPair`, `agrPairL`, `fullT`, `ExcL`, `listW`, `agrW`, `foldPair`, `Word`, `foldW`, `levelPot`, `Good`, `InList`, `NearT` (one column becomes $t$), `foldWord`, `foldTuple`, `pull`, `foldWeight`, `foldClaim` and `FoldAns` (two scalars), `foldVal`, `Doomed`, `Doomed₁`, `nextW` (`leval (x q)` becomes `pos (x q)`), `nextC` and `Handover` (no high part), `Level` and `Level.OK` (`choose_le` becomes $\lfloor n/(t+1) \rfloor \le M$, `thr_step` a step of $t$), `Level.HK`. To drop: the rational functions of `DeepFold/Class.lean` and `card_quadric_zeros_le`. New: the pigeonhole of Lemma F' in place of `card_agrL_outside_le`, `nearT_unique` and `NearT.fold_eq` from `AgreeLE`, Proposition I' as an induction over `listBound_prod` (about 150 lines), the bridge from `GenListBound`. I estimate 5,000 to 6,000 lines touched, almost all by retyping, with less mathematics than the original: one to two weeks for someone who knows the development, or two to three rounds of this swarm. **[estimate]**
- **`formal/`.** Adopting Protocol D is already a rewrite of the PCS part of the soundness proof, of the verifier transcription and of the guest's proof. D' adds: the code as position functionals built from $\pi$; Theorem M, as a formal proof (no complete proof exists on paper yet) or as a hypothesis of the end statement; the extractor's decoder and its cost bound (4.4), which is a proved theorem today.

## 8. The net

The honest comparison is at equal prover cost, because a lower rate is already an option of the deployed protocol and is proved. With $E$ the commitment work at rate 1/2 (190 ms at the benchmark) and the measured parts of 7.1:

| code | prover, units of $E$ | level-0 queries | opening at $\mu = 30$, KiB | needs |
| --- | --- | --- | --- | --- |
| Reed-Solomon, rate 1/2 | 1 | 218 | 335.9 | deployed |
| mixed, rate 1/2, $L = 15$ | 1.8 to 2.2 (2.8) | 125 | 236.7 | Theorem M at five pairs |
| Reed-Solomon, rate 1/4 | 2 | 109 | 222.6 | deployed |
| mixed, rate 1/4, $L = 16$ | 3.3 to 4.1 (5.3) | 64 | 173.0 | Theorem M |
| Reed-Solomon, rate 1/8 | 4 | 73 | 180.7 | deployed |
| mixed, rate 1/8, $L = 16$ | 6.2 to 7.8 (10) | 45 | 152.1 | Theorem M |
| Reed-Solomon, rate 1/16 | 8 | 55 | 158.7 | deployed |
| mixed, rate 1/16, $L = 17$ | 12 to 15 (20) | 36 | 138.1 | Theorem M |

(Prover units **[estimate]**: the rate's own commitments, plus mixing and $\mu$ at 0.47 to 0.86 of them, 1.5 at the pessimistic factor, plus the points at 0.37 $E$ whatever the rate.) The mixed code at rate $\rho$ sits on the curve of plain Reed-Solomon next to rate $\rho/2$: at rate 1/2 it is 6 percent larger than rate 1/4 at the same cost (rate 1/4 also has fewer queries, and always will: the mixed code at rate 1/2 cannot go below 114 queries, the pigeonhole value, and Johnson at rate 1/4 gives 109); at rates 1/4 and 1/8 it gives 4 percent fewer bytes than the next deployed rate at 80 to 100 percent of that rate's cost, more at the pessimistic factor. This is the old identity of the paper's section 2.3: capacity at rate $\rho$ is Johnson at rate $\rho^2$, and the mixing costs about as much as one halving of the rate. On top of that the verifier does 50 to 100 percent more field products, the recursion is 23 to 73 percent more expensive **[estimate]**, knowledge soundness needs either large fold grinds or a decoder nobody has, and four code bases change.

So, if Theorem M is proved: **proof size** -13 to -30 percent at a fixed rate, between +6 and -4 percent at a fixed prover cost; **prover** +27 to +39 percent at a fixed rate (measured parts), up to +59; **native verifier** about unchanged; **recursion** worse; **complexity** large. I would not do it in this form; section 9.5 says what changes with the ladder of constant lists. Two further cases would change it: a list bound that needs no window (the rounds 5 to 10 question), which keeps Reed-Solomon, the affine fold and one weight a query, and for which the paper's accounting (its section 7.2) gives up to -26 percent from level 0 alone and -37 percent with every level; or a deployment that already sits at the lowest rate it can afford in memory and wants the last 13 percent.

## 9. The ladder with constant lists (note 57, section 8)

Added at the lead's request. Hypothesis $\mathsf{T}_t$ at agreement $A$ **[hypothesis, note 57 section 8]**: for every word $D \to K$, every $t$ members of its list at agreement $A$, with agreement sets trimmed to $A$ positions and cover counts $c_x$, satisfy $\sum_x (c_x - 1)_+ \le B_t(A) := (t - 1)k + (t\,nH(A/n) + 130)/64$. For affinely independent members this is the first moment at rank $t - 1$; for dependent ones the lead expects it from the lower rungs and the distance. $\mathsf{T}_2$ is the agreement bound of Fact 4.1.

### 9.1 The exact finite inequality

**Proposition J [proved].** Let $S_1, \dots, S_M$ be subsets of $A$ positions each of a set of $n$ positions, $2 \le t \le M$, and suppose every $t$ of them have $\sum_x (c_x - 1)_+ \le B$. Write $MA = nm_0 + \mathrm{rem}$ with $0 \le \mathrm{rem} < n$. Then
$$F_t(M, A) := tA - n + \frac{(n - \mathrm{rem})\binom{M - m_0}{t} + \mathrm{rem}\binom{M - m_0 - 1}{t}}{\binom{M}{t}} \ \le\ B.$$
*Proof.* Let $m_x$ be the number of sets containing $x$, so $\sum_x m_x = MA$. For a uniform $t$-subfamily the cover count at $x$ is hypergeometric and $\mathbb{E}(c_x - 1)_+ = \mathbb{E}c_x - 1 + \Pr[c_x = 0] = h(m_x)$ with $h(m) = tm/M - 1 + \binom{M - m}{t}/\binom{M}{t}$. The second difference of $m \mapsto \binom{M - m}{t}$ is $\binom{M - m - 1}{t - 2} \ge 0$, so $h$ is convex on the integers, and a sum of a convex function over integers of fixed sum is least on the balanced vector ($n - \mathrm{rem}$ values $m_0$, $\mathrm{rem}$ values $m_0 + 1$). So the average over the $t$-subfamilies of $\sum_x(c_x - 1)_+$, which is $\sum_x h(m_x)$, is at least $F_t(M, A)$, and it is at most $B$. $\square$

Since $\binom{(1 - \alpha)M}{t}/\binom{M}{t}$ increases to $(1 - \alpha)^t$, $F_t(M, A)$ increases to $n\,g_t(\alpha)$, $g_t(p) = tp - 1 + (1 - p)^t$, and $F_t(M, A) \approx n\,g_t(\alpha) - n\,\alpha(1 - \alpha)^{t-1}t(t-1)/(2M)$: this is the lead's correction, with its constant. **Consequence:** under $\mathsf{T}_t$ at $A$, if $F_t(M_0, A) > B_t(A)$ then every list at agreement $A$ has fewer than $M_0$ members (a longer list contains $M_0$ of them). The bound is finite exactly above the threshold $n\,g_t(A/n) > B_t(A)$ and is about $\alpha(1 - \alpha)^{t-1}t(t-1)\,n/(2(n\,g_t(\alpha) - B_t))$; it cannot go below $t - 1$. **[checked, `61_ladder.py selftest`: the identity and the bound on 40 random families by enumeration of all $t$-subfamilies; monotonicity in $M$ and the limit at $n = 2^{25}$; the first-order estimate within 25 percent; the lead's twenty thresholds to four digits.]**

The threshold is below Theorem M's at $L = t - 1$ by $(1 - \alpha)^t/t$, because in a long list a random $t$-subfamily leaves a share $(1 - \alpha)^t$ of the positions uncovered, where Theorem M's count assumes every position covered: 0.6689 against 0.6808 at $t = 3$, rate 1/2, and the same four digits from $t = 12$ on.

### 9.2 What it changes in the protocol

- **Obstacle (b) disappears.** The list of single $K$-valued words is a number below $2^{63}$, so the paper's Proposition 6.2 (`descent`, machine-checked for any code with a generator over $K$) gives at most $2M_0 - 1$ members for every number of lanes and for $E$-valued words. The code hypotheses of Theorem D' at a level on rung $t$ are $\mathsf{T}_t$ at $A^{(i,0)}$ and $\mathsf{T}_2$; no profile, no Proposition I'.
- **The points stay at the paper's Johnson counts:** 11 at level 0 and 8 at the next levels for every list up to $2^{39}$ (10 at level 0 for a list of 8). In prover time that is the 2.3 percent of note 24, not the 12 percent of section 7.1.
- **Obstacles (a), (c), (d) are untouched:** plain folds with a loss, the extractor's decoder, and the window weights.

### 9.3 Parameters

**Level 0, $\mu = 30$ [exact, L1 of `61_ladder.py`].** "Columns" is how far above the threshold the agreement must be for the list bound named; queries include the loss of the 12-bit fold grind.

| rate | $t$ | threshold $A/n$, without and with the entropy term | queries | list one column above the threshold | columns above it for a list of 1000, of 32 | points | Theorem M at $L = t - 1$: $A/n$, queries, points (Prop. I') |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | 3 | 0.6527, 0.6689 | 187 | $2^{23.1}$ | 2710, 80566 | 11 | 0.6808, 196, 12 |
| | 4 | 0.6198, 0.6354 | 166 | $2^{20.7}$ | 1604, 46667 | 11 | 0.6397, 169, 16 |
| | 5 | 0.5979, 0.6133 | 154 | $2^{21.2}$ | 928, 25063 | 11 | 0.6150, 155, 18 |
| | 8 | 0.5623, 0.5777 | 137 | $2^{18.5}$ | 160, 3345 | 11 | 0.5779, 137, 29 |
| | 16 | 0.5312, 0.5468 | 125 | $2^{11.6}$ | 1, 7 | 11 | 0.5468, 125, 61 |
| | 24 | 0.5208, 0.5364 | 121 | $2^{4.5}$ | 0, 0 | 11 | 0.5364, 121, 98 |
| 1/4 | 3 | 0.4421, 0.4643 | 98 | $2^{23.8}$ | 12591, 377389 | 11 | 0.5156, 114, 12 |
| | 4 | 0.4065, 0.4257 | 88 | $2^{24.5}$ | 10086, 304032 | 11 | 0.4530, 95, 16 |
| | 5 | 0.3820, 0.3996 | 82 | $2^{23.9}$ | 8088, 239346 | 11 | 0.4153, 86, 18 |
| | 8 | 0.3392, 0.3546 | 73 | $2^{25.2}$ | 4119, 114072 | 11 | 0.3585, 74, 29 |
| | 16 | 0.2967, 0.3107 | 65 | $2^{20.6}$ | 593, 10362 | 11 | 0.3108, 65, 61 |
| 1/8 | 3 | 0.3045, 0.3313 | 68 | $2^{26.5}$ | 37012, 1129899 | 11 | 0.4321, 90, 12 |
| | 5 | 0.2537, 0.2724 | 58 | $2^{25.4}$ | 29364, 895780 | 11 | 0.3140, 65, 18 |
| | 8 | 0.2167, 0.2313 | 52 | $2^{24.6}$ | 21125, 632377 | 11 | 0.2470, 54, 29 |
| | 16 | 0.1769, 0.1884 | 45 | $2^{23.4}$ | 8918, 226201 | 11 | 0.1907, 46, 61 |
| 1/16 | 3 | 0.2117, 0.2428 | 53 | $2^{27.7}$ | 93109, 2825708 | 11 | 0.3901, 80, 12 |
| | 5 | 0.1723, 0.1923 | 46 | $2^{27.1}$ | 81026, 2467417 | 11 | 0.2630, 57, 18 |
| | 8 | 0.1435, 0.1579 | 41 | $2^{26.3}$ | 67237, 2039421 | 11 | 0.1907, 46, 29 |
| | 16 | 0.1117, 0.1216 | 36 | $2^{26.9}$ | 43061, 1280284 | 11 | 0.1298, 37, 65 |

The lead's queries are confirmed (its 124 at $t = 16$, rate 1/2, is 125 with the exact query term). The list constant is a function of the margin: one column above the threshold it is at most about $nt$; 1000 members need at most 0.035 percent of the columns more, 32 members at most 1.05 percent (at $t = 3$, rate 1/16), which is one query at most. At low rates the small rungs gain little over today's 109, 73, 55 queries, as the lead says.

**The whole opening, $\mu = 30$ [exact, L2].** Rung $t$ at every level where it gives fewer bytes (clipped to $N_i - 1$): levels 0 and 1, and level 2 from $t = 6$ or 8 on. Points are 11 8 8 7 7 12 in every row but one (10 at level 0 for $t = 8$, rate 1/2).

| rate | today | $t = 3$ | 4 | 5 | 8 | 16 | 24 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2, queries (levels 0 1 2) | 218 55 32 | 187 53 31 | 166 49 31 | 154 46 31 | 137 41 28 | 125 36 24 | 121 34 25 |
| 1/2, KiB | 335.9 | 300.4 (-10.6%) | 276.8 (-17.6%) | 262.7 (-21.8%) | 239.8 (-28.6%) | 221.1 (-34.2%) | 216.4 (-35.6%) |
| 1/4, queries | 109 44 28 | 98 44 28 | 88 41 28 | 82 39 28 | 73 35 26 | 65 31 25 | 62 29 24 |
| 1/4, KiB | 222.6 | 207.8 (-6.7%) | 195.0 (-12.4%) | 187.2 (-15.9%) | 173.0 (-22.3%) | 160.5 (-27.9%) | 155.0 (-30.4%) |
| 1/8, queries | 73 37 25 | 68 37 25 | 62 36 25 | 58 34 25 | 52 31 24 | 45 27 24 | 43 25 23 |
| 1/8, KiB | 180.7 | 172.4 (-4.6%) | 165.0 (-8.7%) | 159.0 (-12.0%) | 149.1 (-17.5%) | 138.1 (-23.6%) | 133.3 (-26.2%) |
| 1/16, queries | 55 32 23 | 53 31 22 | 49 31 22 | 46 31 22 | 41 28 22 | 36 24 22 | 34 25 22 |
| 1/16, KiB | 158.7 | 150.7 (-5.0%) | 146.2 (-7.9%) | 142.8 (-10.0%) | 134.5 (-15.3%) | 125.3 (-21.1%) | 123.9 (-22.0%) |

**Against the $q^{L-1}$ version [exact].** At $L = t - 1$ with Proposition I' the openings at rate 1/2 are 310.8, 284.8, 271.3, 249.3, 236.7, 238.3 KiB for $t = 3, 4, 5, 8, 16, 24$: the ladder is 3 to 9 percent of the opening below (5 to 12 at rate 1/4), through the lower threshold at small $t$ and the points at large $t$; and where the $q^{L-1}$ version turns back from $L = 17$ on, the ladder keeps improving up to the largest rung the window admits. The byte optimum of sections 1 to 8 (235.2 KiB at $L = 17$) is passed at rung 12 (228.2).

### 9.4 The window a rung needs, and what a window costs

For the rank the lead asks $r \ge t + 1$ (the differences of $t$ members covering a position span up to $t - 1$ dimensions, so $r \ge t - 1$ is necessary). The isoperimetric side is researcher 60's. The cost side, which decides whether a small rung is cheap:

- **With XOR offsets nothing below $N$ offsets spans**, and windows that do not span are blocks (note 57, section 4). So with offsets in the group $\mathbb{F}_2^N$ every rung pays the cube: 324 changed factors a query at $\mu = 30$ (section 7.2, a lower bound for every spanning set), $N$ products a codeword word, one Keccak-f a position.
- **Index strides.** Take the partners of the position of index $v$ at the indices $v + 2^{j}$ modulo $n$, for $t$ exponents $j$ spread from 0 to $N - 1$. One stride of 1 generates the cyclic group, so $t$ partners span. Adding $2^j$ flips the bits $j$ to $j + c$ ($c$ the carry run, 1 on average), so the partner differs from $x$ by $\beta_j + \dots + \beta_{j+c}$ and changes the factors $k \le j + c$ only: about $\min(j + 2, \kappa)$ products **[proved for the count; the cycle figure is an estimate]**. The general fact is that the verifier's cost of a partner is the scale of its offset (the largest $k$ with the offset outside $U_k$), so a window is cheap exactly as far as it is local, and expansion asks for the opposite.

| window, level 0, $\mu = 30$, rate 1/2 **[exact counts, L4]** | partners | prover: products a codeword word | Keccak-f a position for $\mu$ | verifier: changed factors a query | guest cycles added a query (est.) |
| --- | --- | --- | --- | --- | --- |
| the cube, $r = N + 1 = 26$ | 25 | 25 | 1 | 324 | 756 |
| strides, $r = 4$ (rung 3) | 3 | 3 | 0.12 | 40 | 140 |
| strides, $r = 5$ (rung 4) | 4 | 4 | 0.16 | 54 | 186 |
| strides, $r = 6$ (rung 5) | 5 | 5 | 0.20 | 68 | 232 |
| strides, $r = 9$ (rung 8) | 8 | 8 | 0.32 | 110 | 370 |
| strides, $r = 17$ (rung 16) | 16 | 16 | 0.64 | 222 | 738 |

(A level-0 query is 735 cycle-equivalents today; the encode's field work is about 12 butterflies a word.)

- **Prover [estimate from the measured kernel].** The kernel of 7.1 costs 0.05 to 0.09 of the level's encode field work a partner (one and four threads), so on the benchmark, levels 0 and 1: rung 4 with strides 15 to 36 ms, rung 5 19 to 45, rung 8 30 to 71; plus $\mu$ (under 8 ms) and the points (14 ms): **+5 to +9 percent of `Prove` at rung 4, +6 to +11 at rung 5, +8 to +16 at rung 8**. With the cube window every rung costs 104 to 177 ms, +18 to +30 percent (+50 at the pessimistic factor): the list no longer costs anything, the window costs what it did.
- **Recursion [estimate, L2 and L3].** Cube windows: +24 to +71 percent at rate 1/2 (worst at the small rungs, which keep the most queries). Stride windows: level 0 alone on rungs 4 to 8, +0.2, -1.5, -1.9, -0.6 percent at rate 1/2 and +4 to +5 at rate 1/4; levels 0 to 2, +1 to +6 percent at rate 1/2 and +8 to +15 at rate 1/4. The queries saved pay for the windows and for the eleven points, no more.
- **What a sparse window weakens** (for researchers 58 to 60; I did not analyse it). A polynomial that is constant on blocks of $2^u$ consecutive indices sees $1 + \#\{j \ge u\}$ values on a stride window, where it sees $N - u + 1$ on the cube: the families of low local rank of note 57 section 7 multiply, and at the scales above the largest stride but one a window sees two values. And the circulant on $t$ spread strides is close to a $t$-dimensional torus of side $2^{N/t}$, whose bisection needs only about $n/2^{N/t}$ vertices: the constant $\sigma$ of the Isoperimetric Lemma would be about $2^{-N/t}/2$ (0.016 at $t = 5$, $N = 25$) **[estimate]**, against about 0.08 for the cube. Partners at pseudo-random positions expand best, cost the verifier a full chain each (145 cycles a partner at $\kappa = 24$, so five of them cost as much as the cube) and the prover a cache miss a row.

### 9.5 The net with the ladder

| code, rate 1/2 | prover, units of $E$ **[estimate]** | opening at $\mu = 30$, KiB | recursion (est.) |
| --- | --- | --- | --- |
| Reed-Solomon, rate 1/2 | 1 | 335.9 | |
| rung 5, stride window | 1.2 to 1.35 | 262.7 | +1% |
| rung 8, stride window | 1.3 to 1.5 | 239.8 | +6% |
| rung 16, cube window | 1.55 to 1.95 (2.55) | 221.1 | +27% |
| Reed-Solomon, rate 1/4 | 2 | 222.6 | -36% |
| rung 5 at rate 1/4, stride window | 2.3 to 2.6 | 187.2 | |
| Reed-Solomon, rate 1/8 | 4 | 180.7 | |

With the cube window the ladder is the comparison of section 8 with the points removed: rung 16 at rate 1/2 gives the opening of rate 1/4 at 80 to 98 percent of its prover cost and a much slower recursive verifier (rate 1/4 itself lowers the recursion metric by 36 percent). With stride windows the small rungs are well off the rate curve: rung 5 gives 262.7 KiB at 1.2 to 1.35 $E$ where interpolating between the deployed rates gives about 300, and at rate 1/4 it gives 187.2 KiB at 2.3 to 2.6 $E$ against 180.7 at 4 $E$. So the version worth pursuing is: **constant lists, a rung between 4 and 8, a window of $t + 1$ positions at spread dyadic index distances**, for 18 to 29 percent of the opening at rate 1/2, 5 to 16 percent of proving time and an unchanged recursion, if $\mathsf{T}_t$ can be proved for such windows. Everything else in this note still applies to it: the plain fold and its loss (section 4.1), the extractor (4.4), the fixed-seed oracle (5.2), and the change of code in two provers, three verifiers and `formal/`.

## 10. What I did not do

- I did not prove or test Theorem M, its interleaved form, the first-moment distance or the $t$-wise inequalities; sections 4 to 8 are conditional on the instances named in 5.1 and section 9 on $\mathsf{T}_t$ and $\mathsf{T}_2$. For stride windows no statement of note 57 exists yet: section 9.4 only prices them.
- Lemma F' and Theorem D' are proved by hand along the machine-checked proofs of the paper; only the class bound, completeness, the commutation facts, Proposition I' and the weight count were checked numerically, at toy sizes. Nothing was formalized.
- The mixing kernel is a standalone C kernel at one and four threads on a loaded machine, not an integrated prover; the 15-thread behaviour and every x86 machine are unmeasured. The split of the commitment span into field work and hashing is derived, not traced.
- The guest's cycles are note 08's fitted formula plus a count of products; no guest was written.
- The ladder schedules of the paper would lower the point scalars and the points' prover work here as there; I used one batch a level throughout.
- A decoder for the mixed code with many errors on a known set, and a delegated evaluation of the window weights, are open; either would remove one of the four obstacles and neither would change the comparison of section 8 by much.
