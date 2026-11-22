# 03. Attack-cost model and protocol knobs

Researcher 03. Scope: the exact cost of an attack on the Fiat-Shamir compiled opening of Annex B, what has to be bounded to lower a level's threshold $A$, what-if tables, and protocol-level ideas. Notation as in `00-lead-notes.md`. Scripts: `scripts/03_toy_checks.py` (exhaustive checks over $\mathrm{GF}(2^8)$, 12 s) and `scripts/03_whatif_tables.py` (all tables, under 1 s).

Every statement carries a status: **[proved]** (proof given here), **[checked]** (numerically, sizes stated), **[heuristic]** (a count of degrees of freedom or an average, not a proof), **[conjectured]**.

## 0. Verdicts

1. **The lead's cost model is right in substance.** An attack is a path, its cost is between the maximum and the sum of its per-message costs $2^{g}/p$ (Lemma P), a list of $L$ candidates at agreement $T$ gives an escape of probability about $L/|E|$ at a fold round, and that only matters when $T \ge A$. Section 8 lists what is wrong or missing in the notes and in the main document.
2. **The baseline (a word at agreement $A-1$ from a claim-satisfying codeword) is not an attack on the protocol.** It is the tight example for the state function's query term. A candidate fixed at commitment time that satisfies every claim is a valid witness. The cheapest real attack always starts with one escape for a commitment-time candidate, at cost at least $2^{g}|E|/L$.
3. **The flats family at rate 1/4 is a real attack as soon as $t_0 \le 107$** (cost $2^{109} + 2^{17+t_0}$ hash evaluations, with a constant-time success test). At the deployed $t_0 = 109$ it costs $2^{126}$: no attack, one bit of margin.
4. **The degree slack is usable**: a cheating prover can give lane $u$ degree up to $2^\kappa - 1 + (\text{number of rounds in which } u \text{ is on the } G \text{ side})$. So slack-1 families count in every lane but the all-$F$ one.
5. **The pole pair is never a real attack, with or without a claim weight, and restricting `FoldRoundBound` to nonzero weights does not remove it.** A coset pole pair gives $\Gamma(A) \ge 2^{\lfloor \log_2 (n/A) \rfloor}/|E|$ for every choice of weights (Proposition 4, checked exhaustively on a toy), because what a pole pair exploits is a claim that is true for a polynomial pair far from the committed word. For a claim false for every commitment-time candidate, a pole family of any size gives about one escaping line, the same as a single list member. For the present protocol this distinction is worth little: by Lemma A of note 01 a pole family is a list at degree $d+1$, and lists are real attacks with the same probability per member, so a claim-aware state function would save about one bit of fold grinding. It becomes necessary only with a protocol change that makes lists harmless (section 7.5).
6. **Corrected safe-threshold condition** (section 4): the list at $A - \ell$ must fit four budgets, $b_F = g_f + 2$ (fold), $b_B = g_b + 3 - \log_2 513 \approx g_b - 6$ (level-0 batching), $b_O = (128 s - 125 + g_o + 1 - s \log_2 \nu)/2$ ($s$ OOD points) and the next level's batching inside the query message, and the fold round needs in addition a bound on escapes through polynomials not explained by a close pair. Today the binding budgets are batching and OOD, both $2^{7}$, not the fold round's $2^{9}$.
7. **Grinding buys list budget only up to about $b = 20$**: there are 26 fold-round messages at $\mu = 30$, one Keccak permutation per attempt, so $b$ costs $26 \cdot 2^{b-2}$ permutations (8 times today's whole grinding work at $b = 20$, 450 times at $b = 26$). The lead's $b = 30$ to $40$ is not affordable.
8. **Most promising protocol-level package**: (a) give the OOD claim its own batching coefficient, which turns the batching terms from $(J-1)L/|E|$ into $(J + L)/|E|$, (b) a second OOD point, which lifts the OOD budget to $2^{68}$, (c) fold grinding chosen per level. All three are small protocol changes and stay inside the present proof architecture. They move the usable list budget from $2^{7}$ to $2^{16}$ at 1.2 times today's grinding work, or $2^{20}$ at 8 times. The research side then needs, at agreement $T$: $\Lambda(T) \le 2^{b}$ and the same budget for unexplained escapes. With the lists of note 01 and any budget up to $2^{27}$, the best reachable ladders are 0.70, 0.80, 0.66 and 0.60 of today's opening size at level-0 rates 1/2, 1/4, 1/8, 1/16 ($t_0 = 160, 108, 54, 36$), against 0.51 at capacity.

## 1. The verifier messages

End to end, in transcript order (`08-end-to-end-protocol.tex`, `crates/verifier/src/whir.rs`). $\mu = 30$: six levels, folds $(6,4,4,4,4,4)$, $\kappa_i = (24,20,16,12,8,4)$, rate exponents $R_i = R + (0,3,6,9,12,15)$, message variables $\nu_i = (30,24,20,16,12,8)$. The ladder has the same shape at every level-0 rate.

| message | count at $\mu=30$ | grind | error in `thm:rbr` | list budget $b$ (log2) today |
| --- | --- | --- | --- | --- |
| OOD point $z_i$ after each commitment (level 0's is the first challenge of the whole proof) | 6 | 15 | $\binom{L_i}{2}\nu_i/\lvert E\rvert$ | 7.05 at $\nu = 30$ |
| ring-switch map and $\lambda_0$ (one message) | 1 | 13 | $(J_0+1)L_0/\lvert E\rvert$, $J_0 \le 512$ | 7.00 |
| fold $(\alpha,\beta)$ | 26 | 7 | $\varepsilon_{\mathrm{aff}} + 2L/\lvert E\rvert$ | 9 |
| queries of level $i$ and $\lambda_{i+1}$ (one message) | 6 | 17 | $((A-1)/n)^{t} + (t+1)L_{i+1}/\lvert E\rvert$ | 11 to 15 (half the budget to the list) |
| tail sumcheck | 4 | 0 | $2/\lvert E\rvert$ | none |

One grind attempt is one Keccak-f permutation (`Sponge::absorb_nonce`: absorb the nonce, permute, test the low bits of lane 2). Today's grinding work is $26 \cdot 2^{7} + 2^{13} + 6\cdot 2^{15} + 6 \cdot 2^{17} = 994{,}560$ permutations, 79% of it the query grinds. **[checked]** against the constants in `whir.rs`.

## 2. The cost model

**Setting.** Random oracle, a grind of $g_m$ bits before verifier message $m$. A query to the oracle for message $m$ fixes the whole prefix (prover messages and nonce) and returns a challenge that is uniform and passes the grind with probability $2^{-g_m}$.

**Lemma P (paths). [proved]** Suppose every accepting transcript $\tau$ has a *type* $\pi(\tau)$ in a finite set $\Pi$, and for each type $\pi$ a set of pairs $(m, E^\pi_m)$, where $E^\pi_m$ is an event on (prefix before $m$, challenge of $m$), such that (i) an accepting transcript of type $\pi$ satisfies $E^\pi_m$ at every $m$ of $\pi$ and (ii) for every prefix, $\Pr_{\text{challenge}}[E^\pi_m] \le p^\pi_m$. Then an adversary making $Q$ oracle queries outputs an accepting transcript with probability at most $Q \sum_{\pi} \min_{m \in \pi} 2^{-g_m} p^\pi_m$, plus the usual term for challenges it never queried. Conversely the staged strategy "at each $m$ of the path, redraw until $E_m$" succeeds with expected cost $\sum_{m \in \pi} 2^{g_m}/p_m$ when it can realize each $E_m$ with probability $p_m$.

*Proof.* Fix $\pi$ and let $m^\ast$ minimize $2^{-g_m}p^\pi_m$. An accepting transcript of type $\pi$ contains an answered query for $m^\ast$ whose answer passes the grind and satisfies $E^\pi_{m^\ast}$. Each query does so with probability at most $2^{-g_{m^\ast}}p^\pi_{m^\ast}$, by (ii) and independence of the grind bits. Union over the $Q$ queries and over $\Pi$. The converse is the mean of a sum of geometric variables. $\square$

Round-by-round soundness is the special case where each type is one event, "the state leaves doom at $m$". So: **the cost of a path is its most expensive event, up to the number of events** (sum versus max), and the present theorem bounds the cheapest event of each path of a two-state function. An attack listed below is *real* when I can name a path all of whose events are cheap. It is *a failure of the state function only* when every path through it contains a second event that is expensive, which a two-state function cannot see.

**What a real attack looks like. [proved for commitment-time candidates, given the outer protocol's soundness for a fixed witness]** Let the statement be false. Call a polynomial tuple $U$ a *commitment-time candidate* of level $i$ if it is a function of the transcript up to the commitment of $\mathcal{O}^{(i)}$. Because the level-0 OOD point is drawn before every other challenge, each such $U$ fails the claims current at level $i$ unless a verifier message between the commitment and now escaped *for that $U$*: an outer message (budgeted at $2^{-125}$ per candidate), a batching $\lambda$ (at most $(J-1)/|E|$), or a fold round (at most $2/|E|$, the conic below). After one escape for $U$ the prover is honest for $U$, and the only remaining event is that every query of the level lands where $U$ agrees with the committed word. Hence the cost formula, for level $i$, a word $\mathcal{O}$ and an agreement $T$:
$$C(\mathcal{O}, T) \;\approx\; \frac{2^{g}\,|E|}{\omega\,\Lambda_{\mathcal{O}}(T)} \;+\; 2^{17}\Bigl(\frac{n_i}{T}\Bigr)^{t_i}, \qquad (g,\omega) = (g_f,\ 1\text{ to }2)\ \text{or}\ (g_{\text{batch}},\ 1 \text{ to } J-1),$$
where $\Lambda_{\mathcal{O}}(T)$ counts the usable candidates of $\mathcal{O}$ at agreement at least $T$, and "the committed word" is the word of the level at which the prover switches. The lead's statement holds with "the committed word of some level" in place of "the committed word". The only other source of polynomials is the fold itself: members of a folded word's list that are not folds of commitment-time candidates. Section 3.4 shows that for the known families they add about one line, $1/|E|$ per attempt, whatever their number.

## 3. Explicit strategies

### 3.1 The fold-round residual

Write $\Lambda_\iota := \langle W(\iota,\cdot), \cdot\rangle$, which depends only on a polynomial's low part (its residue modulo $\widehat W_\kappa$), and let the prover's table be $m = (u_0, v, c_0, c_1)$ (the document's $v_G, v_F, \tau_0, \tau_1$). For a pair $(F,G)$ with $c^\ast := \Lambda_0F+\Lambda_1G$ and $P = G + (\alpha+\beta X)F$, in characteristic two,
$$\Delta_{F,G}(\alpha,\beta) := \Lambda_\alpha(P) - \sigma'_m(\alpha,\beta) = \delta_G + \alpha(\delta_G + e) + \alpha^2\delta_F + \beta\,\delta_0 + \alpha\beta(\delta_0+\delta_1),$$
with $\delta_G = \Lambda_0 G - u_0$, $e = c^\ast - c$, $\delta_F = (\Lambda_0+\Lambda_1)F - v$, $\delta_\iota = \Lambda_\iota(XF) - c_\iota$. **[proved]** by expanding $\Lambda_\alpha = (1+\alpha)\Lambda_0 + \alpha\Lambda_1$; **[checked]**: the toy script evaluates the two sides independently.

**Lemma 1 (one candidate's escape set). [proved]** Let $e \ne 0$. (a) $\Delta \ne 0$. (b) If $(\delta_0,\delta_1) \ne (0,0)$, the zero set has between $|E|-1$ and $2|E|-1$ points: for every $\alpha$ with $\delta_0 + \alpha(\delta_0+\delta_1) \ne 0$ there is exactly one $\beta$. (c) If $\delta_0=\delta_1=0$ the zero set is $\{\alpha \in \text{roots of } \delta_G + \alpha(\delta_G+e)+\alpha^2\delta_F\} \times E$: zero, one or two whole lines. (d) For every $\alpha_0 \ne 1$ the table that is honest for $(F,G)$ except $u_0 = \Lambda_0G + \alpha_0 e/(1+\alpha_0)$ gives $\Delta = e(\alpha+\alpha_0)/(1+\alpha_0)$, the whole line $\alpha = \alpha_0$.

So every candidate with a false claim escapes with probability about $1/|E|$ per attempt whatever the prover sends, and a prover can always aim one line at one candidate ("guess $\alpha$"). **[checked]** toy 2a: each of 15 candidates has exactly $|E| - 1 = 255$ escaping pairs.

**Lemma 2 (a list in the $G$ half gives $L$ lines, and a constant-time success test). [proved]** If the candidates are $(F, G_i)$ with one common $F$ (the list varies only in lanes on the $G$ side of this round) and the table is honest for $F$, then $\Delta_i = \delta_G^i(1+\alpha) + \alpha e_i$, with the single root $\alpha_i = \delta_G^i/(\delta_G^i+e_i)$. The escape set is the union of the lines $\alpha = \alpha_i$, of probability $\#\{\alpha_i\}/|E|$, and the prover recognises success by looking $\alpha$ up in a table of $L$ entries. **[checked]** toy 2b: 15 candidates, 15 distinct lines, 3840 = 15|E| escaping pairs.

This matters for whether a list attack is real in time and not only in oracle queries: against a generic list the prover tests $L$ conics per attempt, so its work is about $|E|$ conic evaluations whatever $L$ is. With the list placed in the $G$ half the test is one lookup. Any single-lane list can be placed there (put the bad word in a lane that is on the $G$ side in round 1, exact codewords elsewhere).

### 3.2 (i) The baseline

*Strategy.* Commit to a word that agrees with a tuple $U$ on $A-1$ columns, claims true for $U$, honest for $U$ throughout. The verifier accepts with probability exactly $((A-1)/n)^{t}$ per query attempt, cost $2^{17}(n/(A-1))^{t} \approx 2^{125}$.

*Verdict.* **Failure of the state function only, and a tight one.** [proved] It violates "some member of $\mathrm{lst}(\mathcal{O}; A - \ell, d)$ satisfies the claims" only because $U$ sits one point outside the list. $U$ is fixed at commitment time and satisfies every pooled claim, so by the outer protocol's soundness the statement is true (or an outer message already escaped for $U$, at cost $2^{125}$). The same holds at later levels: a claim-satisfying codeword of level $i+1$ close to nothing is the honest continuation or needed an escape. Consequently the query term is not what an attacker pays first. With a unique candidate ($L = 1$) the cheapest real path inside the opening is a fold escape, $2^{7}\cdot 2^{128} = 2^{135}$ (or the batching message, between $2^{132}$ and $2^{141}$ depending on how many roots its polynomial can be given).

The consequence for the swarm is the lead's point, now with a proof: the true minimum $t$ of a level is set by the largest agreement at which usable lists exceed the escape budget, not by the Johnson radius.

### 3.3 (ii) A large list at agreement $T \ge A$: flats, rate 1/4

Concrete instance, $\mu = 30$, $R = 2$: $n = 2^{26}$, $\kappa = 24$, word $w(x) = x^{2^{25}-1}$, candidates $Q_V$ for the $2^{26}-1$ hyperplanes $V$ of $D$, each of genuine degree $2^{24}-1$ and agreeing with $w$ exactly on $V \setminus \{0\}$, $T = n/2 - 1$. **[checked]** on $n = 16$ (toy 1: 15 hyperplanes, 15 distinct $Q_V$ of degree 3, agreement exactly 7). $w$ and the $Q_V$ are $K$-valued, as level 0 requires: level 0 commits $K$ words, and an $E$ polynomial agreeing with a $K$-valued word on more than $d$ points of $D \subseteq K$ has coefficients in $K$ **[proved]**: its $y$-coordinate vanishes there.

*Strategy.*
1. Take a valid execution $q'$ of the program on a *different* public input. Commit to $\mathrm{Enc}(q')$ with $w$ added to one lane that is on the $G$ side of round 1. The commitment-time candidates at agreement $T$ are $U_V = q' + Q_V e_{\text{lane}}$.
2. Level-0 OOD point: answer with any candidate's value. **It plays no role on this path.** The OOD claim is one of the batched claims, and a fold escape works for a candidate whatever claim it violates.
3. Run the outer protocol honestly for $q'$. Every outer check passes. The two public-input claims are false for every candidate.
4. Batching $(\Phi, \lambda_0)$: nothing needed. (An escape here is possible, with probability at most $513\,L/|E|$ and realistically about $L/|E|$ **[heuristic]**: a candidate's difference polynomial has degree up to $J_0 - 1$ but about one root on average. At a 13-bit grind this path costs $2^{141}/(L\,\omega)$, more than the fold path unless $\omega > 2^{6}$.)
5. Fold round 1: send the table honest for the common $F$. By Lemma 2 the round escapes with probability $(2^{26}-1)/2^{128}$ up to collisions among the $\alpha_V$. Expected cost $2^{7} \cdot 2^{102} = 2^{109}$ permutations and a table of $2^{26}$ entries.
6. After the escape the running claim is true for the fold of $U_{V^\ast}$. Be honest for it through the remaining 25 fold rounds and all later levels. The per-pair conics of other candidates are not used again.
7. Level-0 query message: accepted iff all $t_0$ queries fall in $V^\ast\setminus\{0\}$, probability $(1/2 - 2^{-26})^{t_0}$, cost $2^{17+t_0}(1+2^{-25})^{t_0}$.

*Cost.* $2^{109} + 2^{17 + t_0}$: $2^{126}$ at the deployed $t_0 = 109$, $2^{125}$ at 108, $2^{124}$ at 107. **Real attack for $t_0 \le 107$**, in oracle queries and in time. To neutralise the family by grinding one needs $2^{g_f + 128 - 26} \ge 2^{125}$, $g_f \ge 23$.

*Later levels.* The same strategy works at any level $i \ge 1$ with that level's own word: commit $\mathcal{O}^{(i)}$ with a list at agreement $T'$ on $D_i$, escape either at $\lambda_i$ (which rides level $i-1$'s query message: probability at most $(t_{i-1}+1)L'/|E|$, 17-bit grind) or at a fold round of level $i$, then pay $2^{17}(n_i/T')^{t_i}$. Words are $E$-valued there. So each level needs its own list bound at its own rate $2^{-(R+3i)}$, and at those rates flats sit at $2\rho$, far beyond Johnson.

*Degrees.* **[proved]** Lane $u$ is multiplied by $\prod (\alpha_j + \beta_j X)$ over the rounds $j$ in which it is on the $F$ side, and the level ends with the prover sending $\ell$ high coefficients and committing the low part, which pins the fold to degree at most $2^\kappa - 1 + \ell$ and nothing more. So a candidate may have lane degrees up to $2^\kappa - 1 + g(u)$, $g(u)$ the number of rounds in which $u$ is on the $G$ side, and stays consistent with every later check. The claims only read residues modulo $\widehat W_\kappa$, so they do not see the excess. The analysis's uniform $d = 2^\kappa - 1 + \ell$ is an over-count only for lanes with $g(u) < \ell$. In particular lists of degree exactly $2^\kappa$ are usable in every lane but the all-$F$ one: at rate 1/2 the coset-union count at $9n/16$ is 11440, not 715, and pinning $e_1$ by pigeonhole ($M = 32$ cosets, $m = 18$) gives at least $\binom{32}{18}/32 \approx 2^{23.8}$ there (**[proved]**: $e_1$ is a sum of labels, one of $M$ values; **[checked]** on $n = 64$, $M = 8$, $m = 6$, toy 4). Note 01 reaches the same conclusion from the pole pair (its Lemma A, with degree $d+1$ on the list side) and has much larger families, $2^{29.4}$ at $5n/8$; its table is the one to use.

### 3.4 (iii) The pole pair

**Proposition 4 (coset pole pair, any weights). [proved; checked exhaustively on $n=32$, $|E| = 256$, toy 3]** Let $W \subseteq D$ be a subspace with $|W| \ge A \ge d + 3$, $M = n/|W|$, $\beta_0 \in E \setminus D$, and in one lane $f_0 = 1/(x - \beta_0)$, $f_1 = L_W(x)/(x-\beta_0)$ (zero in the other lanes). Then no pair of degree at most $d$ agrees with $(f_0,f_1)$ on $A - 1$ points, and for *every* $\Lambda_0, \Lambda_1$, with claim $c = 0$ and table $(0, 0, \Lambda_0(1), \Lambda_1(1))$, all $M|E|$ challenges with $\alpha + \beta\beta_0 \in L_W(D)$ escape. So any $N$ with `FoldRoundBound dom d A N` has $N \ge |E| \cdot 2^{\lfloor\log_2(n/A)\rfloor}$ when $A$ is at least $d+3$.

*Proof.* $F(X)(X - \beta_0) - 1$ is nonzero of degree at most $d + 1 < A - 1$, so $f_0$ has no close $F$. The fold is $\beta + (L_W(x) + \alpha + \beta\beta_0)/(x - \beta_0)$, equal to the constant $\beta$ on the coset of label $\alpha + \beta\beta_0$. For $P = \beta$: $(1-\alpha)\Lambda_0P + \alpha\Lambda_1P = \beta\Lambda_0(1) + \alpha\beta(\Lambda_1(1)-\Lambda_0(1))$, which is the table's folded claim. $\square$

Adding a polynomial pair $(\tilde F, \tilde G)$ to $(f_0, f_1)$ gives the same with $c = \Lambda_0\tilde F + \Lambda_1 \tilde G$. So the escape is there exactly when *the claim is true for the polynomial part*, a pair that is nowhere near the word.

This is the tight example for the $\ell_B/|E|$ term of `def:epsaff`, so it is within budget in the Johnson regime. It caps any analysis that uses $\Gamma$ as defined: a level needs $2^{\lfloor \log_2(n/A)\rfloor} < 2^{g_f + 3}$, so **bits per query below $g_f + 3 = 10$**. The deep levels (rate exponents 13 to 19) are near this cap already.

**The general pole pair with a claim. [proved]** By Lemma A of note 01, every list $\{C_i\}$ of a word at degree $d+1$ is a pole family: the fold agrees with $\beta + P_\gamma$ on the line $\alpha + \beta\beta_0 = \gamma$, with $\gamma = C_i(\beta_0)$ and $P_\gamma = (C_i - C_i(\beta_0))/(X - \beta_0)$. Let $M^\ast$ be the number of lines. Restricted to a line, the residual is a quadratic in $\alpha$, and it vanishes identically iff, with $a := (c_0 + \Lambda_0(1))/\beta_0$ and $a'' := (c_1 + \Lambda_1(1))/\beta_0$,
$$\Lambda_0(P_\gamma) = u_0 + \gamma a, \qquad \Lambda_1(P_\gamma) = c + a + \gamma a'', \qquad v = a + a'' .$$
So the lines that escape whole are the points $(\gamma, \Lambda_0P_\gamma, \Lambda_1P_\gamma) \in E^3$ lying on one line of the three-parameter family $\{(\gamma,\ u_0 + \gamma a,\ c + a + \gamma a'')\}$. Every other line of the family contributes at most 2 challenges. Three cases:

| case | escaping challenges | status |
| --- | --- | --- |
| weights zero on the $P_\gamma$ (in particular zero weights) and $c = 0$; or $P_\gamma$ affine in $\gamma$ with $c$ the matching value | all $M^\ast|E|$ | [proved]; toy 3c: 1024 of 1024 |
| any weights, any $c$, table chosen for one $\gamma$ | $|E| + O(M^\ast)$: one whole line, since one point always lies on such a line | [proved]; toy 3c: 259 |
| generic values $\Lambda_\iota(P_\gamma)$, any table | at most $k^\ast|E| + 2M^\ast$, $k^\ast$ the largest number of the $M^\ast$ points on one admissible line; $k^\ast \ge k$ needs $2k - 3$ coincidences | [heuristic] for the count of coincidences; toy 3c: at most 8 = 2 per line over 20 random tables |

So "with a nonzero weight each line keeps at most two escapes" is false as stated: a table can always take one line whole, and all lines escape for nonzero weights that vanish on the $P_\gamma$, or when the claim is the polynomial part's.

*Verdict.* **Not a real attack in any of the cases; a failure of the state function in the first.**
- Zero weight: there is no claim, so nothing false is proved. It breaks proximity ("the word is close to the code"), which no claim of the outer protocol needs: every pooled claim has weight $\ne 0$ and the level-0 weight contains $\lambda_0^{J-1}\mathrm{eq}(z_0,\cdot)$, nonzero on every lane.
- All lines escaping needs the running claim to be true for the polynomial part $\tilde U$, which is a commitment-time candidate. For a false statement that takes an earlier escape for $\tilde U$ (probability at most $(J-1)/|E|$), after which committing $\mathrm{Enc}(\tilde U)$ honestly is strictly better than the pole word. **[proved]** by the principle of section 2.
- One whole line by choice of the table is $1/|E|$ per attempt, the same as one list member, cost $2^{135}$.
- Protocol weights are sampled after the commitment (each level's weight contains $\lambda\,\mathrm{eq}(z_i,\cdot)$ with $z_i$ fresh), so $k^\ast$ lines escape with probability about $\binom{M^\ast}{k}|E|^{-(2k-3)}$ over the weights. Even for $M^\ast = 2^{64}$ this leaves $k^\ast \le 2$ except with probability about $2^{-195}$ (and $k^\ast = 2$ about half the time). **[heuristic]**

On the proof side: with worst-case weights $\Gamma^{\mathrm{un}}(a) \ge M^\ast(a)/|E|$ (notation of section 4), and $M^\ast(a)$ is, up to collisions, the list size at degree $d+1$. So in the present analysis pole families take about as much of the fold budget as the list itself, as the $\ell_B$ term of `def:epsaff` already does inside Johnson. They are not a separate obstruction: where lists at degree $d+1$ fit the budget, pole pairs do too. What is missing beyond Johnson is the converse, a proof that nothing else escapes.

### 3.5 OOD collisions

The OOD term $\binom{L}{2}\nu/|E|$ charges any pair collision. What a collision buys a real attacker is $m$ candidates consistent with the OOD answer, hence $m$ tries at the next escape (an outer message at level 0; nothing better than $m\rho^{t}$ at later levels, since a candidate that satisfies the residual claim is far from the folded word). **[proved]** $\Pr[\text{some } m \text{ candidates collide}] \le \binom{L}{2}\nu / (\binom{m}{2}|E|)$ (Markov on the number of colliding pairs). For a list with no collision structure an $m$-fold collision has probability about $\binom{L}{m}(\nu/|E|)^{m-1}$, so at $L = 2^{26}$ only $m = 2$ is reachable: one bit. But the worst case over list structure is the Markov bound: at $L = 2^{26}$, $m = 2^{13}$ at stage cost $2^{112}$, leaving about 112 bits (script, section E). So the quadratic term is mostly a state-function artifact, but not provably one, and a second OOD point is the right fix.

## 4. The corrected safe-threshold condition (replaces section 3 of the main document)

Fix a level: $n$, $\kappa$, $\ell$, $d = 2^\kappa - 1 + \ell$, $\nu = \kappa + \ell$, $t$ queries, incoming claim count $J$ (at level 0 the search's row is $(J_0+1)L$ with $J_0 \le 512$: the stacked claims and the ring switch's two; $t_{i-1}+2$ after), grinds $g_f, g_b, g_o, g_q$, $s$ OOD points, target 125 bits, $|E| = 2^{128}$.

**Definitions.**
- $\Lambda(a)$: the largest list of tuples of degree at most $d$ at agreement at least $a$, as in the main document. $\Lambda^{\mathrm{use}}(a) \le \Lambda(a)$: the same with lane $u$ at degree at most $2^\kappa - 1 + g(u)$ and, at level 0, $K$-valued words.
- $\Gamma^{\mathrm{un}}(a)$: the largest density of challenges $(\alpha,\beta)$, over violating instances and tables, for which some $P \in \mathrm{lst}(\text{fold}; a, d)$ that is *not* $G + (\alpha+\beta X)F$ for a pair of $\mathrm{lst}(f_0,f_1; a - 1, d)$ satisfies the folded claim. Then $\Gamma(a) \le 2\Lambda(a-1)/|E| + \Gamma^{\mathrm{un}}(a)$ **[proved]**, by Lemma 1(a) and Schwartz-Zippel for the explained members.

**Sufficient (the present proof with the Johnson bound replaced).** The level is safe at $A$ if, with $L := \Lambda(A - \ell)$:

| message | condition | list budget |
| --- | --- | --- |
| fold round $j$ | $2\Lambda(A - \ell + j - 1)/\lvert E\rvert + \Gamma^{\mathrm{un}}(A-\ell+j) \le 2^{-(125 - g_f)}$ | $L \le 2^{g_f + 2}$, less the room $\Gamma^{\mathrm{un}}$ takes |
| level-0 batching | $513\,L/\lvert E\rvert \le 2^{-(125-g_b)}$ | $L \le 2^{g_b + 3}/513 \approx 2^{g_b - 6}$ |
| batching of level $i \ge 1$ | $((A_{i-1}-1)/n_{i-1})^{t_{i-1}} + (t_{i-1}+1)L/\lvert E\rvert \le 2^{-(125 - g_q)}$ | $L \le 2^{g_q + 2}/(t_{i-1}+1)$ at half the budget |
| OOD | $\binom{L}{2}(\nu/\lvert E\rvert)^{s} \le 2^{-(125-g_o)}$ | $L \le 2^{(128s - 124 + g_o - s\log_2\nu)/2}$ |
| queries | $t \ge (125 - g_q)/\log_2(n/(A-1))$, plus the next level's batching row | none |

Present values ($g = (7,13,15,17)$, $s = 1$): $b = 9$, $7.00$, $11$ to $15$, $7.05$. **The binding budgets are batching and OOD at $2^{7}$**, which is why `MAX_LIST_0` is of that size, and the fold round's $2^{9}$ ("$2^{10}$" in the main document) is not the constraint today.

**Floors of this condition, whatever is proved about lists. [proved]** $\Gamma^{\mathrm{un}}(a) \ge 2^{\lfloor\log_2(n/a)\rfloor}/|E|$ (Proposition 4) and $\Gamma^{\mathrm{un}}(a) \ge M^\ast(a)/|E|$, $M^\ast$ the number of pole lines, about the list size $\Lambda_{d+1}(a)$ at degree $d+1$ (note 01, Lemma A). So this state function needs $n/A < 2^{g_f+3}$ and in effect $2\Lambda_d + \Lambda_{d+1} \le 2^{g_f+3}$. The natural target for the fold round beyond Johnson is then $|E|\,\Gamma^{\mathrm{un}}(a) \le C\,\Lambda_{d+1}(a)$ plus lower-order terms, the shape of [CWYZ26, Thm. 4.10]. **[conjectured]**

**Necessary (real attacks). [proved, section 3.3]** If for some $T$ both $\Lambda^{\mathrm{use}}(T) > 2^{g_f + 3}$ and $(n/T)^{t} < 2^{108}$, the level is broken at cost $2^{g_f+128}/\Lambda^{\mathrm{use}}(T) + 2^{17}(n/T)^t < 2^{126}$. The same with $g_b$ and a factor between $1$ and $J-1$ for batching.

**What the certificates of the main document's section 3.3 then mean.**
- A lower certificate needs two theorems at the target agreement, not one: $\Lambda \le 2^{b}$ and $|E|\,\Gamma^{\mathrm{un}} \le 2^{b}$ (or the claim-aware replacement of section 7.6), with $b$ the minimum of the budgets above.
- An upper certificate from lists is "$\Lambda^{\mathrm{use}}(a) > 2^{g_f+3}$", which is $2^{10}$ only at today's fold grind. It is a floor for every analysis at that grinding, and moves with $g_f$.
- An upper certificate from $\Gamma$ ("a violating instance with more than $2^{138}$ escapes") is **not** a floor for every analysis. It is a floor for analyses built on this $\Gamma$.

The gap between necessary and sufficient is then: a factor 2 at the fold round, the factor $J$ at batching, the whole quadratic OOD term, and $\Gamma^{\mathrm{un}}$.

## 5. What grinding costs

Per proof at $\mu = 30$ (any rate): 26 fold messages, 6 OOD points, 6 query messages, 1 batching message, one permutation per attempt. Verifiers pay nothing for a grind (the nonce rides the challenge's own permutation), the guest included.

| list budget $b$ | $g_f = b - 2$ | fold perms $26 \cdot 2^{g_f}$ | level 0 only $6\cdot 2^{g_f}$ | $g_b$ for power batching ($b + 7$) | total with sections 7.2 and 7.3 (split OOD coefficient, $g_b = b - 2$, two OOD points and no OOD grind) | times today |
| --- | --- | --- | --- | --- | --- | --- |
| 9 | 7 | $3.3\cdot 10^{3}$ | $7.7 \cdot 10^{2}$ | 16 | $7.9 \cdot 10^{5}$ | 0.80 |
| 12 | 10 | $2.7\cdot 10^{4}$ | $6.1 \cdot 10^{3}$ | 19 | $8.1\cdot 10^{5}$ | 0.82 |
| 16 | 14 | $4.3\cdot 10^{5}$ | $9.8\cdot 10^{4}$ | 23 | $1.2\cdot 10^{6}$ | 1.24 |
| 18 | 16 | $1.7\cdot 10^{6}$ | $3.9 \cdot 10^{5}$ | 25 | $2.6\cdot 10^{6}$ | 2.6 |
| 20 | 18 | $6.8\cdot 10^{6}$ | $1.6\cdot 10^{6}$ | 27 | $7.9\cdot 10^{6}$ | 7.9 |
| 22 | 20 | $2.7\cdot 10^{7}$ | $6.3 \cdot 10^{6}$ | 29 | $2.9\cdot 10^{7}$ | 29 |
| 24 | 22 | $1.1\cdot 10^{8}$ | $2.5\cdot 10^{7}$ | 31 | $1.1\cdot 10^{8}$ | 115 |
| 26 | 24 | $4.4\cdot 10^{8}$ | $1.0 \cdot 10^{8}$ | 33 | $4.5\cdot 10^{8}$ | 456 |
| 30 | 28 | $7.0\cdot 10^{9}$ | $1.6 \cdot 10^{9}$ | 37 | $7.3\cdot 10^{9}$ | 7300 |

**[checked]** by the script. For scale only: Python's `hashlib` does $2.4 \cdot 10^{6}$ permutations per second on one core of this machine; a multi-way, multi-core search is perhaps one to two orders faster **[not measured]**. So $b \le 20$ is cheap, $b = 24$ is of the order of a second, and $b \ge 30$ is out. Power batching at level 0 costs $2^{b+7}$ in one message and becomes the dominant grind from $b = 14$ on, which is the reason for section 7.2.

## 6. What-if tables

Model: $t = \lceil 108/\log_2(1/\tau)\rceil$ at relative threshold $\tau$; the deployed counts are 1 or 2 above this at Johnson (list slack, degree slack, the batching row). Opening size: opened leaves (64 $K$ words at level 0 at a full stack, 16 $E$ values after), positions, pruned siblings averaged over random query sets, and the opening's 3.3 KiB of stream scalars. "Perms" is the verifier's Merkle hashing, which is also the guest's dominant cost for the opening. The sizes are a model, not a measured proof. **[checked]** by the script only.

### 6.1 Floors from the known lists, as a function of the budget (level 0, $\mu = 30$)

Families: those of note 01, section 4 (height-2 trees and biased padding at rate 1/2, hyperplanes at rate 1/4, flats and the padded pigeonhole family below), which supersede the coset unions I computed (script section F: $2^{9.0}$ at $5/8$ and $2^{23.8}$ at $9/16$ at rate 1/2). Flat counts are for the level-0 domains at $\mu = 30$.

| rate | deployed $t_0$ | budget $2^{7}$ to $2^{9}$ (today's) | budget $2^{10}$ to $2^{27}$ (affordable) | budget needed to pass | next floor |
| --- | --- | --- | --- | --- | --- |
| 1/2 | 218 | 161 or a little more (biased padding) | 160 ($2^{29.4}$ at $5/8$) | $2^{30}$ | 131 ($2^{102.7}$ at $9/16$) |
| 1/4 | 109 | 108 | 108 (hyperplanes, $2^{27}$ at $1/2$) | $2^{28}$ | 77 ($3/8$: $2^{27.8}$ explicit at $N = 25$, $2^{34.5}$ predicted) |
| 1/8 | 73 | 54 | 54 (flats, $2^{51.4}$ at $1/4$) | $2^{52}$ | |
| 1/16 | 55 | 40 | 40 below $2^{15.6}$ (padded pigeonhole at $0.152$), then 36 (flats, $2^{76.6}$ at $1/8$) | $2^{77}$ | |

Reading: a proof with a list budget in the column's range cannot bring $t_0$ below the entry, and no affordable grinding leaves the fourth column. So with the knobs of section 7 the level-0 targets are 160, 108, 54 and 36. The entries are attack-side facts; whether lists are *bounded* by $2^{b}$ above those agreements is what the swarm has to prove.

### 6.2 The whole ladder

Total queries, verifier Merkle permutations and opening size, relative to deployed in brackets.

| level-0 rate | deployed | Johnson, no slack | $\tau = \rho^{0.6}$ | $\tau = \rho^{0.7}$ | $\tau = \rho^{0.8}$ | known-list frontier (budgets $2^{10}$ to $2^{27}$) | capacity |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | 361 q, 336 KiB | 356, 332 (0.99) | 295, 278 (0.83) | 260, 247 (0.74) | 250, 240 (0.72) | 243, 234 (0.70) | 178, 173 (0.51) |
| 1/4 | 234 q, 223 KiB | 230, 220 (0.99) | 208, 202 (0.91) | 196, 193 (0.87) | 183, 183 (0.82) | 178, 179 (0.80) | 115, 115 (0.52) |
| 1/8 | 185 q, 181 KiB | 182, 179 (0.99) | 147, 146 (0.81) | 131, 132 (0.73) | 121, 124 (0.68) | 115, 119 (0.66) | 89, 92 (0.51) |
| 1/16 | 158 q, 159 KiB | 151, 153 (0.96) | 125, 128 (0.81) | 109, 113 (0.71) | 98, 103 (0.64) | 89, 95 (0.60) | 76, 81 (0.51) |

Each column applies its threshold rule at every level's own rate, capped by the known lists: $5/8$ at rate 1/2 and the flats' $2\rho$ below (so at rate 1/4 level 0 stays at 108 in every column but capacity, and at rate 1/2 it stops at 160 from $\rho^{0.7}$ on). Per-level counts are in the script output, for example rate 1/2 at the frontier: $(160, 36, 18, 12, 9, 8)$ against $(218, 55, 32, 23, 18, 15)$. Two corrections to the frontier column, both small: if the deep levels stop at $4\rho$ where note 01's pigeonhole families exist (rates $2^{-6}$ and below), it reads 0.71, 0.82, 0.70, 0.64; with the state function's present cap of 10 bits per query (Proposition 4 at $g_f = 7$), 0.71, 0.82, 0.69, 0.65.

Lowering level 0 alone, later levels as deployed: rate 1/2, $t_0 = 181$: 300 KiB (0.89), $t_0 = 160$: 279 KiB (0.83); rate 1/8, $t_0 = 54$: 160 KiB (0.89); rate 1/16, $t_0 = 40$: 142 KiB (0.89), $t_0 = 36$: 137 KiB (0.86); rate 1/4, only with a budget above $2^{27}$, $t_0 = 77$: 189 KiB (0.85). So level 0 is a little over half of the available gain at rate 1/2 and a third of it at rates 1/8 and 1/16.

### 6.3 Which theorems are worth proving

- **Nothing is available inside Johnson**: removing all slack is 1 to 4%.
- **Rate 1/2, level 0**: the window is $(5/8, 1/\sqrt2)$. A bound $\Lambda(\tau n) \le 2^{b}$, $b \le 20$, with the matching bound on unexplained escapes, is worth 218 to 181 queries at $\tau = 0.66$ and to 161 at $\tau = 0.628$: up to 17% of the opening.
- **Low rates** ($2^{-4}$ to $2^{-19}$) appear in every ladder as levels 1 to 5, and there the window is wide: Johnson gives $R_i/2$ bits per query, the flats cap $R_i - 1$. Bounds for these rates alone are worth 20% of the opening at level-0 rate 1/4 (where level 0 cannot move) and 13 points of the 30% at rate 1/2. A single statement at $\tau = \rho^{0.7}$ for all rates $2^{-3}$ and below gets about two thirds of it.
- **Rates 1/8 and 1/16, level 0**: windows $(1/4, 0.354)$ and $(0.152, 1/4)$, worth 11% each.
- **Rate 1/4, level 0** is closed for every budget up to $2^{27}$. Above that (a level-0 fold grind of 26 bits, $4\cdot 10^{8}$ permutations) the window would be $(3/8, 1/2)$, worth 15%.
- Crossing $5/8$ at rate 1/2 or the flats at lower rates needs lists of $2^{27}$ to $2^{77}$ to be harmless, which no grinding buys: it needs section 7.5 or 7.7.

## 7. Protocol-level ideas

"Protocol change" means the transcript or a verifier constant changes: both provers, the three verifiers and `formal/` move together. "Re-analysis" changes only the proof and the parameter search.

### 7.1 More fold grinding, per level. Protocol change (constants only).

$b_F = g_f + 2$, unchanged proof. Cost in section 5; nothing for verifiers. The grind can differ per level: only the levels whose threshold is lowered beyond Johnson need it, and level 0 alone has 6 of the 26 messages. Also raises the cap of Proposition 4 to $g_f + 3$ bits per query at deep levels, where the fold budget already holds the thresholds up today, inside Johnson: at level 5 of the rate-1/2 ladder ($n = 2^{20}$, $d = 19$) the Johnson list at the threshold that 14 queries would need is about 1000, over $2^{9}$, so the level takes 15 (hand arithmetic, the search was not rerun).

### 7.2 Give the OOD claim its own batching coefficient. Protocol change (small).

Today the running weight is $\sum_k \lambda^{k-1}W_k$ with the OOD claim as one of the powers. Draw one more challenge $\lambda'$ in the same message and use it for the OOD claim alone, at level 0 and at every later level ($W^{(i+1,0)} = W^{(i,\ell)} + \lambda'\mathrm{eq}(z_{i+1},\cdot) + \lambda\sum_q\lambda^q W_{x_q}$).

**Claim. [proved]** Assume OOD separation (the invariant of the OOD message). Then the batching error is at most $(J + L - 3)/|E|$ instead of $(J-1)L/|E|$. *Proof.* For a list member $U$ let $d_k$ be its defects on the other claims and $d^\circ$ its OOD defect. If $d^\circ \ne 0$, for each $\lambda$ exactly one $\lambda'$ solves $\sum_k \lambda^{k-1}d_k + \lambda' d^\circ = 0$: probability $1/|E|$. By separation at most one message has $d^\circ = 0$, and for it some $d_k \ne 0$: probability at most $(J-2)/|E|$. $\square$

Effect: level-0 batching budget from $2^{g_b - 6}$ to $2^{g_b+3}$ ($2^{16}$ at today's grind), later levels from $2^{11}$ to about $2^{19}$. Cost: one more squeeze per level, no proof bytes. This removes 9 bits of pure slack: the real attack at batching was about $L/|E|$ already (section 3.3, step 4).

### 7.3 A second OOD point. Protocol change (small).

Two independent points per commitment: $\binom{L}{2}(\nu/|E|)^2 \le 2^{-110}$ allows $L \le 2^{68}$, and $2^{61}$ with no OOD grind at all, which gives back $6 \cdot 2^{15}$ permutations. **[proved]**: `lem:ood` with the pair's collision probability squared. Cost: 16 bytes and $\nu_i$ squeezes per commitment (110 more permutations per proof for the verifier and the guest), one more multilinear evaluation of the committed message for the prover, one more glued claim. A cheaper variant with the same shape of bound: each point of the form $(\zeta, \zeta^2, \zeta^4, \dots)$ from one challenge, pair collision $2^{\nu}/|E|$; two such points allow $L \le 2^{43}$, three $2^{92}$.

Sections 7.1 to 7.3 together make the usable budget $b = \min(g_f + 2,\ g_b + 3,\ 19) $: 16 at $g_f = 14$ with everything else as today, for 1.24 times today's grinding work.

### 7.4 More query grinding. Protocol change (constants).

$t = \lceil (125 - g_q)/\text{bits}\rceil$: each extra bit is 1% of the queries and doubles the dominant grind. Not competitive.

### 7.5 Two independent claims per fold round. Protocol change (moderate).

The natural form: keep the level's OOD claim as a second running claim through the fold rounds, with its own four scalars per round, instead of batching it. Members of the list other than the OOD-pinned one then violate the second coordinate for certain, with no batching step in between.

*Assessment.* **[proved]** By Lemma 1(d) applied in each coordinate, the prover can make both residuals of one chosen candidate vanish on a common line $\alpha = \alpha_0$. So a member's escape set is *not* finite in general: one candidate still escapes with probability $1/|E|$. **[checked]** toy 2c: generic tables give 17 escaping challenges for 15 candidates (bound $4L$), a tailored table 268, of which 256 are the chosen candidate's line. **[heuristic]** Counting unknowns (8 scalars, one free $\alpha_0$ per candidate) against 4 linear conditions per candidate, at most two candidates can be aimed at once for generic values, so the round's escape probability is about $2/|E| + 4L/|E|^2$: independent of the list up to the OOD budget ($2^{68}$ with two points).

*What a proof would need.* The bound is false in the worst case over weights: when the candidates' value vectors are degenerate (which arbitrary linear functionals allow), every candidate can have its common line and the error is $L/|E|$ again. A state function quantifying over all states therefore gains nothing, whether it has two states or counts half-satisfied candidates. A proof needs (1) a genericity invariant on (list, weights), established with small error by the randomness that fixes the weights after the commitment and preserved through the folds, and (2) the same for polynomials not explained by a close pair. Both are the machinery of section 7.6.

*Cost.* 64 bytes per fold round (1.7 KiB), a second claim recursion for the verifiers, four more inner products per round for the provers (against a folded $\mathrm{eq}$, cheap), a batching of the two claims before the tail.

*Verdict.* The lead's suspicion is right for real attacks and for an average-case analysis, wrong for the current worst-case one. It is the only idea here, short of 7.7, that could make lists of $2^{26}$ and more harmless.

### 7.6 Restricting the state function to the weights the protocol reaches. Re-analysis.

Restricting `FoldRoundBound` to nonzero weights does not help (Proposition 4 holds for every weight; nonzero weights vanishing on the $P_\gamma$ behave as zero ones). What separates the harmful instances is that the claim is true for a *pseudo-candidate*: a polynomial triple $(\tilde G, \tilde F, \tilde H)$, $\tilde H \ne X\tilde F$, with $\tilde G + \alpha\tilde F + \beta\tilde H$ close to the fold on a set of challenges of density much larger than $|E|^{-2}$. A claim-aware analysis would need two things:

1. *An enlarged candidate set.* Define doom over $\mathrm{lst} \cup \{\text{pseudo-candidates}\}$. This is still a sound extractor statement for the outer protocol as long as the set is determined by the commitment and small enough for the OOD and batching terms. For the coset pole pair the pseudo-candidate is the polynomial part, and the state is simply not doomed when its claim holds.
2. *Genericity on the exceptional lines.* On line-supported families a false claim does not bound the escapes (one line per table always, more when the points $(\gamma, \Lambda_0P_\gamma, \Lambda_1P_\gamma)$ are collinear). The state has to carry "at most $k$ of them are collinear in the admissible sense", charged to the message that fixes the weights (OOD point, queries, $\lambda$) and re-established after every fold challenge.

**[conjectured]** With both, the fold round's error on protocol-reachable states is $(2L + O(1))/|E|$, independent of the number of pole lines.

*Verdict.* For the present protocol this is a large proof effort for about one bit: the lines it removes number about $\Lambda_{d+1}$ (note 01, Lemma A), next to the $2\Lambda_d$ that are real. It is worth doing only as the proof technique for section 7.5, where the list term itself goes away and genericity is unavoidable.

### 7.7 A 256-bit field for the opening's challenges. Protocol change (large).

Draw $\alpha, \beta, \lambda, z$ in a quadratic extension $E'$ of $E$. Every term above becomes a count over $2^{256}$: lists and pole families up to $2^{60}$ (one OOD point) or $2^{126}$ fit with no grinding, in the present worst-case proof. It does not remove the need for new coding theory (a bound of the form $2^{130}/|E'|$ on the fold round beyond Johnson is still a theorem nobody has), it only weakens what has to be proved from "at most $2^{10}$" to "at most $2^{130}$". Cost: later levels' leaves double (36 KiB at the deployed counts, rate 1/2), the provers' level-0 folds and weight buffers double, verifier and guest field work in the opening roughly triples, and `formal/` gets a second extension.

### 7.8 Path accounting. Re-analysis.

Lemma P is a drop-in generalisation of the round-by-round theorem and formalises "this path needs two events". It is what makes sections 3.2 and 3.4 rigorous, and what an average-case analysis (7.5, 7.6) would be stated in. Alone it does not relax a budget: the batching and fold escapes of a list member are single-event paths, and for OOD the worst case over list structure still loses $(2b - 13)/3$ bits at a list of $2^{b}$ (section 3.5).

## 8. Where the lead's notes and the main document are wrong or incomplete

`00-lead-notes.md`:
1. Section 2, first bullet: the word at agreement $A-1$ "is the baseline, and it is why the query term is tight". Tight for the state function, not an attack (3.2).
2. Section 2, second bullet: the batching escape is not "about $L/|E|$" in the proof: it is $(J_0+1)L/|E| = 513\,L/|E|$, and later levels' batching shares the 17-bit query grind with a factor $t+1$. These, with OOD, are today's binding budgets ($2^{7}$), not the fold round.
3. Section 2, fourth bullet: "$L \lesssim 2^{3+g}$": $2^{g_f + 2}$ in the proof ($2L/|E|$), $2^{g_f+3}$ for the attack; "cheap": 26 messages, so $b = 30$ costs $7 \cdot 10^{9}$ permutations per proof and $b = 40$ is impossible. The example "rate 1/4 at $A = 3n/8$ with lists of $2^{30}$" needs $g_f = 28$, $1.6\cdot 10^{9}$ permutations even at level 0 alone. What is borderline is $b = 28$ at level 0 only ($4 \cdot 10^{8}$ permutations), which tolerates the $2^{27}$ hyperplane polynomials; the next known lists are at $3n/8$ (note 01), so the window a theorem could use is $(3/8, 1/2)$.
4. Section 3: "with a nonzero claim weight each line keeps at most 2 escapes" is false (3.4): one whole line by choice of table, all lines when the claim is the polynomial part's, for any weights. "`FoldRoundBound` allows the zero weight" is true but removing it changes nothing.
5. Section 1, table: the rate-1/2 row is superseded by note 01 ($5n/8$, $t \ge 160$, for every budget below $2^{29}$).

`whir_soundness_gap.md`:
1. Section 3.2: the conditions omit the batching factor $J$ at level 0 and state the OOD term with $\kappa$ where the code uses the number of message variables $\nu = \kappa + \ell$. Corrected in section 4.
2. Section 3.3: "$\Gamma(a) > 2^{-118}$ shows $A^\ast > a$ for every analysis of this round structure" holds only for analyses through this $\Gamma$. The list certificate's $2^{10}$ is $2^{g_f+3}$.
3. Section 4.2: the degree slack question is settled (3.3, and note 01 by another route): usable in every lane with a $G$ round. The table's floors are superseded by note 01.
4. Section 4.3: as item 4 above. The stated remedy ("restrict the escape count to the weights the protocol can reach") needs the pseudo-candidate and genericity notions of 7.6, not nonzero weights. And "the pole pair caps any analysis well below what the list attacks of section 4.2 allow" is not so: a pole family is a list at degree $d+1$ (note 01, Lemma A), so it caps the present analysis where lists do, and costs about one bit.

## 9. Not done

- The count "at most two candidates can be aimed at once" (7.5) and the collinearity probabilities (3.4) are degree-of-freedom counts, not proofs.
- Whether a list member's batching polynomial can be given many roots under the outer protocol's constraints on the claimed values (I assumed about one root; the proof must assume $J - 1$).
- Any unexplained family that is not line-supported (note 01, Lemma B, says what it would have to look like).
- I read note 01 (sections 0, 2.1 and 4) after writing mine and aligned the floors with it; I did not read the other notes.
- The parameter search was not rerun with other grinds; the "Johnson, no slack" row bounds what any re-tuning inside Johnson can give.
- The proof sizes are a model of the opening (full stack, random positions), not measured proofs, and the permutation rate in section 5 is a scalar Python figure.
