# 15. Fewer points: the nesting loss

Researcher 15 (round 3). Scope: the factor $\tau^{-(\ell-1)}$ that Lemma D6 of note 11 (Proposition 8.1 of note 10, kept by note 14) charges for using one level's points in all of its $\ell$ fold rounds, which is 595 of the 1064 to 1183 bits the level-0 points pay for. Is it real, can a lemma remove it, and which protocol shape pays least for it. The factor $q^3$ of the third-moment count is researcher 16's and is treated here as a constant $C_1$. Notation is note 11's: $q = |E| = 2^{128}$, a level has $\ell$ fold rounds, $d = 2^\kappa - 1 + \ell$, $\epsilon = (d + 2^\ell)/q$, $a_c = \alpha + \beta X$ for $c = (\alpha, \beta)$, a point is $z = (\theta, \zeta)$, $\mathrm{ev}^{(j)}_z$ as in Definition D1, $\mathcal{T}(O')$ the set of pairs $(c, P)$ with $P$ in the list of the fold of $O'$ by $c$, classes and dependent triples as in Lemma 2.1 of note 10, $K_0 = 2^9 q$, $\tau = 2^{-119}$, point budget $2^{-110}$ (the deployed grinds). Statuses: **[proved]** (proof here, by hand, not machine-checked), **[checked]** (numerically, sizes given), **[conjectured]**, **[estimate]**. No Lean or Rust was edited. Scripts: `scripts/15_nesting.c` (brute force, built on the red team's `10_deep_redteam.c`), `scripts/15_schedules.py` (the accounting), `scripts/15_batch_toy.py` (completeness), `scripts/15_run.sh`.

## 0. Summary

1. **The nesting loss is real for the exceptional sets the proofs use, and no lemma of the hoped kind exists.** There are words (Construction N1, section 2.2) for which, with probability about $s\,(r/q)^{s-1}$ over the points, a set of first challenges of density $L/q$ makes the points exceptional for the second round, where $r$ is a degree up to about $d$ and $L$ a number of lines up to the number of pairs of list members. The single-round probability of the same event is about $(r/q)^s(1 + sL/r)$, so the reuse costs a factor $sq/(r + sL)$, a whole point, and the Markov step of Lemma D6 is tight up to the factor $sL/(r + sL) \le 1$. **[proved]**; **[checked]** by brute force over all first challenges at $q = 32$ and $64$ and by exhaustive algebra over all point tuples (measured ratios 0.55 to 0.85 against Markov). It iterates: an 8-lane word has a tree of prefixes of density $(1/q)(1/q)$ with only $s - 2$ special points (**[proved]**, **[checked]** at $q = 32$). Consequently any event defined from the committed lanes alone that covers "exceptional for round 2 after a fraction $1/q$ of the first challenges" has probability at least $s(r/q)^{s-1}$, and one that covers "after some first challenge" at least about $(r/q)^{s-2}$ (Proposition U).
2. **It is not known to be real for soundness, and the constructions say it is not.** At a spoiled prefix the damage is that the colliding list members each win their own $2q$ challenges: measured $4q$ for two members and $6q$ for three, exactly, against $2q$ elsewhere. The deployed $K_0 = 2^9 q$ tolerates $2^8$ members colliding at once, and the round-by-round budget is exceeded only if that happens along at least $2^9$ distinct lines of first challenges. Every family I can build has one line per clique. As an attack the tree is worthless: each level of it costs $2^{7}q/L$ hash evaluations. **[proved]** for the constructions, **[conjectured]** in general (Conjecture C, section 4). A proof would need structure for unexplained close codewords, the same missing ingredient as for $q^3$.
3. **What is true** (Lemma L, section 2.1, **[proved]**): for two tuples, a point and a round, the set of challenges after which the point stops separating their folds is everything, nothing, or one line of slope $\zeta$. So explained list members lose at most one separating point per round outside a set of challenges of density $q^{-2}$ per pair, and that one point is lost on a line. This is the exact relation between the exceptional sets of a word and of its folds for explained members; it does not extend to unexplained ones.
4. **The loss can be paid with cheap points: the ladder** (section 6, Lemma S, **[proved]**). Send only the points round 1 needs after the commitment, and top up before each later round with fresh points that ride in the same verifier message as the previous fold challenge, answered on the folded tuple, which is half the size each round. Every round uses all points sampled so far. No new verifier message, no new grind, no new error term: the fold challenge message keeps $K_0/q^2 + \tau$, and the first batch's message has error $\binom{L}{2}\epsilon^{s_1} + \sum_j C_1\,\epsilon^{\sigma_j}\,\tau^{-(j-1)}$ with $\sigma_j$ the number of points available at round $j$. The nesting bits are still paid, $119$ a round, but by points that cost $1/16, 1/32, \dots$ of a level-0 pass. Completeness **[checked]** (`15_batch_toy.py`); a fresh point after the first challenge removes the collision of N1 except with probability $(r+1)/q$ (**[checked]**, all spoiled first challenges at $q = 32$ and $64$).
5. **Numbers at level 0** ($\kappa = 24$, $\ell = 6$, any rate; prover work in multiplications of the level-0 NTT at rate 1/2; `15_schedules.py`, **[checked]** arithmetic; the prover counts are counts, not timings):

| design | list $2^{40}$: points, scalars, bytes, prover | list $2^{100}$ | list $2^{300}$ |
| --- | --- | --- | --- |
| D, one batch (note 11) | 12, 84, 1344 B, 1.000 | 14, 98, 1568 B, 1.167 | 19, 133, 2128 B, 1.583 |
| **ladder** | **6+1+1+2+1+1 = 12, 66, 1056 B, 0.637** | 8+1+1+1+1+2 = 14, 78, 1248 B, 0.792 | 14+1+1+1+1+1 = 19, 118, 1888 B, 1.288 |
| two batches (8 at commit, 5 before round 4, own message) | 13, 76, 1216 B, 0.745 | 15, 90, 1440 B, 0.911 | 21, 132, 2112 B, 1.411 |
| fresh batch every round | 36, 162, 2632 B, 1.227 | 48, 216, 3496 B, 1.635 | 84, 378, 6088 B, 2.862 |
| full columns | 12, 768, 12288 B, 1.000 | 14, 896, 14336 B, 1.167 | 19, 1216, 19456 B, 1.583 |

   The ladder has the same number of points as D, 21 percent fewer scalars, 36 percent less prover point work at list $2^{40}$ (6 full passes over the committed message instead of 12, plus 6 points worth 1.6 passes), and 6 percent fewer verifier products. At later levels it saves 6 scalars a level and nothing else matters there. Over the whole opening at $\mu = 30$ with lists $2^{40}$ at every level: 299 scalars to 251 (768 bytes), point work 1.019 to 0.651 of the level-0 NTT. With note 11's guess that 12 points are 3 to 10 percent of proving time, the ladder saves 1 to 3.6 percent of proving time (**[estimate]**, unmeasured).
6. **If researcher 16 removes $q^3$** (single-round constant $\binom{L}{2}$ instead of $4L^3q^6/K_0^3$), the nesting is all that is left and the ladder matters more: level 0 at list $2^{40}$ goes from 8 points in one batch (0.667) to 2+1+2+1+1+1 (2 full passes, 39 scalars, 0.319). The red team's "2 to 3 points" would need the nesting gone as well, which this note does not deliver.
7. **Variants that do not help** (section 5): full columns (same soundness, 64 scalars a point; N1 does not involve any prover message, so "no per-round freedom" changes nothing, **[proved]**, **[checked]**); one shared lane point (the list factor returns in the pinning as soon as $L \ge 2^{7}$, **[proved]**); claims discharged at the end of the level (equal to full columns, or unsound, **[proved]**); independent fresh batches every round (sound, dominated by the ladder).
8. **Side findings.** (i) The red team's conjectured floor $(n/q)^s + \binom{\Lambda}{2}\epsilon^s$ for the exceptional set of Theorem 3 misses a term: $m \ge K_0/q$ list members that share their answers at $s - 1$ points give $m$ lines to one answer vector, with probability up to $(r/q)^{s-1}$, for every first challenge (**[checked]**, four members at $K_0 = 2.72q$). It does not turn into winning challenges (one round message serves one line). (ii) `count_exceptional` of `10_deep_redteam.c` compares the largest class with the number of challenges and so cannot see two full classes sharing all answers; with the stronger test of this note the red team's nested words still show 0 spoiled first challenges at generic points (**[checked]**, all 1024 at $q = 32$, five words). Their conclusion "0 of 1024" was right for those words and points, and N1 shows it does not generalise.

## 1. Where the factor comes from, and three meanings of "exceptional"

Lemma D4 of note 11 holds for points outside $\mathrm{Exc}_j(O')$, a set that depends on the word $O'$ folded in round $j$, with $\Pr_{\mathbf z}[\mathbf{z} \in \mathrm{Exc}_j(O')] \le e := C_1\epsilon^s$, $C_1 = 4L^3q^6/K_0^3$, for points independent of $O'$. In round $j \ge 2$ the word is $O^{(j-1)}$, a function of the earlier challenges, which the prover influences after seeing the points. Lemma D6 handles this with a potential and Markov's inequality: $\pi_j := \Pr_{c_1..c_{j-1}}[\mathbf z \in \mathrm{Exc}_j(O^{(j-1)})]$ has mean at most $e$ over $\mathbf z$, and the points are declared bad when $\sum_j \tau^{-(j-1)}\pi_j \ge 1$, probability at most $e\sum_{j<\ell}\tau^{-j}$. Each fold challenge may then raise the potential above 1 with probability $\tau$. With $\tau = 2^{-119}$ and $\ell = 6$ that is $5 \cdot 119 = 595$ bits.

Three events are called exceptional in notes 07, 10, 11, and the answer to "is the loss real" depends on which:

- $\mathrm{E_N}$: the proof's event, $N(\mathbf z) \ge K_0^3/4$, where $N$ counts the non-dependent triples of $\mathcal{T}(O')$ whose $Q$ vanishes at all points.
- $\mathrm{E_3}$: the conclusion of Theorem 3 of note 07 fails: some answer vector has a set $W$ of consistent elements with distinct challenges, $|W| \ge K_0$, with no class holding 74 percent of $W$. $\mathrm{E_3} \subseteq \mathrm{E_N}$.
- $\mathrm{E_4}$: the conclusion of Lemma D4(2) fails: some answers and round message win at least $K_0$ challenges although every list member consistent with the carried claims violates the running claim. $\mathrm{E_4} \subseteq \mathrm{E_N}$. This is the one soundness needs.

Two list pairs of $O'$ that share all their answers put $\mathbf z$ in $\mathrm{E_N}$ and $\mathrm{E_3}$ at once (their two full classes give about $q^6$ non-dependent triples), but in $\mathrm{E_4}$ only if $2q$ times the number of such pairs reaches $K_0$. Sections 2 and 3 are about $\mathrm{E_N}$ and $\mathrm{E_3}$, with $\mathrm{E_4}$ measured alongside.

## 2. The loss is real for $\mathrm{E_N}$ and $\mathrm{E_3}$

### 2.1 What a fold does to a separating point

**Lemma L (lines). [proved]** Let $U \ne U'$ be tuples with lane variables $u_j, \dots, u_\ell$, $\Delta := U + U'$ with halves $\Delta_0$ (the half multiplied by $a_c$) and $\Delta_1$, and $z = (\theta, \zeta)$ a point. Put $e_h := \mathrm{ev}^{(j)}_z(\Delta_h)$. The set of challenges $c$ with $\mathrm{ev}^{(j)}_z(\Delta_1 + a_c\Delta_0) = 0$ is $E^2$ if $e_0 = e_1 = 0$, empty if $e_0 = 0 \ne e_1$, and the line $\{\alpha + \beta\zeta = e_1/e_0\}$ otherwise. The same holds for "both halves of the fold vanish under $\mathrm{ev}^{(j+1)}_z$" (the form round $j + 1$ uses): it is the intersection of two such sets with the same slope, hence $E^2$, empty or one line. Two points with distinct $\zeta$ that are both in the third case are killed together by at most one challenge.

*Proof.* (E1) and (E3) of Lemma D1: $\mathrm{ev}^{(j)}_z(\Delta_1 + a_c\Delta_0) = e_1 + (\alpha + \beta\zeta)e_0$. Two lines of slopes $\zeta \ne \zeta'$ meet in one point. $\square$

So for members of the list of the committed word, the points that separate two of them can only disappear one per round along a line (density $1/q$), or two at once at a single challenge (density $q^{-2}$). This is the structure Lemma D6 has no access to, and it is also what makes the loss real.

### 2.2 Construction N1 and Proposition N

Two consecutive rounds of a level; lanes $(u_1, u_2) \in \{0,1\}^2$ in the order $00, 01, 10, 11$, round 1 folds $u_1$, round 2 folds $u_2$ (more lanes may be present and play no role). Let $R_0 = \prod_{k \le r}(X - \rho_k)$ with distinct $\rho_k \in E \setminus D$, $1 \le r \le d - 1$. Let $U_1$ have lanes of degrees at most $d - 2, d - 1, d - 1, d$, and for $i = 2, \dots, M$
$$U_i := U_1 + R_0 \cdot (0,\ D_i,\ 0,\ D'_i), \qquad \deg D_i \le d - 1 - r,\quad \deg D'_i \le d - r,$$
with $(D_1, D'_1) = 0$. Let $O$ be any word whose lanes $00, 10$ are those of $U_1$ and whose lanes $(01, 11)$ equal those of $U_i$ on a set $S_i$ of at least $A$ columns, for every $i$. (Such a word exists exactly when the 2-lane word $((O_{01} + U_{1,01})/R_0, (O_{11} + U_{1,11})/R_0)$ has the $M$ pairs $(D_i, D'_i)$ in its list at agreement $A$ and degrees $(d - 1 - r, d - r)$: a list at a rate lower by the fraction $r/d$. With disjoint $S_i$ it exists whenever $MA \le n$.) For a pair $i \ne i'$ write $\Delta D := D_i + D_{i'}$, $\Delta D' := D'_i + D'_{i'}$.

**Proposition N. [proved]** For every first challenge $c_1$:
1. The round-2 word $O_{c_1}$ has the pairs $V_i(c_1) := (F^\ast, G_i)$, $F^\ast = U_{1,10} + a_{c_1}U_{1,00}$, $G_i = U_{1,11} + a_{c_1}U_{1,01} + R_0(D'_i + a_{c_1}D_i)$, of degrees at most $(d-1, d)$, agreeing with it on $S_i$. Each is in the pair list at agreement $A$, and its class in $\mathcal{T}(O_{c_1})$ contains all $q^2$ second challenges.
2. $V_i(c_1) = V_{i'}(c_1)$ if and only if $\Delta D' + a_{c_1}\Delta D = 0$, which holds for at most one $c_1$.
3. Otherwise $V_i(c_1)$ and $V_{i'}(c_1)$ have the same round-2 answers at a point with second coordinate $\zeta$ if and only if $R_0(\zeta) = 0$ or $(\Delta D' + a_{c_1}\Delta D)(\zeta) = 0$. For $\zeta$ not a root of $R_0\,\Delta D$ the second condition is the line $\ell_{ii'}(\zeta) := \{\alpha + \beta\zeta = \Delta D'(\zeta)/\Delta D(\zeta)\}$.
4. Let $\mathbf z$ have $\zeta_2, \dots, \zeta_s$ among the roots of $R_0$ and $\zeta_1$ not a root of $R_0\,\Delta D$. For every $c_1 \in \ell_{ii'}(\zeta_1)$ but at most one: (a) $N(\mathbf z) \ge q^2(q^2-1)(q^2-2)$ for the word $O_{c_1}$, so $\mathbf z \in \mathrm{Exc}_2(O_{c_1})$ for every $K_0 \le q^2$; (b) $\mathrm{E_3}$ holds for $O_{c_1}$.
5. Consequently, with $L(\zeta_1)$ the number of distinct values $\Delta D'(\zeta_1)/\Delta D(\zeta_1)$ over the pairs,
$$\Pr_{\mathbf z}\Bigl[\ \Pr_{c_1}\bigl[\mathbf z \in \mathrm{Exc}_2(O_{c_1})\bigr] \ \ge\ L(\zeta_1)\,\frac{q-1}{q^2}\ \Bigr] \ \ge\ s\,\Bigl(\frac{r}{q}\Bigr)^{s-1}\Bigl(1 - \frac{r + d}{q}\Bigr).$$

*Proof.* 1: fold the lanes; degrees add one on the lanes multiplied by $a_{c_1}$. For every $c_2$ the fold $G_i + a_{c_2}F^\ast$ has degree at most $d$ and agrees with the fold of $O_{c_1}$ on $S_i$. 2 and 3: the first halves are equal and the second halves differ by $R_0(\Delta D' + a_{c_1}\Delta D)$. 4(a): for pairwise distinct $c_2, c_2', c_2''$ the elements $(c_2, V_{i,c_2})$, $(c_2', V_{i,c_2'})$, $(c_2'', V_{i',c_2''})$ are consistent with the answers $y^F_m = F^\ast(\zeta_m)$, $y^G_m = G_i(\zeta_m)$, so their $Q$ vanishes at every point (Lemma D2(a)); the first two span the class of $V_i$ (Lemma 2.1(a) of note 10), and the third is not in it because $G_{i'} \ne G_i$; so the triple is not dependent. 4(b): take $W$ with one element per second challenge, alternately from the two classes. 5: the lines $\ell_{ii'}(\zeta_1)$ have the same slope, so distinct ones are disjoint, and each loses at most one point by 2; the points with exactly $s - 1$ coordinates at roots have probability $s(r/q)^{s-1}(1 - r/q)$, and $\zeta_1$ avoids the at most $d$ roots of a fixed $\Delta D$. $\square$

**Reading against Lemma D6.** For a fixed $c_1$ the same mechanism (two of these pairs share all answers) has probability about $(r/q)^s(1 + sL/r)$ over the points (all points at roots, or all but one and the last at the root of some $\Delta D' + a_{c_1}\Delta D$). So reusing the points costs the factor
$$\frac{s\,(r/q)^{s-1}}{(r/q)^s(1 + sL/r)} = \frac{s\,q}{r + sL} = \frac{1}{\tau_L}\cdot\frac{sL}{r + sL}, \qquad \tau_L := \frac{L}{q},$$
and Markov's bound $\mathbb{E}[\pi]/\tau_L$ on $\Pr[\pi \ge \tau_L]$ is attained up to $sL/(r + sL)$. With $r$ of order $d$ and few lines the loss is $sq/r$, between $2^{104}$ and $2^{130}$ at level 0; Lemma D6 charges $2^{119}$. In the potential of Lemma D6 with the deployed $\tau$: $T_0 \ge \tau^{-1}\pi_2 \ge 1$ as soon as $L \ge 2^9$, that is 33 members with pairwise distinct lines, and then $\Pr[T_0 \ge 1] \ge s(r/q)^{s-1}(1 - o(1))$: the level of two rounds has lost one point. **[proved]** given the word; the existence of a level-0 word with 33 such members and $r$ a constant fraction of $d$ is **[conjectured]** only to the extent that lists of that size exist at the correspondingly lower rate, which $\mathrm{ListBound}$ with a budget of $2^{40}$ does not exclude.

### 2.3 Depth: one point per reused round

**Construction N$_k$. [proved]** $k + 1$ consecutive rounds, lanes $(u_1, \dots, u_{k+1})$. Members $U_i = U_1 + R_0\cdot v^{(1)} \otimes \dots \otimes v^{(k-1)} \otimes (D_i, D'_i)$ on the lanes with $u_{k+1} = 1$ (zero on the others), $v^{(m)} = (\lambda_m, 1)$ with $\lambda_m \in E^\ast$, degrees lowered by $k$. After $k$ folds the difference of two members is $R_0\prod_{m<k}(1 + \lambda_m a_{c_m})\,(\Delta D' + a_{c_k}\Delta D)$ in one lane of the second half. So at a point with $\zeta$ not a root of $R_0$ the two folds share their round-$(k+1)$ answers if and only if $a_{c_m}(\zeta) = 1/\lambda_m$ for some $m < k$ or $c_k \in \ell_{ii'}(\zeta)$. With $s - k$ points at roots of $R_0$ and $k$ free points $\zeta_1, \dots, \zeta_k$, the prefixes with $c_m$ on the line $a_{c_m}(\zeta_m) = 1/\lambda_m$ for $m < k$ and $c_k \in \ell_{ii'}(\zeta_k)$ put the points in $\mathrm{Exc}_{k+1}$: a tree with one line per level, the first $k - 1$ shared by all pairs, the last one per pair. Hence $\pi_{k+1} \ge L\,(q-1)^k/q^{2k}$ and $T_0 \ge L/(q\tau)^k$ for these points, which have probability at least $(r/q)^{s-k}$: the potential of Lemma D6 fails with that probability as soon as $L \ge 2^{9k}$ ($2^{45}$ pairs, $2^{23}$ members, for $k = 5$).

So for the potential as defined the nesting costs $k$ points for $k$ reused rounds, at $\log_2(q/r) \ge 104$ bits each where Lemma D6 charges 119. **[proved]** as a statement about such words, **[checked]** for $k = 2$, $M = 2$, $r = 1$ (section 3). Whether level-0 words with $2^{23}$ such members exist is open.

### 2.4 What the spoiled prefixes do to soundness

**[checked]**, exact maximum over all answer vectors and all round messages, with a running claim that every planted member violates (section 3): on a spoiled prefix the best prover wins $4q$ second challenges when two members collide and $6q$ when three do; on every other prefix tested $2q$. This is what the proof of Corollary 4 predicts: each consistent pair that violates the claim wins at most its conic, $2q$. So $\mathrm{E_4}$ at the deployed $K_0 = 2^9 q$ needs $2^8$ members sharing all answers after the fold.

**As an attack. [proved]** for these strategies, in the cost model of note 03. Wait for points with $s - k$ special coordinates: $2^{15}(q/r)^{s-k}$. Grind each of $k$ fold challenges onto its line: $2^{7}q/L$ each, at least $2^{126}$ for $L \le 2^9$. Then round $k + 1$ is won with probability $2m/q$ for a clique of $m$ members. Every path costs at least $2^{7}q/L$, so nothing below $2^{125}$ unless $L > 2^{10}$, and then the lines are one per pair and $m = 2$. The flats family is the instructive case (experiment A4): with $s - 1$ points in $D$ every flat through them collides after a first challenge on the single line $a_{c_1}(\zeta_1) = 1/\mu$, at real size a clique of about $2^{26 - (s-1)}$ members, so the list factor is back in round 2. But it is one line: probability $1/q$, which the fold message's $\tau$ already pays, and the potential flags it at $c_1$ and not at the points. This is the case the potential exists for.

### 2.5 No event before the challenges

**Proposition U. [proved]** Let $S(O)$ be any set of point tuples determined by the committed lanes such that $\mathbf z \notin S(O)$ implies $\Pr_{c_1}[\mathbf z \in \mathrm{Exc}_2(O_{c_1})] < (q-1)/q^2$. For an N1 word $\Pr[S(O)] \ge s(r/q)^{s-1}(1 - (r+d)/q)$. If $S(O)$ must exclude $\mathbf z \in \mathrm{Exc}_2(O_{c_1})$ for every $c_1$, take N1 with $\deg(\Delta D' + a_c\Delta D) = 2$ (constant $\Delta D$, $\deg \Delta D' = 2$, $r \le d - 2$): for any two distinct $\zeta_1, \zeta_2$ off the roots there is exactly one $c_1$ at which both are roots, so $\Pr[S(O)] \ge \binom{s}{2}(r/q)^{s-2}(1 - o(1))$.

*Proof.* Proposition N(4); for the second claim, $\Delta D'(\zeta_m) + (\alpha + \beta\zeta_m)\Delta D = 0$ for $m = 1, 2$ is a linear system in $(\alpha, \beta)$ with determinant $\Delta D^2(\zeta_1 + \zeta_2) \ne 0$. $\square$

So the answer to the question "can exceptional for some round of the level be one event about the $2^\ell$ lanes, with a union over a bounded family" is no at the price $\epsilon^s$: such an event loses one point per reused round if a $1/q$ fraction of bad prefixes is tolerated and two if none is. The family of bad prefixes is a union of lines, one per pair of list members and free point, and it is bounded only if the list is.

## 3. Measurements

`15_nesting.c` rebuilds, for every first challenge $c_1$ (or prefix), the complete lists of all $q^2$ folds of the next round with the red team's enumerator and tests $\mathrm{E_3}$ exactly: for every answer vector with at least $K_0$ consistent challenges it finds the largest class $L_1$ and the number `alt` of challenges that have a consistent element outside $L_1$; a set $W$ with no class at 74 percent exists if and only if `alt` $\ge 0.26 K_0$ (take $0.27K_0$ such elements and fill up with $L_1$; any other class meets $L_1$ in at most one element). "Wins" is the exact maximum over all answer vectors and all round messages of the number of winning second challenges ($\mathrm{E_4}$'s quantity), with weights on the low part and a claim that the planted members violate. $K_0 = \lceil 2.72q\rceil$ unless stated. All **[checked]**; seeds are fixed in `15_run.sh`.

| experiment | field, $n$, $d$, $A$ | points | first challenges scanned | spoiled ($\mathrm{E_3}$) | predicted by Proposition N | wins: spoiled / others |
| --- | --- | --- | --- | --- | --- | --- |
| N1, 2 members, $r = 2$ | $2^5$, 16, 3, 6 | 3 generic (two tuples) | all 1024 | 0, 0 | 0 | . / 64 = $2q$ |
| | | 1 root, 2 generic (two tuples) | all 1024 | 0, 0 | 0 | . / 64 |
| | | 2 roots, 1 generic (two seeds) | all 1024 | 31, 31 | 31 = $q - 1$, the same challenges | 128 = $4q$ / 64 |
| | $2^6$, 16, 3, 6 | 2 roots, 1 generic | all 4096 | 63 | 63, the same | 256 = $4q$ / 128 = $2q$ |
| N1, 4 members (6 pairs) | $2^6$, 32, 3, 8, $K_0 = 4.72q$ | 2 roots, 1 generic | 12 from the 378 predicted (6 distinct lines), 8 uniform | 12, 0 | 12, 0 | 256 = $4q$ / 130 (cell cap) |
| flats: lanes $\mu x^7$ and $G + x^7$ | $2^6$, 16, 4, 7, $K_0 = 8.72q$ | 2 in $D$, 1 generic | 7 on the line $a_{c_1}(\zeta_1) = 1/\mu$, 5 off it | 7 (three full classes), 0 | 7, 0 | 384 = $6q$ / 128 (cell cap) |
| N$_2$, 8 lanes, 2 members, $r = 1$ | $2^5$, 16, 3, 6 | 1 root, 2 generic (two seeds) | prefixes $(c_1, c_2)$: 40 from the 1922 predicted of $2^{20}$; 40 with only $c_1$ on its line; 40 uniform | 40, 0, 0 | 40, 0, 0 | not computed |
| | | | $c_1$ on its line, all 1024 $c_2$; $c_1$ off, all 1024 $c_2$ | 31; 0 | 31; 0 | |
| red team's nested words: random, planted1, planted2, pole, poleflat | $2^5$, 16, 3, 6 | 3 generic | all 1024 each | 0 each | | 64 where computed |

Exhaustive algebra (the collision predicate of Proposition N(3) over all point tuples and all $c_1$; the predicate itself is validated by the scans above):

| instance | $\mathbb{E}_{\mathbf z}$ of the bad fraction of $c_1$ | $\Pr_{\mathbf z}$[at least $L$ lines bad] | $s(r/q)^{s-1}$ | Markov bound $\mathbb{E}/\tau_L$ | truth over bound | $sL/(r + sL)$ |
| --- | --- | --- | --- | --- | --- | --- |
| $q = 32$, $M = 2$, $r = 2$, $s = 2$ | $8.34 \cdot 10^{-3}$ | 0.150 | 0.125 | 0.275 | 0.55 | 0.50 |
| $q = 32$, $M = 2$, $r = 2$, $s = 3$ | $7.71 \cdot 10^{-4}$ | 0.0176 | 0.0117 | 0.0255 | 0.69 | 0.60 |
| $q = 64$, $M = 2$, $r = 2$, $s = 3$ | $9.96 \cdot 10^{-5}$ | $4.52 \cdot 10^{-3}$ | $2.93 \cdot 10^{-3}$ | $6.48 \cdot 10^{-3}$ | 0.70 | 0.60 |
| $q = 64$, $M = 4$, $r = 2$, $s = 3$, $L = 6$ | $4.33 \cdot 10^{-4}$ | $4.02 \cdot 10^{-3}$ | $2.93 \cdot 10^{-3}$ | $4.76 \cdot 10^{-3}$ | 0.85 | 0.90 |

(The measured probabilities exceed $s(r/q)^{s-1}$ because tuples with coinciding free points also count, a toy-size effect of order $1/q$.) A fresh point: of the 31 spoiled first challenges at $q = 32$, 3 (seed 1) and 5 (seed 2) stay spoiled when one more point is drawn uniformly after $c_1$, the number the predicate predicts in each case, against an expected $31 \cdot 3/32 \approx 2.9$; at $q = 64$, 4 of the 63 (predicted 4, expected $63 \cdot 3/64 \approx 3$).

Two remarks on the toy sizes. With uniform points over $\mathrm{GF}(2^5)$ half of the field is $D$, and tuples with all points in $D$ spoil every first challenge (the red team's "all points in $D$" event, independent of $c_1$); mixed tuples spoil 0 to 2 isolated first challenges, the density $q^{-2}$ phenomenon. And a random fold has a few pairs of the pair list by chance, one of which satisfies a random claim with probability $1/q$; the program redraws the claim when that happens and says so.

## 4. What is plausible but not proved

For explained members Lemma L gives the full picture: trees of lines, one point lost per level. Three things stand between that and a theorem with fewer points for Protocol D as it is.

1. **Unexplained elements.** $\mathrm{Exc}_j$ is defined by a count over all of $\mathcal{T}(O^{(j-1)})$, most of which may be close codewords not explained by any list member of the committed word. Nothing relates the unexplained elements of different prefixes, so Markov is all there is. This is the same missing structure as for $q^3$; a result of researcher 16 that bounds $\mathrm{E_N}$ better for one word still has to be nested.
2. **Benign collisions count as exceptional.** $\mathrm{E_N}$ and $\mathrm{E_3}$ fire when two list pairs share their answers, which costs soundness a factor 2. A lemma that tolerates up to $2^7$ consistent pairs ($2q$ wins each) would have to nest only the event "more than $2^7$ members share all answers after the fold". By Lemma L that event lives on lines $a_c(\zeta) = \rho$ on which the points $(\mathrm{ev}(F_i), \mathrm{ev}(G_i)) \in E^2$ of the members are collinear with slope $\rho$, at least $2^7$ of them. To exceed $\tau$ it needs $2^9$ such lines for one point tuple.
3. **Even for explained members the worst case is not excluded.** A list of $2^{40}$ members can in principle be arranged with $2^9$ rich lines (a grid). I know no reason for real lists to be so arranged, and the product-like families I tried to build violate the agreement count, but that is not a proof.

**Conjecture C. [conjectured]** For every level-0 or later word of Protocol D and uniform points, outside an event of probability $O(\ell)\bigl((n/q)^{s-1} + \binom{\Lambda}{2}\epsilon^{s-1}\bigr)$ the following holds at every round: the prefixes after which some answers and round message win $K_0 = 2^9q$ challenges form, conditionally on each earlier prefix, a set of density at most $2^9/q$. If true, 3 or 4 points per level would do with the single batch, and the potential would only have to count lines. Evidence: every construction above has one line per clique, and at toy sizes no prefix with more than $2q$ times the number of colliding members was found. No approach to a proof.

Side finding (i) of the summary belongs here. In experiment A3 with $K_0 = 2.72q$, four members and two points at roots, every first challenge is spoiled in the sense of $\mathrm{E_3}$: the answer vector that is off by one point for all four members is consistent with one line of each (note 10, strategy S2, four times). That is $m$ lines for $m$ members sharing $s - 1$ answers, an event of probability up to $(r/q)^{s-1}$ that does not depend on the challenge, so it is not nesting, and it is missing from the conjectured floor of note 10, section 2.3. With a running claim one round message makes one of the lines win (three of its four free values); the measured maximum stays at $2q + 2$.

## 5. Protocol variants

### 5.1 (a) Full columns

The prover sends, per point, all $2^\ell$ lane values at commit time; the verifier folds the column itself and no $\varphi$ is sent. **Soundness: that of D, no better. [proved]** Lemma D4 holds lane by lane with $\epsilon = (d+1)/q$, and its exceptional set is still that of the folded word. Construction N1 uses no prover message: with the honest column of $U_1$, the folds of $U_1$ and $U_i$ have the same verifier-computed claims at the special points on the lines of Proposition N. The scans of section 3 are this situation (single lanes per half, answers quantified over all vectors). So the fold lemma does not hold for all rounds from one exceptional event, and the point count is D's. **Cost:** $2^\ell s$ scalars instead of $(\ell + 1)s$: 768 against 84 at level 0, 144 against 45 later; the prover's pass is the same (it computes the lane values in either design); the verifier folds $2^\ell$ values per point and round. Dominated.

### 5.2 (b) Fresh points every round

Sound: each round's lemma is applied to points sampled after the word is fixed, no nesting. Two forms. Independent batches, each sufficient alone ($C_1\epsilon^{s'} \le$ budget, 6 points a round at list $2^{40}$): $6\ell$ points, each batch a verifier message, 162 scalars and 1.23 of the level-0 NTT at level 0, worse than D on every count because the round-1 batch is as large as before and every later batch pays the full single-round count again. The right form is the ladder of section 6: fresh points top up the old ones, and the old ones keep their value minus the nesting discount.

The cheapest way to answer a fresh point of round $b$: the prover holds the folded message ($2^{\mu - b + 1}$ elements of $E$) for the sumcheck of that round; the $2^{\ell - b + 1}$ lane values at $\zeta$ are inner products with the tensor $\bigotimes_k (1, \widehat W_k(\zeta))$, one product $E \times E$ per element, fused into that round's pass; later answers for the point are these lane values folded by the challenges (E3). Evaluating on the original $K$-valued lanes instead would cost $2^\mu$ products $K \times E$, more for every $b \ge 2$.

### 5.3 (c) One lane point shared by the univariate points

With one $\theta$ (or one multilinear $r \in E^\ell$) for all $s$ points, two list members $U, U'$ with $\sum_u \theta_0^{e(u)}(U_u + U'_u) = 0$ as polynomials, for example $U' = U + (D, \theta_0 D)$ on two lanes, are separated by no $\zeta$ when $\theta = \theta_0$. Each pair has up to $2^\ell - 1$ such values, so the pinning error is up to $\binom{L}{2}(2^\ell - 1)/q$, above $2^{-110}$ for $L \ge 2^{7}$, and the first-moment count of Lemma D4 gains a term $\Lambda^3q^6(2^\ell/q)$, which is fatal. **[proved]** as a lower bound on the pinning error for such lists. It saves only sampled scalars. Rejected.

### 5.4 (d) Claims discharged once at the end of the level

If the lane values are sent at commit time this is (a). If the prover answers after the level's challenges, nothing binds the answers before the challenges: the only check, $P^{(\ell)}(\zeta_m) = \mathrm{fold}_c(Y_m)$, is one linear equation on a free column, so every fold round is today's round shape and the list attack of note 10, section 7 (about $1.5L$ lines) applies. **[proved]** unsound. Sending columns only for the first $r$ rounds costs $2^r - 1$ scalars against $r$ and changes nothing.

### 5.5 (e) Others

- **Points in an extension field.** One point in $\mathrm{GF}(q^t)$ costs the prover $t$ passes and gives $128t - 24$ bits instead of $104t$ at level 0, because $\log_2 d$ is lost once. Ten point-equivalents instead of twelve (one point in $\mathrm{GF}(q^{10})$ or two in $\mathrm{GF}(q^5)$). Lemma D4 goes through with answers in the extension (**[sketch]**: Schwartz-Zippel over the extension; an injective $c \mapsto a_c(\zeta)$ for $\zeta \notin E$ only helps). The verifier and the guest would do arithmetic in a field of 640 or 1280 bits. Not recommended; combinable with the ladder.
- **Separate batches with their own message** (for example 8 at commit and 5 before round 4): sound, covered by the general form of Lemma S (section 6.3), but each such message has its own budget, which costs 110 bits per batch used. Strictly worse than the ladder.
- **More fold grinding.** Each bit of fold grind is worth $\ell + 2$ bits of points; one point is 104. Not a lever.

## 6. The ladder

### 6.1 Protocol

**Protocol D$_S$.** Protocol D of note 11 (note 14's unified form) with, per level, numbers $s_1 \ge 1$ and $s_2, \dots, s_\ell \ge 0$. After the commitment, $s_1$ points and answers as in Protocol D. For $j = 1, \dots, \ell - 1$ the verifier's message of round $j$ is $(\alpha_j, \beta_j)$ **followed in the same message by** $s_{j+1}$ fresh points $z = (\theta, \zeta) \leftarrow E^2$. The prover's message of round $j + 1$ starts with the answers $y = \mathrm{ev}^{(j)}_z(P^{(j)})$ to these points (evaluations of the tuple after $j$ rounds, with the lane weights of Definition D1 for the remaining variables), then continues as in Protocol D with one $\varphi$ for every point held so far, the new ones included. A new point's carried value starts at $v := y$ and is updated like the others. At the end of the level all $\sigma_\ell = \sum_b s_b$ claims are converted and batched as in Protocol D ($J_{i+1} = 1 + \sigma_\ell + t_i$), or checked on the final polynomial at the last level. A point of batch $b$ costs $\ell - b + 2$ scalars.

Completeness is Lemma D1 (E2), (E3) from round $b$ on. **[proved]**, **[checked]**: `15_batch_toy.py`, $\mathrm{GF}(2^8)$, $\ell \in \{3, 4, 6\}$, 60 honest runs with random schedules, about 1800 identities; an altered answer or $\varphi$ breaks an identity in 139 or 140 of 140 runs (the exception is a zero multiplier, probability $1/q$).

### 6.2 Lemma S

Write $\sigma_j := s_1 + \dots + s_j$ (the points available at round $j$) and let $N_j$ be the number of ordered triples of $\mathcal{T}(O^{(j-1)})$ with pairwise distinct challenges, not dependent, with $\mathrm{ev}^{(j)}_z(Q) = 0$ at all $\sigma_j$ points. $N_j$ is a function of the committed word, the challenges $c_1, \dots, c_{j-1}$ and the batches $1, \dots, j$; no prover message enters.

**Lemma S (ladder potential). [proved]** Let $e_j := \dfrac{4L^3q^6}{K_0^3}\,\epsilon^{\sigma_j}$, where $L$ bounds the lists of all folds as in Lemma D4. After each verifier message $t$ of the level (the batch-1 message, then the messages $(c_j, \text{batch } j+1)$) let
$$T(t) := \sum_{j \text{ not yet started}} \frac{\mathbb{E}[N_j \mid \text{verifier messages up to } t]}{(K_0^3/4)\,\tau^{\,n_j(t)}},$$
where $n_j(t)$ is the number of fold-challenge messages after $t$ and before round $j$. Then:
(a) $\Pr[T \ge 1 \text{ after the batch-1 message}] \le \sum_{j=1}^{\ell} e_j\,\tau^{-(j-1)}$.
(b) If $T < 1$ before the message $(c_j, \text{batch } j+1)$, then $T \ge 1$ after it with probability less than $\tau$.
(c) If $T < 1$ after the message that precedes round $j$ (the batch-1 message for $j = 1$), then $N_j < K_0^3/4$, so the $\sigma_j$ points held at round $j$ are not in $\mathrm{Exc}_j(O^{(j-1)})$ and Lemma D4(2) applies to round $j$ with all carried claims.

*Proof.* The verifier's messages are independent and uniform, so $V_j(t) := \mathbb{E}[N_j \mid \text{messages up to } t]$ is a martingale in $t$, and for every fixed prefix $c_1, \dots, c_{j-1}$ the $\sigma_j$ points are independent of $\mathcal{T}(O^{(j-1)})$, so by Lemma D4(1)'s count $\mathbb{E}[N_j] \le L^3q^6\epsilon^{\sigma_j} = (K_0^3/4)\,e_j$. (a) Before the batch-1 message $n_j = j - 1$, so $\mathbb{E}[T] \le \sum_j e_j\tau^{-(j-1)}$; Markov. (b) The message $(c_j, \text{batch } j+1)$ is one uniform draw. Every term $j' > j$ has $n_{j'}$ lowered by one, so its denominator grows by $1/\tau$, while its numerator keeps its conditional mean; the term $j$ leaves the sum. So $\mathbb{E}[T \text{ after} \mid \text{before}] \le \tau\,T(\text{before}) < \tau$; Markov. (c) For that $j$, $n_j = 0$ and $N_j$ is determined, so the term is $N_j/(K_0^3/4) \le T < 1$. In Lemma D4, $\mathbf z \in \mathrm{Exc}_j$ means $N_j \ge K_0^3/4$ for the points the lemma is applied with, here all $\sigma_j$. $\square$

With $s_2 = \dots = s_\ell = 0$ this is Lemma D6 word for word. The new content is that points sampled with a fold challenge count in full for all later rounds and cost no budget of their own, because the message they ride in already pays $\tau$ for the potential.

**Theorem D$_S$. [proved]** from Lemma S and the proof of Theorem D (note 11, section 2.5; note 14, section 4), under the same hypotheses. Protocol D$_S$ has the round-by-round errors of Theorem D with the point message of level $i$ replaced by
$$\varepsilon^{\mathrm{pt}}_i = \binom{L_i}{2}\epsilon_i^{\,s_1} + \frac{4L_i^3q^6}{K_0^3}\sum_{j=1}^{\ell_i}\tau^{-(j-1)}\,\epsilon_i^{\,\sigma_j},$$
the fold message unchanged at $K_0/q^2 + \tau$ (no $\tau$ at $j = \ell_i$), and the query message at $((A^{(i,\ell_i)} - 1)/n_i)^{t_i} + (\sigma_{\ell_i} + t_i)/q$.

*Proof.* The state after the message $(c_j, \text{batch } j+1)$ is: $(\mathrm{I}_{i,j})$ no member of $\mathrm{List}^{(i,j)}$ satisfies the running claim and the point claims of batches $1, \dots, j$; and $T < 1$. It depends on the transcript up to that message only (the answers to batch $j + 1$ are not in it). The prover's next message adds claims, which can only shrink the set $(\mathrm{I})$ quantifies over, so $(\mathrm{I})$ holds with the new claims included, and that is the hypothesis of Lemma D4(2) for round $j + 1$ with all $\sigma_{j+1}$ points; by (c) these points are not exceptional. So fewer than $K_0$ challenges $c_{j+1}$ break $(\mathrm{I}_{i,j+1})$, an event of $c_{j+1}$ alone, and by (b) the potential part fails with probability less than $\tau$. The level entry (pinning by batch 1, the batching without a list factor), the level exit, the last level and the tail are as in Theorem D with $\sigma_\ell$ claims in place of $s$. The relativised form (knowledge soundness) is unchanged for the same reason. $\square$

Not covered beyond note 11 and note 14: the Fiat-Shamir compilation and the formal `Spec` (one more squeeze group per fold message, a round loop whose number of carried points grows), which I did not write out.

### 6.3 The general form, and why the ladder is the best schedule

If a batch has its own verifier message, that message needs an allowance $\delta'$ for the potential, and every round that uses the batch on top of older points pays $\log_2(1/\delta') \approx 110$ bits for it; a round may also ignore the older points (start afresh), which removes the nesting discount and the old points at once. `15_schedules.py` implements this general accounting (docstring) and searches all schedules: the best with separate messages are 8 points at commit and 5 before round 4 (13 points, 76 scalars, 0.745), or 7, 4, 3 at rounds 1, 3, 5 (0.732). **[checked]** arithmetic; the general lemma is the proof above with $\delta'$ in place of $\tau$ at a batch message and an extra sum for rounds entering there.

Among schedules whose top-ups ride with the fold challenges, the ladder (the least $\sigma_j$ at every $j$) is optimal for the prover's work, the scalars and the verifier's work at once: any valid schedule has $\sigma_j$ at least the ladder's up to the split of the budget among the $\ell$ terms, and a point costs less in every respect the later it is sampled. **[proved]** by exchange; the script removes or delays single points until none can be.

What a round needs, at level 0 with the deployed grinds: $104\,\sigma_j \ge \log_2 C_1 + 110 + 119(j-1)$ plus the share of the sum, with $\log_2 C_1 = 359 + 3\log_2 L$ today. Any improvement of $C_1$ by researcher 16 enters here and nowhere else.

## 7. Numbers

`python3 scripts/15_schedules.py`; its selftest reproduces note 11's table T1 (20 cells) and the 1064 bits. Costs: a point of batch 1 at level 0 is $2^\mu$ products $K \times E$ (two carry-less multiplications each), a point of batch $b \ge 2$ is $2^{\mu - b + 1}$ products $E \times E$ (three each, accumulated unreduced), against $24 \cdot 2^\mu$ multiplications in the level-0 NTT at rate 1/2 (halve the fractions at rate 1/4, and so on): $1/12$ for batch 1 and $2^{-(b-1)}/8$ for batch $b$. Verifier products in $E$ per point: about $2\kappa + \ell + 3$ for the chain of $\widehat W_k(\zeta)$, the terminal product and the conversion, plus 3 per round carried (a formula count, **[estimate]**). All rows **[checked]** arithmetic on **[proved]** bounds.

**Level 0** ($\kappa = 24$, $\ell = 6$, $\epsilon = 2^{-104.0}$; valid for every rate, $n \le 2^{28}$):

| list | design | batches (points @ round) | points | scalars | bytes | prover, of NTT$_0$ | verifier products | extra messages |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $2^{40}$ | D (note 11) | 12@1 | 12 | 84 | 1344 | 1.000 | 900 | 0 |
| | **ladder** | 6@1 1@2 1@3 2@4 1@5 1@6 | 12 | 66 | 1056 | 0.637 | 846 | 0 |
| | two batches | 8@1 5@4 | 13 | 76 | 1216 | 0.745 | 930 | 1 |
| | three batches | 7@1 4@3 3@5 | 14 | 78 | 1264 | 0.732 | 990 | 2 |
| | fresh every round | 6 at each round | 36 | 162 | 2632 | 1.227 | 2430 | 5 |
| | full columns | 12@1 | 12 | 768 | 12288 | 1.000 | more | 0 |
| $2^{100}$ | D | 14@1 | 14 | 98 | 1568 | 1.167 | 1050 | 0 |
| | **ladder** | 8@1 1@2 1@3 1@4 1@5 2@6 | 14 | 78 | 1248 | 0.792 | 990 | 0 |
| | two batches | 10@1 5@4 | 15 | 90 | 1440 | 0.911 | 1080 | 1 |
| | fresh every round | 8 at each round | 48 | 216 | 3496 | 1.635 | 3240 | 5 |
| | full columns | 14@1 | 14 | 896 | 14336 | 1.167 | more | 0 |
| $2^{300}$ | D | 19@1 | 19 | 133 | 2128 | 1.583 | 1425 | 0 |
| | **ladder** | 14@1 1@2 1@3 1@4 1@5 1@6 | 19 | 118 | 1888 | 1.288 | 1380 | 0 |
| | two batches | 16@1 5@4 | 21 | 132 | 2112 | 1.411 | 1530 | 1 |
| | fresh every round | 14 at each round | 84 | 378 | 6088 | 2.862 | 5670 | 5 |
| | full columns | 19@1 | 19 | 1216 | 19456 | 1.583 | more | 0 |

(Two-batch rows without a grind on the second message; with the 15-bit grind the $2^{300}$ row is 16@1 4@4 and each row has 8 more bytes. The three-batch and fresh rows count an 8-byte nonce per extra message.) The points available per round on the ladder at $2^{40}$ are 6, 7, 8, 10, 11, 12: round $j$ gets what Lemma D6 would ask of a level of $j$ rounds.

**Later levels** ($\ell = 4$; the prover's work is below 0.03 of NTT$_0$ in every row and is not the criterion):

| level shape | list | D: points, scalars | ladder: batches, scalars |
| --- | --- | --- | --- |
| $\kappa = 20$ | $2^{40}$ | 9, 45 | 6@1 1@2 1@3 1@4, 39 |
| | $2^{100}$ | 11, 55 | 8@1 1@2 1@3 1@4, 49 |
| | $2^{300}$ | 16, 80 | 13@1 1@2 1@3 1@4, 74 |
| $\kappa = 4$ | $2^{40}$ | 8, 40 | 5@1 1@2 1@3 1@4, 34 |
| | $2^{100}$ | 10, 50 | 7@1 1@2 1@3 1@4, 44 |
| | $2^{300}$ | 15, 75 | 12@1 1@2 1@3 1@4, 69 |

**Whole opening**, $\mu = 30$, the same list bound at every level:

| list | design | points per level | scalars (bytes) | prover, of NTT$_0$ | verifier products |
| --- | --- | --- | --- | --- | --- |
| $2^{40}$ | D | 12 9 9 9 8 8 | 299 (4784) | 1.019 | 2773 |
| | ladder | 6+1+1+2+1+1, 6+1+1+1 (three levels), 5+1+1+1 (two levels) | 251 (4016) | 0.651 | 2629 |
| $2^{100}$ | D | 14 11 11 10 10 10 | 358 (5728) | 1.190 | 3310 |
| | ladder | 8+1+1+1+1+2, 8+1+1+1, 7+1+1+2, 7+1+1+1 (three levels) | 305 (4880) | 0.810 | 3151 |
| $2^{300}$ | D | 19 16 16 15 15 15 | 518 (8288) | 1.617 | 4760 |
| | ladder | 14+1+1+1+1+1, 13+1+1+1 (two levels), 12+1+1+1 (three levels) | 473 (7568) | 1.317 | 4625 |

**If the single-round constant were $\binom{L}{2}$** (the hypothetical in which only the pinning count is left; nothing here proves it):

| list | D at level 0 | ladder at level 0 | whole opening, D | whole opening, ladder |
| --- | --- | --- | --- | --- |
| $2^{40}$ | 8 points, 56 scalars, 0.667 | 2@1 1@2 2@3 1@4 1@5 1@6: 8 points, 39 scalars, 0.319 | 186 scalars, 0.679 | 136 scalars, 0.325 |
| $2^{100}$ | 9, 63, 0.750 | 3@1 2@2 1@3 1@4 1@5 1@6: 9, 47, 0.434 | 218, 0.765 | 170, 0.442 |
| $2^{300}$ | 13, 91, 1.083 | 7@1 1@2 2@3 1@4 1@5 1@6: 13, 74, 0.736 | 331, 1.104 | 284, 0.752 |

**The real cost.** The nesting bits are paid in both designs; what changes is where. At list $2^{40}$ the 5.7 points the nesting needs cost D 0.475 of the level-0 NTT's multiplications and the ladder 0.137; the 6 points of the single round cost 0.5 in both. Recursive verifier: the same 12 chains at level 0, 18 fewer carried updates, the same number of squeezes spread over the fold messages, and a round loop with a growing number of carried points; about 6 percent fewer field products on the point path (**[estimate]**). Proving time: note 11's unmeasured guess of 3 to 10 percent for the 12 points becomes 1.9 to 6.4 percent.

## 8. Recommendation

Adopt the ladder as the shape of Protocol D: at every level the number of points available at round $j$ is the least $\sigma_j$ with $\binom{L}{2}\epsilon^{\sigma_1} + C_1\sum_j \tau^{-(j-1)}\epsilon^{\sigma_j} \le 2^{-110}$, the first $\sigma_1$ after the commitment and the increments with the fold challenges. At level 0 and list $2^{40}$: 6, then 1, 1, 2, 1, 1. It needs no new hypothesis, no new verifier message and no new grind, it dominates the single batch on every count, and it is the only design in the table that does. Whatever researcher 16 obtains for the single-round constant plugs into $C_1$. Keep one batch only if the growing per-round loop is unwelcome in the guest, at the price in the table.

Do not adopt full columns, a shared lane point, end-of-level discharge or independent fresh batches.

## 9. Status

Proved in this note (by hand): Lemma L; Proposition N and its reading against Lemma D6; Construction N$_k$ as an algebraic statement; Proposition U; the unsoundness or dominance of variants (a), (c), (d); Lemma S and Theorem D$_S$ (given Lemma D4 and Theorem D of note 11, which notes 10 and 14 re-derived); the optimality of the ladder among its class.

Checked numerically: Proposition N at $q = 32$ and $64$ over all first challenges, with the exact winning counts; six lines for four members at $n = 32$; the flats family; N$_2$ at $q = 32$; Markov's tightness by exhaustive algebra; the red team's nested words under the stronger test; the fresh point; completeness of mid-level batches; the selftest of the accounting against note 11.

Conjectured or open: Conjecture C (the loss is not real for soundness); the existence at level-0 parameters of words with 33 (one reuse) to $2^{23}$ (five reuses) list members whose differences share a factor $R_0$ of degree comparable to $d$, on which "real" in item 1 of the summary depends for the deployed $\tau$ (for $\tau_L = L/q$ with any $L \ge 1$ it is unconditional given two such members); the extension-field variant.

Not done: no timing of the prover; the guest and native verifier counts are formula counts; Protocol D$_S$ was not run end to end with Merkle openings and the sponge (the toy checks the algebra only); nothing formalised.

**A bug that was fixed before any number above was produced.** The first build of `15_nesting.c` declared the members' polynomials $D'_i$ (`MHP`) as an `int` array and passed it to the harness's byte-array routines, so the planted word used only a quarter of each array (read as bytes) while the "same fold" test and the claim computation read it as integers. The compiler warned, the lead flagged it, and the type is `uint8_t` in the file as delivered, which builds with `-Wall -Wextra` and no warning (the flags `15_run.sh` uses). The only output of the faulty build was one exploratory run at $q = 32$: an expectation $1.75 \cdot 10^{-3}$ and "32 predicted, 31 spoiled" in place of $7.71 \cdot 10^{-4}$ and "31 predicted, 31 spoiled". Neither faulty value appears in this note. Every number in sections 2 to 4 comes from a complete rerun of `15_run.sh` with the corrected, warning-free build.

## 10. Reproduction

- `sh doc/whir_soundness_gap_notes/scripts/15_run.sh` builds `15_nesting.c` with the system compiler into `$TMPDIR` and runs every experiment (items A1 to A4, B, C, D, E; each under six minutes on one thread, the whole set under fifteen). `sh 15_run.sh A2` runs one item. Seeds are fixed.
- `python3 doc/whir_soundness_gap_notes/scripts/15_schedules.py` prints every table of section 7 (one second); `... selftest` checks the accounting against note 11's table T1 and the minimality of the ladders.
- `python3 doc/whir_soundness_gap_notes/scripts/15_batch_toy.py [seed]`: completeness of batches introduced at any round.
- One run by hand: `cc -O2 -Wall -Wextra -o nest15 15_nesting.c -lpthread && ./nest15 m=5 N=4 d=3 A=6 word=n1 M=2 r=2 mode=scan s=3 pts=roots cor=3 fresh=1`. Options: `word` (`n1`, `n2`, `flat4`, `random`, `planted1`, `planted2`, `pole`, `poleflat`), `mode` (`scan`, `scan2`, `alg`), `pts` (`generic`, `roots`, `roots1`, `uniform`), `M`, `r`, `s`, `k0` (multiple of $q$), `nc1`, `online`, `cor`, `fresh`, `seed`.
