# 20. Referee report on the protocol theorem (DEEP-fold WHIR)

Researcher 20 (round 4), independent second referee of the whole theorem: note 14 (Protocol D, Theorem D', Theorem K, the interface, Theorem I, Proposition R2'), with notes 10 and 11 behind it and notes 15 (the ladder, Lemma S, Theorem D$_S$, Construction N1) and 16 (Proposition 3.1, Theorem B, two protocol remarks) on top. Notation is note 14's throughout: $q = |E| = 2^{128}$, levels $i$, $\kappa_i$, $\ell_i$, $n_i$, $d^{(i)} = 2^{\kappa_i} - 1 + \ell_i$, $A^{(i,j)} = A_i - (\ell_i - j)$, $\epsilon_i = (d^{(i)} + 2^{\ell_i} - 1)/q$, points $z = (\theta, \zeta)$, $\mathrm{ev}^{(j)}_z$, $\mathcal T$, classes, $Q$, $N(\mathbf z)$, $\mathrm{Exc}_j(O)$, the potential $T_k$, $K_0$, $\tau$. I write $\Theta := K_0(K_0-1)(K_0-2q)$. Statuses: **[proved]** (a proof in this note or a proof of another note that I re-derived line by line; by hand, not machine-checked), **[checked]** (numerically, sizes given), **[conjectured]**, **[inherited]** (a statement of the existing formalization or of another note that I read and did not re-derive). No Lean, Rust or LaTeX was edited, and no other note was edited: the corrections to other notes are listed here. Scripts, all new and written from scratch: `scripts/20_lines.c`, `scripts/20_attacks.py`, `scripts/20_ladder_toy.py`, `scripts/20_params.py`.

## 0. Verdict

**Theorem D' of note 14 is CORRECT as written.** The protocol, the hypothesis, the state function, every transition, every per-message error and every point count stand. So do Theorem K and Corollary K2 (knowledge soundness with the descent extractor), Theorem I, Proposition R2', and the ladder (Lemma S and Theorem D$_S$ of note 15). I re-derived every lemma and every transition and found no gap, I found no attack, and the theorem needs no new term.

Note 16 is also right, and the two do not contradict each other. Proposition 3.1 of note 16 (a list member that misses the answers at exactly one point wins a whole line of fold challenges, so $k$ members that share $s - 1$ answers win $kq$ challenges with one prover message under the zero weight) is **[proved]** and **[checked]** here with independent code. But the exceptional set of Lemma F is not the set that note 10 described in words. It is *defined* by the triple count $N(\mathbf z) \ge \Theta$, and that set contains every point tuple of note 16 for which $kq \ge K_0$ (Proposition R1 below; in the brute force, 310 of 310 tuples). Its probability bound $L^3q^6\epsilon^s/\Theta$ exceeds $s\binom L2\epsilon^{s-1}$ by more than $2^{600}$ at every level, so nothing binds. Lemma P's $\binom L2\epsilon^s$ is a correct bound for the only thing the proof uses it for (at most one list member matches *all* $s$ answers). What note 16 refutes is the *conjecture* of note 10 (and the sentences that repeat it), not a theorem.

Corrections, none of them to Theorem D':

1. **Note 10, section 2.3 and section 9 item 3; note 14, section 9 item 6.** The conjectured floor $(n/q)^s + \binom\Lambda2\epsilon^s$ and "2 or 3 points might suffice" are refuted as statements about the state function of notes 11 and 14: the true floor is $s(r/q)^{s-1}$, and $s(n/q)^{s-1}$ with points uniform in $E$. Any theorem that replaces the triple count by an explicit description of the exceptional points must carry $s\binom L2\epsilon^{s-1}$ (Theorem B of note 16 does). The honest summary is: proved 12 points at level 0 for lists of $2^{40}$ (6 after the commitment on the ladder), floor of this state function 3, best attack I can build breaks 1 point and not 2.
2. **Note 15, summary item 6 and the last table of section 7** (the hypothetical "if the single-round constant were $\binom L2$"). One point too few at every level. Corrected hypothetical counts: one batch 9, 7, 6, 6, 6, 6 at $2^{40}$ and 10, 8, 7, 7, 7, 7 at $2^{100}$ (these equal note 16's Theorem B row); hypothetical ladders $3{+}2{+}1{+}1{+}1{+}1$ at level 0 for $2^{40}$ (note 15 has $2{+}1{+}2{+}1{+}1{+}1$) and $5{+}1{+}1{+}1{+}1{+}1$ for $2^{100}$. Nothing proved changes: Theorem D$_S$ and the proved ladder schedules ($6{+}1{+}1{+}2{+}1{+}1$ and $8{+}1{+}1{+}1{+}1{+}2$ at level 0) are confirmed.
3. **Note 15's remark on the red team's test is right.** `count_exceptional` of `10_deep_redteam.c` compares the largest class with the number of challenges, so it cannot see several full classes that share all answers. Confirmed with independent code (4 of 4 such tuples missed by the weak test and found by the strong one). No conclusion of note 10 about the theorem depends on it; its measured exceptional frequencies are lower bounds.
4. **Note 16's two protocol remarks need no protocol change.** (a) Drawing $\zeta$ outside $D$ changes no proved bound and no count; it is optional, and worth doing only together with a future sharper proof. (b) $K_0$ is a constant of the analysis, not of the protocol, and note 14 already takes the largest value its fold budget allows ($2^9q$).
5. **Constants.** Theorem D$_S$ of note 15 is stated with note 11's constant $4/K_0^3$; with note 14's $1/\Theta$ it is the same statement with a slightly smaller bound. The final statement below uses $1/\Theta$ everywhere.
6. **"One round message serves one line" (note 10, strategy S2; note 15, summary item 8; note 16, end of section 3) is not right.** Proposition R3 below, **[proved]** and **[checked]** by exact maxima over all prover messages: against a claim that every member violates, with a weight in general position, the prover can always align *two* of the $k$ lines; and it can align *all* $k$ lines, for every weight, when the members lie on one affine line $G_a = G + h_a\Delta$, which is the shape of note 16's own example word. Such a family has at most $(n - d)/(A - d)$ members (5 at rate 1/2 and $A = 0.6n$, 15 at rate 1/16 and $A = n/8$), so this is inside $K_0$ and changes neither the theorem nor the attack verdict, but the fold error of this state function on a doomed state really is $k/q$ with a false claim, not only with the zero weight.
7. **A grind.** Without the multilinear OOD claim the pool has at most 511 claims unless the cap is reused, so the first message's error is at most $512/q$ and the rule $\lceil\log_2 N\rceil - 3$ gives 6 bits; note 14's 7 bits is correct for $J_0 \le 512$ and safe in both readings.

Attacks (section 5): no path against Protocol D or the ladder costs less than $2^{125}$ hash evaluations at the proved point counts, and none that I can build costs less than $2^{125}$ with as few as two points per level, except at thresholds within a factor $1 + 2^{-10}(n/d - 1)$ of the degree, which nothing here uses. With one point per level the protocol is broken at rate 1/4 below $n/2$ (cost about $2^{117}$, flats through a point that lands in $D$). The gap between 2 points (no attack) and 12 (proof) is the residual gap of largest practical weight after the hypothesis itself.

The consolidated final statement is section 6, the residual gaps with severities are section 7.

## 1. What was done

- Read notes 14, 15 and 16 in full; of notes 10 and 11 the statements that note 14 reconciles (Theorem A, sections 2.3, 5.3, 8 and 9 of note 10; Lemmas D4 to D6 and Theorem D of note 11), which are the same statements as note 14's up to constants, and the function `count_exceptional` of `10_deep_redteam.c`; Annex A and Annex B of `doc/leanvm`, section 08 (the end-to-end message order), `crates/verifier/src/whir.rs` (`derive_config`, the grinds), and the definitions `oodCands` and `ringSpec` in `formal/` (to check what the interface actually charges).
- Re-derived by hand, from note 14's text: Lemmas E, L1, L2, F, P, T, every transition M0 to M5, the boundary cases, Theorem K with the descent, Corollary K2, Theorem I, Proposition R2', Lemma S and Theorem D$_S$, Propositions 3.1 and Theorem B of note 16, Lemma L and Proposition N of note 15. Section 3 lists what was checked at each step.
- Ran: an independent exhaustive block search over all $q^2$ point pairs at $q = 64$ (`20_lines.c`); exact counts of winning challenges for ten cheating strategies, with exact maxima over all prover messages at $q = 16$ (`20_attacks.py`); the ladder end to end on note 11's two-level toy (`20_ladder_toy.py`); exact arithmetic for every count and error (`20_params.py`); and the existing `16_sharp.c` (reproduced: 310 exceptional pairs of 4096, frequency 0.075684), `15_nesting.c` (Construction N1, all 1024 first challenges at $q = 32$: 31 spoiled, the 31 predicted), `11_protocol_toy.py`, `14_extractor_toy.py` (reproduced).

## 2. Note 16 against notes 10, 11 and 14

### 2.1 Three different things are called the exceptional set

- $\mathrm{E_N}$, the set of the theorems: $\{\mathbf z : N(\mathbf z) \ge \Theta\}$, with $N$ the number of ordered triples of $\mathcal T$ with pairwise different challenges, $Q \ne 0$ and $\mathrm{ev}_{z_m}(Q) = 0$ for all $m$. Theorem 3 of note 07, Theorem A of note 10, Lemma D4 of note 11 and Lemma F of note 14 all define it this way. It is not described by which configurations it contains.
- The *description* of note 10, section 2.3: "all $s$ points in $D$, or two list members (or two pole lines) sharing all $s$ answers", with the conjectured probability $(n/q)^s + \binom\Lambda2\epsilon^s$. This is a conjecture about $\mathrm{E_N}$, or about the smaller set soundness needs, and it is marked as such there.
- The *test* in `10_deep_redteam.c` (`count_exceptional`), a program.

Note 16 attacks the second. The theorem uses only the first.

### 2.2 Both are right

**Proposition R1 (the theorem's set contains note 16's tuples). [proved]** In the setting of Lemma F of note 14, let $\mathbf z$ be a point tuple for which some weighted claim, carried values, predicate and prover message satisfy the hypothesis of Lemma F(2) and at least $K \ge K_0$ challenges admit a $P$ with (p), (w), (b). Then $N(\mathbf z) \ge K(K-1)(K-M) \ge \Theta$, so $\mathbf z \in \mathrm{Exc}_j(O)$. In particular the tuples of Proposition 3.1 of note 16 with $kq \ge K_0$ are in $\mathrm{Exc}_j(O)$.

*Proof.* This is the contrapositive of Lemma F(2), whose proof is checked in section 3: choose one $P$ for each winning challenge; every class holds at most $M = \max(2q, \binom n2)$ of the chosen elements (a class of a near pair that misses an answer holds at most a line, $q$); by L1(d) at least $K(K-1)(K-M)$ ordered triples are not in one class, and by L1(b), (c) each is counted by $N(\mathbf z)$. For the family of note 16 directly: the $kq$ elements lie on $k$ parallel lines of challenges, one in each member's class. $\square$

**Corollary R2 (the lower bound of note 16 is below the upper bound of Lemma F(1), always). [proved]** If $k$ members with $kq \ge K_0$ exist then $\Lambda q \ge K_0$, so $\Lambda^3q^6\epsilon^s/\Theta > q^3\epsilon^s \ge (q^3\epsilon/s)\cdot s(r/q)^{s-1}$ for every $r \le d$, and $q^3\epsilon/s > 2^{250}$ at every level. If $\Lambda q < K_0$ no such family exists and Proposition 3.1 says nothing. **[checked]** at the deployed constants: the proved point error exceeds $s\binom L2\epsilon^{s-1}$ by a factor between $2^{629}$ and $2^{946}$ over all levels of the $\mu = 30$ ladder and both list budgets (`20_params.py`, table P4).

**What Lemma P is used for. [proved]** Theorem D' uses separation in exactly three places: M1 (at most one $U^\ast \in \mathrm{List}^{(0,0)}$ satisfies all commit-phase point claims), M3 (the same for $\mathrm{List}^{(i+1,0)}$), and Corollary K2. Each needs "two distinct members differ at some point", which fails with probability at most $\binom L2\epsilon^s$: Lemma P as stated. Separation by every $s - 1$ of the points is used nowhere. A member that matches all answers but one is not a candidate of the invariant $(\mathrm I)$: it violates a point claim, the state calls the run doomed, and the member is dealt with in the next fold round inside Lemma F(2), in the case "some $\delta_m \ne 0$: at most a line".

**So what happens to note 16's tuples in Theorem D'.** Two regimes, both covered. If fewer than $K_0/q = 2^9$ members share $s - 1$ answers, the prover wins fewer than $K_0$ challenges, which is the fold message's error $(K_0 - 1)/q^2$: nothing exceptional has happened. If at least $2^9$ do, the points are in $\mathrm{Exc}_1$ of the committed word, $T_0 \ge 1$, and the event was charged to the point message M0, whose bound is far above its true probability. The same holds at later rounds through the potential.

**Where the factor $s\,\epsilon^{s-1}$ does matter. [proved]** In any statement that replaces $\mathrm{E_N}$ by an explicit set, or the constant $L^3q^6/\Theta$ by a constant that is polynomial in $L$ alone. Theorem B of note 16 is such a statement and has the term; I checked its proof (the split into unexplained elements, near pairs with $t(U) = 0$, $1$, $\ge 2$ missed answers, and the use of (X1), (X2)) and it is correct. With its unconditional input $|\mathcal T_{\mathrm{un}}| \le Lq^2$ and $K_u = K_0 - sq - L$ it gives exactly the counts of Lemma F (`20_params.py`, table P6: 12, 9, 9, 9, 8, 8 and 14, 11, 11, 10, 10, 10), as note 16 says.

### 2.3 Brute force

`20_lines.c`, written from scratch: $\mathrm{GF}(2^6)$, $n = 16$, $d = 2$, $A = 5$, one lane per half, $s = 2$, **every** one of the 4096 ordered point pairs, every one of the $q^4$ answer vectors. Word: note 16's `kpairs` with a fresh seed (three members $(F, G + RH_a)$, $R$ of degree 2 with roots 56 and 60 outside $D$; $|\mathcal T| = 12288$, 27 near pairs, no unexplained element). $K_0 = \lceil 2.72q\rceil = 175$, $M = 128$, $\Theta = 1431150$. Columns: the pairs with $K_{\mathrm{void}} \ge K_0$ ($K_{\mathrm{void}}$ is the largest number of challenges consistent with an answer vector that no near pair matches at both points, so that the hypothesis of Lemma F(2) is void and the zero weight wins them all); the weak test (the red team's: largest class below 74 percent of the challenges); the strong test (note 15's: at least $0.26K_0$ challenges have a consistent element outside the largest class); and the pairs for which the block alone already gives $N(\mathbf z) \ge \Theta$ (exact count of the block's triples with $Q \ne 0$, each verified to have $Q(\zeta_m) = 0$). **[checked]**

| category of the point pair | pairs | $K_{\mathrm{void}} \ge K_0$ | weak test | strong test | in $\mathrm{Exc}$ of note 14 by the block's triples | $K_{\mathrm{void}}$ |
| --- | --- | --- | --- | --- | --- | --- |
| both coordinates roots of $R$ | 4 | 0 | 0 | 4 | 4, by hand (below) | 64 |
| exactly one root of $R$ | 248 | 248 | 248 | 248 | 248 | 192 = $3q$ |
| equal coordinates, not a root | 62 | 62 | 62 | 62 | 62 | 192 |
| both in $D$, distinct | 240 | 0 | 0 | 0 | | below 100 |
| exactly one in $D$ | 1472 | 0 | 0 | 0 | | below 100 |
| generic | 2070 | 0 | 0 | 0 | | below 100 |
| all | 4096 | 310 | 310 | 314 | 310 | |

Frequency of $K_{\mathrm{void}} \ge K_0$: 0.0757, equal to note 16's prediction $2(r/q)(1 - r/q) + (q - r)/q^2 = 0.0757$ and not to note 10's formula $(n/q)^2 + \binom32(d/q)^2 = 0.0654$, whose two events (both points in $D$; two members sharing both answers) contribute nothing to it here. Every one of the 310 tuples is in the set of note 14 already by the triples of its one block. The four pairs at two roots are in it as well, **[proved]**: the one block that all three members match holds three full classes, and one element per challenge, a third from each class, gives $K(K-1)(K - \lceil q^2/3\rceil)$ triples with $K = q^2$. The existing `16_sharp.c`, rerun on its own word, gives 310 of 4096 as note 16 reports. So: Proposition 3.1 is real, with exactly the predicted frequency; and Proposition R1 holds on every instance.

The same program on a uniformly random pair of words ($|\mathcal T| = 3754$, no near pair, every element unexplained): 256 exceptional pairs, namely all 240 pairs with both coordinates in $D$ and the 16 pairs with equal coordinates in $D$, frequency $0.0625 = (n/q)^2$. This is the event of note 10, and all 256 are again in the set of note 14 by the triples of one block. So each of the two descriptions is right about the word it was found on and incomplete in general; for an explained word the exceptional points are those where $s - 1$ answers are shared, for a word with no near pair those where all $s$ points are in $D$, and the set $\mathrm{E_N}$ of the theorem contains both without having to know. **[checked]**

### 2.4 Every place the term or the count could have had to change

| where | statement | verdict | change |
| --- | --- | --- | --- |
| note 14, Lemma P; note 11, Lemma D5 | separating except with probability $\binom L2\epsilon^s$ | correct, and sufficient for M1, M3, K2 | none |
| note 14, Lemma F; note 11, Lemma D4; note 10, Theorem A | $\Pr[\mathrm{Exc}] \le \Lambda^3q^6\epsilon^s/\Theta$; off $\mathrm{Exc}$ fewer than $K_0$ winning challenges | correct; $\mathrm{Exc}$ contains note 16's tuples (R1) | none |
| note 14, Theorem D', M0 | $[\binom{L}{2} + (L^3q^6/\Theta)\sum_{j<\ell}\tau^{-j}]\epsilon^{s}$ | correct | none |
| note 14, Theorem D', M2 | $(K_0 - 1)/q^2 + \tau$ | correct; includes up to $2^9 - 1$ lines of note 16's kind | none |
| note 14, section 7.4 and section 8 (points per level) | 11 to 14 at level 0, 7 to 11 later | reproduced | none |
| note 14, section 9, item 6 | "2 or 3 points might suffice" | too optimistic by one point for this state function | replace by the three numbers of correction 1 |
| note 10, section 2.3, last bullet; section 9, item 3 | floor $(n/q)^s + \binom\Lambda2\epsilon^s$; "2, 3, 3 points" | refuted (note 16; section 2.3 above) | floor $s(r/q)^{s-1}$, and $s(n/q)^{s-1}$ for uniform points; "3, 4, 5" at level 0 without the nesting loss |
| note 10, strategy S2 ("one round message can give a whole line to one such candidate only"); note 16, end of section 3 ("a second line is aligned with probability about $q^{-2}$") | not right | two lines always; all $k$ lines for members on one affine line, for the zero weight, and for members with one low part and a true claim (Proposition R3) | replace by Proposition R3 |
| note 15, Theorem D$_S$ | $\binom L2\epsilon^{s_1} + (4L^3q^6/K_0^3)\sum_j\tau^{-(j-1)}\epsilon^{\sigma_j}$ | correct (section 4) | optional: $1/\Theta$ for $4/K_0^3$ |
| note 15, proved ladder schedules | $6{+}1{+}1{+}2{+}1{+}1$, $8{+}1{+}1{+}1{+}1{+}2$, later levels | reproduced exactly | none |
| note 15, summary item 6; section 7, last table | hypothetical counts with constant $\binom L2$: 8 points, ladder $2{+}1{+}2{+}1{+}1{+}1$ | one point short | 9, 7, 6, 6, 6, 6 and $3{+}2{+}1{+}1{+}1{+}1$ at $2^{40}$; 10, 8, 7, 7, 7, 7 and $5{+}1{+}1{+}1{+}1{+}1$ at $2^{100}$ |
| note 15, Conjecture C | has $\epsilon^{s-1}$ already | consistent with note 16 | none |
| note 16, Theorem B and its table | conditional counts | correct | none |
| `doc/whir_soundness_gap.md`, section 3.3 | "about 35 bits per extra point" | consistent with the proved bound ($3b$ + constant against 104 bits a point) | none |

### 2.5 The red team's test

**[proved]** by reading `count_exceptional`: a cell (answer vector) with at least $K_0$ challenges is called bad unless its largest class is explained and has at least 74 percent of the cell's *challenge count*. If $m \ge 2$ near pairs match all answers, the cell holds $m$ full classes over the same $q^2$ challenges, the largest has 100 percent of the challenge count, and the cell is passed, although a set $W$ that alternates between the classes has no class at 74 percent (the event $\mathrm{E_3}$ of note 15), and although with a claim that all $m$ members violate the prover wins about $m$ conics. **[checked]**: in the table above the four pairs with both coordinates at roots of $R$ (all three members share both answers) are passed by the weak test and caught by the strong one. The test does see note 16's configuration when it is run on a word that has it (248 of 248): the red team did not miss it because of the test but because no word with three members sharing a first half and $s - 1$ answers was among its inputs, and because strategy S2 was dismissed for general weights.

Consequences. The frequencies of note 10, section 5.3 are lower bounds on $\Pr[\mathrm{E_3}]$; the configurations missed have probability at most $\binom\Lambda2\epsilon^s$ and were in note 10's formula anyway. Note 10's verdict on Theorem A (the lemma) does not use the test. Its nested experiment ("0 of 1024 first challenges spoiled") was rerun by note 15 with the strong test, still 0 for those words, and Construction N1 shows that it does not generalise. So: note 15's remark is right, and nothing in the theorem depends on it.

### 2.6 The two protocol remarks of note 16

**(a) Draw the points outside $D$. Optional; not part of the final statement.** **[proved]** that it changes nothing proved: Lemma E(E4) holds for $\zeta$ uniform on $E \setminus K$ with $q - 2^{64}$ in the denominator, which moves $s\log_2(1/\epsilon)$ by less than $2^{-59}$ bits, and the smallest margin of any count in section 6.3 is 3 bits. It can be had without a rejection loop in the verifier: reject a transcript whose $\zeta$ lies in $K$ and let the honest prover take the next grind nonce (probability $2^{-64}$ per point). What it buys is the removal of the floors $s(n/q)^{s-1}$ of Proposition 3.3 of note 16, which are below every proved bound by hundreds of bits, and of the only real attack I have on a one-point protocol (section 5; for the flats at rate 1/4 every pair of members is separated by every point outside $D$, section 5.3). It would matter for a sharpened proof with 3 points per level, and for a sharpened ladder whose top-up is a single point (a top-up rides a message with a 7-bit grind, so a point in $D$ costs $2^{7}q/n$, between $2^{107}$ and $2^{110}$, to obtain; under the proved schedules this is inside $\tau$ by Lemma S and harmless). Decision: keep note 14's "not excluded"; revisit only with a sharper theorem.

**(b) Keep $K_0$ large. Nothing to change.** $K_0$ does not appear in the protocol. Theorem D' holds for every integer $K_0 > 2q$ with the errors it states, the point term falls as $K_0^{-3}$ and the fold term grows as $K_0$, and note 14 takes $K_0 = 2^9q$, the largest that keeps the fold message within $2^{-118}$ at $\tau = 2^{-119}$. The content of the remark is a constraint on future proofs: with $K_0 \le 5q$ the family of members that share their low part (Remark 3.4 of note 16) makes $s(2^\kappa/q)^{s-1}$ an unconditional floor.

### 2.7 How many of the $k$ lines a running claim lets through

Notes 10, 15 and 16 say that with a real running claim one round message makes one line win (note 15 measured $2q + 2$ for four members, which is two lines). The exact statement is this.

**Proposition R3. [proved]** Setting of Proposition 3.1 of note 16: members $U_a = (F, G_a)$, $a = 1, \dots, k$, of $\mathrm{List}(O; A, d)$ that share the answers at every point but $z_i$, with pairwise distinct $g_a := \mathrm{ev}^{(j)}_{z_i}(G_a)$ and $\zeta_i \ne 0$; the answers of Proposition 3.1 (honest and common at $m \ne i$, a carried value $v_i$ that no member matches). Let $(W, \sigma)$ be any weighted claim and $p_a := (g_a, \langle W_0, G_a\rangle, \langle W_1, G_a\rangle) \in E^3$.

- (a) For every prover message, the members whose whole line of challenges wins (satisfies (p) and (w)) have collinear points $p_a$. If at least one whole line wins, every other member wins at most one challenge.
- (b) Conversely let $I$ be a set of members with $p_a$ on one line, $\langle W_0, G_a\rangle = c + m\,g_a$ and $\langle W_1, G_a\rangle = c' + m'g_a$ for $a \in I$. If $m'\theta' + m \ne 0$ and $\sigma \ne \langle W_0, F\rangle + c' + m'u$, where $\theta' = \theta_i^{2^{j-1}}$ and $u := v_i + \theta'\mathrm{ev}_{z_i}(F)$ (the second condition says that the claim is false for the virtual member of the line that would match the answer $v_i$), there is a message for which every line of $I$ wins: $|I|\,q$ winning challenges.
- (c) Consequences. Any two members are collinear, so two lines can always be aligned, even when every member violates the claim. If $G_a = G + h_a\Delta$ with scalars $h_a$, all $p_a$ are collinear for every weight, and all $k$ lines are aligned whatever the claim (under the two conditions of (b), which exclude a set of weights and claims of density about $2/q$). Members with one low part are collinear with $m = m' = 0$, where (b) does not apply, and their lines all win if and only if the claim is true for the common low part. For a weight chosen independently of the members, three given members are collinear with probability $q^{-2}$.
- (d) A list has at most $(n - z)/(A - z) \le (n - d)/(A - d)$ members $(F, G + h_a\Delta)$ on one affine line, $z$ the number of columns where $\Delta$ vanishes and $(F, G)$ agrees with $O$.

*Proof.* Write the residual of (w) for the fold of $U_a$ as in the proof of Lemma F: $\rho_a(\alpha, \beta) = \delta^a_G + \alpha(\delta^a_G + e_a) + \alpha^2\delta_F + \beta\delta_0 + \alpha\beta(\delta_0 + \delta_1)$ with $\delta^a_G = \langle W_0, G_a\rangle + v_G$, $e_a = \langle W_0, F\rangle + \langle W_1, G_a\rangle + \sigma$, and $\delta_F, \delta_0, \delta_1$ the same for all members, since they involve $F$ and the message only. By Proposition 3.1 the challenges at which the fold of $U_a$ satisfies (p) are the line $\alpha + \zeta_i\beta = \gamma_a$ with $\gamma_a = \theta' + (u + g_a)\,t$, $t := 1/(\mathrm{ev}_{z_i}(F) + \varphi_i) \ne 0$ (if the prover is also off at a point $m \ne i$ with $\zeta_m \ne \zeta_i$, a member is confined to the intersection of two lines of different slopes and no whole line wins). The conic $\rho_a$ contains that line if and only if $\rho_a = (\alpha + \zeta_i\beta + \gamma_a)(p\alpha + r\beta + s)$. The coefficient of $\beta^2$ gives $\zeta_ir = 0$, so $r = 0$; then $p = \delta_F$, $\zeta_ip = \delta_0 + \delta_1$, $\zeta_is = \delta_0$, and
$$\delta^a_G = s\,\gamma_a, \qquad e_a = (p + s)\,\gamma_a + s .$$
So $p$ and $s$ are common to all members whose line wins, and since $\gamma_a$ is an affine function of $g_a$ with slope $t$, both $\langle W_0, G_a\rangle$ and $\langle W_1, G_a\rangle$ are affine functions of $g_a$ on that set: (a). If one line wins then $\zeta_i^2\delta_F + \zeta_i(\delta_0 + \delta_1) = 0$, which is the coefficient of $\beta^2$ of every $\rho_b$ restricted to a line of slope $\zeta_i$; the restriction is then affine in $\beta$ and has at most one root unless it vanishes. For (b) solve: $st = m$, $(p + s)t = m'$, $v_G = c + s(\theta' + tu)$, and the constant term of the second relation, $\langle W_0, F\rangle + c' + \sigma = (p + s)(\theta' + tu) + s$, which reads $t = (m'\theta' + m)/(\langle W_0, F\rangle + c' + \sigma + m'u)$; the two conditions make $t$ a nonzero field element, and $\varphi_i, v_G, v_F, \sigma_0, \sigma_1$ follow. (c): for one low part $\delta^a_G$ and $e_a$ do not depend on $a$ while the $\gamma_a$ are distinct, so as soon as two lines win the two displayed relations force $s = 0$, $p = 0$ and $e_a = 0$; conversely a true claim and the honest round message make every $\rho_a$ vanish identically. (d): two members of the family agree with each other only where $\Delta$ vanishes, so their agreement sets with $O$ share only the $z$ common columns and are otherwise disjoint: $k(A - z) \le n - z$. $\square$

At the point $\zeta_i = 0$ (probability $1/q$) the factor $r$ is free and a third line can be aligned.

**[checked]** `20_attacks.py`, exact maximum over all $q^5$ prover messages $(v_G, v_F, \sigma_0, \sigma_1, \varphi_i)$ at $q = 16$, each optimum confirmed by brute force over all challenges from the definitions of (p) and (w): members in general position with a false claim, $2q + (k - 2) = 33, 34, 35$ for $k = 3, 4, 5$ (and 33 for $k = 3$ with three points); members on one affine line with a false claim, $kq = 64$ for $k = 4$ and $96$ for $k = 6$ with three points; one low part, $kq = 64$ with a true claim and $q + k - 1 = 19$ with a false one; $\zeta_i = 0$, $3q = 48$.

What this changes. Nothing in Theorem D': a family on an affine line has fewer than $2^9$ members unless $A - d \le (n - d)/2^9$, so its $kq$ wins are below $K_0$; where they are not, the points are in $\mathrm{Exc}$ by Proposition R1. It does change the reading of note 16's floor: the fold transition of the state function of notes 11 and 14 has error $k/q$ at such points for a claim that is false for every member and a weight the prover does not control, so the floor is not an artifact of the zero weight. And it is the cheapest path against a protocol with few points (section 5.2).

## 3. Theorem D', line by line

### 3.1 The checklist

Every row is **[proved]** in note 14 and was re-derived here; the last column says what the check consisted of.

| item of note 14 | verdict | what I verified |
| --- | --- | --- |
| Lemma E (E1 to E4), $\epsilon$ | correct | exponents $e_j(u)$ distinct, total degree $\Delta + 2^\ell - 2^j$; both uses are within $\epsilon$: degree $d$ at $j = 0$, degree $d + 1$ at $j \ge 1$ |
| completeness (1.4) | correct | the update $v \leftarrow v + (\theta^{2^{j-1}} + \alpha + \beta\zeta)\varphi$ from (E2), (E3); the conversion from the novel-basis identity $\mathcal X_{2^\kappa + s} = \widehat W_\kappa\mathcal X_s$, which needs (S1) |
| L1 (a) to (d) | correct | $Q = (a_1 + a_2)(G + a_3F + P_3)$; $\sum L_k = \sum L_ka_k = 0$ in characteristic two; the count of non-coclass triples |
| L2 (a) to (c) | correct | the denominator divides a nonzero polynomial of degree at most one; for several lanes the scalar $a_c(x)$ is still determined at a column outside $Z$ because the vector $(F + O_0)(x)$ is nonzero there |
| Lemma F(1) | correct | $\mathcal T$ is fixed before the points; $\mathbb E[N] \le |\mathcal T|^3\epsilon^s$; Markov |
| Lemma F(2) | correct | the case split is exhaustive (rational, degree $\ge d$, $|Z| \le A - 2$, near pair with a missed answer, near pair matching all answers); the residual of (w) has constant term $\delta_G$ and $\alpha$-coefficient $\delta_G + \sigma^\ast + \sigma$, matching Annex B's update; the residual restricted to lines was also cross-checked numerically against the definitions (`20_attacks.py`) |
| Lemma P | correct | section 2.2 |
| Lemma T | correct | section 3.2 |
| state function, properties (i), (ii), (iv) | correct | section 3.2 |
| M0 | correct | union of Lemma P and Lemma T(a); for $i \ge 1$ the old condition does not involve the new points |
| M1 | correct | one candidate, a polynomial of degree at most $J_0 - 1$ in $\lambda_0$; no union over the list because the point claims are not batched |
| M2 | correct | $A - 1 = A^{(i,j-1)}$; (p) and (w) are the new claims; Lemma T(b) twice |
| M3 | correct | section 3.4 |
| M4, M5 | correct | the point check of step 3 is used and is necessary |
| boundary cases (4.4) | correct | section 3.3 for level 0; degree slack is handled by L2(b), which puts a member whose first half has degree $d$ on a line $\beta = \text{const}$ |
| Theorem K, Corollary K2 | correct | section 3.5 |
| section 6 (interface) | consistent with Annex A, section 08 and the two Lean definitions I read | section 3.6 |
| Theorem I | correct | Facts 1 to 4, monotonicity of $N$, the four special cases $1, L, 2L - 1, L^2 + L - 1$ |
| Proposition R2' | correct | a uniform $K$-linear map sends a nonzero vector to zero with probability $|K|^{-s}$; the two inequalities |
| numbers (7.4, 8) | reproduced | `20_params.py`: the closed forms $3b + 1062$ and $3b + 824$, the counts for $b = 40, 100$, $t_0 = 168, 160, 77$, the grinds |

### 3.2 The state function and the potential

The suspicion was that $T_k$, which is an expectation over challenges not yet drawn, is not a legitimate part of a round-by-round state. It is. **[proved]**

- *Determined by the transcript.* $\pi^{(k)}_j$ is a function of the committed word $O$, the points and $c_1, \dots, c_k$: the folds of $O$ do not involve any prover message, and $\mathrm{Exc}_j$ of a word is a set of point tuples defined from the word alone. The probability in its definition is over uniform challenges, a deterministic quantity. Definition `def:rbr` allows an invariant that is not efficiently computable.
- *Survives prover messages.* For the same reason: after the commitment no prover message enters $T_k$. The part $(\mathrm I_{i,j})$ involves $\sigma^{(i,j)}$ and $v^{(i,j)}_m$, which are fixed by the prover's message *before* the challenge of round $j$, so the condition attached to a verifier message is a function of the transcript up to that message.
- *Conditional expectations.* $\mathbb E_{c_k}[\pi^{(k)}_j] = \pi^{(k-1)}_j$ is the tower property for a uniform $c_k$ independent of the past, which is the round-by-round model. In (a), exchanging $\mathbb E_{\mathbf z}$ and $\mathbb E_c$ needs $\mathbf z$ independent of the later challenges and Lemma F(1) for each fixed folded word, uniformly in the word: this is why $\mathrm{ListBound}_i$ is stated for every lane count $m \le \ell_i$ and every word.
- *The two Markov steps.* $\Pr_{\mathbf z}[T_0 \ge 1] \le \mathbb E[T_0] \le \varepsilon_\ast\sum_{j<\ell}\tau^{-j}$; and $\mathbb E_{c_k}[T_k] = \tau(T_{k-1} - \pi^{(k-1)}_k) < \tau$ when $T_{k-1} < 1$, where $\pi^{(k-1)}_k \in \{0,1\}$ has coefficient one, so $T_{k-1} < 1$ forces $\mathbf z \notin \mathrm{Exc}_k(O^{(k-1)})$.
- *Doom at the end.* $T$ plays no role after the last fold of a level; (iv) is M4 and M5.
- *Grinding of early challenges* (note 15): a prover that redraws $c_1$ until the points are exceptional for round 2 is exactly what $\tau$ pays for. The event "$T_1 \ge 1$" has probability below $\tau = 2^{-119}$ per attempt, $2^{-126}$ after the 7-bit grind.
- *Several openings of one commitment* would be covered too: goodness of $z^{(0)}$ is a property of $(O^{(0)}, z^{(0)})$, and each opening pays its own $\tau$ per fold message. (The outer protocol opens once.)

What is not done: the formal `Spec` has not been instantiated with this state (note 14 says so). I agree that the shape fits.

### 3.3 The first fold round of level 0

**[proved]** Five facts are needed and all hold. (1) The points are sampled after the root and before any outer challenge, and goodness depends on $(O^{(0)}, z^{(0)})$ only, so it survives the whole outer protocol. (2) The claims arrive after the points and may depend on them and on the answers; Lemma F(2) is a statement for *every* weight, claim and carried values at fixed non-exceptional points, so adaptivity is harmless. (3) The list of the lemma at $j = 1$ is $\mathrm{List}(O^{(0)}; A^{(0,1)} - 1, d^{(0)}) = \mathrm{List}^{(0,0)}$, the list that Lemma P pins. (4) The folds $O^{(0)}_c$ are $E$-valued words with 32 lanes; $\Lambda = L_0$ is $\mathrm{ListBound}_0$ at $m = 5$ for $E$-valued lanes, which section 7 of note 14 reduces to $K$-valued single lanes. (5) Members of $\mathrm{List}^{(0,0)}$ have coefficients in $K$ because they agree with $K$-valued lanes on at least $d + 1$ columns of $D_0 \subseteq K$; the answers are in $E$, which is harmless.

### 3.4 The level boundary

**[proved]** The order of step 2 is what makes M3 work, and it is right: root of $O^{(i+1)}$ and $\mathbf h^{(i)}$, then the new points, then the answers, then the queries with $\lambda_{i+1}$. So the one candidate $U^\ast$ of the new list (by separation) and the polynomial $P^\ast = \mathcal P_{g^\ast} + \widehat W_{\kappa_i}H^{(i)}$ are fixed before the queries. $P^\ast$ has degree at most $d^{(i)}$ and low part $g^\ast$ by (S1). If $P^\ast \in \mathrm{List}^{(i,\ell_i)}$, the old invariant gives a violated residual claim or a violated point claim $P^\ast(\zeta_m) \ne v_m$, and adding $\widehat W_{\kappa_i}(\zeta_m)H^{(i)}(\zeta_m)$ to both sides turns the latter into a violated converted claim on $g^\ast$, because $\mathcal P_g(\zeta) = \langle W_{i,\zeta}, g\rangle$ is a polynomial identity valid at every $\zeta \in E$. If not, a query lands on a disagreement except with probability $((A_i - 1)/n_i)^{t_i}$, and the same correction turns it into a violated query claim. The $1 + s_i + t_i$ claims carry the distinct powers $0, \dots, s_i + t_i$ of an independent $\lambda_{i+1}$; repeated query positions do not matter. A tuple $U^\ast$ with a nonzero high part is covered: the batched claim sees $g^\ast$ only, and the new point claims, which see all of $U^\ast$, are only used to single $U^\ast$ out. Every other member of the new list violates a new point claim and needs no union.

*The last level.* **[proved]** The polynomial sent has degree at most $d^{(I-1)}$ by its coefficient count ($2^{\nu_I} + \ell$ novel-basis coefficients). If it lies in the last list, the invariant gives a carried claim $P(\zeta_m) \ne v_m$, which the point check of step 3 rejects, or a violated running claim, which the tail sumcheck carries to the terminal check; if it does not, a query fails except with probability $((A_{I-1} - 1)/n_{I-1})^{t_{I-1}}$. Without the point check a member of the last list that satisfies the running claim and violates a point claim would be accepted, so the check is part of the protocol and not an optimisation.

### 3.5 Knowledge soundness and the extractor

**[proved]**, with one clarification of wording.

- The relativised lemma is right: in the last case of Lemma F(2) the pair $U$ that explains a class with more than $\binom n2$ chosen elements is a near tuple of one of them (L2(c)), clause (b) for that element gives $B(U)$, and the hypothesis then applies. For a list member of a fold, clause (b) is the pull-back predicate.
- The relativised transitions M1 to M4 have the same counts, because the only change is which members the invariant quantifies over.
- The descent is right: $\neg(\mathrm{pull}\,B)(P)$ contains "$P$ agrees with the folded word on at least $A^{(i,j)}$ columns" and "some near tuple fails $B$"; the near tuple on a set of at least $d + 3$ columns is unique; $A^{(i,1)} \ge d + 3$ is (S2). Across a level boundary $\neg B_{i+1,0}(T)$ is $\neg B_{i,\ell_i}(P^\ast_T)$, which again contains membership in the previous list.
- *The extractor never list-decodes.* True. Each step is decoding of one tuple with at most one error on a set the extractor has computed, which is unique decoding (a set of at least $d + 3$ columns, one error). It is led to the candidate by the final polynomial. What it needs besides the transcript is the committed words, from the hash queries, as today.
- *It outputs the pinned candidate* (Corollary K2). True, by Theorem K with $\mathrm{Bad}(U) :\iff U \ne U^\ast$ or $g_U$ violates an input claim.
- *"With the same per-message errors."* The precise statement that is proved: every verifier message preserves the relativised invariant except with the error of Theorem D' for that message, and an accepting run that preserved it at every message yields, by the descent, a list tuple that is not bad. So the probability of "accepts and the extractor's output is bad" is bounded like the probability of "accepts on false claims". This is the form the existing formal proof has, and the compilation to the non-interactive setting is inherited from it.
- A fact worth recording, which is inside the errors and not a gap: an accepted run need not have a pinned tuple. If $k \le 5$ members share their low part and the prover is off in one answer (Remark 3.4 of note 16), the run is accepted with probability about $k/q$ per fold attempt, below the fold error; it opens true claims about the common stack, and the descent returns one of the $k$ tuples. The outer protocol consumes the stack, which is the same for all of them. For members on one affine line the same can happen with a claim that is false for all of them (Proposition R3), after $s - 1$ special points and with at most $(n - d)/(A - d)$ lines: also inside the errors, and the reason the theorem cannot promise more than its fold error on a doomed state.

### 3.6 The interface

**[proved]** at the level of the statements, **[inherited]** for the outer phases. Checked against the sources:

- Section 08 of `doc/leanvm`: one commitment, one opening; the commitment's sample is the first challenge of the proof; the sixteen ring-switching scalars and $\lambda$ are one verifier message with no prover message between. So "the candidate is fixed before the first outer challenge" holds with the point answers in place of the OOD answer.
- Annex A: the soundness of the ring switch is for one fixed $K$-valued stack whose slices do not all match, with error $2/q$ over the sixteen scalars. Protocol D supplies one stack (the low part of the pinned tuple, fixed by the commit-phase answers) and it is $K$-valued (section 3.3, fact 5). The first message's error is $2/q + (J_0 - 1)/q$.
- `formal/`: `oodCands S z y` has at most one element by definition and `ringSpec` charges $L_0 \cdot 2/|E|$ for a set of at most $L_0$ candidates, as note 14 reports. The substitution `ptCands` for `oodCands` is a change of which predicate singles the candidate out, not of what the phases consume.
- The stacked opening: claims on the stack are weighted claims on low parts and are untouched; the point claims are not weighted claims and never join the pool; zero (padding) lanes contribute zero to $\mathrm{ev}$ and are forced to the zero polynomial in every list member.

What I did not do: re-prove any outer phase, or check that every outer phase is in fact charged per candidate of the set it is given (note 14 lists this as inherited; I read only the ring switch).

## 4. The ladder

**Lemma S and Theorem D$_S$ of note 15 are correct. [proved]** I re-derived them with note 14's constant. Let $\sigma_j := s_1 + \dots + s_j$, let $N_j$ be the triple count of round $j$ for the word $O^{(j-1)}$ and all $\sigma_j$ points held at round $j$, and after each verifier message $t$ of the level put
$$T(t) := \sum_{j \text{ not yet started}}\frac{\mathbb E[N_j \mid \text{verifier messages up to } t]}{\Theta\,\tau^{\,n_j(t)}},$$
with $n_j(t)$ the number of fold-challenge messages after $t$ and before round $j$. The points that matter:

- $N_j$ is a function of the committed word, $c_1, \dots, c_{j-1}$ and batches $1, \dots, j$; no prover message enters, so the conditional expectation is well defined and is a martingale in $t$.
- For fixed $c_1, \dots, c_{j-1}$ all $\sigma_j$ points are uniform and independent of $\mathcal T(O^{(j-1)})$, whatever message they were drawn in, so $\mathbb E[N_j] \le L^3q^6\epsilon^{\sigma_j}$. A fresh point of batch $b \le j$ is used at round $j$ through $\mathrm{ev}^{(j)}$ of a tuple of degree at most $d + 1$, within $\epsilon$.
- (a) Markov at the batch-1 message: $\Pr[T \ge 1] \le (L^3q^6/\Theta)\sum_{j=1}^{\ell}\tau^{-(j-1)}\epsilon^{\sigma_j}$. (b) The message $(c_j, \text{batch } j{+}1)$ is one uniform draw; every remaining term keeps its conditional mean and gains a factor $\tau$: $\mathbb E[T_{\text{after}}] \le \tau\,T_{\text{before}}$. (c) Before round $j$ the term $j$ is $N_j/\Theta$ with $n_j = 0$, so $T < 1$ gives $N_j < \Theta$: the points held are not exceptional.
- The claim part: after $(c_j, \text{batch } j{+}1)$ the condition is "no member of $\mathrm{List}^{(i,j)}$ satisfies the running claim and the point claims of batches $1..j$". The answers to batch $j + 1$ add claims and can only shrink the set of members satisfying all claims, so the hypothesis of Lemma F(2) for round $j + 1$ with all $\sigma_{j+1}$ points holds. Pinning is needed only at level entry, with batch 1.
- The level exit converts all $\sigma_\ell$ claims; the query message has $(\sigma_{\ell_i} + t_i)/q$.

Why a top-up of a single point is enough although it rides a 7-bit grind: the fresh point is not asked to make round $j + 1$ safe by itself. By (b) and (c) the old points already are, with probability $1 - \tau$; the fresh points are what made the *expectation* at the batch-1 message small. The condition $T < 1$ after batch 1 is a strong statement about all future draws, and it is charged once, to the 15-bit-ground batch-1 message.

**[checked]**, new: `20_ladder_toy.py` runs the ladder end to end on note 11's two-level toy (schedules $2{+}1{+}2$ and $1{+}2$, the level boundary with all carried claims converted and batched with the queries, the final point checks, the tail and the unrolled terminal weight): 20 honest runs, 2020 identities; ten kinds of altered values, among them an answer of a batch introduced at round 2 or 3 and a $\varphi$ of a late point, rejected in 20 of 20 runs each. This closes the item "not run end to end" of note 15 at the level of the algebra (still no Merkle tree and no sponge).

**Construction N1 of note 15 is correct. [proved]** (re-derived): the fold of $U_1 + R_0(0, D_i, 0, D'_i)$ by $c_1$ is the pair $(F^\ast, G_i)$ with $G_i - G_{i'} = R_0(\Delta D' + a_{c_1}\Delta D)$, so with $s - 1$ points at roots of $R_0$ the two folds share every round-2 answer exactly on the line $a_{c_1}(\zeta_1) = \Delta D'(\zeta_1)/\Delta D(\zeta_1)$, and then the block holds two full classes and $N \ge \Theta$. So for the set $\mathrm{E_N}$ the reuse of points does cost about one point per reused round, the Markov step of Lemma T cannot be improved in general, and the bound of Lemma T(a) is consistent with it for the same reason as in Corollary R2. It is not an attack (two colliding members win $4q$ challenges, section 5.2).

The ladder dominates the single batch on every count (same number of points, fewer scalars, less prover work) and adds no message, no grind and no error term. It survives, and the final statement is written for it; one batch is the schedule $s_2 = \dots = s_\ell = 0$.

## 5. Attacks

Model: note 03, Lemma P (paths). A path costs at least its most expensive event $2^{g}/p$ and at most the sum; every path that ends in an accepted false claim contains the query message of some level against a word at agreement $T$, cost $2^{17}(n/T)^t$, so only lists at agreement above the threshold are usable, and what has to be found is a *cheap* non-query event.

### 5.1 Fold-round counts on toys

`20_attacks.py`. Candidates are given explicitly (folds of members $(F, G_a)$ with a common first half, or pole lines), weights on the low part, and winning challenges are counted by brute force from the definitions (p) and (w). **[checked]**

| experiment | field, $k$, $s$ | prover | winning challenges | reading |
| --- | --- | --- | --- | --- |
| X1, no point claims (today's round shape), false claim for all members | $q = 256$, $k = 5$ | honest for the common $F$ | 1280 = $kq$ | the list attack of note 03 |
| X2, $s$ generic points answered for member 1, false claim | $q = 256$, $k = 5$, $s = 1, 2, 3$ | the same message | 256 = $q$ each | the point claims kill the other members |
| X3, clique: all $s$ points at roots of $R$, members $U_1 + RH_a$ | $q = 256$, $k = 5$, $s = 1, 2, 3$ | the same message | 1280 = $kq$ each | all members share every answer; probability $(r/q)^s$ |
| X4a, note 16: $s - 1$ points at roots, one answer off, zero weight | $q = 256$, $k = 5$, $s = 2, 3$ | Proposition 3.1 | 1280 = $kq$ | Proposition 3.1 |
| X4b, the same, random weight, claim false for every member, members in general position | $q = 16$, $k = 3, 4, 5$ ($s = 2$); $k = 3$ ($s = 3$) | exact maximum over all $q^5$ messages | 33, 34, 35; 33 | $2q + (k - 2)$: two lines (R3) |
| X4b', the same with $\zeta_i = 0$ | $q = 16$, $k = 4$ | exact maximum | 48 = $3q$ | the degenerate point |
| X4e, the same, members on one affine line $G + h_a\Delta$ | $q = 16$, $k = 4$ ($s = 2$), $k = 6$ ($s = 3$) | exact maximum | 64 = $kq$, 96 = $kq$ | all lines, with a false claim (R3) |
| X4c, members with one low part, claim true for it | $q = 16$, $k = 4$ | exact maximum | 64 = $kq$ | an accepted run opens a true claim |
| X4d, members with one low part, claim false | $q = 16$, $k = 4$ | exact maximum | 19 = $q + k - 1$ | one line |
| X5, four pole lines sharing both answers (both points at roots), random weight | $q = 16$, 12 instances | exact maximum over all $q^4$ messages | 19 in 8 instances, 34 in 4 | one line; a second needs a coincidence of probability about $1/q$ per pair |

So the unbatched point claims do what they are for (X1 against X2), the two exceptional mechanisms are real and have the stated probabilities (X3, X4), a claim that is false for every member does not stop the lines of a family on an affine line (X4e), and unexplained lines do not add up (X5).

### 5.2 The paths, at real size

Level 0 of the $\mu = 30$ ladder, deployed grinds. "Wait" is the cost of obtaining special points, "escape" of winning the fold round. **[proved]** as costs of the strategies described (the escape probabilities are those of section 5.1 and of the lemmas cited); `20_params.py`, table P5.

| strategy | needs | wait ($\log_2$) | escape ($\log_2$) | verdict |
| --- | --- | --- | --- | --- |
| list switching as in note 03, section 3.3 | a list above the threshold | 0 | $7 + 2\cdot128 - \log_2 L$ for $s \ge 2$ | dead: a member that misses $s \ge 2$ answers at distinct $\zeta$ wins at most one challenge |
| clique through points in $D$: flats, rate 1/4, threshold below $n/2$, uniform points | all $s$ points in $D$; then $2^{26-s}$ flats share every answer and each wins its own line | $15 + 102s$ | $7 + 128 - (26 - s)$ | **real for $s = 1$: $2^{117}$.** $2^{219}$ for $s = 2$ |
| clique through a common factor: members $U_1 + RH_a$ | $2^{11}$ members at degree $d - r$ above the threshold; all $s$ points at roots of $R$ | $15 + s\log_2(q/r) \ge 15 + 104s$ | $124$ | real for $s = 1$ if such a list exists ($2^{124}$ at $r = d/4$); dead for $s \ge 2$ |
| note 16's lines, members in general position, false claim | $s - 1$ special points | $15 + 104(s - 1) - \log_2 s$ | $7 + 127$ | dead at every $s$: two lines (X4b), probability about $2/q$, what one member gives anyway |
| the same with $k$ members on one affine line $G + h_a\Delta$, false claim | $s - 1$ points at roots of $\Delta$; $k \le (n - d)/(A - d)$ | $15 + 104(s - 1) - \log_2 s$ | $7 + 128 - \log_2 k$ | the cheapest path against few points. $k \le 15$ at the thresholds of interest: $2^{131}$, dead. Real for $s \le 2$ ($2^{124}$) only if $k \ge 2^{11}$, that is $A - d \le (n - d)/2^{11}$, a threshold within $2^{-11}(n/d - 1)$ of capacity; at levels 2 and deeper the wait alone is above $2^{125}$ for $s = 2$ |
| the same with members that share their low part | as above | as above | $7 + 128 - \log_2 k$ if the claim is true for the common stack | not an attack: the claims opened are true for a stack fixed at commitment time (X4c); with a false claim X4d |
| pole lines: $N$ lines of unexplained close codewords sharing all answers | a degree-$(d+1)$ list; all $s$ points at common roots | $15 + 104s$ | $7 + 128$ | dead: one line (X5) |
| nesting (Construction N1 of note 15): grind $c_1$ onto a line after $s - 1$ special points | members colliding after the fold | $15 + 104(s-1)$, then $7 + 128 - \log_2(\text{lines})$ | $7 + 127 - \log_2(\text{clique})$ | dead unless at least $2^{10}$ members collide on each of many lines; every family I can build has one line per clique (for instance members $U_1 + \lambda_iR_0V$ with one $V$ all collide on one line, and by R3(d) a list holds at most $(n - d)/(A - d)$ of them) |
| batching $\lambda_0$ with the ring switch | nothing | 0 | $7 + 128 - \log_2 513 = 126.0$ | the proved bound, tight up to the number of roots |
| queries against a word at agreement $A_0 - 1$ | nothing | 0 | $125$ | the baseline of every level |

Against the proved point counts (12 or $6{+}1{+}1{+}2{+}1{+}1$ at level 0, at least 5 after the commitment at every later level) every path that uses special points costs more than $2^{15 + 104\cdot4}$, and the theorem bounds every other non-query event by $2^{-125}$ after its grind. Against a hypothetical protocol with fewer points: one point is broken; two are not broken by anything above at any threshold with $(n - d)/(A - d) < 2^{10}$. The ladder adds no path: its top-up points ride the fold challenge, and spoiling one (probability $n/q$ or $r/q$, cost about $2^{107}$ to $2^{111}$ under the 7-bit grind) leaves the round with the points it had, which under the proved schedule are sufficient by Lemma S; a sharpened schedule in which a single top-up is the margin of a round would have to count this event at $2^{-100}$ against the fold message.

### 5.3 What I tried and what it showed

- *Words with several members that agree at all but one point* (note 16). This is a real feature of the state function, it survives a real claim for families on an affine line (Proposition R3, X4e), and it is not an attack at the proved point counts, nor with two points at any threshold of interest: such families are too small.
- *Points landing in $D$.* A point in $D$ is a query: every member that agrees with the word at that column shares its answer. This breaks $s = 1$ and nothing else.
- *Degree slack.* A member whose first half has degree $d$ folds out of the degree bound except on a line of challenges (L2(b)); members with the slack in the second half are ordinary members of the list at degree $d$, which is the degree of the hypothesis. No gain. Members that differ only in the slack share every weighted claim and are the family of X4c.
- *Interaction between levels.* A next-level word with a large list is pinned by its own points before the queries; its other members violate a new point claim, and the pinned one is tied to the previous level by the queries or by the old invariant (section 3.4). I found no way to use a list of level $i + 1$ against the claims of level $i$ other than the batching escape $(s_i + t_i)/q$.
- *Grinding of early challenges.* Section 5.2, nesting.
- *The known list families.* Flats (the hyperplane lists) at rate 1/4 are usable through points in $D$ only, and only for $s = 1$: the difference of two members is $(L_V - L_{V'})/X$, a linearized polynomial of degree $2^\kappa$ over $X$ whose roots are exactly $V \cap V' \subseteq D$ (**[proved]**), so a point outside $D$ separates every pair of flats. The $5n/8$ family at rate 1/2 consists of unions of flats; through a point of $D$ it gives the same clique attack on $s = 1$ (about $2^{118}$, when the threshold is far enough below $5n/8$ for the queries to be cheap, for example $t_0 = 131$), and I see no common factor outside $D$ and no use beyond list switching, which is dead for $s \ge 2$.

## 6. The final statement

### 6.1 Protocol D$_S$

Annex B's protocol (`fig:protocol`) with these changes, and no multilinear out-of-domain claim. Parameters: per level $i$ the shape $\kappa_i, \ell_i, R_i$, $n_i = 2^{\kappa_i + R_i}$, $D_i \subseteq K$, a threshold $A_i$, queries $t_i$, and a schedule $s^{(i)}_1 \ge 1$, $s^{(i)}_2, \dots, s^{(i)}_{\ell_i} \ge 0$ with $\sigma^{(i)}_j := s^{(i)}_1 + \dots + s^{(i)}_j$. Grinds: 15 bits before a batch-1 point message, 7 before the first opening message, 7 before a fold message, 17 before a query message.

1. *Commit.* The prover sends the root of $O^{(0)}$. The verifier sends $s^{(0)}_1$ points $z_m = (\theta_m, \zeta_m) \leftarrow E^2$ in one message; the prover answers $y_m = \mathrm{ev}^{(0)}_{z_m}(P^{(0,0)}) = \sum_u\theta_m^{e(u)}P^{(0,0)}_u(\zeta_m)$, $e(u) = \sum_k(1 - u_k)2^{k-1}$. These are the level's first carried claims $v_m := y_m$; they are never batched into the weighted claims.
2. *Open.* The verifier sends the sixteen ring-switching scalars and $\lambda_0$ in one message; the running claim is the batch of the $J_0 \le 512$ weighted claims.
3. *Fold round $j$ of level $i$.* The prover sends the answers $y = \mathrm{ev}^{(j-1)}_z(P^{(i,j-1)})$ to the points of batch $j$ if $j \ge 2$ and $s^{(i)}_j > 0$ (they become carried claims $v := y$), then $v_G, v_F, \sigma_0, \sigma_1$ as today, then $\varphi_m = \mathrm{ev}^{(j)}_{z_m}(F^{(i,j)})$ for every point held. The verifier sends $(\alpha, \beta) \leftarrow E^2$ and, in the same message, the $s^{(i)}_{j+1}$ points of batch $j + 1$ if $j < \ell_i$. Both update the running claim as today and every carried value by $v_m \leftarrow v_m + (\theta_m^{2^{j-1}} + \alpha + \beta\zeta_m)\varphi_m$.
4. *Level boundary* ($i < I - 1$). The prover sends the root of $O^{(i+1)}$ and $\mathbf h^{(i)}$. The verifier sends the $s^{(i+1)}_1$ points of the new commitment; the prover answers them. The verifier sends the $t_i$ queries and $\lambda_{i+1}$ in one message. Each carried claim of level $i$ is converted, $c'_m := v_m + \widehat W_{\kappa_i}(\zeta_m)H^{(i)}(\zeta_m)$ with weight $W_{i,\zeta_m}$, and the $1 + \sigma^{(i)}_{\ell_i} + t_i$ claims (residual, converted points, queries) are batched with the distinct powers of $\lambda_{i+1}$.
5. *Last level.* The prover sends the final polynomial $P$; the verifier checks $P(\zeta_m) = v_m$ for every carried claim, samples and checks the queries, and runs the tail sumcheck and the terminal check, whose weight contains the converted point claims of the earlier levels.

Protocol D of note 14 is the schedule $s_2 = \dots = s_\ell = 0$. Completeness is perfect. **[proved]**, **[checked]** on toys (`11_protocol_toy.py`, `15_batch_toy.py`, `20_ladder_toy.py`).

### 6.2 Hypothesis and theorem

**Standing assumptions.** $1 \le \ell_i \le 2^{\kappa_i}$; $d^{(i)} + 2 \le A^{(i,0)}$ and $A_i \le n_i$; $\binom{n_i}{2} \le 2q$; $K_0 > 2q$ an integer and $0 < \tau < 1$ (analysis constants). All hold on every deployed ladder.

**Hypothesis $\mathrm{ListBound}_i(L_i)$**, for each level: every interleaved word $\{0,1\}^m \times D_i \to E$, $0 \le m \le \ell_i$, has at most $L_i$ polynomial tuples of degree at most $d^{(i)}$ agreeing with it on at least $A^{(i,0)} = A_i - \ell_i$ columns. It holds unconditionally with the Johnson count when $(A^{(i,0)})^2 > n_id^{(i)}$ and with the counting bound. It follows from a bound $L$ for single-lane words over $K$ at the same $(A^{(i,0)}, d^{(i)})$ with $L_i = L$ if $A^{(i,0)} > (n_i + 2d^{(i)})/3$, $L_i = 2L - 1$ if $A^{(i,0)} > (n_i + 3d^{(i)})/4$, $L_i = \lfloor L/(1 - L/2^{64})\rfloor$ if $L \le 2^{62}$, and $N_{L,g}(n_i - d^{(i)})$ in general (Theorem I, Proposition R2' of note 14, **[proved]**).

**Theorem (final form). [proved]** by notes 14 and 15 as refereed here; nothing is machine-checked. Under the standing assumptions and $\mathrm{ListBound}_i(L_i)$ for every level, call the input claims false if no tuple of $\mathrm{List}(O^{(0)}; A^{(0,0)}, d^{(0)})$ matches all commit-phase answers and satisfies every weighted claim. Then Protocol D$_S$ is round-by-round sound with the errors below, and round-by-round knowledge sound with the same errors for the straight-line descent extractor (unique decoding of one error on known sets, no list decoding, polynomial time), which on an accepted run that escaped no message outputs a list tuple satisfying every input claim, namely the one pinned by the commit-phase answers; that tuple is over $K$, is fixed before the first outer challenge, and its low part is the candidate stack of the outer protocol.

| verifier message | round-by-round error | grind | after the grind, at the choices of 6.3 |
| --- | --- | --- | --- |
| batch-1 points of level $i$ | $\binom{L_i}{2}\epsilon_i^{\sigma_1} + \dfrac{L_i^3q^6}{\Theta}\sum_{j=1}^{\ell_i}\tau^{-(j-1)}\epsilon_i^{\sigma_j}$ (one batch: $\bigl[\binom{L_i}{2} + \frac{L_i^3q^6}{\Theta}\sum_{j<\ell_i}\tau^{-j}\bigr]\epsilon_i^{s_i}$) | 15 | at most $2^{-125}$ by the choice of the schedule |
| ring switch and $\lambda_0$ | $(J_0 + 1)/q$ | 7 | $2^{-125.997}$ at $J_0 = 512$ |
| fold challenge of round $j$ (with batch $j + 1$) | $(K_0 - 1)/q^2 + \tau$; no $\tau$ at $j = \ell_i$ | 7 | $2^{-125.000}$ and $2^{-126.000}$ at $K_0 = 2^9q$, $\tau = 2^{-119}$ |
| queries of level $i$ with $\lambda_{i+1}$ | $((A_i - 1)/n_i)^{t_i} + (\sigma^{(i)}_{\ell_i} + t_i)/q$; no second term at the last level | 17 | at most $2^{-125}$ by the choice of $t_i$ |
| tail round | $2/q$ | 0 | $2^{-127}$ |

No list size multiplies a term of order $1/q$, and neither the Johnson hypothesis nor the affine MCA error appears. Unchanged from note 14 and note 15; the term $s\binom L2\epsilon^{s-1}$ of note 16 is not needed (section 2).

### 6.3 Points per level at $\mu = 30$

Levels $(\kappa_i, \ell_i) = (24,6), (20,4), (16,4), (12,4), (8,4), (4,4)$ (`derive_config(30, R)` for every $R$; the rate enters only through $\binom{n_i}{2} \le 2q$), $\log_2(1/\epsilon_i) = 104.0, 108.0, 112.0, 116.0, 119.9, 122.9$, $K_0 = 2^9q$, $\tau = 2^{-119}$, point budget $2^{-110}$. **[checked]** exact rational arithmetic, `20_params.py` tables P1 and P2, written independently and equal to the numbers of notes 14, 15 and 16.

| list budget at every level | one batch (Protocol D), $s_i$ | scalars | ladder, batches per level | scalars | points after the commitment |
| --- | --- | --- | --- | --- | --- |
| $2^{40}$ | 12, 9, 9, 9, 8, 8 | 299 | $6{+}1{+}1{+}2{+}1{+}1$; $6{+}1{+}1{+}1$ (three levels); $5{+}1{+}1{+}1$ (two levels) | 251 | 6, 6, 6, 6, 5, 5 |
| $2^{100}$ | 14, 11, 11, 10, 10, 10 | 358 | $8{+}1{+}1{+}1{+}1{+}2$; $8{+}1{+}1{+}1$; $7{+}1{+}1{+}2$; $7{+}1{+}1{+}1$ (three levels) | 305 | 8, 8, 7, 7, 7, 7 |

The total number of points per level is the same in both designs. The point message's error at these choices is between $2^{-113}$ and $2^{-218}$ before the grind (the smallest margin is 3 bits, at $\kappa = 16$, $2^{100}$, ladder). Queries: $t_i = \lceil 108/\log_2(n_i/(A_i - 1))\rceil$ up to one; at level 0, 168 at $(A_0 - 1)/n = 0.64$ and 160 at $5/8$ (rate 1/2), 77 at $3/8$ (rate 1/4), against 218 and 109 deployed.

What the hypothesis must be for these numbers to mean anything: $\mathrm{ListBound}_0$ at the lowered threshold, and at each later level either its own $\mathrm{ListBound}_i$ or the Johnson threshold (then $L_i \le 2^7$ and the level needs 11, 8, 8, 8, 8, 7 points in one batch).

## 7. Residual gaps

| # | gap | severity | status |
| --- | --- | --- | --- |
| 1 | $\mathrm{ListBound}$ beyond the Johnson radius on the real domain | critical: without it the theorem says nothing new about query counts | **[conjectured]**; not touched here |
| 2 | Nothing is machine-checked. Lemmas E, L1, L2, F, P, T, S, Theorems D', D$_S$, K, I, Proposition R2' are hand proofs, now with three independent derivations of the central lemma and two of everything else | high | this note adds a second referee, not a formal proof |
| 3 | The round-by-round state with the potential has not been instantiated in the formal `Spec`, and the Fiat-Shamir compilation is inherited | high for deployment, low for the mathematics (the state is a function of the transcript; section 3.2) | open |
| 4 | The outer phases are assumed to consume only "at most one $K$-valued candidate stack, fixed before the first outer challenge". Read for the ring switch only | medium | **[inherited]** |
| 5 | The proof's two losses. $q^3$ (unexplained close codewords) and $\tau^{-(\ell-1)}$ (reuse of points): 12 points at level 0 where the state function's floor is 3 and the best attack breaks 1. Removing the first needs a bound on the unexplained mass (hypothesis $\mathrm U$ of note 16), the second a structure theorem for prefixes (Conjecture C of note 15) | medium: cost only (prover passes, scalars, guest cycles), no soundness consequence | open; the ladder is the proved mitigation |
| 6 | The ladder has been run on toys for its algebra only: no Merkle tree, no sponge, no guest implementation, no timing | medium | open |
| 7 | Where the single-lane list exceeds $2^{62}$ and $A \le (n + 3d)/4$ the reduction to $K$-valued words loses a power; the hypothesis must then be stated for $E$-valued words | low | note 14, section 7.3 |
| 8 | Whether a second point really is enough (no attack with $s = 2$ is known away from capacity-edge thresholds; no proof below 12) | low for the protocol as specified, which does not rely on it | open |
| 9 | Recursion across levels: the formal statement about the guest is for one node | unchanged by Protocol D | **[inherited]** |
| 10 | Costs are counts, not measurements | low | open |

## 8. Reproduction

- `cc -O2 -Wall -Wextra -o lines20 doc/whir_soundness_gap_notes/scripts/20_lines.c -lpthread`, then `./lines20 word=kpairs seed=20 threads=3` (the table of section 2.3; about 22 CPU-minutes, so 8 minutes on three idle threads) and `./lines20 word=random seed=20 threads=3` (about 8 CPU-minutes). Builds without warnings. Blocks with fewer than 100 elements are not examined, which is why the last column of the table has a floor.
- `python3 doc/whir_soundness_gap_notes/scripts/20_attacks.py [seed]`: section 5.1 and the check of Proposition R3 (about two minutes of one thread, standard library). The first draft of this script built $\mathrm{GF}(2^8)$ with the modulus $x^8 + x^4 + x^3 + x + 1$, for which $x$ is not a generator, so its log tables were wrong; the run printed impossible counts (27 wins where $kq = 1280$ is forced) and was discarded. The modulus is now $x^8 + x^4 + x^3 + x^2 + 1$ and the constructor asserts primitivity. No number of this note comes from the faulty run. Likewise an early draft let the free point be $\zeta_i = 0$, which is how the degenerate case X4b' was found; the experiments now exclude it and test it separately.
- `python3 doc/whir_soundness_gap_notes/scripts/20_ladder_toy.py [seed]`: the ladder end to end (seconds).
- `python3 doc/whir_soundness_gap_notes/scripts/20_params.py`: every count and error of sections 2.2, 2.4, 5.2 and 6, with a selftest against the closed forms of note 14 (under a second).
- Reruns of earlier scripts used here: `./sharp16 m=6 N=4 d=2 A=5 word=kpairs k=3 r=2 s=2 zmode=all` (310 of 4096), `./nest15 m=5 N=4 d=3 A=6 word=n1 M=2 r=2 mode=scan s=3 pts=roots cor=3` (31 of 1024), `python3 11_protocol_toy.py`, `python3 14_extractor_toy.py`.
