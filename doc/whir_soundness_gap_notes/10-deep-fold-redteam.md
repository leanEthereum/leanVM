# 10. Red team on the DEEP fold (note 07, Theorem 3)

Researcher 10, round 2. Target: Theorem 3 and Corollary 4 of `07-protocol-redesign.md`, their use in variant P, and the two side claims of that note (the present protocol cannot be re-analysed this way; queries before the next commitment are unsound). Notation as in notes 07 and 09: $q = |E| = 2^{128}$, a level has domain $D$ of size $n$, analysis degree $d = 2^\kappa - 1 + \ell$, threshold $A$, $\ell$ fold rounds; for a challenge $c = (\alpha, \beta)$, $a_c = \alpha + \beta X$ and $w_c = f_1 + a_c f_0$; $\mathcal{L}(c)$ is the list of $w_c$ at agreement $A$ and degree $d$, $\Lambda \ge |\mathcal{L}(c)|$, $\mathcal{T}$ the set of all pairs $(c, P)$ with $P \in \mathcal{L}(c)$. Statuses: **[proved]** (proof in this note, on paper, not machine-checked), **[checked]** (numerically, sizes given), **[conjectured]**, **[heuristic]**. Scripts: `scripts/10_deep_redteam.c` (brute force, C, written from scratch, shares nothing with `07_deep_fold_check.py`), `scripts/10_run.sh` (the experiments), `scripts/10_params.py` (the parameter count).

## 0. Verdict

**Holds with corrections.** Theorem 3 and Corollary 4 of note 07 are correct as stated. I re-proved them by a different route (Theorem A below, with slightly better constants), checked every step of the original proof, and verified the conclusion exhaustively, over all answer vectors and all round messages, on toy fields where the hypotheses of Corollary 4 actually hold (they do not at the size note 07 tested). I found no attack: no word and no prover strategy wins more than $2q + O(1)$ fold challenges with a false claim on non-exceptional points, and the only exceptional point sets I can construct have probability of order $\epsilon^s$ up to $\rho^{-s}$, far inside the bound. The corrections are to the evidence and to the protocol sketch around the lemma, not to the lemma:

1. The check of note 07 ran at $q = 32$, $n = 16$, where $\binom{n}{2} = 120 > 2q$, so Corollary 4's hypothesis fails there and its conclusion was never tested. Redone at $q = 64, 128, 256$ where it holds (Section 5).
2. The point message of variant P has one more error term, $s\ell/q$, for a zero lane coordinate (the verifier divides by $r_{i,j}$), or the lane weights must change (Section 8, G5).
3. The last level must check the carried point claims on the polynomial sent in the clear. Note 07 does not say so, and without it the last level has no DEEP protection (G4).
4. Three orderings are load-bearing and unstated: all $s$ points in one verifier message, lane coordinates independent per point, and every $y^F_i$ absorbed before the fold challenge (G8).
5. `ListBound` is needed for interleaved, $E$-valued words: all $q^2$ folds of every round. A bound for single $E$-valued words implies it only for $\Lambda < 2^{64}$, and a bound for $K$-valued words only for $\Lambda < 2^{32}$ (Proposition 2.4). At budgets $2^{70}$ and $2^{100}$ the statement must be proved for interleaved words directly, or for single words over every extension field.
6. Section 3.7 of note 07 ("the present protocol cannot be re-analysed this way") is tagged [proved] but is a count of degrees of freedom, and the count is off by one (four free values, five pairs, exponent $1/5$). The conclusion stands, and the right proof is the attack: in today's round shape a list of $L$ candidates wins about $1.5\,L$ lines of challenges with one round message (Section 7).
7. The exceptional set of Theorem 3 contains "all $s$ points in $D$", of probability $(n/q)^s \approx \epsilon^s \rho^{-s}$, for every word with no close pair whose folds are mostly close to something (precisely: $|\mathcal{T}|(A/n)^s \ge K_0$). This is inside the bound, and it is the largest exceptional event I measured at every size, so it is the floor of any later sharpening unless the points are drawn outside $D$ (Section 2.3).
8. Constants: $4/K_0^3$ can be $1/(K_0(K_0-1)(K_0-2q))$, and $\Lambda q^2$ can be $|\mathcal{T}| = \sum_c |\mathcal{L}(c)|$. Neither changes a point count by more than one at one level.

What is not affected: the number of points per level (I get 12, 9, 9, 9, 8, 8 for lists of $2^{40}$, as note 07; Section 6), the fold error $K_0/q^2 + \tau \le 2^{-118}$, and the conclusion of note 09 that the only missing statement is `ListBound`.

## 1. What I checked of note 07, line by line

- **Lemma 1. [proved], correct.** $L_1 + L_2 + L_3 = 0$ and $\sum_j L_j a_{c_j} = 2(a_1a_2 + a_1a_3 + a_2a_3) = 0$ in characteristic two. (a) uses only $\mathrm{ev}_z(aP) = a(\zeta)\,\mathrm{ev}_z(P)$ for a scalar polynomial $a$, true for the lane-compressed evaluation $\sum_u \mathrm{eq}(r,u) P_u(\zeta)$. (b) needs $c_1 \ne c_2$, which the distinct challenges give.
- **Lemma 2. [proved], correct.** (i): every component of $F$ has a denominator dividing $a_c + a_{c'}$ for all pairs of the class, so one pole $x_0 \in E$ for all lanes and all challenges on the line $\alpha + x_0\beta = \mathrm{const}$. A polynomial $F$ of degree $d$ is possible only when all challenges share $\beta$, again a line. (ii): for $x \notin Z$ the equation $(G - f_1)(x) = a_c(x)(f_0 - F)(x)$ in $E^h$ forces $(f_0 - F)(x) \ne 0$ (else $x \in Z$) and fixes the scalar $a_c(x)$; two such points fix $c$. The argument is the same for one lane and for $h$ lanes. A slightly sharper count: a polynomial class whose pair agrees on $|Z| \le A - 2$ points has at most $\binom{n - |Z|}{2}$ members.
- **Theorem 3. [proved], correct**, including the constants: for $K \ge 30$, $K - K^2/(4(K-1)) \ge 0.74K$; Markov on $N$ with $\mathbb{E}[N] \le (\Lambda q^2)^3 \epsilon^s$; the consistency of $(F, G)$ with the answers needs two elements of $W'$ with different $a_c(\zeta_i)$, which $|W'| > q$ gives. The exceptional set depends on the words and the points only, never on the answers, so answers chosen after the points are covered: the statement is "for every $m$".
- **Corollary 4. [proved], correct.** The residual of a pair with $c^\ast \ne c$ is $\delta_G + \alpha(\delta_G + e) + \alpha^2\delta_F + \beta\delta_0 + \alpha\beta(\delta_0 + \delta_1)$ with $e \ne 0$, for weights that see only low parts and pairs of degrees $(d-1, d)$: the computation of `lem:fold-list` uses only linearity of $\langle W_\iota, \cdot\rangle$. At most $2q$ zeros, attained (two parallel lines $\alpha = \alpha_1, \alpha_2$ when $\delta_0 = \delta_1 = 0$): so $0.74K_0 > 2q$ is needed and $K_0 > 2q$ is necessary for any such statement.
- **"Wins" is the right event. [proved]** A challenge is counted when some $P \in \mathcal{L}(c)$ satisfies the folded running claim and all folded point claims. That is exactly the negation of the invariant after the challenge (Section 8.1), weighted claims included. Proximity alone is not what is bounded: the theorem allows every challenge to have a close codeword.
- **Hidden list dependence.** None in the fold error. $\Lambda$ enters only $\mathbb{E}[N]$, cubed, and the separation term. But $\Lambda$ must bound the list of every fold $w_c$, an arbitrary $E$-valued word with $2^{\ell - j}$ lanes at degree $d$ with its slack: correction 5.
- **Points in $D$, in $K$. [proved]** Schwartz-Zippel is over uniform $\zeta \in E$ and does not care. No term $n/q$ has to be added and no point has to be rejected. Points in $D$ are however where the exceptional set concentrates (Section 2.3). Completeness is unaffected: the weight $(\mathrm{novel}_v(\zeta))_v$ is the tensor of `lem:colweight` at any $\zeta \in E$.
- **Degree slack. [proved]** Lists before and after the fold are at the same $d$; the point claims evaluate whole polynomials, so they pin high parts too, and the honest fold is consistent exactly. The slack costs nothing but $\ell$ in $\epsilon$.
- **Numerical table of note 07, Section 3.3. [checked]** Reproduced in structure by independent code at the same size, with other random words: largest classes 60 / 304 / 32 / 32 (random, planted, pole, flats), best answer vector at two points 65 / 304 to 307 / 64 / 32, at three points 60 / 304 / 32 to 64 / 32, and 992 challenges with a close codeword for the flats pole pair.

## 2. Independent proof, constants, tightness

Setting as in note 07, Section 3.2: $D \subseteq E$, $h \ge 1$ lanes, words $f_0, f_1 : D \to E^h$, $d + 1 < A \le n$, points $z_i = (r_i, \zeta_i)$ uniform and independent in $E^{\log_2 h} \times E$, $\mathrm{ev}_z(P) = \sum_u \mathrm{eq}(r, u) P_u(\zeta)$, answers $m = (y^F_i, y^G_i)_{i \le s}$, and $(c, P)$ is $m$-consistent if $\mathrm{ev}_{z_i}(P) = y^G_i + a_c(\zeta_i) y^F_i$ for all $i$. $\epsilon := (d + 1 + \log_2 h)/q$.

### 2.1 The geometry: classes are the lines of a linear space

For two elements $e_1 = (c_1, P_1)$, $e_2 = (c_2, P_2)$ of $\mathcal{T}$ with $c_1 \ne c_2$ there is exactly one pair of rational tuples $(F, G)$ with $P_j = G + a_{c_j}F$ for $j = 1, 2$, namely $F = (P_1 + P_2)/(a_{c_1} + a_{c_2})$, $G = P_1 + a_{c_1}F$. For a rational pair $\rho = (F, G)$ let its *class* be $\mathcal{C}(\rho) := \{(c, P) \in \mathcal{T} : P = G + a_c F\}$. A class has at most one element per challenge.

**Lemma 2.1 (linear space). [proved]** (a) Two elements of $\mathcal{T}$ with different challenges lie in exactly one class. (b) Three elements with pairwise different challenges lie in one class if and only if $Q := (a_{c_2} + a_{c_3})P_1 + (a_{c_1} + a_{c_3})P_2 + (a_{c_1} + a_{c_2})P_3 = 0$. (c) If the three are $m$-consistent for one $m$, then $\mathrm{ev}_{z_i}(Q) = 0$ for all $i$. (d) For a set $W \subseteq \mathcal{T}$ of $K$ elements with pairwise different challenges, writing $k_\rho := |\mathcal{C}(\rho) \cap W|$: $\sum_{\rho : k_\rho \ge 2} k_\rho(k_\rho - 1) = K(K-1)$, and if every $k_\rho \le M$, the number of ordered triples of $W$ that are not in one class is at least $K(K-1)(K-M)$.

*Proof.* (a) Existence is the formula; if both lie in $\mathcal{C}(F', G')$ then $P_1 + P_2 = (a_{c_1} + a_{c_2})F'$, so $F' = F$ and $G' = G$. (b) Write $a_j := a_{c_j}$ and let $(F, G)$ be the pair of $e_1, e_2$. Then $(a_2 + a_3)P_1 + (a_1 + a_3)P_2 = (a_1 + a_2)G + (a_1a_2 + a_1a_3 + a_1a_2 + a_2a_3)F = (a_1 + a_2)(G + a_3F)$, so $Q = (a_1 + a_2)(P_3 + G + a_3F)$, which vanishes exactly when $e_3 \in \mathcal{C}(F, G)$. (c) $\mathrm{ev}_{z_i}(Q) = y^G_i \sum_j L_j(\zeta_i) + y^F_i \sum_j L_j(\zeta_i)a_j(\zeta_i) = 0$, the two sums being zero in characteristic two. (d) By (a) every ordered pair of $W$ is in exactly one class. The ordered triples in one class number $\sum_\rho k_\rho(k_\rho-1)(k_\rho-2) \le (M-2)\sum_\rho k_\rho(k_\rho - 1) = (M-2)K(K-1)$, out of $K(K-1)(K-2)$. $\square$

**Lemma 2.2 (size of a class). [proved]** Let $\mathcal{C} = \mathcal{C}(F, G)$. (a) If $F$ is not a polynomial tuple, all challenges of $\mathcal{C}$ lie on one line $\alpha + x_0\beta = \gamma$, so $|\mathcal{C}| \le q$. (b) If $F$ is a polynomial tuple and $\deg F = d$, all challenges of $\mathcal{C}$ share $\beta$, so $|\mathcal{C}| \le q$. (c) Otherwise $\deg F \le d - 1$, $\deg G \le d$, and with $Z := \{x \in D : F(x) = f_0(x), G(x) = f_1(x)\}$: if $|Z| \le A - 2$ then $|\mathcal{C}| \le \binom{n - |Z|}{2}$. (d) If $|Z| \ge A - 1$, that is $(F, G) \in \mathcal{L}_{\mathrm{pair}}$: the elements of $\mathcal{C}$ that are $m$-consistent are all of $\mathcal{C}$ if $\mathrm{ev}_{z_i}(F) = y^F_i$ and $\mathrm{ev}_{z_i}(G) = y^G_i$ for all $i$, and otherwise lie on a line of slope $\zeta_i$ (at most $q$); and if $\langle W_0, F\rangle + \langle W_1, G\rangle \ne c$, at most $2q$ elements of $\mathcal{C}$ satisfy the folded running claim, whatever the round message.

*Proof.* (a), (b), (c) are Lemma 2 of note 07, which I re-derived: $P_c + P_{c'} = (a_c + a_{c'})F$ is a polynomial of degree at most $d$ for all pairs of the class; a pole of $F$ divides every $a_c + a_{c'}$; a polynomial $F$ of degree $d$ forces every $a_c + a_{c'}$ to be constant; and in (c) every element has at least two agreement points outside $Z$, each of which fixes $a_c(x)$. (d) For a polynomial pair, $\mathrm{ev}_{z_i}(G + a_cF) - y^G_i - a_c(\zeta_i)y^F_i = \delta^G_i + (\alpha + \beta\zeta_i)\delta^F_i$ with $\delta_i$ the pair's error at point $i$: identically zero, or a line, or empty. The claim part is `lem:fold-list`. $\square$

### 2.2 The theorem

**Theorem A (DEEP fold, re-derived). [proved]** Let $N(z)$ be the number of ordered triples of $\mathcal{T}$ with pairwise different challenges, not in one class, with $\mathrm{ev}_{z_i}(Q) = 0$ for all $i \le s$. Then $\mathbb{E}_z[N] \le |\mathcal{T}|^3\epsilon^s \le \Lambda^3 q^6 \epsilon^s$. Let $M \ge 2$ and $K_0 > M$ be integers and call $z$ *exceptional* if $N(z) \ge K_0(K_0 - 1)(K_0 - M)$; this has probability at most
$$\varepsilon_{\mathrm{pt}} := \frac{|\mathcal{T}|^3\,\epsilon^s}{K_0(K_0-1)(K_0-M)} \le \frac{\Lambda^3 q^6\,\epsilon^s}{K_0(K_0-1)(K_0-M)} .$$
For $z$ not exceptional and every answer vector $m$: every set $W$ of $m$-consistent elements with pairwise different challenges and $|W| \ge K_0$ has a class with more than $M$ elements. Consequently:

1. (Theorem 3 of note 07.) With $M = \max(q, \binom{n}{2})$: such a $W$ contains more than $M$ elements of one pair $(F, G) \in \mathcal{L}_{\mathrm{pair}}$ that is consistent with the answers.
2. (Corollary 4 of note 07.) With $M = \max(2q, \binom{n}{2})$: if no pair of $\mathcal{L}_{\mathrm{pair}}$ that is consistent with the answers satisfies the running claim, then for every round message fewer than $K_0$ challenges have an $m$-consistent $P \in \mathcal{L}(c)$ satisfying the folded running claim.

*Proof.* $Q \ne 0$ is a tuple of degree at most $d + 1$ fixed by the triple, the points are independent of it and of each other, so each triple counted by $N$ has probability at most $\epsilon^s$ (Schwartz-Zippel in $(r, \zeta)$, total degree $d + 1 + \log_2 h$); Markov gives $\varepsilon_{\mathrm{pt}}$. Let $z$ be non-exceptional and $W$ as stated with all classes of size at most $M$. By Lemma 2.1(c) and (b) every triple of $W$ not in one class is counted by $N(z)$, and by 2.1(d) there are at least $K(K-1)(K-M) \ge K_0(K_0-1)(K_0-M)$ of them, a contradiction. For 1, a class with more than $\max(q, \binom{n}{2})$ elements is a pair of $\mathcal{L}_{\mathrm{pair}}$ by Lemma 2.2(a) to (c), and it is consistent with the answers by 2.2(d) since it has more than $q$ consistent elements. For 2, take one winning element per winning challenge. Its classes have at most $q$ elements (2.2(a), (b), and (d) for a pair not consistent with the answers), at most $\binom{n}{2}$ (2.2(c)), or at most $2q$ (2.2(d) for a consistent pair, which violates the claim by hypothesis). $\square$

Comparison with note 07. Theorem 3 there is the case $N(z) < K_0^3/4$, with the conclusion "$0.74\,|W|$ elements on one pair". Both are right. In the form $\varepsilon_{\mathrm{pt}} = C\,\Lambda^3 q^3 \epsilon^s$ with $K_0 = kq$ and $M = 2q$: note 07 has $C = 4/k^3$, Theorem A has $C = 1/(k^2(k-2))$: $0.199$ against $0.188$ at $k = 2.72$, $0.148$ against $0.111$ at $k = 3$, and a factor 4 at large $k$ (two bits out of about 1200). **So $4\Lambda^3q^6\epsilon^s/K_0^3$ is right**, and is within a factor 4 of what this method gives. **[checked]** `10_params.py`, first table.

**The best $K_0$.** The fold error is $K_0/q^2$ and the point error falls like $K_0^{-3}$, so $K_0$ should be as large as the fold message's budget allows: with the 7-bit fold grind, $K_0 \approx 2^{8.6} q$. The smallest usable value is any $K_0 > 2q$; $2.72\,q$ is a choice, not a threshold. Each doubling of $K_0$ is worth 3 bits against about 104 bits per point at level 0, so nothing depends on it.

### 2.3 Tightness

- **$K_0 > 2q$ is necessary. [proved], [checked]** A list member with a false claim wins exactly $2q$ challenges with the round message that is honest except $v_F$ shifted by $e$ (residual $e\,\alpha(1 + \alpha)$: the lines $\alpha = 0$ and $\alpha = 1$). Exhaustive search over all answer vectors and round messages: between $2q$ and $2q + 3$ at $q = 32, 64, 128$ (Section 5.2), the surplus being single challenges of other list members. So the fold error of the modified protocol is at least $2/q$, and Corollary 4 gives $(2 + \delta)/q$.
- **The factor $\epsilon^s$ is tight up to $c^s$. [proved], [checked]** (i) Take a pole pair over a word whose degree-$(d+1)$ list is $C_i = C_0 + R\,H_i$ with $R$ of degree $r$ with roots in $E \setminus D$. When all $s$ points are roots of $R$, probability $(r/q)^s$, the answers $y^F_i = 1/(\zeta_i - x_0)$, $y^G_i = C_0(\zeta_i)/(\zeta_i - x_0)$ are consistent with every line at once. Built at $q = 256$, $n = 32$, $d = 5$, $A = 10$, three members, $r = 3$: at the roots of $R$ one answer vector wins $768 = 3q > K_0 = 697$, at generic points $256 = q$ (Section 5.4). (ii) Two pairs $(F, G)$, $(F, G + RH)$ of $\mathcal{L}_{\mathrm{pair}}$: at the roots of $R$ both are consistent with one answer vector and one round message wins $256 = 4q$ challenges at $q = 64$, against $128 = 2q$ at generic points.
- **Points in $D$. [proved], [checked]** If $\zeta_1, \dots, \zeta_s \in D$, the answers $y^F_i = \mathrm{ev}_{z_i}(f_0)$, $y^G_i = \mathrm{ev}_{z_i}(f_1)$ (values of the committed words themselves) are consistent with every $(c, P)$ such that $P$ agrees with $w_c$ at $\zeta_1, \dots, \zeta_s$, because then $\mathrm{ev}_{z_i}(P) = \mathrm{ev}_{z_i}(w_c)$. That is about a fraction $(A/n)^s$ of $\mathcal{T}$, in no particular class. So for every word with no close pair and $|\mathcal{T}|(A/n)^s \gtrsim K_0$ (at our sizes: every word whose folds mostly have a close codeword, for all $s$ in play), the exceptional set has probability at least about $(n/q)^s \approx \epsilon^s\rho^{-s}$. Measured: with uniform points at $q = 64$, $n = 16$ the exceptional frequency is 22, 4, 1 of 300 at $s = 2, 3, 4$ for a random word, against $(n/q)^s = 6.3\%, 1.6\%, 0.4\%$; at $q = 128$, 318, 39, 4 of 20000 for the flats pole pair against $1.6\%, 0.20\%, 0.024\%$; at $q = 256$, 70 of 20000 at $s = 2$ against $0.39\%$ (Section 5.3). This is the dominant exceptional event at every size I tried. It is harmless for the bound ($\rho^{-s} \le 2^{19 \cdot 8}$ at the deepest level against the factor $q^3$), and it disappears if the points are drawn from $E \setminus D$, which costs nothing. A point in $D$ is in effect a query, and a query does not separate list members.
- **The factor $\Lambda^3q^3$ is not known to be tight. [conjectured]** Every exceptional event I can build has probability at most about $(n/q)^s + \binom{\Lambda}{2}\epsilon^{s}$: all points in $D$, or two list members (or two pole lines) sharing all $s$ answers. Configurations with candidates that miss the answers at one point each are rarer still or do not reach $K_0$: with a claim, one round message can give a whole line to one such candidate only. If that were the truth, 2 or 3 points would do at level 0 instead of 12 to 14. The factor $q^3$ pays for unexplained close codewords about which nothing is known, and I see no way to remove it without structure.

### 2.4 Lanes and fields in `ListBound`

**Proposition 2.4. [proved]** Suppose every word $D \to \mathbb{F}$ over a field $\mathbb{F} \supseteq K$ has at most $\Lambda_1$ polynomials of degree at most $d$ at agreement $A$. Then every $h$-lane word over $\mathbb{F}$ has at most $\Lambda_1$ tuples at agreement $A$, provided $\binom{\Lambda_1 + 1}{2} < |\mathbb{F}|$. *Proof.* Given $\Lambda_1 + 1$ distinct tuples, a random $\lambda \in \mathbb{F}^h$ maps two of them to the same polynomial $\sum_u \lambda_u U_u$ with probability $1/|\mathbb{F}|$, so some $\lambda$ keeps them distinct, and they all agree with the word $\sum_u \lambda_u f_u$ on $A$ points. $\square$

So a single-word bound over $E$ gives the interleaved bound for $\Lambda_1 < 2^{64}$, and a bound for $K$-valued words gives the $E$-valued one (an $E$-valued word is two $K$-lanes) only for $\Lambda_1 < 2^{32}$. For the budgets $2^{40}$, $2^{70}$, $2^{100}$ of note 07, notes 12 and 13 should state their bounds for words over an arbitrary finite extension of $K$ (then the proposition applies over a large enough extension) or for interleaved words directly. Level 0 commits a $K$-valued word, but its folds are $E$-valued from the first challenge on.

A second remark in the same direction: Theorem A needs only $|\mathcal{T}| = \sum_c |\mathcal{L}(c)|$, the total over the $q^2$ folds, not the maximum. I do not see how to use the difference.

## 3. Corrections to note 07, precisely

| # | where | what | status |
| --- | --- | --- | --- |
| 1 | 3.3 and item 2 of Section 0 | The toy ($q = 32$, $n = 16$) has $\binom{n}{2} = 120 > 2q = 64$ and $0.74K_0 = 64 < 120$: Corollary 4 does not apply. The table checks the class structure (Lemma 2) only. Replaced by Section 5 here. | [checked] |
| 2 | 3.4, error table, row "points" | Add $s\ell/q$ for $r_{i,j} = 0$, mentioned in the text and missing in the table. Better: weights $\prod_k r_k^{u_k}$ instead of $\mathrm{eq}(r, u)$, so that $v_i = y^F_i + r_{i,j}y^G_i$, the prover sends $y^G_i$, the verifier computes $y^F_i = v_i + r_{i,j}y^G_i$, and there is no division and no failure event. Schwartz-Zippel is unchanged (the weights are still linearly independent multilinear monomials). | [proved] |
| 3 | 3.4, step 3 | At the last level the verifier holds $P^{(i,\ell)}$ and must check $P^{(i,\ell)}(\zeta_k) = v_k$ for all $k$. Not stated. | [proved] necessary: without it a polynomial of the last list that satisfies the running claim and violates a point claim is accepted, and the last level's fold rounds lose the theorem |
| 4 | 3.4 | State that the $s$ points of a commitment are one verifier message, that the $r_i$ are independent across points, and that the $y^F_i$ of round $j$ are absorbed before $(\alpha_j, \beta_j)$. With a shared $r$ the bad probability is $\ell/q + \epsilon'^s$; with points drawn one message at a time the exceptional event becomes $s$ events of probability $\epsilon$ each, cost $s/\epsilon$ instead of $\epsilon^{-s}$. | [proved] |
| 5 | 3.4, row "queries and next batching" | $J = t + s + 1$ claims, error $(t + s)/q$, not $(t + s + 1)/q$. Harmless. | [proved] |
| 6 | 3.6, "only the list bound" | The list bound must be for $2^{\ell-j}$-lane $E$-valued words, every $j$, at degree $d$ and agreement $A - \ell$; Proposition 2.4 for when single words suffice. | [proved] |
| 7 | 3.7 | Not a proof. The fold round has four free values (the running claim, with the OOD answer inside, is fixed before the round), so the dependency is on five pairs and the moment bound gives $\Lambda(\mu/q)^{1/5}$; with the OOD answer counted as free, six and $1/6$ as written. Either way the method fails, and the real reason is the attack of Section 7. | [heuristic] for the method, [proved] and [checked] for the attack |
| 8 | 3.2, Theorem 3 | Optional: constant $1/(K_0(K_0-1)(K_0-M))$, $|\mathcal{T}|$ for $\Lambda q^2$, and the remark that the exceptional set contains all point tuples inside $D$. | [proved] |
| 9 | 3.5, verifier cost | Also count the challenges: $s(\ell + 1)$ field elements squeezed per commitment for the points (299 at $\Lambda = 2^{40}$), about as many permutations as the scalars absorbed. Still small against the Merkle work. | arithmetic |

Nothing else in Sections 3.1 to 3.6 of note 07 needed changing. I did not re-derive the byte counts of 3.5 and 3.6.

## 4. Attack attempts

Path costs are in the model of note 03 (Lemma P), with the present grinds: fold 7 bits, points 15 bits. "DEEP" means two or more unbatched point claims.

| # | strategy | today's round shape | with DEEP points | status |
| --- | --- | --- | --- | --- |
| S1 | A list of $L$ candidates in the $G$ half, one round message (note 03, 3.3) | wins about $1.5\,L$ lines: 24 lines for 15 candidates at $q = 64$, 21 at $q = 32$ | exactly $2q$: the candidate the answers name, and nothing else | [checked] exhaustive over all answers and messages |
| S2 | Aim a whole line at one candidate (note 03, Lemma 1(d)) | one line per attempt | the named candidate gets two lines ($2q$). A candidate that misses the answers at two points gets at most one challenge. A candidate that misses them at exactly one point can be given the line of that point (three equations on the four free values), which leaves every other candidate a generic conic: about $2q$ in total again, and it needs two candidates agreeing at $s - 1$ points | [proved] for the counts; the total is bounded by Corollary 4 in any case |
| S3 | Pole pair, any numerator, with a claim | several lines' worth: 219 to 228 of 4096 at $q = 64$ | one line ($q$ challenges): 64 or 65 of 4096 at $q = 64$, flats family and random numerator | [checked] exhaustive |
| S4 | Pole pair over big degree-$(d+1)$ lists: 620 flats at rate 1/8, the list of $x^{16}L_W$ at rate 1/2 and $5n/8$ (2168 members on the domain inside $\mathrm{GF}(2^6)$, 1400 on a generic one by note 05) | every challenge has several close codewords | one line, as soon as the points separate the list ($s \ge 2$ for the flats, $s \ge 4$ at $q = 64$ for the $5n/8$ word, where $\epsilon = 1/4$) | [checked] |
| S5 | Pair planted on $A - 2$ points (crossing sets) | n/a | at most $\binom{n - A + 2}{2}$: 66 at $n = 16$; below $2q$ whenever $\binom{n}{2} \le 2q$ | [proved] Lemma 2.2(c), [checked] |
| S6 | Answers chosen after the points to merge several classes | n/a | impossible off the exceptional set: the maximum over all $q^{2s}$ answer vectors is the largest class plus at most a few challenges at $s = 2$, and exactly the largest class from $s = 3$ or $4$ on | [checked] exhaustive, $s = 2, 3, 4$ |
| S7 | Wait for exceptional points: roots of $R$, or all points in $D$ | n/a | works with probability $(r/q)^s$ or $(n/q)^s$: path cost at least $2^{15 + 100 s}$ | [proved], [checked] |
| S8 | Put one point in $D$ by grinding the point message | n/a | costs $2^{15} q/(s n)$, between $2^{111}$ and $2^{114}$ hash evaluations at level 0 depending on the rate, and makes that point useless against candidates agreeing with the word there; the other $s - 1$ points are untouched | [proved] for the cost; harmless as long as $s - 1$ points still pay for the list |
| S9 | Two fold rounds with the same points: hope the first challenge makes the points bad for the second round | n/a | no first challenge did: 0 of 1024 (all of them) at $q = 32$ for five word shapes, 0 of 500 at $q = 64$ for three | [checked], Section 5.5 |
| S10 | Two lanes per half: a planted tuple in both lanes, a pole pair in one lane with exact codewords in the other | n/a | same counts as one lane; a random two-lane word has almost no close tuples at all. I did not build a two-lane word with a different pole family in each lane | [checked] $h = 2$, thin |

**Cheapest path found against the modified fold. [proved] given Corollary 4.** Escape the fold for the candidate the answers name: probability $2/q$ per attempt, cost $2^{7} q/2 = 2^{134}$ hash evaluations, independent of the list size; or one pole line, $2^{135}$. Then the queries, $2^{17}(n/T)^t$. Nothing below $2^{125}$. With today's fold the same path costs $2^{135}/L$.

**Consequence for the attack floors of note 09. [proved] for the listed strategies only.** With $s \ge 2$ unbatched points a candidate that disagrees with the answers at two points wins at most one challenge, so $L$ candidates add at most $L/q^2$ to the escape probability of a round, and two candidates share all $s$ answers with probability at most $\binom{L}{2}\epsilon^s$ over the points. Both are negligible for every family known to the swarm: the flats at rate 1/4 ($2^{26}$), the family at $5n/8$ ($2^{30.8}$) and the one at $9n/16$ ($2^{102.7}$) all cost the $2^{134}$ above. So the "attack floor $t$" column of note 09 is a statement about today's protocol. For the modified one the known attacks give no floor above the point where lists reach about $2^{130}$, and everything between there and Johnson is open on the proof side only.

## 5. Brute-force evidence

`10_deep_redteam.c` computes, for a pair of words, the complete list of every fold (all $q^2$ challenges) by a depth-first walk over $(d+1)$-subsets with Newton updates, each $(c, P)$ produced once from the first $d + 1$ points of its agreement set. The lists were compared with a naive Lagrange enumeration on random challenges in every run that says so (0 mismatches in all). Then: dependency classes through 200 to 600 anchors; the exact maximum, over **all** answer vectors $m \in E^{2s}$, of the number of challenges with an $m$-consistent list member (branch and bound, exact above the stated floor); the exact maximum over all $m$ **and** all round messages $(v_G, v_F, \sigma_0, \sigma_1) \in E^4$ of the number of winning challenges, for random weights on the low part and a claim false for the planted pair; the same with no point claims; and for every point tuple whether it is exceptional (some $m$ with at least $K_0 = \lceil 2.72q\rceil$ consistent challenges and less than 74 percent of them on one pair of $\mathcal{L}_{\mathrm{pair}}$).

Words: `random`; `plantedK`, a pair of degrees $(d-1, d)$ agreeing on exactly $A - K$ common points; `pole`, $f_0 = 1/(x - x_0)$, $f_1 = w/(x - x_0)$ with $w$ random; `poleflat`, the same with $w = x^{2(d+1)}$ (all flats of size $2(d+1)$); `flatlist`, $f_0 = F$ exactly and $f_1 = G + x^{2d+1}$, so the pairs $(F, G + Q_V)$ for all subspaces $V$ of size $2(d+1)$ are in $\mathcal{L}_{\mathrm{pair}}$; `five8`, a pole pair over $x^{16}L_W$ of note 05; `polerh` and `twopairs`, the constructions of Section 2.3. "Generic points" are outside $D$, distinct, and not the pole; "uniform points" are uniform in $E$, the distribution of the theorem.

### 5.1 Structure (Lemma 2, Theorem 3)

All **[checked]**. "Lemma 2 violations" counts pole classes above $q$ and unexplained polynomial classes above $\max(q, \binom{n}{2})$: zero in every run of this note.

| field, $n$, $d$, $A$ | word | $\lvert\mathcal{T}\rvert$, challenges with a close codeword, $\Lambda$ | largest class: pair of $\mathcal{L}_{\mathrm{pair}}$ / other polynomial / pole | best answer vector, generic points, $s = 1$; $2$; $3$; $4$ |
| --- | --- | --- | --- | --- |
| $2^6$, 16, 3, 6 | random | 7034, 3466 of 4096, 9 | none / 64 / 64 | 164 to 202; 64 to 68; 64 to 65; 64 |
| | planted0 | 10429, 4096, 8 | 4096 / 66 / 64 | 4096 at every $s$ |
| | planted1 | 7368, 3506, 8 | 652 / 64 / 64 | 701 to 734; 652 to 655; 652; 652 |
| | planted2 | 7098, 3462, 7 | none / 66 / 11 | 167 to 201; 66 to 69; 66; 66 |
| | pole | 6592, 3264, 5 | none / 8 / 64 | 256 to 448; 64 to 128; 64 to 128; 64 |
| | poleflat | 1920, 1920, 1 | none / 3 / 64 | 64 at every $s$ |
| | flatlist | 61440, 4096, 15 | 4096 / 3 / 3 | 4096 (each of the 15 pairs) |
| $2^6$, 16, 7, 10 (rate 1/2) | random | 7402, 3514, 7 | none / 28 / 64 | 161 to 193; 64 to 68; 64; 64 |
| | planted1 | 7739, 3600, 8 | 427 / 28 / 64 | 492 to 560; 427 to 430; 427; 427 |
| | planted2 | 7410, 3514, 7 | none / 28 / 64 | 171 to 207; 65 to 70; 64; 64 |
| | pole | 8256, 3584, 6 | none / 5 / 64 | 256 to 448; 64 to 128; 64; 64 |
| $2^8$, 32, 7, 12 (rate 1/4) | random | 3173, 3115 of 65536, 3 | none / 7 / 4 | .; at most 255; at most 255 |
| | planted1 | 8360, 8044, 3 | 5171 / 9 / 3 | .; 5171 to 5172; 5171 |
| | planted2 | 3348, 3274, 2 | none / 221 / 4 | .; at most 255; at most 255 |
| | pole | 2816, 2816, 1 | none / 0 / 256 | .; 256; 256 |
| | poleflat (62 flats) | 28160, 28160, 1 | none / 3 / 256 | .; 256; 256 |
| $2^8$, 32, 3, 8 (rate 1/8) | poleflat (620 flats) | 158720, 61184, 6 | none / 7 / 256 | .; 256; 256; 256 |
| $2^6$, 32, 15, 20 (rate 1/2, $5n/8$) | five8 (2168 lines) | 138752, 4032 of 4096, 46 | none / 4 / 64 | .; 256 to 768; 128 to 256; 64; 64 at $s = 5$ |
| $2^6$, 16, 3, 6, two lanes per half | planted0 | 4097, 4096, 2 | 4096 / 0 / 0 | .; 4096; 4096; 4096 |
| | pole (second lane exact) | 6592, 3264, 5 | none / 8 / 64 | .; 64 to 256; 64 to 128; 64 |
| | poleflat | 1920, 1920, 1 | none / 3 / 64 | .; 64; 64; 64 |

A dot means not computed; "at most 255" means below the search floor $q - 1$. Classes are found through random anchors, so a class of $k$ elements is seen with probability $1 - (1 - k/|\mathcal{T}|)^{\text{anchors}}$: certain for the large ones, likely for the rest.

Reading. (i) One point is useless, as it must be: every answer pair is consistent with a $1/q$ fraction of $\mathcal{T}$ on average, so the best one wins at least $|\mathcal{T}|/q$ challenges **[proved]** by averaging. (ii) From two generic points on, the best answer vector wins the largest class and a few stragglers; from three or four on, exactly the largest class. (iii) The classes are what Lemma 2 says: a line for a pole, at most $\binom{n-A+2}{2}$ for a pair two points short (66 at $n = 16$, $A = 6$; 221 of a possible 231 at $n = 32$, $A = 12$), everything larger is a pair of $\mathcal{L}_{\mathrm{pair}}$. (iv) Where the list is large against $1/\epsilon$ (the `five8` row: 2168 list members, $\epsilon = 1/4$) two or three points do not separate it and several lines merge; four do. This is the term $\binom{\Lambda}{2}\epsilon^s$ at work, and the reason lists enter the point message. (v) With two lanes per half and errors in both lanes, almost nothing is close: the `random`, `planted1` and `planted2` words have $|\mathcal{T}| = 1, 2, 0$ (rows omitted), because a repair must work in every lane at once.

### 5.2 Corollary 4, exhaustively

Maximum number of winning challenges over all answer vectors (two generic points) and all $q^4$ round messages. **[checked]**, exact (every cell of answers with enough consistent challenges to matter was searched).

| field, $n$, $d$, $A$ | word | no point claims, best round message | two point claims, best answers and message | $2q$ | $K_0 = 2.72q$ |
| --- | --- | --- | --- | --- | --- |
| $2^6$, 16, 3, 6 | planted0 (one member, false claim) | 284 | 128, 128, 129 | 128 | 174 |
| | planted1 | 242 | 127, 127, 127 | | |
| | flatlist (15 members) | **1536** (24 lines) | **128**, 128, 128 | | |
| | pole | 228 | 65, 64, 64 | | |
| | poleflat (30 lines) | 219 | 64, 64, 64 | | |
| | random | 222 | 64, 64, 65 | | |
| | twopairs, generic points | . | 128, 128 | | |
| | twopairs, points at the roots of $R$ | . | **256** (exceptional, probability $(2/q)^2$) | | |
| $2^7$, 16, 3, 6 | planted0 | . | 257 | 256 | 348 |
| $2^5$, 16, 3, 6 | planted0 | 270 | 67, 65, 65 | 64 | 87 |
| | flatlist (15 members) | **672** (21 lines) | 64, 64, 64 | | |
| | pole | 305 | 65, 34, 33 | | |
| $2^5$, 16, 3, 6, two lanes per half | planted0 | 67 | 64, 64, 64 | 64 | 87 |
| | flatlist | 672 | 64, 64, 64 | | |
| | pole | 323 | 33, 33, 33 | | |

The `flatlist` rows are the central claim in one line: fifteen list members with a false claim win 37.5 percent of the challenges in today's round shape and $2q$ of $q^2$ with two unbatched point claims, the count for a single member. At $q = 64$ and $q = 128$ the hypotheses of Corollary 4 hold ($\binom{16}{2} = 120 \le 2q$) and the maximum stays below $K_0$ in every case off the exceptional set.

### 5.3 The probability bound where it says something

At $q = 256$, $n = 16$, $d = 3$, $A = 6$ the bound of Theorem A with the measured $|\mathcal{T}|$ is below 1 from $s = 3$ on. Uniform points, 20000 tuples per word, every answer vector with at least $K_0 = 697$ consistent challenges examined. **[checked]**

| word | $\lvert\mathcal{T}\rvert$ | exceptional tuples at $s = 2$; $3$; $4$ | bound $\lvert\mathcal{T}\rvert^3\epsilon^s/(K_0(K_0-1)(K_0-2q))$ at $s = 2$; $3$; $4$ | $(n/q)^s$ |
| --- | --- | --- | --- | --- |
| random | 7769 | 70; 0; 0 | 1.28; 0.0199; 0.00031 | 0.0039; 0.00024; 0.000015 |
| planted2 | 7711 | 83; 3; 0 | 1.25; 0.0195; 0.00031 | |
| pole | 5888 | 53; 0; 0 | 0.56; 0.0087; 0.00014 | |
| poleflat (30 lines) | 7680 | 70; 2; 0 | 1.23; 0.0193; 0.00030 | |

The same at $q = 128$ ($K_0 = 349$, $(n/q)^s = 0.016, 0.0020, 0.00024$):

| word | $\lvert\mathcal{T}\rvert$ | exceptional tuples of 20000 at $s = 2$; $3$; $4$ | bound at $s = 2$; $3$; $4$ |
| --- | --- | --- | --- |
| pole | 6656 | 558; 26; 3 | 25.5; 0.80; 0.025 |
| poleflat (30 lines) | 3840 | 318; 39; 4 | 4.9; 0.153; 0.0048 |

The bound is never violated. Where it is below 1 the observed frequency is at least 24 times smaller (24 to several hundred times, or no occurrence at all), and it sits at $(n/q)^s$: at $q = 256$, 70 and 83 of 20000 against 78 expected for "both points in $D$", 3 and 2 against 4.9 for three; at $q = 128$, 318 against 312, 39 against 39, 4 against 4.9 for the flats pole pair. (The pole pair with a random numerator has more at $s = 2$, 558: its degree-4 list is large against $1/\epsilon$, so list members also collide at points outside $D$.) At $q = 64$ with 300 uniform tuples, where the bound is vacuous: 22, 4, 1 exceptional tuples at $s = 2, 3, 4$ for a random word, 21, 2, 0 for planted2, 20, 4, 1 for the flats pole pair, 100, 6, 1 for the pole pair with a random numerator, against $(n/q)^s = 6.3\%, 1.6\%, 0.4\%$.

### 5.4 An explicit exceptional tuple

**[checked]** $q = 256$, $n = 32$, $d = 5$, $A = 10$, pole pair over a word with three degree-6 list members $C_i = C_0 + R\,H_i$ on disjoint sets of 10 points, $R$ of degree 3 with roots $243, 119, 99$ outside $D$. $|\mathcal{T}| = 1280$, all in pole classes of 256 (five lines), $\Lambda = 1$, no pair. With the points at the roots of $R$: one answer vector wins $768 = 3q$ challenges at $s = 2$ and at $s = 3$, above $K_0 = 697$ and with only a third of them in one class, so the tuple is exceptional. With 20 generic tuples: 256 every time. The exceptional tuples of this word have probability at least $(3/256)^s$, against a bound of $0.0128$ at $s = 2$ and $0.0003$ at $s = 3$. So the conclusion of Theorem 3 does fail on a set of points of probability about $(r/q)^s$ with $r$ up to a constant fraction of $d$, and the factor $\epsilon^s$ cannot be improved in general. The second construction (`twopairs`, Section 5.2) does the same for Corollary 4: $4q$ winning challenges on a set of probability $(2/q)^2$.

### 5.5 Two rounds with the same points

A 4-lane word, round 1 folds it to two lanes with $c_1$, round 2 is Theorem 3 for those two lanes, with the same three generic $\zeta_i$ (the lane coordinate of round 1 plays no role in round 2). For each $c_1$ the full lists of round 2 are recomputed and every answer vector winning more than $q$ challenges is found. **[checked]**

| field | 4-lane word | first challenges | of them, round 2 has an answer vector with at least $K_0$ wins not explained by a pair | largest round-2 maximum, and what it is |
| --- | --- | --- | --- | --- |
| $2^5$ | random | all 1024, two point triples | 0 | 1024, a pair of $\mathcal{L}_{\mathrm{pair}}$ that exists for that $c_1$ |
| | planted1 (a 4-lane tuple on $A - 1$ points) | all 1024, two triples | 0 | 309, the fold of the planted tuple |
| | planted2 | all 1024, two triples | 0 | 307, a pair |
| | pole (lane $(0,0)$ is $1/(x - x_0)$, two lanes random, one zero) | all 1024, two triples | 0 | 342, a pair |
| | poleflat (lane $(0,0)$ is $1/(x - x_0)$, lane $(1,1)$ is $x^8/(x - x_0)$) | all 1024, two triples | 0 | 1024 at $c_1 = (0,0)$, a pair; one line otherwise |
| $2^6$ | random | 500 sampled, one triple | 0 | 656, a pair |
| | planted2 | 500 sampled | 0 | 653, a pair |
| | poleflat | 500 sampled | 0 | at most $q$ for all 500 |

At these sizes a random fold often has a pair of $\mathcal{L}_{\mathrm{pair}}$ by chance (a pair has 7 coefficients and must fit 5 points), which is why large maxima appear; they are all explained.

So in these instances the set of first challenges that spoil the points for the second round, which the nested Markov argument budgets at $\tau = 2^{-119}$, is empty at toy size, where $\epsilon^s$ is $2^{-9}$ to $2^{-12}$. This says the nesting loss is probably an artifact; it proves nothing.

## 6. Parameters

From `10_params.py`, with Theorem A's constant, $M = 2q$ ($\binom{n}{2} \le 2^{55}$ for $n \le 2^{28}$), $\epsilon = (2^\kappa + 2\ell - 1)/q$ (first round of the level, the most lanes), the $\mu = 30$ ladder ($\kappa = 24, 20, 16, 12, 8, 4$, $\ell = 6, 4, 4, 4, 4, 4$; the counts do not depend on the rate, since $n$ enters only through $\binom{n}{2} \le 2q$), fold budget $2^{-118}$ (7-bit grind), point budget $2^{-110}$ (15-bit grind), half of it for the exceptional set. The split of the fold budget between $K_0/q^2$ and $\tau$ is optimised: $K_0 = 384\,q$, $\tau = 2^{-118.7}$. **[checked]** arithmetic.

| list bound $\Lambda$ | points per level, variant P (levels 0 to 5) | scalars | bytes | note 07 |
| --- | --- | --- | --- | --- |
| $2^{8}$ | 11, 8, 8, 8, 8, 7 | 272 | 4352 | same |
| $2^{40}$ | 12, 9, 9, 9, 8, 8 | 299 | 4784 | same |
| $2^{70}$ | 13, 10, 10, 9, 9, 9 | 326 | 5216 | 13, 10, 10, 10, 9, 9 |
| $2^{100}$ | 14, 11, 11, 10, 10, 10 | 358 | 5728 | same |
| $2^{130}$ | 14, 12, 11, 11, 11, 10 | 373 | 5968 | |

Level 0 at $\Lambda = 2^{40}$: the points must pay $3 \cdot 40 + 3 \cdot 128 - \log_2(k^2(k-2)) + 5 \cdot 118.7 + 111 = 1183$ bits at 104.0 bits per point, so 11.4 points. Of these bits, 593 are the nesting over the six rounds, 358 are the factor $q^3/k^3$, 111 the message's own budget and 120 the list. With no grinding at all on the fold and point messages (fold $2^{-125}$: $K_0 = 3.7\,q$, $\tau = 2^{-125.9}$) the counts are 13, 10, 9, 9, 9, 9 at $2^{40}$: one more point at three levels. With fresh points every round (variant F, no nesting): 6, 6, 6, 6, 5, 5 at $2^{40}$ and 8, 8, 7, 7, 7, 7 at $2^{100}$, but twice the answers per round and the extra batching of note 07, which I did not analyse.

**Fold-round error against $2^{-118}$. [proved] given Theorem A and Proposition 8.1.** $K_0/q^2 + \tau = 2^{-119.4} + 2^{-118.7} = 2^{-118.0}$ with the optimised split, or $2^{-119}$ with note 07's $K_0 = 2^8q$, $\tau = 2^{-120}$. No list term, no pole term, no $\varepsilon_{\mathrm{aff}}$. The irreducible part is $2/q = 2^{-127}$.

**The answers to "how many points".** Level 0: 12, 13, 14 points for lists of $2^{40}$, $2^{70}$, $2^{100}$. Later levels: 9 down to 8, 10 down to 9, 11 down to 10. This agrees with note 07 everywhere except one level at $2^{70}$, where the better constant saves a point.

## 7. The two side claims

**"The present protocol cannot be re-analysed this way."** True, and for a stronger reason than the one given.

- *The method.* **[heuristic]** As corrected in Section 3, item 7: with the single out-of-domain point batched into the running claim, a winning challenge imposes one linear condition on the four free values of the round message, a dependency needs five pairs and gives one determinant condition with probability about $\mu/q$ over the point, and the moment bound is $(\Lambda q^2)^5(\mu/q)/K_0^5 < 1$, that is an error of order $\Lambda(\mu/q)^{1/5}$. One *unbatched* point does not help either: the triple bound is $\Lambda^3q^6\epsilon/K_0^3$, an error $\Lambda\epsilon^{1/3}$, and by averaging every answer pair is consistent with $|\mathcal{T}|/q$ elements, so the list factor is back (**[proved]**, and the $s = 1$ column of Section 5.1). Two points are structurally enough in every instance I ran; the proof needs $q^3\epsilon^s \ll 1$, five fresh points or eleven to fourteen carried ones.
- *The protocol.* **[proved], [checked]** No analysis of today's protocol can have a fold error without a list factor, because the factor is real: for candidates $(F, G_i)$ sharing $F$, the round message honest for $F$ with $v_F$ shifted gives candidate $i$ the roots of $\delta^i_G + \alpha(\delta^i_G + e_i) + \alpha^2\delta_F$, one or two whole lines each (note 03, Lemma 2, with the quadratic term added). Measured: 24 lines for 15 candidates at $q = 64$, 21 at $q = 32$ (Section 5.2). After the escape the prover is honest for that candidate. So the term $2L/q$ of `lem:fold-list` is tight up to a factor between 1 and 2, and the gain of Theorem 3 requires the protocol change.

**"Queries before the next commitment are unsound."** **[proved]**, correct. If the $t$ query points of level $i$ are known before $f^{(i+1)}$ is committed, the prover chooses $f^{(i+1)}$ and $\phi$ with $\mathrm{Enc}_i(f^{(i+1)})[x_q] = c_q$ for all $q$ and $\langle W^{(i,\ell)}, f^{(i+1)}\rangle$ equal to the running claim: $t + 1$ linear conditions (evaluations at distinct points and one more functional) on $2^{\kappa_i} + \ell$ unknowns, solvable for every value of the right-hand sides as soon as the $t + 1$ functionals are independent, which holds for $t < 2^{\kappa_i}$ and a weight outside the span of the $t$ column weights. After that the prover is honest for $f^{(i+1)}$. Acceptance with probability 1 for a false claim at level $i$, at every level but possibly the last ($2^4 + 4 = 20$ unknowns against 16 conditions: still solvable). The same holds for the new point claims: they too must be answered before the queries, which variant P does.

## 8. From the lemma to a round-by-round theorem

### 8.1 What I verified of the composition

I wrote out the state function of variant P and checked each transition. This is independent of note 11 and should be compared with it. Proposition 8.1 is **[proved]**. The transitions are **[proved] in outline**: each was checked on paper at the level of detail of the proof of `thm:rbr`, conditional on `ListBound`, but this is a proof outline and not a written-out theorem, and none of it is formalized.

*State function.* For a level with committed word $\mathcal{O}$ ($2^\ell$ lanes), fold words $\mathcal{O}^{(j)}$, lists $\mathrm{lst}^{(j)} = \mathrm{lst}(\mathcal{O}^{(j)}; A - (\ell - j), d)$, points $z_k = (r_k, \zeta_k)$, carried values $v_k$:

- $\mathrm{Exc}_j(w)$: the point tuples whose projection on the coordinates $(r_{k,j+1..\ell}, \zeta_k)_k$ is exceptional in Theorem A for the two halves of $w$, with $M = 2q$.
- $\mathrm{Bad}_\ell(w) := \mathrm{Exc}_\ell(w)$ and $\mathrm{Bad}_j(w) := \mathrm{Exc}_j(w) \cup \{z : \Pr_c[z \in \mathrm{Bad}_{j+1}(w_c)] > \tau\}$.
- After the points of the level: distinct tuples of $\mathrm{lst}^{(0)}$ differ under some $\mathrm{ev}_{z_k}$; $z \notin \mathrm{Bad}_1(\mathcal{O})$; no $r_{k,j}$ is zero (if the weights are $\mathrm{eq}$).
- After the batching challenge ($j = 0$) and after fold challenge $j$: no $U \in \mathrm{lst}^{(j)}$ satisfies the running claim and all $s$ carried point claims $\mathrm{ev}_{z_k^{(j)}}(U) = v_k$; and $z \notin \mathrm{Bad}_{j+1}(\mathcal{O}^{(j)})$ for $j < \ell$.

**Proposition 8.1 (nesting). [proved]** If $\Pr_z[\mathrm{Exc}_j(w)] \le e$ for all $j$ and all words, then $\Pr_z[\mathrm{Bad}_1(w)] \le e\sum_{k<\ell}\tau^{-k} \le e\,\tau^{-(\ell-1)}/(1-\tau)$. *Proof.* $p_j := \sup_w \Pr_z[\mathrm{Bad}_j(w)]$ satisfies $p_j \le e + p_{j+1}/\tau$ by Markov on $g(z) := \Pr_c[z \in \mathrm{Bad}_{j+1}(w_c)]$, whose mean over $z$ is $\mathbb{E}_c\Pr_z[\mathrm{Bad}_{j+1}(w_c)] \le p_{j+1}$: the word $w_c$ does not depend on $z$, and the projection used in round $j + 1$ is uniform. $\square$ This is note 07's sketch, and it is right. The loss is intrinsic to using Theorem A as a black box: for a bad set with product structure a tree search does find it at cost $\ell\,p^{-1/\ell}$.

*Transitions.*

1. **Points of a level** (level 0: at commit time). Error $\binom{\Lambda}{2}\bigl((d + \ell)/q\bigr)^s + 2\varepsilon_{\mathrm{pt}}\tau^{-(\ell-1)}$ $(+\ s\ell/q)$. Separation is of tuples, high parts included, not of messages as in `lem:ood`: the new point claims see whole polynomials.
2. **Fold challenge $j$.** The prover has sent the round message and the $y^F_k$; $y^G_k$ follows from $v_k$. A pair of $\mathcal{L}_{\mathrm{pair}} \subseteq \mathrm{lst}^{(j-1)}$ consistent with these answers satisfies the carried point claims, so by the invariant it violates the running claim: the hypothesis of Corollary 4. The points are not in $\mathrm{Exc}_j$. So fewer than $K_0$ challenges break the claim part and at most a $\tau$ fraction the $\mathrm{Bad}_{j+1}$ part: error $K_0/q^2 + \tau$. If no list member satisfies the carried claims at all, no pair is consistent with any $y^F$ and the same bound holds.
3. **Queries and $\lambda_{i+1}$.** By separation at most one $U^\ast \in \mathrm{lst}^{(i+1,0)}$ matches the new answers. Every other member violates a new point claim, which stays unbatched: no union over the list. For $U^\ast$, with $g^\ast$ its message and $P^\ast := \mathrm{poly}(g^\ast) + \text{high part } \phi$: if $P^\ast \in \mathrm{lst}^{(i,\ell)}$ it violates the running claim or some $P^\ast(\zeta_k) = v_k$, that is $g^\ast$ violates the residual claim or a converted point claim $\langle W_{\zeta_k}, g\rangle = v_k - \widehat W_\kappa(\zeta_k)\sum_s\phi_s\mathrm{novel}_s(\zeta_k)$; otherwise a query catches it except with probability $((A-1)/n)^t$. Then $\lambda$: $(J-1)/q$ with $J = t + s + 1$.
4. **Level 0 batching.** As 3 without queries: $(J_0 - 1)/q$, the "false claims" hypothesis being that the pinned member violates an input claim.
5. **Last level.** With the check of correction 3, the two cases of `thm:rbr` apply to the polynomial sent.

So the error table of note 07, Section 3.4, is right with corrections 2 and 5.

### 8.2 The gaps

| # | gap | kind |
| --- | --- | --- |
| G1 | The state function carries a non-constructive condition on the points ($z \notin \mathrm{Bad}_j$), defined through the lists of all folds of all folds. Fine for round-by-round soundness, but `formal/`'s state function and `FoldRoundBound` have to be rebuilt around it. | proof engineering |
| G2 | `ListBound` hypothesis in its exact form: for every level and every $j \ge 1$, every $2^{\ell - j}$-lane word $D_i \to E$ has at most $\Lambda$ tuples of degree at most $2^{\kappa_i} - 1 + \ell_i$ at agreement $A_i - (\ell_i - j)$, and the same for $2^{\ell}$ lanes at $A_i - \ell_i$ (separation). Proposition 2.4 for the reductions. | open, the whole problem |
| G3 | Level 0: the points are part of the commit phase. The outer protocol's "one pinned candidate" becomes "the message of the unique list tuple matching the $s$ answers", and the definition of false input claims must include the point claims. The separation and $\mathrm{Bad}_1$ errors are charged to a verifier message that precedes every outer message. Not checked against `08-end-to-end-protocol.tex` or the ring switch. | to write |
| G4 | Last level: explicit check of the point claims (correction 3). | protocol |
| G5 | Zero lane coordinate: an error term, a completeness error of $s\ell/q$ if the verifier aborts, or monomial weights (correction 2). The Lean completeness statement is perfect today. | protocol |
| G6 | Knowledge soundness. Today's extractor outputs the message pinned by the OOD answer. Here it outputs the message of the pinned tuple. I expect no difficulty and did not check it. | not examined |
| G7 | Fiat-Shamir and grinding: the point message now carries two (or three) error terms under one grind; the per-round $\tau$ shares the fold grind with $K_0/q^2$. Budgets in Section 6. | arithmetic, done |
| G8 | Transcript order (correction 4): one message for the $s$ points of a commitment; $y^F$ before the fold challenge; new points and their answers before the queries of the previous level. If a $y^F$ could be chosen after its challenge, every $(c, P)$ would be consistent and the theorem would say nothing. | protocol |
| G9 | Independence: $r_k$ independent across points, $\zeta_k$ in $E$ (in $K$, $\epsilon$ would be $2^{-40}$), fresh per level. Optional: $\zeta_k \in E \setminus D$. | protocol |
| G10 | Variant F (fresh points every round, old point claims batched into the running claim) is not covered: the running claim then contains whole-polynomial evaluations, its weight is no longer a low-part weight, and every intermediate list needs its own separation. | not examined |
| G11 | The converted point claims add $s$ tensor weights per level to the final weight evaluation of the verifier and the guest, and $s(\ell + 1)$ squeezed challenges per commitment. Costs only. | cost |
| G12 | Everything is on paper. The brute force covers $q \le 256$, $n \le 32$, $h \le 2$, one or two rounds. | status |

## 9. What remains unproved

1. **`ListBound`** below Johnson, in the form of G2. Nothing in this note bears on it.
2. **The composition as a theorem.** Section 8.1 is an outline with every transition checked and no obstacle found, not a written proof, and knowledge soundness (G6) and the level-0 interface (G3) were not examined.
3. **Whether the losses are real.** The proof pays $q^3$ for unexplained close codewords and $\tau^{-(\ell-1)}$ for reusing the points across the rounds of a level: 951 of the 1183 bits at level 0. Every exceptional event I could construct has probability about $(n/q)^s$ or $\binom{\Lambda}{2}\epsilon^s$, and no first challenge spoiled the points in the two-round experiment. **[conjectured]**, on toy evidence only: the true exceptional probability of a level is of order $\ell\,\bigl((n/q)^s + \binom{\Lambda}{2}\epsilon^{s}\bigr)$, which would need 2, 3, 3 points at level 0 for lists of $2^{40}$, $2^{70}$, $2^{100}$. I have no proof and no approach.
4. **Variant F.**

## 10. Reproduction

- `sh doc/whir_soundness_gap_notes/scripts/10_run.sh` builds `10_deep_redteam.c` with the system compiler into `$TMPDIR` and runs every experiment above; `sh 10_run.sh B1` (or `A`, `A4`, `C`, ...) runs one item. Each item takes under ten minutes on at most four threads; the whole set about 40 minutes. The seeds are fixed, so the numbers above are reproduced exactly.
- `python3 doc/whir_soundness_gap_notes/scripts/10_params.py`: the constants and the point counts of Section 6. Instant.
- One run by hand: `cc -O2 -o deep10 10_deep_redteam.c -lpthread && ./deep10 m=6 N=4 d=3 A=6 word=flatlist mode=tables s=2`. Options: `m` (field degree, 5 to 8), `N` ($\log_2 n$), `d`, `A`, `H` (lanes per half), `word`, `mode` (`points`, `tables`, `nested`), `s`, `trials`, `pmode` (0 uniform points, 1 generic, 2 the word's exceptional points), `check` (naive list comparisons), `floor`, `seed`.
