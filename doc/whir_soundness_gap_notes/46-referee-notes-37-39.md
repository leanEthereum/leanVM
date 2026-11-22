# 46. Referee report on notes 37 (dimension induction) and 39 (period descent)

Researcher 46, round 7, hostile independent referee. Every statement is tagged **[proved]** (I checked the proof line by line, or the proof is in this note), **[checked]** (numerically, with my own code, sizes stated), **[quoted]** (taken from an earlier refereed note, not re-proved) or **[conjectured]**. All code is mine (`scripts/46_*`, section 8); of the earlier programs only `02_lists.c` was run, once, as an oracle to compare one output (section 2.1). Notation is that of notes 37 and 39: $F$ a field of characteristic two, $D \subset F$ an $\mathbb{F}_2$-subspace of dimension $N$, $n = 2^N$, codewords of degree $< k$, agreement $T$, slack $\Delta = T - k + 1$, $\sigma = \Delta/n$, $L_U = \prod_{u \in U}(X - u)$, $D/U = L_U(D)$.

## 0. Verdicts

**The reduction is correct.** I found no gap and no false step in note 37 section 3 (Lemma 3.2, Proposition 3.3, Corollary 3.4, Theorem 3.5) or in note 39 section 1 (Lemma 1.2, Theorem 1.3, Lemma 1.4, Corollary 1.5, Proposition 1.6, Remark 1.7). The conditional bound $\Lambda \le \binom{f+1}{3}^J 2^{NJ - J(J-1)/2}(n/\Delta + 1)$ holds on every subspace domain of every field of characteristic two, for every $k \le n/2$ and every $T \ge k$, under the hypothesis as note 39 states it (primitive lists of the level problems, multi-valued words included, at every level $j < J$). The four numbers are right: $2^{466.4}$, $2^{552.9}$, $2^{773.0}$, $2^{969.5}$. What needs changing is not the mathematics but what is said about the hypothesis and about $f$ (section 1.6): the values $f = 7$ and $f = 16$ are placeholders with no data behind them at $\tau = 0.64$, $f = 133$ is a greedy lower bound that my own search raises to $134$ (so the hypothesis PL$_0(133)$ behind the $2^{970}$ is false as stated; with $134$ the number is $2^{970.3}$, and the true constant is unknown), and stopping the induction at a quotient of 32 or 64 points is strictly better than going to the end: it removes the 4, 8 and 16-point levels from the hypothesis and lowers the bounds to $2^{444.5}$, $2^{516.5}$, $2^{692.8}$.

| item | claim | verdict | how |
| --- | --- | --- | --- |
| 1a | triple function, "periodic", "bad", "primitive": well defined, depend on the triple only | correct | proof read |
| 1b | members with period $a$ for a fixed pair are exactly $c_0 + \varrho\,Q(X^2 + aX)$ | correct | proof read; 0 errors on the $35062$ members of the sets $M_{a'}$ and $21418$ non-members met in 15 descent steps |
| 1c | injection into the list of the periodic subcode, degree halves, agreement drops by $z_0 \le \lvert U\rvert\deg\varrho$, slack does not decrease | correct | proof read; agreements recomputed point by point, 0 errors |
| 1d | the new word is arbitrary, the code is $\{Q(L_{U'}(X))\}$ on $D$ over the same field, one lane | correct | section 1.2 |
| 1e | the hypothesis is needed for that code at every level | correct, and stated so in note 39 Theorem 1.3; the lead's one-line summary is accurate | section 1.4 |
| 1f | multi-valued words reduce to ordinary words with loss $2/\sigma$ (Lemma 1.4) | correct; the slack fraction halves, and it transfers the hypothesis only | proof read |
| 1g | induction, base case $n/\Delta$, the factor $\binom{f+1}{3}^J 2^{NJ - J(J-1)/2}$, the $+1$ | correct for $j_0 \le N - 1$ (so for $k \le n/2$) | proof read; recursion unrolled exactly in `46_numbers.py` |
| 1h | constant triple functions (collinear members) | handled: they are bad, they lie in every $M_{a'}$, and a level with $D/U = 0$ is never descended from | section 1.3 |
| 1i | every subspace domain, every window | correct (it is conditional everywhere) | |
| 1j | arithmetic | correct; $f = 133$ should be $\ge 134$ | `46_numbers.py`, `46_triples prim` |
| 2 | note 39 Proposition 4.1: $56n - 392 + 14336\binom{N-3}{2}_2$ members, structure, period-free part $0$ for $n \ge 64$ | correct; proof read; **exhaustively confirmed at $n = 32$ and at $n = 64$** on random domains, all $508536$ claimed members verified at $n = 128$ | section 2 |
| 3 | note 39 Theorem 2.3, Corollaries 2.4 to 2.6, sharpness, failure on the real shape | correct; "278" should be "277"; sharp up to one unit of $m'$ at $n = 16$; the real shape fails already at $n = 16$ | section 3 |
| 4 | note 37 Lemma 4.1, Lemma 4.2, Theorem 4.3, Theorem 5.1 and its table | correct with one change: Theorem 4.3 needs $\delta < 2n$ in its statement; the table is valid and slightly improvable | section 4 |
| 5 | note 37 Proposition 2.1, Corollary 2.2: set invariance is destroyed by perturbation | confirmed | section 5 |

**The conditional theorem in the form I would sign** is Theorem R in section 1.5, with Corollary R0 for ordinary words. In one sentence: *if, on the given domain, every level problem of dimension above $N - j_0$ has the property that more than $f$ members always contain three whose function is constant or periodic, then every word has at most $\binom{f+1}{3}^{j_0} 2^{Nj_0 - j_0(j_0-1)/2}(B_{j_0} + 1)$ codewords, $B_{j_0}$ the elementary bound of note 37 Lemma 3.2 for the level $j_0$.*

**New facts found while refereeing.** (i) **[checked, exhaustive]** At $n = 64$ the list of $X^{32}L_W$ at agreement $\ge 38$ on a random subspace of $\mathrm{GF}(2^{64})$ is exactly the $103544$ members of Proposition 4.1, with no member having a root outside $D$; this was open in note 37 ("the oracle is out of reach at $n = 64$") and in note 39 it rested on the proof. The method (section 2.2) is a linearization of the power sums and uses none of the theory under review. (ii) **[checked]** A primitive sublist of $134$ members at $(n, k, T) = (32, 17, 19)$. (iii) **[checked]** Theorem S fails on the real shape $\mathrm{span}(1, x, x^2, x^3)$ already at $n = 16$. (iv) **[proved, arithmetic]** The best stopping level of the induction is not the last one.

## 1. The reduction

### 1.1 Definitions

Note 37 uses $\xi = u_0/u_1$ with $u_0 + u_1 + u_2 = 0$ the three differences divided by their gcd, note 39 uses $(c_l - c_i)/(c_j - c_i)$. **[proved]** The six functions obtained by permuting the three members are $\xi, 1/\xi, 1 + \xi, 1/(1 + \xi), \xi/(1 + \xi), (1 + \xi)/\xi$, Möbius transformations with coefficients in $\mathbb{F}_2$, which commute with $X \mapsto X + a$. So the group $\Pi(\xi) = \{a \in D : \xi(X + a) = \xi(X)\}$ and the property "constant" depend on the unordered triple, and the two notes agree. "Constant" is "the three codewords are collinear". For a level-$j$ problem ($\lvert U\rvert = 2^j$, members $P(L_U(X))$, $P \in F[Y]$) the function lives in $F(Y)$ and its periods are taken in $(D/U) \setminus 0$; a period $a'$ in $D/U$ is the same thing as invariance of $P \circ L_U$ ratios under the preimage of $\{0, a'\}$, a subspace $U' \supset U$ of twice the size. Nothing is ambiguous.

### 1.2 The descent step (note 37 Proposition 3.3)

**[proved]** I re-derived every line. Let $P_0 \ne P_1$ be members of a level-$j$ problem with word $v : D \to F \cup \{\bot\}$, degree bound $\kappa$, agreement $A$, $m = \lvert U\rvert$, and $a' \in (D/U) \setminus 0$, $q' = Y^2 + a'Y$, $u = P_1 - P_0$.

1. The fixed field of $Y \mapsto Y + a'$ in $F(Y)$ is $F(q')$ (index 2, and $q'$ is fixed). So a member $P_l$ whose function is invariant has $(P_l - P_0)/u = p_l(q')/e_l(q')$ with $p_l, e_l$ coprime, and $p_l(q'), e_l(q')$ are coprime too (substitute in a Bezout identity). Hence $e_l(q') \mid u$.
2. Writing $u = u_0(q') + Y u_1(q')$ (unique), $e(q') \mid u$ iff $e \mid u_0$ and $e \mid u_1$, so the largest such $e$ is $e_u = \gcd(u_0, u_1)$ and $\varrho = u/e_u(q')$ depends only on $(P_0, P_1, a')$. (The note argues by closure under lcm, which is also right; the gcd form is what I implemented.) Then $P_l = P_0 + \varrho\,Q_l(q')$ with $Q_l = p_l e_u/e_l$, and conversely every polynomial of this form has an invariant function: "exactly" is correct.
3. $\deg\varrho + 2\deg Q_l = \deg(P_l - P_0) \le \kappa$, so $\deg Q_l \le \kappa' = \lfloor(\kappa - \deg\varrho)/2\rfloor \le \lfloor\kappa/2\rfloor$.
4. **The word.** At $x$ with $\varrho(L_U(x)) \ne 0$: $P_l(L_U(x)) = v(x)$ iff $Q_l(L_{U'}(x)) = v'(x)$, $v' = (v - P_0 \circ L_U)/(\varrho \circ L_U)$, because $q' \circ L_U = L_{U'}$ for $U' = L_U^{-1}\{0, a'\} \cap D$. At the at most $m\deg\varrho$ points with $\varrho(L_U(x)) = 0$ every member of $M_{a'}$ takes the value of $P_0$; $z_0$ of them are agreements, the same for all members, and $v' = \bot$ there. So $\mathrm{agr}_{v'}(Q_l) = \mathrm{agr}_v(P_l) - z_0$ exactly.
5. **Slack.** $A - z_0 - 2m\kappa' \ge A - m\deg\varrho - m(\kappa - \deg\varrho) = A - m\kappa$.

**Which code, which field, how many lanes.** The image problem is: polynomials $Q \in F[Y]$ of degree $\le \kappa'$, evaluated as $Q(L_{U'}(x))$ on the same $n$ points of $D$, against the word $v'$ with values in $F \cup \{\bot\}$. Same field (no extension), one lane. Equivalently it is the Reed-Solomon code of degree $\le \kappa'$ on the subspace $D/U'$ of $n/2^{j+1}$ points over $F$, against a word that carries $2^{j+1}$ values (or blanks) at every point, a member's agreement being counted with multiplicity. The word is arbitrary in the sense that nothing ties the $2^{j+1}$ values at a point together; it is not an interleaved word and not an ordinary word, and the threshold is $2^{j+1}\kappa' + \Delta$ in units of points of $D$, so the *absolute* slack $\Delta$ is preserved while the quotient shrinks.

**[checked]** `46_triples ... descent` implements the step for an arbitrary level (polynomials, the values $L_U(x)$, the word with blanks) and iterates it. For every member of $M_{a'}$ it checks that $\varrho$ divides $P_l - P_0$, that the quotient lies in $F[q']$, the degree bound, the equality of agreements recomputed point by point, $z_0 \le m\deg\varrho$ and the slack; for up to 3000 members outside $M_{a'}$ it checks that they are not of the form $P_0 + \varrho\,Q(q')$. Runs: the $n = 64$ list ($103544 \to 15736 \to 504 \to 56 \to 4$ members over four steps, degree bound $32 \to 16 \to 8 \to 4 \to 2$), the same list with a pair of members with double points ($\deg\varrho = 4$, $z_0 = 8 = \lvert U\rvert\deg\varrho$), the 31 flats at $n = 32$ ($31 \to 15 \to 7 \to 3$, $\deg\varrho = 1$ and $z_0 = \lvert U\rvert$ at every step, down to constants), and the $65131$-member list of $X^{15}$, $k = 12$ ($65131 \to 2395 \to 35 \to 5$). From the second step on the word is multi-valued. No error in any step.

### 1.3 Base case, counting, induction

**Lemma 3.2 of note 37. [proved]** For an affine space $H$ of dimension $r$ of level polynomials the direction space vanishes on at most $\kappa + 1 - r$ points of $D/U$, that is on $z \le m(\kappa + 1 - r)$ points of $D$; off them the members of $H$ through $(x, v(x))$ form a hyperplane or nothing; a member lies in at least $A - z$ of these. So $f(r)(A - z) \le (n - z)f(r - 1)$, and the product follows. For $\kappa = 0$ it is $n/A \le n/\Delta$. One remark for users of the sharp product: $\Lambda_{N,j}(\kappa, \Delta)$ is a supremum over degrees $\kappa' \le \kappa$, and the product is not monotone in the degree (consecutive degrees differ by the factor $(n' - \kappa' - 1)/(\Delta/m + \kappa' + 1)$, $n' = n/m$, which is below 1 once $\kappa' + 1 > (1 - \sigma)n'/2$). At rate 1/2 the maximum is at a degree slightly below the top one ($960$ instead of $935$ on 16 points). The notes use $(n/\Delta)^{\kappa+1}$, which is monotone, so nothing in them is affected.

**Supersaturation (note 39 Lemma 1.2). [proved]** $\binom{L}{f+1}/\binom{L-3}{f-2} = \binom L3/\binom{f+1}{3}$ and $3\binom L3/\binom L2 = L - 2$: a list of $L > f$ members without primitive sublist of $f + 1$ members has a pair with at least $(L - 2)/\binom{f+1}{3}$ bad thirds.

**The recursion (note 39 Theorem 1.3). [proved]** With $a_j = \Lambda_{N,j}(\lfloor(k-1)/2^j\rfloor, \Delta)$ and $G = \binom{f+1}{3}$: a bad third of the pair lies in $M_{a'} \setminus \{P_0, P_1\}$ for at least one of the $2^{N-j} - 1$ nonzero $a'$ (in all of them if it is collinear), $\lvert M_{a'}\rvert \le a_{j+1}$ by section 1.2, so $(L - 2)/G \le (2^{N-j} - 1)(a_{j+1} - 2)$ and $a_j \le f + G\,2^{N-j}a_{j+1}$. Unrolling and absorbing the additive terms into the $+1$ needs $2f \le G\,2^{N-j_0+1}$, true for $f \ge 2$ and $j_0 \le N - 1$. For $k \le n/2$, $J = \lceil\log_2 k\rceil \le N - 1$. **[checked]** `46_numbers.py` unrolls $a_j = f + G\,2^{N-j}a_{j+1}$ from $a_J = n/\Delta$ with exact rationals for $f = 2, 7, 134$ at $N = 25$: $a_0 = 2^{326.95}, 2^{466.22}, 2^{773.55}$, below the closed forms $2^{327.03}, 2^{466.40}, 2^{773.74}$.

**Collinear members.** They are bad by definition, belong to every $M_{a'}$, and descend to constants times $e_u$. The only place where "belongs to some $M_{a'}$" could fail is a level with $D/U = \{0\}$, that is $j = N$, and the recursion never starts from such a level because $j < j_0 \le N - 1$.

**Note 37 Theorem 3.5 (hypothesis DP$(B)$). [proved]** Same recursion with $a_j \le 2 + B + 2^{N-j}a_{j+1}$; the stated bound $2^{NJ - J(J-1)/2}(J(B + 2) + n/\Delta)$ follows since the exponents $Ni - i(i-1)/2$ increase for $i \le N$. At $N = 25$, rate 1/2, $\tau = 0.64$: $2^{329.8}$ for $B = 0$, $2^{342.3}$ for $B = 13568$.

### 1.4 What the hypothesis is, exactly

This is where a reader of the one-line summary can be misled, so I spell it out. **[proved]**

1. It is needed **at every level $j < j_0$, for the level code, against multi-valued words**. A level-$j$ instance is a subspace $U \le D$ of dimension $j$, a degree bound $\kappa \le \lfloor(k-1)/2^j\rfloor$, a word $v : D \to F \cup \{\bot\}$ and polynomials $P \in F[Y]$ of degree $\le \kappa$ with $\#\{x : v(x) = P(L_U(x))\} \ge 2^j\kappa + \Delta$. Only the given field and the given domain occur (the suprema "over all fields and domains" in the notes are not needed).
2. It is needed **at every rate up to $\rho$**, not only at the rate of the original code: after one step the degree is $\lfloor(\kappa - \deg\varrho)/2\rfloor$, anything between $0$ and $\lfloor\kappa/2\rfloor$, with the same absolute slack. For instance at $\rho = 1/2$, $\tau = 0.64$ the level problems include rate $1/4$ at agreement fraction $0.39$ on the quotient, which is $0.11$ below the Johnson radius of that rate. Note 39's Conjecture PL says "at every rate up to $\rho$", correctly.
3. The levels **contain every ordinary problem of smaller dimension** at the corresponding parameters (note 39 Remark 1.7, correct, and $L_U(D)$ is generic when $D$ is: the $b_i$ outside $U$ are algebraic over $\mathbb{F}_2(U\text{-basis}, L_U(b_i))$, so the $N$ elements are algebraically independent). At $N = 25$, $k = 2^{24}$, $T = \lceil 0.64n\rceil$ ($\Delta = 4697622$) the ordinary problems inside the levels are, by `46_numbers.py`: quotient of 128 points, degree $\le 63$, agreement $\ge 81$; 64 points, degree $\le 31$, agreement $\ge 40$; 32 points, degree $\le 15$, agreement $\ge 20$; 16 points, degree $\le 7$, agreement $\ge 10$; 8 points, degree $\le 3$, agreement $\ge 5$; 4 points, degree $\le 1$, agreement $\ge 2$. Because the slack is rounded up, the three quotients of 16, 32 and 64 points sit **exactly at $5/8$**, not at $0.64$.
4. At the small levels the hypothesis is either automatic or a finite statement about which nothing is known. By Lemma 3.2 every list of the 4, 8, 16, 32-point levels has at most $13$, $55$, $960$, $328733$ members. So PL$(f)$ with $f \ge 960$ is automatic on quotients of at most 16 points, while PL$(7)$ there is a nontrivial claim about multi-valued words on 16 points for which no evidence exists either way. This is the reason for the stopping level of section 1.5.

5. **The subspace-polynomial families are consistent with it. [proved]** For the word $X^{2^v}$ and the members $X^{2^v} - L_V$, $V \le D$ of dimension $v$ (rate $2^{v-1}/n$, agreement $2^v/n$, the lists of size $2^{v(N-v)}$ that are superpolynomial for $v \approx N/2$), all differences are linearized polynomials, and for linearized $A, B$ that are not proportional $A/B$ is unchanged by $X \mapsto X + a$ iff $A(a) = B(a) = 0$. So a triple $(V_0, V_1, V_l)$ is bad as soon as $V_0 \cap V_1 \cap V_l \ne 0$, which is forced when $N > 3(N - v)$. The slack fraction of these lists equals their rate $2^{v-1-N}$, so at slack fraction $\ge \sigma$ the codimension is at most $\log_2(1/\sigma) - 1$ and every triple is bad in dimension above $3\log_2(1/\sigma)$. They are not a counterexample to PL at fixed $\sigma$, and they show why the hypothesis must be at fixed slack fraction and why $f$ must be allowed to depend on $\sigma$.

**Multi-valued to ordinary (note 39 Lemma 1.4). [proved]** Choosing one point per coset uniformly, $\mathrm{agr}_w(P)$ has mean $\mathrm{agr}_v(P)/m \ge \kappa + \sigma n'$ and is at most $n'$; Markov on $n' - \mathrm{agr}_w$ gives $\Pr[\mathrm{agr}_w \ge a] \ge (\kappa + \sigma n' - a + 1)/n' \ge \sigma/2$ for $a = \kappa + \lceil\sigma n'/2\rceil$. A sublist of a primitive list is primitive and the periods are the same. So $f_j \le (2/\sigma) f^{\mathrm{ord}}$ at slack fraction $\sigma/2$. Three things to keep in mind: the loss $2/\sigma$ is in $f$ and enters the bound to the power $3j_0$; the ordinary hypothesis is at **half** the slack (at $\tau = 0.64$: agreement fraction $0.57$ on the quotients, well below $5/8$, where the known lists are much larger); and it cannot be iterated to bound lists, as the note says. Corollary 1.5 is a correct consequence.

### 1.5 The theorem I would sign

**Theorem R. [proved, conditional]** Let $F$ be a field of characteristic two, $D \subset F$ an $\mathbb{F}_2$-subspace of dimension $N$, $n = 2^N$, $2 \le k \le n$, $k \le T \le n$, $\Delta = T - k + 1$, $J = \lceil\log_2 k\rceil$, $1 \le j_0 \le \min(J, N - 1)$ and $f \ge 2$ an integer. Call *level-$j$ instance* a quadruple $(U, \kappa, v, \mathcal{P})$ with $U \le D$ a subspace of dimension $j$, $0 \le \kappa \le \lfloor(k-1)/2^j\rfloor$ ($\kappa = k - 1$ if $j = 0$), $v : D \to F \cup \{\bot\}$, and $\mathcal{P}$ a set of polynomials $P \in F[Y]$ of degree at most $\kappa$, each with $\#\{x \in D : v(x) = P(L_U(x))\} \ge 2^j\kappa + \Delta$. Call three members *bad* if $(P_c - P_a)/(P_b - P_a)$ is a constant or is unchanged by $Y \mapsto Y + a'$ for some nonzero $a' \in L_U(D)$.

*Hypothesis* PL$(f, j_0)$: for every $j < j_0$, every level-$j$ instance with $\lvert\mathcal{P}\rvert > f$ contains a bad triple.

*Conclusion*: every word $w : D \to F$ has at most
$$\binom{f+1}{3}^{j_0}\ 2^{Nj_0 - j_0(j_0-1)/2}\ \bigl(B_{j_0} + 1\bigr), \qquad B_{j_0} = \max_{0 \le \kappa \le \lfloor(k-1)/2^{j_0}\rfloor}\ \prod_{i=0}^{\kappa}\frac{n - 2^{j_0}i}{\Delta + 2^{j_0}(\kappa - i)},$$
polynomials of degree $< k$ agreeing with it on at least $T$ points. For $j_0 = J$, $B_J = n/\Delta$ and this is note 39 Theorem 1.3.

*Proof.* Sections 1.2 and 1.3; the base case is Lemma 3.2 applied to the level $j_0$ with its supremum over degrees. $\square$

**Corollary R0 (ordinary words). [proved, conditional]** In the same setting let $\sigma = \Delta/n$ and suppose that for every $j < j_0$, every subspace $U \le D$ of dimension $j$, $D' = L_U(D)$, $n' = n/2^j$, every $1 \le k' \le \lfloor(k-1)/2^j\rfloor + 1$ and every ordinary word $w' : D' \to F$, every set of more than $f_0$ polynomials of degree $< k'$ agreeing with $w'$ on at least $k' - 1 + \lceil\sigma n'/2\rceil$ points contains a bad triple (periods in $D' \setminus 0$). Then the conclusion of Theorem R holds with $f = \lfloor 2f_0/\sigma\rfloor$.

**Remarks.** (a) Degree slack: for codewords of degree $\le k - 1 + \ell$ replace $k$ by $k + \ell$; the condition $j_0 \le N - 1$ takes care of $k + \ell > n/2$. (b) Single lane; the interleaved case costs the factor 2 of the brief. (c) The theorem is about one domain: the hypothesis is asked of the subspaces $L_U(D)$ of the given $D$ only. (d) A list bound at the levels implies PL with $f$ the bound, and PL implies a list bound $2^{O(N^2)}$: the hypothesis is weaker than what it yields only by this quantitative trade, as note 39 says.

**Numbers. [proved arithmetic, `46_numbers.py`, exact integers]** $N = 25$, $k = 2^{24}$, $T = \lceil 0.64n\rceil = 21474837$, $\Delta = 4697622$, $J = 24$, $NJ - J(J-1)/2 = 324$.

| $f$ | $j_0 = J = 24$ (the notes) | $j_0 = 21$ | $j_0 = 20$ | $j_0 = 19$ | $j_0 = 18$ | best |
| --- | --- | --- | --- | --- | --- | --- |
| 7 | $2^{466.4}$ | $2^{446.9}$ | $2^{444.5}$ | $2^{449.5}$ | $2^{470.5}$ | $2^{444.5}$, hypothesis on quotients of $\ge 64$ points |
| 16 | $2^{552.9}$ | $2^{522.5}$ | $2^{516.5}$ | $2^{518.0}$ | $2^{535.3}$ | $2^{516.5}$, quotients of $\ge 64$ points |
| 133 | $2^{773.0}$ | | | | | |
| 134 | $2^{773.7}$ | $2^{715.8}$ | $2^{700.6}$ | $2^{692.8}$ | $2^{701.0}$ | $2^{692.8}$, quotients of $\ge 128$ points |
| 1000 | $2^{982.5}$ | $2^{898.5}$ | $2^{874.6}$ | $2^{858.1}$ | $2^{857.6}$ | $2^{857.6}$, quotients of $\ge 256$ points |

Ordinary words (Corollary R0): $f_0 = 133$ gives $f = 1899$ and, at $j_0 = 21$ with the base $(n/\Delta)^8 = 2^{22.7}$ of note 39, $2^{969.5}$ (the note's $2^{970}$); $f_0 = 134$ gives $f = 1914$ and $2^{970.3}$; with the base of Lemma 3.2 and the best level, $2^{908.1}$ at $j_0 = 18$ for $f_0 = 134$ and $2^{754.9}$ at $j_0 = 19$ for $f_0 = 20$.

### 1.6 What should be changed in the notes (reduction part)

1. **$f = 133$ is not the truth at $(32, 17, 19)$.** `46_triples 5 1 ... prim 600` finds a primitive sublist of **134** members in the list of note 39 Proposition 4.1 at $n = 32$ (132 members with a double point and 2 sets, all $392084$ triples re-verified), so $f_{N-5} \ge 134$ at $(k, T) = (n/2 + 1, 19n/32)$, and the true value is unknown (greedy search). The hypothesis PL$_0(133)$ of Corollary 1.5, which as written includes $k' \le \rho 2^{N'} + 1$ and therefore $(32, 17, 19)$ at $\sigma = 0.14$, is false; with $134$ in its place the number is $2^{970.3}$. Severity: cosmetic for the number, but it shows that the constant is a lower bound, not a measured value. **[checked]**
2. **The "$+1$" in $k' \le \rho 2^{N'} + 1$ is not needed when $k = 2^{N-1}$**: then $\lfloor(k-1)/2^j\rfloor + 1 = k/2^j$, and the 32-point instance forced by PL$_0$ at $\sigma = 0.14$ is $(32, 16, 18)$, where the largest list I know is the $2395 = 105 \cdot 32 - 965$ members of $X^{16}L_U$, $\lvert U\rvert = 2$ (recomputed, `46_tops 5 1 16 18 xlw 16 1`), whose best primitive sublist in 16 greedy runs has $20$ members. **[checked]**
3. **$f = 7$ and $f = 16$ are placeholders.** $7$ is the generalized Singleton value at $(32, 17, 19)$, a different parameter point; $16$ is a list size at $21/32$, not a primitive list. At $\tau = 0.64$ with $j_0 = J$ the hypothesis covers multi-valued words on 4, 8 and 16 points, where only Lemma 3.2 is known. I found nothing that refutes PL$(7, 20)$ (the sublists of the list of Proposition 4.1 that are lists in degree $< n/2$ have $2$, $4$ or $7$ members at $n = 32$ and $64$, and the classes of 7 are $W$-invariant, with every triple bad: `46_triples ... classes`), and nothing that supports it beyond the families of note 39. **[checked for the family; the hypothesis itself conjectured]**
4. **State the stopping level.** Theorem 1.3 already has the parameter $j_0$; the notes evaluate it only at $j_0 = J$, where each of the last levels costs a factor $\binom{f+1}{3}2^{N-j}$ although Lemma 3.2 bounds those levels outright. Section 1.5 gives the optimum. This is an improvement of 22 to 81 bits and, more important, it removes the base-index effect of the smallest dimensions from the hypothesis (the effect that note 39 Remark 1.7 identifies as the source of $f \ge 133$).

## 2. Note 39 Proposition 4.1

Claim: on a generic subspace the list of $w = X^{n/2}L_W$, $\lvert W\rvert = n/8$, in degree $\le n/2$ at agreement $\ge 19n/32$ consists of $56n - 392$ sets of size $5n/8$ and $14336\binom{N-3}{2}_2$ multisets $1_{H'} - 1_A + 1_C + 1_{A'}$ of support $19n/32$, every member invariant under a subspace of $W$ of size at least $n/32$.

### 2.1 $n = 32$: exhaustive, three ways

**[checked]** (a) `46_tops 5 1 17 19 xlw 16 2` enumerates all $347373600$ subsets $S$ of 19 points. A member is $w - c = Z_S\,(X - r)$ and exists iff the coefficients of $Z^2, Z^3$ of $\mathrm{rev}(w)/\Psi_S$ vanish; $r$ is then read off and located. Result: $42336$ passing subsets, $15736$ members ($14336$ of agreement 19 with one double point, $1400$ of agreement 20), none with a root outside $D$. The same list, as subsets of $\mathbb{F}_2^5$ and bit for bit, on a second random domain (seed 7) and on the real shape $\mathrm{span}(1, x, \dots, x^4)$. (At $n = 32$ "no root outside $D$" is trivial: $r = e_1(S) \in D$.) (b) `46_rm 5 1 17 19 xlw 16 2`, the power-sum method of section 2.2: the same $15736$ members, identical dump. (c) The oracle `02_lists.c` of note 02 (exhaustive interpolation over $\binom{30}{17}$ index sets, 188 s) on my points and my word: $15736$ agreement sets, identical to mine. (d) `46_family 5 1` generates the claimed family from its combinatorial description alone: $56 + 1344 + 14336$ members, all distinct, all verified in $\mathrm{GF}(2^{64})$, and the file is identical to the exhaustive list. Profile: $(19, 2, 1) : 14336$, $(20, 1, 2) : 1344$, $(20, 1, 4) : 56$ (support, largest multiplicity, order of the period group), as in note 39.

### 2.2 $n = 64$: exhaustive, by a method of my own

The note verifies the family at $n = 64$ and relies on the proof for completeness. I wanted a completeness check that uses neither Theorem W, nor Theorem S, nor the classification. **[proved; this is the design of `46_rm.c`]**

A member is $P = w - c$, monic of degree $40$, with $e_j(\text{roots of }P) = t_j$ for $j \le 7$ ($\mathrm{rev}(w) = \sum t_jZ^j$) and at least $38$ distinct roots in $D$. Let $m \in \mathbb{F}_2^D$ be the parity of the multiplicities of its roots in $D$. In characteristic two the power sums are **linear over $\mathbb{F}_2$ in $m$**: $p_j = \sum_x m_x x^j$ plus the contribution of the roots outside $D$, and $p_j$ of all roots is a polynomial in $t_1, \dots, t_j$ (Newton), namely its value $\pi_j$ on the roots of $w$ itself. At most two roots are not among the 38, and a single root outside $D$ is impossible ($e_1 = t_1$ lies in $D$). So there are two cases.

- *Case A: the roots outside $D$ have even multiplicity* (none, or one double root). Then $\sum_x m_x x^j = \pi_j$ for $j = 1, 3, 5, 7$: $256$ linear equations over $\mathbb{F}_2$ in $64$ unknowns, solved exactly on the numeric domain. The solution space has dimension $23$ on a random domain. For each of its elements of weight $36, 38$ or $40$, $R = \mathrm{rev}(w)/\Psi_m$ must be the square $\Psi_\nu(Z)^2$ of the missing part $\nu$ (mass 2, 1 or 0); its odd coefficients and $R_6$ must vanish, $e_i(\nu) = \sqrt{R_{2i}}$, and the roots of $\nu$ are located in $D$ or outside.
- *Case B: two distinct roots $r, r + d$ outside $D$*, and 38 simple roots in $D$. Then $d = \sum_x m_x x \in D \setminus 0$, the third power sum gives $h_2 = r(r + d) = (\pi_3 + d^3 + \sum m_x x^3)/d$, and the fifth becomes $\sum_x m_x(x^5 + d^2x^3 + x^6/d) = \pi_5 + d^5 + d^2(\pi_3 + d^3) + (\pi_3 + d^3)^2/d$, again linear over $\mathbb{F}_2$ because squaring is. For each of the 63 values of $d$ the system is solved; on its solution space $h_2$ takes at most $2^5$ values, each is enumerated, the seventh power sum adds a linear equation, and every solution of weight 38 is verified in full ($\Psi_m(1 + dZ + h_2Z^2) \equiv \mathrm{rev}(w) \bmod Z^8$). Solutions whose $r$ lies in $D$ are multiset tops already found in case A, which gives a built-in test: their number must be $780$ per simple member plus $1$ per member with two double points.

**[checked]** `46_rm 6 1 33 38 xlw 32 3` (two minutes on four threads), random domain: case A examines $1230712$ parity vectors and finds $103544$ members, $3192$ simple and $100352$ with two double points, **none with a root outside $D$** and none of any other shape (no member of support 39, no triple point). Case B verifies $562303392$ sets of weight 38 and finds $2590112$ solutions, all with $r \in D$: $2489760 = 780 \cdot 3192$ with the pair outside the set and $100352$ with the pair inside, exactly the prediction, and **$0$ members with two distinct roots outside $D$**. The complete list is identical, as a file, to the family generated by `46_family 6 1` ($56 + 3136 + 100352$, all verified in $\mathrm{GF}(2^{64})$, profile $(38, 2, 2) : 100352$, $(40, 1, 4) : 3136$, $(40, 1, 8) : 56$). The same on a second random domain (seed 2), with the same numbers.

So at $n = 64$: exactly $103544 = 56 \cdot 64 - 392 + 14336 \cdot 7$ members, no member outside the classification, no member of agreement 39, every member a multiset top with a period group of order at least $2 = n/32$. This also confirms Corollary 2.4 (Theorem S) in a case where it is not trivial ($r = 2$).

**Real shape.** `46_rm 6 0 33 38 xlw 32 3 maxe 2` on $\mathrm{span}(1, x, \dots, x^5)$: case A (solution space of dimension 25, $4964280$ vectors) gives the same $103544$ multiset tops, set for set. Case B is **not completed** there: $h_2$ has up to $2^6$ free values per direction, the solution spaces are larger, and the run exceeds the budget (I stopped it after 30 CPU-minutes). So on the real shape at $n = 64$ members with two distinct roots outside $D$ are not excluded by my computation. The proposition does not claim the real shape.

### 2.3 $n = 128$, the proof, and the consequences

**[checked]** `46_family 7 1`: $56 + 6720 + 501760 = 508536$ members, all distinct, **all** verified in $\mathrm{GF}(2^{64})$ (15 coefficients each), profile $(76, 2, 4) : 501760$, $(80, 1, 8) : 6720$, $(80, 1, 16) : 56$. Completeness at $n = 128$ is not checked by computation (the power-sum method would need $2^{30}$ parity vectors with excess up to 4).

**[proved]** I read the proof of Proposition 4.1 in full: the reduction ($w \equiv Z_{\mu_0}$ modulo degree $\le n/2$, Corollary 2.4 applies since $9n/16 < 19n/32$, Theorem W and its converse at depth $n/8 - 1$), the coset masses (the three patterns $(4^5, 0^3)$, $(4^3, 2^4, 0)$, $(5, 3^4, 1^3)$ are the only ones; I redid the enumeration), the three estimates of $U$ (the identities $nU = 16\sum(\mu - 1)^2$, $nU = 2n + 16X$, $nU = 3n + 16Y$ are right), the structure of case (O), the converse and the count $14 \cdot 16\binom{N-3}{2}_2 \cdot 64$. It is correct. It rests on Theorem W with its converse (note 02, refereed in note 21) and on Corollary 2.4 (section 3). My description of the $448(n/8 - 1)$ members of pattern (E2), derived from the proof and used in `46_family.c`: half of a coset $H'$ of a hyperplane $H \supset W$ cut by a functional outside $W^\perp$, plus three of the four cosets of $W$ off $H'$.

**Period-free part. [checked]** `46_triples 6 1 ... pairs`: for a pair of $W$-invariant members at $n = 64$, $B = 0$ and $\lvert\Pi(\xi_l)\rvert$ is $2$ for $100352$ thirds, $4$ for $3136$, $8$ for $52$, with $2$ collinear, the row of note 39 exactly; $B = 0$ for 12 further $W$-invariant pairs. At $n = 32$: $B = 14336$ for the first $W$-invariant pair, between $13568$ and $14336$ over 300 such pairs, and `bmin` gives the minimum over all $15735$ partners for one member of each of the three types: $13568$, $13968$, $14977$, the three numbers of note 39. (That these three members represent all pairs is the orbit argument of the note, which I accept and did not recheck.) Corollary 4.2 is a one-line consequence of the proposition and is right. Corollary 4.3: the counting bound ($14, 10, 8, 8$, then $2$ from $n = 1024$) is right, and my greedy search gives $14$ at $n = 64$ and **$134$ at $n = 32$** (note: $133$).

## 3. Note 39 Theorem 2.3 and Corollaries 2.4 to 2.6

### 3.1 The proof

**[proved]** I checked every step.

- *Lemma 2.1.* $v_{f,i} = \sum_s f(s)s_i/(1 + \ell_sZ)$ with coefficients in $\mathbb{F}_2$, and the even part of $1/(1 + \ell Z)$ is its square. Right.
- *Lemma 2.2.* $\partial_i(C^2) = 0$ gives $\sum_s f(s)s_i\ell_s^d = 0$ for $d \le m' - 2$; the monomials $\prod_a b_{\kappa(a)}^{2^a}$ are distinct for distinct $\kappa$; so $f \bmod 2$ is orthogonal to all monomials of degree $\le w + 1$, lies in $\mathrm{RM}(N - w - 2, N)$, and is a sum of indicators of flats of dimension $\ge w + 2$. **Simplification:** the appeal to Theorem W is not needed. For a flat $V + u$ of dimension $d$, $\Psi = \mathrm{rev}(L_V) + L_V(u)Z^{2^d} \equiv 1 \pmod{Z^{2^{d-1}}}$ directly, so $\Psi_F \equiv 1 \pmod{Z^{2^{w+1}}}$ and Theorem 2.3 is independent of note 02.
- *Step 1.* Uniqueness of the Padé form for $\alpha + \beta < m'$, descent to $K$, and grading by the automorphism $b_i \mapsto \lambda b_i$ of $K(\lambda)$: right, including for irreducible factors (they stay irreducible over $K(\lambda)$, and $\lambda = 1$ identifies the factor).
- *Step 2.* The formula for $v_{\mathrm{even}} - v^2$ is right; each term is a proper fraction, the numerator has degree $\le 2(\alpha + \beta) - 2 \le m' - 2$ and vanishes modulo $Z^{m'-1}$, so it is zero, and the partial fractions have disjoint poles. This is the only place where $m' \ge 2(\alpha + \beta)$ is used.
- *Step 3.* Euler: $E\omega = \omega$ from $\omega\tilde p'(\omega) = \sum_j jc_j\omega^{d-j}$ in characteristic two; $x = \omega - \sum(\partial_i\omega)b_i$ has $Ex = 0$ and $Ex = x$. Right.
- *Step 4.* $b$ is a 2-basis of every finite separable extension of $K$, so $\partial_i\omega = 0$ for all $i$ gives $\omega = \theta^2$ with $\theta \in K(\omega)$, and $p$ is the square of $\prod(1 + \theta Z^{q/2}) \in K[Z]$. Right.
- *Step 5.* $\lceil m'/2\rceil \ge \alpha + \beta \ge 2(\deg A_2 + \deg B_2)$, and square roots with constant term 1 are unique. Right.

Corollary 2.4 ($\beta = 0$, $\mathrm{rev}(h) \equiv \Psi_{\mu_0 - 1_S}$), Corollary 2.5 (the reduced fraction of $\mathrm{rev}(h_1)/\mathrm{rev}(h_2)$ has $\alpha + \beta \le r_1 + r_2$; $M \le T + (T - k + 1)/3$ is $M - k + 1 \ge 4(M - T)$) and Corollary 2.6 (twist, then note 12 Theorems 2.4 and 2.5, which are stated for multiset top lists of any mass and were refereed in note 21; lanes by note 12 Proposition 1.1, applied before Corollary 2.5 so that the combined word is the one that is shown to be a twisted top) are correct consequences. **One arithmetic slip:** at $\tau = 0.64$, $1/(16\epsilon^2) = 277.8$, so the bound is $277$ codewords, not $278$.

### 3.2 Numerical tests

**[checked]** *$n = 16$, all functions.* `46_pade16 1`: for each of the $3^{15} = 14348907$ functions $f : D \setminus 0 \to \{-1, 0, 1\}$ on a random basis and each type $(\alpha, \beta)$, $\alpha \ge \beta$ (the other half is $f \mapsto -f$), the program decides by exact linear algebra whether $\Psi_f$ has a rational approximant of that type modulo $Z^{m'}$, reduces it and tests whether numerator and denominator split over $D$.

| $\alpha + \beta$ | $m'$ | covered by the theorem | approximants, types $(\alpha + \beta, 0)$, $(\alpha + \beta - 1, 1)$, $(2, 2)$ | not split over $D$ |
| --- | --- | --- | --- | --- |
| 2 | 4 | yes | $171549$, $268569$ | $0$, $0$ |
| 3 | 6 | yes | $5428$, $12123$ | $0$, $0$ |
| 4 | 8 | yes | $16033$, $42538$, $60243$ | $0$, $0$, $0$ |
| 3 | 5 | no | $5428$, $12123$ | $0$, $0$ |
| 4 | 7 | no | $16033$, $42538$, $60243$ | $0$, $0$, $0$ |
| 4 | 6 | no | $85509$, $42538$, $188163$ | $69476$, $0$, $127920$ |

Most approximants are nontrivial (support of $f$ larger than $\alpha + \beta$ for $14092$ of $16033$ at type $(4, 0)$, and so on). So the theorem holds in every covered case, fails at $m' = 2(\alpha + \beta) - 2$ (as the note says), and **does not fail at $m' = 2(\alpha + \beta) - 1$** for these functions: the approximants modulo $Z^5$ and $Z^7$ are the same as modulo $Z^6$ and $Z^8$. "Sharp" in the note should read "sharp up to one". **[conjectured]** $m' \ge 2(\alpha + \beta) - 1$ suffices.

*$n = 32$, one side (Corollary 2.4), all subsets.* `46_tops` (section 2.1) for other words, generic domain: $X^{15}$, $k = 12$, agreement $\ge 13$ ($m' = 4$, $r \le 2$): $65131$ members, $52080$ with $r = 2$ and $8680$ with $r = 1$, all roots in $D$. $X^{16}L_W$: $k = 15$: $48$ members with $r = 2$; $k = 13$ ($m' = 8$): $48$ with $r = 2$ and $35$ with $r = 4$; all roots in $D$. $X^{15}$, $k = 10$, agreement $\ge 12$ ($m' = 6 = 2r$): only the 31 flats. These are the numbers of note 39 section 2.7. *$n = 64$:* section 2.2 ($r = 2$, $m' = 8$).

**Sharpness. [checked]** $X^{15}$, $k = 10$, agreement 11 ($r = 4 = m'/2 + 1$): $93248$ members, each with four roots outside $D$; $k = 8$, agreement 9: $26040$ with six roots outside $D$; $X^{16}L_W$, $k = 14$ ($m' = 7$, $r = 4$, not covered): $35$ members, all roots in $D$. As in note 39 section 2.8.

**The real shape. [checked]** $\mathrm{span}(1, x, \dots, x^4)$, $X^{15}$, $k = 12$: $345841$ members, $280710$ of them with two roots outside $D$ at $r = 2$ (covered range); $k = 10$, agreement 12: $100$ members with three roots outside $D$. As in the note. **New:** the failure is already there at $n = 16$. On $\mathrm{span}(1, x, x^2, x^3)$ the word $X^9$, $k = 6$, has $9$ members of agreement 7 with two roots outside $D$ ($m' = 4 = 2r$; none on a random domain), $X^{11}$, $k = 8$, has $25$; and `46_pade16 0` finds $26988$ functions with a type $(2, 0)$ approximant modulo $Z^4$ that does not split, and $48$ of type $(4, 0)$ modulo $Z^8$. Types $(1, 1)$, $(3, 0)$, $(2, 1)$, $(3, 1)$, $(2, 2)$ show no failure there. The note's remark that the pair test finds no violation on the real shape at $n = 16$ is about the two-sided statement at $m' = 4r$ and is consistent with this.

## 4. Note 37, the formal model

### 4.1 Proofs

**Normal form, Lemma 4.1 (transfer). [proved]** The uniqueness argument gives $\xi \in K(X)$ when $\nu \ge 2\delta + 1$; the contents are pairwise coprime; $v_i = \gamma_iZ_ih_i$ with $\deg h_i \le s_i$. Reduction modulo a nonzero $z \in D$ is a homomorphism to a polynomial ring, injective on classes $\{x, x + z\}$. Part (1): a class that meets $R_i$ and $R_j$ is a root of $\bar v_l \ne 0$ in all three sub-cases ($z$ divides neither content, or one of them) and contains no point of $R_l$, so it is a root of $\bar h_l$; distinct $x$ give distinct classes because $x + z \in R_j$ is not in $R_i$. Part (2): $\bar\gamma_i\bar Z_i\bar h_i = \bar\gamma_j\bar Z_j\bar h_j \ne 0$ and a class of $R_i$ that misses $R_j$ is a root of $\bar h_j$ with multiplicity at least its number of points in $R_i$. Correct.

**Lemma 4.2 (rigidity). [proved]** $\Omega = v_0(X)v_1(X + a) + v_1(X)v_0(X + a)$ has degree $\le 2\delta - 1$ and vanishes on the three disjoint sets. Correct, on every subspace domain.

**Theorem 4.3 (gap). [proved, with one change]** Steps 1 to 4 are right; I re-derived the inequalities, in particular $\lvert\mathcal{Z}_0\rvert \ge r_2 - s_0n/r_1$ (needs $r_1(1 + r_2) \ge s_0n$, true since $s_0n < \delta^2/4$ and $r_1r_2 \ge 0.83\delta^2$), the count $\sum_i\lvert R_i \cap (R_i + a)\rvert \ge \nu - (s_0 + 2s_1 + 3s_2) \ge \nu - 2s$, the bound on $\lvert\mathcal{P}_2\rvert$ and the constants $0.123$, $0.274$. **The statement is false as written for $\delta > (6 + \sqrt{32})\,n \approx 11.7n$**: there $3\delta - \nu \le 3\delta < \delta^2/4n$ for every function, whatever its fibres. The proof uses $\delta < 2n$ in its second sentence ("$\delta/2 > \delta^2/4n$"). Add the hypothesis $\delta < 2n$ (or $\delta \le n$). For triple functions of codewords $\delta \le k - 1 < n$, so Theorem 5.1 is not affected. Severity: minor, statement only.

**Corollary 3.6 and Theorem 5.1. [proved]** The mean defect is $(L\theta n + T - k + 1)/(L - 1)$, exactly; the second moment bound, the cubic inequality $p^3 \le \tau^3 + 3\tau^2(p - \tau) + (1 + 2\tau)(p - \tau)^2$, the two Markov steps, $s_l \le d_{ij}$, $\deg G \le \lvert B\rvert + 2d^\ast$ (from $\gcd(ab, cd) \mid \gcd(a, c)\,bd$), $\delta \ge \tfrac67\beta n$, $\tfrac{9}{49} > \tfrac17$, the interval for $\delta$ and the averaging over pairs are all right. Corollary 3.6 is right (the fixed field of the translations by $\Pi^\ast$ is $F(L_{\Pi^\ast})$, and the count of note 04 Theorem 1.2 is the argument of Lemma 3.2 for an affine space of codewords).

### 4.2 The table of Theorem 5.1

**[proved arithmetic, `46_numbers.py`]** Johnson threshold at $N = 25$, rate 1/2: $T_J = 23726566$; $T = T_J - 175$ gives $T/n = 0.7071016$ and $\theta = 7.36 \cdot 10^{-6}$, as in the note. With the note's $\beta = 0.0875$: $\pi^\ast = n/8$, $\delta^\ast = 3$, Gaussian binomial times product $= 2^{72.69}$. The note's $g = 0.052$ corresponds to $\theta_1 \approx \theta/2$ and gives $2^{72.69}/0.052 = 2^{77.0}$, a valid bound. The theorem allows $\theta_1 \to 0$ here (the first term $1 + 2/\theta_1$ only has to stay below the second), which gives $g = 0.082$ and $2^{76.3}$; optimizing $\beta$ as well, $2^{76.2}$ at $\beta = 0.0777$.

| rate | $N$ | points below $T_J$ | note 37 | same $\beta$, $\theta_1 \to 0$ | remark |
| --- | --- | --- | --- | --- | --- |
| 1/2 | 25 | 175 | $2^{77.0}$ | $2^{76.3}$ | |
| 1/2 | 28 | 1399 | $2^{86.0}$ | $2^{85.3}$ | |
| 1/4 | 25 | 376 | $2^{74.1}$ | $2^{73.5}$ | |
| 1/4 | 28 | 3015 | $2^{83.1}$ | $2^{82.5}$ | |
| 1/8 | 25 | 237 | $2^{19.6}$ | $2^{18.0}$ (largest admissible $\theta_1$) | no power of two in $[0.0627n, n/8 - 1]$: confirmed |
| 1/16 | 25 | 225 | $2^{20.2}$ | $2^{18.6}$ | no power of two in $[0.0314n, n/16 - 1]$: confirmed |

Every number of the note is a valid evaluation of the theorem. The window is also a little wider than stated: $g > 0$ is possible up to $437$, $942$, $867$, $566$ points below the Johnson threshold at rates $1/2, 1/4, 1/8, 1/16$ ($N = 25$, $\theta$ up to $1.8 \cdot 10^{-5}$, $2.8 \cdot 10^{-5}$, $1.8 \cdot 10^{-5}$, $8.4 \cdot 10^{-6}$), against the note's $1.2 \cdot 10^{-5}$, $1.9 \cdot 10^{-5}$, $8.4 \cdot 10^{-6}$, $5.6 \cdot 10^{-6}$. At rates $1/2$, $1/4$ and $1/16$ the note's values are mine divided by $1.5$, which is the choice $\theta_1 = \theta/2$; at rate $1/8$ the note's value is smaller, I assume because $\beta$ is pinned there by the power-of-two condition. None of this changes the assessment of the note: the window is a relative $10^{-5}$.

### 4.3 Numerical tests

**[checked]** *Counting step of Theorem 4.3.* For all $59530$ parameter sets $(n \le 1024, \delta, s_0 \ge s_1 \ge s_2)$ with $s < \delta^2/4n$ and $\nu \le n$, with the exact bounds of Steps 1 and 3: $\lvert\mathcal{Z}_0\rvert + \lvert\mathcal{Z}_1\rvert - 1 - \lvert\mathcal{P}_2\rvert > \delta/2$ and $\delta \ge 3s$, no failure. (The note reports $58862$ sets for $N \le 10$; mine are $3 \le N \le 10$, $\delta \ge 2$, $\nu \le n$. I did not track down the difference in the enumeration convention; neither run has a failure.)

*Lemmas 4.1, 4.2 and Theorem 4.3 on real triple functions.* `46_triples ... transfer 3000`: for 3000 random non-collinear triples of the list at $n = 32$ and 3000 at $n = 64$ (random basis), the gcd, the three fibres in $D$, $\delta$, $s_i$ and the period group are computed, and for each of the $31$ or $63$ directions the existence of an admissible type is tested. No triple has a direction without admissible type; $1753$ and $3143$ directions have a forced transfer type; Lemma 4.2: $110$ and $246$ directions satisfy the hypothesis and all are periods; Theorem 4.3: $6$ and $1$ functions have $s < \delta^2/4n$ and all are flats, and the smallest value of $4ns/\delta^2$ over non-flats is $10.0$ and $11.8$; $\nu - 2\delta - \lvert\Pi\rvert \le 0$ throughout (Conjecture P of note 17, with equality attained). **The power of the Lemma 4.1 test is limited:** random disjoint sets of the same sizes violate it for only $20$ and $49$ of the 3000 triples, because for most triples of these lists $s$ is large and the constraints are nearly vacuous. The note's own test on lifts ($116$ of $196$ controls violate) is the stronger one; mine is an independent confirmation on a different source of functions.

## 5. Note 37, the negative result

**Proposition 2.1, Corollary 2.2, Proposition 2.3. [proved]** The two Hoeffding bounds and the union bound are right ($2Le^{-2t^2/n} + L(n - 1)e^{-t^2/n} \le L(n + 1)e^{-t^2/n} < 1$ for $t^2 = n\ln(2Ln)$), the perturbed word has no new list member at the lower threshold beyond the old list at that threshold, and $(1 - \lambda)^2(1 + \lambda/2) \le 1 - \tfrac54\lambda$ holds for $\lambda^2 \le 1/2$. The conclusion is right: a dichotomy "all but $B$ members have an agreement set invariant up to $\eta n$ in some direction" at agreement $\tau'$ is, without any recursion, a list bound at $\tau'(1 + 4\eta + o(1))$, so it cannot serve as the inductive hypothesis of the set recursion of Corollary 1.2 (which is itself correct). The descent on differences is not touched: the codewords, hence the triple functions, do not change.

**[checked]** *Exact periods at $n = 64$* (`46_triples 6 1 ... perturb`): all $103544$ members have an agreement set with a nonzero period; after changing the word on 6 random points only $360$ still do, after 3 points $5517$ (the members whose lost points form an invariant set), while every member is still a member and $B = 0$ for the $W$-invariant pair, the functions being the same. *The quantitative statement* (`46_perturb`): members of the families (a2) and (b) sampled from their coordinate description, self-intersections by Walsh-Hadamard autocorrelation.

| $n$ | $\lambda$ | members | exact period before, after | mean $\lvert S'\rvert/\lvert S\rvert$ | $\max_a\lvert S' \cap (S' + a)\rvert/\lvert S'\rvert$, mean and worst | largest $\max_a\lvert S' \cap (S' + a)\rvert - (1 - \lambda)^2\lvert S\rvert$, and $t$ |
| --- | --- | --- | --- | --- | --- | --- |
| $2^{12}$ | 0.1 | 400 | 400, 0 | 0.9020 | 0.9091, 0.9181 | 58.1, 247.9 |
| $2^{14}$ | 0.1 | 400 | 400, 0 | 0.9009 | 0.9053, 0.9109 | 148.3, 518.2 |
| $2^{16}$ | 0.02 | 200 | 200, 0 | 0.9795 | 0.9801, 0.9814 | 84.9, 1058.1 |

Before the perturbation the ratio is $1$ (exact invariance under $n/32$ or $n/16$ translations); after it, it is $1 - \lambda$ up to fluctuations, both inequalities of Proposition 2.1 hold with room, and no member keeps any exact period. Confirmed.

## 6. Errors, gaps and corrections

| # | where | what | severity |
| --- | --- | --- | --- |
| E1 | note 37 Theorem 4.3, statement | false for $\delta > 11.7n$ (hypothesis vacuous); add $\delta < 2n$. Proof and all uses unaffected | minor |
| E2 | note 39 section 1 "Numbers", Remark 1.7, section 6, Corollary 4.3 | "$133$" is a greedy value; I find $134$. PL$_0(133)$ as stated in Corollary 1.5 is false; with $134$: $2^{773.7}$ and $2^{970.3}$; the true constant is unknown | minor (number), but every use of 133 as a value of $f$ should say "at least" |
| E3 | note 39 section 1 "Numbers", summary | $f = 7$, $16$ are placeholders, not supported at $\tau = 0.64$; with $j_0 = J$ the hypothesis includes multi-valued words on 4, 8, 16 points | presentation |
| E4 | note 39 Theorem 1.3, use | evaluate at the best $j_0$ with the base of Lemma 3.2: $2^{444.5}$, $2^{516.5}$, $2^{692.8}$ instead of $2^{466}$, $2^{553}$, $2^{773}$, and $2^{908}$ instead of $2^{970}$, with a smaller hypothesis | improvement |
| E5 | note 39 Corollary 1.5 | $k' \le \rho 2^{N'} + 1$: the $+1$ is not needed for $k = 2^{N-1}$ and it is what brings $(32, 17, 19)$ into the hypothesis | minor |
| E6 | note 39 Corollary 2.6, the line after it and section 6 | $277$, not $278$ | trivial |
| E7 | note 39 Lemma 2.2 | Theorem W is not needed (flats only, elementary) | simplification |
| E8 | note 39 section 2.8 | sharpness is "up to one": no failure at $m' = 2(\alpha + \beta) - 1$ at $n = 16$; the real shape fails already at $n = 16$ ($m' = 4$, $r = 2$) | precision |
| E9 | note 37 Theorem 5.1, table and "the windows end at" | valid; $\theta_1 = \theta/2$ is not optimal, bounds improve by $0.6$ to $1.6$ bits and the windows by a factor $1.5$ where no power-of-two condition binds | harmless |
| E10 | note 37 Lemma 3.2 as used with the supremum over degrees | the product is not monotone in the degree; use the maximum, or $(n/\Delta)^{\kappa+1}$ as the notes do | remark |

No claim of either note is false in substance. I found no gap in any proof.

## 7. What I did not do

- I did not re-prove Theorem W with its converse (note 02) nor Theorems A, A' of note 12; both were refereed in note 21 and are used as quoted. Proposition 4.1 for $n \ge 128$ depends on the first, Corollary 2.6 on the second. Theorem 2.3 depends on neither (E7).
- Completeness of the classification is computed at $n = 32$ and $64$ only; at $n = 128$ only membership.
- The orbit argument behind "exact minimum over all $1.2 \cdot 10^8$ pairs" at $n = 32$ is accepted; I recomputed the three minima over $3 \times 15735$ pairs.
- The $n = 64$ exhaustive search on the real shape covers multiset tops and double roots outside $D$, not two distinct roots outside $D$.
- I did not review note 39 section 5 (affine rank) and Proposition 3.1 beyond a reading (the proof of 3.1 is correct), nor note 37 section 6 beyond the list sizes ($31$, $504$, $1400$, $15736$, all reproduced).
- The hypothesis PL is not tested for multi-valued words anywhere, by anyone. The descent test of section 1.2 exercises the injection on multi-valued words, not the hypothesis.
- One computation went over the budget: the first real-shape run of `46_rm` at $n = 64$ (stopped after 30 CPU-minutes); the program now skips case B when it is that large and says so.

## 8. Reproduction

Under `doc/whir_soundness_gap_notes/scripts/`, C with the system compiler and Python 3 without dependencies. `46_run_all.sh [dir]` builds into a scratch directory and runs everything (about 15 minutes on four threads); `46_results.txt` holds the outputs quoted here.

- `46_gf.h`: $\mathrm{GF}(2^{64})$ (modulus $x^{64} + x^4 + x^3 + x + 1$), domains (seed 0 is the real shape), small polynomial arithmetic.
- `46_tops.c`: `./46_tops N seed k T pow M | xlw a j | xb a hexmask [dump file]`. All $T$-subsets; the full list of a top-type word with the roots of each member located. $n \le 32$.
- `46_rm.c`: `./46_rm N seed k T word [dump file] [maxe E]`. The power-sum linearization of section 2.2, for $M - T \le 2$.
- `46_family.c`: `./46_family N seed [dump file]`, $N = 5, 6, 7$. The claimed family from its description, every member evaluated.
- `46_pade16.c`: `./46_pade16 seed`. Theorem 2.3 for all $3^{15}$ functions at $n = 16$ (45 s).
- `46_triples.c`: `./46_triples N seed dumpfile pairs P | bmin | prim R | descent [b | pow M k] | transfer T | perturb lambda | classes [file]`. Periods of triple functions, best pairs, greedy primitive sublists with re-verification, the descent of Proposition 3.3 at every level, the lemmas of note 37 section 4, the small perturbation test, the sublists in degree $< n/2$.
- `46_perturb.c`: `./46_perturb N lambda count seed`. Proposition 2.1 at $n = 2^{12}$ to $2^{16}$.
- `46_numbers.py`: all the arithmetic (conditional bounds for every $f$ and $j_0$, Corollary 2.6, the table of Theorem 5.1 with its optimization, the counting step of Theorem 4.3, the ordinary problems inside the levels).

## References

Notes 02 (Theorem W and its converse), 04 (Theorem 1.2), 12 (Proposition 1.1, Theorems 2.4, 2.5), 17, 21 (the referee report on notes 02 and 12), 37 and 39 of this directory. No external source was used.
