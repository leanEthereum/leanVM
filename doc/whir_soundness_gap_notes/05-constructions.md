# 05. Attack constructions by theory: rate 1/2 and low rates

Researcher 05. Notation as in `00-lead-notes.md`: $K = \mathrm{GF}(2^{64})$, $D \subset K$ the $\mathbb{F}_2$-span of $1, x, \dots, x^{N-1}$, $n = 2^N$, rate $\rho = 2^{-R}$, $k = 2^\kappa = \rho n$ (written $k$ below, to keep $K$ for the field). $L_S = \prod_{s \in S}(X - s)$ is the locator of $S \subseteq D$ and $L_V$ the subspace polynomial of a subspace $V$. Every statement is tagged **[proved]**, **[checked]** (numerically, sizes given) or **[conjectured]**. Scripts are `scripts/05_*.py`, pure Python, each under two minutes. This report overlaps `01-literature-attacks.md` on the $5n/8$ family (found independently, I say below what is added) and takes two facts from it: the height-3 tree count and the biased-padding construction.

## 0. Summary

**Constructions (attack side).**

| rate | best $T/n$, list $\ge 2^{10}$ | list $\ge 2^{26}$ | list $\ge 2^{40}$ | floor $t$ at $2^{10}$ | Johnson |
| --- | --- | --- | --- | --- | --- |
| 1/2 | $5/8$: $56(2^N - 7) = 2^{30.8}$ (Thm 2.1); $0.6289$ with $1008$ members by [01, 3.4] | $5/8$ ($2^{30.8}$, degree $\le k$; $2^{30.1}$ genuine at $5n/8 - 1$) | $9/16$: $\ge 2^{72}$ (Prop 3.1), $2^{102.7}$ by [01, 3.3] | 160 (161 with [01, 3.4]) | 0.7071, 217 |
| 1/4 | $1/2$: $2^N - 1$ genuine at $n/2 - 1$, $2^{N+1} - 2$ at $n/2$ with degree $\le k$ | $3/8$: $56(2^N - 7) = 2^{30.8}$ (Cor 2.3); at $1/2$ the count is $2^{26} - 2$ for $N = 25$ | $5/16$: $(2^{N-1} - 2)^2 = 2^{48}$ (Prop 3.1) | 108 | 0.5, 108 |
| 1/8 | $1/4$: $\binom{N}{2}_2 = 2^{47.4}$ (flats) | $1/4$ | $1/4$ | 54 | 0.3536, 72 |
| 1/16 | $1/8$: $\binom{N}{3}_2 = 2^{67.6}$ (flats) | $1/8$ | $1/8$ | 36 | 0.25, 54 |

Sizes are evaluated at $N = 25$ as asked (the deployed level 0 has $N = 24 + R$, which only raises the counts). Floors are $t = \lceil 108 / \log_2(n/T) \rceil$. Nothing new was found inside the open windows $(5/8, 0.7071)$ at rate 1/2, $(1/4, 0.3536)$ at rate 1/8 and $(1/8, 1/4)$ at rate 1/16 beyond lists of constant size, and Section 6 proves that a whole class of constructions cannot enter them.

**What is new here.**

1. **The full common-top class of the word $X^{n/2} L_W$ at $5n/8$ (Theorem 2.1). [proved], [checked]** It has exactly $56(2^N - 7)$ members, $8/3$ times the tree count of [01] for one padding set, because all eight cosets of $W$ serve as padding for the same word. At $n = 32$ an exhaustive search over all $\binom{32}{20}$ sets shows that this class is the entire list of that word (1400 sets), so within common tops the family cannot be enlarged without changing the word. **[checked]**
2. **Complement duality (Proposition 1.3). [proved]** $S \mapsto D \setminus S$ maps common-top families at (rate $\rho$, agreement $\tau$) to common-top families at (rate $1 + \rho - 2\tau$, agreement $1 - \tau$), preserving the Johnson boundary. So the rate-1/2 window is the same problem as low-rate windows: a common-top family at rate 1/2 and $11n/16$ exists if and only if one exists at rate 1/8 and $5n/16$.
3. **The second coefficient of a subspace polynomial (Proposition 4.1). [proved], [checked]** For $V \subseteq D$ of codimension $r$, $c(V)^{2^r} = \sum_{H \not\supseteq V} \delta_H$, the sum over hyperplanes $H$ of $D$ not containing $V$, with $\delta_H = \prod_{d \in D \setminus H} d$, and the $\delta_H^{-2}$ form an $\mathbb{F}_2$-space. This answers idea 5 of the brief: flats of dimension $\kappa + 2$ share $c$ only by coincidence. In the real $K$ the fibers of $c$ are trivial apart from exactly one structural pair in codimension 2 ($N \le 13$) and three in codimension 3 ($N \le 10$) **[checked]**, and pigeonhole gives lists at $T = 4k$ only on the later ladder levels (Section 4.3).
4. **A rigidity theorem for formal families (Theorem 6.3). [proved], [checked]** Call a family of sets *formal* if it shares its top on every $\mathbb{F}_2$-subspace of every field of characteristic two (flats, coset unions with a prescribed label sum, trees, padded flats are all formal). A family that is not formal shares its top on at most a $2^{-39}$ fraction of the $N$-dimensional subspace domains of $K$ (Lemma 6.1). For formal families: at rate 1/2 and $T > 5n/8$ there are at most $n^2/(4(T - n/2)^2) \le 15$ members; at rate 1/8 and $n/4 < T \le 0.3536n$ at most 11; at rate 1/16 at most 8 for $n/8 < T < 3n/16$ and exactly 1 for $3n/16 < T < n/4$. So the dyadic thresholds $3/4, 5/8, 9/16, \dots$ at rate 1/2 and $2\rho$ at low rates are exactly where formal families stop being large, and any attack inside the open windows must use an algebraic coincidence specific to $D \subset K$.
5. **Caveat on item 4.** The theorem is about common tops in the strict sense (the word is a monic polynomial of degree $T$). Words of higher degree whose extra roots are again in $D$ (multiset tops) escape it: the biased padding of [01, 3.4] is such a family and reaches $0.6289n$ with $2^{10}$ members. The quantization lemma (6.2) still holds for multisets, and I conjecture the cap $5/8 + O(L^{-1/2})$ for all formal multiset families.

## 1. Tools

### 1.1 Reversed locators and the gap

For a finite multiset $m$ on $D$ of total mass $|m|$ write $\Lambda_m(X) = \prod_s (1 - sX)^{m(s)} = X^{|m|} L_m(1/X)$. The coefficient of $X^j$ in $\Lambda_S$ is $e_j(S)$, the coefficient of $X^{T-j}$ in $L_S$. Two $T$-sets *share their top with gap $g$* if $\Lambda_S \equiv \Lambda_{S'} \pmod{X^g}$, that is $L_S - L_{S'}$ has degree $\le T - g$. A family sharing its top with gap $g$, with $R$ the common part of degree $> T - g$, gives the list $\{C_S = R - L_S\}$ of polynomials of degree $\le T - g$ agreeing with the one word $R$ exactly on $S$, and the pole pair $(1/(x - \beta), R/(x - \beta))$ of the lead notes. So agreement $T$ at degree bound $k$ needs gap $g = T - k$ (degree $\le k$, inside the analysis degree $d = k - 1 + \ell$) or $g = T - k + 1$ (genuine degree $< k$). $\Lambda$ is multiplicative over disjoint unions, which is the whole point of the notation.

**Genuine variant. [proved]** If every member contains $0$ and $L_S = R + C_S$ with $\deg C_S \le k$, then $C_S(0) = R(0)$ for all $S$, so $(C_S - R(0))/X$ has degree $< k$ and agrees with the word $(R(x) - R(0))/x$ on $S \setminus \{0\}$: genuine codewords at agreement $T - 1$. A translation-invariant family has a fraction $T/n$ of its members through $0$.

### 1.2 The gap lemma

**Lemma 1.1. [proved]** Let $S = S_1 \sqcup \dots \sqcup S_m$ and $L_{S_i} = A_i + B_i$ with $A_i$ monic of degree $|S_i|$ and $\deg B_i \le |S_i| - g_i$. Then $L_S = \prod_i A_i + C$ with $\deg C \le |S| - \min_i g_i$.

*Proof.* Expand the product. Every term other than $\prod A_i$ contains some $B_i$ and loses at least $g_i$ in degree. $\square$

The pieces available on a subspace domain, with their gaps:

- a *fixed set* $P$: $A = L_P$, $B = 0$, gap $\infty$;
- a *coset of a fixed subspace* $W$: $L_{a+W} = L_W(X) + L_W(a)$, $A = L_W$, gap $|W|$;
- a *free flat* $a + V$ of size $Q$, any direction: $L_V$ is linearized, so $L_{a+V} = X^Q + (\text{degree} \le Q/2)$, $A = X^Q$, gap $Q/2$;
- a flat whose direction ranges over a class on which the top $j$ coefficients $c_{s-1}, \dots, c_{s-j}$ of $L_V$ are constant: gap $Q(1 - 2^{-j-1})$.

Since $L_W^2 = X^{2|W|} + (\text{degree} \le |W|)$, the tops $L_W^2$ and $X^{2|W|}$ are interchangeable whenever the gap in play is at most $|W|$. Lemma 1.1 with one fixed set and free flats is Lemma C of [01] ([DKTZ26, Lemma 6.1]). The consequence used throughout: **a family built from these pieces has $T - k \le$ the smallest gap, hence every piece has size at least $T - k$ and every free flat size at least $2(T - k)$.**

### 1.3 Complement duality

**Proposition 1.3. [proved]** Let $\mathcal{F}$ be a family of $T$-subsets of $D$ sharing their top with gap $g$. Then $\{D \setminus S : S \in \mathcal{F}\}$ is a family of $(n - T)$-sets sharing their top with gap $g$. In terms of (rate, agreement) $= (\rho, \tau)$ with $g = (\tau - \rho) n$, the dual family sits at $(1 + \rho - 2\tau,\ 1 - \tau)$, and $\tau^2 > \rho$ if and only if $(1 - \tau)^2 > 1 + \rho - 2\tau$.

*Proof.* $\Lambda_S \Lambda_{D \setminus S} = \Lambda_D$, and $\Lambda_S$ is invertible modulo $X^g$, so $\Lambda_{D \setminus S} \equiv \Lambda_D / \Lambda_S$ depends only on $\Lambda_S \bmod X^g$. The dual degree bound is $(n - T) - g$. The last claim is $\tau^2 - \rho = (1-\tau)^2 - (1 + \rho - 2\tau)$. $\square$

Rate 1/2 at $\tau$ is dual to rate $3/2 - 2\tau$ at $1 - \tau$: $(1/2, 5/8) \leftrightarrow (1/4, 3/8)$, $(1/2, 11/16) \leftrightarrow (1/8, 5/16)$, $(1/2, 23/32) \leftrightarrow (1/16, 9/32)$. The whole window $(5/8, 0.7071)$ at rate 1/2 is dual to agreements $(0.2929, 3/8)$ at rates between $0.086$ and $1/4$, which contains the rate-1/8 window point $5/16$. Checked on the class of Theorem 2.1 at $N = 6$ (`05_check_five_eighths.py`, last line). The duality is for common tops only. It does not turn arbitrary lists into lists.

### 1.4 What a general list is

Interpolate the word $w$ by a polynomial of degree $< n$. A codeword $P$ agrees with $w$ on $S$ iff $w - P = L_S E$ for some polynomial $E$. So a list at agreement $T$ is a family of polynomials $N_i = L_{S_i} E_i$ sharing all coefficients above degree $k$, with $|S_i| \ge T$: a common top with *phantom roots* (the roots of $E_i$). The strict common top is $E_i = 1$. If the phantom roots lie in $D$ the object is a multiset on $D$ (Section 6.4). Phantom flats outside $D$ do not help in the calculus of Lemma 1.1: a flat $F \subset K$ of size $Q$ has gap $Q/2$ but only $Q_0 = |F \cap D|$ agreement points, and replacing it by the flat $F \cap D$ of $D$ keeps the agreement, lowers the degree by $Q - Q_0$ and the smallest gap by at most $(Q - Q_0)/2$, so the degree bound does not go up. **[proved]**

## 2. Rate 1/2 at agreement $5n/8$

Let $W \subset D$ be a subspace of codimension 3 ($|W| = n/8$, eight cosets), $N \ge 4$.

**Theorem 2.1. [proved]** Let $\mathcal{F}_W$ be the set of all $S \subseteq D$ of size $5n/8$ that are disjoint unions of flats, each of which is a coset of $W$ or has size at least $n/4$. Then:

1. every $S \in \mathcal{F}_W$ has $L_S = X^{n/2} L_W + C_S$ with $\deg C_S \le n/2$, so the single word $w = X^{n/2} L_W$ agrees with $C_S$ exactly on $S$;
2. $|\mathcal{F}_W| = 56(2^N - 7)$, and the $C_S$ are pairwise distinct;
3. the $35(2^N - 7)$ members through $0$ give genuine codewords $C_S / X$ of degree $< n/2$ agreeing with $x^{n/2 - 1} L_W(x)$ on $5n/8 - 1$ points.

For $N = 25$: $2^{30.8}$ polynomials of degree $\le 2^{24}$ at agreement $5n/8$, and $2^{30.1}$ genuine codewords at $5n/8 - 1$. Query floor $\lceil 108/\log_2(8/5) \rceil = 160$.

*Proof.* (1) Each piece has gap at least $n/8$: a coset of $W$ has $A = L_W$ and gap $n/8$, a free flat of size $Q \ge n/4$ has $A = X^Q$ and gap $Q/2 \ge n/8$. By Lemma 1.1, $L_S = L_W^i X^{5n/8 - i n/8} + (\text{degree} \le n/2)$ where $i$ is the number of $W$-cosets among the pieces, and $L_W^2 - X^{n/4}$ has degree $\le n/8$, so $L_W^i X^{5n/8 - in/8} - X^{n/2} L_W$ has degree $\le n/2$ for every odd $i \le 5$. ($i$ is odd because the other pieces have sizes divisible by $n/4$.)

(2) A flat of size $\ge n/4$ is a union of flats of size $n/4$, and two cosets of $W$ form a flat of size $n/4$, so the members are: (a) unions of 5 cosets of $W$, $\binom{8}{5} = 56$ sets; (b) $F \sqcup P$ with $F$ a flat of size $n/4$ whose direction $V_F$ does not contain $W$ and $P$ three cosets of $W$; (c) $F_1 \sqcup F_2 \sqcup C$ with two such flats and one coset. Count (b): since $V_F \not\supseteq W$ and $F$ must miss a coset, $V_F + W$ is a hyperplane $H \supset W$ (7 choices), $V_F$ is one of the $2^{N-1} - 1 - 3$ hyperplanes of $H$ not containing $W$, $F$ is one of its 4 translates and then meets exactly the four $W$-cosets of its $H$-coset, and $P$ is 3 of the 4 cosets in the other $H$-coset: $7 \cdot (2^{N-1} - 4) \cdot 4 \cdot 4 = 56(2^N - 8)$. These are distinct sets, and distinct from (a), because $P$ is the union of the $W$-cosets contained in $S$ and $F = S \setminus P$ contains none. Type (c) adds nothing: disjoint $F_1, F_2$ lie in the two cosets of a hyperplane $H' = V_{F_1} + V_{F_2}$. If $W \subset H'$, $C$ lies in one coset of $H'$ beside, say, $F_2$, so $W \subseteq V_{F_2}$ and $F_2 \sqcup C$ is three cosets of $W$: type (b) or (a). If $W \not\subset H'$, put $W_0 = W \cap H'$. $C$ splits into two cosets of $W_0$, each beside one $F_i$ and disjoint from it, which forces $W_0 \subseteq V_{F_1} \cap V_{F_2}$. Working in $D / W_0 \cong \mathbb{F}_2^4$ with $\ell$ the image of $W$: the planes $F_1 + \ell$ and $F_2$ in the same 3-dimensional coset are equal (then $S$ is five cosets of $W$), or meet in a line (then $F_1 \sqcup F_2$ is two cosets of $W$ plus two parallel lines, that is a flat of size $n/4$: type (b)), or are parallel, which leaves no room for $C$. Total $56(2^N - 8) + 56$. Distinct $S$ give distinct $C_S = w - L_S$.

(3) $\mathcal{F}_W$ is invariant under translations by $D$, so a fraction $5/8$ of its members contain $0$. Apply the genuine variant of Section 1.1 with $R = X^{n/2} L_W$, $R(0) = 0$. $\square$

**[checked]** `05_check_five_eighths.py`: full enumeration of $\mathcal{F}_W$ for $N = 5, 6, 7$ inside $\mathrm{GF}(2^{16})$ gives 1400, 3192, 6776 members ($= 56(2^N - 7)$) of which 875, 1995, 4235 contain 0, and every locator (all of them for $N \le 6$, 300 for $N = 7$, 40 random members for $N = 8, 9$) has the top of $X^{n/2} L_W$ above degree $n/2$.

**The class is the whole list at $n = 32$. [checked]** `05_exact_list_n32.py` counts, by meet in the middle, all 20-subsets $S$ of $D_5 \subset \mathrm{GF}(2^{16})$ with $(e_1, e_2, e_3)(S) = (0, c_W, c_W')$, the top of $X^{16} L_W$: exactly 1400. So this word has no list member outside $\mathcal{F}_W$, of any shape.

**Relation to [01] and [DKTZ26].** For one padding coset the members containing it number $21 \cdot 2^N - 133$, which is $M_2(N) + 7$ in the notation of [01, 3.3] (the height-2 trees avoiding $W$, plus the 7 hyperplane cosets avoiding $W$). The gain here is the factor $8/3$ from using all eight cosets against one word, the exact count with proof, and the exhaustive check.

**Corollary 2.2 (arbitrary padding). [proved]** Let $H$ be a hyperplane of $D$, $b \notin H$, and $P \subseteq H$ any set of $3n/8$ points. For each of the $2^N - 2$ affine hyperplanes $F$ of the coset $b + H$, $L_{P \sqcup F} = L_P X^{n/4} + C_F$ with $\deg C_F \le n/2$. (Lemma 1.1 with a fixed set and a free flat. Checked for random $P$ at $N = 8, 9$.)

**Corollary 2.3 (rate 1/4 at $3n/8$). [proved]** The complements of the members of $\mathcal{F}_W$ are $56(2^N - 7)$ sets of size $3n/8$ whose locators share the top of $X^{n/4} L_W$ above degree $n/4$: a list of $2^{30.8}$ at rate 1/4 and agreement $3n/8$ (floor 77 queries for a list budget above $2^{26}$). By Proposition 1.3, using $1/\Lambda_W \equiv \Lambda_W \pmod{X^{n/8}}$. **[checked]** at $N = 6$.

## 3. Larger lists below the frontier: stacking

**Proposition 3.1. [proved]** Let $Y \subset D$ be a subspace of codimension $b$, choose $j$ of its $2^b$ cosets, a fixed set $P$ inside the other cosets, and in each chosen coset an arbitrary affine hyperplane $F_i$ of that coset. Then $S = P \sqcup F_1 \sqcup \dots \sqcup F_j$ has $L_S = L_P X^{jn/2^{b+1}} + C_S$ with $\deg C_S \le |S| - n/2^{b+2}$, and there are $(2^{N-b+1} - 2)^j$ such sets for a given $P$.

*Proof.* Lemma 1.1: the $F_i$ are free flats of size $n/2^{b+1}$, gap $n/2^{b+2}$, disjoint because they lie in different cosets. $\square$

At rate 1/2 take $j = 2^b - 1$ and $|P| = 3n/2^{b+2}$ in the last coset: agreement $(1/2 + 2^{-b-2})n$ with $(2^{N-b+1} - 2)^{2^b - 1}$ members. $b = 1$: $5/8$, $2^N - 2$. $b = 2$: $9/16$, $(2^{N-1} - 2)^3 \approx 2^{72}$ at $N = 25$. $b = 3$: $17/32$, $2^{161}$. These explicit counts are below the tree counts quoted in [01] ($M_3(25) = 2^{102.7}$) but need no reference. At rate 1/4: $b = 2$, $j = 2$, $|P| = n/16$ gives $5n/16$ with $(2^{N-1} - 2)^2 = 2^{48}$ members. **[checked]** for the $9/16$ stack at $N = 6, 8$ (30 random members each, one common top).

At a rate $\rho \le 1/4$ none of this exceeds the flats: $T - k \le$ smallest gap $\le$ smallest piece, and $T > 2k$ would give $T - k > T/2$, so a single piece (Section 5).

## 4. Single flats: the second coefficient of $L_V$

For $T > 2k$ at low rate the only candidates in the gap calculus are flats $V$ of dimension $s \ge \kappa + 2$ whose top coefficients are shared. Write $L_V = X^{2^s} + c(V) X^{2^{s-1}} + \dots$ and $L_D = X^n + d X^{n/2} + \dots$. Sharing $c(V)$ alone gives gap $\tfrac34 2^s$, hence $T = 4k$ for $s = \kappa + 2$ (genuine degree $< k$ on $V \setminus 0$, by dividing by $X$).

### 4.1 A formula for $c(V)$

For a hyperplane $H$ of $D$ let $\delta_H = L_H(u)$ for any $u \in D \setminus H$, that is $\delta_H = \prod_{d \in D \setminus H} d$. Then $L_D = L_H^2 + \delta_H L_H$.

**Proposition 4.1. [proved]** (i) The map $H \mapsto \delta_H$ is injective and $\widehat{D} := \{0\} \cup \{\delta_H^{-2}\}$ is an $\mathbb{F}_2$-subspace of $K$ of dimension $N$, with $H \mapsto \delta_H^{-2}$ additive in the functional defining $H$. (ii) For a subspace $V \subseteq D$ of codimension $r$,
$$c(V)^{2^r} = d + \sum_{H \supseteq V} \delta_H = \sum_{H \not\supseteq V} \delta_H ,$$
the sums over hyperplanes $H$ of $D$. Equivalently $c(V)^{2^{r+1}} = d^2 + \sum_{\alpha \in A_V \setminus 0} \alpha^{-1}$ where $A_V = \{\delta_H^{-2} : H \supseteq V\} \cup \{0\}$ is an $r$-dimensional subspace of $\widehat{D}$.

*Proof.* Identify a linearized polynomial $P = \sum a_i X^{2^i}$ with the operator $\sum a_i \sigma^i$ on $K$ ($\sigma$ the Frobenius), and let $P^\sharp = \sum \sigma^{-i} a_i$, so $(PQ)^\sharp = Q^\sharp P^\sharp$. Let $\Lambda = L_V(D)$, an $r$-dimensional space, and $M = L_\Lambda = \sum_{i \le r} m_i X^{2^i}$, so $L_D = M \circ L_V$ and comparing the coefficients of $X^{n/2}$ gives $d = c(V)^{2^r} + m_{r-1}$. For a hyperplane $\Gamma$ of $\Lambda$, $M = (\sigma + \delta_\Gamma) L_\Gamma$, so $M^\sharp = L_\Gamma^\sharp (\sigma^{-1} + \delta_\Gamma)$ kills $\delta_\Gamma^{-2}$. Distinct $\Gamma$ have distinct $\delta_\Gamma$ (if $\delta_\Gamma = \delta_{\Gamma'}$ then $(L_\Gamma + L_{\Gamma'})(L_\Gamma + L_{\Gamma'} + \delta_\Gamma) = 0$ and $L_\Gamma + L_{\Gamma'}$ vanishes at 0, so $L_\Gamma = L_{\Gamma'}$). The kernel of $M^\sharp$ is the root set of $\sigma^r M^\sharp = \sum_i m_i^{2^{r-i}} X^{2^{r-i}}$, a separable linearized polynomial of degree $2^r$, so it is an $\mathbb{F}_2$-space $A$ of size $2^r$, equal to $\{0\} \cup \{\delta_\Gamma^{-2}\}$, and $\sigma^r M^\sharp = m_0^{2^r} L_A$. Comparing the coefficients of $X$ and $X^2$: $1 = m_0^{2^r} \prod_{\alpha \in A \setminus 0} \alpha$ and $m_{r-1}^2 = m_0^{2^r} e_{2^r - 2}(A \setminus 0)$, so $m_{r-1}^2 = \sum_{\alpha \ne 0} \alpha^{-1} = \sum_\Gamma \delta_\Gamma^2$ and $m_{r-1} = \sum_\Gamma \delta_\Gamma$. With $\Lambda = D$, $r = N$ this gives the subspace $\widehat{D}$ and $d = \sum_H \delta_H$. Additivity in (i): for the three hyperplanes through a subspace of codimension 2, the case $r = 2$ says that the three $\delta_H^{-2}$ are the nonzero elements of a 2-dimensional space, so they sum to zero. For general $V$ the hyperplanes $\Gamma$ of $\Lambda$ are the $L_V(H)$, $H \supseteq V$, and $L_D = (\sigma + \delta_\Gamma) L_\Gamma L_V = (\sigma + \delta_\Gamma) L_H$ shows $\delta_\Gamma = \delta_H$. $\square$

**[checked]** `05_check_flat_tops.py`: additivity of $H \mapsto \delta_H^{-2}$ and formula (ii) for $r = 1, 2, 3$ on random subspaces, $N = 8$ in $\mathrm{GF}(2^{16})$, and additivity for $N = 25$ in the real $K$.

Two consequences. First, $c$ is injective on the hyperplanes of any fixed space, and if $A \subset A'$ with index 2 then $\iota(A') - \iota(A) = \pi_A / L_A(\gamma)$ determines the coset $\gamma + A$ (here $\iota(A) = \sum_{\alpha \ne 0} \alpha^{-1}$, $\pi_A$ the product of $A \setminus 0$), so two subspaces of $D$ with the same $c$ and the same codimension never meet in a hyperplane of both. **[proved]** Second, the fibers of $c$ on codimension-$r$ subspaces are the level sets of $A \mapsto \iota(A)$ on $r$-dimensional subspaces of $\widehat{D}$, a rational function with no reason to collide: $\iota$ vanishes identically on $\mathbb{F}_4$-lines $\alpha \mathbb{F}_4$ and would have large fibers if $\widehat{D}$ had subfield structure, but it has none.

### 4.2 Numerics on the fibers of $c$

**[checked]** `05_check_flat_tops.py`:

- $\mathrm{GF}(2^{16})$, $N = 8$, codimension 2: 10795 subspaces, 873 colliding pairs against a birthday expectation of 889, fibers of size at most 4. So in a small field $c$ behaves like a random function.
- Real $K$, $N = 12$, codimension 2: 2794155 subspaces, 2794154 distinct values. The single collision is structural and present for every $N$ from 6 to 13 (the script prints $N = 8$ to $12$): $c(V_1) = c(V_2)$ for $V_1 = (x^2 + x + 1) \cdot \mathrm{span}(1, \dots, x^{N-3})$ and $V_2 = \{f \in D : f(0) = f(1) = [x^{N-1}] f\}$ (the place of degree 2 against the three rational places of $\mathbb{F}_2(x)$). In codimension 3 there are exactly three colliding pairs ($N = 8, 9, 10$). These give lists of size 2 at $T = 4k - 1$, nothing more.
- Real $K$, $N \in \{20, 22, 25, 28\}$: $\dim(\lambda \widehat{D} \cap \widehat{D}) = 0$ and $\dim(\lambda D \cap D) = 0$ for all 254 elements $\lambda \in \mathrm{GF}(256) \setminus \mathrm{GF}(2)$. For $D$ and $\lambda = \omega \in \mathrm{GF}(4)$ this is a proof for $N \le 32$: $\mu = \omega \lambda$ with $\lambda, \mu \in D$ gives $\mu^2 + \mu\lambda + \lambda^2 = 0$, an identity of polynomials of degree $\le 2N - 2 < 64$ in $\mathbb{F}_2[x]$, impossible because $X^2 + X + 1$ has no root in $\mathbb{F}_2(x)$. **[proved]** So $D$ contains no set $\lambda \mathbb{F}_4^*$, the simplest set with a sparse non-linearized locator ($X^3 - \lambda^3$). The $\mathbb{F}_4$-sublines (five points, locator $X^5 + aX^4 + bX + c$) are excluded only heuristically: three points determine the subline and the other two must fall in $D$, an expected $2^{5N - 128}/120 < 1$ configurations. **[conjectured]**

So at rate 1/16 the Johnson-tight candidate "flats of dimension $\kappa + 2$ with a common $c$" ($T = 4k - 1 = n/4 - 1$) gives lists of size 2 on our domain, against $2^{26}$ for its rate-1/4 analogue. **[checked]** for $N \le 13$, **[conjectured]** for $N = 28$ on the birthday heuristic ($2^{2N-3} \ll 2^{32}$).

### 4.3 Pigeonhole at $T = 4k$ on the later ladder levels

**Proposition 4.3 ([BKR06] style, see [01, 3.2]). [proved]** For rate $2^{-R}$, $R \ge 3$, let $r = R - 2$. Some word $x^{4k} + c\,x^{2k}$ agrees on $4k$ points each with at least $2^r \binom{N}{r}_2 / |K|$ polynomials of degree $\le k$, and some word $x^{4k-1} + c\,x^{2k-1}$ on $4k - 1$ points with at least $\binom{N}{r}_2 / |K|$ genuine codewords.

*Proof.* The $\binom{N}{r}_2 \ge 2^{r(N-r)}$ subspaces of dimension $\kappa + 2$ have their $c(V)$ in $K$. Take the most popular value. For $V$ in that fiber and any $a$, $L_V(X) + L_V(a) - X^{4k} - cX^{2k}$ has degree $\le k$ and vanishes with the word on $a + V$. $\square$

**[checked]** in $\mathrm{GF}(2^8)$, $N = 7$, rate 1/32: 11811 subspaces of codimension 3, largest fiber 62 (average 46.1), 62 distinct polynomials of degree $\le 4$ each agreeing with $x^{16} + cx^8$ on 16 points.

On the leanVM ladder (level $i \ge 1$ has $N_1 = N_0 - 3$, $R_1 = R_0 + 3$, then $N_{i+1} = N_i - 1$, $R_{i+1} = R_i + 3$; $\mu = 30$) the exponent $r(N - r) - 64$ is:

| level-0 rate | level 1 $(N, R)$ | level 2 | level 3 | level 4 |
| --- | --- | --- | --- | --- |
| 1/2 | $(22, 4)$: none | $(21, 7)$: $2^{16}$ | $(20, 10)$: $2^{32}$ | $(19, 13)$: $2^{24}$ |
| 1/4 | $(23, 5)$: none | $(22, 8)$: $2^{32}$ | $(21, 11)$: $2^{44}$ | $(20, 14)$: $2^{32}$ |
| 1/8 | $(24, 6)$: $2^{16}$ | $(23, 9)$: $2^{48}$ | $(22, 12)$: $2^{56}$ | |
| 1/16 | $(25, 7)$: $2^{36}$ | $(24, 10)$: $2^{64}$ | $(23, 13)$: $2^{68}$ | |

So from level 2 on (level 1 for level-0 rates 1/8 and 1/16) lists above $2^{10}$ exist at $T = 4k$, twice the flats' agreement: the query floor of such a level is $\lceil 108/(R - 2) \rceil$ instead of $\lceil 108/(R - 1) \rceil$ (for example 22 instead of 18 at $R = 7$, against a Johnson count of 31). Sharing two coefficients ($T = 8k$, $r = R - 3$, 128 bits) never has enough subspaces on the ladder at $\mu = 30$ (closest: $(23, 13)$ with $2^{130}/2^{128}$). These lists are non-constructive. At level 0 the pigeonhole gives nothing for $\rho \ge 1/16$.

## 5. Obstructions inside unions of flats and coset unions

**Proposition 5.1 (first-order obstruction). [proved]** Let $S$ be a disjoint union of flats $a_i + V_i$, $Q$ the smallest size. Then $e_j(S) = 0$ for $0 < j < Q/2$ and $e_{Q/2}(S) = \sum_{|V_i| = Q} c(V_i)$. So in a common-top family of unions of flats with gap $g > Q/2$, the sum of $c$ over the smallest flats, an element of $K$ given by Proposition 4.1, is constant on the family.

*Proof.* $\Lambda_{a+V} = 1 + c(V) X^{|V|/2} + \dots$, and $\Lambda$ is multiplicative. $\square$

Consequences. (a) Rate 1/2, $5n/8 < T < 3n/4$: a member cannot consist of flats of size $n/2$ only, so it has a flat of size $Q \le n/4$, and $g = T - n/2 > n/8 \ge Q/2$. So the family lies in one fiber of the $K$-valued function "sum of $c$ over the smallest flats". With the fibers of $c$ trivial (Section 4.2), a member whose smallest flat is unique has that flat's direction frozen, and then its label enters the next coefficient. (b) Rate $\le 1/4$, $T > 2k$: $g > T/2$. A single flat needs its $c$ shared (Section 4). With two or more flats $Q \le T/2 < g$, and at degree deficits in $[Q/2, Q)$ only the first-order terms of the smallest flats appear, so for every $j$ the sum over the smallest flats of the $j$-th coefficient of $L_{V_i}$ is constant on the family: a unique smallest flat has a frozen direction. (c) Cosets of one subspace $W$ with $M = n/|W|$ cosets: $L_S = V_U(L_W)$ and the problem is the same problem for the label set $U$ in the $\log_2 M$-dimensional label space $L_W(D)$, at the same rate and relative agreement. Sharing $e_1(U)$ costs $\log_2 M$ bits (it is a label), $e_2(U)$ lies in the span of the pairwise products of a basis of the label space ($\binom{\log_2 M + 1}{2}$ bits), $e_3(U)$ costs 35 bits at $M = 32$, 56 at $M = 64$, and 64 beyond. Against $\binom{M}{m}$ sets this pigeonhole never reaches $2^{10}$ in the open windows: at rate 1/2, $M = 16$, $m = 11$ has 4368 sets for 14 bits, $M = 32$, $m = 21$ has $2^{26.9}$ sets for $5 + 15 + 35 + 64$ bits. **[proved]** as an accounting, it does not exclude coincidences.

**Formal classes for sixteen cosets. [checked]** `05_check_formal.py` computes, for label sets $U \subset \mathbb{F}_2^4$ with the basis labels as indeterminates, the classes that share $e_1, \dots, e_{g-1}$ identically (so on every domain and for every $W$ of codimension 4). At rate 1/2: $m = 10$ ($5/8$): classes of 504 and 448; $m = 11$ ($11/16$): largest class 3 (a 4-flat of labels plus one fixed label); $m = 12$ ($3/4$): largest class 4. Dually at rate 1/8, $m = 5$ ($5/16$): largest class 3. This is the rigidity the lead observed for unions of cosets of one subspace, and Section 6 explains it.

## 6. Formal families cannot enter the open windows

### 6.1 Formal families

Coordinatize $D$ by a basis $\beta_1, \dots, \beta_N$, so sets are subsets of $\mathbb{F}_2^N$ and $s = \sum_a s_a \beta_a$. Replace the $\beta_a$ by indeterminates $b_a$: $\Lambda^{\mathrm{f}}_S(X) = \prod_{s \in S} (1 + (\sum_a s_a b_a) X) \in \mathbb{F}_2[b_1, \dots, b_N][X]$. A family of $T$-subsets of $\mathbb{F}_2^N$ is **formal with gap $g$** if all its members have the same $\Lambda^{\mathrm{f}}_S \bmod X^g$. The definition does not depend on the choice of coordinates, since a linear change of coordinates is a linear change of the indeterminates. Specializing $b \mapsto \beta$ shows that a formal family shares its top with gap $g$ on every $N$-dimensional $\mathbb{F}_2$-subspace of every field of characteristic two. All families of Sections 2 and 3, the flats, the coset unions with prescribed label sum of the main document, and the trees of [DKTZ26] are formal: their proofs use only Lemma 1.1.

**Lemma 6.1 (non-formal families are domain-specific). [proved]** If a family of subsets of $\mathbb{F}_2^N$ is not formal with gap $g \le n$, then it shares its top with gap $g$ for at most a fraction $g/(|K| - 2^N) < 2^{-39}$ of the injective linear embeddings $\mathbb{F}_2^N \to K$.

*Proof.* Some $e_j(S) - e_j(S')$, $j < g$, is a nonzero polynomial of degree $j < |K|$ in $b$, with at most $j |K|^{N-1}$ zeros in $K^N$ (Schwartz and Zippel), while at least $|K|^N - 2^N |K|^{N-1}$ tuples are independent. $\square$

### 6.2 Quantization

For a function $m : \mathbb{F}_2^N \to \mathbb{Z}$ and a functional $\varphi$ let $\widehat{m}(\varphi) = \sum_x m(x) (-1)^{\varphi(x)}$.

**Lemma 6.2. [proved]** Let $m, m'$ be multisets on $\mathbb{F}_2^N$ (non-negative integer multiplicities) of the same mass with $\Lambda^{\mathrm{f}}_m \equiv \Lambda^{\mathrm{f}}_{m'} \pmod{X^g}$, and let $2^e < g$. Then for every nonzero functional $\varphi$ the masses of $\{\varphi = 1\}$ under $m$ and $m'$ agree modulo $2^{e+1}$, and so $\widehat{m}(\varphi) \equiv \widehat{m'}(\varphi) \pmod{2^{e+2}}$.

*Proof.* Lift to $\mathbb{Z}[b]$: $\tilde\Lambda_m = \prod_s (1 - \tilde s X)^{m(s)}$ with $\tilde s = \sum_a s_a b_a$, which reduces to $\Lambda^{\mathrm{f}}_m$ modulo 2. Then $F = \tilde\Lambda_m / \tilde\Lambda_{m'} = 1 + 2u + X^g v$ with $u, v \in \mathbb{Z}[b][[X]]$, and $\log F = -\sum_{i \ge 1} (p_i(m) - p_i(m')) X^i / i$ with $p_i(m) = \sum_s m(s) \tilde s^i$. Modulo $X^g$, $\log F = \sum_{j \ge 1} (-1)^{j-1} (2u)^j / j$, and $2^j / j \in 2\mathbb{Z}_{(2)}$ for all $j \ge 1$. So $p_i(m) - p_i(m') \in 2i\,\mathbb{Z}_{(2)}[b]$ for $i < g$. Take $i = 2^e$ and read the coefficient of $b_a^{2^e}$, which is $\sum_{s : s_a = 1} (m(s) - m'(s))$: it is divisible by $2^{e+1}$. Every nonzero functional is a coordinate functional in suitable coordinates. Finally $\widehat{m}(\varphi) = |m| - 2 m(\{\varphi = 1\})$. $\square$

(The other coefficients of the $p_i$ give congruences for the masses of flats of higher codimension. They are not needed below.)

### 6.3 The theorem

Let $g' = 2^{\lceil \log_2 g \rceil}$ be the least power of two with $g' \ge g$.

**Theorem 6.3. [proved]** Let $\mathcal{F}$ be a formal family of $T$-subsets of $\mathbb{F}_2^N$ with gap $g$, and $S \ne S'$ in $\mathcal{F}$, $f = 1_S - 1_{S'}$.

(a) $\widehat{f}(\varphi) \in 2g'\mathbb{Z}$ for all $\varphi$ and $\widehat{f}(0) = 0$. Either $S$ and $S'$ are the two cosets of a hyperplane (then $T = n/2$), or $\widehat{f}$ has at least two nonzero values and $|S \triangle S'| = \frac{1}{n}\sum_\varphi \widehat{f}(\varphi)^2 \ge 8g'^2/n$.

(b) If $T \ne n/2$ and $4g'^2 > n \min(T, n - T)$ then $|\mathcal{F}| = 1$.

(c) If $n/8 < g \le n/4$ and $T \ne n/2$, then $S \setminus S'$ and $S' \setminus S$ are two cosets of one subspace of codimension 2, and
$$|\mathcal{F}| \le 1 + \frac{T(n - T)}{(T - n/2)^2} .$$

(d) If $n/16 < g \le n/8$ and $T < 3n/16$, then $S \setminus S'$ and $S' \setminus S$ are two cosets of one subspace of codimension 3, and $|\mathcal{F}| \le 8$.

*Proof.* (a) Lemma 6.2 with $2^{e+1} = g'$, and $\widehat{f}(0) = |S| - |S'| = 0$. If $\widehat{f}$ is supported on a single $\varphi$, then $f = \frac{a}{n}\chi_\varphi$ has constant absolute value, and since $f$ takes values in $\{0, \pm 1\}$ and is not zero, $f = \pm\chi_\varphi$: $S$ and $S'$ are the two cosets of $\ker\varphi$. Otherwise at least two values are nonzero, each of absolute value at least $2g'$, and Parseval gives the bound.

(b) The hyperplane case needs $T = n/2$. Otherwise $|S \triangle S'| \le 2\min(T, n - T)$ contradicts (a).

(c) Here $g' = n/4$ and the hyperplane case of (a) is excluded by $T \ne n/2$. So $\widehat{f}$ takes values in $\frac n2 \mathbb{Z}$, and $|\widehat{f}(\varphi)| \le |S \triangle S'| \le 2\min(T, n-T) < n$ forces values in $\{0, \pm n/2\}$. If $k$ of them are nonzero, $|S \triangle S'| = kn/4 < n$, so $k \le 3$. $k = 1$ and $k = 3$ make $f = \frac12 \sum \pm\chi_\varphi$ half-integral. So $k = 2$: $f = \frac12(\epsilon_1 \chi_{\varphi_1} + \epsilon_2 \chi_{\varphi_2})$ with $\varphi_1 \ne \varphi_2$ nonzero, which is $+1$ on the flat $\{\epsilon_1\chi_{\varphi_1} = \epsilon_2\chi_{\varphi_2} = 1\}$, $-1$ on the opposite coset of the same codimension-2 subspace, and $0$ elsewhere. For the count fix $S_0 \in \mathcal{F}$. For $S \ne S_0$ the set $C_S = S_0 \triangle S$ is a coset of the hyperplane $\ker \psi_S$, $\psi_S = \varphi_1 + \varphi_2$, and $|S_0 \cap C_S| = n/4$, so $|\widehat{1_{S_0}}(\psi_S)| = |n/4 - (T - n/4)| = |T - n/2|$. Distinct $S$ have distinct $\psi_S$: otherwise $C_S$ and $C_{S'}$ are equal ($S = S'$) or complementary ($S \triangle S' = D$, excluded since $|S \triangle S'| = n/2$). Parseval for $1_{S_0}$: $(|\mathcal{F}| - 1)(T - n/2)^2 \le \sum_{\psi \ne 0} \widehat{1_{S_0}}(\psi)^2 = nT - T^2$.

(d) Here $g' = n/8$, $\widehat{f} \in \frac n4\mathbb{Z}$, $|\widehat{f}| \le |S \triangle S'| \le 2T < 3n/8$, so the nonzero values are $\pm n/4$ and their number $k = 16|S \triangle S'|/n$ is less than 6. $f = \frac14\sum_{i \le k} \epsilon_i\chi_{\varphi_i}$ is an integer, so $k$ is even, and $k = 2$ gives half-integers. So $k = 4$, the sum of the four signs is never $\pm 2$, so $\prod_i \epsilon_i\chi_{\varphi_i} = 1$ identically: $\varphi_4 = \varphi_1 + \varphi_2 + \varphi_3$ with $\varphi_1, \varphi_2, \varphi_3$ independent, and $f = \pm 1$ exactly on the two flats $\{\epsilon_i\chi_{\varphi_i} = \pm 1,\ i \le 3\}$ of codimension 3. Fix $S_0$. Each other member removes from $S_0$ a flat of codimension 3 contained in $S_0$. Two different flats of size $n/8$ meet in at most $n/16$ points and would cover $3n/16 > T$ points, so it is the same flat $F$ for all members, replaced by one of the 7 other cosets of its direction. $\square$

**Corollaries. [proved]** For formal families, with degree bound $k = \rho n$ and gap $g = T - k$:

- **Rate 1/2.** For $5n/8 < T \le 3n/4$: $|\mathcal{F}| \le n^2/(4g^2)$, at most 15 just above $5n/8$, at most 7 at $11n/16$, at most 5 at the Johnson radius, at most 4 at $3n/4$. For $T > 3n/4$: one member. Tight at $3n/4$ (three of the four cosets of a codimension-2 subspace).
- **Rate 1/4.** For $3n/8 < T < n/2$: $|\mathcal{F}| \le 1 + T(n-T)/(n/2 - T)^2$, which allows the $2^N - 1$ flats at $T = n/2 - 1$.
- **Rate 1/8.** For $n/4 < T \le 3n/8$ the same bound: at most 4 just above $n/4$, at most 11 up to the Johnson radius $0.3536n$.
- **Rate 1/16.** For $n/8 < T < 3n/16$: at most 8 (part (d)). For $3n/16 < T < n/4$: one member (part (b), $g' = n/4$ and $4g'^2 = n^2/4 > nT$). At $T = 3n/16$ exactly the class of triples of cosets of a codimension-4 subspace with a given label sum has 35 members.
- **Any rate, $g > n/4$, $T \ne n/2$:** one member, by (b) ($g' \ge n/2$).

**[checked]** `05_check_formal.py` computes all formal classes exactly (polynomial arithmetic in the indeterminates) for $N = 4$, $m \in \{5, \dots, 12\}$ and $N = 5$, $m \in \{5, 6\}$: Lemma 6.2 holds in every class, at rate 1/2 the largest classes have 3 members at $T = 11$ (bound 7) and 4 at $T = 12$ (bound 4) and all pairs are coset exchanges, and at rate 1/16 ($N = 5$, $k = 2$) the largest classes have 7 members at $T = 5$ (bound 8), 35 at $T = 6 = 3n/16$, and 1 at $T = 6$ with $g = 5$. Lemma 6.2 with $g = n/8$ is also checked on all of $\mathcal{F}_W$ for $N = 5, 6$.

**Reading.** At each rate the agreements at which formal families can be large are exactly the ones already reached: $3/4$, $5/8$, $9/16$, ... at rate 1/2 (list sizes $O(1)$, $\Theta(n)$, $\ge n^3$), and $2\rho$ at rates $\le 1/4$. Inside the open windows a formal family has at most 15 members. By Lemma 6.1, any larger family there is tied to the specific pair $(D, K)$: it needs identities among the $e_j \in K$ that fail for all but a $2^{-39}$ fraction of subspace domains. On our domain the only source of such identities found is pigeonhole, and its accounting (Sections 4.3 and 5) falls short of $2^{10}$ at level 0 for every rate.

### 6.4 Scope: multiset tops

Theorem 6.3 is about strict common tops. If the word has degree $M > T$ and the extra roots of each $w - P$ lie in $D$, the object is a family of multisets $m_i$ of mass $M$ with supports of size $\ge T$, gap $g = M - k$. Lemma 6.2 applies as stated, but parts (b) to (d) used $|f| \le 1$. The biased padding of [01, 3.4] is the example: $m_i = 1_B + 1_{H_i}$ with $B$ a fixed set of $n/4$ points and $H_i$ affine hyperplanes, $M = 3n/4$, $g = n/4$, agreement $|B \cup H_i| = 5n/8 + |\widehat{1_B}(\varphi_i)|/2$, which is formal as a multiset family and reaches $0.6289n$ with 1008 members. Its differences $1_{H_i} - 1_{H_j}$ are again two-character functions, as (c) would predict, and the Parseval cap $5/8 + \sqrt{3/(64L)}$ of [01] is the multiset analogue of the count in (c).

**[conjectured]** Every formal multiset family of $L$ members at rate 1/2 has agreement at most $(5/8 + O(L^{-1/2}))n$. Sketch of what is missing: when all members differ from one member $m_0$ by two-character functions, each exchanged flat lies in the support of $m_0$, the supports are forced to contain a hyperplane coset up to $n/L$ points, and the family is a star $B + 1_{H_i}$ up to $O(1)$ stars and $O(1/\epsilon)$ exceptions, where the cap is Parseval. I did not exclude families using differences with four or more characters (squared distance $\ge n$), which are possible in principle once multiplicities are allowed.

So the precise status at rate 1/2 above $5n/8$: strict common tops, at most 15 formal members; multiset tops, $2^{10}$ members up to about $0.63n$ by [01] and a conjectured cap there; domain-specific families, nothing found and no proof.

## 7. Things that do not help

- **Varying the pair $(W, U)$ (idea 2 of the brief). [proved]** $S = L_W^{-1}(U)$ with $U$ a union of flats of the label space is a union of flats of $D$ whose directions contain $W$. $L_W^{2^a}$ is linearized with the same gap as a free flat of size $2^a |W|$, so containing a common varying $W$ buys nothing, and an odd number of cosets of a varying $W$ exposes $c(W)$ at degree deficit $|W|/2$ (Proposition 5.1).
- **Phantom flats, multiplicative cosets, subfield sublines.** Sections 1.4 and 4.2.
- **Rational words. [proved]** For a word $R / L_Z$ with $Z \subseteq D$, a list member $S$ needs $L_S \equiv R \pmod{L_Z}$ besides a shared top, that is prescribed values $\prod_{s \in S}(z - s)$ for $z \in Z$. The number of conditions is still $T - k$. Formally these value conditions are fatal: $\prod_{s \in S}(z - s) = \prod_{s \in S'}(z - s)$ in the unique factorization domain $\mathbb{F}_2[b]$ forces $S = S'$. So a formal list on a rational word has no strict members beyond one, and denominators only make sense together with phantom roots.
- **Interleaving and the extension $E$.** A list over $E$ at agreement $T$ is a list of the 2-interleaved code over $K$: pairs of list members of two $K$-words with agreement sets meeting in $\ge T$ points. With two copies of a family at agreement $T' > T$ this gives at most the square of a list that the single lane already has at $T'$, and intersections of two members of the $3n/4$ classes are $5n/8$ at best. No gain found. **[proved]** for these two cases only.
- **Sums of two flats with cancelling $c$.** For hyperplanes $V_1, V_2$ of a common space, $c(V_1) + c(V_2)$ is constant on a family iff $\delta_1 + \delta_2$ is, a conic condition $1/\alpha_1 + 1/\alpha_2 = s$ on $\widehat{D}'$ whose solution count is the additive energy of $\{1/\alpha\}$. Structured solutions need $\mathbb{F}_4$-lines in the dual space, absent by 4.2. **[checked]** only through 4.2.

## 8. Answers to the brief, in order

1. *Multi-level structures.* Lemma 1.1 computes the shared top of any union of flats of mixed dimensions and directions. Result: Theorem 2.1 and Proposition 3.1, frontier $5n/8$ at rate 1/2.
2. *Label-space tricks.* No gain (Section 7, first item, and the formal classes for 16 labels in Section 5).
3. *Complements.* Proposition 1.3, Corollary 2.3. Links the rate-1/2 and low-rate windows.
4. *Non-common-top lists.* Section 1.4: they are common tops with phantom roots. Phantom roots in $D$ are the multiset tops of [01, 3.4] and Section 6.4, the only mechanism known to beat $5n/8$ (slightly). Phantom roots outside $D$: nothing found.
5. *Low rates.* Proposition 4.1 and Section 4.2: flats of dimension $\kappa + 2$ share $c$ only by coincidence, pigeonhole works from ladder level 2 on (Section 4.3), and Theorem 6.3 shows formal constructions cannot enter the windows $(1/4, 0.3536)$ and $(1/8, 1/4)$ with more than 11 and 8 members.
6. *Theorems and query floors.* Section 0 table.

**For the proof side.** (i) Theorem 6.3 is a proof that "all structure visible to $\mathbb{F}_2$-linear algebra" stops at the dyadic thresholds. A list bound beyond Johnson on $D_{\kappa,R}$ could therefore try to separate formal members (at most 15, classified) from non-formal ones (to be shown rare on this $D$). (ii) At rate 1/2 a provable target could be $\Lambda(T) \le 2^{31}$ for $T$ slightly above $5n/8$, or $\Lambda(T) \le$ a constant plus multiset-top members for $T \ge 0.64n$. (iii) The dual formula of Proposition 4.1 reduces "do codimension-$r$ flats share $c$" to level sets of $\sum_{\alpha \in A \setminus 0} 1/\alpha$ over subspaces $A$ of one explicit 25-dimensional space, a concrete exponential-sum question.

## 9. Reproduction

All in `doc/whir_soundness_gap_notes/scripts/`, pure Python 3, no dependencies.

- `05_gf.py`: field and subspace helpers.
- `05_check_five_eighths.py [Nmax]`: Theorem 2.1 (enumeration, count, tops), Corollaries 2.2 and 2.3, Proposition 3.1, Lemma 6.2 on $\mathcal{F}_W$. One second for $N \le 7$.
- `05_exact_list_n32.py`: the exact list of $X^{16} L_W$ at $n = 32$. One second.
- `05_check_flat_tops.py`: Proposition 4.1, fibers of $c$, structural collisions, subfield closure in the real $K$, pigeonhole demonstration. Ten seconds.
- `05_check_formal.py`: formal classes, Lemma 6.2, Theorem 6.3. Ninety seconds.

## References

As in `01-literature-attacks.md`: [DKTZ26] (ECCC TR26-237), [BKR06]/[BKR10] (subspace polynomials), [01] for that report.
