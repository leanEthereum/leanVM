# 30. Subspace GM-MDS: the proofs of the generic-points theorems, run on linear forms

Researcher 30. Every statement is tagged **[proved]** (proof here), **[quoted]** (read in the cited paper), **[checked]** (numerically, sizes stated) or **[conjectured]**. Scripts are `scripts/30_*`, section 10 says how to run them.

Notation as in note 17. $D$ is a generic $\mathbb{F}_2$-subspace of dimension $N$ of a field $F$ (basis $t_1, \dots, t_N$ algebraically independent over $\mathbb{F}_2$), $n = 2^N$, $Z_S = \prod_{s \in S}(X - s)$, $L_U = Z_U$ for a subspace $U$. A **multiplicity vector** is $m : D \to \mathbb{Z}_{\ge 0}$, $|m| = \sum_x m(x)$, $Z^m = \prod_x (X - x)^{m(x)}$. A **pattern** is a list $(m_i, c_i)_{i \in I}$ with an ambient degree bound $K$, $|m_i| + c_i \le K$: it stands for the spaces $V_i = Z^{m_i} F[X]_{<c_i} \subseteq F[X]_{<K}$. Its **rank** is $\dim \sum_i V_i$, it is **independent** if the sum is direct, and a **dependency** is $(u_i) \ne 0$, $u_i \in V_i$, $\sum u_i = 0$. In Lovett's notation the pattern with $c_i = K - |m_i|$ is $P(K, \mathcal{V})$, in Yildiz and Hassibi's it is $[(S_i, r_i)]$ with $r_i = c_i$. For $a \in D \setminus 0$ the **merge** $\mathcal{P}/a$ is the push-forward to $D/a$ (a generic subspace of dimension $N - 1$): $(m/a)(\bar x) = m(x) + m(x + a)$, same $c_i$ and $K$.

A **three-set pattern** is $(m_0, m_1, m_2; \delta)$: $K = \delta + 1$, $c_i = \delta + 1 - |m_i|$, and its **excess** is $E = \sum_i |m_i| - 2\delta$. It is square when $E = 2$. For pairwise disjoint sets $R_i$ a dependency with all $u_i \ne 0$ is a rational function $\xi = u_0/u_1$ of degree $\le \delta$ with $R_0, R_1, R_2$ in its fibres over $0, \infty, 1$: Conjecture P of note 17 says that square set patterns are independent unless a period explains the dependency.

## 0. Summary

**The honest headline.** I did not prove a subspace GM-MDS theorem, and there is no new unconditional list bound. What this note establishes is the exact place where the proofs of the generic-points theorems stop on linear forms, a corrected statement that survives every test I could run (including with multiplicities, which the induction needs and which nobody had tested), and a precise obstruction to completing the induction: patterns whose determinant is a product of the linear forms of $D$.

| | statement | status |
| --- | --- | --- |
| 2 | The generic-points chain is: list $\Rightarrow$ agreement hypergraph $\Rightarrow$ zero pattern of order $L + 1$ in the dual code $\Rightarrow$ GM-MDS. Only the last arrow uses the evaluation points, and inside it only one step: Lovett's Lemma 2.5, equal to Case 3 of Yildiz and Hassibi (merge one point into another, using one unit of slack) | quoted, read in full |
| 3.1 | On a subspace domain: sets $S_j$ carry a pseudo-list iff $\sum_j Z_{D \setminus S_j} F[X]_{<|S_j| - k} \ne F[X]_{<n-k}$. For three members this is Roth's three-polynomial Sylvester determinant on three disjoint sets | proved |
| 4.1 | The merge exists on linear forms only as $t_N \mapsto 0$, which merges all $n/2$ pairs $\{x, x + a\}$ at once. Rank is still lower semicontinuous (merge lemma), also for the second degeneration (a half of $D$ sent to infinity) | proved, checked |
| 4.2 | The count after the merge needs slack $\mu_a(I)$ = number of classes met by all sets of $I$ without a common point, against the slack 1 that non-tightness gives | proved |
| 4.3 | Even when the count holds the merged statement is false: **Lovett's Conjecture 1.5 fails in every positive characteristic** ($(X - a_1)^p, (X - a_2)^p, (X - a_3)^p$, $k = p + 1$). On a subspace every merge produces exactly this Frobenius degeneracy from every near-period | proved |
| 4.4 | For a square pattern with determinant $\Delta \ne 0$: $\sum_{a \ne 0} \mathrm{corank}(\mathcal{P}/a) \le \deg\Delta = \sum_i (c_i |m_i| + \binom{c_i}{2}) - \binom{K}{2}$ | proved, checked |
| 5.1 | Periodic and Frobenius families reduce **exactly** to $|U| 2^j$ patterns on the quotient, with the cofactor counts replaced by ceilings $\lceil (c_i - r)/(|U| 2^j) \rceil$. This is the "degree counted in powers of $L_U$" | proved |
| 5.2 | Sufficient condition (S) for a dependency of a three-set pattern with multiplicities: $u_i = G \cdot (v_i \circ L_U)^{2^j}$ | proved |
| S3 (5.3) | **Conjecture S3.** A three-set pattern with multiplicities on a generic subspace is dependent iff (D) two of its spaces meet or (S) holds | conjectured. Checked: all $7.3 \cdot 10^7$ square set patterns at $n = 16$ (up to translation and relabeling), and all $1.1 \cdot 10^9$ of their merges (multiplicities $\le 2$ on 8 points): 0 mismatches |
| 6.1 | **Terminal patterns.** At $n = 16$ there are independent square set patterns for which all 15 merges are dependent and none of the 30 half-restrictions is independent: 25200 at $\delta = 6$ and 40110 at $\delta = 7$ (none for $\delta \le 5$). The minimal-counterexample induction of GM-MDS cannot treat them | checked, exhaustive |
| 6.2 | For the terminal patterns examined $\Delta = \prod_{a \ne 0} a^{\kappa_a}$ exactly, $\kappa_a$ the corank of the merge along $a$ | checked (two patterns) |
| 6.3 | With excess the obstruction recedes (at $n = 16$, $\delta = 6$: 25200, 3150, 0 terminal patterns for $E = 2, 3, 4$), with multiplicities it grows (after one merge of a random pattern at $n = 32$, $E = 2$, $\delta = 13$: 75% terminal) | checked |
| 7.1 | Solution side: the excess of $\xi$ does not decrease under a nondegenerate reduction | proved |
| 7.2 | If for every direction the reduction is periodic with $\ge E$ periods and has no common factor, then $\xi$ has more than $n 2^{-3n/E}$ periods. So the whole difficulty of Conjecture P is the common factor of the reductions | proved |
| 9 | List bound: only the conditional one of note 17 ($2^{73}$ to $2^{82}$ at $N = 25$ to $28$ for $\tau \in (11/16, 1/\sqrt2)$, rate 1/2). Nothing at the other rates | conditional on P |

**What the brief asked and what came out.** (1) All six sources were obtained and the proofs of Lovett and of Yildiz and Hassibi read line by line (section 1). (2) The failing step is identified and the failure is characterized: section 4. (3) The corrected statement is S3 for three sets. I proved its sufficient direction and the exact reduction of periodic families, verified the converse one level down with multiplicities, and showed that the adapted induction does **not** go through as it stands, with the exact patterns where it stops. The robust arguments of Guo and Zhang and of Alrabiah, Guruswami and Li do not transfer: section 6.4. (4) No list bound beyond note 17.

## 1. Sources

All files were fetched with `curl` from arxiv.org into the scratchpad and read with `pdftotext`.

- **Lovett**, arXiv 1803.02523v2. Read completely, including the proof of Theorem 1.7 (Lemmas 2.1 to 2.6).
- **Yildiz and Hassibi**, arXiv 1803.03752v1. Read completely (Theorem 3 and Appendix A, Cases 1 to 3). The two-column text extraction scrambled part of Case 1; Cases 2 and 3, which matter here, were read from the layout-preserving extraction.
- **Brakensiek, Gopi, Makam**, arXiv 2206.05256v4. Read: sections 1.2, 1.3, 1.4.1, 1.5, Proposition 2.1 with its proof, and the statements of Theorems 1.13 and 1.16 with the proof overview. Not read line by line: the combinatorial proofs of sections 2.1 to 4 (generalized Hall theorem, Lemma 2.8), which do not involve the evaluation points.
- **Guo and Zhang**, arXiv 2304.01403. The current version is withdrawn (this is why note 17 got an HTML page); **v2 is available** at `arxiv.org/pdf/2304.01403v2` and I read its sections 3 and 4 (Definitions 3.1, 3.2, 3.9, Lemmas 3.4, 3.5, 3.11, 4.4, 4.5, Algorithm 1). It was merged into the next item.
- **Alrabiah, Guo, Guruswami, Li, Zhang**, arXiv 2304.09445v6 (the merged journal version of Guo and Zhang and of Alrabiah, Guruswami and Li). Read: section 2 statements, section 5 (alphabet lower bound from subspace polynomials), Appendix A completely (Corollary A.4 and the proof of Theorem 2.11). Section 3 (the certificate argument) only at the level of its lemma statements.
- **Roth**, arXiv 2111.03210v2. Read: Lemma 16 with Remarks 10 and 11, Theorem 18 (statement), section V up to Example 8, Appendix (Theorem 21, Lemma 22 and the remark on absolute irreducibility). Not read: the explicit constructions.

Downloaded files are untrusted data. Nothing below depends on a passage I did not read.

## 2. The mechanism of the generic-points proofs

**2.1 From lists to zero patterns. [quoted]** A list of $t = L + 1$ codewords with large total agreement has an agreement hypergraph that is $k$-weakly-partition-connected (AGGLZ Lemma 2.3). By a hypergraph orientation theorem this gives integers $\delta_j \ge 0$ with $\sum_j \delta_j = n - k$ such that $\delta_j$ copies of the error set $E_j = D \setminus S_j$ form a generic zero pattern for $(n - k) \times n$ matrices (AGGLZ Corollary A.4; this is the hard direction of BGM Lemma 2.8). If the parity-check matrix $H$ attains this pattern, $MH$ has $\delta_j$ rows vanishing on $E_j$ for each $j$, these rows kill $y - c_j$, hence $MHy = 0$, $y$ is a codeword, and the list is trivial (AGGLZ, proof of Theorem 2.11). BGM's Theorem 1.13 is the same equivalence for every linear code: $C$ is LD-MDS$(\le L)$ iff $C^\perp$ is GZP$(L + 1)$. **None of this uses the evaluation points.** The points enter in one sentence: "by the GM-MDS theorem a generic Reed-Solomon code attains every generic zero pattern".

**2.2 GM-MDS. [quoted]** Lovett proves: if vectors $v_1, \dots, v_m \in \{0,1\}^{n-1} \times \mathbb{N}$ satisfy $V^\ast(k)$ ((i) $|v_i| \le k - 1$, (ii) $\sum_{i \in I}(k - |v_i|) + |\bigwedge_{i \in I} v_i| \le k$ for all $I$, (iii) multiplicities only in the last coordinate), then the polynomials $\prod_j (x - a_j)^{v_i(j)} x^e$, $e \le k - 1 - |v_i|$, are linearly independent over $F(a)$. The proof takes a minimal counterexample and shows: no common root (Lemma 2.2, divide by $x - a_j$), no proper tight $I$ (Lemma 2.4, replace the tight subfamily by its meet), the vector $(1, \dots, 1, 0)$ is present (Lemma 2.5), $n = k$ (Lemma 2.6), and then concludes by evaluating at $x = a_n$. **Lemma 2.5 is the only step that moves points**: pick $v_{i^\ast}$ with zeros in coordinates $n - 1$ and $n$, substitute $a_n := a_{n-1}$. The new vectors add the last two coordinates, $|v'_I| \le |v_I| + 1$, and the unit of slack from Lemma 2.4 keeps (ii). If the merged polynomials are independent, a dependency with coprime coefficients $w_{i,e}(a)$ would have all $w_{i,e}$ divisible by $a_{n-1} - a_n$. Yildiz and Hassibi's Theorem 3 ($\det M[(S_i, r_i)] \ne 0$ iff $|\bigcap_\Omega S_i| + \sum_\Omega r_i \le \max_\Omega (|S_i| + r_i)$ for all $\Omega$) has the same skeleton: Case 1 splits at a tight proper $\Omega$, Case 2 removes a row when the maximizer of $|S_i| + r_i$ is unique, and Case 3 substitutes $\alpha_n = 0$, merging one point into the distinguished root at the origin. Both generalizations exist to make this one merge possible: a single point with multiplicity (Lovett), or a factor $x^{k - |S_i| - r_i}$ (Yildiz and Hassibi).

**2.3 Random puncturing. [quoted]** Guo and Zhang (Lemma 3.11) and AGGLZ (Theorem 2.11, Lemma 2.14) take the generic nonvanishing of the reduced intersection matrix from BGM, that is from GM-MDS, and add robustness: it survives deleting the rows of $\lambda k/(t-1)$ (respectively $\epsilon n$) coordinates. The probabilistic part uses that the variable $X_i$ occurs only in the rows of coordinate $i$, so that $r$ successive "faulty indices" are nearly independent events of probability $\le (t-1)(k-1)/(q - n + 1)$ each.

**2.4 Roth. [quoted]** For $L = 2$ a non-2-MDS code has three error vectors with pairwise disjoint supports $J_0, J_1, J_2$, $2 \le |J_m| \le n - k - 1$, in one coset (Lemma 16, Remark 11), and for Reed-Solomon codes the condition is the vanishing of the $\rho \times \rho$ three-polynomial Sylvester determinant $\det S_\rho$ of the three locators, $\rho = n - k$, $\sum |J_m| = 2\rho$, homogeneous of degree $\rho^2 - \frac12\sum_m \rho_m^2$ (Lemma 22). Whether $\det S_\rho$ is absolutely irreducible is left open there.

## 3. The dictionary on a subspace domain

**Proposition 3.1 (lists as spanning). [proved]** Let $D$ be any subspace domain, $S_0, \dots, S_L \subseteq D$, $E_j = D \setminus S_j$, $m_j = |S_j| - k$. There are a word $y$ that is not a codeword of $\mathrm{RS}[D, k]$ and codewords $c_j$ (not necessarily distinct) with $y = c_j$ on $S_j$ if and only if
$$\sum_{j} Z_{E_j}\, F[X]_{< m_j} \ \ne\ F[X]_{< n - k} .$$
A list with two distinct members and $|S_j| \ge k$ has such a $y$.

*Proof.* $\sum_{x \in D} x^i = 0$ for $i \le n - 2$, so $H = (x^i)_{i < n-k,\, x \in D}$ is a parity-check matrix. $y - c_j$ is supported on $E_j$ for some codeword $c_j$ iff the syndrome $z = Hy$ lies in $H_{E_j}$, the span of the columns in $E_j$. Pair $F[X]_{<n-k}$ with syndromes by $\langle g, z\rangle = \sum g_i z_i$: the column of $x$ pairs to $g(x)$, so the annihilator of $H_{E_j}$ is $\{g : g|_{E_j} = 0\} = Z_{E_j} F[X]_{<n - k - |E_j|}$, and $n - k - |E_j| = m_j$. Hence $\bigcap_j H_{E_j} \ne 0$ iff the annihilators do not span. $\square$

So the statement that excludes lists is of **spanning** type with $(L + 1)$ sets and $m_j$ polynomials per set. A count shows that it needs $\sum_j m_j \ge n - k$, the generalized Singleton bound. Choosing $\delta_j \le m_j$ with $\sum \delta_j = n - k$ gives a square pattern $[(E_j, \delta_j)]$ in the sense of Yildiz and Hassibi, and section 2.1 is the statement that the combinatorial condition of their Theorem 3 can be met. For three members the supports can be made disjoint (Roth) and the square patterns are exactly the three-set patterns of this note with $R_i = J_i$, $\delta = \rho - 1$, and $\Delta$ is Roth's $\det S_\rho$ (same description as a Sylvester matrix of three locators and same degree; I did not compare the matrices entry by entry). In the form of note 17 the same determinant appears with $R_i$ the pairwise intersections of the agreement sets and $\delta \le k - 1$.

## 4. Where the proofs break on linear forms

### 4.1 The merge becomes global, and what survives of it

On $D$ the points are the $n$ linear forms $\sum x_i t_i$. A specialization that identifies two of them, $x$ and $y$, is the quotient of $\mathbb{F}_2[t]$ by the linear form $a = x + y$, and it identifies $z$ with $z + a$ for **every** $z$. There is no homomorphism that moves one point and fixes the others. This is the step where Lovett's Lemma 2.5 and Case 3 of Yildiz and Hassibi fail. Everything else in Lovett's proof (Lemmas 2.1, 2.2, 2.4, 2.6 and the final evaluation) is valid for any set of distinct points.

**Lemma 4.1 (merge and restriction). [proved]** For every pattern $\mathcal{P}$ on a generic subspace $D$:
1. $\mathrm{rank}(\mathcal{P}) \ge \mathrm{rank}(\mathcal{P}/a)$ for every $a \in D \setminus 0$.
2. $\mathrm{rank}(\mathcal{P}) \ge \mathrm{rank}(\mathcal{P}|_H)$ for every affine hyperplane $H$ of $D$, where $\mathcal{P}|_H$ is the pattern on $H$ (translated to a generic subspace of dimension $N - 1$) with vectors $m_i|_H$ and the same $c_i$ and $K$ (the mass $|m_i| - |m_i|_H|$ has gone to infinity).

In particular a pattern is independent as soon as one merge or one restriction is.

*Proof.* The coefficient matrix $M$ of the polynomials $Z^{m_i} X^e$ has entries in $\mathbb{F}_2[t]$. (1) Choose the basis with $t_N = a$. Modulo $t_N$ the matrix is that of $\mathcal{P}/a$ on the generic subspace spanned by $t_1, \dots, t_{N-1}$, and a minor that is nonzero modulo $t_N$ is nonzero. (2) Translate so that $H$ is the span of $t_1, \dots, t_{N-1}$ (a translation by $b \in D$ acts on $F[X]_{<K}$ by $X \mapsto X + b$ and preserves ranks). Put $t_N = 1/s$ and multiply the column of $Z^{m_i} X^e$ by $s^{|m_i| - |m_i|_H|}$: each factor $s(X - x' - 1/s) = sX - sx' - 1$ becomes $1$ at $s = 0$, and the matrix at $s = 0$ is that of $\mathcal{P}|_H$. $\square$

**[checked]** `30_validate.py`: on 850 random three-set patterns at $N = 3, 4$ (half of them built periodic), none of the 246 dependent ones had an independent merge or restriction, and all 604 independent ones had both.

These two operations and their compositions are all the monomial degenerations: a valuation with $v(t_i) = w_i$ sends the points with a basis vector of negative weight in their support to infinity and merges the rest along the span of the positive weights.

### 4.2 The count after the merge

For sets $S_i$ and $I \subseteq [m]$ the merged vectors satisfy $|\bigwedge_I (S_i/a)| = |\bigcap_I S_i| + \mu_a(I)$, where $\mu_a(I)$ is the number of classes $\{x, x + a\}$ that meet every $S_i$, $i \in I$, and contain no point common to all of them. **[proved]** (count class by class). Lovett's condition (ii) for the merge therefore needs slack $\mu_a(I)$ for every $I$, while non-tightness provides 1. For two sets $\mu_a(i, j) = |(S_i \setminus S_j) \cap ((S_j \setminus S_i) + a)|$, and $\sum_{a} \mu_a(i,j) = |S_i \setminus S_j|\,|S_j \setminus S_i|$: the average over directions is quadratic in the densities, linear in $n$. For a square three-set pattern of disjoint sets the merged condition (ii) reads $|R_i \cap (R_j + a)| \le \delta + 1 - |R_l|$ for the three pairs, and a rough count says that it is met by an average direction when the sets are balanced and $\delta < n/4$, and by few or no directions when $|R_l|$ is close to $\delta$ (section 6.1 has the exact numbers at $n = 16$).

### 4.3 Frobenius: the merged statement is false even when the count holds

**Proposition 4.2. [proved]** Lovett's Conjecture 1.5 (the statement of his Theorem 1.7 without restriction (iii)) is false over every field of characteristic $p > 0$: $n = 3$, $k = p + 1$, $v_i = p\,e_i$ satisfy $V(k)$, and $P(k, \mathcal{V}) = \{(x - a_i)^p\} = \{x^p - a_i^p\}$ consists of three polynomials in the span of $x^p$ and $1$. For $p = 2$: $(a_2^2 + a_3^2)(x - a_1)^2 + (a_1^2 + a_3^2)(x - a_2)^2 + (a_1^2 + a_2^2)(x - a_3)^2 = 0$.

*Proof.* (i): $|v_i| = p = k - 1$. (ii): $|I| + 0 \le 3 \le p + 1$. The dependency is immediate. $\square$ (**[checked]** `30_checks.py` item 1.)

This is not a curiosity: it is what every merge on a subspace produces. If $S$ is $a$-periodic then $S/a = 2 \cdot 1_{S/a}$ and $Z_S$ reduces to a square. More generally a pattern that is $a$-periodic outside a few classes merges to $G \cdot (\text{squares})$, and squares live in $F[X^2]$, where the count of unknowns is halved. So the class of statements that is closed under the only available merge necessarily has multiplicities at all points, and in that class the hypothesis $V(k)$ is not sufficient.

### 4.4 A degree bound

**Proposition 4.3. [proved]** Let $\mathcal{P}$ be a square pattern ($\sum c_i = K$) on a generic subspace with determinant $\Delta \in \mathbb{F}_2[t]$. Then $\Delta$ is homogeneous of degree $\sum_i \bigl(c_i |m_i| + \binom{c_i}{2}\bigr) - \binom{K}{2}$, and if $\Delta \ne 0$,
$$\prod_{a \in D \setminus 0} a^{\mathrm{corank}(\mathcal{P}/a)} \ \Big|\ \Delta, \qquad\text{so}\qquad \sum_{a \ne 0} \mathrm{corank}(\mathcal{P}/a) \ \le\ \deg\Delta .$$

*Proof.* The coefficient of $X^d$ in $Z^{m_i} X^e$ is homogeneous of degree $|m_i| + e - d$, which gives the degree. Over the discrete valuation ring $\mathbb{F}_2[t]_{(a)}$ the valuation of a determinant is at least the corank of the matrix modulo $a$ (Smith normal form), and distinct linear forms are non-associate primes. $\square$

For three disjoint sets the degree is Roth's $\rho^2 - \frac12 \sum \rho_m^2$. The proposition is a test for dependence (more than $\deg\Delta$ degenerate directions, with multiplicity, force $\Delta = 0$). It cannot prove independence, and section 6.2 shows that it is attained.

## 5. The corrected statement

### 5.1 Periodic and Frobenius families reduce exactly

**Proposition 5.1. [proved]** Let $U \le D$, $q = 2^j$, $Q = q|U|$, $\ell = L_U^q$ (an additive polynomial of degree $Q$), and let all vectors of a pattern have the form $m_i = q \cdot (\beta_i \circ \pi_U)$ with $\beta_i$ a multiplicity vector on $D/U$. Then $Z^{m_i} = z_i(\ell)$ with $z_i = \prod_y (Y - \ell(y))^{\beta_i(y)}$, the points $\ell(D)$ form a generic subspace of dimension $N - \dim U$, and
$$\mathrm{rank}(\mathcal{P}) = \sum_{r=0}^{Q-1} \mathrm{rank}(\mathcal{P}_r), \qquad \mathcal{P}_r = \Bigl(\beta_i,\ \bigl\lceil \tfrac{c_i - r}{Q} \bigr\rceil\Bigr)_i \ \text{ in degree } < \bigl\lceil \tfrac{K - r}{Q} \bigr\rceil \text{ on } \ell(D) .$$
In particular $\mathcal{P}$ is independent iff every $\mathcal{P}_r$ is, and Lovett's condition for the $\mathcal{P}_r$ is necessary: $\sum_{i \in I} \lceil (c_i - r)/Q \rceil + |\bigwedge_I \beta_i| \le \lceil (K - r)/Q \rceil$ for all $I$ and $r$.

*Proof.* $F[X] = \bigoplus_{r < Q} X^r F[\ell]$ because $\ell$ is monic of degree $Q$, and $\deg(X^r g(\ell)) = r + Q \deg g$. Multiplication by $z_i(\ell)$ preserves each summand, and $F[X]_{<c} = \bigoplus_r X^r F[\ell]_{<\lceil (c - r)/Q \rceil}$. $\ell(D) = \{L_U(x)^q\}$ is spanned by the $q$-th powers of the images of a complementary basis, which are algebraically independent. $\square$

The ceilings are the whole effect. Three cosets of $U$ with $\delta = |U|$: $c_i = 1$, $K = |U| + 1$, the generic count $3 \le K$ holds, but for $r = 0$ it reads $3 \le \lceil (|U| + 1)/|U| \rceil = 2$. This is $\xi = \mu \circ L_U$, the flats. In general a family of $\ell$ sets gains at most $\ell - 1$ units of $Q$ over the generic count, which for three sets is the bound $\nu \le 2\delta + |\Pi|$ of Conjecture P.

Non-periodic failures of the zero-pattern statement exist too, but in a different regime. **[proved]** At $n = 8$, $k = 4$ any four of the seven 3-subsets with a given sum $s \ne 0$ satisfy the MDS condition (two of them share at most one point, at most three pass through one point) and their locators $X^3 + sX^2 + \dots$ span at most three dimensions. Five affine planes of $\mathbb{F}_2^3$ not through a common point ($k = 5$) fail in the same way, inside the 4-dimensional space of affine linearized polynomials. These are the first Walsh congruence of Theorem W ($e_1$ of a set is $\mathbb{F}_2$-linear in its indicator) and the flats. They are patterns of order $k$ with one polynomial per set. A list pattern has order $L + 1$ and $m$ consecutive cofactor degrees per set, and a shared top of the locators only helps if it is longer than $m$, which is the rigidity regime of notes 02, 04 and 12. So for list patterns the multiplicative structure of Proposition 5.1 is the only failure I know, and S3 below says that for three sets it is the only one.

### 5.2 The sufficient direction

**Proposition 5.2. [proved]** A three-set pattern $(m_0, m_1, m_2; \delta)$ on any subspace domain $D$ has a dependency if
- **(D)** $|\max(m_i, m_j)| \le \delta$ for some $i \ne j$ (pointwise maximum), or
- **(S)** there are a subspace $U \le D$, $q = 2^j$, an integer $\delta_0 \ge 0$ and multiplicity vectors $\beta_0, \beta_1, \beta_2$ on $D/U$ with $\sum_i |\beta_i| \le 2\delta_0 + 1$ and
$$\sum_{x \in D} \max_i \bigl(m_i(x) - q\,\beta_i(\pi_U x)\bigr)^+ \ +\ q\,|U|\,\delta_0 \ \le\ \delta .$$

*Proof.* (D): $u_i = u_j = Z^{\max(m_i, m_j)}$, $u_l = 0$. (S): on $\ell(D)$, $\ell = L_U^q$, the system $\sum v_i = 0$, $Z^{\beta_i} \mid v_i$, $\deg v_i \le \delta_0$ has at least $3(\delta_0 + 1) - \sum|\beta_i|$ unknowns and $\delta_0 + 1$ equations, so a solution $(v_i) \ne 0$. With $G = Z^g$, $g(x) = \max_i (m_i(x) - q\beta_i(\pi x))^+$, put $u_i = G \cdot v_i(\ell)$: then $\sum u_i = 0$, $\mathrm{ord}_x u_i \ge g(x) + q\beta_i(\pi x) \ge m_i(x)$ and $\deg u_i \le |g| + q|U|\delta_0 \le \delta$. $\square$

(S) with $U = 0$, $q = 1$ contains the common-root obstruction (Lovett's (ii) for $I = \{0,1,2\}$), and (D) is Lovett's (ii) for pairs. A period is $|U| \ge 2$, and $q \ge 2$ is the Frobenius case of Proposition 4.2.

### 5.3 Conjecture S3 and its tests

**Conjecture S3. [conjectured]** On a generic subspace a three-set pattern with multiplicities has a dependency **only if** (D) or (S) holds.

For set patterns the "only if" is the pattern form of Conjecture P (note 17 Proposition 4.2). S3 extends it to multiplicities, which is the form any induction through merges must have, and it had not been tested.

**[checked, exhaustive]** `30_crit.c`, random basis in $\mathrm{GF}(2^{64})$. Every set pattern at $n = 16$ with $0 \in R_0$ and $|R_0| \ge |R_1|, |R_2|$ (which covers all patterns up to translation and relabeling), $\delta = 2, \dots, 7$, and all 15 merges of each (multiplicities 0, 1, 2 on the 8 points of a generic subspace of dimension 3). "Dependent" is decided by rank. The prediction is evaluated on every dependent pattern (the conjectured direction) and on 1 in 64 of the independent ones (the proved direction, as a check of the program).

| $\delta$ | set patterns | dependent, all (S) | merges examined | dependent merges: (D) / (S) | unpredicted |
| --- | --- | --- | --- | --- | --- |
| 2 | 45045 | 315 | 675675 | 20790 / 10395 | 0 |
| 3 | 1351350 | 0 | 20270250 | 1304100 / 130410 | 0 |
| 4 | 10510500 | 7980 | 157657500 | 18639600 / 477540 | 0 |
| 5 | 33108075 | 10395 | 496621125 | 90237000 / 1065015 | 0 |
| 6 | 25540515 | 14175 | 383107725 | 106177680 / 4031685 | 0 |
| 7 | 2240238 | 0 | 33603570 | 13841520 / 4700220 | 0 |

The proved direction was re-checked on $1.4 \cdot 10^7$ independent patterns and merges, also without a mismatch. At $\delta = 7$ the (S)-witnesses $(|U|, q, \delta_0)$ of the dependent merges are $(1, 2, 1)$: 3245760, $(1, 2, 2)$: 1386000, $(1, 2, 3)$: 60900, $(2, 2, 1)$: 7560. All of them are Frobenius, as section 4.3 predicts, and the last ones combine a period with Frobenius. No merge was dependent for a reason other than (D) and (S). Also at $n = 8$, $\delta = 2, 3$: 0 mismatches.

What this adds to the evidence for P: the statement is stable under the one operation that an inductive proof can use, with the Frobenius twist as the only new phenomenon.

## 6. Can the induction be completed?

A proof in the manner of GM-MDS would take a pattern that satisfies the criterion (not (D), not (S)) and is dependent, minimal in $N$, and derive a contradiction from Lemma 4.1: some merge or restriction must again violate (D) and (S), and is then independent by minimality. This requires: **every independent pattern has an independent merge or restriction, up to terminal cases that can be settled by hand** (in Lovett's proof the terminal case is $n = k$ with the vector $(1, \dots, 1, 0)$).

### 6.1 Terminal patterns

**[checked, exhaustive]** `30_merge.c`: all square set patterns at $n = 16$ with $0 \in R_0$, $|R_0| \ge |R_1| \ge |R_2|$.

| $\delta$ | patterns | independent | independent with no independent merge | of these, certified by a restriction |
| --- | --- | --- | --- | --- |
| 2 | 45045 | 44730 | 0 | |
| 3 | 1351350 | 1351350 | 0 | |
| 4 | 10510500 | 10502520 | 0 | |
| 5 | 33108075 | 33097680 | 0 | |
| 6 | 25540515 | 25526340 | **25200** | 0 |
| 7 | 2240238 | 2240238 | **40110** | 0 |

So for $\delta \le 5$ every independent pattern at $n = 16$ is certified by one merge to 8 points, and for $\delta = 6, 7$ there are **terminal** patterns: independent, with all 15 merges dependent and no admissible restriction independent. At $n = 8$ there are none. The terminal patterns at $\delta = 7$ have sizes $(7, 5, 4)$, $(7, 6, 3)$ and $(6, 5, 5)$ and are partitions of $D$.

Example. $R_0 = \{0,1,2,4,6,8,9\}$, $R_1 = \{3,5,10,11,12,13\}$, $R_2 = \{7,14,15\}$ (labels in $\mathbb{F}_2^4$). For $U = \{0, 1, 8, 9\}$ the cosets are $\{0,1,8,9\} \subseteq R_0$, $\{2,3,10,11\}$ and $\{4,5,12,13\}$ with three points in $R_1$ and one in $R_0$, and $\{6,7,14,15\}$ with three points in $R_2$ and one in $R_0$. It is a $U$-periodic configuration with three points moved. Along each $a \in U \setminus 0$ the merge has five full classes, distributed $(2, 2, 1)$, and three mixed classes, and it is dependent by (S) with $G$ the three mixed classes and $\xi = \eta^2$, $\deg\eta = 2$: $3 + 2 \cdot 2 = 7 \le \delta$. Along the other 12 directions the pair count fails, that is (D) holds. **[checked]**

For a partition of $D$ with $x$ mixed and $n/2 - x$ full classes along $a$, (S) with $q = 2$ needs $x + 2\lceil (n/2 - x - 1)/2 \rceil \le n/2 - 1$, (take $U = 0$, $\beta_i$ the full classes of $R_i$, $G$ the mixed classes), which holds exactly when $x$ is odd. **[proved]** (arithmetic, $n/2$ is even). So a partition pattern is terminal as soon as every direction has an odd number of mixed classes or fails the pair count.

### 6.2 Their determinant is a product of linear forms

**[checked]** `30_checks.py` item 3 and `30_orders.py`. For the example above $\deg\Delta = 17$ (Proposition 4.3) and the coranks of the 15 merges are $(1,2,1,2,1,\dots,1)$, with sum 17. By Proposition 4.3, $\Delta = \prod_{a \ne 0} a^{\kappa_a}$ exactly. The orders of vanishing of $\Delta$ along the 15 linear forms, computed independently by interpolation in one basis variable, are the same numbers. For random independent patterns the linear forms account for only a part of the degree (for instance 7 to 10 out of 17 to 20 at $\delta = 7$), the rest being a factor that vanishes on no merge.

So a terminal pattern is one whose three-polynomial Sylvester determinant, irreducible or not for independent variables (Roth leaves this open), splits completely into the linear forms of $D$ when restricted to a subspace. No degeneration of the kind used in the GM-MDS proofs can certify such a determinant: every one of them lands on a zero. A proof must use the first-order term, that is show that $\Delta$ vanishes along $a$ to the order $\kappa_a$ and no further. For corank one this is the nonvanishing of the pairing $\lambda_a\bigl(\sum_i u_i \sum_{x \in R_i,\, x \notin H} (X - \bar x)^{-1}\bigr)$, where $(u_i)$ is the explicit dependency $G\,(v_i \circ L_U)^q$ of the merge, $\lambda_a$ spans its cokernel, and $H$ is a complement hyperplane of $a$. This combines the place with the derivation $\partial/\partial a$ (the Wronskian vector of note 17 section 3.1). I did not carry it out. **[open]**

### 6.3 Excess helps, multiplicities hurt

**[checked]** `30_merge.c` with overdetermined patterns ($\sum |R_i| = 2\delta + E$, "unsolvable" = no dependency), $n = 16$, exhaustive: at $\delta = 6$ the numbers of unsolvable patterns without an unsolvable merge are 25200, 3150, 0 for $E = 2, 3, 4$; at $\delta = 4$ and $\delta = 5$ there are none for $E = 2, 3, 4$.

**[checked, sampled]** `30_step.c`: random set patterns at $n = 32$, pushed forward along one random direction to 16 points (multiplicities $\le 2$), 20000 samples each. Fraction of the unsolvable push-forwards that have no unsolvable merge to 8 points:

| $\delta$ | $E = 2$ | $E = 3$ | $E = 4$ | $E = 6$ |
| --- | --- | --- | --- | --- |
| 13 | 12408 / 16555 | 5894 / 18138 | 1432 / 19044 | 46 / 19799 |
| 10 | 4098 / 17831 | | 6 / 19671 | 0 / 19972 |

Merges keep $\delta$ and $E$ and halve the number of points, so the relative excess doubles at each step while the multiplicities double too. The data say that the second effect wins at small excess: after a single merge most square patterns are already terminal. An induction through merges is therefore not a matter of handling a thin exceptional set. It needs, at every level, a direct theorem for the patterns that are crowded relative to their excess. In the list application the excess is $E \ge (3\tau - 2)n + 2$, at most $0.12\,n$ in the rate-1/2 window, with $\delta$ up to $n/2$: at $n = 32$ this is $E \le 4$, $\delta \approx 13$, the third column of the table.

### 6.4 What the robust arguments of Guo-Zhang and AGL give here

Nothing for the nonvanishing itself, for two reasons (read off from the arguments, not a theorem). (a) Their only input about generic points is BGM's theorem. Robustness to deleting $\epsilon n$ coordinates is derived from it by a count on the hypergraph, and the corresponding statement on a subspace is again a statement about patterns with excess, the regime of section 6.3: it shrinks the set of terminal patterns but I have no theorem that it empties it. (b) The probabilistic amplification uses that each variable occurs in the rows of one coordinate. On a subspace each of the $N$ variables occurs in the rows of $n/2$ coordinates, deleting those rows deletes half of the code, and there are at most $N$ faulty indices against at least $2^n$ agreement patterns: the union bound would need $\log_2 |F| \gtrsim n/N$. For the generic subspace no probability is needed at all, only the base nonvanishing, which is what is missing. For the real domain this confirms that the random-puncturing proofs give nothing.

## 7. The solution side: what a reduction preserves, and the exact missing piece

Here $\xi = u_0/u_1$, $u_0 + u_1 + u_2 = 0$, pairwise coprime, over $F_0 \supseteq \mathbb{F}_2(t)$ purely transcendental, $\delta = \max\deg u_i$, $m_i(x) = \mathrm{ord}_x u_i$ for $x \in D$, $M = \sum_i |m_i|$, $E(\xi) = M - 2\delta$. For $a \ne 0$ reduce at the place of $\{0, a\}$ after scaling $(u_i)$ to Gauss valuation 0: $\bar u_0 + \bar u_1 + \bar u_2 = 0$, $\bar G = \gcd$, $\bar\xi_a = \bar u_0/\bar u_1$. Call $a$ nondegenerate if no $\bar u_i$ is zero.

**Lemma 7.1 (excess is monotone). [proved]** For nondegenerate $a$: $E(\bar\xi_a) \ge E(\xi)$, with multiplicities counted on $D/a$.

*Proof.* Let $o_i = \mathrm{ord}_{\bar x}\bar u_i \ge m_i(x) + m_i(x + a) =: \mu_i$ and $g = \min_i o_i = \mathrm{ord}_{\bar x}\bar G$. Because $\sum \bar u_i = 0$ the minimum is attained twice. At most two of the $\mu_i$ are positive. In each of the cases (which two orders equal $g$, and which $\mu$ are positive) one checks $\sum_i o_i - \sum_i \mu_i \ge g$: for instance if $o_i = o_j = g \le o_l$ and $\mu_i, \mu_j > 0$, the difference is $(g - \mu_i) + (g - \mu_j) + o_l \ge o_l \ge g$. Hence $\sum_i (o_i - g) \ge \sum_i \mu_i - 2g$, and summing over classes the multiplicity mass of $\bar\xi_a$ is at least $M - 2\deg\bar G$, while $2\deg\bar\xi_a \le 2\delta - 2\deg\bar G$. $\square$

**Lemma 7.2 (translations, with multiplicity). [proved]** For $b \in D$: either $b \in \Pi(\xi)$ or $\sum_i \sum_x \min(m_i(x), m_i(x + b)) \le 2\delta$. (Note 17 Proposition 3.4, same proof: $u_0(X)u_1(X + b) - u_1(X)u_0(X + b)$ has degree $\le 2\delta$ and vanishes to that order.)

**Theorem 7.3 (periods of all reductions force a period). [proved]** Let $E = E(\xi) \ge 1$. Suppose that for every $a \ne 0$ there is a subspace $W_a \ni a$ of $D$ with $|W_a| \ge 2E$ such that $x \mapsto m_i(x) + m_i(x + a)$ is $W_a$-periodic for $i = 0, 1, 2$. Then each $m_i$ has fewer than $n/E$ nonzero Walsh coefficients besides the constant one, the three $m_i$ are invariant under a common subspace of codimension less than $3n/E$, and this subspace consists of periods of $\xi$: $|\Pi(\xi)| > n\,2^{-3n/E}$.

*Proof.* With $\hat f(\varphi) = \sum_x f(x)(-1)^{\varphi(x)}$, the transform of $f(x) + f(x + a)$ is $(1 + (-1)^{\varphi(a)})\hat f(\varphi)$, and a $W_a$-periodic function has its transform supported on $W_a^\perp$. So $\hat m_i(\varphi) = 0$ whenever $\varphi(a) = 0$ and $\varphi \notin W_a^\perp$. Let $\Sigma$ be the nonzero support of $\hat m_i$. Counting pairs $(a, \varphi)$ with $\varphi \in \Sigma$, $\varphi(a) = 0$: $|\Sigma|(n/2 - 1) \le (n - 1)(n/(2E) - 1)$, so $|\Sigma| < n/E$. $m_i$ is invariant under $\bigcap_{\varphi \in \Sigma}\ker\varphi$. For $b$ in the common subspace, $\sum_i\sum_x \min(m_i(x), m_i(x+b)) = M > 2\delta$ and Lemma 7.2 applies. $\square$

**How this isolates the problem.** Let PM be the solution form of the conjecture with multiplicities (note 17 section 6.1, item 4, stated there untested): *$E(\xi) \le \deg\ell$ for some additive $\ell = L_U^q$ with $\xi \in F(\ell)$*. S3 is its pattern form, the one I tested; the two say the same for a pattern whose dependency is unique up to a scalar. Assume PM in dimension $N - 1$, let $\xi$ have simple roots in $D$ and excess $E$, and call a direction $a$ **exact** if it is nondegenerate, $\bar G_a = 1$, and no root of $\xi$ outside $D$ reduces into $D/a$. For an exact $a$ the multiplicities of $\bar\xi_a$ are the push-forward of the $m_i$, its excess is $\ge E$ (Lemma 7.1), and it is a function of some $L_{\bar U}^q$ with $q|\bar U| \ge E$. If $q \ge 2$ every class of $a$ holds 0 or 2 points of each fibre, so $\sum_i |R_i \cap (R_i + a)| = M > 2\delta$ and $a$ is a period of $\xi$ (Lemma 7.2). If $q = 1$ the hypothesis of Theorem 7.3 holds at $a$ with $W_a$ the preimage of $\bar U$. Hence: **if every direction is exact and $E \ge 3n/N$, then $\xi$ has a nonzero period**, and with $E = cn$ a period group of index at most $2^{3/c}$. **[proved under these hypotheses, which are not established]** What stands between this and Conjecture P for linear excess is exactly the defect of exactness, $\deg\bar G_a$ plus the number of roots outside $D$ that reduce into $D/a$, which a priori is only bounded by $\delta - E$. The Fourier step tolerates an $\ell^1$ error of $o(\sqrt n)$ per direction, the same $\sqrt n$ threshold that note 04 found for phantom roots. The terminal patterns are the pattern-side face of the same thing: in the example of section 6.1 every admissible direction has $\deg\bar G_a = 3$.

## 8. A closed form for the three-set determinant

**Proposition 8.1 (Hankel form). [proved]** For pairwise disjoint $R_0, R_1, R_2$ with $|R_i| \le \delta$, $\sum|R_i| = 2\delta + 2$, put $s = \delta + 1 - |R_2|$ and $w(x) = Z_{R_2}(x)/(Z_{R_0}'(x) Z_{R_1}(x))$ for $x \in R_0$. The pattern is dependent iff the $s \times s$ Hankel matrix $(\mu_{i+j})_{i,j<s}$, $\mu_r = \sum_{x \in R_0} x^r w(x)$, is singular, and by the Cauchy-Binet formula, up to the nonzero factor $\mathrm{Res}(Z_{R_0}, Z_{R_1})$,
$$\det(\mu_{i+j}) \ \doteq\ \sum_{A \subseteq R_0,\ |A| = s}\ \frac{\prod_{x \in A,\, z \in R_2}(x - z)\ \prod_{x \in R_0 \setminus A,\, y \in R_1}(x - y)}{\prod_{x \in A,\, y \in R_0 \setminus A}(x - y)} .$$

*Proof.* $V_0 \cap V_1 = 0$ because $|R_0| + |R_1| > \delta$. A functional on $F[X]_{\le\delta}$ vanishes on $V_0$ iff it is a combination of the evaluations at $R_0$, and on $V_0 + V_1$ iff it is $\lambda_g(f) = \sum_{x \in R_0} g(x) f(x)/(Z_{R_0}'(x)Z_{R_1}(x))$ with $\deg g < |R_0| + |R_1| - \delta - 1 = s$ (the dual of the Reed-Solomon code of dimension $\delta + 1$ on $R_0 \cup R_1$). The pattern is dependent iff some $\lambda_g \ne 0$ kills $V_2 = Z_{R_2}F[X]_{<s}$, that is iff the form $(g, h) \mapsto \sum_{x \in R_0} g(x)h(x)w(x)$ on $F[X]_{<s}$ is degenerate. Cauchy-Binet gives $\sum_A \prod_{x \in A} w(x) \prod_{x < y \in A}(x - y)^2$, and $\prod_{x \in A} Z_{R_0}'(x) = \prod_{x<y \in A}(x-y)^2 \prod_{x \in A, y \in R_0 \setminus A}(x - y)$. $\square$

**[checked]** `30_checks.py` item 2: the Hankel matrix is singular exactly when the pattern is dependent, 800 random patterns at $n = 8$, half of them periodic.

So Conjecture P for square patterns is the statement that an explicit signed-free sum of $\binom{|R_0|}{s}$ products of linear forms of $D$ vanishes only for periodic configurations. A merge kills every term whose $A$ contains a point with $x + a \in R_2$, which is how section 6.1 looks in this form. I did not find a leading-term argument: in characteristic two the terms cancel in pairs.

## 9. The list bound, and what remains

**No unconditional bound.** For all words on a generic subspace the only list bound remains Theorem 5.1 of note 17, conditional on Conjecture P. Its values for the sizes of the brief (`30_checks.py` item 4, $\log_2$ of the bound, rate 1/2):

| $\tau$ | $N = 25$ | $N = 26$ | $N = 27$ | $N = 28$ |
| --- | --- | --- | --- | --- |
| $(0.6875,\ 0.7071)$ | 72.9 to 73.3 | 75.9 to 76.3 | 78.9 to 79.3 | 81.9 to 82.3 |
| $0.68$ | 97.5 | 101.5 | 105.5 | 109.5 |
| $0.675$ | 126.0 | 131.0 | 136.0 | 141.0 |
| $0.67$ | 165.6 | 171.6 | 177.6 | 183.6 |

At rates 1/4, 1/8, 1/16 the three-set statement says nothing below the Johnson radius (it needs $\tau \ge 1/2$, $5/12$, $3/8$), and the windows there, like $(5/8, 2/3]$ at rate 1/2, need the statement for four or more sets. Proposition 3.1 and Proposition 5.1 hold for any number of sets and give the form such a statement must have: spanning of $\sum_j Z_{E_j}F[X]_{<m_j}$ unless a subfamily, after removing a common factor, is pulled back through some $L_U^q$ and fails the ceiling count of Proposition 5.1 on the quotient. For four or more sets a subfamily can have a larger period group than the whole family (note 17 section 6.2), so the criterion must be a maximum over partitions as in BGM's Theorem 1.16. I did not test it, note 27 is about that case.

**What remains, precisely.**

1. **S3 for terminal patterns.** Prove that a pattern violating (D) and (S) all of whose merges satisfy (D) or (S) is independent. By section 6.2 this is a first-order statement: $\Delta$ vanishes along each $a$ exactly to the corank of the merge. The dependency of each merge is explicit, so the pairing of section 6.2 is computable in principle. If this is proved for all levels (with multiplicities), S3 follows by the induction of section 6, and with it P and the bound above.
2. **The weak form that suffices.** Theorem 5.1 of note 17 only needs: excess $E \ge cn$ implies $|\Pi| \ge c'E$. By section 7 this follows by induction if the common factors $\bar G_a$ of the reductions can be controlled for a positive fraction of the directions $a$. A bound $\deg\bar G_a + (\text{phantom landings}) = o(\sqrt n)$ for most $a$ would do, and I have no such bound.
3. **Base cases with multiplicities.** On two points the pattern is defined over $\mathbb{F}_2$ after scaling ($X^{\alpha_i}(X + 1)^{\beta_i}F[X]_{<c_i}$), so S3 at $N = 1$ is a statement about binomial coefficients modulo 2 and should be provable by Lucas' theorem. Not done.
4. **Four and more sets**, as above.

**Consequences for the design question.** Nothing changes with respect to note 17: on the generic model, thresholds down to about $0.678\,n$ at rate 1/2 remain conditional on P, and the present note adds evidence for P in the only form in which an inductive proof could use it, together with the reason why the inductive proof of the generic-points theorem does not transfer.

## 10. Reproduction

Under `doc/whir_soundness_gap_notes/scripts/`, C with the system compiler and `02_gf.h` ($\mathrm{GF}(2^{64})$, random basis from a fixed xorshift seed), Python 3 without packages.

- `30_merge.c`: `cc -O2 -o 30_merge 30_merge.c`, `./30_merge N delta [seed] [dump] [extra]`. Section 6.1 ($N = 4$, $\delta = 4..7$: 5 s to 3 minutes each) and the overdetermined patterns of section 6.3 (`./30_merge 4 6 0 0 1`, about one minute). With `dump = 1` it prints the terminal patterns.
- `30_crit.c`: `cc -O2 -o 30_crit 30_crit.c`, `./30_crit N delta [stride] [seed] [dump]`. Section 5.3. $N = 4$: $\delta = 2, 3$ seconds, $\delta = 7$ 45 s, $\delta = 4, 5, 6$ three to eight minutes each. The prediction is evaluated on every dependent pattern and on 1 in 64 of the independent ones. (A first version evaluated it on all patterns; its complete runs at $N = 3$ and at $N = 4$, $\delta = 2, 3$ also gave 0 mismatches.)
- `30_step.c`: `cc -O2 -o 30_step 30_step.c`, `./30_step N s delta extra samples [seed]`. Section 6.3, for instance `./30_step 5 1 13 0 20000` (20 s).
- `30_lib.py`, `30_checks.py`: `python3 30_checks.py` (under a minute). Proposition 4.2, Proposition 8.1, the degree and corank count of section 6.2, the table of section 9.
- `30_validate.py`: `python3 30_validate.py` (two minutes). Lemma 4.1 on random patterns.
- `30_orders.py`: `python3 30_orders.py` (a few minutes). Orders of vanishing of $\Delta$ along the linear forms, by interpolation in one basis variable at $\deg\Delta + 2$ values, for random patterns and for the terminal example of section 6.1.

## References

- [Lov] S. Lovett. MDS matrices over small fields: a proof of the GM-MDS conjecture. arXiv 1803.02523v2.
- [YH] H. Yildiz, B. Hassibi. Optimum linear codes with support constraints over small fields. arXiv 1803.03752v1.
- [BGM] J. Brakensiek, S. Gopi, V. Makam. Generic Reed-Solomon codes achieve list-decoding capacity. arXiv 2206.05256v4.
- [GZ] Z. Guo, Z. Zhang. Randomly punctured Reed-Solomon codes achieve the list decoding capacity over polynomial-size alphabets. arXiv 2304.01403v2 (later versions withdrawn, merged into [AGGLZ]).
- [AGGLZ] O. Alrabiah, Z. Guo, V. Guruswami, R. Li, Z. Zhang. Random Reed-Solomon codes achieve list-decoding capacity with linear-sized alphabets. arXiv 2304.09445v6.
- [Roth] R. M. Roth. Higher-order MDS codes. arXiv 2111.03210v2.
