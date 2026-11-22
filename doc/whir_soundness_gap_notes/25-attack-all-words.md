# 25. Attack on the list conjecture by theory: words that are not tops

Researcher 25, round 4. Every statement is tagged **[proved]** (proof in this note), **[quoted]** (from another note, not re-proved), **[checked]** (numerically, sizes stated) or **[conjectured]**. Scripts are `scripts/25_*`, section 9 says how to run them.

Notation. $F$ is a field of characteristic 2, $D \subset F$ an $\mathbb{F}_2$-subspace of dimension $N$, $n = 2^N$. Codewords are polynomials of degree at most $d$ ($d = k - 1$ genuine, $d = k - 1 + \ell$ with slack; at rate 1/2, $k = n/2$). A *list at agreement $T$* is a word $w : D \to F$ with distinct codewords $c_i$ and sets $S_i = \{x : c_i(x) = w(x)\}$, $|S_i| \ge T$. $Z_S = \prod_{s \in S}(X - s)$, $L_V = Z_V$ for a subspace $V$. "Generic" means that $D$ has an algebraically independent basis. In the computations $F = \mathrm{GF}(2^{64})$ with the leanVM modulus and a random basis, which gives rigorous statements for the generic model whenever the computed object is "a matrix has full rank" (a matrix of full rank at one specialization has full rank generically).

## 0. Summary

**Headline.** I did not find a family that beats the known ones inside a window. No word that is not a top was found whose list grows with $n$ at a fixed agreement fraction above $5/8$ (rate 1/2), above $1/4$ (rate 1/8) or above $1/8$ (rate 1/16). What I can offer instead is (a) two theorems valid for all words on every domain that kill whole classes of constructions, (b) an exact reduction of the most natural way to build a growing list from a word that is not a top (a periodic word and members indexed by a moving subspace) to a finite problem, solved for index up to 32 at rate 1/2, and (c) a precise list of what is still open, with one place that I consider the most plausible location of a counterexample if there is one.

| | statement | scope | status |
| --- | --- | --- | --- |
| 1.1 | Four list members with $c_1 + c_2 + c_3 + c_4 = 0$ force $T \le (n + 3d)/4$. So above $5n/8$ at rate 1/2 every list is a Sidon set of $(F[X], +)$ | all words, every domain | proved, attained at $5n/8$ |
| 1.2 | $2^j$ members forming an affine $\mathbb{F}_2$-subspace force $T \le d + (n - d)/2^j$: the thresholds $3/4, 5/8, 9/16, 17/32$ of the known families | all words, every domain | proved |
| 1.3 | Gluing by independent choices ($c_{ij} = a_i + b_j$) is impossible above $(n + 3d)/4$ | all words, every domain | proved |
| 2.4 | A $U$-periodic word $f \circ L_U$ with $\lvert D/U\rvert = M'$ has members periodic under a hyperplane $W$ of $U$ for more than $C(M')$ hyperplanes only through a *hyperplane family*: an identity in one parameter $\theta$ on the $M'$ labels | every subspace domain | proved |
| 2.6, 2.7 | A hyperplane family at rate 1/2 has agreement at most $2/3$, and none exists above $5/8$ for $M' \le 16$ (a balance condition and Parseval) | every subspace domain | proved |
| 2.8 | If the phantom factor of the members keeps its direction (it does in every known family), the agreement is at most $5/8$: $5/8$ is an exact barrier for that shape | every subspace domain | proved |
| 2.10 | A hyperplane family above $5/8$ with $M' \ge 64$ forces, on the $M'$-point label domain, a word with at least $M'/4 - 5$ codewords at the same agreement fraction | every subspace domain | proved |
| section 2.6 | No hyperplane family above $5/8$ for $M' = 8, 16$ (all types) and $M' = 32$ (all types the balance condition allows); none above the flats at rates 1/4 (genuine), 1/8, 1/16 for $M' \le 16$ | generic domain | checked, exhaustive over types |
| section 2.7 | No family indexed by subspaces of codimension 2 or 3 of $U$ above $5/8$ on label domains of 16 and 32 points | generic domain | checked, exhaustive over agreement sets |
| 3.1 to 3.3 | Rational words $P/Q$: fewer than $T - d$ poles give no member at all. The list is a common-residue class of locators modulo $Q$. For poles in general position the list is 1 | every domain | proved, checked at $n = 16, 32$ |
| 4.2 | Error vectors with values in $g(x)\cdot\mathbb{F}_2$ (indicator-type errors, any multiplier $g$): at most $1/(2\tau - 1)^2$ members at rate 1/2 | every domain | proved |
| 6 | Interleaving and extension fields give no list beyond single lanes over $K$ below $2^{62}$ | every domain | quoted (note 14) |
| 7 | The $\mathbb{F}_2(x)$-identities of the real domain do not multiply: their number does not depend on $N$ | real domain | quoted (note 13), with one proved remark |

**What is not covered.** (i) Hyperplane families with $M' \ge 64$ and agreement in $(5/8, 0.664)$: the counting conditions allow them from $M' = 64$ on ($84/128$), I cannot enumerate their types, and Theorem 2.10 only says they need a list of at least 11 on a 64-point domain at agreement $0.65$, which multiset tops may well provide. This is the most plausible location of a counterexample that I know (section 2.8). (ii) Families indexed by subspaces of codimension $j \ge 2$ on label domains of 64 points or more. (iii) Any growth that is not tied to the affine group of $D$. (iv) The low-rate windows beyond $M' = 16$.

**How strong is the evidence that arbitrary words do not help.** At the sizes where everything can be enumerated (note 18: all words at $n = 16$; this note: all periodic words with moving-subspace members up to 32 labels, and index 32 for hyperplanes) nothing that is not a top grows, and every growing family known is forced by Theorem 1.1, Proposition 1.2 and Theorem 2.8 to sit exactly at the dyadic thresholds. Against that, nothing here is a proof for all words, the place method fails for them (note 12), and the first size at which the simplest non-top mechanism is not excluded by counting is $M' = 64$, beyond every exhaustive computation of the swarm. My assessment: the conjecture is more likely true than false in the rate-1/2 window, with real but moderate confidence above $2/3$ (where three independent arguments agree: Proposition 2.6, note 17's conditional theorem, the multiset bound) and less between $5/8$ and $2/3$.

## 1. Two facts for all words on every domain

### 1.1 Additive quadruples

**Theorem 1.1. [proved]** Let $D$ be any set of $n$ points of a field of characteristic 2 and let a list at agreement $T$ for polynomials of degree at most $d$ contain four distinct members with $c_1 + c_2 + c_3 + c_4 = 0$. Then
$$4T \le n + 3d .$$

*Proof.* At a point $x$ the four values sum to zero. If three of them equal $w(x)$, so does the fourth. So the number $\mu(x)$ of members that agree with $w$ at $x$ is $0, 1, 2$ or $4$. If $\mu(x) = 2$, say $c_i(x) = c_j(x) = w(x)$, then $x$ is a zero of $c_i - c_j$, which is one of the three polynomials $c_1 - c_2 = c_3 - c_4$, $c_1 - c_3 = c_2 - c_4$, $c_1 - c_4 = c_2 - c_3$. If $\mu(x) = 4$, $x$ is a zero of all three. So $\mu(x) \le 1 + \#\{\text{pairings vanishing at } x\}$, each of the three polynomials is nonzero of degree at most $d$, and $4T \le \sum_x \mu(x) \le n + 3d$. $\square$

**Corollary. [proved]** At rate 1/2 with $d = n/2 - 1 + \ell$: a list at agreement $T > 5n/8 + 3(\ell - 1)/4$ contains no four members with zero sum. It is a Sidon set in the additive group of polynomials. For genuine codewords this holds from $T = 5n/8$ on.

**Proposition 1.2 (affine subspaces). [proved]** If a list contains $c_0 + \sum_i \epsilon_i a_i$ for all $\epsilon \in \mathbb{F}_2^j$, with $a_1, \dots, a_j$ linearly independent over $\mathbb{F}_2$, then $2^j T \le n + (2^j - 1)d$, that is $T \le d + (n - d)/2^j$.

*Proof.* At $x$ the members agreeing with $w$ are the $\epsilon$ with $\sum \epsilon_i a_i(x) = w(x) - c_0(x)$: empty or a coset of $\ker_x = \{\epsilon : \sum\epsilon_i a_i(x) = 0\}$. A nonzero $\epsilon$ lies in $\ker_x$ for at most $d$ points. So $2^j T \le \sum_x |\ker_x| \le n + (2^j - 1)d$. $\square$

Remarks. (i) At rate 1/2 these thresholds are $3/4, 5/8, 9/16, 17/32$: exactly where the known growing families live, and exactly the generalized Singleton bound for $2^j$ members on generic points (note 17, Theorem 1.1). So on every domain, lists with additive structure obey the generic-points bound, and the families at $5n/8$ are extremal for it. **[checked]** (`25_sidon_check.py`): among the 504 members of $(y^2 + \eta y)^5$ at $(n, d, T) = (16, 8, 10)$ there are 14 additive quadruples, each with multiplicities in $\{0, 1, 2, 4\}$ and total exactly $4T$, so Theorem 1.1 is attained. The list of 16 that note 18 found at $(16, 8, 11)$, one step above the threshold, has none (recovered by linear algebra on a second domain, 16 distinct codewords, 0 coincidences $c_i + c_j = c_k + c_l$). (ii) For the low rates the theorem bites only near the top of the window: $(n + 3d)/4 = 0.34n$ at rate 1/8. Proposition 1.2 with $j = 3, 4$ excludes affine subspaces of 8 members above $0.234n$ at rate 1/8 and of 16 members above $0.121n$ at rate 1/16, that is in the whole windows.

**Corollary 1.3 (independent gluing). [proved]** Suppose a word is glued from pieces so that two parts of a member can be chosen independently and add: the list contains $a_i + b_j$ for $i, j \in \{1, 2\}$ with $a_1 \ne a_2$, $b_1 \ne b_2$. Then $T \le (n + 3d)/4$. So a product of two lists, the mechanism by which a glued word could have a list exponentially larger than its pieces, cannot exist above $5n/8$ at rate 1/2. This answers "what the best gluing gives between $5/8$ and $0.707$" for additive gluing: nothing.

*Proof.* $(a_1 + b_1) + (a_1 + b_2) + (a_2 + b_1) + (a_2 + b_2) = 0$. $\square$

A gluing in which the dependence is not additive is not excluded by this: four members with agreement sets $A_i \sqcup B_j$ ($A_i$ in one region, $B_j$ in another) are allowed by pairwise counting up to $\tau = 2/3$ (**[proved]**: $c_{11} - c_{21}$ vanishes on $(A_1 \cap A_2) \cup B_1$ and $c_{11} - c_{12}$ on $(B_1 \cap B_2) \cup A_1$, and with $|A_1 \cap A_2| \ge 2|A_i| - |D_1|$, $|B_1 \cap B_2| \ge 2|B_j| - |D_2|$ the sum of the two inequalities is $3T \le n + 2d$, and nothing more follows from pairs). Section 2 treats the structured version of that.

### 1.2 Linear parametrizations and the Sidon lines

The Sidon tangent lines of note 02 ($c_a = aX + a^2$, $a$ in a Sidon set) are the smallest case of a list parametrized $\mathbb{F}_2$-linearly: $a \mapsto c_a$ is additive. Theorem 1.1 says that this is not an accident of that example.

**Corollary 1.4. [proved]** Let $P$ be a finite $\mathbb{F}_2$-vector space, $v \mapsto c_v$ an injective additive map from $P$ to polynomials of degree at most $d$, and $A \subseteq P$ such that $\{c_0 + c_a : a \in A\}$ is contained in a list at agreement $T > (n + 3d)/4$. Then $A$ is a Sidon set of $P$, so $|A| \le \sqrt{2|P|} + 1$, and at a point $x$ the members that agree with $w$ are $A \cap (v_x + N_x)$ for the subspace $N_x = \{v : c_v(x) = 0\}$, at most $\sqrt{2|N_x|} + 1$ of them, with $\sum_x (|N_x| - 1) \le (|P| - 1)d$.

Putting the three inequalities together gives $\tau|A| \lesssim \sqrt{2\rho|P|}$, which is the Johnson bound again and no more **[proved]**. So linear families are neither excluded below the Johnson radius nor produced by this. What a constant-rate analogue of the Sidon lines needs is visible, though: the kernels $N_x$ must have index about $1/\rho$ in $P$ for most $x$, so at rate 1/2 the form $(x, v) \mapsto c_v(x)$ must have $\mathbb{F}_2$-rank one in $v$ at almost every point. The only example I know is $c_v(x) = \kappa\langle x, v\rangle$, the first-order Reed-Muller code inside degree $\le n/2$, whose lists are at most $1/(2\tau - 1)^2$ (Proposition 4.2). I found no other. Note 18 (Corollary 5.4) proves by a different argument that the Sidon lines themselves do not scale.

## 2. Periodic words and families that grow by moving a subspace

### 2.1 Why this mechanism

Every family in the notes whose size grows with $n$ grows because a subspace moves: the word is fixed, and there is one member, or a bounded number, for each subspace $W$ of a given kind (flats, the $56n - 392$ members of $L_U^5$, the trees of [DKTZ26], the Gold sets). The lifting lemma (note 02, Lemma 3) explains the other half: a list on a label domain $L_W(D)$ lifts to $D$ at the same rate and agreement with constant size. So the scheme "a $U$-periodic word $w = f \circ L_U$, and members that are periodic under a smaller subspace $W \le U$ which varies" is the general form of a growing family obtained by lifting, and it is where a non-top word can enter: $f$ is an arbitrary function on the $M' = |D/U|$ labels. In the generic model there is also a reason from symmetry: a word with values in the fixed field of the group $G_U$ of linear maps of $D$ that preserve $U$ and act trivially on $D/U$ has a $G_U$-invariant list, so one member that is periodic under a hyperplane $W$ of $U$ and not under $U$ brings a member for each of the $|U| - 1$ hyperplanes (this is how one member of $L_U^5$ becomes $56n$). This paragraph is motivation, not a theorem: the statements proved below do not use the generic model except where said. The same reasoning for the translation group gives the words that are covariant under all translations modulo codewords, and those are exactly the words $X^{n/2}\ell(X)$, which contain the padded hyperplanes with a subspace as padding: **[proved]** a polynomial $w$ of degree $< n$ has $\deg(w(X + t) - w(X)) \le n/2$ for all $t \in D$ if and only if $w = X^{n/2}\ell(X)$ plus a polynomial of degree $\le n/2$, with $\ell$ linearized of degree $\le n/4$ (the coefficient of $X^i$, $i > n/2$, in $w(X + t) - w(X)$ is a polynomial in $t$ of degree $< n/2$ with $n$ roots, so $w_j\binom{j}{i}$ vanishes for $n/2 < i < j$, and by Lucas $j - n/2$ is a power of two). These are the words of note 18's list of 16, they are multiset tops in every case examined there, and note 12 Theorem A bounds them. I did not study them further.

**Lemma 2.1 (periods). [proved]** Let $w(x + a) = w(x)$ on $D$ for some $a \in D$, and let $c$ of degree $\le d$ have full agreement set $S$ with $|S| > d$. Then $c(X + a)$ has full agreement set $S + a$, and $c(X + a) = c(X)$ if and only if $S + a = S$.

*Proof.* $c(x + a) = w(x + a) = w(x)$ iff $x + a \in S$. If $S + a = S$ the two polynomials agree on more than $d$ points. $\square$

### 2.2 Hyperplanes of $U$: the normal form

Setting, used in sections 2.2 to 2.6. $U \le D$, $M' = |D/U| = 2^r \ge 4$, $h = M'/2$, $\Lambda_U = L_U(D)$ (the $M'$ labels, a subspace of $F$ of dimension $r$, generic if $D$ is), $L(u) = L_{\Lambda_U}(u) = u^{M'} + \sum_{i<r} l_i u^{2^i}$. The word is $w = f \circ L_U$ for an arbitrary $f : \Lambda_U \to F$. For a hyperplane $W$ of $U$: $\Lambda_W = L_W(D)$ has $2M'$ points, $\eta_W$ is the nonzero element of $L_W(U)$, and $L_U = q \circ L_W$ with $q(Y) = Y^2 + \eta_W Y$. A $W$-periodic polynomial is $\tilde c \circ L_W$, and at rate 1/2 it has degree $\le n/2 - 1 + \ell$ with $1 \le \ell \le |W|$ iff $\deg\tilde c \le M'$ ("slack"), and degree $< n/2$ iff $\deg\tilde c \le M' - 1$ ("genuine"). Put $d' = M'$ or $M' - 1$ and $h' = \lfloor d'/2\rfloor$. The protocol's $\ell = 6$ is the slack case.

**Lemma 2.2 (the parameter). [proved]** For $\theta \in F$ define $\alpha_{r-1} = \theta^{h}$, $\alpha_{i-1} = (\theta^{M'} l_i + \alpha_i)^{1/2}$ for $i = r - 1, \dots, 1$, $s(\theta) = \alpha_0 + \theta^{M'} l_0$ and $\Psi_\theta(u) = \sum_{i<r}\alpha_i u^{2^i}$. Then:

1. $\Psi_\theta(u)^2 + \Psi_\theta(u) = s(\theta)\,u + \theta^{M'}L(u)$, so $\Psi_\theta^2 + \Psi_\theta = s(\theta)u$ on $\Lambda_U$.
2. The $\alpha_i$ and $s$ are additive polynomials in $\theta$, $\Psi_\theta = \sum_{e<r}\theta^{2^e}\omega_e(u)$ with $\omega_e$ linearized of degree $2^e$ and $\omega_0 = u$, so $\Psi_{\theta + \theta'} = \Psi_\theta + \Psi_{\theta'}$, and $s(\theta) = \theta + \dots + l_0\theta^{M'}$ is separable of degree $M'$.
3. If $s(\theta) \ne 0$ and $\eta = s(\theta)^{-1/2}$, the points $y = \eta(\Psi_\theta(u) + \epsilon)$, $u \in \Lambda_U$, $\epsilon \in \mathbb{F}_2$, form a subspace $\Lambda_\theta$ of dimension $r + 1$ with $y^2 + \eta y = u$.
4. For every hyperplane $W$ of $U \le D \subset F$ and every $\mathbb{F}_2$-linear section $\sigma : \Lambda_U \to \Lambda_W$ of $q$ there is exactly one $\theta \in F$ with $\Lambda_\theta = \Lambda_W$ and $\eta\Psi_\theta = \sigma$. The $M'$ values of $\theta$ belonging to one $W$ are a coset of $\Theta_0 = \ker s$, and $\theta_0 \mapsto \Psi_{\theta_0}|_{\Lambda_U}$ is a bijection from $\Theta_0$ to the linear functionals $\Lambda_U \to \mathbb{F}_2$.

*Proof.* (1) Compare the coefficients of $u^{2^i}$ in $\Psi^2 + \Psi + su$ and $\alpha_{r-1}^2 L$: they are $\alpha_{i-1}^2 + \alpha_i = \theta^{M'}l_i$ for $i \ge 1$ and $\alpha_0 + s = \theta^{M'}l_0$. (2) By descending induction $\alpha_i = \sum_{j \ge i} c_{ij}\theta^{2^j}$ with $c_{ii} = 1$: the square root of such a sum with $j \ge i \ge 1$ is again a polynomial. (3) $y^2 + \eta y = \eta^2(\Psi^2 + \Psi) = \eta^2 s u$ on $\Lambda_U$, and the set is closed under addition because $\Psi_\theta$ is additive. (4) The linearized polynomial $\Psi$ of degree $\le h$ with $\Psi(u_i) = \sigma(u_i)/\eta_W$ on a basis satisfies $\Psi^2 + \Psi = u/\eta_W^2$ on $\Lambda_U$, so $\Psi^2 + \Psi + u/\eta_W^2$ is a multiple of $L$, and its coefficients obey the recursion with $\theta$ the $h$-th root of the leading coefficient of $\Psi$. Two sections differ by a functional with values in $\{0, \eta_W\}$. $\square$

**Proposition 2.3 (normal form). [proved]** Every polynomial $\tilde c$ of degree $\le d'$ is uniquely $\tilde c(Y) = g(q(Y)) + (Y/\eta)\,G(q(Y))$ with $\deg g \le h'$, $\deg G \le h - 1$, and it is a polynomial in $q$ (that is, $\tilde c \circ L_W$ is $U$-periodic) iff $G = 0$. At the label $y = \eta(\Psi_\theta(u) + \epsilon)$ it agrees with $f \circ q$ iff $f(u) = g(u) + (\Psi_\theta(u) + \epsilon)G(u)$. So it agrees at both labels over $u$ iff $G(u) = 0$ and $f(u) = g(u)$, and at exactly one iff $G(u) \ne 0$ and $(f(u) - g(u))/G(u) - \Psi_\theta(u) \in \mathbb{F}_2$.

*Proof.* $\tilde c(Y) + \tilde c(Y + \eta)$ is invariant under $Y \mapsto Y + \eta$, so it is $G(q(Y))$, and $\tilde c - (Y/\eta)G(q)$ is invariant. Degrees: $2\deg G + 1 \le d'$ and $2\deg g \le d'$. $\square$

**Definition.** A *type* is $(A, B, \chi)$ with $A, B \subseteq \Lambda_U$ disjoint, $\chi : B \to \mathbb{F}_2$. Put $p = |A|$, $s' = |B|$, $C = A \sqcup B$. A member of that type at $\theta$ is a pair $(g, G_1)$, $G_1 \ne 0$, $\deg g \le h'$, $\deg G_1 \le h - 1 - p$ with
$$f = g + (\Psi_\theta + \chi)\,Z_A\,G_1 \quad\text{on } C \qquad (\text{the product is } 0 \text{ on } A). \tag{$\ast$}$$
Its agreement on the $2M'$ labels is $|S| = 2p + s'$, and on $D$ it is $(|S|/2M')\,n$. Write $\mathcal{V}_\theta = P_{\le h'}|_C + (\Psi_\theta + \chi)Z_A P_{\le h - 1 - p}|_C \subseteq F^C$. A *hyperplane family* of that type is a word $f$ with $f|_C \in \mathcal{V}_\theta$ for all $\theta$ and $f|_C \notin P_{\le h'}|_C$.

The count: $\mathcal{V}_\theta$ has codimension $|S| - d' - 1$ in $F^C$ when $|S| > d'$ (the map $(g, G_1) \mapsto g + (\Psi_\theta + \chi)Z_AG_1$ is then injective, because a kernel element is a $W$-periodic polynomial of degree $\le d'$ with more than $d'$ zeros). So one member at one $\theta$ costs the generic number of conditions, and a family is an intersection over a one-parameter family of subspaces.

**Proposition 2.4 (growth is an identity). [proved]** Fix $U \le D \subset F$ and $f$. Either some type is a hyperplane family, and then every hyperplane $W$ of $U$ carries at least $2^{\delta + 1}$ members that are $W$-periodic and not $U$-periodic at agreement $(|S|/2M')n$, $\delta$ the affine dimension of $B$ (above $5/8$ this is $2M'$ members per hyperplane, and the list has at least $2n - 2M'$ members, since a polynomial periodic under two hyperplanes of $U$ is $U$-periodic). Or the number of hyperplanes of $U$ carrying a member at agreement $> d'|W|$ that is $W$-periodic and not $U$-periodic is at most $4^{M'}M'^2/4$, whatever $n$ is.

*Proof.* For a type, $f|_C \in \mathcal{V}_\theta$ says that the matrix of the injective map above, augmented by the column $f$, has no larger rank. Its entries are polynomials of degree $\le h$ in $\theta$ in at most $h - p$ columns, so the condition is the vanishing of polynomials of degree $\le h(h - p) \le M'^2/4$ in $\theta$: it holds for all $\theta$ or for at most $M'^2/4$ values. There are at most $4^{M'}$ pairs $(A, B, \chi)$ up to the choice of section. By Lemma 2.2 (4) every hyperplane is some $\theta \in F$ with $s(\theta) \ne 0$, the member is then defined over $F$ and has $G_1 \ne 0$ because $f|_C$ is not a polynomial of degree $\le h'$, and the members of one $W$ are those of the types $\chi + a$, $a$ an affine function, distinct for distinct restrictions $a|_B$ (Lemma 2.5 below). $\square$

Validation. **[checked]** `25_periodic1.c` enumerates all types on $M' = 8$ and $16$ labels and intersects $\mathcal{V}_\theta$ over five random $\theta$. It finds exactly the known families and nothing else at or below $5/8$: for $M' = 8$, slack, $|S| = 10$: 56 types $(3, 4)$ ($B$ an affine plane, $A$ three of the four other labels, the word $u^5$, which is note 02's Theorem 5) and 28 types $(2, 6)$ (the padding family $u^4 Z_A$, $A$ any pair); for $M' = 16$, $|S| = 20$: 1820 types $(4, 12)$ (the padding family $u^8 Z_A$, $A$ any 4-set, note 01 section 3.4) and 840 types $(6, 8)$ (the lift of $u^5$); genuine at $|S| = 9$ and $19$: the padding families $u^4 Z_A$ with $|A| = 1$ and $u^8 Z_A$ with $|A| = 3$, 8 and 560 types.

### 2.3 Counting: the balance condition

**Lemma 2.5 (conjugates). [proved]** If $f$ is a hyperplane family of type $(A, B, \chi)$ then it is one of type $(A, B, \chi + a)$ for every affine $a : \Lambda_U \to \mathbb{F}_2$, and when $G_1$ does not vanish on $B$ (which can be assumed, moving the zeros to $A$) the members of types $\chi + a$ and $\chi + a'$ over one $W$ are distinct unless $a = a'$ on $B$.

*Proof.* $\mathcal{V}_{\theta + \theta_0}(\chi) = \mathcal{V}_\theta(\chi + \Psi_{\theta_0})$ for $\theta_0 \in \Theta_0$ by additivity, and $\mathcal{V}_\theta(\chi + 1) = \mathcal{V}_\theta(\chi)$ because $g + (\Psi + \chi)Z_AG_1 = (g + Z_AG_1) + (\Psi + \chi + 1)Z_AG_1$. The members of types $\chi + a$ and $\chi + a'$ pick different labels over the points of $B$ with $a \ne a'$, where each agrees at exactly one label. $\square$

**Proposition 2.6 (balance). [proved]** A hyperplane family of type $(A, B, \chi)$ at rate 1/2 with $s' \ge 2$ satisfies $p + s' \le M'$ and, for every affine hyperplane $H$ of $\Lambda_U$ that does not contain $B$,
$$2p + |B \cap H| \le d' .$$
Consequently $4p + s' \le 2d'$ and $|S| \le 4M'/3$: the agreement fraction of a hyperplane family is at most $2/3$. If moreover $|S| > d' + M'/4$ (above $5/8$), then $B$ lies in no affine hyperplane, and with $b = 1_B$ and $\beta = 2d' - 4p - s'$: $|\hat b(\varphi)| \le \beta$ for all $\varphi \ne 0$ and $\beta^2 \ge s'(M' - s')/(M' - 1)$ (Parseval).

*Proof.* Let $a$ be the affine function with zero set $H$. It is not zero on $B$, so the members of types $\chi$ and $\chi + a$ over one $W$ are distinct polynomials of degree $\le d'$ in the label variable, and they agree with the word, hence with each other, at the $2p$ labels over $A$ and at one label over each point of $B \cap H$. Some hyperplane cuts $B$ properly, and adding the inequalities for it and its complement gives $4p + s' \le 2d'$, so $3|S| = (4p + s') + 2(p + s') \le 2d' + 2M'$. If $B$ lies in a hyperplane, $s' \le M'/2$ and $|S| = (4p + s')/2 + s'/2 \le d' + M'/4$. $\square$

The condition is void for the hyperplanes containing $B$, and it has to be: in the $5/8$ family of type $(3, 4)$ on 8 labels $B$ is an affine plane, $2p + s' = 10 > 8$, and equality $4p + s' = 2d'$ holds.

**Corollary 2.7. [proved]** At rate 1/2 there is no hyperplane family with agreement above $5/8$ for $M' = 8$ and $M' = 16$, with or without slack. For $M' = 32$ only $|S| = 41$ with $(p, s') = (9, 23)$ or $(10, 21)$ passes Parseval.

*Proof.* `25_balance.py` evaluates the Parseval form for all $(p, s')$, and checks the balance condition itself (over the hyperplanes not containing $B$, together with $|S| \le d' + M'/4$ when one contains it) over all pairs $(A, B)$ for $M' = 8, 16$ and $|S| > 5M'/4$: none of the 56, 496288, 110968, 11440 pairs passes. By hand for $M' = 16$, $|S| = 21$, $(p, s') = (5, 11)$: $\beta = 1$ and $\beta^2 = 1 < 55/15$. $\square$

The largest $|S|$ that the counting allows (an upper bound, since sets $B$ with such flat spectra need not exist):

| $M'$ | 8 | 16 | 32 | 64 | 128 | 256 | 512 | 1024 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| largest $\lvert S\rvert$, slack | 10 | 20 | 41 | 84 | 168 | 338 | 679 | 1360 |
| fraction | 0.6250 | 0.6250 | 0.6406 | 0.6562 | 0.6562 | 0.6602 | 0.6631 | 0.6641 |

So counting leaves room in $(5/8, 2/3)$ from $M' = 32$ on, and from $M' = 128$ on the constraint on $B$ is loose (a 40-subset of $\mathbb{F}_2^7$ with all Walsh coefficients at most 8). This is the same interval in which note 17 finds no constraint on triples.

### 2.4 The barrier at $5/8$ for members whose phantom factor keeps its direction

In every known family the polynomial $G$ of Proposition 2.3 is $Z_A$ times a constant: the members over different hyperplanes differ in $g$ and in a scalar. For that shape $5/8$ is exact.

**Theorem 2.8. [proved]** Let $f$ be a hyperplane family of type $(A, B, \chi)$ at rate 1/2 in which $G_1 = \lambda(\theta)G_\ast$ for a fixed polynomial $G_\ast$ of degree $\gamma_\ast$ and a scalar $\lambda(\theta)$. If $s' > h + \gamma_\ast$, then $p + \gamma_\ast \le M'/4$ and $|S| \le 5M'/4$. For $|S| > 5M'/4$ the hypothesis $s' > h + \gamma_\ast$ holds whenever $\gamma_\ast = 0$. So no hyperplane family above $5/8$ has $G = \lambda(\theta)Z_A$.

*Proof.* Divide $(\ast)$ on $B$ by $Z_A$: with $\phi = (f - g_0)/Z_A$ for the interpolant $g_0$ of $f$ on $A$, $\phi = \tilde g_\theta + \lambda(\theta)(\Psi_\theta + \chi)G_\ast$ on $B$ with $\deg\tilde g_\theta \le a := h' - p$. Subtracting the equations for $\theta$ and $\theta'$ after division by $\lambda$, and using $\Psi_\theta - \Psi_{\theta'} = \Psi_{\theta + \theta'}$: $\Psi_\tau G_\ast \in P_{\le a}|_B + F\phi|_B$ for generic $\tau$, hence for all $\tau$, hence $\omega_e G_\ast \in P_{\le a}|_B + F\phi|_B$ for each $e < r$ (the $\tau^{2^e}$ are linearly independent functions). The classes of the $\omega_eG_\ast$ modulo $P_{\le a}|_B$ therefore span at most a line. But $\omega_eG_\ast$ has degree exactly $2^e + \gamma_\ast \le h + \gamma_\ast < s'$, so a combination of those with $2^e + \gamma_\ast > a$ that lies in $P_{\le a}$ on the $s'$ points of $B$ is zero as a polynomial. Hence at most one $e$ has $2^e + \gamma_\ast > a$, that is $h/2 + \gamma_\ast \le h' - p$. Then $|S| = 2p + s' \le p + M'$. For the last claim: $4p + s' \le 2M'$ and $2p + s' > 5M'/4$ give $s' > M'/2 = h$. $\square$

The reason behind all the known families, in this language. **[proved]** On an affine flat $B$ of dimension $b$ every linearized polynomial is an affine map, so $\Psi_\theta|_B$ lies in the span of $1, u, u^2, \dots, u^{2^{b-1}}$ restricted to $B$, for every $\theta$. With $a = 2^{b-1} - 1$ and $G_1$ constant, $P_{\le a}|_B + F\Psi_\theta|_B = P_{\le a}|_B + Fu^{2^{b-1}}|_B$ does not depend on $\theta$, and $\phi = u^{s'/2}$ is a family with $|S| = M' + 2$: agreement $1/2 + 1/M'$, the glued families of note 02 ($5/8$ for $M' = 8$). Replacing "affine" by "Reed-Muller degree $t$" does not seem to give more, by a parameter count that I did not turn into a proof: the functions of degree $\le t$ on a $b$-flat have dimension $\sum_{i \le t}\binom{b}{i}$, the products $u^i$ and $\Psi_\theta u^i$ stay in that space only for $i$ of binary weight $\le t$ and $\le t - 1$, so $2a + 1 \le 2^{t+1} - 1$, and the two numbers are equal only for $b = t + 1$, which is again $|S| = M' + 2$.

### 2.5 Bootstrap: a family forces a large list on the label domain

**Lemma 2.9 (the limit $\theta \to 0$). [proved]** Let $f$ be a hyperplane family of type $(A, B, \chi)$ with slack, and for an affine $a$ let $B^a = \{u \in B : \chi(u) = a(u)\}$, $X_a = A \cup B^a$, so $X_a \cup X_{a+1} = C$ and $|X_a| + |X_{a+1}| = |S|$. If $|B^a| > h - p$ and $|B^{a+1}| > h - p$ ("$a$ is nondegenerate"), there are polynomials $\gamma(a) \ne \gamma(a + 1)$ of degree $\le h$ with $f = \gamma(a)$ on $X_a$ and $f = \gamma(a + 1)$ on $X_{a+1}$. All but at most $2M's'/(|S| - M')^2 < 32$ of the $2M'$ affine functions are nondegenerate when $|S| > 5M'/4$.

*Proof.* By Lemma 2.5 assume $a = 0$. The map $\mu_\theta : (g, G_1) \mapsto g + (\Psi_\theta + \chi)Z_AG_1$ is polynomial in $\theta$, $\Psi_0 = 0$, and $\mu_0$ is injective: a kernel element has $g = 0$ on $X_0$, at least $h + 1$ points, so $g = 0$, and then $G_1 = 0$ on $B^1$, more than $h - 1 - p$ points. The minors that express $f \in \mathrm{im}\,\mu_\theta$ vanish for all $\theta$, hence at $\theta = 0$, so $f = g + \chi Z_AG_1$: $\gamma(0) = g$, $\gamma(1) = g + Z_AG_1$. They differ because $f|_C$ is not a polynomial of degree $\le h$. For the count, the events $a(u) = \chi(u)$, $u \in B$, are pairwise independent for a uniformly random affine $a$, so $|B^a|$ has mean $s'/2$ and variance $s'/4$, and Chebyshev applies with deviation $(s' + 2p - M')/2$. $\square$

So a family at index $M'$ produces, on the $M'$-point domain $\Lambda_U$ and for the same code rate, codewords agreeing with $f$ on the sets $A \cup (B \cap \{\chi = a\})$ for almost all affine $a$: a list problem one level down.

**Theorem 2.10 (bootstrap). [proved]** Let $f$ be a hyperplane family with slack, $M' \ge 64$ and $|S| > 5M'/4$. Then $f$ is at distance more than $M'/8 - \sqrt{M'}/2$ on $C$ from every polynomial of degree $\le M'/2$, and there are at least $M'/4 - 5$ distinct polynomials of degree $\le M'/2$ each agreeing with $f$ on at least $|S|/2$ points of $\Lambda_U$. In particular $\Lambda_{\Lambda_U}(\tau M') \ge M'/4 - 5$ for the agreement fraction $\tau = |S|/2M'$ of the family.

*Proof.* Let $\mathcal{N}$ be the nondegenerate affine functions, $|\mathcal{N}| > 2M' - 32$, closed under $a \mapsto a + 1$. For a polynomial $\gamma$ of degree $\le h$ let $M_\gamma = \{u \in C : f(u) \ne \gamma(u)\}$ and $\mathcal{A}_\gamma = \{a \in \mathcal{N} : \gamma(a) = \gamma\}$. (i) *No near codeword.* If $|M_\gamma| \le M'/8 - \sqrt{M'}/2$, the Chebyshev count with deviation $(|S| - M')/2 - |M_\gamma| > \sqrt{s'}/2$ gives an $a$ with $|X_a|, |X_{a+1}| \ge h + 1 + |M_\gamma|$. Then $\gamma(a) - \gamma$ vanishes on $X_a \setminus M_\gamma$, more than $h$ points, so $\gamma(a) = \gamma$, likewise $\gamma(a + 1) = \gamma$, a contradiction. (ii) *A codeword serves few functions.* For $a \in \mathcal{A}_\gamma$, $\gamma = f$ on $X_a = A \cup B^a$, so $M_\gamma \subseteq B \setminus B^a$ and all $a \in \mathcal{A}_\gamma$ equal $\chi + 1$ on $M_\gamma$, and the number of affine functions with prescribed values on a set of size $> 2^{r - 1 - i}$ is at most $2^i$. By (i) and $M' \ge 64$, $|M_\gamma| > M'/16$, so $|\mathcal{A}_\gamma| \le 8$. (iii) Two distinct $\gamma, \gamma'$ in the image agree with $f$, hence with each other, on $A \cup (B \setminus (M_\gamma \cup M_{\gamma'}))$, so $|M_\gamma| + |M_{\gamma'}| \ge p + s' - h = |S| - p - h \ge (3|S| - 3M')/2 > 3M'/8$, using $2p \le 2M' - |S|$ from Proposition 2.6. So all but at most one $\gamma$ have $|M_\gamma| > 3M'/16 > M'/8$ and $|\mathcal{A}_\gamma| \le 4$. (iv) At least $M' - 16$ functions $a \in \mathcal{N}$ have $|X_a| \ge |S|/2$, and they need at least $1 + (M' - 16 - 8)/4$ distinct $\gamma(a)$. $\square$

What this does and does not give. It shows that hyperplane families cannot be the first source of growth: a family at index $M'$ needs lists of size proportional to $M'$ on $M'$ points at the same fraction. If lists on generic subspaces at fraction $\tau$ were known to be at most $L_\infty(\tau)$ at every size, the index would be bounded by $4L_\infty + 20$ and Proposition 2.4 would bound the contribution of this mechanism by a constant. It does not exclude a family: at $\tau = 0.65$ the multiset tops alone give lists of 16 at $n = 32$ (note 18) and are allowed up to $1/(16\epsilon^2) = 100$ (note 12, Theorem A), so indices $64, 128, 256$ are compatible with it.

### 2.6 Computations for hyperplanes

**[checked]** `25_periodic1.c`, random $\Lambda_U$ in $\mathrm{GF}(2^{64})$, $\chi$ modulo affine functions, a type is reported when the spaces $\mathcal{V}_\theta/P_{\le h'}$ for five random $\theta$ have a common nonzero element. "None" entries are rigorous for the generic label domain: the first test is that two of these spaces are independent, which is a full-rank statement.

| rate | $M'$ | labels | $\lvert S\rvert$ (fraction) | types examined | families found |
| --- | --- | --- | --- | --- | --- |
| 1/2 | 8 | 16 | 11 (0.6875), slack and genuine | 112 | none |
| 1/2 | 16 | 32 | 21 (0.6562), slack and genuine | 3242752 | none |
| 1/2 | 16 | 32 | 22 (0.6875), slack and genuine | 1081856 | none |
| 1/2 | 16 | 32 | 23 (0.7188), slack | 183040 | none |
| 1/2 | 32 | 64 | 41 (0.6406), slack and genuine | 1572864 (12 sets $A$, all $\chi$ modulo affine) | none |
| 1/2 | 32 | 64 | 42 and above | 0 pass Parseval | none |
| 1/4 | 8, 16 | 16, 32 | 6, 7 and 13 (genuine) | 448, 400, 9309440 | none |
| 1/4 | 16 | 32 | 13, 14, 15, 16 (slack) | $\approx 10^7$ each | only restrictions of the affine hyperplanes of the word $X^{n/2}$: 560, 120, 16, 1 types $(0, s')$ with $\chi$ affine |
| 1/8 | 8 | 16 | 4 (genuine), 5, 6 | 84, 112, 112 | none |
| 1/8 | 16 | 32 | 8 (0.25), slack | 280160 | the 30 flats |
| 1/8 | 16 | 32 | 9, 10, 11 (window), slack | 603520, 1081856, 1560832 | none |
| 1/16 | 16 | 32 | 4 (0.125), slack | 1960 | the 140 flats |
| 1/16 | 16 | 32 | 5, 6, 7 (window), slack | 6048, 17696, 46720 | none |

For $M' \le 16$ at rate 1/2 the enumeration covers all types, whether or not they pass the balance condition, and agrees with Corollary 2.7. For $M' = 32$ only the types allowed by Proposition 2.6 are examined: $A$ contains an affine basis (forced), one representative per orbit of the 720 affine maps permuting it, 12 sets for $(9, 23)$ and none for $(10, 21)$.

**Conclusion of 2.2 to 2.6.** At rate 1/2, a periodic word $f \circ L_U$ with $|D/U| \le 32$, $f$ arbitrary, has at most a bounded number (independent of $n$) of hyperplanes $W$ of $U$ carrying a $W$-periodic member above $5n/8$, on a generic domain. The $56n - 392$ members of $L_U^5$ are the end of this mechanism for index up to 32. **[proved for $M' \le 16$, checked for $M' = 32$]**

### 2.7 Subspaces of codimension two and three

For $W \le U$ of codimension $j$ the label domain $\Lambda_W$ has $2^jM'$ points, each label of $\Lambda_U$ has a fibre of $2^j$ points, a member has a pattern $a_u = |S \cap \text{fibre}_u| \in [0, 2^j]$, and a family would have about $|U|^j$ members. **[proved]** Two members of the same pattern over $W, W'$ in general position agree on $\sum_u a_u^2$ labels of $\Lambda_{W \cap W'}$, so $\sum_u a_u^2 \le 2^{2j}d'/2$ while $\sum_u a_u = \tau 2^j M'$: for $j = 1$ this is $\tau \le 2/3$, for $j = 2$ it allows $\tau = 0.7$ (patterns of 2s and 3s), and for large $j$ it tends to the Johnson radius. So counting does not confine these families to a subinterval of the window.

**[checked]** `25_periodic_any.c` takes a random label domain $\Lambda$ of 16 or 32 points with a marked subspace $\bar U$ of dimension $j$, enumerates every agreement set $S$ of the given size, and decides by a rank computation whether some polynomial $c$ of the degree bound and some $f$ on the labels satisfy $c = f \circ L_{\bar U}$ on $S$ other than the trivial $c = g \circ L_{\bar U}$. Whenever the number of conditions $|S| - d' - 1$ exceeds the dimension $M' - t_0$ of the periodic words modulo codewords, a solution at a random $\Lambda$ is necessary for a family (a rank drop that is not formal does not happen at a random specialization), so no solution means no family of any codimension-$j$ type.

| labels | $j$, $M'$ | $\lvert S\rvert$ | degree | conditions against dimensions | sets with a solution | of these not periodic under an element of $\bar U$ |
| --- | --- | --- | --- | --- | --- | --- |
| 16 | 2, 4 | 11 | $\le 8$ and $\le 7$ | 2 against 1, 3 against 2 | 0 | 0 |
| 16 | 3, 2 | 11 | $\le 8$ | 2 against 0 | 0 | 0 |
| 32 | 2, 8 | 21 | $\le 16$ | 4 against 3 | 118272 | 0 |
| 32 | 2, 8 | 21 | $\le 15$ | 5 against 4 | 118272 | 0 |
| 32 | 3, 4 | 21 | $\le 16$ | 4 against 1 | 0 | 0 |

For each of the 118272 sets at $(32, j = 2)$ every solution has $c$ periodic under one nonzero $\eta \in \bar U$. They are the 21-subsets of the sets of pattern $(4, 4, 4, 2, 2, 2, 2, 2)$ that are unions of cosets of some $\{0, \eta\}$ ($3 \cdot 1792 \cdot 22 = 118272$, with 1792 the number of types $(3, 5)$ on 8 labels): single-parameter members of the hyperplane problem on 16 labels, which always exist (2 conditions against 3 dimensions), and Corollary 2.7 shows that those are not families. So on label domains of at most 32 points there is no family of codimension 1, 2 or 3 above $5/8$ at rate 1/2. At 16 labels with $j = 2$ the periodic words are spanned by $L_{\bar U}^3$ alone, and at 32 labels with $j = 3$ likewise: these are the words $L_U^3$, $|U| = n/4$, strict tops of degree $3n/4$ used far below their degree.

### 2.8 What is not covered: the place where I would look for a counterexample

1. **Hyperplane families with $M' \ge 64$.** Allowed by counting at $|S| = 83, 84$ of 128 for $M' = 64$ (types $(19, 45)$, $(20, 43)$, $(20, 44)$) and up to $0.664$ for large $M'$. The types cannot be enumerated ($2^{37}$ functions $\chi$ per pair $(A, B)$). What such a family must look like, from this section: $B$ has a nearly flat Walsh spectrum (Proposition 2.6), $\chi$ is not affine on $B$ and $G_1$ changes direction with $\theta$ (Theorem 2.8), and $f$ has on the 64-point domain $\Lambda_U$ at least 11 codewords at agreement $\ge 42$ whose agreement sets contain $A \cup (B \cap \{\chi = a\})$ for the affine functions $a$, each codeword serving at most 4 or 8 of them (Theorem 2.10). Two further exact necessary conditions, which I state without having exploited them: **[proved]** letting $\theta \to \infty$ in $(\ast)$ gives, when $C = \Lambda_U$, $f \in P_{\le h} + \sqrt{u}\,Z_AP_{\le h-1-p}$, independent of $\chi$ ($\sqrt u$ is the linearized polynomial $\omega_{r-1}/\sqrt{l_0}$ on $\Lambda_U$, since $\omega_{r-1}^2 = l_0u$ there, $\Psi_\theta/\theta^h \to \omega_{r-1}$, and the limit of $\mathcal{V}_\theta$ in the Grassmannian is this space because the sum is direct for degree reasons and so has the same dimension); and for two nondegenerate $a$, $a + \lambda$ the four codewords $\gamma(a), \gamma(a+1), \gamma(a+\lambda), \gamma(a+\lambda+1)$ give polynomials $E, E + G, E + G', E + G + G'$ of degree $\le h - p$ vanishing on the four cells of the partition of $B$ by $(\chi + a, \lambda)$, an over-determined system as soon as $s' > 3(h - p)$, which is equivalent to $|S| + p > 3M'/2$ and holds above $5/8$. So a family requires, for every pair $(a, \lambda)$, a singular configuration of four sets on a generic subspace. I expect that only flats produce such singularities, as in note 17's Conjecture P, and that no family exists. **[conjectured]** I could not prove it, and this is a statement of the same kind and difficulty as Conjecture P.
2. **Codimension $j \ge 2$ on 64 labels or more.** Nothing beyond the pairwise count.
3. **Translation-covariant words** $X^{n/2}\ell(X)$: exhausted at $n = 32$ by note 18 (16 members at $T = 21, 22$, no growth from $n = 16$), bounded when they are multiset tops, not analysed here for larger $n$.

## 3. Rational words

Let $w = P/Q$ on $D$ with $Q$ of degree $q$ without roots in $D$. Subtracting a codeword, $\deg P < q$ can be assumed whenever $\deg P \le q + d$.

**Proposition 3.1 (few poles, no list). [proved]** A polynomial $c$ of degree $\le d$ with $P \ne cQ$ agrees with $P/Q$ on at most $\max(\deg P, d + q)$ points. So a pole word ($\deg P < q$) has no codeword at agreement $T$ unless $q \ge T - d$: inside a window the number of poles is linear in $n$, at least $n/8$ at rate 1/2 above $5/8$.

*Proof.* $P - cQ$ is a nonzero polynomial of that degree. $\square$

**Proposition 3.2 (lists of rational words are residue classes). [proved]** With $\deg P < q$ and $m = T - d - 1$: the members at agreement $T$ correspond to the pairs $(S, G)$ with $|S| = T$, $\deg G \le q - m - 1$ and $Z_S G \equiv P \pmod Q$. For $q = m + 1$: the members are the $T$-sets whose locators have residues modulo $Q$ proportional to $P$. A top word is the same statement at the place at infinity (proportional modulo $X^{-(m+1)}$, that is equal $e_1, \dots, e_m$).

*Proof.* $P - cQ = Z_S G$ with $\deg(Z_SG) \le d + q$. $\square$

So rational words are tops at another place, and the question is which place carries identities.

**Proposition 3.3 (no identity at a place in general position). [proved]** If $Q$ has two simple roots $\beta_0, \beta_1$ that are algebraically independent over $\mathbb{F}_2(D)$, or one root of multiplicity $\ge 2$ transcendental over $\mathbb{F}_2(D)$, and $q = m + 1$, then the list at agreement $T$ has at most one member.

*Proof.* Two members give $Z_S(\beta_0)Z_{S'}(\beta_1) = Z_S(\beta_1)Z_{S'}(\beta_0)$, an identity in two independent transcendentals, so $Z_S/Z_{S'}$ is constant and $S = S'$. For a double root, $Z_S'/Z_S = Z_{S'}'/Z_{S'}$ at a transcendental point, so $(Z_S/Z_{S'})' = 0$, the quotient is a square, and since both have simple roots $S = S'$. $\square$

Why infinity is different. **[proved]** For a flat $a + V$ the locator is $L_V(X) + L_V(a)$. At infinity it is $X^{|V|}$ plus terms of degree $\le |V|/2$: a window of length $m < |V|/2$ sees nothing, which is the whole flats family, and Theorem W of note 02 extends this to all sets with congruent Walsh spectra. At a finite point $\beta$ it is $L_V(\beta + a) + c_0Y + c_1Y^2 + c_2Y^4 + \dots$ in $Y = X - \beta$: sparse too, but a window of length $m$ sees $c_0, \dots, c_{\lfloor\log_2 m\rfloor}$, about $N - 3$ independent coefficients of $L_V$, against at most two at infinity. Two flats are proportional modulo $Y^{m+1}$ only if all of these agree up to a scalar.

Poles placed on the structure of $D$. If $Q = Q_0(L_V)$ for a subspace $V \le D$ (poles on cosets $b + V$, $b \notin D$, in a larger subspace of $F$; this includes $Q = L_V + \gamma$ and its powers and products), then for $V$-periodic $P$ the word is $V$-periodic and belongs to section 2 with $f$ a rational function on the labels, and for general $P$ the $V$-periodic sets $S$ have $Z_S \bmod Q$ equal to a polynomial in $L_V$ modulo $Q_0$: the class structure is the one on the label domain, lifted. If the poles fill a whole coset $b + D$, $Q = L_D(X) + L_D(b)$ is constant on $D$ and every word is of that form: no restriction and no information. So rational words are either without structure (Proposition 3.3), or periodic words, or everything.

**[checked]** `25_rational_words.py` with the exhaustive oracle of note 02 (all polynomials of degree $\le d$, no assumption on their form). $S_0$ is a member of the $5n/8$ family that is not $U$-periodic, the top word is $Z_{S_0}$ (that is $L_U^5$ modulo codewords), and the rational words are $(Z_{S_0} \bmod Q)/Q$ with $\deg Q = m + 1$, so that $S_0$ is a member of each.

| word | $n = 16$, $d = 8$, $T = 10$ | $n = 32$, $d = 16$, $T = 20$ |
| --- | --- | --- |
| top ($Q$ at infinity) | 504 | 1400 |
| $m + 1$ random simple poles | 1 | 1 |
| one pole of order $m + 1$ | 1 | 1 |
| poles a coset $b + U$ ($Q = L_U + \gamma$) | 4 | 4 |
| $m + 1$ poles in $b + D$ | 4 | 1 |
| poles $b + V$, $V$ another subspace | 1 | 1 |
| random $P$, $m$ simple poles | none | none |

The lists of 4 are the sets obtained from $S_0$ by exchanging full cosets of the subspace $V$ spanned by the differences of the poles: a full coset $s + V \subseteq S$ contributes the same factor $L_V(b + s)$ to every residue $Z_S(b + v)$, $v \in V$. At $n = 16$ the two poles differ by some $v \in D$ and $S_0$ contains three pairs $\{s, s + v\}$ out of four available (or two out of two, list 1); at $n = 32$ with poles $b + U$, $S_0$ contains three full cosets of $U$ out of four available. It is a lifted trivial list, and the 504 and 1400 members at infinity collapse to it.

## 4. Syndromes and error values

The dual form of a list is in note 17, Proposition 2.6 **[quoted]**: with $t = n - T$ and syndrome series $\sigma(Y) = \sum_j p_j Y^{-j-1}$, $p_j = \sum_x e(x)x^j$, the error locators of the members are the polynomials $aQ_1 + bQ_2$ of degree $t$ (with $\deg a \le t - \deg Q_1$, $\deg b \le t - \deg Q_2$, $Q_1, Q_2$ consecutive convergent denominators of $\sigma$, $\deg Q_1 + \deg Q_2 = n - d$) that split over $D$ with simple roots. The error values are $e(x) = \Gamma(x)/Z_E'(x)$ with the evaluator $\Gamma = [\sigma Z_E]_{\text{pol}}$, and $\Gamma$ is the phantom polynomial up to a constant: a top is $\Gamma = 1$. The brief asks for syndromes with many sparse solutions whose values are structured. Three structures, three answers.

**Proposition 4.1 (values constant on cosets are lifts). [proved]** If every error vector $w - c_i$ is constant on the cosets of a subspace $V \le D$, then $w - c_0$ and all $c_i - c_0$ are $V$-periodic and the list is the lift of a list on $L_V(D)$: constant size at fixed $|D/V|$, and section 2 when $V$ varies.

*Proof.* $c_i - c_0 = (w - c_0) - (w - c_i)$ is constant on cosets. $\square$

**Proposition 4.2 (indicator-type errors). [proved]** Let $d \le n/2$ and let $g : D \to F$ be any function without zeros. If the error vectors of a list are $w - c_i = g\cdot\varepsilon_i$ with $\varepsilon_i \in \mathbb{F}_2^D$, the list has at most $1/(2\tau - 1)^2$ members at agreement $\tau n$, $\tau > 1/2$: at most 16 at $5/8$ and at most 9 at $2/3$. For $g = 1$ the differences $\varepsilon_i - \varepsilon_j$ are the $\mathbb{F}_2$-valued polynomial functions of degree $\le d$, which for $d = n/2$ are the affine functionals.

*Proof.* $g(\varepsilon_i - \varepsilon_j) = c_j - c_i$ has at most $d \le n/2$ zeros, so $\varepsilon_i, \varepsilon_j$ are at Hamming distance $\ge n/2$, and each $\varepsilon_i$ has weight $\le (1 - \tau)n$. With $v_i = (-1)^{\varepsilon_i} \in \{\pm 1\}^D$: $\langle v_i, v_j\rangle \le 0$ and $\langle v_i, \mathbf{1}\rangle \ge (2\tau - 1)n$, so $L^2(2\tau - 1)^2 n \le |\sum v_i|^2 \le Ln$. For the last statement, an $\mathbb{F}_2$-valued $\phi$ has $L_D \mid \phi^2 + \phi$, so $\deg\phi \ge n/2$ unless $\phi$ is constant, and $\deg\phi = n/2$ forces $\phi^2 + \phi = cL_D$, $\phi$ additive up to a constant. $\square$

The same argument with the $q$-ary Johnson bound **[quoted, standard]** shows that error values in $g\cdot\Gamma$ for a fixed subgroup $\Gamma$ of $F$ of order $q$ give bounded lists for $\tau > 1 - (1 - 1/q)(1 - \sqrt{1 - q/(2q - 2)})$: $0.683$ for $q = 4$, $0.703$ for $q = 16$. So a large list in the window needs error vectors whose values, relative to one another, do not lie in a small group: the tops have $e_i = Z_{S_i}$ on $E_i$, as far from that as possible.

**Proposition 4.3 (values given by a polynomial on the support are twists). [proved]** Let $g$ be a polynomial of degree $r$ without zeros in $D$. The lists of degree $\le d$ whose error vectors are $g$ times the error vectors of a list $(w'; c_i')$ of degree $\le d - r$ are the twists $(gw'; gc_i')$, with the same agreement sets: $r$ units of degree are spent and no agreement is gained. In syndrome terms, a flat $V$ of size $t$ with error values $g(x)/c_0(V)$, $\deg g < r$, $m + r \le t/2$, has the syndrome $(0^{t - r}, g_{r-1}, \dots, g_0, 0^{m})$ independent of $V$, which is the complement of the flats family twisted by $g$.

*Proof.* The first statement is note 17's Proposition 2.4. For the second, the power sums of a coset $a + V$ vanish below index $|V| - 1$, equal $c_0(V)$ there, and vanish again up to index $3|V|/2 - 2$, because $\sum_{x \in a + V}(Y - x)^{-1} = c_0(V)/(L_V(Y) + L_V(a))$. $\square$

I found no fourth structure. The module form says what one would be: a pencil $aQ_1 + bQ_2$ with many members that split over $D$, where $Q_1, Q_2$ are not themselves built from subspace polynomials.

## 5. The small examples that are not tops

Note 18 computed the exact maxima over all words at $n = 16$ and classified the extremal words **[quoted]**: in the rate-1/2 window the maximum is 3 (16 with slack one, a translation orbit that does not grow at $n = 32$), every list above the strict tops is a multiset top or a polygon of at most 6 lines in a label plane, and the Sidon lines give exactly 6 at rate 1/8, $\tau = 5/16$, for every $n \ge 16$, by lifting. Two remarks from this note's side.

1. The lists of 11 and 16 of note 02 and the list of 16 at $(16, \le 8, 11)$ are of the kinds that sections 1 and 2 control: the first two sit at or below the threshold $(n + 3d)/4$ of Theorem 1.1, where additive structure is allowed, and the third is a single orbit of the translation group, Sidon as Theorem 1.1 requires (checked in section 1.1), a multiset top, and periodic under a subspace of index 16 from $n = 32$ on.
2. The lifting lemma turns any list on a label domain into a constant list at every $n$. The only way I know to make a lifted list grow is to move the subspace through which one lifts, which is section 2, or to let a larger group act. So "scaling the tiny examples" is the question of section 2 with $f$ the tiny example, and the answer for label domains up to 32 points is that none of them scales above $5/8$.

## 6. Interleaved and extension-field words

**[quoted]** (note 14, Proposition R2', after note 13) If single $K$-valued words have at most $L \le 2^{62}$ codewords at agreement $A$, every word with any number of lanes over $K$ or $E$ has at most $L/(1 - L/2^{64})$. The reason is short: an interleaved member agrees with the word only where all lanes agree, a random $K$-linear combination of the lanes maps the word to a single-lane word and the tuples to codewords with the same agreement sets, and two tuples collide with probability $2^{-64}$. So a genuinely interleaved word cannot have a list above the single-lane maximum by more than the factor $1 + L/2^{64}$, and I looked for no example: none can matter below $2^{62}$. Theorem 1.1 and Propositions 1.2, 3.1, 4.2 hold verbatim for interleaved words (their proofs count zeros of differences).

## 7. The real domain

The pair of subspaces of note 19, Proposition 5.1 ($V = \{f : f(0) = f(1) = f_{N-1}\}$, $V' = \{f : x^2 + x + 1 \mid f\}$, with $c_1(V) = c_1(V')$) is an identity of $\mathbb{F}_2(x)$. Whether such identities multiply into a family that grows with $N$ was already measured **[quoted, note 13 section 4.3]**: exactly 1 such pair of planes for $N = 6, \dots, 16$, exactly 3 pairs at the next invariant, 246 affine pairs, 24 pairs in the $5n/8$ class, all independent of $N$ and all attached to the three rational places and the quadratic place, that is to $\mathrm{PGL}_2(\mathbb{F}_2)$ acting on polynomials of degree $< N$. A family growing with $N$ would need identities attached to places of growing degree, and none was seen up to $N = 16$.

One remark on the other non-generic feature, that $D$ is closed under multiplication by small polynomials and under Frobenius while degrees stay below $N$. **[proved]** For $V_0 = \{f : \deg f < N - j\}$ and $a \ne 0$ of degree $\le j$, $aV_0 \le D$ and $L_{aV_0}(X) = a^{|V_0|}L_{V_0}(X/a)$, so the coefficient of $X^{2^i}$ is $a^{|V_0| - 2^i}c_i(V_0)$; and $L_{V^2}$ has the squares of the coefficients of $L_V$ when $V^2 \le D$. These are $2^{j+1} - 1$ subspaces of codimension $j$ with locators related by explicit scalings, the largest structured family of subspaces special to the real domain that I see, and they share no coefficient: the second coefficients $a^{|V_0|/2}c(V_0)$ are pairwise distinct when $c(V_0) \ne 0$, because $a \mapsto a^{|V_0|/2}$ is injective. So this structure gives relations between classes and no coincidence.

## 8. Mechanisms, one line each

| mechanism of the brief | result | status |
| --- | --- | --- |
| 1. rational words | need $\ge T - d$ poles; lists are residue classes modulo $Q$; one member for poles in general position; poles on cosets of subspaces give periodic words; observed lists 1 or 4 against 504 | proved, checked $n = 16, 32$ |
| 2. gluing | additive gluing capped at $(n + 3d)/4 = 5n/8$ exactly; subspace-moving gluing (hyperplanes of $U$) below $2/3$ always, absent for index $\le 16$ (proved) and $32$ (checked), absent for codimension 2, 3 up to 32 labels (checked); open for index $\ge 64$ | proved and checked, with a stated hole |
| 3. scaling the tiny examples | lifts are constant; they scale only through section 2; the Sidon lines are a linear family over a Sidon set, which above $5n/8$ every additive family must be, and their constant-rate analogue is the first-order Reed-Muller code | proved, with note 18 |
| 4. syndromes with structured values | constant on cosets: lifts; values in $g\cdot\mathbb{F}_2$: at most $1/(2\tau - 1)^2$; polynomial on the support: twists | proved |
| 5. interleaving | no gain below $2^{62}$ | quoted |
| 6. real-domain identities | number independent of $N$; multiplicative structure gives no coincidence | quoted, one proved remark |

## 9. Reproduction

All under `doc/whir_soundness_gap_notes/scripts/`, C with the system compiler (`cc -O2`), field arithmetic in `25_gf.h` ($\mathrm{GF}(2^{64})$, leanVM modulus, random elements from a fixed xorshift seed, changed by the seed argument).

- `25_periodic1.c`: `./25_periodic1 r S slack [seed] [verbose] [R]`. Hyperplane families on $M' = 2^r$ labels at agreement $S$ of $2M'$, rate $2^{-R}$ (default 1/2). $r = 3$: instant. $r = 4$: 12 s for $S = 21$, 35 s for $S = 20$, about two minutes for $S = 19$ genuine, under a minute for each low-rate row. $r = 5$ (rate 1/2 and above $5/8$ only, balanced types): 13 s for $S = 41$.
- `25_balance.py`: the table of section 2.3 and the exhaustive balance check for $M' = 8, 16$. One second.
- `25_periodic_any.c`: `./25_periodic_any nu j T kdeg [seed] [part parts]`. All agreement sets of size $T$ on $2^\nu$ labels with $\bar U$ of dimension $j$. 16 labels: instant. 32 labels, $j = 2$, $T = 21$: four parts (`part parts` = `0 4` to `3 4`) of at most a minute and a half each. 32 labels, $j = 3$: one minute.
- `25_sidon_check.py`: Theorem 1.1 attained on the 504 members at $(16, 8, 10)$, and no additive quadruple in note 18's list of 16 at $(16, 8, 11)$. One second.
- `25_rational_words.py <02_lists binary> N [seed]`: section 3's table, with the oracle `02_lists.c` of note 02 (`cc -O2 -o lists 02_lists.c -lm`). $N = 4$: under a second. $N = 5$: seven oracle calls of about two minutes each, three at a time, six and a half minutes in all.

## References

- Notes 01, 02, 12, 13, 14, 17, 18, 19 of this directory.
- [DKTZ26] Dao, Kominers, Thaler, Zheng. Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields. ECCC TR26-237.
