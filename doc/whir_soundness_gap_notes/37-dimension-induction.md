# 37. Dimension induction: what descends, what cannot, and a gap theorem at the split end

Researcher 37, round 5. Every statement is tagged **[proved]** (proof in this note), **[quoted]** (from a cited note, not re-proved), **[checked]** (numerically, sizes stated) or **[conjectured]**. Scripts are `scripts/37_*`, section 8 says how to run them.

Notation. $F$ is a field of characteristic two, $D \subset F$ an $\mathbb{F}_2$-subspace of dimension $N$, $n = 2^N$. $D$ is **generic** if it has a basis $b_1, \dots, b_N$ algebraically independent over $\mathbb{F}_2$ (the formal model). Codewords are polynomials of degree $< k$, $\rho = k/n$, $T = \tau n$ is an agreement count. A *list* is a word $w : D \to F$ with distinct codewords $c_i$ and $S_i = \{x : c_i(x) = w(x)\}$, $|S_i| \ge T$. $L_U = \prod_{u \in U}(X - u)$ for a subspace $U$, $Z_S = \prod_{s \in S}(X - s)$. For three members, $\xi$ is the triple function of note 17 ($\xi = u_0/u_1$, $u_0 + u_1 + u_2 = 0$ the differences divided by their gcd), $\delta = \deg\xi$, $R_0, R_1, R_2 \subseteq D$ its fibres over $0, \infty, 1$, $r_i = |R_i| \le \delta$, $\nu = r_0 + r_1 + r_2$, and $\Pi(\xi) = \{a \in D : \xi(X + a) = \xi(X)\}$. I write $s_i = \delta - r_i \ge 0$ and $s = s_0 + s_1 + s_2 = 3\delta - \nu$, the **non-split degree** of $\xi$. $\Lambda^\ast_N(k, T)$ is the largest list at agreement $T$ over all fields of characteristic two, all $N$-dimensional subspaces and all words (finite: at most $\binom{n}{k}$).

## 0. Summary

**The honest headline.** The recursion on the dimension through $x \mapsto x^2 + ax$, in the form proposed in the brief (a member whose agreement set is invariant descends, a dichotomy "invariant or few" closes the induction), is exact and easy (section 1), but the dichotomy it needs is **not a reduction**: by a random perturbation of the word every list becomes a list, at an agreement lower by a factor $1 - \lambda$, in which no member is invariant or near-invariant in any direction, so the "few" side of the dichotomy contains the whole list problem at a slightly larger agreement (Proposition 2.1, proved, every subspace domain). The recursion gives nothing in that form. The form that survives perturbation is a descent on **periods of the differences** (the triple functions $\xi$), which is lossless and goes to the list problem of the periodic subcode (section 3, proved on every subspace domain); it yields $2^{N^2/2 + O(N)}$ conditional on a density hypothesis that I could not prove and that the data at $n = 16, 32$ neither supports strongly nor refutes. What I can prove unconditionally is at the other end: a **gap theorem** in the formal model (a triple function is either a flat or has non-split degree at least $\delta^2/4n$, Theorem 4.3), and from it the first list bound for all words strictly below the Johnson radius on a generic subspace, in a window that is real but only about $10^{-5}$ wide (Theorem 5.1).

| | statement | where it holds | status |
| --- | --- | --- | --- |
| 1.1, 1.2 | Fold dictionary and exact set descent: members with $\lvert S \cap (S + a)\rvert \ge 2A$ inject into a list at agreement $A$ of the code of degree $< \lceil k/2\rceil$ on $D/a$ over a quadratic extension. Recursion $\Lambda^\ast_N(k, T) \le B^{\mathrm{set}}_N + (n - 1)\Lambda^\ast_{N-1}(\lceil k/2\rceil, A)$ | every subspace domain | proved |
| 1.3 | The weak descent (half-agreed fibres kept as linear constraints) is a bijective restatement of the problem; its patterns number $\binom{n}{T}$ | every subspace domain | proved (trivial) |
| 2.1, 2.2 | **Perturbation.** Every list is, after changing the word on a random set of density $\lambda$, a list at agreement $(1 - \lambda)\lvert S_i\rvert - t$ in which every member has $\lvert S \cap (S + a)\rvert \le (1 - \lambda)^2\lvert S_i\rvert + t$ for all $a \ne 0$, $t = \sqrt{n\ln(2Ln)}$. So $B^{\mathrm{set}}_N$ at $(T', \eta)$ is at least the number of members of any list in a band at $T'/(1 - \lambda)$, $\lambda \approx 4\eta/\tau$: the set dichotomy is equivalent to the list bound up to a shift | every subspace domain | proved |
| 3.2, 3.3 | **Difference descent.** For two fixed members, the members $c_l$ whose $\xi_l$ has the period $a$ are $c_0 + \varrho\,Q_l(X^2 + aX)$ and inject, with agreement minus degree preserved, into a list of the periodic subcode. Iterated: the $U$-problem (polynomials in $L_U$ against an arbitrary word) | every subspace domain | proved |
| 3.4, 3.5 | Recursion on differences: $\Lambda \le 2 + B^{\mathrm{diff}} + \sum_{a}(\dots)$ and, if at every level all but $B$ members have a periodic $\xi$ for a suitable pair, $\Lambda^\ast_N(k, T) \le 2^{NJ - J(J-1)/2}\,(J(B + 2) + n/(T - k + 1))$, $J = \lceil\log_2 k\rceil$ | every subspace domain | proved conditional on hypothesis DP |
| 3.6 | Bounded-index form: if for one pair a fraction $g$ of the members have $\lvert\Pi(\xi_l)\rvert \ge \pi$, then $L \le 2 + g^{-1}\binom{N}{\log_2(n/\pi)}_2\prod_{i \le \lfloor (k-1)/\pi\rfloor + 1}\frac{n - k + i}{T - k + i}$ | every subspace domain | proved |
| 4.1 | Transfer lemma: for every $z \ne 0$, $\lvert R_i \cap (R_j + z)\rvert \le s_l$ unless $z$ divides the content of the third polynomial, and then $\lvert R_i \cap (R_j + z)\rvert \ge r_i - s_j$ | generic $D$ | proved (sharpening note 17 Proposition 3.5), checked on 196 functions, $n \le 64$ |
| 4.3 | **Gap theorem.** Either $\nu(\xi) = 3\delta$ and $\xi = \mu \circ L_\Pi$ with $\lvert\Pi\rvert = \delta$, or $\nu(\xi) \le 3\delta - \delta^2/(4n)$. So Conjecture P holds whenever $s < \delta^2/4n$ | generic $D$, all fields | proved; the counting step checked exhaustively for $N \le 10$ |
| 5.1 | **List bound below Johnson.** For $T^2 \ge n(k - 1) - \theta n^2$ with $\theta \approx 7 \cdot 10^{-6}$ (rate 1/2), $1.1 \cdot 10^{-5}$ (1/4), $5 \cdot 10^{-6}$ (1/8), $3.4 \cdot 10^{-6}$ (1/16): at most $2^{77}$, $2^{74}$ members at rates 1/2, 1/4 ($N = 25$; $2^{86}$, $2^{83}$ at $N = 28$) and at most $2^{20}$ members at rates 1/8 and 1/16, for every word and any number of lanes | generic $D$ | proved |
| 6 | Profiles of real lists at $n = 16, 32$: the $5n/8$ family is fully periodic in both senses, one step below it 91 percent of the list is periodic in neither | generic $D$ | checked |

**What the theorem of section 5 is worth.** As a statement it is the first unconditional (formal model) bound on lists of arbitrary words below the Johnson radius on a subspace domain, at all four rates, and it is polynomial where it must be (rate 1/4, where flats give $n - 1$ members). As a parameter gain it is nothing: 175 to 376 points below the Johnson threshold at $N = 25$, a relative $10^{-5}$. The window is limited by the method (Markov on pair defects, and the constant $1/4$ of the gap theorem), and even Conjecture P in full would extend "the typical triple is a flat" only to about $\tau \ge 0.686$ at rate 1/2 (a heuristic estimate, section 5). It is not a route to the windows of the brief.

## 1. The fold dictionary and the exact set descent

Everything in this section holds on every subspace domain of every field of characteristic two.

**Proposition 1.1 (dictionary). [proved]** Let $a \in D \setminus 0$, $q = X^2 + aX$ and $D/a := q(D)$, an $\mathbb{F}_2$-subspace of dimension $N - 1$ ($q$ is $\mathbb{F}_2$-linear with kernel $\{0, a\}$ on $D$). Every $c \in F[X]$ is uniquely $c = c_0(q) + X c_1(q)$, and $\deg c < k$ iff $2\deg c_0 \le k - 1$ and $2\deg c_1 \le k - 2$. For a word $w$ and $y = q(x)$ put $w_1(y) = (w(x) + w(x + a))/a$ and $w_0(y) = w(x) + x\,w_1(y)$ (both symmetric in $x \leftrightarrow x + a$). Then: $c$ agrees with $w$ at $x$ and at $x + a$ iff $(c_0, c_1)(y) = (w_0, w_1)(y)$; $c$ agrees at $x$ and not at $x + a$ iff $c_0(y) + x\,c_1(y) = w_0(y) + x\,w_1(y)$ and $c_1(y) \ne w_1(y)$.

*Proof.* Division by $q$ with remainder of degree at most one, repeated. $w(x) = w_0(y) + x w_1(y)$ and $w(x + a) = w_0(y) + (x + a) w_1(y)$ by the definitions, and the same for $c$. $\square$

**Corollary 1.2 (exact descent and the set recursion). [proved]** For a list and an integer $A$, the members with $|S_i \cap (S_i + a)| \ge 2A$ map injectively, by $c \mapsto c_0 + \vartheta c_1$ with $\vartheta$ transcendental or quadratic over $F$, to a list of polynomials of degree $< \lceil k/2\rceil$ over $F(\vartheta)$ on $D/a$ for the word $w_0 + \vartheta w_1$ at agreement $A$. Hence, with $B^{\mathrm{set}}_N(k, T; A)$ the largest number of members of a list at agreement $T$ with $|S \cap (S + a)| < 2A$ for every $a \ne 0$:
$$\Lambda^\ast_N(k, T) \ \le\ B^{\mathrm{set}}_N(k, T; A) + (n - 1)\,\Lambda^\ast_{N-1}(\lceil k/2\rceil, A) .$$
The rate is unchanged, the agreement fraction goes from $\tau$ to $2A/n$, and the two lanes cost nothing because $\Lambda^\ast$ is a supremum over fields.

*Proof.* $1$ and $\vartheta$ are linearly independent over $F$, so $c_0 + \vartheta c_1$ agrees with $w_0 + \vartheta w_1$ at $y$ iff both lanes agree, which by Proposition 1.1 means that the full fibre over $y$ lies in $S$. The number of full fibres is $|S \cap (S + a)|/2$. $c \mapsto (c_0, c_1)$ is a bijection. $\square$

If $A = T/2$ could be taken (all but few members exactly invariant) and $B^{\mathrm{set}}$ were polynomial, the recursion would give $\Lambda^\ast_N \le 2^{N^2/2 + O(N\log N)}$, which the framework of the brief can afford. Section 2 shows why this cannot be made to work.

**Remark 1.3 (the weak descent is the identity). [proved]** Keeping, for a member, its full fibres and on each half-agreed fibre the linear constraint $c_0(y) + x\,c_1(y) = w(x)$ loses nothing and gains nothing: the pair (set of full fibres, set of half fibres with the marked point) determines $S$ and is determined by it, and the constraints are the original linear system. After $j$ steps along a flag $U_j$ the object is the code with $2^j$ lanes on $D/U_j$, the symbol at $y$ being the restriction of $c$ to a coset of $U_j$, an arbitrary vector of $F^{|U_j|}$ as long as $|U_j| \le k$. The number of partial-information patterns is $\binom{n}{T}$ at every step. So a bound can only come from dropping the half fibres, which is Corollary 1.2, or from structure in the codewords, which is section 3.

**Remark 1.4 (pigeonhole over directions). [proved]** $\sum_{a \ne 0}|S \cap (S + a)| = |S|^2 - |S|$, so every member has a direction with $|S \cap (S + a)| \ge \tau^2 n - 1$ and some direction serves $L/n$ members. The descent then lands at agreement fraction $\tau^2$, which in every window is below the rate ($\tau^2 < \rho$ is the definition of "below Johnson"). Sets of density $\tau$ with all self-intersections near $\tau^2 n$ and pairwise intersections near $\tau^2 n < \rho n$ exist in exponential number, so no argument that uses only the sizes $|S_i \cap (S_j + a)|$ can go further.

## 2. The set dichotomy is not a reduction

**Proposition 2.1 (perturbation). [proved]** Let $w$ be a word on any $n$-point set $D$ that is an $\mathbb{F}_2$-subspace, with $L$ list members $c_i$ and agreement sets $S_i$, over a field with more than $L$ elements (pass to an extension otherwise). Let $0 < \lambda < 1$ and $t = \sqrt{n\ln(2Ln)}$. There is a set $P \subseteq D$ and a word $w'$, equal to $w$ off $P$, such that the agreement set of $c_i$ with $w'$ is $S_i' = S_i \setminus P$ and, for every $i$ and every $a \ne 0$:
$$\bigl|\,|S_i'| - (1 - \lambda)|S_i|\,\bigr| \le t, \qquad |S_i' \cap (S_i' + a)| \ \le\ (1 - \lambda)^2\,|S_i \cap (S_i + a)| + t \ \le\ (1 - \lambda)^2 |S_i| + t .$$

*Proof.* Put each point in $P$ independently with probability $\lambda$, and on $P$ give $w'$ a value different from all $c_i(x)$. $|S_i'|$ is a sum of $|S_i|$ independent indicators of mean $1 - \lambda$, so it deviates by more than $t$ with probability at most $2e^{-2t^2/n}$ (Hoeffding). $|S_i' \cap (S_i' + a)|$ is twice the number of fibres $\{x, x + a\} \subseteq S_i$ that avoid $P$, a sum of $f \le n/2$ independent variables with values in $\{0, 2\}$ and mean $2(1 - \lambda)^2$, so it exceeds its mean by more than $t$ with probability at most $e^{-t^2/2f} \le e^{-t^2/n}$. There are $L$ events of the first kind and $L(n - 1)$ of the second, and $2Le^{-2t^2/n} + L(n - 1)e^{-t^2/n} < 2Ln\,e^{-t^2/n} = 1$. $\square$

For lists of size $2^{\mathrm{poly}(N)}$, $t = O(\sqrt n\,\mathrm{poly}(N)) = o(n)$.

**Corollary 2.2 (the "few" side contains the list problem). [proved]** Let $\lambda \le 1/4$, $T_1$ an agreement count, $T' = \lceil(1 - \lambda)T_1 - t\rceil$ and $\eta n = \lambda T_1/4 - 2t - 1$. For every word, the number of list members with $T_1 \le |S_i| < (1 + \lambda/2)T_1$ is at most $B^{\mathrm{set}}_N(k, T'; (T' - \eta n)/2)$. Consequently, if $B^{\mathrm{set}}_N(k, T'; (T' - \eta' T')/2) \le B$ for all $T'$ in a range, then $\Lambda^\ast_N(k, T_1) \le \lceil 2\ln(n/T_1)/\ln(1 + 2\eta')\rceil\,B$ for $T_1 = (1 + 4\eta' + o(1))\,T'$ in the corresponding range.

*Proof.* Apply Proposition 2.1 to these members. Then $|S_i'| \ge T'$, and $|S_i' \cap (S_i' + a)| \le (1 - \lambda)^2(1 + \lambda/2)T_1 + t \le (1 - \tfrac54\lambda)T_1 + t < T' - \eta n$ for all $a$ (using $(1 - \lambda)^2(1 + \lambda/2) \le 1 - \tfrac54\lambda$ for $\lambda \le 1/4$). So they are members of a list at agreement $T'$ none of which is counted by the second term of Corollary 1.2 at $2A = T' - \eta n$. For the consequence cover $[T_1, n]$ by bands of ratio $1 + \lambda/2$ with $\lambda = 4\eta' + o(1)$. $\square$

In words: a dichotomy "all but $B$ members are invariant up to $\eta n$ in some direction" at agreement $\tau'$ implies, without any recursion, the list bound $O(B\log n/\eta)$ at agreement $\tau'(1 + 4\eta)$. For the recursion the losses $\eta$ must be summable over $N$ levels, so the shift is negligible and the hypothesis is the conclusion. Exact invariance is even more fragile: one changed point destroys every period of every member through it, and the flats themselves ($S = V \setminus 0$) have no exact period.

**Proposition 2.3 (depth of a robust descent). [proved]** For the random perturbation of Proposition 2.1 and a member whose set was invariant under a subspace $U$, the expected number of cosets of a subspace $U' \le U$ that lie in $S_i'$ is $(1 - \lambda)^{|U'|}|S_i|/|U'|$. So a descent that keeps full cosets retains the fraction $(1 - \lambda)^{2^j}$ of the agreement after $j$ steps and is dead after $\log_2(1/\lambda)$ steps, at a quotient that still has $\lambda n$ points.

*Proof.* A coset survives iff none of its $|U'|$ points is in $P$. $\square$

This is why the right invariant cannot be a property of the agreement sets. The codewords of a perturbed list are the same codewords, and what is periodic in every known family is a property of the codewords alone: the triple functions.

## 3. The descent that survives: periods of the differences

Everything in this section holds on every subspace domain of every field of characteristic two.

### 3.1 The $U$-problem

**Definition 3.1.** Let $U \le D$ be a subspace of size $m$, $\mathcal{L} = L_U$, $D/U := \mathcal{L}(D)$ (a subspace of dimension $N - \log_2 m$), $\kappa \ge 0$ an integer and $v : D \to F \cup \{\bot\}$ a word that may be undefined at some points. A *member* of the $U$-problem at agreement $A$ is a polynomial $P \in F[Y]$ of degree at most $\kappa$ with $\#\{x \in D : v(x) = P(\mathcal{L}(x))\} \ge A$. It is the list problem, for an arbitrary word, of the code of $U$-periodic polynomials $\{P(L_U)\}$, or equivalently the problem on $D/U$ in which every point carries the multiset of the $m$ values of $v$ on its coset. $U = 0$, $\kappa = k - 1$ is the ordinary problem. The *slack* is $A - m\kappa$ (it is $T - k + 1$ for the ordinary problem). $\Lambda_{N,j}(\kappa, \Delta)$ is the largest number of members over all fields, domains, $U$ of dimension $j$, words, degrees $\kappa' \le \kappa$ and agreements with slack at least $\Delta$.

**Lemma 3.2 (base bound). [proved]** If $A > m\kappa$, the $U$-problem has at most $\prod_{i=0}^{\kappa}\frac{n - mi}{A - mi} \le \bigl(\frac{n}{A - m\kappa}\bigr)^{\kappa + 1}$ members.

*Proof.* The argument of note 04 Theorem 1.2. Let $f(r)$ be the largest number of members in an affine subspace $H$ of dimension $r$ of $\{P(\mathcal{L}) : \deg P \le \kappa\}$. The common zeros in $D$ of its direction space are the preimages of at most $\kappa + 1 - r$ points of $D/U$, so their number $z$ is at most $m(\kappa + 1 - r)$. Off them, $\{h \in H : h(x) = v(x)\}$ is empty or of dimension $r - 1$, and a member lies in at least $A - z$ of these, so $f(r)(A - z) \le (n - z)f(r - 1)$ and $(n - z)/(A - z)$ increases with $z$. $\square$

### 3.2 The descent

**Proposition 3.3 (difference descent). [proved]** Let $P_0 \ne P_1$ be two members of a $U$-problem (degree $\kappa$, agreement $A$, $|U| = m$), $a' \in (D/U) \setminus 0$, $q' = Y^2 + a'Y$, and $U' = \mathcal{L}^{-1}\{0, a'\} \cap D$, so that $L_{U'} = q'(\mathcal{L})$. Let $M_{a'}$ be the set of members $P_l$ such that $(P_l - P_0)/(P_1 - P_0)$ is invariant under $Y \mapsto Y + a'$ (it contains $P_0$, $P_1$ and every member collinear with them). Then there are $\varrho \in F[Y]$ and polynomials $Q_l$ with
$$P_l = P_0 + \varrho\,Q_l(q'), \qquad \deg Q_l \le \kappa' := \lfloor(\kappa - \deg\varrho)/2\rfloor,$$
and $P_l \mapsto Q_l$ is an injection of $M_{a'}$ into the members of the $U'$-problem with the word $v'(x) = (v(x) - P_0(\mathcal{L}(x)))/\varrho(\mathcal{L}(x))$ ($\bot$ where $v = \bot$ or $\varrho(\mathcal{L}(x)) = 0$), degree $\kappa'$ and agreement $A' = A - z_0$, $z_0 = \#\{x : \varrho(\mathcal{L}(x)) = 0,\ v(x) = P_0(\mathcal{L}(x))\} \le m\deg\varrho$. The slack does not decrease: $A' - 2m\kappa' \ge A - m\kappa$.

*Proof.* The fixed field of $Y \mapsto Y + a'$ in $F(Y)$ is $F(q')$. Write $u = P_1 - P_0$ and $(P_l - P_0)/u = p_l(q')/e_l(q')$ with $p_l, e_l \in F[Y]$ coprime, $e_l$ monic. Then $p_l(q')$ and $e_l(q')$ are coprime (substitute in a Bezout identity), so $e_l(q')$ divides $u$. The monic $e$ with $e(q') \mid u$ are closed under least common multiples, because $\gcd(e, e')(q') = \gcd(e(q'), e'(q'))$ by the same Bezout argument. Let $e_u$ be the largest, $\varrho = u/e_u(q')$ and $Q_l = p_l\,e_u/e_l$: then $P_l - P_0 = \varrho\,Q_l(q')$, also for $l = 0$ ($Q = 0$) and $l = 1$ ($Q = e_u$), and $\deg\varrho + 2\deg Q_l \le \kappa$. At a point with $\varrho(\mathcal{L}(x)) \ne 0$, $P_l(\mathcal{L}(x)) = v(x)$ iff $Q_l(L_{U'}(x)) = v'(x)$. At a point with $\varrho(\mathcal{L}(x)) = 0$ all members of $M_{a'}$ take the value of $P_0$, and there are $z_0$ such points where this is the value of $v$. So the agreement of $Q_l$ is that of $P_l$ minus $z_0$. Finally $2m\kappa' \le m\kappa - m\deg\varrho$ and $z_0 \le m\deg\varrho$. $\square$

For $U = 0$ this says: for two fixed members $c_0, c_1$ of an ordinary list, the members $c_l$ whose triple function $\xi_l$ (a Möbius image of $(c_l - c_0)/(c_1 - c_0)$) has the period $a$ are exactly $c_0 + \varrho\,Q_l(X^2 + aX)$, and they form a list of the $\{0, a\}$-problem with no loss in agreement. The price is that the word $v'$ is two-valued on $D/a$: the descent of Corollary 1.2 is the special case in which $v'$ is $a$-invariant on the support of every member. A perturbation of $w$ changes $v'$ at the same points and nothing else.

**Corollary 3.4 (recursion on differences). [proved]** For a list of a $U$-problem and a pair $(P_0, P_1)$ let $B(P_0, P_1)$ be the number of members $P_l$ whose function $(P_l - P_0)/(P_1 - P_0)$ is not constant and has no period in $(D/U) \setminus 0$. Then $L \le 2 + B(P_0, P_1) + \sum_{a' \ne 0}(|M_{a'}| - 2)$, and with $B^{\mathrm{diff}}_{N,j}$ the maximum over lists of the minimum over pairs of $B(P_0, P_1)$:
$$\Lambda_{N,j}(\kappa, \Delta) \ \le\ 2 + B^{\mathrm{diff}}_{N,j}(\kappa, \Delta) + (2^{N-j} - 1)\,\Lambda_{N,j+1}(\lfloor\kappa/2\rfloor, \Delta) .$$

**Theorem 3.5 (the dimension induction, conditional). [proved conditional on DP]** Hypothesis **DP**$(B)$: $B^{\mathrm{diff}}_{N,j}(\kappa, T - k + 1) \le B$ for all $0 \le j \le J := \lceil\log_2 k\rceil$ and $\kappa \le (k - 1)/2^j$. Then
$$\Lambda^\ast_N(k, T) \ \le\ 2^{NJ - J(J-1)/2}\Bigl(J(B + 2) + \frac{n}{T - k + 1}\Bigr) .$$
At $N = 25$, rate 1/2, this is $2^{324}(24B + n/(T - k + 1))$.

*Proof.* Iterate Corollary 3.4: the product of the factors $2^{N - i}$, $i < j$, is $2^{Nj - j(j-1)/2}$. At level $J$, $\kappa = 0$ and Lemma 3.2 gives at most $n/\Delta$ members. $\square$

A density version works the same way: if at every level some pair has a period for a fraction $g$ of the members (instead of all but $B$), the factor per level is $2^{N-j}/g$ and the bound is multiplied by $g^{-J}$, which is affordable for $g \ge 1/\mathrm{poly}(n)$.

**Corollary 3.6 (bounded index). [proved]** Let $c_0, c_1$ be two members of an ordinary list at agreement $T > k$, $\pi$ a power of two, and suppose that $G$ of the other members $c_l$ have $|\Pi(\xi_l)| \ge \pi$ or are collinear with $c_0, c_1$. Then
$$G + 2 \ \le\ \binom{N}{\log_2(n/\pi)}_2\ \prod_{i=1}^{\lfloor(k-1)/\pi\rfloor + 1}\frac{n - k + i}{T - k + i} .$$

*Proof.* This is the mechanism of note 17 Theorem 5.1 without Conjecture P. Choose for each such $l$ a subspace $\Pi^\ast \le \Pi(\xi_l)$ of size $\pi$. By Proposition 3.3 iterated (or directly, with $L_{\Pi^\ast}$ in place of $q'$) the members assigned to $\Pi^\ast$, with $c_0$ and $c_1$, lie in $c_0 + \varrho\cdot\{Q(L_{\Pi^\ast}) : \deg Q \le \lfloor(k - 1 - \deg\varrho)/\pi\rfloor\}$, an affine space of codewords of dimension at most $\lfloor(k-1)/\pi\rfloor + 1$, and note 04 Theorem 1.2 bounds the members in it. $\square$

### 3.3 Status of the hypothesis

DP is a statement about codewords only, so the perturbation of section 2 does not touch it, and twists (note 17 Proposition 2.4) fix every $\xi$. I have no proof of DP for any $B = 2^{\mathrm{poly}(N)}$ in any window, and it is a P-type statement: for three members with forced excess it follows from Conjecture P (note 17 Lemma 2.3), and in the middle of the windows single triples have no forced excess at all, so only a density statement can hold. What I can say:

1. **[proved, section 5]** On a generic subspace, within about $10^{-5}$ of the Johnson radius, the density form holds with periods of full size: a fraction $g \ge 0.05$ of all triples are flats.
2. **[checked, section 6]** For the $5n/8$ family at $n = 32$ ($1400$ members) there are pairs for which every other member has a periodic $\xi_l$ ($B = 0$). For the same word one step lower ($T = 19$, $15736$ members) the best of the 3200 pairs I sampled has a period for $2166$ members and none for $13568$. Those are lifts-to-be: at $n = 32$ the family sits at its base index, and the same configurations lifted to larger $n$ are periodic. So, unless a pair that I did not sample does much better, $B^{\mathrm{diff}}_{N,0}$ is about $1.3 \cdot 10^4$ or more at $N = 5$ in this region, and the hypothesis can only hold in the form "primitive (period-free) configurations exist only up to a bounded dimension $N_0(\tau)$", which is the bounded-index picture of notes 17 and 27.
3. **[conjectured]** DP$(B)$ with $B = 2^{O(N)}$ in every window. I do not consider the evidence strong: it is the statement that everything large is a lift.

## 4. The formal model: transfer lemma and gap theorem

In this section $D$ is generic, $A = \mathbb{F}_2[b_1, \dots, b_N]$, $K = \mathbb{F}_2(b)$. $A$ is a unique factorization domain with the single unit 1, every $z \in D \setminus 0$ is a prime of $A$ (a nonzero linear form), $A/zA$ is a polynomial ring in $N - 1$ variables, and the reduction $D \to A/zA$ is $\mathbb{F}_2$-linear with kernel $\{0, z\}$.

**Normal form. [proved]** Let $\xi \in F(X)$ be nonconstant with $\nu \ge 2\delta + 2$. By the uniqueness lemma (note 26 Lemma 1.2) the linear system "degree at most $\delta$, zeros on $R_0$, poles on $R_1$, value 1 on $R_2$" has the single solution $\xi$, and since its coefficients lie in $K$, $\xi \in K(X)$. Write $\xi = v_0/v_1$, $v_0 + v_1 + v_2 = 0$, with $v_i \in A[X]$ pairwise coprime in $K[X]$, $\max\deg v_i = \delta$, and no prime of $A$ dividing all coefficients of all three. Then the contents $\gamma_i$ of the $v_i$ are pairwise coprime (a prime dividing two of them divides the third polynomial), and by Gauss's lemma $v_i = \gamma_i Z_i h_i$ with $Z_i = \prod_{x \in R_i}(X - x)^{m_i(x)}$ the full contribution of the roots in $D$ and $h_i \in A[X]$ primitive, without roots in $D$, of degree at most $\delta - r_i = s_i$. Put $\mathcal{Z}_l = \{z \in D \setminus 0 : z \mid \gamma_l\}$: three pairwise disjoint sets of directions.

**Lemma 4.1 (transfer). [proved]** Let $\{i, j, l\} = \{0, 1, 2\}$ and $z \in D \setminus 0$.

1. If $z \notin \mathcal{Z}_l$ then $|R_i \cap (R_j + z)| \le s_l$.
2. If $z \in \mathcal{Z}_l$ then $|R_i \cap (R_j + z)| \ge r_i - s_j = r_j - s_i$.

So every direction is of one of four types (neutral, or transferring one pair of fibres into each other), and for each pair of fibres the number $|R_i \cap (R_j + z)|$ avoids the interval $(s_l,\ r_i - s_j)$, which has length $r_i + r_j + r_l - 2\delta = \nu - 2\delta$.

*Proof.* Reduce modulo $z$ and write a bar for reductions. $\bar h_i \ne 0$ has degree at most $s_i$, and $\bar Z_i$ has, at the class $\{x, x + z\}$, a root of multiplicity $m_i(x) + m_i(x + z)$. (1) $\bar v_l = \bar\gamma_l\bar Z_l\bar h_l \ne 0$. Let $x \in R_i$ with $x + z \in R_j$. Its class is a root of $\bar Z_i$ and of $\bar Z_j$. If $z$ divides neither $\gamma_i$ nor $\gamma_j$, it is a common root of $\bar v_i$ and $\bar v_j$, hence of $\bar v_l$. If $z \mid \gamma_i$ then $\bar v_i = 0$ and $\bar v_j = \bar v_l$, and the class is a root of $\bar v_j$, hence of $\bar v_l$; symmetrically if $z \mid \gamma_j$. The class contains no point of $R_l$, so it is a root of $\bar h_l$. Distinct $x$ give distinct classes, and $\bar h_l$ has at most $s_l$ roots. (2) Now $\bar v_l = 0$ and $\bar\gamma_i\bar Z_i\bar h_i = \bar\gamma_j\bar Z_j\bar h_j \ne 0$. For $x \in R_i$ with $x + z \notin R_j$ the class of $x$ is a root of $\bar Z_i$ of multiplicity at least the number of its points in $R_i$, and not a root of $\bar Z_j$, so it is a root of $\bar h_j$ of at least that multiplicity. Summing over classes, $r_i - |R_i \cap (R_j + z)| \le \deg\bar h_j \le s_j$. $\square$

Part of this is in earlier notes: note 17 Proposition 3.5 has (1) for non-degenerate directions and the lower bound of (2), by valuations, and note 26 section 2.4 observes that the contents are products of elements of $D$. What is added is that (1) holds in every case in which the third content is not divisible (in particular in the transfer directions of the other two pairs), which is what makes the count below possible.

**[checked]** `37_transfer_check.py`: 196 functions $\xi = \xi_0 \circ L_\Pi$ on random subspaces of $\mathrm{GF}(2^{64})$ with $n = 8, \dots, 64$ ($\xi_0$ the unique function with a prescribed fibre pattern, $|\Pi| \le 4$): for every direction a type satisfying (1) and (2) exists (0 violations, 3020 directions with a forced transfer type), while 116 of 196 random triples of disjoint sets of the same sizes violate the lemma.

**Lemma 4.2 (rigidity). [proved; note 17 Proposition 3.4 with the threshold lowered by one; every subspace domain]** If $a \ne 0$ and $\sum_i |R_i \cap (R_i + a)| \ge 2\delta$ then $a \in \Pi(\xi)$.

*Proof.* $\Omega = v_0(X)v_1(X + a) + v_1(X)v_0(X + a)$ has degree at most $2\delta - 1$: if both $v_0$ and $v_1$ have degree $\delta$ the leading terms cancel. It vanishes on $R_0 \cap (R_0 + a)$ and $R_1 \cap (R_1 + a)$ (a factor of each term vanishes) and on $R_2 \cap (R_2 + a)$ (there $v_0 = v_1$ at $x$ and at $x + a$, and the two terms are equal). These sets are disjoint, so $\Omega = 0$, which is $\xi(X + a) = \xi(X)$. $\square$

**Theorem 4.3 (gap). [proved]** Let $D$ be a generic subspace of dimension $N$ of any field $F$ and $\xi \in F(X)$ nonconstant of degree $\delta$. If $s = 3\delta - \nu(\xi) < \delta^2/(4n)$, then $s = 0$ and $\xi = \mu \circ L_\Pi$ with $\Pi = \Pi(\xi)$ of size $\delta$ and $\mu$ of degree one. In other words: every triple function is a flat or has
$$\nu(\xi) \ \le\ 3\delta - \frac{\delta^2}{4n} .$$

*Proof.* If $\delta = 1$ the hypothesis forces $\nu = 3$ and there is nothing to prove. Let $\delta \ge 2$. If $\nu \le 2\delta + 1$ then $s \ge \delta - 1 \ge \delta/2 > \delta^2/4n$, so $\nu \ge 2\delta + 2$ and the normal form applies. Put $\epsilon = s/\delta$. From $3\delta - s = \nu \le n$ we get $\delta \le n/(3 - \epsilon)$, and then $\epsilon < \delta/4n$ gives $\epsilon < 0.086$ and $\delta/n < 0.344$. Label the fibres so that $s_2 \le s_1 \le s_0$, hence $r_2 \ge r_1 \ge r_0 \ge \delta - s$.

*Step 1, many transfer directions.* $R_1$ and $R_2$ are disjoint, so $\sum_{z \ne 0}|R_1 \cap (R_2 + z)| = r_1 r_2$. By Lemma 4.1 the summand is at most $s_0$ off $\mathcal{Z}_0$ and at most $r_1$ on it, so $r_1 r_2 \le |\mathcal{Z}_0| r_1 + (n - 1 - |\mathcal{Z}_0|)s_0$ and
$$|\mathcal{Z}_0| \ \ge\ \frac{r_1 r_2 - s_0(n - 1)}{r_1 - s_0}, \qquad\text{likewise}\qquad |\mathcal{Z}_1| \ \ge\ \frac{r_0 r_2 - s_1(n - 1)}{r_0 - s_1} .$$

*Step 2, sums of transfer directions are near-periods.* Let $z \ne z'$ in $\mathcal{Z}_0$ and $a = z + z'$. The sets $R_1 \cap (R_2 + z)$ and $R_1 \cap (R_2 + z')$ have at least $r_1 - s_2$ elements each, so they share at least $r_1 - 2s_2$ points $x$, and for each of them $x + z \in R_2 \cap (R_2 + a)$. Hence $|R_2 \cap (R_2 + a)| \ge r_1 - 2s_2 = r_2 - s_1 - s_2$, and in the same way $|R_1 \cap (R_1 + a)| \ge r_2 - 2s_1 = r_1 - s_1 - s_2$. For $a \in (\mathcal{Z}_1 + \mathcal{Z}_1) \setminus 0$: $|R_0 \cap (R_0 + a)| \ge r_0 - s_0 - s_2$ and $|R_2 \cap (R_2 + a)| \ge r_2 - s_0 - s_2$.

*Step 3, common near-periods are periods.* Both $(\mathcal{Z}_0 + \mathcal{Z}_0) \setminus 0$ and $(\mathcal{Z}_1 + \mathcal{Z}_1) \setminus 0$ lie in $\mathcal{P}_2 = \{a \ne 0 : |R_2 \cap (R_2 + a)| \ge r_2 - s_0 - s_2\}$, and $\sum_{a \ne 0}|R_2 \cap (R_2 + a)| = r_2(r_2 - 1)$ gives $|\mathcal{P}_2| \le r_2(r_2 - 1)/(r_2 - s_0 - s_2)$. The first set has at least $|\mathcal{Z}_0| - 1$ elements and the second at least $|\mathcal{Z}_1| - 1$, so they share at least $|\mathcal{Z}_0| + |\mathcal{Z}_1| - 2 - |\mathcal{P}_2|$ elements $a$. For such $a$, $\sum_i|R_i \cap (R_i + a)| \ge \nu - (s_1 + s_2) - (s_0 + s_2) - (s_1 + s_2) \ge \nu - 2s = 3\delta - 3s \ge 2\delta$ (using $s_1 + 2s_2 \le s$ and $\epsilon \le 1/3$), so $a \in \Pi(\xi)$ by Lemma 4.2. Therefore
$$|\Pi(\xi)| \ \ge\ |\mathcal{Z}_0| + |\mathcal{Z}_1| - 1 - |\mathcal{P}_2| .$$

*Step 4, the count.* With $|\mathcal{Z}_0| \ge r_2 - s_0 n/r_1$, $|\mathcal{Z}_1| \ge r_2 - s_1 n/r_0$ (weaken Step 1), $r_0, r_1 \ge \delta(1 - \epsilon)$, $r_2 \ge \delta - s/3$, and $|\mathcal{P}_2| \le r_2 - 1 + (s_0 + s_2)\,r_2/(r_2 - s_0 - s_2) \le r_2 - 1 + s/(1 - \epsilon)$ (because $(s_0 + s_2)/r_2 \le \epsilon$, which is $s\,s_2 \le s_1\delta$):
$$|\Pi(\xi)| \ \ge\ \delta - s\Bigl[\frac13 + \frac{1}{1 - \epsilon} + \frac{n/\delta}{1 - \epsilon}\Bigr] \ >\ \delta - \delta\Bigl[\frac{\delta}{4n}\Bigl(\frac13 + \frac{1}{1 - \epsilon}\Bigr) + \frac{1}{4(1 - \epsilon)}\Bigr] \ >\ \delta\,(1 - 0.123 - 0.274) \ >\ \frac{\delta}{2} .$$
$\deg\xi = |\Pi|\deg\xi_0$ for $\xi = \xi_0 \circ L_\Pi$, so $|\Pi|$ divides $\delta$ and $|\Pi| = \delta$, $\deg\xi_0 = 1$. Then every fibre of $\xi$ in $D$ is empty or a full coset of $\Pi$, and $r_i \ge \delta - s > 0$ gives $r_i = \delta$ and $s = 0$. $\square$

**[checked]** `37_gap_inequality.py` part 1: with the exact bounds of Steps 1 and 3 (no weakening), $|\mathcal{Z}_0| + |\mathcal{Z}_1| - 1 - |\mathcal{P}_2| > \delta/2$ and $\delta \ge 3s$ for all 58862 parameter sets $(n, \delta, s_0, s_1, s_2)$ with $N \le 10$ that satisfy the hypothesis, and for 200000 random ones with $11 \le N \le 28$.

**Remarks.** (i) **[proved]** Conjecture P of note 17 ($\nu \le 2\delta + |\Pi|$) holds for every $\xi$ with $s < \delta^2/4n$. Note 26 Corollary 2.1 has it for $s \le 1$. (ii) The scale $\delta^2/n$ is right for this method and the constant is within a factor 8 of optimal for the statement: the function of generic type with fibre pattern $(3, 3, 1)$ on 8 points has $s\,n/\delta^2 = 16/9$ and no period, and its lifts keep this ratio **[checked]**. Under Conjecture P every non-flat function has $s \ge \delta/2$, which is stronger by the factor $2n/\delta > 5.8$. (iii) The proof uses genericity only in Lemma 4.1. The counting, the near-periods and the rigidity hold on every subspace domain, so on any domain the conclusion holds for every $\xi$ that satisfies the transfer dichotomy in all directions. On the real domain the dichotomy can fail (the reduction modulo a point of $D$ has no meaning in a finite field), and I have no substitute.

## 5. A list bound strictly below the Johnson radius on a generic subspace

**Theorem 5.1. [proved]** Let $D$ be a generic subspace of dimension $N$ of any field, $k \le n/2$, $k < T$, $\tau = T/n$ and $\theta = (k - 1)/n - \tau^2$ (the Johnson bound is the case $\theta < 0$). Let $0 < \beta < (k - 1)/n$ and $\theta_1 > 0$ be such that
$$g \ :=\ 1 - \frac{63(\theta + \theta_1)}{\beta^2} - \frac{\tau^3 + (1 + 2\tau)(\theta + \theta_1)}{(k - 1)/n - \beta} \ >\ 0 .$$
Let $\pi^\ast$ be the least power of two with $\pi^\ast \ge \tfrac67\beta n$ and $\delta^\ast = \lfloor(k - 1)/\pi^\ast\rfloor$. Then every word, with any number of lanes, has at most
$$\max\Bigl(1 + \frac{2}{\theta_1},\ \ 2 + \frac1g\binom{N}{\log_2(n/\pi^\ast)}_2\prod_{i=1}^{\delta^\ast + 1}\frac{n - k + i}{T - k + i}\Bigr)$$
codewords of degree $< k$ at agreement $T$. If moreover no power of two lies in the interval $[\tfrac67\beta n,\ \min(k - 1,\ T - k + 1 + \tfrac{2}{21}\beta^2 n)]$, the list has fewer than $1 + 2/\theta_1$ members.

*Proof.* Let $L$ be the list size and suppose $L - 1 \ge 2/\theta_1$. Cut every agreement set down to a set $S_i$ of exactly $T$ points, and let $\mu(x)$ be the number of $i$ with $x \in S_i$, $d_{ij} = k - 1 - |S_i \cap S_j| \ge 0$ the *defect* of a pair.

*Pairs.* $\sum_{i<j}d_{ij} = \binom L2(k - 1) - \sum_x\binom{\mu(x)}{2} \le \binom L2(k - 1) - n\binom{LT/n}{2}$ by convexity, so the mean defect is at most $(L\theta n + T - k + 1)/(L - 1) \le n(\theta + 2/(L - 1)) \le n(\theta + \theta_1)$. Call a pair *heavy* if $d_{ij} > d^\ast := \beta^2 n/21$. By Markov the heavy pairs are at most a fraction $21(\theta + \theta_1)/\beta^2$ of all pairs, and the triples containing a heavy pair at most a fraction $63(\theta + \theta_1)/\beta^2$ of all triples.

*Triple intersections.* With $p_x = \mu(x)/L$: $\sum_x p_x = \tau n$ and $\sum_x(p_x - \tau)^2 = L^{-2}\sum_x\mu(x)^2 - \tau^2 n \le n(\theta + (T - k + 1)/(nL)) \le n(\theta + \theta_1)$. Since $p^3 \le \tau^3 + 3\tau^2(p - \tau) + (1 + 2\tau)(p - \tau)^2$ for $0 \le p \le 1$, the mean over triples of $|S_i \cap S_j \cap S_l|$, which is at most $\sum_x p_x^3$, is at most $n(\tau^3 + (1 + 2\tau)(\theta + \theta_1))$. So the triples with $|S_i \cap S_j \cap S_l| > k - 1 - \beta n$ are at most the fraction given by the last term of $g$.

*Good triples are flats.* So a fraction at least $g$ of the triples have three light pairs and $|B| \le k - 1 - \beta n$, $B$ the triple intersection. For such a triple let $G$ be the gcd of the differences and $\xi$ its function. As in note 17 Theorem 2.1, $s_l \le d_{ij}$ (the roots of $u_l$ in $D$ contain $S_i \cap S_j$ minus the roots of $G$, and $\delta \le k - 1 - \deg G$), so $s \le 3d^\ast = \beta^2 n/7$. Writing $c_i - c_j = Z_{S_i \cap S_j}h_{ij}$ with $\deg h_{ij} \le d_{ij}$, $G$ divides $\gcd(Z_{S_i \cap S_j}, Z_{S_j \cap S_l})\,h_{ij}h_{jl} = Z_B h_{ij}h_{jl}$, so $\deg G \le |B| + 2d^\ast$ and $\delta \ge (k - 1 - d^\ast) - \deg G \ge \beta n - 3d^\ast \ge \tfrac67\beta n$ (as $\beta \le 1/2$). Then $\delta^2/4n \ge \tfrac{9}{49}\beta^2 n > \tfrac17\beta^2 n \ge s$, and Theorem 4.3 says that $\xi = \mu \circ L_\Pi$ with $|\Pi| = \delta$, a power of two, $\delta \ge \tfrac67\beta n$. Also $|B| \ge |S_i \cap S_j| + |S_i \cap S_l| - |S_i| \ge 2(k - 1 - d^\ast) - T$ and $\delta \le k - 1 - |B|$, so $\delta \le \min(k - 1,\ T - k + 1 + 2d^\ast)$. This proves the last assertion: if no power of two is available there is no good triple, so $g > 0$ is contradicted and $L - 1 < 2/\theta_1$.

*Counting.* Each good triple is counted for three pairs, so some pair $(c_0, c_1)$ has at least $g(L - 2)$ good third members, each with $|\Pi(\xi_l)| \ge \pi^\ast$. Corollary 3.6 bounds their number. $\square$

**Numbers. [proved; evaluated by `37_gap_inequality.py` part 2 with exact $n$, $k$, $T$]** Johnson threshold: the least $T$ with $T^2 > n(k - 1)$.

| rate | $N$ | $T/n$ | points below the Johnson threshold | $\beta$, $g$ | bound |
| --- | --- | --- | --- | --- | --- |
| 1/2 | 25 | $0.7071016$ | 175 | $0.0875$, $0.052$ | $2^{77.0}$ |
| 1/2 | 28 | $0.7071016$ | 1399 | $0.0875$, $0.052$ | $2^{86.0}$ |
| 1/4 | 25 | $0.4999888$ | 376 | $0.0794$, $0.099$ | $2^{74.1}$ |
| 1/4 | 28 | $0.4999888$ | 3015 | $0.0794$, $0.099$ | $2^{83.1}$ |
| 1/8 | 25 | $0.3535463$ | 237 | $0.0731$, $0.059$ | $2^{19.6}$ (no power of two) |
| 1/8 | 28 | $0.3535463$ | 1904 | $0.0731$, $0.059$ | $2^{19.6}$ (no power of two) |
| 1/16 | 25 | $0.2499932$ | 225 | $0.0366$, $0.160$ | $2^{20.2}$ (no power of two) |
| 1/16 | 28 | $0.2499933$ | 1808 | $0.0366$, $0.159$ | $2^{20.2}$ (no power of two) |

The windows end at $\theta \approx 1.2 \cdot 10^{-5}$, $1.9 \cdot 10^{-5}$, $8.4 \cdot 10^{-6}$, $5.6 \cdot 10^{-6}$; the rows are at 0.6 of that. At rates 1/8 and 1/16 the degree of a flat would have to be a power of two between $\tfrac67\beta n$ and $k - 1$, and there is none, so the list is bounded by a constant: near the Johnson radius the typical triple of a large list has $\delta \approx (\rho - \rho^{3/2})n$, which is a power of two times $n$ only at rate 1/4 ($n/8$, the flats). At rate 1/2 the constant bound also holds, but only within about $1.4 \cdot 10^{-7}$ of the radius. Degree slack (codewords of degree $\le k - 1 + \ell$) is the same theorem with $k + \ell$ for $k$.

**Why the window is so thin, and what would widen it.** The chain is: below Johnson by $\theta$ and a large list force mean pair defect about $\theta n$; a triple is a flat when its three defects sum to less than $\delta^2/4n \approx n/260$; Markov then needs $\theta \ll 10^{-3}$, and the second Markov (triple intersections) costs another factor. With perfectly uniform lists (every pair and every triple at the mean, so $s = 3(\rho - \tau^2)n$ and $\delta = (\rho - \tau^3)n$) Theorem 4.3 would apply down to $\tau \approx 0.706$ at rate 1/2, and Conjecture P in its place (non-flat implies $s \ge \delta/2$) down to about $0.686$ **[heuristic computation, not a theorem]**. Below that the typical triple of a large list is not near a flat, triples have no forced excess, and the method has nothing to say.

## 6. Profiles of real lists

`37_profile.c` enumerates the full list of a word on a random subspace of $\mathrm{GF}(2^{64})$ (every polynomial, by exhaustive interpolation as in `02_lists.c`), and prints for every member $|S|$, the stabilizer of $S$ and $\sigma = \max_{a \ne 0}|S \cap (S + a)|$, and for sampled pairs the period groups of all triple functions (tested at three random points of the field). **[checked]**, generic domain, seed 1:

| word, $(n, k, T)$ | list | members with an exact period of $S$ | profile $(\lvert S\rvert, \lvert\mathrm{Stab}\rvert, \sigma)$ : count | triple functions |
| --- | --- | --- | --- | --- |
| flats, $X^{15}$, $(32, 8, 15)$ | 31 | 0 | $(15, 1, 14)$ : 31 | every non-collinear triple has $\lvert\Pi\rvert = 4 = \delta$ |
| the same word changed at 2 points, $T = 13$ | 31 | 16 | $(13, 1, 12)$ : 7, $(14, 2, 14)$ : 16, $(15, 1, 14)$ : 8 | unchanged |
| $X^8 L_W$, $\lvert W\rvert = 2$, $(16, 9, 10)$ | 504 | 56 | $(10, 1, 8)$ : 448, $(10, 2, 10)$ : 56 | best of 2000 pairs: a period for 78 of 502 |
| $X^{16} L_W$, $\lvert W\rvert = 4$, $(32, 17, 20)$ | 1400 | 1400 | $(20, 2, 20)$ : 1344, $(20, 4, 20)$ : 56 | best of 2000 pairs: a period for all 1398; over random pairs 14 percent of the thirds |
| $X^{16} L_W$, $(32, 17, 19)$ | 15736 | 1400 | $(19, 1, 16)$ : 14336, plus the 1400 above | best of 200 pairs among the 56 members with $\lvert\mathrm{Stab}\rvert = 4$: a period for 2166 of 15734; over 3000 random pairs 0.09 percent of the thirds |
| the same word changed at 1 point, $T = 19$ | 7224 | 525 | $(19, 1, 16)$ : 5824, $(19, 1, 18)$ : 875, $(20, 2, 20)$ : 504, $(20, 4, 20)$ : 21 | as above |

Reading. (i) The flats have no member with an invariant set and are completely periodic in the sense of section 3: this is the difference between the two descents in the smallest example. (ii) The $5n/8$ family at $n = 32$ is exactly what the set recursion wants (every member invariant under 1 or 3 nonzero directions, 504 members per direction at most) and what the difference recursion wants (a pair with $B = 0$), and one changed point removes 875 members from the first picture (they become $(19, 1, 18)$) and none from the second. (iii) The members of that family are invariant under a subspace of size $n/16$, not $n/8$: at $n = 16$ the 448 members outside the 56 have no period at all. (iv) One step below $5n/8$ at $n = 32$ the list is eleven times larger and 91 percent of it has neither an invariant set nor, for any pair I sampled, a periodic triple function. The count $14336 = 56 \cdot 4^4$ fits the following description, which I did not prove: in the Walsh criterion of notes 02 and 05 (same $e_1, e_2, e_3$ iff spectra congruent modulo 8) add to the indicator of a $U$-periodic member the signed indicator of an affine 3-flat split into two parallel 2-flats, one inside the set and one meeting it in a single point, which becomes a double point. In dimension $N$ the same configuration has the 2-flats replaced by flats of size $n/8$, the double point by a coset of size $n/32$, and the members are periodic under a subspace of size $n/32$: the family lives at agreement $19n/32$ with index 32, and at $n = 32$ we see its base. **[interpretation, checked only through the count]**

So the data are consistent with "every large list is a lift from a bounded index $M(\tau)$" ($M = 16$ at $5/8$, $32$ at $19/32$) and show that at the base index lists of size $10^4$ already exist with no period of any kind. For the induction this means that the term $B$ of either recursion is large in small dimension and must vanish, or stay polynomial, in large dimension, and nothing here proves that.

## 7. Answers to the brief, and what remains

**The recursion established.** Two exact forms, both on every subspace domain. Sets: $\Lambda^\ast_N(k, T) \le B^{\mathrm{set}}_N(k, T; A) + (n - 1)\Lambda^\ast_{N-1}(\lceil k/2\rceil, A)$ (Corollary 1.2). Differences: $\Lambda_{N,j}(\kappa, \Delta) \le 2 + B^{\mathrm{diff}}_{N,j} + (2^{N-j} - 1)\Lambda_{N,j+1}(\lfloor\kappa/2\rfloor, \Delta)$ for the $U$-problems, with the slack $\Delta = T - k + 1$ preserved and base case $n/\Delta$ (Corollary 3.4, Lemma 3.2).

**The dichotomy.** For sets it is not false but vacuous: Corollary 2.2 shows that bounding the non-invariant members at agreement $\tau'$ with tolerance $\eta$ is the same as bounding all lists at $\tau'(1 + 4\eta)$. For differences the dichotomy (hypothesis DP) is open. It is proved only in the density form, with full-size periods, within $10^{-5}$ of the Johnson radius on a generic subspace (Theorem 5.1), and it follows from Conjecture P above $2n/3$ at rate 1/2 (note 17).

**Bounds $2^{\mathrm{poly}(N)}$.** Unconditional: Theorem 5.1 only (formal model, the table of section 5). Conditional on DP$(B)$: $2^{NJ - J(J-1)/2}(J(B + 2) + n/(T - k + 1))$ on every subspace domain, in every window (Theorem 3.5).

**Tool 1 of the brief (additive combinatorics on the agreement sets).** Remark 1.4: intersection sizes alone cannot work, and the average direction lands below the rate. The place where sumset arguments do work is on the fibres of one $\xi$ (Theorem 4.3, Steps 2 and 3), not on the agreement sets.

**Tool 2 (weak descent).** Remark 1.3 and Proposition 2.3: the exact object is the original problem, and a descent that drops partial fibres dies after $\log_2(1/\lambda)$ steps on a perturbed word.

**Tool 3 (forbidden configurations and Ramsey).** The proved prohibitions (no additive quadruple above $(n + 3d)/4$, no affine family of size $2^j$ above $d + (n - d)/2^j$) concern $\mathbb{F}_2$-linear relations among the codewords, and a set of $L$ elements of the $\mathbb{F}_2$-space of polynomials can be linearly independent whatever $L$ is, as trivial lists are. No supersaturation statement forces such relations before structure is proved, so there is nothing to extract. **[proved, trivial]**

**Tool 4 (which steps hold on every domain).** Sections 1, 2, 3 entirely. In section 4 only Lemma 4.1 needs the formal model.

**What remains.**

1. DP, or its bounded-index form: for $\tau$ in a window there is $N_0(\tau)$ such that in dimension $N > N_0$ every list larger than $2^{\mathrm{poly}(N)}$ has a pair with a positive (or inverse polynomial) fraction of periodic thirds. The cheapest test is the scaling of the period-free part of the $19n/32$ list from $n = 32$ to $n = 64$, which needs a structured enumeration (the oracle is out of reach at $n = 64$).
2. A transfer lemma on the real domain. Lemma 4.1 is the only formal-model step in Theorem 4.3 and Theorem 5.1, and it is a statement about reductions of three coprime polynomials modulo the points of $D$.
3. Widening Theorem 5.1 is possible by constants only (a second-moment bound in place of Markov, the exact Step 1), and not to the windows.
4. Theorem 4.3 is a new case of Conjecture P ($s < \delta^2/4n$). The regime that note 17 Theorem 5.1 needs has $s$ up to $0.4n$, and there the count of Step 1 gives no transfer direction at all ($r_ir_j < s_ln$).

## 8. Reproduction

Under `doc/whir_soundness_gap_notes/scripts/`.

- `37_transfer_check.py [seed]`: `python3 37_transfer_check.py 1`, 2 seconds. Lemma 4.1, Lemma 4.2 and the ratio $s\,n/\delta^2$ on 196 functions with $n \le 64$, with a control on random sets.
- `37_gap_inequality.py`: `python3 37_gap_inequality.py`, 1 second. Part 1 is the exhaustive check of the counting step of Theorem 4.3, part 2 the numbers of Theorem 5.1.
- `37_profile.c`: `cc -O2 -o 37_profile 37_profile.c` (uses `02_gf.h`), `./37_profile N k T seed word [args] [pert m]`, with `NPAIRS` and `STABMIN` in the environment. The rows of section 6: `5 8 15 1 pow 15`, `5 8 13 1 pow 15 pert 2`, `NPAIRS=2000 ... 4 9 10 1 xl 1 8`, `NPAIRS=2000 ... 5 17 20 1 xl 2 16` (one minute), `STABMIN=4 NPAIRS=200 ... 5 17 19 1 xl 2 16` and `NPAIRS=3000 ... 5 17 19 1 xl 2 16` (two minutes each), `5 17 19 1 xl 2 16 pert 1` (two minutes).

## References

Notes 02, 04 (Theorem 1.2), 05, 17 (Theorems 2.1 and 5.1, Propositions 3.4 and 3.5), 18, 25, 26 (Lemma 1.2, Theorem A, Corollary 2.1, section 2.4), 27 of this directory. No external source was used.
