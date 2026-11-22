# 04. List-size upper bounds beyond the Johnson radius

Researcher 04 (proof side). Every statement is tagged **[proved]** (proof in this note), **[checked]** (numerically, sizes stated) or **[conjectured]**. Scripts are `scripts/04_*`, section 7 says how to run them.

Notation. $F$ is any field of characteristic two and $D \subset F$ an $\mathbb{F}_2$-subspace of dimension $N$, $n = 2^N$. For leanVM, $D = D_{\kappa,R} \subset K = \mathrm{GF}(2^{64})$ and $F$ is $K$, $E$ or a power of $E$ (interleaving). Codewords are polynomials of degree $< k$ (so $k = \rho n$ for genuine codewords and $k = \rho n + \ell$ for the analysis degree $d = k - 1$). $T$ is an agreement count and $m := T - k$. For $S \subseteq D$, $Z_S = \prod_{s \in S}(X - s) = \sum_j e_j(S) X^{|S| - j}$, and for a linear functional $\varphi : D \to \mathbb{F}_2$, $n_\varphi(S) = |\{s \in S : \varphi(s) = 1\}|$. A *list* is a polynomial $w$ (any polynomial that restricts to the word on the agreement sets), distinct $c_1, \dots, c_L$ of degree $< k$ and sets $S_i \subseteq D$ with $w = c_i$ on $S_i$, $|S_i| \ge T$. Its *phantom degree* is $r := \deg w - T$. A *strict common top* is a list with $r = 0$: then $w - c_i = \lambda Z_{S_i}$ and all $Z_{S_i}$ share $e_1, \dots, e_m$. In general $w - c_i = Z_{S_i} g_i$ with $\deg g_i = r$, and the roots of $g_i$ are the phantom roots (in $D$, where they give locators with multiplicities, or anywhere else).

## 0. Summary

**The honest headline.** I have no unconditional bound of the form $\Lambda(T) \le 2^b$ below the Johnson threshold on the real domain $D_{\kappa,R} \subset K$, for all words, at any rate. What I have is (a) three small results that do hold on the real domain for all words, (b) a method (specialization at a place) that proves list bounds beyond Johnson on *generic* subspace domains, including for words that are not locators, and (c) a precise account of why (b) cannot be transferred to a 64-bit field by any argument I can see, with numbers.

Notes 02 (Theorem W, Proposition 6) and 05 (Lemma 6.2, Theorem 6.3) contain the rigidity of strict common tops in the formal model. I found the same statement independently by a different proof and with an independent exhaustive check (sections 2.4 and 2.7), so that result now has three derivations. I do not claim it. What this note adds to it is marked "new" below.

| | statement | where it holds | status |
| --- | --- | --- | --- |
| 1.1 | Lists over $E$ or interleaved codes are lists over $K$, up to size $2^{32}$ | real domain, all words | proved |
| 1.2 | A list inside an $r$-dimensional affine space of codewords has at most $\prod_{i \le r} \frac{n-k+i}{T-k+i}$ members, for every $T \ge k$ | any MDS code, all words | proved, tight |
| 1.3 | Pinning extends the Johnson bound by $O(b)$ agreement points for a budget $2^b$, no more | any MDS code, all words | proved (a negative result) |
| 2.3 | New. Specialization dichotomy: for every subspace $W \le D$, two list members have $\sum_C \min(|S_i \cap C|, |S_j \cap C|) \le k - 1$ or $\sum_C \max(\cdot,\cdot) \le \deg w$, the sums over the cosets of $W$ | generic domains, all words | proved |
| 2.4 | New. With phantom degree $r$: $n_\varphi(S_i) - n_\varphi(S_j) \bmod 2^{a+1}$ lies in $[-r, r]$ for every functional $\varphi$ ($2^a \le m$, $m + r < 2^{a+1}$) | generic domains, all words | proved, checked $n = 16$ |
| 2.5 | $r = 0$: the congruence of 02 and 05, then $\le 1/(2\tau - 1)^2$ members for $n/8 \le m$ | generic domains, strict common tops | proved (third derivation), checked exhaustively at $n = 16, 32$ |
| 2.6 | New. The same rigidity survives up to about $(\tau - \frac12)\sqrt{n/2}$ phantom roots placed anywhere: any two members differ on $n/2 \pm 4r(r+1)$ points and $L \le \frac{n/4}{(T - n/2)^2/n - 2r(r+1)}$ | generic domains, $n/8 \le m$, $m + r < n/4$ | proved |
| 2.7 | New. At every gap: $L \le (2n-1)^{\nu}$ with $\nu \le n\min(T, n - T)/(2m^2)$, polynomial in $n$ for every fixed $\tau - \rho > 0$ | generic domains, strict common tops | proved (crude exponent) |
| 3.1 | New. On the real domain at $N = 25$ the binary code that contains all differences $1_S + 1_{S'}$ of a common-top class has dimension $\ge 243198$ at $m = n/8$, against $326$ on a generic domain | real domain | proved, bound validated on analogues |
| 3.3 | New. On the real shape at $n = 32$, $93\%$ of the common-top pairs at rate 1/2 and $T = 5n/8$ are not formal, yet the largest class is 13 (formal: 7) | real shape, $n = 16, 32$ | checked |

**Conjectured.** Conjecture C (section 5): on $D_{\kappa,R} \subset K$ at level-0 sizes, the lists in the open windows are the formal ones plus what a 64-bit pigeonhole on a structured family gives, which is nothing at rate 1/2 above $5n/8$. Evidence: the formal theorems, the accounting of section 3.4, toy sizes. Counter-evidence to keep in mind: at toy sizes the real shape exceeds the formal bounds by small factors (9 against 7.1), and at rate 1/4 the Gold prediction of note 01 (about $2^{30}$ members at $3n/8$, not formal) shows that a 64-bit field is small enough for non-formal families of quadric type at $N = 25$.

**Dead** (section 4): arguments that use only pairwise or higher intersections, pinning, Guruswami-Sudan with linearized $Y$-monomials, folded-code interpolation along translations, recursion through $D \to L_a(D)$, character theory over $K$, $S$-unit bounds, incidence bounds, a first-moment bound over random domains.

**What it means for the query counts.** Nothing proved moves a threshold. If Conjecture C (or C1, C2 of note 02) is accepted as an assumption, the thresholds become the dyadic ones: about $5n/8$ at rate 1/2 ($t \approx 160$ to $168$ instead of 218), $n/4$ at rate 1/8 ($t \approx 54$ to $57$ instead of 73), $n/8$ to $3n/16$ at rate 1/16 ($t \approx 36$ to $45$ instead of 55), with list budgets of about $2^{31}$ at the dyadic points themselves. Rate 1/4 stays closed.

## 1. Results that hold on the real domain, for all words

### 1.1 Extension fields and interleaving

**Proposition 1.1. [proved]** Let $F \supseteq K$ be a finite extension (or $F = K^h$ with coordinatewise operations, the $h$-interleaved code), $D \subset K$. If some word over $F$ has $L$ list members at agreement $T$ with $\binom{L}{2} < |K|$, then some word over $K$ has $L$ list members with the same agreement sets. Hence $\Lambda_F(T) \le \Lambda_K(T)$ whenever $\Lambda_K(T) < 2^{32}$.

*Proof.* For a $K$-linear $\lambda : F \to K$ apply $\lambda$ to the values of $w$ and to the coefficients of the $c_i$. Since $D \subset K$, $\lambda(c_i(x)) = (\lambda c_i)(x)$ on $D$, so $\lambda c_i$ agrees with $\lambda \circ w$ on $S_i$ and has degree $< k$. For $i \ne j$ pick a nonzero coefficient $\gamma_{ij}$ of $c_i - c_j$. The $\lambda$ with $\lambda(\gamma_{ij}) = 0$ are a fraction $1/|K|$ of all $\lambda$, so some $\lambda$ keeps all $\binom{L}{2}$ differences nonzero. For the last claim take a sublist of size $\Lambda_K(T) + 1$. $\square$

So list bounds below $2^{32}$ only need to be proved over $K$. (Above $2^{32}$ the statement is open, and does not matter for budgets of $2^{30}$.)

### 1.2 Lists inside a low-dimensional space of codewords

**Theorem 1.2. [proved]** Let $C$ be an MDS code of length $n$ and dimension $k$ (any evaluation domain), $H \subseteq C$ an affine subspace of dimension $r$, $w$ any word and $T \ge k$. Then
$$\#\{h \in H : |\{x : h(x) = w(x)\}| \ge T\} \ \le\ \prod_{i=1}^{r} \frac{n - k + i}{T - k + i} \ \le\ \Bigl(\frac{n-k}{T-k}\Bigr)^{r} \quad (\text{the last for } T > k).$$

*Proof.* Induction on $r$, the case $r = 0$ being trivial. Let $H = c_0 + H_0$ and $Z$ the set of common zeros of $H_0$. The codewords vanishing on $Z$ form a subcode of dimension $k - |Z|$, so $z := |Z| \le k - r$. For $x \notin Z$ the set $H_x = \{h \in H : h(x) = w(x)\}$ is empty or an affine subspace of dimension $r - 1$. A list member agrees with $w$ on at least $T - z$ points outside $Z$, so it lies in at least $T - z$ of the $H_x$. With $f(r)$ the maximum of the left side, $L (T - z) \le (n - z) f(r - 1)$, and $(n - z)/(T - z)$ increases with $z \le k - r$. $\square$

Remarks. (i) The bound holds at every agreement above $k$, far beyond Johnson, and it is attained: for $H = C$ and $T = k$ it is $\binom{n}{k}$, and for the coset-union family of the main document ($H = F[L_W]_{\le M\rho}$, zero sets are unions of cosets, so $z$ moves in steps of $|W|$) the same induction gives exactly $\binom{M}{m}$. (ii) Read backwards: a list of size $L$ at agreement $T$ spans an affine space of dimension at least $\log L / \log\frac{n-k}{T-k}$. The $2^{30.8}$ family at rate 1/2 and $5n/8$ must span dimension $\ge 16$. (iii) It does not give a list bound by itself, because lists inside the Johnson radius can already have dimension comparable to their size, and a list beyond Johnson contains them. It would give one from any statement of the form "the list is covered by $J$ affine spaces of dimension $r$" ($L \le J ((n-k)/(T-k))^r$), which is how folded Reed-Solomon proofs conclude. I found no such covering statement for subspace domains (section 4, items 3 and 4). (iv) Example of a subcode where it settles the question: codewords supported on $r$ fixed exponents, for instance the $\kappa + 1$ exponents $2^i - 1$ that carry all flats, have lists of size at most $((1-\rho)/(\tau-\rho))^r$ at every $\tau > \rho$, polynomial in $n$ for $r = O(\log n)$.

### 1.3 Pinning: Johnson plus $O(b)$ points

**Proposition 1.3. [proved]** Let $C$ be MDS of length $n$, dimension $k$, and $\Delta := n(k-1) - T^2 \ge 0$ (at or beyond Johnson), $T < (n + k - 1)/2$. With $j := \lfloor \Delta/(n + k - 1 - 2T) \rfloor + 1$,
$$\Lambda(T) \ \le\ \frac{\binom{n}{j}}{\binom{T}{j}}\,(n - j)(T - k + 1) \ \le\ \Bigl(\frac{n - j + 1}{T - j + 1}\Bigr)^{j}\, n^2 .$$

*Proof.* For a $j$-set $J$ let $\mathcal{L}_J$ be the members whose agreement set contains $J$. They agree on $J$, so $c_i = c_0 + Z_J h_i$ with $\deg h_i < k - j$, and the $h_i$ form a list of the MDS code of length $n - j$ and dimension $k - j$ on $D \setminus J$ at agreement $T - j$. Its Johnson denominator is $(T - j)^2 - (n - j)(k - 1 - j) = j(n + k - 1 - 2T) - \Delta \ge 1$ by the choice of $j$, so $|\mathcal{L}_J| \le (n - j)(T - k + 1)$. Double counting, $L \binom{T}{j} \le \sum_J |\mathcal{L}_J|$. $\square$

For a budget $2^b$ this allows $j \approx (b - 2N)/\log_2(n/T)$, that is $\Delta \lesssim j (n + k - 2T)$, that is $T \ge \sqrt{nk} - O(b)$. At rate 1/2 with $b = 80$ it is fewer than 4 points below Johnson. Each pinned point costs a factor $n/T$ and buys $n + k - 2T$ in a deficit that is quadratic in $n$. This is the precise sense in which elementary counting stops at Johnson, and [Jo26] (quoted in note 01) is the same phenomenon for MCA.

### 1.4 Two reductions that I used and that others state

Complement duality for strict common tops ($S \mapsto D \setminus S$ maps $(k, T)$ to $(n + k - 2T, n - T)$) is Proposition 1.3 of note 05 and Lemma 2 of note 02. I found it independently and `04_loc16.py` shows the symmetry on the exact table for $n = 16$. **[proved]** there. If every agreement set is a union of cosets of one subspace $W$ of index $M$, the list is a list of the $|W|$-interleaved code of length $M$ on $L_W(D)$ and has at most $\binom{M}{\kappa_M}/\binom{T'}{\kappa_M}$ members, $\kappa_M = \lceil kM/n \rceil$, $T' = \lceil TM/n \rceil$ (any $\kappa_M$ cosets determine the codeword). **[proved]** So the coset-union family is the whole list of its kind, and such lists are bounded independently of $n$.

## 2. Generic domains: specialization at a place

### 2.1 The setting

Call $D \subset F$ **generic** if it has a basis $b_1, \dots, b_N$ that is algebraically independent over $\mathbb{F}_2$ (then every basis is). This is the formal model of notes 02 and 05 realized in a field: a list on a generic domain is a list "for formal reasons", and all the known families (flats, trees, glued coset unions, padded hyperplanes) exist on generic domains. A finite field contains no generic domain. Section 3 is about that.

**Lemma 2.1 (places). [proved]** Let $D \subset F$ be generic and $W \le D$ a subspace. There is a valuation $v$ on $F$, with valuation ring $O$ and residue field $\kappa$, such that $D \subset O$ and the residue map $D \to \kappa$ is $\mathbb{F}_2$-linear with kernel exactly $W$. Its image $\bar D \cong D/W$ is an $\mathbb{F}_2$-subspace of $\kappa$ of dimension $N - \dim W$.

*Proof.* Take a basis $b'_1, \dots, b'_N$ of $D$ whose last $\dim W$ elements span $W$. On $\mathbb{F}_2[b']$ let $v(P)$ be the least total degree in the variables $b'_i \in W$ of a monomial of $P$. This is the order of vanishing along a prime ideal with polynomial graded ring, so it is a discrete valuation on $\mathbb{F}_2(b')$, with residue field containing $\mathbb{F}_2(b'_i : b'_i \notin W)$. An element of $D \setminus W$ has value 0 and residue its component on the $b'_i \notin W$, an element of $W \setminus 0$ has value 1. Extend $v$ to $F$ (Chevalley). $\square$

I use the Gauss extension $v(\sum a_i X^i) = \min v(a_i)$ on $F[X]$, which is multiplicative, and the reduction $\mathrm{red} : O[X] \to \kappa[X]$, a ring homomorphism with $\mathrm{red}(f) \ne 0$ iff $v(f) = 0$. For $S \subseteq D$, $Z_S$ is monic in $O[X]$ and $\mathrm{red}(Z_S) = \prod_{C \in D/W} (X - z_C)^{|S \cap C|}$, where $z_C \in \bar D$ is the residue of the coset $C$.

### 2.2 The specialization lemma

**Lemma 2.2. [proved]** Let $D$ be generic, $W \le D$, and $v$ as in Lemma 2.1. Let $(w; c_i; S_i)$ be a list with at least two members and $|S_i| \ge k$. Then there are $\lambda \in F^\ast$ and nonzero $P_i \in \kappa[X]$ such that (a) $\prod_C (X - z_C)^{|S_i \cap C|}$ divides $P_i$ and $\deg P_i \le \deg w$, (b) $\deg(P_i - P_j) < k$ for all $i, j$.

*Proof.* Let $W_{\mathrm{top}}$ be the part of $w$ in degrees $\ge k$. It is nonzero: if $w$ had degree $< k$ it would be a codeword agreeing with every $c_i$ on $\ge k$ points, and the members would not be distinct. In particular $w - c_i \ne 0$. Write $w - c_i = Z_{S_i} g_i$. I claim $v(w - c_i) = v(W_{\mathrm{top}})$. The Gauss value is a minimum over coefficients, so $v(w - c_i) \le v(W_{\mathrm{top}})$. If it were smaller, scale by $\mu$ with $v(\mu) = -v(w - c_i)$: then $\mathrm{red}(\mu(w - c_i))$ is nonzero of degree $< k$, but it equals $\mathrm{red}(Z_{S_i})\,\mathrm{red}(\mu g_i)$, of degree $\ge |S_i| \ge k$. Now take $\lambda$ with $v(\lambda) = -v(W_{\mathrm{top}})$ and $P_i = \mathrm{red}(\lambda(w - c_i)) = \mathrm{red}(Z_{S_i})\,\mathrm{red}(\lambda g_i)$. (a) is clear, and $P_i - P_j = \mathrm{red}(\lambda(c_j - c_i))$ has degree $< k$. $\square$

In words: a list on a generic domain specializes, for every $W$, to a list of the *multiplicity* code on the generic domain $D/W$ (polynomials of degree $< k$, agreement of order $|S_i \cap C|$ at the point $z_C$), except that distinct members may collapse to the same $P$. This is the upper-bound counterpart of the lifting lemma (Lemma 3 of note 02), which goes from $L_W(D)$ up to $D$.

**Theorem 2.3 (dichotomy for every $W$). [proved]** Let $D$ be generic and $(w; c_i; S_i)$ a list. For every subspace $W \le D$ and all $i \ne j$, with sums over the cosets $C$ of $W$:
$$\sum_C \min(|S_i \cap C|, |S_j \cap C|) \le k - 1 \qquad\text{or}\qquad \sum_C \max(|S_i \cap C|, |S_j \cap C|) \le \deg w .$$
If $|S_i| = |S_j| = T$ and $f = 1_{S_i} - 1_{S_j}$, this says that $\delta_W := \frac12 \sum_C |\sum_{x \in C} f(x)|$ is never in the interval $(r, m]$: it is at most $r = \deg w - T$ or at least $m + 1$.

*Proof.* If $P_i \ne P_j$, the nonzero polynomial $P_i - P_j$ of degree $< k$ is divisible by $\prod_C (X - z_C)^{\min}$. If $P_i = P_j$, it is divisible by $\prod_C (X - z_C)^{\max}$ and has degree $\le \deg w$. For the last sentence, $\sum_C \min = T - \delta_W$ and $\sum_C \max = T + \delta_W$. $\square$

For $W = 0$ this is the usual $|S_i \cap S_j| \le k - 1$. For general words ($\deg w$ close to $n$) the second alternative is almost always available and the theorem says little. It has content when $r < m$, that is $\deg w < 2T - k$.

### 2.3 Hyperplanes: congruences with phantom roots

**Theorem 2.4. [proved]** Let $D$ be generic, $(w; c_1, c_2; S_1, S_2)$ a list with $|S_1| = |S_2| = T \ge k$, $m = T - k$, $r = \deg w - T$, $\varphi$ a nonzero functional and $d = n_\varphi(S_1) - n_\varphi(S_2)$.

1. $|d| \le r$ or $|d| \ge m + 1$.
2. If $2^a \le m$ and $m + r < 2^{a+1}$, then $d \bmod 2^{a+1} \in [-r, r]$.
3. For every power of two $A \le m + 1$, $d \bmod A \in [-r, r]$.

For $r = 0$, part 2 with $a = \lfloor \log_2 m \rfloor$ is $n_\varphi(S_1) \equiv n_\varphi(S_2) \pmod{2^{a+1}}$.

*Proof.* Apply Lemma 2.2 with $W = \ker\varphi$. There are two cosets, with residues $0$ and $y \ne 0$, so $P_i = X^{T - n_i}(X - y)^{n_i} G_i$ with $n_i = n_\varphi(S_i)$. By (b) and $T \ge k$ the $P_i$ have the same degree $T + r'$, $0 \le r' \le r$, so $\deg G_1 = \deg G_2 = r'$. Part 1 is Theorem 2.3. For the rest let $d \ge 0$ (the statement is symmetric). Dividing $P_1 - P_2$ by $X^{T - n_1}(X - y)^{n_2}$, the polynomial $(X - y)^d G_1 - X^d G_2$ has degree $< d - m$. Put $t = 1/X$ and $\Gamma_i(t) = t^{r'} G_i(1/t)$, a polynomial of degree $\le r'$ with $\Gamma_i(0) \ne 0$. Then
$$(1 - yt)^d\, \Gamma_1(t) \equiv \Gamma_2(t) \pmod{t^{m + r' + 1}} .$$
Let $A = 2^{a+1}$ be as in part 2, so $m + r' + 1 \le A \le 2m$, and write $d = d_0 + A d_1$, $0 \le d_0 < A$. In characteristic two $(1 - yt)^{A d_1} = (1 - (yt)^A)^{d_1} \equiv 1 \pmod{t^A}$, so $(1 - yt)^{d_0}\Gamma_1 \equiv \Gamma_2 \pmod{t^{m + r' + 1}}$. If $d_0 \le m$, both sides are polynomials of degree $\le m + r'$, so they are equal, and comparing degrees $d_0 \le r'$. If $d_0 > m$, multiply by $(1 - yt)^{A - d_0}$: $\Gamma_1 \equiv (1 - yt)^{A - d_0}\Gamma_2$ with $A - d_0 \le A - m - 1 \le m - 1$, so again equality and $A - d_0 \le r'$. Hence $d \bmod A \in [-r', r']$. Part 3 is the same computation modulo $t^A$ with $A \le m + 1 \le m + r' + 1$: either $d_0 + r' < A$ and equality gives $d_0 \le r'$, or $d_0 \ge A - r'$. $\square$

**[checked]** `04_phantom16.py`: for $n = 16$ on a random domain in $\mathrm{GF}(2^{64})$ it finds all pairs of $T$-sets joined by one phantom root $z \in K$ (solving for $z$, which is in $D$ or not), for $(T, k) = (12, 10), (12, 9), (13, 11), (13, 10), (4, 2), (4, 1), (5, 3)$: 90720, 43680, 14280, 10920, 90720, 43680 and 397320 pairs, against 210, 210, 0, 0, 210, 210, 1680 strict pairs. Every one of them satisfies $|d \bmod 4| \le 1$ for all 15 functionals. So phantom roots create many more pairs than strict tops do, and they all obey the theorem.

### 2.4 Strict common tops: the known rigidity, a third time

**Corollary 2.5. [proved]** (Theorem W converse and Proposition 6 of note 02, Lemma 6.2 and Theorem 6.3 of note 05.) On a generic domain let $S \ne S'$ be $T$-sets sharing $e_1, \dots, e_m$, $2^a \le m$, and $f = 1_S - 1_{S'}$. Then $\hat f(\varphi) = \sum_x f(x)(-1)^{\varphi(x)} \in 2^{a+2}\mathbb{Z}$ for all $\varphi$ and $|S \triangle S'| = \frac1n \sum_\varphi \hat f(\varphi)^2$. If $n/8 \le m$ and $T \ne n/2$, then $S \triangle S'$ is an affine hyperplane cut by $S$ and $S'$ into the two cosets of a subspace of codimension 2, $|S \cap S'| = T - n/4$, and a class has at most $n^2/(4(T - n/2)^2) = 1/(2\tau - 1)^2$ members.

*Proof.* Theorem 2.4 with $r = 0$ gives the congruence, $\hat f(\varphi) = -2d$ and Parseval the rest. For $n/8 \le m$: $\hat f(\varphi) = \frac n2 c_\varphi$, $f = \frac12 \sum c_\varphi \chi_\varphi$ is integer valued so $\sum c_\varphi$ is even, $|S \triangle S'| = \frac n4 \sum c_\varphi^2 < n$, so exactly two $c_\varphi = \pm 1$. The count is the Johnson computation with all pairwise intersections equal to $T - n/4$: $L\,T^2/n \le T + (L-1)(T - n/4)$. $\square$

Notes 02 and 05 have sharper constants in the windows (at most 4 members above $5n/8$ at rate 1/2, 7 at $5n/8$). The proof here is different: theirs lifts to characteristic zero or extracts a pure-power coefficient, this one reduces at a place. The place version shows what is actually used: one valuation for each functional. It is also what extends to phantom roots.

### 2.5 New: the rigidity is stable under few phantom roots

**Theorem 2.6. [proved]** Let $D$ be generic and $(w; c_i; S_i)_{i \le L}$ a list with $|S_i| = T$, $T \ge 5n/8$ or $T \le 3n/8$, $m = T - k \ge n/8$, phantom degree $r = \deg w - T$ with $m + r < n/4$ and $r \le \sqrt n/4 - 1$. Then for all $i \ne j$
$$\bigl|\,|S_i \triangle S_j| - n/2\,\bigr| \le 4r(r+1), \qquad\text{and}\qquad L \le \frac{n/4 - 2r(r+1)}{(T - n/2)^2/n - 2r(r+1)}$$
whenever the denominator is positive, that is $r(r+1) < (\tau - \frac12)^2 n/2$.

*Proof.* Fix $i \ne j$, $f = 1_{S_i} - 1_{S_j}$, $d_\varphi = n_\varphi(S_i) - n_\varphi(S_j)$, so $\hat f(\varphi) = -2 d_\varphi$. By Theorem 2.4 part 2 with $2^{a+1} = n/4$, $d_\varphi = \frac n4 c_\varphi + \eta_\varphi$ with $c_\varphi \in \mathbb{Z}$, $|\eta_\varphi| \le r$. Let $\nu = \sum_\varphi c_\varphi^2$. Parseval gives $|S_i \triangle S_j| = \frac4n \sum d_\varphi^2 = \frac n4 \nu + 2\sum c_\varphi \eta_\varphi + \frac4n \sum \eta_\varphi^2$, so $\bigl||S_i \triangle S_j| - \frac n4 \nu\bigr| \le 2r\nu + 4r^2$. Write $f = F + E$ with $F = -\frac12 \sum c_\varphi \chi_\varphi$ and $\sum_x E(x)^2 = \frac4n \sum \eta_\varphi^2 \le 4r^2 < n/4$. If $\sum c_\varphi$ were odd, $F$ would be a half-integer everywhere and $|E| \ge \frac12$ everywhere, so $\sum E^2 \ge n/4$. Hence $\nu \equiv \sum c_\varphi$ is even. $\nu = 0$ gives $|S_i \triangle S_j| \le 4r^2 < n/4 \le 2m$, impossible since $|S_i \cap S_j| \le k - 1$. $\nu \ge 4$ gives $|S_i \triangle S_j| \ge n - 8r - 4r^2 > 3n/4 \ge 2\min(T, n - T)$, impossible. So $\nu = 2$, which is the first claim, and $|S_i \cap S_j| \le T - n/4 + 2r(r+1)$. The second claim is the Johnson computation with this intersection bound. $\square$

At $N = 25$ and $\tau = 0.65$ this tolerates $r \le 600$ phantom roots, with $L \le 14$ for $r \le 300$. It does not reach the padded hyperplanes of note 01, which have $r \approx n/8$ phantom roots (all in $D$). So it answers a small part of "general words unknown" in notes 02 and 05: phantom roots outside $D$ are no better than phantom roots inside $D$ as far as these congruences go, and a number of them below about $\sqrt n$ changes nothing.

### 2.6 New: a polynomial bound at every gap

**Theorem 2.7. [proved]** On a generic domain, a family of $T$-sets sharing $e_1, \dots, e_m$, $a = \lfloor \log_2 m \rfloor$, has at most $(2n - 1)^{\nu}$ members, where
$$\nu = \Bigl\lfloor \frac{2n \min(T, n - T)}{4^{a+2}} \Bigr\rfloor \ <\ \frac{n \min(T, n - T)}{2m^2} = \frac{\min(\tau, 1 - \tau)}{2(\tau - \rho)^2} .$$

*Proof.* Fix a member $S_1$. Another member $S$ is determined by $f = 1_S - 1_{S_1}$, hence by the integers $c_\varphi = \hat f(\varphi)/2^{a+2}$ (Corollary 2.5), and $\sum c_\varphi^2 = n |S \triangle S_1|/4^{a+2} \le \nu$. A vector with $\sum |c_\varphi| \le \nu$ is a sum of $\nu$ terms from $\{0, \pm e_\varphi\}$, $\varphi \ne 0$. $\square$

So strict common tops on generic domains are polynomially bounded at every constant distance from capacity. The exponent is crude. At rate 1/2 for $9n/16 \le T < 5n/8$ it is between 12 and 14, while the largest known family there has $56n - 392$ members (notes 02 and 05) at the upper end and about $n^4$ at the lower end. The proof shows that every difference $f$ is a function of at most $\nu$ linear functionals, so the true exponent is governed by a finite classification (section 6, item 2).

### 2.7 Checks of section 2

**[checked]** `04_universal16.py`: $n = 16$, random domain in $\mathrm{GF}(2^{64})$ on which the 35 monomials of degree 4 are verified independent. For all 77 pairs $(T, m)$ with $m \le 7$ every class satisfies the congruence of Corollary 2.5, and for $m \in \{2, 3\}$, $T \ne 8$ every difference is an affine hyperplane and every class is within $1/(2\tau - 1)^2$.

**[checked]** `04_universal32.c`: $n = 32$, all $T$-subsets, keyed on $(e_1, \dots, e_m)$ in two independent random embeddings into $\mathrm{GF}(2^{64})$ at once (128 bits, enough for the 70 monomials of degree 4). By complement duality $(k, T) = (8, 12), (6, 11), (4, 10)$ are rate 1/2 at $T = 20, 21, 22$.

| $(T, m)$ | dual rate-1/2 agreement | classes with $\ge 2$ members | largest | bound $1/(2\tau-1)^2$ | congruence failures | non-hyperplane differences |
| --- | --- | --- | --- | --- | --- | --- |
| $(12, 3)$ | 20, degree $\le n/2$ | 1038438 | 1400 (155 classes) | none (modulus 4) | 0 of $3.6 \cdot 10^{10}$ pairs | not applicable |
| $(12, 4)$ | 20 | 1598360 | 7 | 16 | 0 of 1692600 | 0 |
| $(11, 5)$ | 21 | 451360 | 3 | 10.2 | 0 of 520800 | 0 |
| $(10, 6)$ | 22 | 76880 | 3 | 7.1 | 0 of 111600 | 0 |

The 1400 is the class of notes 02 and 05 ($56n - 392$). A second seed gives the same line for $(12, 4)$.

## 3. Why this does not transfer to the real domain

### 3.1 What the proofs need and what $K$ has

Section 2 needs, for each functional $\varphi$, a place of the field whose residue map kills exactly $\ker\varphi$. A finite field has no places. Equivalently (notes 02 and 05) one needs the monomials of degree up to $2^a \approx n/8$ in a basis of $D$ to be $\mathbb{F}_2$-independent, and $K$ has dimension 64. On the real shape the situation is worse than for a random subspace at small degree: $D \cdot D = \mathrm{span}(1, \dots, x^{2N-2})$ has dimension $2N - 1$ instead of $\binom{N+1}{2}$.

What survives rigorously on $D = \mathrm{span}(1, \dots, x^{N-1})$: for $j(N - 1) < 64$ the value $e_j(S)$ is a polynomial in $x$ of degree $\le j(N-1)$ and equality in $K$ is equality in $\mathbb{F}_2[x]$, where the three places $x = 0$, $x = 1$, $x = \infty$ exist. So for the three functionals "coefficient of $1$", "sum of the coefficients" and "coefficient of $x^{N-1}$" the congruences of Theorem 2.4 hold for the equalities among $e_1, \dots, e_{\lfloor 63/(N-1) \rfloor}$. **[proved]** At $N = 25$ that is $e_1, e_2$ only (a congruence modulo 4 for three functionals). It is useless, and I record it only to show how little a 64-bit field certifies.

### 3.2 The linear part of the obstruction, with numbers

Two members of a common-top class share $e_1, \dots, e_m$, hence the power sums $p_j = \sum_{s} s^j$, $j \le m$ (Newton). So $1_S + 1_{S'}$ lies in the binary code
$$B_m = \Bigl\{ v \in \mathbb{F}_2^D : \sum_{x} v_x x^j = 0 \ \text{for } 0 \le j \le m \Bigr\},$$
a binary alternant code. This is the $\mathbb{F}_2$-linear shadow of the class structure.

**Proposition 3.1. [proved]** Let $v_0$ be such that $2^{v_0 - 1} \le m + 1 < 2^{v_0}$. (i) Always $B_m \supseteq \mathrm{RM}(N - v_0, N)$, with equality on a generic domain. (ii) If $[F : \mathbb{F}_2] = e$ is finite, then for every $w_0$
$$\dim B_m \ \ge\ \sum_{w > w_0} \binom{N}{w} \ -\ e \cdot \#\{\, j \le m \text{ odd} : \mathrm{wt}_2(j) > w_0 \,\} .$$

*Proof.* With $x = \sum_i x_i b_i$ ($x_i \in \mathbb{F}_2$), $x^j = \prod_{t \in \mathrm{bits}(j)} \sum_i x_i b_i^{2^t}$, so $\sum_x v_x x^j = \sum_\gamma \mu_\gamma\, b^\gamma \sum_x v_x \prod_{i \in \mathrm{supp}\,\gamma} x_i$, the sum over exponent vectors $\gamma$ of total degree $j$, where $\mu_\gamma$ is the multinomial coefficient modulo 2. It is odd exactly when the binary digits of the $\gamma_i$ partition those of $j$, so only supports of size $\le \mathrm{wt}_2(j)$ occur, and every support of size between 1 and $\mathrm{wt}_2(j)$ does occur. The largest $\mathrm{wt}_2(j)$ for $j \le m$ is $v_0 - 1$. So a $v$ orthogonal to all monomials of degree $\le v_0 - 1$ in the bits, that is $v \in \mathrm{RM}(v_0 - 1, N)^\perp = \mathrm{RM}(N - v_0, N)$, is in $B_m$, and on a generic domain, where the $b^\gamma$ are independent, nothing else is. For (ii), $B_m$ is the orthogonal of $\mathcal{T}_m = \{x \mapsto \mathrm{Tr}(P(x)) : \deg P \le m\}$. Since $\mathrm{Tr}(c\,x^{2j}) = \mathrm{Tr}(\sqrt c\, x^j)$, only odd $j$ and the constants matter. Each odd $j$ contributes a space of dimension $\le e$, and those with $\mathrm{wt}_2(j) \le w_0$ lie in $\mathrm{RM}(w_0, N)$ by the first part. So $\dim \mathcal{T}_m \le \dim \mathrm{RM}(w_0, N) + e \cdot \#\{j \text{ odd} \le m, \mathrm{wt}_2(j) > w_0\}$. $\square$

**[checked]** `04_alternant_dim.py` computes $\dim B_m$ exactly (rank over $\mathbb{F}_2$) on $\mathrm{span}(1, \dots, x^{N-1})$ in $\mathrm{GF}(2^{12})$, $\mathrm{GF}(2^{10})$ ($N = 10$) and $\mathrm{GF}(2^{16})$ ($N = 9$) for six values of $m$ each. The bound holds in all 18 cases. It is exact in the six cases with $e = 16$, within $4\%$ in the six with $e = 12$ (for example $m = n/8$: $\dim B_m = 377$, bound 374, generic value 56), and within $22\%$ when $D$ is the whole field ($e = N = 10$).

For leanVM at rate 1/2 ($N = 25$, $e = 64$):

| $m$ | lower bound on $\dim B_m$ | on a generic domain |
| --- | --- | --- |
| $n/8 - 1$ and $n/8$ | 243198 | 326 ($\mathrm{RM}(2, 25)$) |
| $0.15n$ | 222206 | 326 |
| $3n/16$ | 59074 | 326 |
| $0.2n$ | 56834 | 326 |
| $n/4 - 1$ | 1154 | 26 ($\mathrm{RM}(1, 25)$) |

Reading. On a generic domain the differences in the window are quadrics at the level of power sums (and affine hyperplanes once the even $e_j$ are used). On the real domain the same linear constraints leave a code of dimension at least $2.4 \cdot 10^5$: there are at least $2^{243198}$ subsets $\Delta$ of $D$ whose power sums up to $n/8$ all vanish. The reason is a count by 2-adic weight: the odd exponents $j < n/8$ of weight $w$ number $\binom{21}{w-1}$, each is worth 64 bits, and the monomials of degree $w$ number $\binom{25}{w}$, which is larger for $w \ge 18$. So no argument that is linear over $\mathbb{F}_2$ in the indicator can recover the rigidity at $N = 25$ in a 64-bit field. Any transfer has to use the non-linear conditions (the even $e_j$) and has to be about cliques, not about pairs.

### 3.3 Pairs are not rare on the real shape. Classes stay small anyway (toy sizes)

**[checked]** The same exhaustive enumeration on the real shape $D = \mathrm{span}(1, x, \dots, x^4)$ in $K$ ($n = 32$), against the generic table of section 2.7:

| $(T, m)$ | dual rate-1/2 agreement | classes with $\ge 2$ members (generic) | pairs violating the generic congruence | largest class (generic) |
| --- | --- | --- | --- | --- |
| $(12, 3)$ | 20, degree $\le n/2$ | 1038438 (1038438) | 0 | 1400 (1400) |
| $(12, 4)$ | 20 | 17088808 (1598360) | 21524896 of 23217496 | 13 (7) |
| $(11, 5)$ | 21 | 6820480 (451360) | 7966080 of 8486880 | 7 (3) |
| $(10, 6)$ | 22 | 76880 (76880) | 0 | 3 (3) |

and for $n = 16$ (`04_universal16.py --poly`): at $m = 2$ the real shape has classes of 15 at $(k, T) = (8, 10)$ (generic 7), 9 at $(9, 11)$ (generic 3, and above the generic bound $7.1$), 8 at $(10, 12)$ (generic 4), and no deviation at $m = 3, 4, \dots$.

So at toy sizes the real shape is far from formal in the sense that matters for a proof: at $T = 5n/8$ and rate 1/2, $93\%$ of the common-top pairs are accidents of the embedding. Lemma 6.1 of note 05 (a non-formal family survives on a $2^{-40}$ fraction of domains) is true and is not in conflict with this: it is a statement about one family, and a domain has only $64N$ bits while there are $2^{\Theta(n)}$ candidate pairs, so every domain has accidental pairs, in number about (pairs) $\times 2^{-(\text{bits of the constraints that fail formally})}$. For the same reason **a first-moment bound over random domains cannot work**: the probability that a given set of nonzero forms vanishes at a random point of $K^N$ is at least about $2^{-64N}$ whenever they have a common zero, and the number of candidate cliques is exponential in $n$. This is a counting argument against the method, not a theorem.

What the tables do support: the accidental pairs do not assemble into large classes. The largest real-shape class is within a factor 2 to 3 of the generic one in every window cell computed, and the deviation disappears as soon as the depth $m$ carries enough bits ($m = 6$ at $n = 32$, where $e_6$ alone has 25 bits).

### 3.4 The accounting that replaces a proof

A real class at depth $m$ is a union of formal classes glued by accidents, and an accident is one or more equalities in $K$ that are not formal identities, each worth at most 64 bits (49 for $e_2$ on the real shape). The only general mechanism I know that produces accidents in bulk is pigeonhole on a formal family: a formal class of size $L_0$ at depth $m_0 < m$ whose next coefficients take values in $K$ splits into real classes of size about $L_0 / 2^{64 c}$ at depth $m$, $c$ the number of coefficients between $m_0$ and $m$ that are not formally constant on it. At rate 1/2 and $N = 25$:

- from the $5n/8$ class ($L_0 = 2^{30.8}$, depth $n/8 - 1$) to depth $n/8$: $c = 1$, expected number of accidental pairs $2^{60.6 - 64} < 1$, no triples. (At $N = 28$ a handful of pairs.)
- from the $9n/16$ classes ($L_0 \le 2^{102.7}$, depth $n/16 - 1$) to depth $n/8$: for unions of flats of size $n/8$ the non-constant positions below $n/8$ are $n/16, 3n/32, 7n/64, \dots$, so $c \ge 22$, $64c = 1408$ bits against 103.
- coset unions with $M$ labels: the cost is $\sum_j \min(64, \dim \mathrm{Sym}^j)$ of the label space, which exceeds $\log_2 \binom{M}{5M/8}$ for every $M$ (notes 02 section 7, 05 section 5).

Nothing reaches $2^{10}$. This is the same accounting as in notes 01, 02 and 05, and it has the same weakness: it bounds what pigeonhole gives, not what exists. Its one known failure mode at our size is instructive: at rate 1/4 the Gold family of note 01 has $2^{4N - 10}$ quadric candidates against one 64-bit condition, so about $2^{26}$ solutions at $N = 25$, each worth 16 codewords, at agreement $3n/8$. That family is not formal and not a strict common top (its word has degree $n/2$). So "real = formal" is false at rate 1/4 between $3n/8$ and $7n/16$ as soon as $4N > 74$, and the right conjecture has to include the pigeonhole term.

## 4. Dead ends

1. **Counting with intersections only.** Any argument that uses only $|S_i \cap S_j| \le k - 1$, or the MDS bounds on higher intersections ($j$ affinely independent members share at most $k - j + 1$ points), stops at Johnson: below it the second-moment condition is met by set systems with pseudorandom intersections $\tau^2 n < k$, and the higher MDS conditions are implied by the pairwise one up to $O(j)$. Flats show that subspace domains really do sit at Johnson at rate 1/4. Pinning (Proposition 1.3) is the quantitative form.
2. **Guruswami-Sudan with linearized monomials.** Using only $Y^{2^i}$ in the interpolation polynomial would make the list an $\mathbb{F}_2$-affine space and Theorem 1.2-style counting applicable, but it uses a subset of the monomials of the same weighted degree, so its radius is strictly worse than Johnson.
3. **Folded-code interpolation along translations.** Interpolating $A_0(X) + \sum_{a \in W} A_a(X)\, Y_a$ through the points $(x, (w(x + a))_{a \in W})$ captures a member only if its agreement set is nearly $W$-invariant (for an arbitrary set of density $\tau$ the common part of $|W|$ translates has density $\tau^{|W|}$), and even then the solution space of $\sum_a A_a(X) c(X + a) = A_0$ is a module over $F[L_W]$ of rank up to $|W| - 1$, of dimension $\Theta(k)$: translations have order two, so there is no analogue of the bounded-dimension step of folded Reed-Solomon. The coset-union family lives exactly in this module.
4. **Covering the list by low-dimensional spaces.** Needed to use Theorem 1.2. Lists inside Johnson already have dimension comparable to their size, so any such statement must be specific to the beyond-Johnson part. I have none.
5. **Recursion through $D \to L_a(D)$.** Writing $c = g_0(L_a) + X g_1(L_a)$ turns a list into a list of the 2-interleaved code of half the length at the same rate, but only on the fibres that lie entirely in the agreement set, of density $\ge 2\tau - 1$: the agreement gets worse. The half fibres give the norm relation $N(c - w) = 0$, which is quadratic in $(g_0, g_1)$. Restricting to a hyperplane doubles the rate instead. Every natural reduction goes from the small domain to the large one (lifting), which is the direction of the attacks.
6. **Character theory over $K$.** $K$-valued functions on $\mathbb{F}_2^N$ have no characters in characteristic two. The transform that works is the integer Walsh transform of the agreement sets, and connecting it to the code needs a place (section 2) or independent monomials.
7. **$S$-unit and Mason-Stothers bounds** for $Z_{S_i} - Z_{S_j} = c_j - c_i$: the known bounds for unit equations over function fields are exponential in the rank of the unit group, here $n$, and in characteristic $p$ Frobenius produces genuine infinite families, which is what flats are.
8. **Incidence bounds** (rich curves through the graph of $w$): they address $k = O(1)$ and $T \ll n$. The Sidon example of note 02 lives there.
9. **A first-moment bound over random domains.** Section 3.3.
10. **The dual (key equation) form.** The error locators $Z_{D \setminus S_i}$ of all members lie in the solution module of one key equation, of rank two over $F[X]$, and the list is the set of its elements of degree $\le n - T$ that split over $D$. Strict common tops are the special case where one of the two generators is constant. I could not use the general case for anything.

## 5. Conjectures and what they would give

**Conjecture C. [conjectured]** For $D = D_{\kappa,R} \subset K$ at level-0 sizes ($N = 24 + R$): (a) rate 1/2: $\Lambda(T) \le 2^{10}$ for $T \ge 0.64n$, and $\Lambda(T) \le 2^{32}$ for $T \ge 5n/8 + \ell$; (b) rate 1/8: $\Lambda(T) \le 2^{10}$ for $T \ge n/4 + n/64$; (c) rate 1/16: the same for $T \ge 3n/16$.

Evidence for: Corollary 2.5 and the sharper Proposition 6 of note 02 (formal strict tops are $\le 4$ or $\le 7$ in these ranges), Theorem 2.6 (stable under up to about $\sqrt n$ phantom roots anywhere), the Parseval cap of note 01 for the one known multiset mechanism ($5/8 + O(L^{-1/2})$, hence the margin $0.64$ in (a)), the accounting of section 3.4, and toy sizes on the real shape (largest classes 13, 7, 3 at $n = 32$).

Evidence against, or missing: (i) nothing is proved for words with many phantom roots outside $D$, on any domain; (ii) on the real shape the toy classes exceed the formal ones (factor up to 3) and one cell exceeds the formal Parseval bound; (iii) the Gold prediction at rate 1/4 shows non-formal families of size $2^{30}$ at our $N$, so a structured non-formal family in the windows of (a) to (c) would not be surprising in principle, and I only know that the obvious candidates fail the count. I would put (a) well ahead of (b) and (c): the rate-1/2 window has been attacked by four notes and by [DKTZ26], [Zhu26], the low-rate windows much less.

If Conjecture C is taken as an assumption (as proximity-gap conjectures were for FRI), the level-0 thresholds and query counts would be: rate 1/2, $A = 0.64n$, $t = 168$ (or $A = 5n/8 + \ell + 1$, $t = 160$, with 22 more grinding bits); rate 1/8, $A = 17n/64$, $t = 57$; rate 1/16, $A = 3n/16$, $t = 45$; rate 1/4 unchanged. Against 218, 73, 55 deployed.

## 6. What to try next, ranked

1. **General words on generic domains.** This is the clean open problem and I think it is tractable: prove that a list on a generic domain at rate 1/2 and agreement $(5/8 + \epsilon)n$ has $O(\epsilon^{-2})$ members, for every word. Lemma 2.2 is the tool: for every $W$ the list specializes to a list of the multiplicity code on the generic domain $D/W$, with collapses. For each functional the members fall into at most $1 + (n - T)/(m + 1)$ clusters (members with the same $P$), different clusters have $n_\varphi$ at distance $\ge m + 1$, and what is missing is control inside a cluster when $r \ge m$. Two sub-steps: (a) phantom roots in $D$ (locators with multiplicities), where Theorem W of note 02 is exact and the conjectured cap is $5/8 + O(L^{-1/2})$; (b) an induction on $N$ through $W$ of dimension one, where the specialized code is the mixed 2-interleaved code of half the length.
2. **The second dyadic range in the formal model.** For $n/16 \le m < n/8$ every difference is $f = \frac14 \sum c_\varphi \chi_\varphi$ with values in $\{-1, 0, 1\}$ and at most 14 characters, so $f$ is a function of at most 14 functionals and the classification is finite. Carry it out and prove $O(n)$ members at rate 1/2 for $T > 9n/16$ (the truth at the top of the range is $56n - 392$). This would make "list budget $2^{32}$ at $A$ just above $9n/16$" a theorem of the formal model, $t = 131$.
3. **Measure cliques on the real shape where wrapping occurs.** Take $N = 10$ to $14$ in $\mathrm{GF}(2^{e})$ with $e/N \approx 64/25$ and the power basis, enumerate the full $5n/8$ class of notes 02 and 05 (it has $56n - 392$ members, so this is cheap), and histogram $e_{n/8}$ on it. The largest fibre is the real-shape list at $T = 5n/8$ genuine from that class. The accounting predicts the formal value 7 plus isolated pairs. A fibre of size growing with $n$ would refute Conjecture C(a) at once. Then the flat-swap clique search suggested in note 02 section 9.
4. **Sharpen Theorem 2.6 to $r$ linear in $n$ for roots outside $D$.** Part 1 of Theorem 2.4 holds for every $r < m$. The loss to $\sqrt n$ comes from using Parseval on the errors $\eta_\varphi$. A structural use of the dichotomy of Theorem 2.3 over all $W$ at once (the quantity $\delta_W$ jumps over $(r, m]$ along every flag) should do better.
5. **A real-domain theorem.** I have no approach. Any proof must separate cliques from pairs and must use the even $e_j$ (section 3.2). If the design can tolerate it, the cheapest "theorem" is a conjecture stated for the exact parameters, with sections 2 and 3.4 as its support.

## 7. Reproduction

All under `doc/whir_soundness_gap_notes/scripts/`. Python 3 without dependencies, one C file compiled with the system compiler.

- `04_loc16.py [--generic]`: exact strict common-top maxima for $n = 16$, all $(k, T)$, on the real shape or a random domain in $K$, with the Johnson bound for comparison. 1 s and 15 s.
- `04_universal16.py [--poly]`: Corollary 2.5 on $n = 16$ (monomial independence, congruences, hyperplane differences, class sizes). About 15 s.
- `04_universal32.c`: `cc -O2 -o u32 04_universal32.c`, then `./u32 T m mode seed` with mode 0 (two random embeddings) or 1 (real shape). The tables of sections 2.7 and 3.3 are `12 3`, `12 4`, `11 5`, `10 6` in both modes. About 100 s each on one core.
- `04_phantom16.py`: Theorem 2.4 with one phantom root anywhere in $K$, $n = 16$. A few minutes.
- `04_alternant_dim.py`: Proposition 3.1, exact ranks on three analogues and the bound at $N = 25$. Under 1 s.
- `04_padded_flats.py`: a direct check (degrees and pointwise agreement over $K$) of the simplest rate-1/2 family at $5n/8 - 1$, the hyperplanes of a hyperplane, minus the origin, padded by a fixed set: $2^{N-1} - 1$ genuine codewords, $N = 4, 5, 6$. It is a special case of Lemma C of note 01 and is kept only as an independent check.
