# 12. List bounds on generic domains: multiset tops, linear stability, the second dyadic range

Researcher 12, round 2. Every statement is tagged **[proved]** (proof in this note, possibly computer assisted, and then I say which finite computation it uses), **[checked]** (numerically, sizes stated) or **[conjectured]**. Scripts are `scripts/12_*`, section 10 says how to run them.

Notation. $F$ is a field of characteristic two, $D \subset F$ an $\mathbb{F}_2$-subspace of dimension $N$, $n = 2^N$, and $D$ is **generic**: it has a basis that is algebraically independent over $\mathbb{F}_2$ (the formal model of notes 02, 04, 05). Codewords are polynomials of degree $< k$, $k = \rho n$, $T = \tau n$ is an agreement count, $m = T - k$. For a multiset $\mu : D \to \mathbb{Z}_{\ge 0}$, $|\mu|$ is its mass, $Z_\mu = \prod_s (X - s)^{\mu(s)}$, $n_\varphi(\mu) = \sum_{\varphi(s) = 1} \mu(s)$ for a functional $\varphi \in D^\ast$, and $\hat f(\varphi) = \sum_x f(x)(-1)^{\varphi(x)}$, $\chi_\varphi = (-1)^{\varphi}$. A *list* is $(w; c_i; S_i)_{i \le L}$: a polynomial $w$ that restricts to the word, distinct $c_i$ of degree $< k$, and sets $S_i$ with $w = c_i$ on $S_i$, $|S_i| \ge T$. Its *phantom degree* is $r = \deg w - T$. The list is a **strict common top** if $w - c_i = \lambda Z_{S_i}$, and a **multiset top** if some polynomial representative $w$ of the word (of any degree $M$) has $w - c_i = \lambda Z_{\mu_i}$ for multisets $\mu_i$ on $D$, that is every root of every $w - c_i$ lies in $D$. $u := n/16$.

## 0. Summary

**What is now proved, in the generic model.**

| | statement | class of words | status |
| --- | --- | --- | --- |
| A (2.4) | Rate 1/2, $T = (5/8 + \epsilon)n$: $L \le \max\bigl(1/(16\epsilon^2),\ 1 + (2\tau - \tfrac12)/\epsilon\bigr)$. This proves the cap $5/8 + O(L^{-1/2})$ conjectured in notes 02 and 05, with constant $1/4$ against $0.2165$ for the biased padding of note 01 | multiset tops, any mass | proved |
| A' (2.5) | Rate 1/8, $T = (1/4 + \epsilon)n$: $L \le \max(15,\ 1 + (2\tau - \tfrac18)/\epsilon)$. Rate 1/16, $T = (3/16 + \epsilon)n$: $L \le \max(7,\ 1 + (2\tau - \tfrac1{16})/\epsilon)$ | multiset tops, any mass | proved |
| B (3.1) | If $m \ge n/8$, $T \ge 5n/8$ or $T \le 3n/8$, and the phantom degree is $r \le n/96$: any two members differ by a hyperplane swap up to $4r + 8r^2/n$ points, and $L \le \frac{n/4 - \theta}{(T - n/2)^2/n - \theta}$, $\theta = 2r + 4r^2/n$. This replaces the $\sqrt n$ of note 04 Theorem 2.6 by a linear tolerance. At rate 1/16, $3n/16 \le T < n/4 - 3r$: $L = 1$ | all words of degree $\le T + n/96$, phantom roots anywhere | proved |
| C (5.1) | Second dyadic range ($n/16 \le$ depth): the symmetric difference of two members is the support of a quadratic Boolean function of rank $\le 4$, of size $n/4, 3n/8, n/2, 5n/8$ or $3n/4$; a class has at most $2n^5$ members | strict common tops | proved (the exponent is far from the truth) |
| D (5.2) | The class of seven cosets of a codimension-4 subspace has exactly $105n - 965$ members for every $n \ge 32$: a list of that many genuine codewords (degree $< n/2$) at agreement exactly $9n/16$. For $N = 25$ this is $2^{31.7}$ | strict common tops | proved, computer assisted ($n = 32$, $n = 64$ enumerations), and checked independently at $n = 128$ |
| E (1.1) | Every bound above holds over every field $F \supseteq D$ and for interleaved words with any number of lanes, with no loss | as in each row | proved |

**What is not proved.** There is still no bound for all words, even in the generic model, in any of the three windows. Section 4 says exactly why the place method stops (it gives information only when the phantom degree is below $m$), gives the two facts that any all-words bound must respect (the trivial lists of size about $(1 - \rho)/(\tau - \rho)$, which exceed every strict-top bound at rates 1/8 and 1/16, and a small example where the all-words list is twice the multiset one), and states the problem as a rank problem for explicit matrices. In the second dyadic range the upper bound $O(n)$ is **[conjectured]**, supported by exhaustive enumeration at $n = 16, 32$ and complete classes at $n = 64, 128$.

**The second dyadic range, reconciled** (rate 1/2, $N = 25$, all in the formal model, section 5.4). The counts quoted in round 1 at "$9n/16$" live at two different depths. Genuine codewords (degree $< n/2$) at agreement exactly $9n/16$ have depth $n/16$, the second range, and the largest class known and found is $105n - 965 = 2^{31.7}$. Degree $\le n/2$ at $9n/16$, or genuine at $9n/16 - 1$, has depth $n/16 - 1$, the third range, where the $2^{44.8}$ (glued coset unions), $2^{72}$ (stacks) and $2^{102.7}$ (height-3 trees) are sublists of the list of one and the same word $X^{n/2} L_U$, $|U| = n/16$. So with analysis degree $d = k - 1 + \ell$: a budget of $2^{32}$ is what the threshold $A = 9n/16 + \ell$ needs (conjecturally sufficient for strict tops), budgets between $2^{32}$ and $2^{102}$ buy nothing more, and below $9n/16 + \ell$ the list is at least $2^{102.7}$.

## 1. Tools

### 1.1 Fields and interleaving in the generic model

**Proposition 1.1. [proved]** Let $D \subset F$ be generic and let $(w^l; c_i^l; S_i)_{l \le h}$ be an $h$-interleaved list over $F$: distinct tuples $(c_i^1, \dots, c_i^h)$, $i \le L$, with $w^l = c_i^l$ on $S_i$ for all $l$. Then over $F' = F(t_1, \dots, t_h)$ the single word $w^t = \sum_l t_l w^l$ has the list $(w^t; c_i^t; S_i)$ with $c_i^t = \sum_l t_l c_i^l$ pairwise distinct, $D$ is generic in $F'$, and $\deg w^t \le \max_l \deg w^l$. Conversely a single-lane list is an interleaved list with one lane.

*Proof.* The $t_l$ are linearly independent over $F$, so distinct tuples give distinct combinations, and a basis of $D$ that is algebraically independent over $\mathbb{F}_2$ in $F$ stays so in $F'$. $\square$

Consequence. In the generic model a list bound proved for every field containing $D$ is a list bound for interleaved words with any number of lanes and the same agreement sets, with no loss (not even the $2^{32}$ ceiling of note 04 Proposition 1.1, which comes from $K$ being finite). All theorems below are for an arbitrary field $F \supseteq D$, so (a) base field, (b) arbitrary extensions and (c) any number of lanes all hold. What does change under interleaving is the *class of words*: a hypothesis on the word must hold for the combination $w^t$. For Theorem B (phantom degree $\le r$) it is enough that every lane has a representative of degree $\le T + r$. For Theorem A (multiset tops) the combination must split over $D$, which forces $w^l - c_i^l = a_l Z_{\mu_i}$ with scalars $a_l$: all lanes are multiples of one multiset top word modulo codewords. So Theorem A is in substance a single-lane statement, and I do not claim more. None of this says anything about the real domain, where Proposition 1.1 is not available.

### 1.2 The Walsh criterion and its reduction modulo 2

I use Theorem W of note 02 and its converse (equivalently Lemma 6.2 of note 05, Corollary 2.5 of note 04), for multisets: on a generic domain, two multisets $\mu, \mu'$ of equal mass share $e_1, \dots, e_t$ if and only if $n_\varphi(\mu) \equiv n_\varphi(\mu') \pmod{2^{a+1}}$ for all $\varphi$, where $2^a \le t < 2^{a+1}$. Equivalently $f = \mu - \mu'$ has $\hat f(\varphi) \in 2^{a+2}\mathbb{Z}$ for all $\varphi$ and $\hat f(0) = 0$. A multiset top list of mass $M$ in degree $< k$ shares $e_1, \dots, e_g$ with $g := M - k$, so $a = \lfloor \log_2 g \rfloor$.

**Lemma 1.2 (parity). [proved]** Let $f : \mathbb{F}_2^N \to \mathbb{Z}$ with $\hat f(\varphi) \in 2^j \mathbb{Z}$ for all $\varphi$. Then $f \bmod 2$ is a Boolean function of algebraic degree at most $N - j$: it lies in the Reed-Muller code $\mathrm{RM}(N - j, N)$ (zero if $j > N$).

*Proof.* $f = 2^{-N} \sum_\varphi \hat f(\varphi) \chi_\varphi$ and $\chi_\varphi = \prod_{i \in \mathrm{supp}\,\varphi} (1 - 2x_i) = \sum_{A \subseteq \mathrm{supp}\,\varphi} (-2)^{|A|} x^A$. The coefficient of the monomial $x^A$ in $f$ is $2^{-N}(-2)^{|A|} \sum_{\varphi \supseteq A} \hat f(\varphi) \in 2^{|A| + j - N}\mathbb{Z}$. The multilinear expansion of an integer-valued function on $\{0,1\}^N$ is unique and has integer coefficients (Möbius inversion), so the coefficients with $|A| > N - j$ are even. $\square$

For $\{0, \pm 1\}$-valued $f = 1_S - 1_{S'}$ this is the Reed-Muller shadow of note 04 Proposition 3.1 on a generic domain. Its use for multisets is new: with $j = a + 2$,

- $n/8 \le g < n/4$ ($a = N - 3$): the odd-multiplicity sets $O(\mu) = \{x : \mu(x) \text{ odd}\}$ of two members differ by an affine function, $1_{O(\mu)} + 1_{O(\mu')} \in \{0, 1, 1_H : H \text{ an affine hyperplane}\}$;
- $n/4 \le g < n/2$: $O(\mu') = O(\mu)$ or $O(\mu') = D \setminus O(\mu)$;
- $g \ge n/2$: $O(\mu') = O(\mu)$.

**[checked]** `12_multiset16.c`: for $n = 16$ and all $3^{16}$ multisets with multiplicities $\le 2$, grouped by the Walsh key at the modulus given by $(M, k)$, for $(k, T) \in \{(8, 10), (8, 11), (8, 12), (2, 4), (2, 5)\}$ and all masses $M$: no pair in any class violates the parity statement.

### 1.3 The dichotomy of note 04

**Theorem (note 04, 2.3 and 2.4). [proved there]** On a generic domain let two members of a list have $|S_1| = |S_2| = T$, $f = 1_{S_1} - 1_{S_2}$, $r = \deg w - T$. For a subspace $W \le D$ put $\delta_W = \frac12 \sum_{C \in D/W} |\sum_{x \in C} f(x)|$. Then $\delta_W \le r$ or $\delta_W \ge m + 1$. For $W = \ker\varphi$, $\delta_W = |d_\varphi|$ with $d_\varphi = n_\varphi(S_1) - n_\varphi(S_2) = -\hat f(\varphi)/2$, and if $2^a \le m$, $m + r < 2^{a+1}$ then $d_\varphi \bmod 2^{a+1} \in [-r, r]$.

I reread both proofs (specialization at the place with kernel $W$, Gauss valuation, comparison of $\mathrm{red}(\lambda(w - c_1))$ and $\mathrm{red}(\lambda(w - c_2))$) and use them as stated. Call $W$ **low** if $\delta_W \le r$ and **high** if $\delta_W \ge m + 1$. $W = D$ is low and $W = 0$ is high, since $\delta_0 = |S_1 \triangle S_2|/2 \ge m + 1$.

## 2. Multiset tops: a constant bound in the open windows

Throughout this section $(w; c_i; S_i)_{i \le L}$ is a multiset top list on a generic domain: $\deg w = M$, $w - c_i = \lambda Z_{\mu_i}$ with $\mu_i$ multisets on $D$ of mass $M$, pairwise distinct, $S_i = \mathrm{supp}\,\mu_i$, $|S_i| \ge T$, and $g = M - k \ge T - k$. Strict common tops are the case $M = T$, and the biased padding of note 01 section 3.4 is $\mu_i = 1_B + 1_{H_i}$, $M = 3n/4$. Write $O_i = \{x : \mu_i(x) \text{ odd}\}$ and $\mu_i = 1_{O_i} + 2\nu_i$, so $Z_{\mu_i} = Z_{O_i} Z_{\nu_i}^2$, and $R_i = \mathrm{supp}\,\nu_i$, so $S_i = O_i \cup R_i$.

### 2.1 Three lemmas

**Lemma 2.1 (sizes). [proved]** $|O_i| \ge 2|S_i| - M \ge 2T - M$ and $|O_i| \le M$.

*Proof.* $M = |O_i| + 2|\nu_i| \ge |O_i| + 2|R_i| \ge |O_i| + 2(|S_i| - |O_i|)$. $\square$

**Lemma 2.2 (Frobenius descent). [proved]** Let $\mathcal{C}$ be a set of members with the same odd set $O$, $|\mathcal{C}| \ge 2$, and $\omega = |O|/n$. Then $|O| \le k - 1$, the polynomials $v_i = Z_{\nu_i}$, $i \in \mathcal{C}$, satisfy $\deg(v_i - v_j) < (k - |O|)/2$, hence $|R_i \cap R_j| < (k - |O|)/2$ for $i \ne j$, and if $\tau > \rho + \frac18$ then
$$|\mathcal{C}| \ \le\ \frac{2\tau - \rho}{\tau - \rho - \frac18} .$$

*Proof.* $O \subseteq S_i \cap S_j$ and two distinct codewords agree on at most $k - 1$ points. In characteristic two $Z_{\mu_i} - Z_{\mu_j} = Z_O (v_i^2 - v_j^2) = Z_O (v_i - v_j)^2$, a nonzero polynomial of degree $< k$, so $2\deg(v_i - v_j) < k - |O|$, and $v_i - v_j$ vanishes on $R_i \cap R_j$. So the sets $R_i$ have $|R_i| \ge |S_i \setminus O| \ge p := T - |O|$ and pairwise intersections at most $q$ with $q < (k - |O|)/2$. (In words: the $\nu_i$ are a list of the code of degree $< (k - |O|)/2$, of rate below $\rho/2$.) The Johnson count for a set system (trim each $R_i$ to $p$ points, count pairs $(x, \{i, j\})$): $|\mathcal{C}|\,(p^2/n - q) \le p - q$ whenever $p^2 > nq$. Now
$$\frac{p^2}{n^2} - \frac qn \ >\ (\tau - \omega)^2 - \frac{\rho - \omega}{2} \ \ge\ \min_{\omega \in \mathbb{R}} = \frac{\tau - \rho}{2} - \frac1{16} \quad (\text{at } \omega = \tau - \tfrac14),$$
where $q$ was replaced by its upper bound $q^\ast = (k - |O|)/2$: this is allowed because $(p - q)/(p^2/n - q)$ increases with $q$. With the same replacement $(p - q^\ast)/n = \tau - \rho/2 - \omega/2 \le \tau - \rho/2$. $\square$

The minimum over $\omega$ is where the number $5/8$ comes from at rate 1/2: after removing the common odd part and taking a square root, the list sits strictly inside the Johnson radius of the smaller code for every size of the odd part if and only if $\tau > \rho + 1/8$.

**Lemma 2.3 (distinct odd sets). [proved]** Assume $g \ge n/8$. Let $O_{i_1}, \dots, O_{i_q}$ be pairwise distinct odd sets of members and suppose no two of them are complementary. Then $\sum_{j \le q} (n - 2|O_{i_j}|)^2 \le n^2$.

*Proof.* By Lemma 1.2, $1_{O_{i_j}} = 1_{O_{i_1}} + \alpha_j \pmod 2$ with $\alpha_j = \varphi_j + c_j$ affine, $\alpha_1 = 0$. With $G = (-1)^{1_{O_{i_1}}}$, $n - 2|O_{i_j}| = \sum_x (-1)^{1_{O_{i_1}}(x) + \alpha_j(x)} = (-1)^{c_j}\hat G(\varphi_j)$. Distinct odd sets that are not complementary have distinct $\varphi_j$, and $\sum_\varphi \hat G(\varphi)^2 = n^2$. $\square$

### 2.2 The theorem at rate 1/2

**Theorem 2.4 (A). [proved]** On a generic domain at rate 1/2, a multiset top list of any mass at agreement $T = (\frac58 + \epsilon)n$, $\epsilon > 0$, has
$$L \ \le\ \max\Bigl(\frac{1}{16\epsilon^2},\ 1 + \frac{2\tau - \frac12}{\epsilon}\Bigr) .$$
More precisely, if $M < 3n/4$ then $L \le n^2/(4T - 2M - n)^2 \le 1/(16\epsilon^2)$, and if $M \ge 3n/4$ then $L \le 1 + (2\tau - \frac12)/\epsilon$. Consequently a multiset top list with $L$ members has agreement at most $(\frac58 + \frac{1}{4\sqrt L})n$ as soon as $L \ge 64$.

*Proof.* $g = M - k \ge T - k > n/8$, so Lemma 1.2 applies. Case $M < 3n/4$: by Lemma 2.1, $|O_i| \ge 2T - M > n/2 + 2\epsilon n > k - 1$. By Lemma 2.2 no two members share their odd set, and two odd sets of size $> n/2$ are not complementary. Lemma 2.3: $L\,(4T - 2M - n)^2 \le n^2$, and $4T - 2M - n > 4\epsilon n$. Case $M \ge 3n/4$: $g \ge n/4$, so by Lemma 1.2 the odd sets take at most two values, $O$ and $D \setminus O$. One of them has at least $n/2 = k$ points and belongs to at most one member (Lemma 2.2), the other class has at most $(2\tau - \rho)/(\tau - \rho - \frac18) = (2\tau - \frac12)/\epsilon$ members. For the last sentence, $1 + (2\tau - \frac12)/\epsilon < 1/(16\epsilon^2)$ when $\epsilon \le 1/32$. $\square$

Remarks. (i) For $M = T$ (strict common tops) the first bound is $1/(2\tau - 1)^2$, Corollary 2.5 of note 04, by a different proof that never looks at Walsh coefficients beyond their parity. (ii) Tightness: the biased padding of note 01 has $L = 3/(64\epsilon^2)$ against the bound $4/(64\epsilon^2)$. The factor $4/3$ is the term $\hat G(0)^2$ of Lemma 2.3, which that family wastes ($|B| = n/4$ exactly). I do not know whether $1/(16\epsilon^2)$ is attained. (iii) The second regime ($M \ge 3n/4$, bound $O(1/\epsilon)$) has no known example beyond $O(1)$ members. (iv) At $\epsilon = 0$ nothing is claimed, correctly: at $T = 5n/8$ there are multiset lists growing with $n$ (note 02 section 6).

### 2.3 Rates 1/8 and 1/16

**Theorem 2.5 (A'). [proved]** On a generic domain let $\rho \le \frac18$ and $T = (\rho + \frac18 + \epsilon)n$, $\epsilon > 0$, $T < n/2$. A multiset top list of any mass has
$$L \ \le\ \max\Bigl(\Bigl\lceil \frac{1}{(1/2 - 2\rho)^2} \Bigr\rceil - 1,\ 1 + \frac{2\tau - \rho}{\epsilon}\Bigr) .$$
At rate 1/8 this covers the whole window $(n/4, 0.3536n)$ with $L \le \max(15, 1 + (2\tau - \frac18)/\epsilon)$. At rate 1/16 it covers $(3n/16, n/4)$ with $L \le \max(7, 1 + (2\tau - \frac1{16})/\epsilon)$.

*Proof.* $g \ge T - k > n/8$. If $M < k + n/4$: $|O_i| \ge 2T - M > 2T - k - n/4 = k + 2\epsilon n$, so by Lemma 2.2 the odd sets are pairwise distinct, and $|O_i| \le M < k + n/4 \le 3n/8$, so no two are complementary and $n - 2|O_i| > n/2 - 2k$. Lemma 2.3 gives $L (1/2 - 2\rho)^2 < 1$. If $M \ge k + n/4$: the odd sets take at most two values $O$, $D \setminus O$, and at most one of the two is smaller than $k$, so one class is a single member and the other is bounded by Lemma 2.2. $\square$

At rate 1/16 the lower part $(n/8, 3n/16]$ of the window is not covered: there $g$ can lie in $[n/16, n/8)$, the odd sets differ by quadratic functions, and when the odd set is common the descended list of Lemma 2.2 can lie outside its own Johnson radius. The natural proof is a recursion on Lemma 2.2 (the descended family is again a multiset top family with $(k, g) \mapsto ((k - |O|)/2, g/2)$), which I did not carry out. One sub-case goes as follows: if $M < 3n/16$ and $T > n/8$, then $|O_i| > k$, the odd sets are distinct, $O_i \triangle O_j$ is the support of a nonzero quadratic function with fewer than $3n/8$ points, hence a flat of codimension 2 (the weights of $\mathrm{RM}(2, N)$ below $3n/8$ are $0$ and $n/4$), each such flat contains more than $|O_1|/2 + n/32$ points of $O_1$, and a Fourier count as in section 5 should bound $L$ by a constant. I have only a sketch of that count, so the whole lower half of the rate-1/16 window is listed as open for multisets.

### 2.4 Checks

**[checked]** `12_multiset16.c` ($n = 16$, all multisets with multiplicities $\le 2$, exact classes by Walsh key, largest number of class members with support $\ge T$):

| $(k, T)$ | $T/n$ | largest multiset top list (mass where attained) | strict tops ($M = T$) | all words, annealing of note 02 | bound of this section |
| --- | --- | --- | --- | --- | --- |
| $(8, 10)$ | $5/8$ | 15 ($M = 11$) | 7 | 11 | none ($\epsilon = 0$) |
| $(8, 11)$ | $11/16$ | 3 ($M = 11$ and $M = 15$) | 3 | 3 | 16 |
| $(8, 12)$ | $3/4$ | 1 | 1 | 1 | 9 |
| $(2, 4)$ | $1/4$ | 4 ($M = 4, 5, 8$) | 4 | 9 | none |
| $(2, 5)$ | $5/16$ | 3 ($M = 5, 9$) | 3 | 6 | 15 |

Three things to read off. At $(8, 10)$ the multiset maximum 15 exceeds what the annealing of note 02 found (11), so that search was not exhaustive and its "explained by multisets" conclusion stands. At $(8, 11)$, the only window point of $n = 16$ at rate 1/2, multisets give nothing beyond strict tops. At $(2, 5)$, inside the rate-1/8 window, the all-words list (6, the Sidon tangent lines of note 02 section 8) is twice the multiset one: **all words are not multiset tops**, even in the generic model. That example has $k = 2$ and does not scale to constant rate (section 4.3), but it shows that Theorem A cannot be the whole story by a formal argument.

## 3. Stability under a linear number of phantom roots

Note 04 Theorem 2.6 shows that the rigidity of strict common tops survives about $(\tau - \frac12)\sqrt{n/2}$ phantom roots, and loses the rest because it bounds the errors $\eta_\varphi$ of the congruences one functional at a time. Using the dichotomy for all subspaces $W$ at once, as suggested in note 04 section 6 item 4, the tolerance becomes linear.

**Theorem 3.1 (B). [proved]** Let $D$ be generic and $(w; c_i; S_i)_{i \le L}$ a list with $|S_i| = T$, $T \ge 5n/8$ or $T \le 3n/8$, $m = T - k \ge n/8$, and phantom degree $r = \deg w - T$ with $r \le n/96$ and $m + r < n/4$. Then for all $i \ne j$ there is a hyperplane swap $g = 1_A - 1_B$ ($A$, $B$ the two cosets of a codimension-2 subspace inside one affine hyperplane) with
$$\#\{x : (1_{S_i} - 1_{S_j})(x) \ne g(x)\} \ \le\ 4r + \frac{8r^2}{n}, \qquad \bigl|\,|S_i \triangle S_j| - \tfrac n2\,\bigr| \le 4r + \frac{8r^2}{n},$$
and, with $\theta = 2r + 4r^2/n$,
$$L \ \le\ \frac{n/4 - \theta}{(T - n/2)^2/n - \theta} \qquad\text{whenever } \theta < (\tau - \tfrac12)^2 n .$$
If $2T < n/2 - 4r - 8r^2/n$ (for example rate 1/16 and $3n/16 \le T < n/4 - 3r$), then $L = 1$.

*Proof.* Fix $i \ne j$, $f = 1_{S_i} - 1_{S_j}$, $\sigma = |S_i \triangle S_j| \le 2\min(T, n - T) \le 3n/4$, $d_\varphi = -\hat f(\varphi)/2$. I use section 1.3.

*Step 1, spectral form of the dichotomy.* For a subspace $V \le D^\ast$ let $\mu(V) = \sum_{\varphi \in V} \hat f(\varphi)^2$, and $W = V^\perp \le D$ with coset sums $a_C = \sum_{x \in C} f(x)$. Parseval on $D/W$: $\mu(V) = \frac{n}{|W|} \sum_C a_C^2$. If $W$ is low, $\sum_C |a_C| \le 2r$ and $|a_C| \le |W|$, so $\mu(V) \le 2rn$. If $W$ is high, $\sum_C |a_C| \ge 2m + 2$ over $n/|W|$ cosets, so by Cauchy and Schwarz $\mu(V) \ge (2m+2)^2 > n^2/16$. Since $r \le n/96$, $6rn < (2m + 2)^2$. Call $V$ low or high accordingly.

*Step 2, every high $V$ contains a big functional.* Let $V$ be a minimal high subspace, of dimension $j$. If $j \ge 2$, all its $2^j - 1$ hyperplanes $V'$ are low, each nonzero $\varphi \in V$ lies in $2^{j-1} - 1$ of them, and $\hat f(0) = 0$, so $(2^{j-1} - 1)\mu(V) = \sum_{V'} \mu(V') \le (2^j - 1)\,2rn$, that is $\mu(V) \le 6rn$, a contradiction. So $j = 1$: $V = \{0, \beta\}$ with $|d_\beta| \ge m + 1$. Let $\mathrm{Big} = \{\beta \ne 0 : |d_\beta| \ge m + 1\}$. Hence: a subspace $V$ with $V \cap \mathrm{Big} = \emptyset$ is low, $\mu(V) \le 2rn$. And $\mathrm{Big} \ne \emptyset$, because $D^\ast$ is high.

*Step 3, the big coefficients.* By the congruence of section 1.3 with $2^{a+1} = n/4$, $d_\varphi \in \frac n4\mathbb{Z} + [-r, r]$, and $|d_\varphi| \le \sigma/2 \le 3n/8$. For $\beta \in \mathrm{Big}$, $|d_\beta| > n/8 > r$, so $d_\beta = \epsilon_\beta \frac n4 + \eta_\beta$ with $\epsilon_\beta = \pm 1$, $|\eta_\beta| \le r$, and $|\hat f(\beta)| \ge n/2 - 2r$. For $\varphi \notin \mathrm{Big}$, $|\hat f(\varphi)| \le 2r$. Parseval: $t (n/2 - 2r)^2 \le n\sigma \le 3n^2/4$ for $t = |\mathrm{Big}|$, so $t \le 3/(1 - 4r/n)^2 < 4$.

*Step 4, the energy outside $\mathrm{Big}$ is linear in $r$.* Let $B = \mathrm{span}(\mathrm{Big})$, of dimension $b \le 3$. A complement $V$ of $B$ in $D^\ast$ misses $\mathrm{Big}$, so $\mu(V) \le 2rn$, and a given $\varphi \notin B$ lies in a fraction $2^{-b}$ of the $2^{b(N - b)}$ complements. Averaging, $\sum_{\varphi \notin B} \hat f(\varphi)^2 \le 2^b \cdot 2rn \le 16rn$. The at most 7 elements of $B \setminus (\mathrm{Big} \cup 0)$ contribute at most $28r^2$.

*Step 5, $t = 2$.* Let $G = -\frac12 \sum_{\beta \in \mathrm{Big}} \epsilon_\beta \chi_\beta$. Then $\hat f - \hat G$ is $-2\eta_\beta$ on $\mathrm{Big}$ and $\hat f$ elsewhere, so $\sum_x (f - G)^2 \le \frac1n(12r^2 + 28r^2 + 16rn) = 16r + 40r^2/n < n/4$. If $t$ is odd, $G$ is a half-integer at every point while $f$ is an integer, so $\sum (f - G)^2 \ge n/4$. Hence $t = 2$, $\mathrm{Big} = \{\beta_1, \beta_2\}$, and $G = g$ is a hyperplane swap: it is $\pm 1$ on the two cosets of $\ker\beta_1 \cap \ker\beta_2$ where $\epsilon_1\chi_{\beta_1} = \epsilon_2\chi_{\beta_2}$ and $0$ elsewhere.

*Step 6, the sharp count.* With $t = 2$ redo step 4 with the hyperplanes $V_x = \{\varphi : \varphi(x) = 0\}$ of $D^\ast$, $x$ ranging over the points with $\beta_1(x) = \beta_2(x) = 1$. Each $V_x$ misses $\mathrm{Big}$, contains $\beta_1 + \beta_2$, and contains each $\varphi \notin B$ for exactly half of the $x$. So $\frac12 \sum_{\varphi \notin B} \hat f(\varphi)^2 + \hat f(\beta_1 + \beta_2)^2 \le 2rn$, and $\sum_x (f - g)^2 \le \frac1n(8r^2 + 4rn) = 4r + 8r^2/n$. Since $f - g$ is integer valued, it is nonzero on at most that many points, and $|\mathrm{supp}\, g| = n/2$.

*Step 7.* $|S_i \cap S_j| = T - \sigma/2 \le T - n/4 + \theta$, and the Johnson count $L(T^2/n - I) \le T - I$ with $I = T - n/4 + \theta$ gives the bound. If $2T < n/2 - 4r - 8r^2/n$ then $\sigma \le 2T$ contradicts $\sigma \ge n/2 - 4r - 8r^2/n$, so there is no second member. $\square$

Remarks. (i) The class of words covered is natural: $w$ is itself a polynomial of degree at most $T + n/96$, that is a codeword of the Reed-Solomon code of rate $\tau + 1/96$. For $N = 25$ this allows $r \le 349525$ phantom roots, placed anywhere in $\overline{F}$, against $r \le 1447$ in note 04. At $\tau = 0.65$ the count is $L \le 20$ for $r \le n/200$. (ii) By Proposition 1.1 it holds for interleaved words whose lanes all have degree at most $T + n/96$. (iii) The constant $1/96$ is not optimized, but the method cannot pass $r = m$: for $r \ge m$ the interval $(r, m]$ of the dichotomy is empty and section 1.3 says nothing (section 4.1). The padded hyperplanes of note 01 have $r = n/8 - \epsilon n$ and $m = n/8 + \epsilon n$, just inside $r < m$ and far outside $r \le n/96$, and they are not rigid, so some loss between $n/96$ and $m$ is real. (iv) The same proof works for multisets plus $r$ outside roots once $|a_C| \le |W|$ is replaced by a bound on the mass per coset. I did not write it out.

## 4. All words: what is missing, precisely

I have no bound for all words in any window, even on a generic domain. This section records why the present tools stop, one new piece of information that holds for all words, and the facts an all-words theorem must respect.

### 4.1 The place method is pairwise and stops at $r = m$

**[proved]** For a general word the interpolant has degree up to $n - 1$, so $r$ can be as large as $n - 1 - T$, and $r \ge m$ as soon as $T \le (n + k - 1)/2$, the unique decoding radius. For $r \ge m$ the dichotomy of section 1.3 is empty: every value of $\delta_W$ is $\le r$ or $\ge m + 1$. Concretely, for the place of a hyperplane $\ker\varphi$ the members fall into at most $1 + (n - T)/(m + 1)$ clusters (members with the same reduction $P$; at most 3 above $5n/8$ at rate 1/2), two members in different clusters have $|d_\varphi| \ge m + 1$, and two members in the same cluster are not constrained at all. A pair lies in different clusters for at most $n\sigma/(2m+2)^2 < 12$ functionals (for $m \ge n/8$, $\sigma = |S_i \triangle S_j| \le 3n/4$). So for all but a bounded number of places every pair is in the unconstrained situation, and no argument that uses the specializations pair by pair can bound a list of general words. This is the same obstruction as in Theorem 2.4 of note 04: with $r \ge m$ free phantom roots per member the $m + r$ conditions at one place can always be met.

The parity structure of section 2 is also lost: Lemma 1.2 is about roots in $D$. A phantom root $\rho \in \overline F$ has, at the place of $\ker\varphi$, a residue that is $0$, the residue $y_\varphi$ of the other coset, or neither, and for a point of $D$ the map $\varphi \mapsto [\text{residue is } y_\varphi]$ is linear. For an element of $\overline F$ it is arbitrary: the places of distinct hyperplanes are pairwise inequivalent valuations, and by weak approximation any finite pattern of residues is realized. **[proved]** (standard). So a single phantom root can imitate a point with any Boolean "coordinate function", and only the fact that the phantom roots are roots of $g_i = (w - c_i)/Z_{S_i}$, with $c_i$ in a $k$-dimensional space, constrains them.

### 4.2 Information beyond pairs

**Lemma 4.1 (three members). [proved]** Let $D$ be generic, $W \le D$, $v$ the valuation of note 04 Lemma 2.1 with its Gauss extension, and $c_i, c_j, c_l$ three members of a list of any word, with agreement sets $S_i, S_j, S_l$. Put $\nu_{ab} = v(c_a - c_b)$. After relabeling, $\nu_{ij} = \nu_{il} \le \nu_{jl}$. If $\nu_{ij} < \nu_{jl}$, then, with sums over the cosets $C$ of $W$,
$$\sum_C \max\bigl(|S_i \cap S_j \cap C|,\ |S_i \cap S_l \cap C|\bigr) \ \le\ k - 1 .$$
If the three values are equal, the reductions $\bar c_{ab} = \mathrm{red}(\mu(c_a - c_b))$, $v(\mu) = -\nu_{ij}$, are nonzero of degree $< k$, $\bar c_{ab}$ is divisible by $\prod_C (X - z_C)^{|S_a \cap S_b \cap C|}$, and $\bar c_{ij} + \bar c_{jl} + \bar c_{li} = 0$.

*Proof.* The Gauss valuation is ultrametric on $F[X]$ and $(c_i - c_j) + (c_j - c_l) = c_i - c_l$, so the two smallest of the three values are equal. $c_a - c_b = Z_{S_a \cap S_b} h$ with $v(Z_{S_a \cap S_b}) = 0$, so $\mathrm{red}(\mu(c_a - c_b)) = \mathrm{red}(Z_{S_a \cap S_b})\,\mathrm{red}(\mu h)$ whenever $v(\mu) = -\nu_{ab}$. If $\nu_{jl} > \nu_{ij}$ then $\mathrm{red}(\mu(c_j - c_l)) = 0$ and $\bar c_{ij} = \bar c_{il}$ is a nonzero polynomial of degree $< k$ divisible by both products. $\square$

So for every $W$ the list carries an ultrametric tree, and at every node the children are joined by a "list of differences" of the multiplicity code on $D/W$. For $W = 0$ this is empty (the valuation is trivial). I have not derived a list bound from it. It is the analogue, for subspace domains, of the step in which proofs of the GM-MDS theorem merge two evaluation points.

**The exact problem. [proved]** Sets $S_0, \dots, S_L$ are the agreement sets of a list (of some word, over some field containing a generic $D$) if and only if the homogeneous linear system $c_i(x) = c_j(x)$, $x \in S_i \cap S_j$, in the unknown coefficients of $c_0, \dots, c_L$, has a solution over $\mathbb{F}_2(b_1, \dots, b_N)$ with the $c_i$ pairwise distinct. (Define the word as $c_i$ on $S_i$. A solution over an extension gives one over the field of definition, and distinctness for all pairs at once is obtained by a generic combination of solutions.) The system has $\sum_i |S_i| - |\bigcup S_i| \ge (L+1)T - n$ equations and $(L + 1)k - k$ unknowns modulo the diagonal. If the evaluation points were algebraically independent, the higher-order MDS property of generic Reed-Solomon codes (Brakensiek, Gopi and Makam, via the GM-MDS theorem of Lovett and of Yildiz and Hassibi; quoted from memory, not re-read for this note) says that the count is exact, and a list at agreement $T$ has fewer than $(n - k)/(T - k)$ members, at most 3 at rate 1/2 and $5n/8$, which is the size of the trivial lists below. On a subspace the points are $n$ linear forms in $N$ variables, the count is not exact (flats, trees), and the all-words problem on a generic domain is precisely the determination of these ranks: a GM-MDS theorem for the linear forms $\sum x_i b_i$. Sections 2 and 3 are the part of it that parity and pairwise places can see.

### 4.3 What an all-words bound must respect

- **Trivial lists. [proved]** (note 02 section 1) Every domain has lists of size $\lfloor (n - k + 1)/(T - k + 1) \rfloor$, about $(1 - \rho)/(\tau - \rho)$. In the rate-1/2 window this is 3 or 2. At rate 1/8 it is 6 just above $n/4$ and 3 at the Johnson radius, and at rate 1/16 it is 14 just above $n/8$ and 5 near $n/4$. These exceed the strict common top bounds (4 at rate 1/8; 8, 7 and 1 at rate 1/16) and they have large phantom degree. So "all words behave like strict tops" is false at low rates even generically, and the right constant is at least the generic-points value.
- **Sidon tangent lines** (note 02 section 8): 6 lines at agreement 5 for $n = 16$, $k = 2$, against 3 for multiset tops (section 2.4). For a family $c_a = \sum_{i \le s} q_i(X) a^i$ each point lies on at most $s$ members, so $L\,T \le s\,n$, and I know no version at constant rate.
- **Multiset tops**: $3/(64\epsilon^2)$ members at $(5/8 + \epsilon)n$ at rate 1/2.

**Conjecture G. [conjectured]** On a generic domain, for every word (hence every interleaved word): at rate 1/2 and $T = (5/8 + \epsilon)n$, $\Lambda(T) \le C/\epsilon^2$; at rate 1/8 and $T = (1/4 + \epsilon)n$, and at rate 1/16 and $T = (1/8 + \epsilon)n$, $\Lambda(T) \le C/\epsilon$, with absolute constants $C$. Evidence: Theorems A, A', B, the strict-top theorems of round 1, annealing at $n = 16$ (note 02). Missing: any all-words statement, and any search for general words at $n \ge 32$ in the windows.

## 5. The second dyadic range

Here lists are strict common tops on a generic domain, and a *class at depth $t$* is a maximal family of $T$-sets sharing $e_1, \dots, e_t$. The second dyadic range is $n/16 \le t < n/8$: the classes are the classes of $(n_\varphi \bmod n/8)_\varphi$ and do not depend on $t$ in this range. A class of $T$-sets is a list of genuine codewords of degree $< T - t$ at agreement $T$, so at rate 1/2 the range is $9n/16 \le T < 5n/8$ for genuine codewords and $9n/16 + \ell \le T < 5n/8 + \ell$ for the analysis degree $k - 1 + \ell$. By complement duality (note 05 Proposition 1.3) the classes of $T$-sets and of $(n - T)$-sets correspond, and I state sizes for the smaller of the two, $|S| = n - T \in (6u, 7u]$, $u = n/16$.

### 5.1 The differences are quadrics of rank at most 4

**Proposition 5.1 (C). [proved]** Let $S \ne S'$ be in one class at depth $t \ge n/16$, $f = 1_S - 1_{S'}$, $X = S \triangle S'$. Then:

1. $\hat f(\varphi) \in \frac n4\mathbb{Z}$, so $f = \frac14 \sum_\varphi c_\varphi \chi_\varphi$ with integers $c_\varphi$, $c_0 = 0$, and $|X| = u \sum c_\varphi^2$.
2. $1_X$ is a quadratic Boolean function whose alternating form has rank $\le 4$. So $X$ is one of: an affine hyperplane; a flat of codimension 2 or its complement; the set $\{q = 1\}$ for $q = \lambda_1\lambda_2 + \lambda_3$ (three independent functionals); six or ten of the sixteen cosets of a codimension-4 subspace, namely $\{\lambda_1\lambda_2 + \lambda_3\lambda_4 = 1\}$ up to a translation, or its complement; or $\{\lambda_1\lambda_2 + \lambda_3\lambda_4 + \lambda_5 = 1\}$. In particular $|X| \in \{n/4, 3n/8, n/2, 5n/8, 3n/4\}$ (and $X = D$ only if $T = n/2$), $X$ is a function of at most 5 functionals, and $|S \cap S'| \in \{T - n/8, T - 3n/16, T - n/4, T - 5n/16, T - 3n/8\}$.
3. A class has at most $2n^5$ members.

*Proof.* (1) is the converse of Theorem W with $a = N - 4$. (2) $f \equiv 1_X \pmod 2$, so $1_X \in \mathrm{RM}(2, N)$ by Lemma 1.2 with $j = N - 2$. Also $f^2 = 1_X$, so for $\gamma \ne 0$, $\hat X(\gamma) = \frac1n \sum_\alpha \hat f(\alpha)\hat f(\alpha + \gamma) = u \sum_\alpha c_\alpha c_{\alpha + \gamma}$, and the sum is even because $\alpha$ and $\alpha + \gamma$ give the same term. So $\hat X(\gamma) \in \frac n8\mathbb{Z}$ for $\gamma \ne 0$. For a quadratic function $q$ of rank $2h$ the Walsh transform of $(-1)^q$ is $\pm 2^{N - h}$ on an affine subspace of $D^\ast$ of dimension $2h$ and zero elsewhere (Dickson), and $\hat X(\gamma) = -\frac12 \widehat{(-1)^q}(\gamma)$ for $\gamma \ne 0$. If $h \ge 1$ that affine subspace contains a nonzero $\gamma$, so $2^{N - h - 1} \in 2^{N-3}\mathbb{Z}$ and $h \le 2$. The list is Dickson's normal forms for $h \le 2$, balanced or not, and the sizes are $n/2$ and $n/2 \pm 2^{N - h - 1}$. (3) $S' = S \triangle X$ and there are at most $n^4 \cdot n \cdot 2$ functions $\lambda_1\lambda_2 + \lambda_3\lambda_4 + \lambda_5 + c$. $\square$

**[checked]** `12_class_atoms.py` on the two complete classes at $n = 64$ of section 5.2 (5755 and 3192 members): every difference from the seed is a quadric of rank $\le 4$, $\sum c^2 \in \{4, 6, 8, 10, 12\}$, and the characters $\varphi$ with $c_\varphi \ne 0$ span a space of dimension 2 to 5.

Note 04 section 6 predicted "functions of at most 14 functionals". The truth is 5 for the symmetric difference. The bound $2n^5$ replaces the exponent 12 to 14 of note 04 Theorem 2.7, and it is still far from the truth, which the next subsection shows to be linear for the classes that matter. An intermediate statement that I can prove but that has an absurd constant: for $|S| \le 7u$, with $\hat S(\varphi) = r_\varphi + 4u\,j_\varphi(S)$ and $r_\varphi \in (-2u, 2u]$ the common residues, Parseval reads $\sum_{\varphi \ne 0} (j_\varphi^2 + \frac{r_\varphi}{2u} j_\varphi) = E \le 63/16$ for every member, every term is $\ge 0$, and a functional with $|r_\varphi| < u$ costs at least $1/2$ when $j_\varphi \ne 0$. So a member is determined by its $j$ on the at most 63 functionals with $|r_\varphi| \ge u$ and by at most 7 further functionals: $|\text{class}| \le 5^{63}(4n)^7$. **[proved]**, useless numerically.

### 5.2 Two exact classes

**Theorem 5.2 (D). [proved, computer assisted]** Let $Y \le D$ have codimension 4 ($|Y| = u$), $n \ge 32$, and let $S_0$ be a union of seven cosets of $Y$. The class of $S_0$ in the second dyadic range has exactly
$$715 + 1680\,(n/16 - 1) = 105n - 965$$
members: the $715$ unions of seven cosets of $Y$ with the same label sum, and for each of the $n/16 - 1$ hyperplanes $Y'$ of $Y$, $1680$ sets that are unions of cosets of $Y'$ but not of $Y$. By complements: for $n \ge 32$ there are $105n - 965$ sets of size $9n/16$ whose locators share $e_1, \dots, e_{n/8 - 1}$ on every $\mathbb{F}_2$-subspace domain of every field of characteristic two, that is one word with $105n - 965$ genuine codewords (degree $< n/2$, in fact degree $\le 7n/16$) at agreement exactly $9n/16$. For $N = 25$: $3{,}523{,}214{,}395 = 2^{31.71}$.

*Proof.* The finite inputs are: (a) for $n = 32$ the class has 2395 members, of which 715 are invariant under $Y$ (`12_class32.py`, and independently the exhaustive `12_class ex32 14 1`); (b) for $n = 64$ the class has 5755 members (`12_class seed64`, which enumerates $S_0 + \mathrm{RM}(2, 6)$, a superset of the class by Lemma 1.2). Now let $n \ge 32$. $\hat S_0$ is supported on $Y^\perp$ (16 functionals) with $\hat S_0(\varphi) = u \cdot \mathrm{odd}$, so the residues are $r_\varphi = \pm u$ on $Y^\perp \setminus 0$ and $0$ outside. For a member $S$ write $\hat S = r + 4uj$. Parseval: $\sum_{\varphi \ne 0} \hat S(\varphi)^2 = 63u^2$. The 15 functionals of $Y^\perp \setminus 0$ contribute $u^2(1 + 8\mathbb{Z}_{\ge 0})$ each, the others $16u^2 j_\varphi^2$, so $a := \sum_{\varphi \notin Y^\perp} j_\varphi^2 \in \{0, 1, 2, 3\}$ and all these $j_\varphi$ are $0$ or $\pm 1$. Restrict $1_S$ to a coset $z + Y$: it is a $0/1$ function of $y \in Y$ with mean $G(z) = |S \cap (z + Y)|/|Y|$ and Fourier coefficients $\frac14 J_\xi(z)$, $J_\xi(z) = \sum_{\psi|_Y = \xi} j_\psi \chi_\psi(z)$, at the nontrivial characters $\xi$ of $Y$. Parseval on $Y$: $\sum_\xi J_\xi(z)^2 = 16\,G(z)(1 - G(z))$, an integer between 0 and 4 with $G(z)$ rational, so it is $0$, $3$ or $4$ for every $z$ (the values 1 and 2 give irrational $G$). If $a = 1$, $\sum_\xi J_\xi(z)^2 = 1$: impossible. If $a = 2$ with the two functionals in different classes modulo $Y^\perp$, the sum is 2: impossible. So for $a = 2$ they agree on $Y$, and $S$ is invariant under the hyperplane $Y' = Y \cap \ker\psi_1$. If $a = 3$: three in one class give $J^2 \in \{1, 9\}$, two and one give $\{1, 5\}$, so the three are pairwise distinct on $Y$, and a $0/1$ function $G + \frac14(\pm\chi_{\xi_1} \pm \chi_{\xi_2} \pm \chi_{\xi_3})$ needs $\xi_1 + \xi_2 + \xi_3 = 0$. Then $S$ is invariant under the codimension-2 subspace $Y'' = Y \cap \ker\psi_1 \cap \ker\psi_2$ of $Y$. In every case $S$ is the lift of a member of the same class on $D/Y'$ (32 points) or on $D/Y''$ (64 points): the congruences modulo $n/8$ divide by $|Y'|$ or $|Y''|$. By (b) the class on 64 points has $5755 = 715 + 3 \cdot 1680$ members, which by (a) are exactly the members invariant under one of the three hyperplanes of the 4-element group $Y/Y''$. So $a = 3$ does not occur, every member is invariant under a hyperplane of $Y$, two different hyperplanes give $Y$-invariance, and the count follows from (a). The class on 16 points is all 7-sets with a given sum, $\binom{16}{7}/16 = 715$. $\square$

The same argument with three cosets of a codimension-3 subspace is the completeness proof of note 02 section 5 ($56n - 392$).

**[checked]** Class sizes in the formal model. Exhaustive for $n = 32$ (`12_class ex32`, all sets of each size, both values of the sum), complete classes of lifted seeds for $n = 64$ (`12_class seed64`) and $n = 128$ (`12_class128`), and note 02 for $n = 16$:

| $\lvert S \rvert$ | rate-1/2 meaning of the complement | $n = 16$ | $n = 32$, largest class | $n = 64$, lifted seed | $n = 128$, lifted seed | growth |
| --- | --- | --- | --- | --- | --- | --- |
| $4u$ | none (flats at rate 1/8) | | | | | $4\binom{N}{2}_2$ affine flats of codimension 2: $n^2$, proved |
| $6u$ | $5n/8$, degree $\le n/2$ | 504 | 1400 | 3192 | 6776 | $56n - 392$, proved (note 02) |
| $6u + 1$ | $5n/8 - 1$ genuine | | 1323 | 1995 | | $35n - 245$ at $n = 64$, the count of note 02; $n = 32$ has 448 more |
| $6.5u$ | $19n/32$ genuine | | 1323 | 1995 | 3339 | $21n + 651$ on these three sizes |
| $7u$ | $9n/16$ genuine | 715 | 2395 | 5755 | 12475 | $105n - 965$, proved for this class (Theorem 5.2); $n = 128$ is an independent check of the proof |
| $7.5u$ | none (depth too small at rate 1/2) | | 4371 | 19251 | 49011 | $465n - 10509$ on these three sizes |
| $8u$ | none | | 8742 | 78246 | 661670 | faster than quadratic |

(At $n = 32$ the sizes $6u + 1$ and $6.5u$ coincide. At $n = 64$ the set of $7u + 1 = 29$ points obtained by adding a point to the seed has a class of 9315.) So in the second range the classes are quadratic in $n$ at $4u$ (flats), linear on every seed computed between $6u$ and $7.5u$, with a constant that grows with the size, and superlinear at $8u$. Only $(6u, 7u]$ is a list at rate 1/2.

**Conjecture 5.3. [conjectured]** On a generic domain, a class of $T$-sets at depth $\ge n/16$ with $9n/16 \le T < 5n/8$ has at most $105n$ members, and the maximum over the range is $105n - 965$, at $T = 9n/16$. Evidence: exhaustive at $n = 16$ and $n = 32$ (all classes), complete classes of the lifted seeds at $n = 64$ and $n = 128$, Theorem 5.2. Missing: a proof that every class, not only these seeds, is tied to a single free functional. The quadric structure of Proposition 5.1 reduces it to this: the alternating forms of the differences form a set with pairwise differences of rank $\le 4$, for a fixed form there are at most $16T/u \le 160$ admissible affine parts (Parseval for $1_{S_0}(-1)^q$, valid whenever $|X| \ne 5n/8$), and one must show that only $O(n)$ forms occur. For forms of rank 2 this follows from the count $\sum_{\gamma} \pm\hat S_0(\gamma) = 2^h |X| (2T - n)/n$ over the Walsh support of the quadric, which forces a functional with $|\hat S_0| \ge u/3$ in it. For rank 4 the same count pins only one of four dimensions.

### 5.3 Multisets and general words in the second range

Nothing is proved. At agreement exactly $5n/8$ with genuine codewords, strict tops are in the first range (at most 7), but multiset tops of mass $M > T$ have $g = M - k$ in the second range and grow with $n$: note 02 found 12 ($n = 16$) and 28 ($n = 32$) for one padded word, and the exact multiset maximum at $n = 16$ is 15 (section 2.4). Whether multiset tops between $9n/16$ and $5n/8$ stay $O(n)$ is open. Lemma 2.2 is the tool: a class with common odd set descends to a multiset top list at rate below 1/4.

### 5.4 Reconciling the counts at $9n/16$, and the budgets

All statements are for rate 1/2 in the formal model. **[proved]** unless marked.

| agreement and degree | depth | range | largest known list ($N = 25$) | upper bound |
| --- | --- | --- | --- | --- |
| $T > 5n/8$, degree $< n/2$ | $> n/8$ | first | 3, and 4 at $3n/4$ with degree $\le n/2$ | 4 (note 02 Proposition 6) |
| $T = 5n/8$, degree $< n/2$ | $n/8$ | first | 7 | 7 |
| $T = 5n/8$, degree $\le n/2$ | $n/8 - 1$ | second | $56n - 392 = 2^{30.81}$ | $2n^5$, conjectured $105n$ |
| $T = 5n/8 - 1$, degree $< n/2$ | $n/8 - 1$ | second | $35n - 245 = 2^{30.13}$ | same |
| $T = 9n/16$, degree $< n/2$ | $n/16$ | second | $105n - 965 = 2^{31.71}$ | same |
| $T = 9n/16$, degree $\le n/2$ | $n/16 - 1$ | third | $2^{102.7}$ (height-3 trees), containing in the same class the stacks ($2^{72}$) and the glued coset unions ($2^{44.8}$) | $(2n-1)^{56}$ (note 04 Theorem 2.7) |
| $T = 9n/16 - 1$, degree $< n/2$ | $n/16 - 1$ | third | a constant fraction of the previous line (members through one point) | same |

The three round-1 numbers at "$9n/16$" ($2^{44.8}$, $2^{72}$, $2^{102.7}$) are all lists in degree $\le n/2$, one coefficient above genuine: the glued word $L_U^9$ and the tree word $X^{n/2} L_U$ agree above degree $n/2$ because $L_U^8 = X^{n/2} + (\text{degree} \le n/4)$, so they are sublists of one list, whose exact size I did not determine. One agreement point higher in depth the list drops to about $2^{31.7}$. With the analysis degree $d = k - 1 + \ell$ every threshold moves up by $\ell$. So in the formal model, for strict common tops: a budget of $2^{32}$ is what $A = 9n/16 + \ell$ requires and, if Conjecture 5.3 holds, suffices; a budget between $2^{32}$ and $2^{102}$ buys nothing below that; $A \le 9n/16 + \ell - 1$ needs more than $2^{102.7}$, and $2^{75}$ (the glued count at $17n/32$) is not a threshold for anything. For the DEEP-fold accounting of note 09 this means the option "ListBound$(1/2, 9/16 + \epsilon, 100)$, 131 queries" should read "ListBound$(1/2, 9/16 + \ell/n, 32)$, about 131 queries", still conditional on general words and on the real domain.

## 6. Complement duality: what transfers between rates

Proposition 1.3 of note 05: $S \mapsto D \setminus S$ maps a strict common top family at (rate $\rho$, agreement $\tau$) with gap $g = (\tau - \rho)n$ to one at (rate $1 + \rho - 2\tau$, agreement $1 - \tau$) with the same gap, and preserves the Johnson boundary. **[proved]** there. Consequences, all for strict common tops:

| statement | at rate 1/2 | dual statement |
| --- | --- | --- |
| first range, $g \ge n/8$: differences are hyperplane swaps, $L \le 1/(2\tau - 1)^2$ (self-dual) | $\tau \in (5/8, 3/4]$ | rate $3/2 - 2\tau \in [0, 1/4)$ at agreement $1 - \tau \in [1/4, 3/8)$: the point $\tau = 11/16$ is rate 1/8 at $5n/16$, inside the rate-1/8 window |
| Proposition 5.1 (quadrics of rank $\le 4$), bound $2n^5$ | $\tau \in [9/16, 5/8)$ | rate $(1/4, 3/8]$ at agreement $(3/8, 7/16]$ |
| Theorem 5.2: $105n - 965$ | $9n/16$, degree $< n/2$ (indeed $\le 7n/16$) | $7n/16$, degree $< 3n/8$ (indeed $\le 5n/16$): a list at rate $5/16$ and agreement $7/16$, Johnson radius $0.559$ |
| $56n - 392$ (note 02, note 05 Corollary 2.3) | $5n/8$, degree $\le n/2$ | $3n/8$, degree $\le n/4$: rate 1/4 |

The windows at rates 1/8 and 1/16 are dual to rates above $0.41$ and above $9/16$, so duality connects each window to *one curve* through the $(\rho, \tau)$ plane and not to another window as a whole. The strict-top theorems do not need it: they are stated in terms of the gap and of $\min(T, n - T)$ and hold on both sides.

**What does not transfer. [proved]** Duality is a statement about $\Lambda_S \Lambda_{D \setminus S} = \Lambda_D$. For a multiset $\mu \le j \cdot 1_D$ the analogue is $\mu \mapsto j \cdot 1_D - \mu$, which keeps the gap but turns the agreement set $\mathrm{supp}\,\mu$ into $\{\mu < j\}$, so agreement is not preserved, and for words with phantom roots outside $D$ there is no complement at all. So Theorems A and A' are not dual to each other. They are two instances of the same proof (the three lemmas of section 2.1 are stated for every rate), and Theorem B is proved directly for $T \ge 5n/8$ and for $T \le 3n/8$.

**Consequences at rates 1/8 and 1/16, collected.** Rate 1/8, $n/4 < T \le 0.3536n$: strict tops $\le 4$ (note 02), words of degree $\le T + n/96$: $L \le \frac{1/4 - \theta/n}{(1/2 - \tau)^2 - \theta/n}$, between 4 and 14 for $r \le n/400$ (Theorem B), multiset tops $\le \max(15, 1 + (2\tau - \frac18)/(\tau - \frac14))$ (Theorem A'). Rate 1/16, $3n/16 \le T < n/4$: strict tops unique, words of degree $\le T + n/96$ unique as long as $T < n/4 - 3r$ (Theorem B), multiset tops $\le \max(7, 1 + (2\tau - \frac1{16})/(\tau - \frac3{16}))$ for $T > 3n/16$ (Theorem A'). Rate 1/16, $n/8 < T < 3n/16$: strict tops $\le 7$ (note 02), nothing new here.

## 7. Interleaving

By Proposition 1.1 an $h$-interleaved list on a generic domain over $F$ is a single-lane list over $F(t_1, \dots, t_h)$ with the same agreement sets, for every $h$. So in the generic model:

- (a) base field, (b) arbitrary extensions, (c) interleaved words with any number of lanes: every theorem of this note and every formal-model theorem of notes 02, 04, 05 holds in all three settings with the same bound. Nothing is lost, in particular there is no ceiling like the $2^{32}$ of note 04 Proposition 1.1.
- What the hypothesis means for an interleaved word: *strict common top* and *multiset top* require the combination $\sum_l t_l (w^l - c^l_i)$ to split over $D$, which forces all lanes to be proportional modulo codewords, so these classes are single-lane in substance. *Phantom degree $\le r$* (Theorem B) is a genuine interleaved class: every lane is a polynomial of degree $\le T + r$.
- The other direction of the brief (project a list of tuples to the lanes): the lane projections are lists with agreement sets containing the $S_i$, but distinct tuples can collide in a lane, and from per-lane bounds $\Lambda_1$ one only gets $\Lambda_1^h$ tuples. The generic combination avoids that loss, and it needs the coefficient field to be allowed to grow, which is free in the generic model and is exactly what is not free over $K$.

For the protocol this settles nothing by itself: the DEEP-fold hypothesis (note 11) is about the real domain $D_i \subset K$ and extensions of $K$ of degree up to 128, where neither genericity nor a theorem for all words is available. What it does say is that interleaving is not an extra obstacle on top of the single-lane problem: on any domain where a bound is proved uniformly over extension fields, it holds for all lane counts.

## 8. Final table (generic model)

Bounds on the number $L$ of codewords of degree $< k$ agreeing with one word on at least $T = \tau n$ points, $D$ generic. Every upper bound holds over every field containing $D$ and for any number of interleaved lanes (section 7). "None" in the all-words rows means: nothing beyond the Johnson bound, which starts at the upper end of each window.

| rate | window | class of words | best proven upper bound | best known lower bound |
| --- | --- | --- | --- | --- |
| 1/2 | $5/8 < \tau < 0.7071$, $\epsilon = \tau - 5/8$ | strict common tops | 4 (note 02), also $1/(2\tau - 1)^2$ | 3 |
| 1/2 | same | degree of the word $\le T + r$, $r \le n/96$ | $\frac{1/4 - \theta/n}{(\tau - 1/2)^2 - \theta/n}$, $\theta = 2r + 4r^2/n$ (Theorem B) | 3 |
| 1/2 | same | multiset tops | $\max(1/(16\epsilon^2),\ 1 + (2\tau - \frac12)/\epsilon)$ (Theorem A) | $3/(64\epsilon^2)$ (note 01) |
| 1/2 | same | all words | none | $\max(3,\ 3/(64\epsilon^2))$ |
| 1/2 | $9/16 \le \tau < 5/8$ (genuine) | strict common tops | $2n^5$ (Proposition 5.1); conjectured $105n$ | $105n - 965$ at $9n/16$ (Theorem 5.2), $35n - 245$ at $5n/8 - 1$ |
| 1/2 | same | multiset tops, all words | none | the line above; multisets grow with $n$ also at exactly $5n/8$ |
| 1/2 | $17/32 \le \tau < 9/16$ (genuine: up to $9n/16 - 1$) | strict common tops | $(2n-1)^{56}$ (note 04) | $\Theta(n^4)$, $2^{102}$ at $N = 25$ |
| 1/8 | $1/4 < \tau < 0.3536$, $\epsilon = \tau - 1/4$ | strict common tops | 4 (note 02) | 3 |
| 1/8 | same | degree of the word $\le T + r$, $r \le n/96$ | $\frac{1/4 - \theta/n}{(1/2 - \tau)^2 - \theta/n}$ (Theorem B) | 3 |
| 1/8 | same | multiset tops | $\max(15,\ 1 + (2\tau - \frac18)/\epsilon)$ (Theorem A') | 3 |
| 1/8 | same | all words | none | $\lfloor (n - k + 1)/(T - k + 1) \rfloor$: 6 down to 3 (trivial lists) |
| 1/16 | $3/16 \le \tau < 1/4$ | strict common tops | 1 (note 02) | 1 |
| 1/16 | same | degree of the word $\le T + r$, $r \le n/96$, $T < n/4 - 3r$ | 1 (Theorem B) | 1 |
| 1/16 | $3/16 < \tau < 1/4$, $\epsilon = \tau - 3/16$ | multiset tops | $\max(7,\ 1 + (2\tau - \frac1{16})/\epsilon)$ (Theorem A') | 1 |
| 1/16 | $3/16 \le \tau < 1/4$ | all words | none | 7 down to 5 (trivial lists) |
| 1/16 | $1/8 < \tau < 3/16$ | strict common tops | 7 (note 02) | 7 |
| 1/16 | same | multiset tops, all words | none | 14 down to 7 (trivial lists) |

Reading. Every family known to rounds 1 and 2 that grows with $n$ (flats, trees, stacks, glued coset unions, padded hyperplanes with any padding) is a strict or a multiset top, and for these classes the three windows are now closed in the formal model by theorems with small constants, except the lower half of the rate-1/16 window for multisets. The all-words rows are empty on the proof side. The lower bounds there are of constant size and come from constructions that exist on every domain.

## 9. Open problems, in order of value

1. **All words on a generic domain** (Conjecture G). The exact formulation is the rank problem of section 4.2. Lemma 4.1 is the first relation that involves three members. A proof would have to combine it over all $W$, as the proofs of the GM-MDS theorem do over merged points.
2. **$O(n)$ in the second dyadic range** (Conjecture 5.3). Reduced in section 5.2 to showing that only $O(n)$ alternating forms of rank 4 occur in a class. The energy argument of Theorem 5.2 works whenever the residues of the class are supported on a subspace, and I expect a regularity argument on the residues to do the general case.
3. **Multiset tops in the lower half of the rate-1/16 window and in the second dyadic range at rate 1/2**: the recursion on Lemma 2.2.
4. **Tightness**: is $1/(16\epsilon^2)$ attained by multiset tops at rate 1/2 (known: $3/(64\epsilon^2)$)? Does the regime $M \ge 3n/4$ of Theorem A contain any list longer than $O(1)$?
5. **Phantom degree between $n/96$ and $m$**: Theorem B stops at $r \le n/96$ because step 2 needs $6rn < (2m+2)^2$. The padded hyperplanes show that rigidity fails near $r = m$. Where it fails first is not known.
6. **An all-words search at $n = 32$ in the windows** ($k = 16$, $T = 21, 22$ and $k = 4$, $T = 9, 10, 11$), with the incremental oracle that note 02 section 9 item 3 asks for. Not done here.

## 10. Reproduction

All under `doc/whir_soundness_gap_notes/scripts/`. C with the system compiler, Python 3 without dependencies. Nothing here uses field arithmetic: by Theorem W and its converse the formal model is combinatorics of Walsh keys.

- `12_class.c`: `cc -O2 -o 12_class 12_class.c`. `./12_class ex32 T s` enumerates all $T$-subsets of $\mathbb{F}_2^5$ with XOR-sum $s \in \{0, 1\}$, keyed on $(n_\varphi \bmod 4)_\varphi$, and prints the largest classes with one representative each (the tables of section 5.2; $T = 12, \dots, 16$, a few seconds to two minutes each, up to 0.3 GB). `./12_class lift HEX32` prints the lift of a subset of $\mathbb{F}_2^5$ to $\mathbb{F}_2^6$. `./12_class seed64 HEX64 [file]` enumerates the class of a seed at $n = 64$ modulo 8 inside $S_0 + \mathrm{RM}(2, 6)$ and optionally dumps it (one second). Seeds used: `cff3c000` ($7u$, 2395 then 5755), `58851331` ($6u$, 1400 then 3192), `92151593` (13 points, 1323, lift 1995), `5885133158851333` (25 points, 1995), `f690096e` (15 points, 4371, lift 19251), `8d721be4` (16 points, 8742, lift 78246), `cff3c000cff3c001` (29 points, 9315).
- `12_class128.c`: `cc -O3 -o 12_class128 12_class128.c`, `./12_class128 HEX32`: the class at $n = 128$ (modulus 16) of the lift of a subset of $\mathbb{F}_2^5$, inside $S_0 + \mathrm{RM}(2, 7)$ ($2^{29}$ candidates, one second). `cff3c000` gives 12475, `58851331` 6776, `92151593` 3339, `f690096e` 49011, `8d721be4` 661670.
- `12_class32.py [hexseed ...]`: the class of a seed at $n = 32$ inside $S_0 + \mathrm{RM}(2, 5)$ and the number of members invariant under each translation: input (a) of Theorem 5.2 (2395 members, 715 invariant under $h = 1$, none under any other $h$). Ten seconds.
- `12_class_atoms.py members.txt hexseed`: the differences inside a dumped $n = 64$ class: Proposition 5.1. A few seconds.
- `12_multiset16.c`: `cc -O2 -o 12_multiset16 12_multiset16.c`, `./12_multiset16 k T`: all multisets on $\mathbb{F}_2^4$ with multiplicities $\le 2$, exact multiset top lists per mass, and the parity check of Lemma 1.2 (section 2.4). About 20 seconds per $(k, T)$, 0.7 GB.
