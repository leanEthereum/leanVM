# 21. Referee report on the coding-theory theorems (lists below the Johnson radius)

Researcher 21 (independent referee). I read the proofs of notes 00, 01, 02, 04, 05, 12, 13, 14 (section 7) and 19 as a hostile reader and re-verified the numerics with code written from scratch (`scripts/21_*`; no script of another researcher is called, and I looked at their outputs only to compare numbers). Tags: **[proved]** means that I checked the written proof line by line and found it complete (or completed it here); **[checked]** means verified numerically by my own code on the sizes stated; **[quoted]** means taken from a paper or note that I did not verify; **[conjectured]** as usual. Notation as in `09-round1-synthesis.md`: $F$ a field of characteristic two, $D \subset F$ an $\mathbb{F}_2$-subspace of dimension $N$, $n = 2^N$, $k = \rho n$, genuine codewords have degree $< k$, "slack $\ell$" means degree $\le k - 1 + \ell$ (the analysis degree $d$). A family of $T$-sets has *depth* $g$ if its locators share $e_1, \dots, e_g$; it is then a list at agreement $T$ in degree $\le T - g - 1$. "Generic" means that a basis of $D$ is algebraically independent over $\mathbb{F}_2$ (the formal model). No subspace of a finite field is generic, so a "generic" upper bound is a statement about families that share their top on every domain, and says nothing by itself about the lists of $D_{\kappa,R} \subset K$.

## 0. Verdicts

| # | claim | source | verdict | independent check |
| --- | --- | --- | --- | --- |
| 1 | Flats lemma | 00 section 1 | correct | all 127 and 255 hyperplanes at $N = 7, 8$ and samples at rates 1/8, 1/16 |
| 2 | $56n - 392$ polynomials of degree $\le n/2$ at agreement $5n/8$ with the word $L_U^5$; $35n - 245$ genuine at $5n/8 - 1$; $7n - 35$ at up to $5n/8 + \ell - 1$ with slack $\ell$ | 02 Thm 5, 05 Thm 2.1, 01 | correct as lower bounds on every subspace domain; "exactly" holds in the formal model and at $n = 32$ on the leanVM shape; one wrong explanatory sentence in note 02 (section 5, item E1) | both descriptions enumerated at $N = 5, 6, 7$, identical sets; exact classes at $n = 32, 64, 128$; exact list on real-shape and random domains at $n = 32$ |
| 3 | $56n - 392$ against $21n - 140$ | 02, 05, 01 | reconciled: $21n - 140 = M_2(N)$ counts the members that contain one fixed coset of $U$ (minus the 7 that are coset plus hyperplane); the class of the word uses all eight cosets | counted at $N = 5, 6, 7$ |
| 4 | $105n - 965$ genuine codewords at agreement exactly $9n/16$ | 12 Thm 5.2 | correct, on every subspace domain as a lower bound, exact in the formal model | classes re-enumerated at $n = 32, 64, 128$; tops multiplied out in $K$ |
| 5 | Class sizes at $9n/16$ | 00, 02, 05, 01, 12 | reconciled (section 2.3): they live at three different depths | $n = 16, 32$ tables reproduced |
| 6 | Biased padding at about $0.629n$ | 01 section 3.4 | correct with changes: the explicit set has $1008n/4096$ points, not $n/4$, so its 1008 codewords are genuine; $3/(64\epsilon^2)$ is a cap of the mechanism, not an achieved size (E3). Sharpened here to a closed form: $(4^{m'} - 2^{m'})/4$ genuine codewords at $(5/8 + 2^{-m'-2})n$, proved | Walsh spectrum recomputed for $m' = 4..10$ |
| 7 | Theorem W and its converse | 02 section 2 | correct | exhaustive: sets at $N = 4$, multisets at $N = 3, 4$ |
| 8 | Strict common tops above $5n/8$: at most $1/(2\tau - 1)^2$ | 02 Prop 6, 04 Cor 2.5, 05 Thm 6.3 | correct, not sharp (the sharp generic value is 4), and the hypothesis is depth $\ge n/8$, that is $T \ge 5n/8 + \ell$ with slack $\ell$ (E2) | all classes at $n = 32$ |
| 9 | Theorems A, A' (multiset tops) | 12 section 2 | correct | all multisets with support $\ge T$ at $n = 16$, masses up to 17 |
| 10 | Theorem B (phantom degree $\le n/96$) | 12 section 3 | correct; the summary row omits the hypothesis $m + r < n/4$ (E4); vacuous for $n < 96$, so not testable by brute force | hand check; the congruence it rests on (04 Thm 2.4) checked with one phantom root at $n = 16$ |
| 11 | Interleaving costs nothing on a generic domain | 12 Prop 1.1 | correct, with the caveat stated there (strict and multiset tops are single-lane classes in substance) | hand check |
| 12 | Sparse top keys, pigeonhole is exact | 13 Prop 3.1, Cor 3.2 | correct; "bits of coincidence" in part 3 is an accounting, not a bound (E6) | 60 pairs of lattice elements, three domains |
| 13 | Interleaving on the real domain | 13 Prop 3.4, 3.5; 14 Prop R2', Thm I | correct | hand check; recursion values recomputed |
| 14 | Fibres of at most 3591 on the $5n/8$ class | 13 Prop 4.1 | correct (irreducibility and the Bezout count hold); far from tight | masks, Lemma 2.1, the curve; fibres in $\mathrm{GF}(2^9), \mathrm{GF}(2^{10}), \mathrm{GF}(2^{12})$ |
| 15 | Dual criterion, dual BCH bound | 19 Thm 1, 2 | correct | exhaustive at $n = 32$ in fields of 32 to 4096 elements, 138 runs, no failure |
| 16 | List bounds inside one previous-level class, constants $4{,}107{,}099{,}165$ and $2^{36}$ | 19 Thm 3a, 3b, 3c | correct; they bound a list only up to the unbounded factor $M(w)$, as the note says | constants recomputed; cells at $n = 32$ |
| 17 | The real domain is not generic | 19 Prop 5.1 | correct | $c_1(V) = c_1(V')$ recomputed for $N = 25..28$, same hexadecimal values |

**No claim in the list is false.** I found no gap in any proof. The corrections are about explanations, hypotheses and what counts as a lower bound; they are listed in section 5 (E1 to E8). The table of what is actually proved is section 6.

## 1. What I did and did not do

Code. `21_gf.py` ($\mathrm{GF}(2^m)$ on Python integers), `21_attack_checks.py`, `21_nine16_checks.py`, `21_real_checks.py`, and three C programs: `21_walsh.c` (classes in the formal model, by the Walsh criterion only), `21_multiset16.c` (multiset tops at $n = 16$), `21_dual32.c` ($n = 32$ exhaustive in small fields, note 19). All fields are built from scratch; $K$ uses the modulus $x^{64} + x^4 + x^3 + x + 1$. Outputs are in `scripts/21_results.txt`.

Not done. I did not obtain [DKTZ26], so the count $M_3(N)$ of height-3 trees ($2^{102.7}$ at $N = 25$) stays **[quoted]**; everything that depends on it is marked. I did not referee the DEEP fold (notes 07, 10, 11, 14 sections 1 to 6), the all-words notes 15 to 18, the experiments and "Law P" of note 13 sections 4.2 to 6 (I reran nothing at $N = 25$ except Proposition 5.1 of note 19), or the pinning bound of note 04 (Proposition 1.3). From note 04 I checked by hand only what the later notes use: Lemmas 2.1 and 2.2, Theorems 2.3, 2.4 and 2.7, Corollary 2.5. Nothing was run above $n = 128$ except identities that need $O(N^2)$ field operations.

## 2. Attack side

### 2.1 Flats (note 00, section 1)

**Statement.** $F$ any field of characteristic two, $D \subset F$ any $\mathbb{F}_2$-subspace, $V \le D$ a subspace of size $2^s$. Then $Q_V = (L_V - X^{2^s})/X$ has degree $2^{s-1} - 1$ and $Q_V(x) = x^{2^s - 1}$ exactly for $x \in V \setminus 0$. With $s = \kappa + 1$: the single word $x^{2k-1}$ has the $\binom{N}{R-1}_2$ genuine codewords $Q_V$ at agreement $2k - 1 = 2\rho n - 1$, pairwise distinct. Single lane, word and codewords over the field generated by $D$. With slack 1 (degree $\le k$) the $2^{R-1}\binom{N}{R-1}_2$ affine flats agree with $x^{2k}$ on $2k$ points; with slack $\ell$ the flats that avoid a fixed $(\ell - 1)$-set $A$ give agreement $2k + \ell - 1$ with the word $x^{2k} Z_A$.

**Verdict: correct. [proved]** ($L_V$ is linearized; for $x \ne 0$, $Q_V(x) = x^{2^s - 1}$ iff $L_V(x) = 0$.)

**Check. [checked]** `21_attack_checks.py flats`, leanVM shape in $K$: all 127 hyperplanes at $N = 7$ and all 255 at $N = 8$ (rate 1/4), 60 random subspaces each at $(N, \rho) = (7, 1/8)$ and $(8, 1/16)$. Agreement is exactly $V \setminus 0$, the $Q_V$ are distinct, the Gaussian binomials match an explicit enumeration of subspaces.

**Remark on "Johnson is tight at rate 1/4" (E5).** At $T = n/2 - 1$, $T^2 - n(k - 1) = 1 > 0$, so the classical Johnson bound applies at the flats' agreement and gives $n(T - k + 1)/(T^2 - n(k-1)) = n^2/4$. The flats are therefore a list of size $n - 1$ one point *inside* the range of the Johnson bound, not a list beyond it. The conclusion for the protocol is unchanged (no budget below $2^N - 1$ allows $A \le n/2 - 1$), but the table should not present flats at rate 1/4 as a beyond-Johnson example.

### 2.2 The $5n/8$ class at rate 1/2 (note 02 Theorem 5, note 05 Theorem 2.1, note 01 section 3.3)

**Statement.** $F$, $D$ arbitrary as above, $N \ge 4$, $U \le D$ with $|U| = n/8$. Let $\mathcal{F}_U$ be the set of $S \subseteq D$ that are five cosets of $U$, or the disjoint union of an affine flat of size $n/4$ whose direction does not contain $U$ and three cosets of $U$. Equivalently (note 02): for a hyperplane $W$ of $U$, the unions of ten cosets of $W$ whose ten labels in $L_W(D)$ sum to the nonzero element $\eta_W$ of $L_W(U)$. Then:

1. $|\mathcal{F}_U| = 56n - 392$, every member has $5n/8$ points, and $\deg(L_U^5 - Z_S) \le n/2$. So the word $L_U^5$ (equivalently $X^{n/2}L_U$, same coefficients above degree $n/2$) agrees on exactly $5n/8$ points with $56n - 392$ distinct polynomials of degree $\le n/2$ (slack 1). **[proved]**, every subspace domain, single lane.
2. For $p \in D$ the $35n - 245$ members through $p$ give genuine codewords at agreement $5n/8 - 1$ with the word $(L_U^5 - L_U(p)^5)/(X - p)$. **[proved]**
3. For a set $A$ of $j \le \ell - 1$ points in one coset of $U$, the $7n - 35$ members that avoid that coset, each enlarged by $A$, agree with $L_U^5 Z_A$ on $5n/8 + j$ points in degree $\le n/2 + j$. **[proved]** So with the analysis degree $d = k - 1 + \ell$ lists of size $7n - 35$ exist up to agreement $5n/8 + \ell - 1$.
4. In the formal model $\mathcal{F}_U$ is the whole class of its word: no other $5n/8$-set shares $e_1..e_{n/8-1}$ with it. **[proved]** I completed the sketch of note 02: the complement $S'$ has, in units of $n/8$, odd Walsh values on $U^\perp$ (3 at 0) and even values elsewhere, with $\sum v^2 = 24$; so either $S'$ is $U$-invariant or exactly two functionals $\psi_1, \psi_2 \notin U^\perp$ carry $\pm 2$; restricting $1_{S'}$ to a coset of $U$, its nontrivial Fourier coefficients are $\pm\frac14$ at $\psi_1|_U$ and $\psi_2|_U$, and Parseval on $U$ ($G(1 - G) = \sum \text{coefficients}^2$ with $G$ rational) excludes $\psi_1|_U \ne \psi_2|_U$; so $S'$ is invariant under $W = U \cap \ker\psi_1$ and is a lift from 16 labels.

What is **not** proved: that $\mathcal{F}_U$ is the whole list of $L_U^5$ on the real domain $D_{24,1}$ (conjecture C3 of note 02), and the exact size of the genuine list at $5n/8 - 1$ in general.

**Verdict: correct. One explanatory sentence of note 02 is wrong (E1).**

**Checks. [checked]** `21_attack_checks.py five8 7`: for $N = 5, 6, 7$ and a random $U$ the two descriptions give the same sets, $1400$, $3192$, $6776$ of them; $875$, $1995$, $4235$ contain a given point; $189$, $413$, $861$ avoid a given coset. With field arithmetic in $K$ on the leanVM shape and on a random basis: every member ($N = 5, 6$; 400 random members at $N = 7$) has the top of $L_U^5$ down to $e_{n/8-1}$, and for three members per case the full polynomial $L_U^5 - Z_S$ has degree $\le n/2$ and agrees with the word on exactly $5n/8$ points. `21_walsh rm2`: the formal class of three cosets of $U$ (complements) has exactly $1400$, $3192$, $6776$ members at $n = 32, 64, 128$, of which 56 are $U$-invariant, and the class at $5n/8 - 1$ (three cosets plus a point) has $1323$, $1995$, $4235$: so $35n - 245$ is exact in the formal model at $n = 64, 128$, and $n = 32$ has 448 more (members where the punctured point is a double root; a small-size effect). `21_walsh classes32`: $1400$ is the largest class of all 12-sets of $\mathbb{F}_2^5$ modulo 4. `21_attack_checks.py mitm` (exact count over all $\binom{32}{20}$ sets by meet in the middle, in $K$): the list of $L_U^5$ in degree $\le 16$ has exactly 1400 members on the leanVM shape $\mathrm{span}(1..x^4)$ and on two random bases; in degree $< 16$ it has 7 (random) and 9 (leanVM shape, this $U$); the punctured word has 1323 genuine codewords at agreement 19 on all three.

**Reconciling $56n - 392$ with $21n - 140$.** Fix one coset $C_0$ of $U$. The members of $\mathcal{F}_U$ that contain $C_0$ number $21n - 133$ (checked: 539, 1211, 2555). Seven of them are $C_0$ plus an affine hyperplane; the other $21n - 140 = 28(6 \cdot 2^{N-3} - 5) = M_2(N)$ are $C_0$ plus the support of a height-2 tree avoiding $C_0$, which is the count that note 01 takes from [DKTZ26] (checked: 532, 1204, 2548). Every non-invariant member contains exactly three cosets of $U$ and every invariant one five, so $8(21n - 133) = 3(56n - 448) + 5 \cdot 56$. So: $21n - 140$ is the number of list members *for one padding coset*; $56n - 392$ is the list of the word, which does not care which coset is called padding. Both are right, and the second is the relevant one.

### 2.3 Agreement $9n/16$ (note 12 Theorem 5.2 and section 5.4)

**Statement (note 12, Theorem 5.2).** $D$ arbitrary, $n \ge 32$, $Y \le D$ of size $n/16$. The sets of size $7n/16$ that are (i) unions of seven cosets of $Y$ with a given label sum (715), or (ii) for a hyperplane $Y'$ of $Y$, lifts of the 1680 non-invariant members of the 32-point class, number $715 + 1680(n/16 - 1) = 105n - 965$. Their complements are $105n - 965$ sets of $9n/16$ points sharing $e_1..e_{n/8 - 1}$ on every subspace domain: one monic word of degree $9n/16$ with that many codewords of degree $\le 7n/16$ (so genuine at rate 1/2) at agreement exactly $9n/16$. In the formal model this is the whole class.

**Verdict: correct. [proved, computer assisted]** As a lower bound on every domain the only inputs are Theorem W and the number 2395 at $n = 32$. I checked that lifts stay in the class: for $\varphi \notin Y'^\perp$, $n_\varphi(S) = |S|/2 = 7n/32$, and for $\varphi \in Y'^\perp \setminus Y^\perp$, $n_\varphi(S) = |Y'| n'_\varphi \equiv 7|Y'| = 7n/32 \pmod{4|Y'| = n/8}$. The exactness proof (Parseval on a coset of $Y$, values $0, 3, 4$ only) is correct and uses the two enumerations $2395$ and $5755$.

**Checks. [checked]** `21_walsh rm2`: 2395 (715 invariant), 5755 (715), 12475 (715) at $n = 32, 64, 128$, inside $S_0 + \mathrm{RM}(2, N)$, which contains the class by Lemma 1.2 of note 12 (proof checked). `21_walsh classes32 14 4`: 2395 is the largest class of all 14-sets with odd label sum, by brute force over all sets, without Lemma 1.2. `21_nine16_checks.py`: every member is invariant under $Y$ (715) or under exactly one hyperplane of $Y$ ($1680(n/16-1)$); in $K$, on the leanVM shape and on a random basis, all complements at $n = 32, 64$ and 1500 random ones at $n = 128$ share $e_1..e_{n/8-1}$. `21_attack_checks.py mitm`: on a random basis at $n = 32$ the class of the 18-point seed has 2395 members at depth 2 and at depth 3; on the leanVM shape $\mathrm{span}(1..x^4)$ it has 38375 at depth 2 (the toy-size effect of note 02: $e_2$ lies in a 9-dimensional space) and 2395 at depth 3.

**Reconciling the class sizes quoted at "$9n/16$".** All are correct; they are at different depths and different $n$.

| quoted number | where | what it is | status |
| --- | --- | --- | --- |
| 715 genuine, 11440 with slack | 00, at $n = 16$ | $T = 9 = k + 1$: depth 1 (all 9-sets with a given sum, $\binom{16}{9}/16$) and depth 0 (all 9-sets). $105n - 965 = 715$ at $n = 16$ | checked |
| $105n - 965 = 2^{31.7}$ | 12 | genuine, agreement exactly $9n/16$, depth $n/16$ (second dyadic range) | proved, checked |
| $2^{44.8}$ | 02 Theorem 5, $M' = 16$ | degree $\le n/2$ at $9n/16$, depth $n/16 - 1$: $11440 + (n/16 - 1)(14732720 - 11440)$ | proved; $\nu = 14732720$ recounted, 30 members checked in $K$ at $N = 7$ |
| $(2^{N-1} - 2)^3 = 2^{72}$ | 05 Proposition 3.1 | degree $\le n/2$ at $9n/16$, same depth, another sublist of the same kind | proved; 40 members checked at $N = 6, 7$ |
| $2^{102.7}$ | 01, from [DKTZ26] | height-3 trees, degree $\le n/2$ at $9n/16$ | quoted, not verified by anyone in the project |

So for genuine codewords the proved lower bound drops from at least $2^{72}$ at $9n/16 - 1$ to $105n - 965$ at $9n/16$, and with the analysis degree every threshold moves up by $\ell$. Note 12 section 5.4 says this correctly. The statement "budgets between $2^{32}$ and $2^{102}$ buy nothing" there is **[conjectured]** (it needs Conjecture 5.3, all words, and the real domain).

### 2.4 Biased padding (note 01, section 3.4)

**Statement.** $D$ arbitrary, $B \subseteq D$ any set, $H$ an affine hyperplane. The word $X^{n/2}L_B$ agrees with $L_B(L_H - X^{n/2})$, of degree $\le |B| + n/4$, exactly on $H \cup B$. For the better coset, $|H \cup B| = n/2 + (|B| + |\hat B(a)|)/2$.

**Verdict: correct with two changes.** (i) The explicit set (labels $(x, y) \in \mathrm{GF}(64)^2$ with the two low bits of $xy$ equal to 11, lifted through a subspace of codimension 12) has $|B| = 1008n/4096$, not $n/4$ as the text says. The numbers are right: 1008 directions with $|\hat B| = 48n/4096$, agreement $161n/256 = 0.62891n$. Because $|B| < n/4$ the codewords have degree $\le 0.4961n$: **they are genuine codewords**, which the note does not say. (ii) $3/(64\epsilon^2)$ is an upper cap for this mechanism (Parseval), not a list size that is reached. See E3.

**The family in closed form. [proved]** Let $q = 2^{m'}$, $2m' \le N$, identify a quotient of $D$ of dimension $2m'$ with $\mathrm{GF}(q)^2$, and let $B$ be the preimage of $\{(x, y) : \mathrm{Tr}(c_0xy) = \mathrm{Tr}(c_1xy) = 1\}$ with $1/c_0, 1/c_1, 1/(c_0 + c_1)$ independent over $\mathbb{F}_2$ (any $c_0 \ne c_1$ if $m'$ is odd; $c_0/c_1 \notin \mathrm{GF}(4)$ in general). Then $1_B = \frac14(1 - \chi_{c_0} - \chi_{c_1} + \chi_{c_0 + c_1})$ with $\chi_c = (-1)^{\mathrm{Tr}(cxy)}$, and $\hat\chi_c(a, b) = q(-1)^{\mathrm{Tr}(ab/c)}$ (sum over $y$ first). So $|B| = (q^2 - q)/4$ labels, and for $(a, b) \ne 0$, $|\hat B(a, b)| = 3q/4$ exactly when $(\mathrm{Tr}(u/c_0), \mathrm{Tr}(u/c_1), \mathrm{Tr}(u/(c_0 + c_1)))$, $u = ab$, is $(0, 0, 1)$ or $(1, 1, 0)$: $q/4$ values of $u \ne 0$, each with $q - 1$ pairs $(a, b)$. Hence: **on every subspace domain with $N \ge 2m'$ one word has $(4^{m'} - 2^{m'})/4$ genuine codewords (degree $\le n/2 - n/2^{m'+2}$) at agreement $(5/8 + 2^{-m'-2})n$.** In terms of $\epsilon = \tau - 5/8$ this is $L = 1/(64\epsilon^2) - 1/(16\epsilon)$. At $N = 25$, $m' = 12$: $4{,}193{,}280 = 2^{22.0}$ genuine codewords at agreement $5n/8 + 2^{11}$. In particular the genuine list at exactly $5n/8$ grows at least like $n/8$ (like $n/4$ for even $N$), which settles the question left open in note 02 section 6 ("at least about $n$, not 7") and in note 12 section 5.3.

**Checks. [checked]** `21_real_checks.py padding`, for $m' = 4..8$ with the two low bits of $xy$ in the polynomial basis: $(|B|, L, \tau) = (60, 60, 41/64)$, $(248, 248, 81/128)$, $(1008, 1008, 161/256)$, $(4064, 4064, 321/512)$, $(16320, 16320, 641/1024)$; also $m' = 9, 10$ in a one-off run ($65408$ and $261888$ directions). $L\epsilon^2 \to 1/64$. `21_real_checks.py padfield`, end to end in $K$ on the leanVM shape at $N = 8$, $m' = 4$: 60 distinct codewords of degree $\le 124 < k = 128$, each agreeing with the one word $X^{n/2}L_B$ on exactly $164 = 41n/64$ points. Random $B$ of density exactly $1/4$ on a 14-dimensional quotient: the 1024-th largest $|\hat B|$ is 102, so $2^{10}$ polynomials of degree $\le n/2$ at $0.6281n$, as note 01 says. The identity itself: $N = 8$, random $B$ of 64 and of 61 points, three hyperplanes each, degree and exact agreement.

Query floors: $\lceil 108/\log_2(n/T)\rceil$ is 160 at $5/8$, 161 at $321/512$ (4064 genuine members) and at $0.6281$ ($2^{10}$ members in degree $\le n/2$), 162 at $161/256$ (1008 genuine members, which is just below $2^{10}$). So the main document's floor "160, 161 with the padding family" stands.

## 3. Rigidity on generic domains

### 3.1 Theorem W (note 02, section 2)

**Statement.** $D$ any subspace of any field of characteristic two, $c, c' : D \to \mathbb{Z}$ with $n_\varphi(c) \equiv n_\varphi(c') \pmod{2^{a+1}}$ for every functional $\varphi$ (equivalently, for equal masses, Walsh transforms congruent modulo $2^{a+2}$). Then $e_j(c) = e_j(c')$ for all $j < 2^{a+1}$. Converse, on a generic domain only: if $e_j(c) = e_j(c')$ for $j \le t$ and $2^a \le t$, then $n_\varphi(c) \equiv n_\varphi(c') \pmod{2^{a+1}}$. So on a generic domain the classes at depth $t$ are the same for all $t$ in $[2^a, 2^{a+1})$. Sets and multisets alike.

**Verdict: correct. [proved]** Each step of the proof holds: the basis $\varepsilon_A$ of the group ring and the divisibility $2^{\max(0, m - |A|)} \mid \gamma_A$; $\Pi(\varepsilon_A) \equiv 1$ modulo degree $2^{|A| - 1}$ because every homogeneous component is divisible by the $2^{|A|-1}$ distinct linear forms $\ell_\beta$; Frobenius. The equal-mass hypothesis is harmless: the point 0 contributes neither to $e_j$ nor to $n_\varphi$. The main document's sentence ("two sets share $e_1..e_{2^{a+1}-1}$ exactly when their Walsh spectra agree modulo $2^{a+2}$") needs the words "of equal size, on a generic domain; the implication from Walsh to tops holds on every domain".

**Checks. [checked]** `21_attack_checks.py thmw`: random basis in $K$, $N = 4$, all subsets, all $T$, $t \le 7$ (119 cells): the two partitions are equal. Forward direction on the leanVM shape in $K$ and on $D = \mathrm{GF}(16)$: no violation. Multisets: $N = 3$, multiplicities $\le 4$, all masses, $t \le 7$ (203 cells), and $N = 4$, multiplicities $\le 2$, mass $\le 7$ (114084 multisets, 40 cells): partitions equal.

### 3.2 Strict common tops in the windows (note 02 Proposition 6, note 04 Corollary 2.5, note 05 Theorem 6.3)

**Statement.** $D$ generic, single lane, word monic of degree $T$ with $w - c_i = Z_{S_i}$ (strict common top), depth $g = T - k - \ell$.

- Rate 1/2, $g \ge n/8$, $5n/8 < T$: at most 4 members (note 02), in particular at most $1/(2\tau - 1)^2$ (notes 04, 05); every two members differ by a swap of two cosets of a codimension-2 subspace. At $T = 5n/8$, $g = n/8$: at most 7, attained. For $T > 3n/4$: one.
- Rate 1/8, $n/4 \le T < 3n/8$, $g \ge n/8$: at most 4 (note 02); note 05 gives 11.
- Rate 1/16: at most 8 for $n/16 \le g < n/8$ and $T < 3n/16$ (7 if $T > n/8$); exactly 1 for $g \ge n/8$, $T < n/4$.

**Verdict: all three notes are correct. The bound $1/(2\tau - 1)^2$ that the main document quotes is the weakest of the three.** Note 02's argument is the sharp one: every other member is $S_0 - A_i + B_i$ with $B_i \subseteq D \setminus S_0$, two distinct flats of size $n/4$ cover at least $3n/8$ points, and $|D \setminus S_0| < 3n/8$, so $B$ is unique and $A_i$ is one of the three other cosets of its direction. See E2 for the hypothesis in the analysis degree.

**Checks. [checked]** `21_walsh classes32`: all $s$-subsets of $\mathbb{F}_2^5$, $s = 3..16$, moduli 4, 8, 16, largest class for each (by complement this is the table of note 02 for the random domain, all four rates). Every entry of that table is reproduced: rate 1/2, $T = 18..24$ genuine: $2395, 1323, 7, 3, 3, 3, 1$, and with slack 1: $1400$ at 20, $4$ at 24; rate 1/4, $T = 10..16$: $513, 589, 7, 7, 15, 31, 2$; rate 1/8, $T = 6..12$: $35, 155, 4, 3, 3, 3, 1$; rate 1/16, $T = 4..8$: $8, 7, 1, 1, 4$. So in the window at rate 1/2 the largest strict class at $n = 32$ has 3 members (bound 4).

### 3.3 Theorems A and A' (note 12, section 2)

**Statement.** $D$ generic, single lane, any field. A *multiset top list*: one polynomial representative $w$ of the word, of degree $M$, with $w - c_i = \lambda Z_{\mu_i}$, $\mu_i$ multisets on $D$ of mass $M$, $\deg c_i < k$, agreement sets $\mathrm{supp}\,\mu_i$ of size $\ge T$. (A) Rate 1/2, $T = (5/8 + \epsilon)n$, $\epsilon > 0$: $L \le n^2/(4T - 2M - n)^2 \le 1/(16\epsilon^2)$ if $M < 3n/4$, and $L \le 1 + (2\tau - \frac12)/\epsilon$ if $M \ge 3n/4$. (A') $\rho \le 1/8$, $T = (\rho + \frac18 + \epsilon)n < n/2$: $L \le \max(\lceil 1/(1/2 - 2\rho)^2\rceil - 1,\ 1 + (2\tau - \rho)/\epsilon)$.

**Verdict: correct. [proved]** I checked Lemma 1.2 (parity: $\hat f \in 2^j\mathbb{Z}$ implies $f \bmod 2 \in \mathrm{RM}(N - j, N)$), Lemma 2.1, Lemma 2.2 (Frobenius descent: $Z_{\mu_i} - Z_{\mu_j} = Z_O(v_i - v_j)^2$, then the Johnson count for the sets $R_i$, and the minimisation over $\omega$ that produces $5/8$), Lemma 2.3 and the two case distinctions. With slack $\ell$ the theorem applies with $k$ replaced by $k + \ell$, so its window starts at $T > 5n/8 + \ell$. Theorem A' does not cover rate 1/16 on $(n/8, 3n/16]$, as the note says.

**Checks. [checked]** `21_multiset16`: all multisets on $\mathbb{F}_2^4$ with support $\ge T$ (any multiplicities), each mass separately, grouped by the Walsh key. $(k, T) = (8, 11)$, masses 11 to 17: largest classes $3, 1, 1, 2, 3, 1, 1$ (bounds 7 for $M = 11$, 15 for $M \ge 12$). $(8, 10)$: $7, 15, 2, 2$ for $M = 10..13$ (no bound at $\epsilon = 0$; the 15 at $M = 11$ is the number of note 12). $(8, 12)$: 1 for $M = 12..16$. $(2, 5)$: $3, 1, 1, 2, 3, 1, 1$ for $M = 5..11$ (bound 15, then 9). $(2, 4)$: $4, 4, 1, 1, 4, 4$. With slack 1 (degree $\le 8$, entered as $k = 9$): $(9, 11)$: $3, 16, 1, 2$ for $M = 11..14$, and $(9, 12)$: $4, 1, 1, 1$. The 16 at $T = 11 = 5n/8 + \ell$ is the list that note 18 reports for all words; it is the image, under multiplication by one linear factor, of the genuine multiset lists at exactly $5n/8$, and it is the reason the window of Theorem A starts strictly above $5n/8 + \ell$ in the analysis degree. All agree with the table of note 12 section 2.4 where it has entries. This is weak evidence (the bounds are not approached at $n = 16$); the proof is what carries the statement.

### 3.4 Theorem B (note 12, section 3) and the dichotomy of note 04

**Statement.** $D$ generic, any field, lists $(w; c_i; S_i)$ with $w$ a polynomial of degree $T + r$, $|S_i| = T$, $\deg c_i < k$, $m = T - k \ge n/8$, $T \ge 5n/8$ or $T \le 3n/8$, $r \le n/96$ **and $m + r < n/4$**. Then any two members differ from a hyperplane swap in at most $4r + 8r^2/n$ points and $L \le (n/4 - \theta)/((T - n/2)^2/n - \theta)$, $\theta = 2r + 4r^2/n$, when the denominator is positive. For interleaved words it is enough that every lane has degree $\le T + r$ (Proposition 1.1).

**Verdict: correct. [proved]** I checked the two results of note 04 it rests on (Lemma 2.2: specialization at the place of $W$ with the Gauss valuation; Theorem 2.3: $\delta_W \le r$ or $\delta_W \ge m + 1$; Theorem 2.4: the congruence $d_\varphi \bmod 2^{a+1} \in [-r, r]$) and the seven steps of the proof (spectral form of the dichotomy, minimal high subspaces have dimension 1, at most three big coefficients, averaging over complements, parity forces exactly two, the sharp count). The summary table of note 12 drops the hypothesis $m + r < n/4$ (E4). The theorem needs $n \ge 96$ to allow $r = 1$, so it cannot be tested exhaustively.

**Check. [checked]** `21_real_checks.py phantom`: $n = 16$, random domain in $K$, all pairs of $T$-sets joined by at most one phantom root on each side (solving for the roots), for $(T, k) = (12, 10), (12, 9), (5, 3), (4, 2)$: $90930$, $43680$, $399000$ and $90930$ pairs (of which $210$, $0$, $1680$, $210$ are strict; the same counts as note 04 reports), and every pair satisfies the congruence of Theorem 2.4 of note 04 ($|d \bmod 4| \le 1$) for all 15 functionals.

### 3.5 Interleaving on a generic domain (note 12, Proposition 1.1)

**Statement.** If $D \subset F$ is generic and an $h$-lane word over $F$ has $L$ list members (tuples) with agreement sets $S_i$, then the single word $\sum_l t_l w^l$ over $F(t_1..t_h)$ has $L$ list members with the same agreement sets, and $D$ is generic in $F(t)$. So any bound proved for all fields containing a generic $D$ holds for all lane counts.

**Verdict: correct. [proved]** The caveat in the note is necessary and correctly stated: the *class of words* must be preserved by the combination. Phantom degree $\le r$ is (lane by lane); strict and multiset tops force all lanes to be proportional modulo codewords. So "interleaving costs nothing" is a statement about bounds that hold uniformly over extension fields, on generic domains only.

### 3.6 Also checked in note 12

Proposition 5.1 (differences in the second dyadic range are quadrics of rank $\le 4$; at most $2n^5$ members): **[proved]**, correct. Conjecture 5.3 ($105n$) stays a conjecture; at $n = 32$ my enumeration gives the same maxima as note 12 ($1400$, $1323$, $2395$, $4371$, $8742$ for $|S| = 12..16$).

## 4. The real domain

### 4.1 Sparse top keys and the pigeonhole (note 13, Proposition 3.1 and Corollary 3.2)

**Statement.** $D$ any subspace of any field, $L_e = \{c \in \mathbb{Z}^D : \sum c = 0,\ \hat c \equiv 0 \bmod 2^{e+1}\}$. For $c \in L_e$, $\Lambda_c \equiv 1 + \sum_{i=0}^{e}\theta_i(c)X^{2^{e+1} - 2^{e-i}} \pmod{X^{2^{e+1}}}$ with additive $\theta_i$. Hence inside a set $\mathcal{F}$ of multisets pairwise congruent modulo $L_e$, the classes of the concrete domain at depth $g \in [2^e, 2^{e+1})$ are the fibres of an explicit map to $F^{i(g)}$, and some class has at least $|\mathcal{F}|/|F|^{i(g)}$ members.

**Verdict: correct. [proved]** (generators from Theorem W; $\Lambda_{\varepsilon_A}^{\pm1} \equiv 1 + \delta_A X^q(1 + c_1X^{q/2} + \dots)$ modulo $X^{2q}$; Frobenius; additivity of $1 + O(X^{2^e})$ modulo $X^{2^{e+1}}$). Part 3 of the corollary proves that $e' + 1$ field elements vanish for a deep accident; calling this "$64(e'+1)$ bits of coincidence" is an accounting (E6). The consequence "$2^{38.7 - 1.1j}$ genuine codewords at $9n/16 + j$ on $D_{24,1}$" is proved *given* $M_3(N)$ from [DKTZ26] (E7).

**Check. [checked]** `21_real_checks.py sparse`: 60 pairs of random elements of $L_e$, $N = 5, 6$, all levels, leanVM shape in $K$, random basis in $K$, random subspace of $\mathrm{GF}(2^8)$: support and additivity as stated.

### 4.2 Interleaving (note 13 Propositions 3.4, 3.5; note 14 Proposition R2' and Theorem I)

**Statements.** (3.4, R2') $D \subseteq K$, $s \ge 1$. If every $s$-lane word over $K$ has at most $L \le |K|^s/4$ list members at $(A, d)$, every word with values in any finite-dimensional $K$-vector space has at most $L/(1 - L/|K|^s)$. (3.5) $\Lambda_{K^2}(T) \le \Lambda_K(T)(1 + \Lambda_K(2T - d))$. (Theorem I) For any code with pairwise agreement $\le d$ and single-lane lists $\le L$ at $A$: interleaved lists are at most $N_{L,g}(n - d)$, which is $L$ for $A > (n + 2d)/3$, $2L - 1$ for $A > (n + 3d)/4$, $L^2 + L - 1$ for $A > (n + 4d)/5$. All words, every domain (3.4 and R2' need $D \subseteq K$).

**Verdict: all correct. [proved]** I checked the random-projection count ($\binom{L'}{2}/|K|^s$ collisions, then $L' < 2L$, then the refined inequality), the grouping argument of 3.5, and Facts 1 to 4 and the induction of Theorem I. `21_real_checks.py consts` recomputes the values $1, L, 2L - 1, L^2 + L - 1$ of the recursion. I did not rerun the exhaustive toy cases of note 14.

Consequence worth stating in the main document: at rate 1/2, for $A > 2n/3$ (up to slack) interleaving is free on every domain, and on $(5n/8, 2n/3]$ it costs at most a factor 2, with no assumption.

### 4.3 The Artin-Schreier bound (note 13, Proposition 4.1)

**Statement.** Every field of characteristic two, every subspace domain with $N \ge 5$, every $U$ of size $n/8$: each value of $e_{n/8}$ is taken by at most $7 + 16 \cdot 224 = 3591$ of the $56n - 392$ members of the class of $L_U^5$. So this class contributes at most 3591 genuine codewords at agreement $5n/8$ to any word.

**Verdict: correct. [proved]** Details checked. (i) Lemma 2.1, $e_{n/8}(S) = e_2(Y)$: the exponents of $L_W^{10}$ and $L_W^9$ never equal $n/2$ because $l \le N - 4$. (ii) The coordinates: $t_i^2 + t_i = \lambda_i\alpha_W$ with $\alpha_W = \eta_W^{-2}$, additive in the functional of $W$, injective. (iii) Irreducibility: the coordinate ring of $C$ is free of rank 4 over $\bar F[t_1]$, and its fraction ring is a field iff no $(a\lambda_2 + b\lambda_3)/\lambda_1 \cdot (t_1^2 + t_1)$, $(a, b) \ne 0$, is $h^2 + h$ with $h \in \bar F(t_1)$; such an $h$ is a polynomial of degree 1 and forces the coefficient into $\{0, 1\}$; excluded because $\lambda_1, \lambda_2, \lambda_3$ are $\mathbb{F}_2$-independent. (iv) Degree: the closure of $C$ is a component of a complete intersection of two quadrics, degree $\le 4$, so a quadric not containing it meets it in at most 8 points. (v) The quadric $Q_c - v\alpha$ contains $C$ iff $c_{00} = 0$, $c_{ij} = 0$ ($1 \le i < j$), $c_{0i} = c_{ii}$, $v = \sum c_{ii}\lambda_i$: I recomputed this by reducing with $t_i^2 = t_i + \lambda_i\alpha$.

**Checks. [checked]** `21_real_checks.py curve`: the 504 label sets fall into 232 masks, 8 of 7 sets and 224 of 2 sets; the 8 masks of (v) are exactly the classes of the 56 invariant sets. Lemma 2.1 and $e_{n/8} = \eta^2Q_c(1, t)$ on random $(W, Y)$ at $N = 6, 7$ in $K$ and $\mathrm{GF}(2^{10})$, and all hyperplanes lie on the curve. Fibres with $D = \mathrm{GF}(2^m)$, $m = 9, 10, 12$ (63, 127, 511 hyperplanes): largest fibre 80, 78, 74 sets. **Observation:** for each of the 224 realised masks no value was ever taken at two hyperplanes (Bezout allows 8; over all 1015 nonzero masks the maximum is 3). If that is a theorem the bound is $7 + 2 \cdot 224 = 455$. It is plausibly a consequence of note 19 Theorem 2 (four dual points never coincide), but I did not prove it. **[conjectured]**

### 4.4 Note 19: Theorems 1, 2, 3 and Proposition 5.1

**Statements.** Every subspace domain of every field of characteristic two. A *previous-level class* is a class of equal-size sets modulo $L_{N-3}$ ($n_\varphi$ congruent modulo $n/8$). For $S, S'$ in one such class let $\Omega = \{\varphi : (\hat S - \hat S')(\varphi)/(n/4) \text{ odd}\}$, a set of points $a_\varphi = 1/\delta_\varphi$ of the dual space.

- Theorem 1 / Corollary 1.3: $S, S'$ share their top to depth $g \in [n/8, 3n/16)$ iff $\sum_\Omega 1/a = 0$; to depth $g \in [3n/16, 7n/32)$ iff also $\sum_\Omega 1/a^3 = 0$; always $|\Omega|$ even and $\sum_\Omega a = 0$.
- Theorem 2: then $\Omega = \emptyset$ or $|\Omega| \ge 6$ (for $g \ge n/8$), $\ge 8$ (for $g \ge 3n/16$); $|S \triangle S'| \ge 3n/8$, respectively $\ge n/2$.
- Theorem 3a ($g \ge 3n/16$, $s = \min(T, n - T) < n/2$): at most $1/(1 - 2s/n)^2$ sets of one previous-level class pairwise at depth $g$. 3b ($n/8 \le g < 3n/16$, $n/4 < s < n/2$): at most $J(\min(J, 32)Q + 1)$. 3c ($g \ge n/8$, $3n/16 \le s < n/4$): at most $48u^2/((12u - s)(4u - s))$, $u = n/16$.
- Proposition 5.1: on $D_{\kappa,R}$, $N = 25..28$, $V = \{f : f(0) = f(1) = f_{N-1}\}$ and $V' = (x^2 + x + 1)\mathbb{F}_2[x]_{<N-2}$ have $c_1(V) = c_1(V')$, so $Z_{V \setminus V'} - Z_{V' \setminus V}$ is a constant.

Class of words: strict common tops only, and only the members inside one previous-level class. The list of a word is bounded by $B \cdot M(w)$ with $M(w)$ the number of previous-level classes it meets; nothing bounds $M(w)$ on a concrete domain.

**Verdict: all correct. [proved]** I checked: the identity $\Lambda_c^{\sigma^N}(X^n) = \prod(1 + u_\varphi)^{-\hat c(\varphi)}$ and the comparison of exponents; the recursion $c_i^2 = D_i + \delta c_{i-1}$ and the triangular system for the $P_m$; the Reed-Muller argument for part 4; the Vandermonde argument (five, respectively seven, consecutive vanishing power sums); Lemma 3.1 ($L \le 4/(4 - \rho^2)$); Lemma 3.2 (F1, F2, F3, all sign cases); the graph argument of 3b (independent sets $\le J$, a neighbour's $\Omega$ is determined by four of its points, at most $\min(J, 32)$ neighbours per $\Omega$, the four thresholds on $|v_1|$); 3c. The constants: with each factor bounded separately over $s \in (5u, 6u)$ I get $J \le 15$ and $Q \le 14 \cdot 41 \cdot 59 \cdot 539$, so $L \le 15(15 Q + 1) = 4{,}107{,}099{,}165 < 2^{32}$, as claimed. (Evaluating the fourth factor pointwise gives 494 in place of 539 and $3{,}764{,}205{,}915$; immaterial.) For $s \in [6u, 7u)$: $J \le 63$, $Q \le 15 \cdot 62 \cdot 62 \cdot 566$, $L \le 63(32Q + 1) = 65{,}793{,}289{,}023 < 2^{36}$. At $s = 6u$: $1{,}275{,}264{,}016$.

**Checks. [checked]** `21_dual32` ($n = 32$, a 5-dimensional subspace of $\mathrm{GF}(2^m)$, $m \in \{5, 6, 7, 8, 12\}$, power and random bases, all $s$-sets inside sum buckets, keys by multiplying out): 138 runs over $(s, g)$ with $s = 6..13$, $g = 4..7$. In every previous-level class the partition by $e_4$ (and by $(e_4, e_5)$) equals the partition by $P_1$, the partition by $(e_4, e_5, e_6)$ equals that by $(P_1, P_2)$, and by $(e_4..e_7)$ that by $(P_1, P_2, P_3)$: zero failures. Over $2.5 \cdot 10^8$ pairs inside cells: $|\Omega| \in \{0, 6, 8, 10, 12\}$ for $g \in \{4, 5\}$ and $\{0, 8, 10, 12\}$ for $g \ge 6$; distances $\ge 12 = 3n/8$, respectively $\ge 16 = n/2$; exactly 12 in the range of 3c. Largest cells against the bounds: 3a: 3 (bound 7) at $s = 10$, 7 (16) at $s = 12$, 4 (4, attained) at $s = 8$, 5 (10) at $s = 11$; 3c: 2 (5) at $s = 6$, 5 (11) at $s = 7$; 3b region: 23 at $(s, g) = (11, 5)$, 31 at $(13, 5)$. Deep accidents are common in these small fields: one real class met up to 32 previous-level classes at $(s, g) = (10, 4)$ and $(11, 4)$, 7 at $(7, 4)$, which confirms that the factor $M(w)$ cannot be dropped by a field-independent argument. `21_real_checks.py pair`: $c_1(V) = c_1(V')$ in $K$ for $N = 25, 26, 27, 28$, with the values `cba43a67a8eb80e2`, `1ffceca7a13db23d`, `77ed94d3be30112c`, `cbca51b44a3f6baf` (identical to note 19, computed by my own recursion), $\dim(V \cap V') = N - 4$, $c_2(V) \ne c_2(V')$; for $N = 6..9$, $Z_A - Z_B$ multiplied out is a nonzero constant and the six dual points have $\sum 1/a = 0$, $\sum 1/a^3 \ne 0$.

What Proposition 5.1 does and does not show: the *structure* theorem of the generic model ("every pair is a hyperplane swap", and "the list is 1" at rate 1/16 on $[3n/16, n/4)$ for strict tops) is false on the real domain. It does not produce a list larger than 2, and lists of size 2 or 3 exist on every domain anyway (trivial lists).

## 5. Errors and corrections

- **E1 (note 02, summary item 2 and section 5 "Relation to note 01").** "Most members are unions of ten cosets of a varying hyperplane $W$ that are not unions of two flats" is wrong. Every member is five cosets of $U$, or an affine flat of size $n/4$ plus three cosets of $U$ (checked: the two descriptions give identical families at $N = 5, 6, 7$). The factor $8/3$ over the tree count comes from the eight possible padding cosets, as note 05 says. No count changes.
- **E2 (main document section 4, synthesis item 5: "at most $1/(2\tau - 1)^2$ members above $5n/8$ ... at most 11 and 8 at rates 1/8 and 1/16").** True, but (i) the proved sharp values are 4 at rate 1/2 and 4 at rate 1/8 (note 02 Proposition 6), 8 then 1 at rate 1/16; (ii) the hypothesis is depth $\ge n/8$: with the analysis degree $d = k - 1 + \ell$ the bound starts at $T = 5n/8 + \ell$, and for $5n/8 \le T \le 5n/8 + \ell - 1$ there are at least $7n - 35$ members; for multiset tops (Theorem A) it starts at $T > 5n/8 + \ell$, and at $T = 5n/8 + \ell$ itself multiset lists are not bounded by anything proved (16 members at $n = 16$, $\ell = 1$); (iii) it is a statement about the formal model, so about families that share their top on every domain.
- **E3 (note 01 section 3.4; note 12 section 2.2 remark (ii), section 4.3, table of section 8).** The biased padding does not have $L = 3/(64\epsilon^2)$ members. That number is the Parseval cap of the mechanism. The explicit family has $L = 1/(64\epsilon^2) - 1/(16\epsilon)$ at $\epsilon = 2^{-m'-2}$ (section 2.4, now with a proof for every $m'$). So the gap between Theorem A ($1/(16\epsilon^2)$) and the best construction is a factor 4, not $4/3$, and the "best known lower bound" in note 12's final table should read "$1/(64\epsilon^2) - 1/(16\epsilon)$ for $\epsilon = 2^{-j}$, $j \le N/2 + 2$". Also: the explicit $B$ has $1008n/4096$ points, not $n/4$, and its codewords are genuine. Consequence for the main document: "above $5n/8$ only a family of about $2^{10}$ at $0.629n$ is known" undersells it. The same family has $2^{22}$ genuine members at $5n/8 + 2^{11}$ ($N = 25$), $2^{16}$ at $0.6255n$, 4064 at $0.6270n$ and 1008 at $0.6289n$. What remains true is that nothing growing with $n$ is known at a *fixed* fraction above $5/8$.
- **E4 (note 12, summary row B).** Add the hypothesis $m + r < n/4$ (it is in Theorem 3.1).
- **E5 (note 00 section 1, main document section 4).** Flats at rate 1/4 are one point inside the range of the Johnson bound (which gives $n^2/4$ there), not beyond it. "Closed" is right for the threshold; "Johnson is tight" should be read as "the list at the radius is at least $n - 1$".
- **E6 (note 13, Corollary 3.2 part 3 and the summary line "at least $64(e'+1)$ bits of coincidence").** What is proved is the vanishing of $e' + 1$ field elements. It is not a rarity statement: note 19 section 4.3 shows the corresponding linear map has a kernel of dimension in the millions. Keep it as accounting.
- **E7 (note 13, section 3.2, "$2^{38.7 - 1.1j}$ proved to exist"; main-document-level tables that use $2^{102.7}$).** Conditional on the count $M_3(N)$ quoted from [DKTZ26, Thm 6.10], which nobody in the project re-derived. With the lists verified here (the $2^{72}$ stacks, of which a fraction $2^{-j}$ avoids $j$ given points) the same pigeonhole gives only $2^{8 - j}$.
- **E8 (main document section 4, "Two sets share ... exactly when their Walsh spectra agree").** Add "of equal size, on a generic domain". On every domain only the implication from Walsh congruence to common tops holds.

None of these changes an attack floor. E3 changes one number that people may quote (the tightness of Theorem A), E2 and E7 change what the main document may call proved.

## 6. What is actually proved (the list problem)

Conventions. $L$ is the number of codewords of degree $< k$ agreeing with one word on at least $T = \tau n$ points; with the analysis degree $d = k - 1 + \ell$ replace $k$ by $k + \ell$ (every dyadic point moves up by $\ell$). "All domains" means every $\mathbb{F}_2$-subspace of every field of characteristic two, so it includes $D_{\kappa,R} \subset K$. "Generic" means the formal model: the bound holds for families that share their top on every domain, for any number of lanes (note 12 Proposition 1.1), and says nothing about domain-specific coincidences. "Per class" means inside one previous-level class of a strict common top list; the list of a word is bounded only up to the number $M(w)$ of such classes, which is unbounded in theory. Lower bounds are single-lane, over the field generated by $D$, on all domains unless stated. A lower bound at an agreement is a lower bound at every smaller agreement (the same word and codewords). Sizes at level 0, $\mu = 30$ ($N = 24 + R$).

**Upper bounds for all words on the real domain.**

| range | bound | status |
| --- | --- | --- |
| $T^2 > n(k - 1)$ (Johnson), any rate, any lanes | $n(T - k + 1)/(T^2 - n(k-1))$ | proved (classical; what `formal/` uses) |
| any $T$ below that, any rate | nothing (a few points beyond Johnson by pinning, note 04 Proposition 1.3, not refereed here) | open |
| any lanes or extension of $K$, given a bound $L$ for single $K$-valued words | $L$ if $A > (n + 2d)/3$; $2L - 1$ if $A > (n + 3d)/4$; $L/(1 - L/2^{64})$ if $L \le 2^{62}$ | proved (note 14 Theorem I, Proposition R2') |

**Rate 1/2.**

| agreement (genuine degree) | best proved upper bound, class of words, domains | best proved lower bound (all domains) | conjectured or measured |
| --- | --- | --- | --- |
| $T > n/\sqrt2$ | Johnson, all words, all domains | | |
| $11n/16 \le T \le n/\sqrt2$ | generic: strict tops $\le 4$; multiset tops $\le \max(1/(16\epsilon^2), 1 + (2\tau - \frac12)/\epsilon)$, $\epsilon = \tau - \frac58$; words of degree $\le T + n/96$: $\frac{1/4 - \theta/n}{(\tau - 1/2)^2 - \theta/n}$. All domains: strict tops, per class, $\le 1/(2\tau - 1)^2 \le 7$. All words: nothing | 3 (three hyperplanes plus a common set) | all words: $O(1/\epsilon^2)$ (Conjecture G generic, C1 real). Measured: 3 for all words at $n = 16$, $T = 11$ (note 18, not refereed) |
| $5n/8 < T < 11n/16$ | generic: as above. All domains: strict tops, per class, $< 2^{32}$. All words: nothing | 3; multiset tops: $(4^{m'} - 2^{m'})/4$ genuine codewords at $\tau = \frac58 + 2^{-m'-2}$ for every $m' \le N/2$ (proved in section 2.4, checked for $m' = 4..10$): $2^{22.0}$ at $5n/8 + 2^{11}$, 4064 at $0.6270n$, 1008 at $0.6289n$ for $N = 25$; $2^{10}$ in degree $\le n/2$ at $0.6281$ (checked for one random $B$). Real $D_{24,1}$: explicit pairs that are not hyperplane swaps | as above; no family growing with $n$ at fixed $\tau > 5/8$ is known |
| $T = 5n/8$ (in the analysis degree: $T = 5n/8 + \ell$) | generic strict tops: $\le 7$ (attained). All domains: the class of $L_U^5$ contributes $\le 3591$ to any word; strict tops per class $\le 1{,}275{,}264{,}016$. Multiset tops, all words: nothing | 7 (strict); multiset tops: $(4^{m'} - 2^{m'})/4$ with $m' = \lfloor N/2\rfloor$, that is $2^{22.0}$ at $N = 25$ (the line above, since a list at a larger agreement is a list at $5n/8$) | exact growth: at least $n/8$, at most unknown; measured 15 at $n = 16$ (reproduced), 28 at $n = 32$ for one word (note 02) |
| $T = 5n/8$, degree $\le n/2$; and up to $5n/8 + \ell - 1$ in the analysis degree | generic strict tops: $2n^5$. All words: nothing | $56n - 392 = 2^{30.81}$ at $5n/8$ (exactly the class of the word in the formal model, and at $n = 32$ on the leanVM shape); $7n - 35 = 2^{27.8}$ up to $5n/8 + \ell - 1$ | exact on $D_{24,1}$ (C3) |
| $9n/16 \le T < 5n/8$ | generic strict tops: $2n^5$ (note 12 Proposition 5.1). All words: nothing | $105n - 965 = 2^{31.71}$ at $9n/16$; $35n - 245 = 2^{30.13}$ at $5n/8 - 1$ (exact in the formal model at $n = 64, 128$) | $\le 105n$ for strict tops (Conjecture 5.3); pigeonhole term $2^{38.7}$ just above $9n/16$ on $D_{24,1}$ (proved given [DKTZ26]) |
| $T = 9n/16$, degree $\le n/2$ (genuine: $9n/16 - 1$) | generic strict tops: $(2n - 1)^{56}$ (note 04 Theorem 2.7) | $(2^{N-1} - 2)^3 = 2^{72}$ (stacks); $2^{44.8}$ (glued unions); $2^{102.7}$ quoted from [DKTZ26] | |

**Rate 1/4.**

| agreement | upper bound | lower bound | conjectured or measured |
| --- | --- | --- | --- |
| $T \ge n/2 - 1$ | Johnson: $n^2/4$ at $n/2 - 1$, $n/4 + 1$ at $n/2$ | $2^N - 1$ genuine at $n/2 - 1$ (flats); $2n - 2$ in degree $\le k$ at $n/2$ | |
| $7n/16 \le T < n/2 - 1$ | generic strict tops: $1 + T(n - T)/(n/2 - T)^2$. All domains, strict tops per class: $n^2/(n - 2T)^2$. All words: nothing | hyperplanes through a common set of $a = n/2 - T$ points: $2^{N - \lceil\log_2 a\rceil} - 1$ genuine codewords, about $n/(n/2 - T)$ (7, 7, 15, 31 at $n = 32$, $T = 12..15$, reproduced) | Gold families $2^{13.5}$ at $7n/16$ (note 01, conjectured) |
| $3n/8 \le T < 7n/16$ | all domains, strict tops per class: $< 2^{36}$. All words: nothing | $56n - 392$ in degree $\le n/4$ at $3n/8$ (complements, checked at $N = 6$) | Gold: $2^{30.5}$ to $2^{34.5}$ at $3n/8$ (conjectured) |

**Rate 1/8.**

| agreement | upper bound | lower bound | conjectured or measured |
| --- | --- | --- | --- |
| $T > 0.3536n$ | Johnson | | |
| $5n/16 \le T \le 0.3536n$ | generic: strict tops $\le 4$; multiset tops $\le \max(15, 1 + (2\tau - \frac18)/\epsilon)$, $\epsilon = \tau - \frac14$; degree $\le T + n/96$: Theorem B. All domains: strict tops per class $\le 11$. All words: nothing | trivial lists $\lfloor (n - k + 1)/(T - k + 1)\rfloor$: 4 to 3 | all words $O(1/\epsilon)$ (Conjecture G). Measured at $n = 16$: 6 for all words against 3 for multiset tops (notes 02, 12, 18) |
| $n/4 < T < 5n/16$ | generic: as above. All domains: strict tops per class $< 2^{21}/\epsilon^2$. All words: nothing | trivial lists: 6 to 4; explicit non-swap pairs on $D_{24,3}$ | |
| $T \le n/4$ | none | $\binom{N}{2}_2 = 2^{51.4}$ genuine at $n/4 - 1$ (flats) | |

**Rate 1/16.**

| agreement | upper bound | lower bound | conjectured or measured |
| --- | --- | --- | --- |
| $T \ge n/4$ | Johnson | | |
| $3n/16 \le T < n/4$ | generic: strict tops $= 1$; multiset tops $\le \max(7, 1 + (2\tau - \frac1{16})/(\tau - \frac3{16}))$ for $T > 3n/16$; degree $\le T + n/96$ and $T < n/4 - 3r$: 1. All domains: strict tops per class $\le \frac{3}{16(3/4 - \tau)(1/4 - \tau)}$ (5 to 11 and more near $n/4$). All words: nothing | trivial lists: 7 to 5. On $D_{24,4}$: 2 strict-top members where the generic value is 1 | |
| $n/8 < T < 3n/16$ | generic strict tops: $\le 7$. Nothing else | trivial lists: 14 to 7; a pigeonhole list of about $2^{15.6}$ in degree $\le k$ at $0.152n$ for $N = 28$ (note 01 section 3.2, existence proof read, not recomputed) | |
| $T \le n/8$ | none | $\binom{N}{3}_2 = 2^{76.6}$ genuine at $n/8 - 1$ (flats) | |

**One-paragraph reading.** On the real domain, for all words, the only proved list bound is Johnson, plus the two interleaving reductions. Everything else on the proof side is either about the formal model (three classes of words: strict tops, multiset tops, words of degree at most $T + n/96$; constants 4, $1/(16\epsilon^2)$, and a Johnson-type expression) or about strict tops inside one previous-level class on every domain (constants 7, $2^{32}$, $2^{36}$, 11, 5 to 11). The lower bounds $56n - 392$ ($5n/8$, degree $\le n/2$), $35n - 245$ ($5n/8 - 1$), $105n - 965$ ($9n/16$), the flats, and $(4^{m'} - 2^{m'})/4$ genuine codewords at $(5/8 + 2^{-m'-2})n$ are proved on every subspace domain and reproduced here. $2^{102.7}$ is quoted. No list that grows with $n$ is known at any fixed fraction above $5/8$ (rate 1/2), $1/4$ (rate 1/8) or $1/8$ (rate 1/16), and no proof excludes one.

## 7. Reproduction

All in `doc/whir_soundness_gap_notes/scripts/`, Python 3 without dependencies and C with the system compiler; `21_run_all.sh [builddir]` rebuilds and reruns everything into `21_results.txt` (about 25 minutes of CPU in total on an idle machine, no single run above 10 minutes, at most three processes at a time, memory below 1 GB).

| script | what it does | time |
| --- | --- | --- |
| `21_gf.py` | $\mathrm{GF}(2^m)$, linearized polynomials, locators; self-test | 1 s |
| `21_attack_checks.py flats` | section 2.1 | 7 s |
| `21_attack_checks.py thmw` | section 3.1 | 2 min |
| `21_attack_checks.py five8 7` | section 2.2, both descriptions, counts, tops in $K$ | 20 s |
| `21_attack_checks.py mitm` | exact classes at $n = 32$ in $K$ by meet in the middle | 1 min |
| `21_attack_checks.py extra` | stacks and glued unions at $9n/16$, random padding, complements at rate 1/4 | 1 s |
| `21_walsh.c` | `classes32 s M`: all $s$-subsets of $\mathbb{F}_2^5$ by Walsh key modulo $M$; `rm2 N M seed c [file]`: the class of a seed at $n = 32, 64, 128$ | up to 40 s per call |
| `21_nine16_checks.py` | section 2.3 from the dumps of `21_walsh rm2` | 25 s |
| `21_multiset16.c` | section 3.3 | up to 2 min per $(k, T)$ |
| `21_dual32.c` | section 4.4, one run per $(m, \text{basis}, s, g)$ | 0.1 s to 1 min |
| `21_real_checks.py padding, padfield, pair, sparse, curve, consts` | sections 2.4, 4.1, 4.3, 4.4 | 20 s in all |
| `21_real_checks.py phantom` | section 3.4 | several minutes |
