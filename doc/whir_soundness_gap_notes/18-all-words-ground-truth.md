# 18. All words: exact ground truth at $n = 16$, structured exhaustion at $n = 32$

Researcher 18, round 4. Every statement is tagged **[proved]** (proof in this note), **[checked]** (numerically, sizes and domains stated) or **[conjectured]**. Scripts are `scripts/18_*`, section 7 says how to run them.

Notation. $F$ is a field of characteristic 2 ($\mathrm{GF}(2^{64})$ with the leanVM modulus in every run unless stated), $D \subset F$ an $\mathbb{F}_2$-subspace of dimension $N$, $n = 2^N$. Codewords are polynomials of degree $< k$, $T$ is an agreement count, $e = n - T$ the number of errors, $m = T - k$, $M = n - k$. $\Lambda(T)$ is the largest number of codewords agreeing with one word on at least $T$ points, over ALL words $w : D \to F$. "Generic" means a random basis of $D$ in $\mathrm{GF}(2^{64})$ (the formal model of notes 02, 04, 05, 12; two independent bases). "Real shape" means $D = \mathrm{span}(1, x, \dots, x^{N-1})$, in $\mathrm{GF}(2^{64})$ with the real modulus and in $\mathrm{GF}(2^{10})$, $\mathrm{GF}(2^{11})$, $\mathrm{GF}(2^{12})$ (field degree about $2.56 N$ and around it). A list is a *strict top* if its word is a polynomial of degree exactly $T$ modulo codewords, and a *multiset top* if every $(w - c_i)/Z_{S_i}$ splits over $D$ (notes 02 and 12).

## 0. Summary

**What was done.** The largest list over all words was computed exactly, by exhaustive search with a proof-carrying structure (section 2), for every $(k, T)$ at $n = 16$ where the search is feasible: 26 parameter pairs on a generic domain, 19 of them also on the real shape. This includes both points of $n = 16$ that lie in the open windows, $(k, T) = (8, 11)$ at rate 1/2 and $(2, 5)$ at rate 1/8, and all the boundary points. At $n = 32$ full exhaustion is out of reach, and I exhausted natural linear classes of words instead: all words invariant under a translation, all words of small phantom degree (polynomials of degree at most $T + r$), all words containing given pairs or quadruples of agreement sets. Every extremal word found was classified, and every non-top configuration was explained and its scaling settled.

**Exact maxima at $n = 16$, all words** (generic domain; the real shape agrees wherever it was run, except one row).

| $(k, T)$ | $T/n$ | all words | strict tops | multiset tops | generic points | what the extremal words are |
| --- | --- | --- | --- | --- | --- | --- |
| $(8, 10)$ | $5/8$ | **15** | 7 | 15 | 3 | one class: the padded hyperplane word $X^8 Z_C$ of notes 01 and 02 (multiset top, mass 11) |
| $(8, 11)$, window | $11/16$ | **3** | 3 | 3 | 2 | three classes: a strict top, a multiset top (codeword plus 4 errors), one word that is not a top |
| $(8, 12)$ | $3/4$ | 1 | 1 | 1 | 1 | unique decoding |
| $(9, 11)$, window with slack 1 | $11/16$ | **16** | 3 | 16 | 3 | one class: $X^8 \ell(X)$, $\ell$ linearized of degree 4, one translation orbit (multiset top, mass 12) |
| $(9, 12)$ | $3/4$ | **4** | 4 | 4 | 2 | the complements of the four cosets of a 2-dimensional subspace (strict top) |
| $(4, 7)$ | $7/16$ | **15** | 15 | 15 | 3 | the flats |
| $(4, 8)$, Johnson radius | $1/2$ | **3** | 2 | 2 | 2 | 71 classes, all triangles (section 5.3) |
| $(2, 5)$, window | $5/16$ | **6** | 3 | 3 | 4 | the Sidon tangent lines (one configuration, two classes); 6 is proved for every domain (Proposition 5.2) |
| $(2, 6)$ | $3/8$ | **3** | 1 | 2 | 3 | triangles |

The complete table (42 rows, 26 of them exhausted, with Johnson, trivial lists, the real shape and three small fields) is in section 3. Not exhausted at $n = 16$: the 16 rows in which a syndrome is only pinned by five or more members: $(2, 3)$, $(2, 4)$, $(3, 4..6)$, $(4, 5)$, $(4, 6)$, $(5, 6)$, $(5, 7)$, $(6, 7)$, $(6, 8)$, $(7, 8)$, $(7, 9)$, $(8, 9)$, $(9, 10)$, $(10, 11)$. None of them is in a window. For these I give exact maxima over the words of phantom degree $\le r$ for small $r$ (section 3.3).

**What $n = 16$ says.** In every exhausted case the all-words maximum is the multiset-top maximum or a polygon of at most 6 lines (triangle, quadrilateral, hexagon) in a label plane. In the rate-1/2 window the maximum over all words is 3, the strict-top value, on the generic domain, on the real shape in $\mathrm{GF}(2^{64})$ and in the three small fields. The lists that note 02 found by annealing above the strict tops are all accounted for: 11 at $(8, 10)$ is inside the multiset list of 15, which is the exact maximum; 6 at $(2, 5)$ is the exact maximum; 16 and 17 at $(4, 6)$ and 9 at $(2, 4)$ are lists of words that are not tops, below every window (section 3.3). One new kind of list appears with slack 1: the 16 translates of one agreement set, for a word that is invariant under all translations modulo codewords. It gives the 16 at $(9, 11)$ and, at $(3, 5)$ (degree $\le 2$, the slack-1 version of the rate-1/8 window point), a list of 16 for a word that is not a top, against 7 for multiset tops. Proposition 5.5 explains it and shows that it lives at $T = k + \log_2 n - 2$, so it is a small-$n$ effect.

**What was learned at $n = 32$** (generic domain, section 4).

- $T = 22$, rate 1/2 (the lift of the window point of $n = 16$): the maximum is **3** over all words invariant modulo codewords under a translation (an 8-dimensional family containing every lift from 16 points), over all words of phantom degree $\le$ 5 (polynomials of degree $\le$ 27), and over all words whose list contains a given lifted pair or a given interval pair. Four random pairs of 22-sets with union $D$ have no third member at all.
- $T = 21$, rate 1/2 (the new window point): strict tops 3, phantom degree $\le 1$: 6, phantom degree $\le 2$, $\le 3$ and $\le 4$: **16**, all multiset tops (mass 22 and 23, biased paddings in the sense of note 01). So the all-words maximum at $(32, 16, 21)$ is at least 16, five times the strict-top value, attained by a multiset top. This is consistent with note 12 Theorem A, which bounds multiset tops by $1/(16\epsilon^2) = 64$ at $\epsilon = 1/32$.
- Degree $\le n/2$ (slack 1): the fully translation-invariant words $X^{16}\ell(X)$ have exactly 16, 16, 4 at $T = 21, 22, 23$: the list of 16 at $11/16$ does not grow from $n = 16$ to $n = 32$.
- Rate 1/8: the largest list containing four (or five) of the six lifted Sidon lines at $T = 10$ is 6. Words of phantom degree $\le$ 5 at $T = 11$ have at most 3 (the strict tops). At $T = 9$ and $10$ words of phantom degree $\le 4$ and $\le 5$ have at most 4 (a multiset top of mass $T + 1$).

**The decisive question.** I found no family of non-top words whose list grows with $n$ at a fixed $(\rho, \tau)$ inside a window, and the evidence is against one, with the following precise content.

1. **[proved]** The Sidon lines do not scale. With lifting and anti-shortening they give a list of $L$ at $\tau = \rho + (L - 3)/M'$ on $M'$ labels, which forces $L < 2(1 - \rho)/(\tau - \rho) + 2$ (Corollary 5.4). More generally a list in which every point outside a common core lies on at most $j$ members is at most $j$ times the trivial list. In the rate-1/8 window the Sidon family gives exactly 6, at $\tau = 5/16$, for every $n \ge 16$.
2. **[proved]** At $(n, k, T) = (16, 2, 5)$, $\Lambda = 6$ on every domain and in every field, so the excess over tops (3) in the only window point of rate 1/8 is this bounded configuration.
3. **[proved]** The orbit lists of translation-invariant words (16 members at $n = 16$ with slack 1, not tops at rate 1/8) have agreement $k + \log_2 n - 2$ and leave every window as $n$ grows (Proposition 5.5). **[checked]** at $n = 32$: they have 32 members at $T = k + 3$, which is $5n/8$ for $k = 17$, and inside the windows the invariant words have only the lifts of the $n = 16$ lists.
4. **[checked, exhaustive]** At $n = 16$ no word that is not a top beats the multiset tops in the rate-1/2 window (3 against 3, and 16 against 16 with slack 1), on the generic domain and on the real shape. The non-top lists that beat tops elsewhere are polygons ($(4, 8)$: 3 against 2, $(3, 7)$: 4 against 2, $(2, 6)$: 3 against 2), bounded as in item 1, or orbit lists.
5. **[checked, exhaustive inside the classes named above]** At $n = 32$ nothing beats the multiset tops in the rate-1/2 window. The list sizes at fixed fraction did not grow from $n = 16$ to $n = 32$ at $\tau = 11/16$ (3 and 3 genuine, 16 and 16 with slack 1).
6. **[proved in note 12, generic domain]** Multiset tops are bounded in the rate-1/2 window by $1/(16\epsilon^2)$ at $\tau = 5/8 + \epsilon$. The data here (15 at $\epsilon = 0$ and 3 at $\epsilon = 1/16$ for $n = 16$; at least 28, then 16, then 3 at $\epsilon = 0, 1/32, 1/16$ for $n = 32$) fit that shape: large lists close to $5/8$ at every size, nothing growing at a fixed $\epsilon$.

What this does not settle: words of large phantom degree that are invariant under no translation at $n = 32$ (the bulk of all words), and everything at $n \ge 64$. A complete answer at $n = 32$ is far out of reach of these methods (section 6 gives the costs); the natural next computations are listed there.

## 1. The exact criterion

### 1.1 Syndromes, members, configurations

For a word $w : D \to F$ put $s(w) = (s_0, \dots, s_{M-1})$, $s_i = \sum_{a \in D} w(a)\, a^i$, and read $s$ as a linear functional on polynomials of degree $< M$: $s(\sum q_i X^i) = \sum q_i s_i$. For $E \subseteq D$ let $U_E \subseteq F^M$ be the span of the vectors $h_a = (a^i)_{i < M}$, $a \in E$, and $Z_E = \prod_{a \in E}(X - a)$.

**Lemma 1.1. [proved]** Let $N \ge 2$. (a) $\sum_{a \in D} a^j = 0$ for $0 \le j \le n - 2$ and $\sum_{a \in D} a^{n-1} = c_0 := \prod_{a \ne 0} a \ne 0$. (b) $w \mapsto s(w)$ is onto $F^M$ and its kernel is the code. (c) If $P_w = \sum_j p_j X^j$ is the interpolant of $w$ (degree $< n$), then $s_i = c_0\, p_{n-1-i} + (\text{a combination of the } p_j,\ j > n - 1 - i)$. So $s$ starts with exactly $z$ zeros if and only if $w$ is, modulo codewords, a polynomial of degree exactly $n - 1 - z$.

*Proof.* $L_D = Z_D$ is linearized, so $L_D' = c_0$ and $\sum_a 1/(X - a) = c_0 / L_D(X) = c_0 X^{-n}(1 + O(X^{-n/2}))$, while the left side is $\sum_j (\sum_a a^j) X^{-j-1}$. This is (a). For (b), a codeword $c$ has $\deg(c X^i) \le n - 2$ for $i < M$, so it is in the kernel, and the map is onto because the $h_a$ of any $M$ points are a Vandermonde basis. (c) is (a) applied to $s_i = \sum_j p_j \sum_a a^{i+j}$. $\square$

**Lemma 1.2. [proved]** Let $E \subseteq D$, $|E| \le M$. The following are equivalent: (i) some codeword agrees with $w$ on $D \setminus E$; (ii) $s(w) \in U_E$; (iii) $s(X^l Z_E) = 0$ for $0 \le l < M - |E|$. The codeword is then unique, and it disagrees with $w$ exactly on $\{a \in E : s(Z_{E \setminus a}) \ne 0\}$.

*Proof.* A word supported on $E$ with values $y_a$ has syndrome $\sum_a y_a h_a$, which gives (i) $\Leftrightarrow$ (ii) by Lemma 1.1 (b). The $h_a$, $a \in E$, are independent, and a polynomial $q$ of degree $< M$ pairs to zero with all of them exactly when $Z_E \mid q$, so the annihilator of $U_E$ is $Z_E \cdot \{\deg < M - |E|\}$, which is (iii). If $s = \sum_a y_a h_a$ then $s(Z_{E \setminus a}) = y_a Z_{E \setminus a}(a)$. $\square$

So the list of $w$ at agreement $T$ is the set of $e$-sets $E$ with $s(w) \in U_E$, counted by their exact supports, and

$$\Lambda(T) = \max_{0 \ne s \in F^M} \#\{\text{distinct supports of size} \le e \text{ through } s\}.$$

The $h_a$ are $n$ points of a rational normal curve in $\mathbb{P}^{M-1}$, the $U_E$ are its $e$-secant spaces, and $\Lambda$ asks for the point on the largest number of them. For a family of sets this is the rank formulation of note 12 section 4.2:

**Corollary 1.3. [proved]** $T$-sets $S_0, \dots, S_L$ with complements $E_i$ are agreement sets of $L + 1$ distinct codewords with one word (over $F$, if $|F| > \binom{L+1}{2}$) if and only if $I = \bigcap_i U_{E_i}$ is not contained in $U_{E_i \cap E_j}$ for any $i \ne j$. In particular $|S_i \cap S_j| \le k - 1$, and for two sets $\dim(U_{E_i} \cap U_{E_j}) = 2e - M$ whatever the domain: only triples and beyond see the structure of $D$.

*Proof.* A syndrome of $I$ has members $E_i$ and $E_j$ with the same codeword exactly when it lies in $U_{E_i \cap E_j}$ (Lemma 1.2 applied to the common support). $I$ is not a union of $\binom{L+1}{2}$ proper subspaces over a field with more elements than that. The dimension count is the Vandermonde independence of any $M$ of the $h_a$. $\square$

### 1.2 Word types

By Lemma 1.1 (c) every word has a *phantom degree* $r = (n - 1 - z) - T \le e - 1$: it is a polynomial of degree $T + r$ modulo codewords and no less. For a member with agreement set $S$, $w - c = Z_S \cdot g$ with $\deg g = T + r - |S|$ (the cofactor, which is the classical error evaluator up to a constant). Then:

- $r = 0$: strict common top. A word of degree exactly $T$ cannot have any other kind of member, and a word of degree $< T$ has no list.
- every cofactor splits over $D$: multiset top of mass $T + r$ (through the interpolant, the representative of least degree; note 12 allows any representative, and its exhaustive program `12_multiset16` covers all masses up to $2n$ with multiplicities $\le 2$, which is what the "multiset tops" column below uses).
- otherwise the word is not a top in either sense. This is the class for which notes 02, 04, 05, 12 prove nothing unless $r \le n/96$ (note 12 Theorem B).

The programs print $r$, the splitting of the cofactors, and the least $d_1$ with a nonzero $\sigma$ of degree $\le d_1$ killing all windows $s(X^l \sigma)$, $l < M - d_1$, together with the number of roots of that $\sigma$ at infinity (degree drop), in $D$ and elsewhere. **[standard, quoted]** (kernels of Hankel matrices, equivalently the key equation): the locators of all members lie in the module window $\sigma_1 \cdot \{\deg \le e - d_1\} + \sigma_2 \cdot \{\deg \le e - d_2\}$ with $d_1 + d_2 = M + 1$, a list of two or more needs $d_1 \ge m + 1$, and $d_1 = m + 1 + r$ with all roots of $\sigma_1$ at infinity is the same as "polynomial of phantom degree $r$". I use this only to describe words: roots at infinity say the word is a low-degree polynomial, roots in $D$ that it is a simpler word plus errors there, other roots that it has poles. **[checked]** on the strict and multiset tops found below with $m + 1 + r \le (M + 1)/2$: $d_1 = m + 1 + r$ and all roots are at infinity.

### 1.3 Symmetry

**Lemma 1.4. [proved]** In the formal model the set of list configurations is invariant under $\mathrm{AGL}(N, 2)$ acting on $D \cong \mathbb{F}_2^N$. On a concrete domain it is invariant under the translations by elements of $D$.

*Proof.* The condition of Corollary 1.3 is a set of rank conditions on matrices whose entries are polynomials over $\mathbb{F}_2$ in the basis of $D$. A linear change of basis maps an algebraically independent basis to another one. $X \mapsto X + a$ preserves degrees and $D$. $\square$

A rank drop on a random basis in $\mathrm{GF}(2^{64})$ is formal up to an error probability of about $\deg / 2^{64}$ per test, and conversely a formal list configuration survives specialization. So one random basis gives the formal maxima with overwhelming probability. Every maximum below was nevertheless computed on two independent bases where the run takes under a minute, and every extremal family was re-derived on the second basis.

### 1.4 Reference values

- **Johnson.** If $T^2 > n(k-1)$ then $\Lambda(T) \le n(T - k + 1)/(T^2 - n(k - 1))$.
- **Generic points.** $G = \lceil (n - T)/(T - k) \rceil = \lfloor (M - 1)/m \rfloor$: the largest list of a Reed-Solomon code on points in general position (the generalized Singleton bound, attained by the higher-order MDS property of generic Reed-Solomon codes; quoted as in note 12, not re-read). $G$ sets always leave a nonzero $I$ by counting dimensions, on any domain.
- **Trivial lists.** $\lfloor (n - k + 1)/(T - k + 1) \rfloor$ on every domain (note 02 section 1).
- **Unique decoding.** $\Lambda(T) = 1$ for $2T \ge n + k$.

## 2. Programs

### 2.1 `18_exhaust.c`: all words, $n = 16$

It works with syndromes and locators (Lemma 1.2 (iii)) and decides $\Lambda(T)$ exactly for the domain and field of the run.

1. *Symmetry.* The $e$-sets are split into orbits of the group $G$ ($\mathrm{AGL}(4,2)$, order 322560, on a generic domain; the 16 translations on the real shape), each orbit representative $E_0$ gets its stabilizer, and the pairs $(E_0, E_1)$ are taken up to the stabilizer. A pair class is skipped when the reversed pair is an earlier class. Inside a class every further member $X$ must be in an orbit not before that of $E_0$, and every pair $(Y, X)$ of the list with $Y$ in the orbit of $E_0$ must be a class not before the current one (the transporter of each set to its representative is stored, so the class of a pair costs two table lookups). Any list can be moved so that its smallest pair class is the current pair, so nothing is lost.
2. *Nodes.* A node is a space $I$ of syndromes (at the start $U_{E_0} \cap U_{E_1}$, of dimension $2e - M$) and a list of candidate sets. For a candidate $X$ the $m \times \dim I$ matrix $(s_b(X^l Z_X))$ over a basis $(s_b)$ of $I$ is reduced without divisions. Rank 0: $X$ is a member for every word of $I$ (free). Full rank: dead. Rank $\dim I - 1$: $X$ selects one point of $\mathbb{P}(I)$; the points are normalized and hashed, so a node whose candidates are all points is settled without branching. Otherwise $X$ cuts out a subspace, and the node branches on it, in index order, passing down all point candidates and the later subspace candidates. Along the chain of its members that successively cut $I$ down, every list is met with all its members present.
3. *Exact counts.* At every group of equal points, and at a generic point of every $I$, the number of distinct error supports among the known members is computed at that concrete syndrome (Lemma 1.2). When it reaches the current maximum the full list of that syndrome is recomputed from scratch over all $e$-sets and recorded. So the reported maximum is a true list size, and the bound "members so far plus live candidates below the target" is the only pruning.
4. *Output.* The maximum, all extremal families (as families of maximal agreement sets), their classes under $G$ by a canonical form, and for one family per class: agreement sizes, pairwise intersections, the dimension of the space of words having that family, the type (section 1.2) of the recorded word and of the lowest-degree word of the family, and a word for independent checking.

An optional argument restricts the search to words of phantom degree $\le r$ (the syndromes with $e - 1 - r$ leading zeros). It makes the deep cases shallow, and with $r = 0$ it is the strict-top enumeration of note 02.

### 2.2 `18_sub.c`: linear families of words, $n = 16$ or $32$

It works with values and divided differences. A family is a space of words modulo codewords given by $d$ basis words. A $T$-set $S$ is an agreement set of $w$ if and only if the Newton coefficients of $w$ on $S$ of order $k, \dots, T - 1$ vanish. The scan walks all $T$-sets in increasing order of points, keeps the divided-difference diagonal of each basis word (one multiplication per order when a point is added, with a table of inverses of differences), and after each point beyond the $k$-th appends one row: the new top coefficients of the $d$ basis words. Once the rows have rank $d$ no extension of the prefix can be an agreement set of a nonzero word of the family, and the subtree is cut. A surviving $T$-set gives one point of the family (hashed and grouped as above) or a subspace (recursed on, equal subfamilies once). Three refinements are needed for exactness: (a) *free points*, on which the family is unconstrained: their indicator words are in the family, they are listed first in the scan order, only the indicators of the free points inside $S$ count as columns, and the members of a group are then compared on the free values they impose (an exact search over assignments); (b) in an *anchored* family (all words vanish on a first member, whose codeword is 0) a set on which every kernel word vanishes is another agreement set of the same codeword and is dropped; (c) every count is recomputed as a number of distinct maximal agreement sets at a concrete word, and the full list of that word is then computed by a scan with $d = 1$. One scan settles a family with $d \le m + 1$. A family with $d \le 2m + 1$ is settled by taking the first member up to the symmetry group of the family (orbit representatives by union-find over all $\binom{n}{T}$ sets) and scanning the subfamily it leaves. The families used:

- `fam S1 S2 ...`: all words having the given sets as agreement sets, so the result is the largest list containing them;
- `fix h`: all words invariant modulo codewords under $h$ independent translations (for $h = 1$ and $k$ even these are exactly the words $w'(X^2 + tX)$ lifted from $n/2$ points; lists all of whose members are invariant are lifts and are left to the smaller instance);
- `osc r`: all words of phantom degree $\le r$;
- `word`: one word, the exact list oracle.

### 2.3 Validation

**[checked]**

- The two programs share no code beyond the field multiplication and use different representations (syndromes and locators against values and divided differences). They agree on the complete all-words problems $(k, T) = (9, 12), (11, 13), (7, 11), (5, 10)$ at $n = 16$ (4, 2, 2, 2), on the phantom-degree-1 problem at $(8, 10)$ (15), and on the largest lists containing given pairs at $(8, 10)$, $(8, 11)$, $(4, 7)$, $(2, 5)$ (15, 3, 15, 6).
- Every recorded extremal word (one per class: 1910 words in 150 result files, from both generic bases, the real shape in four fields and the phantom-degree runs) was re-run through note 02's oracle `02_lists.c`, which interpolates through $k$-subsets and shares no code with this note: the number of codewords at agreement $\ge T$ equals the reported maximum in every case (`18_verify16.py`).
- With $r = 0$ the search reproduces the random-domain strict-top column of note 02 section 3 at every $(k, T)$ where both exist, and the all-words maxima at $(8, 10)$, $(8, 11)$, $(9, 11)$, $(9, 12)$ equal the multiset maxima of `12_multiset16` (15, 3, 16, 4), with extremal words that this note's cofactor test independently classifies as multiset tops.
- $(k, T) = (2, 5)$: the program finds 6, and Proposition 5.2 proves 6.
- Two independent random bases give the same maxima and the same numbers of classes in every case run on both (table of section 3).

## 3. Ground truth at $n = 16$

### 3.1 The table

**[checked]** `18_exhaust`, exhaustive. Every $(k, T)$ with $2 \le k \le 13$ and $k < T$ below the unique-decoding radius is listed (for $2T \ge n + k$ the list is 1). Columns: the Johnson bound ("below" if $T^2 \le n(k - 1)$); the generic-points value $G$ and the trivial list of section 1.4; the strict-top maximum (this note's search restricted to phantom degree 0, which equals note 02's table where both exist); the multiset-top maximum (note 12's `12_multiset16`, all masses, multiplicities $\le 2$; empty where I did not run it); the exact maximum over all words on two random bases, and the number of extremal families up to $\mathrm{AGL}(4, 2)$; the exact maximum over all words on the real shape in $\mathrm{GF}(2^{64})$ and in the three small fields (empty: not run, because with translations as the only symmetry the run is too long). "Not exhausted" means the search did not finish in 40 seconds on four cores, and by the node counts it would need hours to years; these are the rows in which five or more members are needed to pin a syndrome. The row $(5, 8)$ is settled by the phantom-degree runs of section 3.3, which reach the largest phantom degree there. The row $(4, 7)$ took 13.5 minutes on four cores (over the ten-minute budget; one basis only).

| $k$ | $T$ | $T/n$ | Johnson bound | generic points | trivial | strict tops | multiset tops | all words, generic (seed 1 / seed 2) | classes | all words, real shape $\mathrm{GF}(2^{64})$ | real shape $\mathrm{GF}(2^{10}), (2^{11}), (2^{12})$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 2 | 3 | 0.1875 | below | 13 | 7 | 35 |  | not exhausted |  |  |  |
| 2 | 4 | 0.2500 | below | 6 | 5 | 4 | 4 | not exhausted |  |  |  |
| 2 | 5 | 0.3125 | 7 | 4 | 3 | 3 | 3 | 6 / 6 | 2 |  |  |
| 2 | 6 | 0.3750 | 4 | 3 | 3 | 1 | 2 | 3 / 3 | 1012 |  |  |
| 2 | 7 | 0.4375 | 2 | 2 | 2 | 1 | 2 | 2 / 2 | 35 | 2 | 2, -, - |
| 2 | 8 | 0.5000 | 2 | 2 | 2 | 2 | 2 | 2 / 2 | 12 | 2 | 2, 2, 2 |
| 3 | 4 | 0.2500 | below | 12 | 7 | 140 |  | not exhausted |  |  |  |
| 3 | 5 | 0.3125 | below | 6 | 4 | 3 | 7 | not exhausted |  |  |  |
| 3 | 6 | 0.3750 | 16 | 4 | 3 | 7 | 7 | not exhausted |  |  |  |
| 3 | 7 | 0.4375 | 4 | 3 | 2 | 1 | 2 | 4 / 4 | 1 | 4 |  |
| 3 | 8 | 0.5000 | 3 | 2 | 2 | 2 | 2 | 2 / 2 | 55 | 2 |  |
| 3 | 9 | 0.5625 | 2 | 2 | 2 | 1 | 2 | 2 / 2 | 8 | 2 |  |
| 4 | 5 | 0.3125 | below | 11 | 6 |  |  | not exhausted |  |  |  |
| 4 | 6 | 0.3750 | below | 5 | 4 | 7 | 15 | not exhausted |  |  |  |
| 4 | 7 | 0.4375 | 64 | 3 | 3 | 15 | 15 | 15 | 2 |  |  |
| 4 | 8 | 0.5000 | 5 | 2 | 2 | 2 | 2 | 3 / 3 | 71 | 3 |  |
| 4 | 9 | 0.5625 | 2 | 2 | 2 | 1 | 2 | 2 / 2 | 35 | 2 |  |
| 5 | 6 | 0.3750 | below | 10 | 6 |  |  | not exhausted |  |  |  |
| 5 | 7 | 0.4375 | below | 5 | 4 | 15 | 30 | not exhausted |  |  |  |
| 5 | 8 | 0.5000 | below | 3 | 3 | 30 | 30 | 30 (seed 1, by phantom degree) |  |  |  |
| 5 | 9 | 0.5625 | 4 | 2 | 2 | 1 | 2 | 3 / 3 | 3 | 3 |  |
| 5 | 10 | 0.6250 | 2 | 2 | 2 | 1 | 2 | 2 / 2 | 17 | 2 |  |
| 6 | 7 | 0.4375 | below | 9 | 5 |  |  | not exhausted |  |  |  |
| 6 | 8 | 0.5000 | below | 4 | 3 | 30 |  | not exhausted |  |  |  |
| 6 | 9 | 0.5625 | 64 | 3 | 2 | 15 | 15 | 15 / 15 | 1 |  |  |
| 6 | 10 | 0.6250 | 4 | 2 | 2 | 1 | 2 | 3 / 3 | 1 | 3 |  |
| 7 | 8 | 0.5000 | below | 8 | 5 |  |  | not exhausted |  |  |  |
| 7 | 9 | 0.5625 | below | 4 | 3 | 15 |  | not exhausted |  |  |  |
| 7 | 10 | 0.6250 | 16 | 2 | 2 | 7 | 7 | 7 / 7 | 1 | 7 |  |
| 7 | 11 | 0.6875 | 3 | 2 | 2 | 1 | 2 | 2 / 2 | 17 | 2 | 2, 2, 2 |
| 8 | 9 | 0.5625 | below | 7 | 4 |  |  | not exhausted |  |  |  |
| 8 | 10 | 0.6250 | below | 3 | 3 | 7 | 15 | 15 / 15 | 1 |  |  |
| 8 | 11 | 0.6875 | 7 | 2 | 2 | 3 | 3 | 3 / 3 | 3 | 3 | 3, 3, 3 |
| 9 | 10 | 0.6250 | below | 6 | 4 |  |  | not exhausted |  |  |  |
| 9 | 11 | 0.6875 | below | 3 | 2 | 3 | 16 | 16 / 16 | 1 | 16 |  |
| 9 | 12 | 0.7500 | 4 | 2 | 2 | 4 | 4 | 4 / 4 | 1 | 4 | 4, 4, 4 |
| 10 | 11 | 0.6875 | below | 5 | 3 |  |  | not exhausted |  |  |  |
| 10 | 12 | 0.7500 | below | 2 | 2 | 4 | 5 | 5 / 5 | 1 | 8 |  |
| 11 | 12 | 0.7500 | below | 4 | 3 | 140 |  | 140 / 140 | 1 |  |  |
| 11 | 13 | 0.8125 | 5 | 2 | 2 | 1 | 2 | 2 / 2 | 5 | 2 |  |
| 12 | 13 | 0.8125 | below | 3 | 2 | 35 | 35 | 35 / 35 | 1 | 35 |  |
| 13 | 14 | 0.8750 | 8 | 2 | 2 | 8 | 8 | 8 / 8 | 1 | 8 |  |

Reading. (i) The two window points: $(8, 11)$ has $\Lambda = 3$ on all five domains, and $(2, 5)$ has $\Lambda = 6$ on every domain (proved). (ii) In every exhausted row the all-words maximum is the larger of the multiset-top value and of a polygon: it exceeds the multiset tops only in the rows $(2, 5)$, $(2, 6)$, $(3, 7)$, $(4, 8)$, $(5, 9)$, $(6, 10)$, and there it is 6, 3, 4, 3, 3, 3, never above twice the generic-points value (at $(11, 12)$ the multiset value was not computed; the strict tops already give the maximum there). (iii) All words exceed the generic-points value by a large factor exactly where tops do: the flat rows and the $5n/8$ row. (iv) The real shape equals the generic domain in every row run on both, except $(10, 12)$, where it has 8 against 5: the known doubling of the leanVM shape at depth 2 (note 02 section 3, the pair of rows $(2, 4)$ and its complement), a strict-top effect.

### 3.2 The extremal words

**[checked]** from the class descriptions printed by `18_exhaust` (sets as 16-bit masks over $\mathbb{F}_2^4$, point $x$ = bit $x$).

- **$(8, 10)$: 15, one class.** Sets `0fcf 3bf3 3cfc 5dd5 5dea 6ed9 6ee6 9ed6 9ee9 adda ade5 cbfc ccf3 f8cf ffc0`: twelve at agreement 10, three at 11. The points $6, 7, 11$ lie in all 15 sets and with the point 10 they form a 2-flat. The word is a polynomial of degree 11, $w - c_i = Z_{S_i}(X)(X - \rho_i)$ with $\rho_i \in S_i$: the padded hyperplane word $X^8 Z_C$, $C$ a codimension-2 flat minus a point, of notes 01 and 02 (which found 12 + 3 for it). So that word is extremal among all words, the class is unique, and the list of 11 that annealing found is a part of it. No word of phantom degree 0 has more than 7, and every word of phantom degree $\ge 2$ has fewer than 15.
- **$(8, 11)$: 3, three classes.** (a) `0fef f0ef ffe0`: a hyperplane plus a common set: $V$ a 2-dimensional subspace, $C$ three points of one coset of $V$, and $S = H \cup C$ for the three affine hyperplanes $H$ made of two of the other three cosets. The words with this family form a line, one of them is the strict top $X^8 Z_C$, the others have phantom degree 4 and are not tops: the same three sets are also agreement sets of non-top words. (b) `0eff fe0f fff0`: agreements 11, 11, 12. The word is a codeword plus 4 errors (its 12-member is at the unique-decoding radius) and it is a multiset top of mass 15. (c) `0fdf f8cf ffe0`: pairwise intersections 6, 7, 7, one word, with a denominator of degree 4 without roots in $D$ or at infinity: not a top. It has the same size as the tops.
- **$(9, 11)$: 16, one class.** Sets `177f 2bbf 4ddf 71f7 7f17 8eef b2fb bf2b d4fd df4d e8fe ef8e f771 fbb2 fdd4 fee8`, a single orbit of the translation group. The syndrome is $(0, 0, 0, s_3, 0, s_5, s_6)$: the word is $X^8 \ell(X)$ with $\ell = X^4 + aX^2 + bX$, a word that is invariant under all translations modulo polynomials of degree $\le 8$. It is the orbit list of Proposition 5.5, an effect of $T - k = N - 2$ that does not persist at larger $n$. Here $w - c_i = Z_{S_i}(X)(X - \rho_i)$ with $\rho_i \in S_i$, so it is also a multiset top of mass 12 (the biased padding of note 01), and its size equals $1/(16\epsilon^2)$ at $\epsilon = 1/16$ (note 12 Theorem A; that theorem is stated for degree $< k$ and I did not check that it covers degree $\le n/2$).
- **$(9, 12)$: 4**: the complements of the four cosets of a 2-dimensional subspace (strict top). **$(4, 7)$: 15**, two classes, both the fifteen 3-flats through a point with that point removed; in one class the word is free at the removed point, in the other it also meets one member there. **$(6, 9)$: 15 and $(7, 10)$: 7**: strict tops, an affine hyperplane plus one, respectively two, common points (note 02 section 4, item 3). **$(11, 12)$: 140, $(12, 13)$: 35, $(13, 14)$: 8**: strict tops, the classes of note 02 at depth 1.
- **$(10, 12)$: 5 (generic), a multiset top of mass 13**, against 4 for strict tops. On the real shape 8.
- **$(2, 5)$: 6, two classes, one configuration.** (a) `1780 1870 244c 422a 8116 e880`: six lines, every nonzero point on exactly two of them, the point 0 unused: the Sidon tangent lines $y = aX + a^2$, $a$ in a Sidon set of six elements, meeting at $X = a + a'$ (note 02 section 8). The word is free at the unused point. (b) `022b 02d4 0d24 3118 9442 e881`: the same hexagon translated by $t = 14$ (every triangle of meeting points sums to 14), with the value at the unused point chosen on one of the six lines, which then has agreement 6. Both have phantom degree 10, the largest possible, and they are not multiset tops of any mass up to 32 (`12_multiset16` gives 3).
- **$(3, 7)$: 4, one class**, `0c1f 30ec c1c3 fe00`: four sets pairwise meeting in the two points of a coset of $V = \{0, 1\}$, 12 points on two sets and 4 on one. It is Proposition 5.3 with $|V| = 2$, $L = 4$ (four lines in the plane of the 8 labels, meeting at the labels $a_i + a_j + t$ for a Sidon set of 4 in $\mathbb{F}_2^3$), each line with one extra point.
- **$(4, 8)$: 3, 71 classes; $(6, 10)$: 3, one class; $(5, 9)$: 3, three classes; $(2, 6)$: 3, 1012 classes**: three members pairwise sharing at most $k - 1$ points. All 71 classes at $(4, 8)$, the class at $(6, 10)$, two of the three at $(5, 9)$ and 34 of the 40 printed at $(2, 6)$ are triangles in the sense of section 5.3 (the pairwise intersections are a common core plus cosets of one subspace); the others are degenerate triangles in which two members share fewer points. **$(2, 7)$, $(2, 8)$, $(3, 8)$, $(3, 9)$, $(4, 9)$, $(5, 10)$, $(7, 11)$, $(11, 13)$: 2**, pairs.

### 3.3 The rows that were not exhausted

For these rows the search restricted to words of phantom degree $\le r$ is feasible for small $r$. **[checked]** exhaustive for each $r$ shown, generic domain (basis 1), and the real shape for $r \le 2$.

| $k$ | $T$ | largest phantom degree $e - 1$ | generic, $r = 0, 1, 2, \dots$ | all words, generic | real shape $\mathrm{GF}(2^{64})$, $r = 0, 1, 2$ |
| --- | --- | --- | --- | --- | --- |
| 2 | 3 | 12 | 35, 35, 35, 35, 35 | not exhausted |  |
| 2 | 4 | 11 | 4, 4, 4, 5, 8, 8, 8, 8, 8 | not exhausted | 8, 8, 8 |
| 3 | 4 | 11 | 140, 140, 140, 140 | not exhausted |  |
| 3 | 5 | 10 | 3, 7, 7, 16, 16, 16, 16 | not exhausted |  |
| 3 | 6 | 9 | 7, 7, 7, 7, 7, 7, 7, 7, 7 | not exhausted |  |
| 4 | 6 | 9 | 7, 15, 15, 15, 15, 15 | not exhausted | 15, 15, 15 |
| 4 | 7 | 8 | 15, 15, 15, 15 | 15 | 15, 15, 15 |
| 5 | 7 | 8 | 15, 30, 30, 30, 30, 30 | not exhausted |  |
| 5 | 8 | 7 | 30, 30, 30, 30, 30, 30, 30, 30 | 30 |  |
| 6 | 8 | 7 | 30, 30, 30, 30, 30, 30 | not exhausted |  |
| 7 | 9 | 6 | 15, 23, 23, 23, 23, 23 | not exhausted |  |
| 8 | 10 | 5 | 7, 15, 15, 15, 15, 15 | 15 | 15, 15, 15 |
| 8 | 11 | 4 | 3, 3, 3, 3 | 3 |  |
| 9 | 11 | 4 | 3, 16, 16, 16, 16 | 16 | 9, 16, 16 |

Lower bounds for all words in these rows, from the annealed words of note 02 re-examined with the exact oracle of this note (`18_sub word`): $(4, 6)$: 16 on the generic domain and 17 on the real shape, both words of phantom degree 9 (the largest possible) that are not tops; the list of 16 has agreements $8 \times 6$, $7 \times 7$, $1 \times 8$ and contains most of the flat family of $(4, 7)$, the list of 17 has all agreements equal to 6. $(2, 4)$: 9, phantom degree 11, irregular configurations of nine lines with point degrees between 1 and 4, not of Sidon type. Both rows are below every window: $(4, 6)$ is rate 1/4 at $3n/8$, under the flats, and $(2, 4)$ is the flat boundary $n/4$ of rate 1/8, where lists grow with $n$ anyway. 

Reading the profiles. They are flat after one to three steps. $(4, 6)$: no word of phantom degree $\le 5$ has more than 15 (the flats, which are a multiset top of mass 7 here), so the lists of 16 and 17 need phantom degree 6 to 9. $(2, 4)$: at most 8 up to phantom degree 8 (the cosets of two complementary 2-dimensional subspaces, for a linearized word of degree 8: the orbit list of Proposition 5.5 for $k = 2$, not a top, against 4 for multiset tops), and 9 at phantom degree 11. $(3, 5)$, the slack-1 version of the window point $(2, 5)$: 16 from $r = 3$ on, again an orbit list of a word that is not a top, and nothing larger up to $r = 6$. $(3, 6)$: 7 up to $r = 8$ of 9. $(5, 8)$: the profile reaches the largest phantom degree, so 30 (the affine hyperplanes) is the exact maximum over all words, and the row is exhausted in this way. $(7, 9)$: 23 from $r = 1$ on, a multiset top of mass 10. $(2, 3)$ and $(3, 4)$: the strict-top values 35 and 140 up to $r = 4$ and $r = 3$. Apart from the two orbit lists, no word of the phantom degrees covered beats the multiset tops in any row.

### 3.4 The real shape and small fields

**[checked]** On the real shape the only symmetries are the 16 translations, so the exhaustive search costs about 20000 times more and was run on the 19 rows of the table where that is affordable. The window point $(8, 11)$ has maximum 3 in $\mathrm{GF}(2^{64})$ (1529 classes of triples under translations), in $\mathrm{GF}(2^{10})$ (1613 classes), in $\mathrm{GF}(2^{11})$ (1949) and in $\mathrm{GF}(2^{12})$ (1529): a smaller field has more accidental triples, and still no list of 4. $(9, 11)$ has 16 in $\mathrm{GF}(2^{64})$ (168 classes under translations), and $(9, 12)$ has 4 in all four fields. $(2, 5)$ is 6 by Proposition 5.2. The boundary rows $(8, 10)$ and $(4, 7)$ are too expensive on the real shape for all words; for phantom degree $\le 2$ they are in the profile table above.

## 4. $n = 32$: what was exhausted and what was sampled

Full exhaustion is out of reach: at $(32, 16, 22)$ a syndrome is pinned by a pair of 22-sets plus one more set, there are about $4 \cdot 10^6$ classes of pairs under $\mathrm{AGL}(5, 2)$, and one pair costs 35 to 60 CPU-seconds, so about 5 CPU-years; at $(32, 16, 21)$ and at rate 1/8 it is worse. What can be exhausted are linear families of words (`18_sub`, section 2.2). Everything below is on a generic domain (basis 1; a second basis where stated), **[checked]**, and "exhausted" means: the stated number is the exact maximum list over all words of the family.

### 4.1 Rate 1/2

| family of words | $k$ | $T = 20$ | $T = 21$ | $T = 22$ | $T = 23$ |
| --- | --- | --- | --- | --- | --- |
| strict tops (note 02, exhaustive) | 16 | 7 | 3 | 3 | 3 |
| phantom degree $\le 1$ (degree $\le T + 1$) | 16 | not finished in 400 s | 6 | 3 (two bases) | |
| phantom degree $\le 2$ | 16 | | 16 | 3 | |
| phantom degree $\le 3$ | 16 | | 16 | 3 | |
| phantom degree $\le 4$ | 16 | | 16 | 3 | |
| phantom degree $\le 5$ (at $T = 22$: degree $\le 27$ of at most 31) | 16 | | not run | 3 | |
| all words invariant under one translation modulo codewords (8-dimensional family, 80 classes of first members, plus the lifts from $n = 16$) | 16 | | not run | 3 (two bases) | |
| fully translation-invariant words $X^{16}\ell(X)$, degree $\le n/2$ | 17 | | 16 | 16 | 4 |

The extremal words at $T = 21$: for $r \le 1$, six sets with all pairwise intersections 14, a multiset top of mass 22; for $r \le 2$, $3$ and $4$, sixteen sets, fifteen at agreement 21 and one at 22, seven points common to all of them and the other 25 points in nine each, pairwise intersections 14 and 15, $w - c_i = Z_{S_i}(X)(X - \rho_i)(X - \rho_i')$ with $\rho_i, \rho_i' \in D$: a multiset top of mass 23 of the form $1_{H_i} + 1_B$, $B$ the seven common points, each hyperplane $H_i$ meeting $B$ in two points (one for the member at 22). This is the biased padding of note 01 section 3.4 at its first nontrivial size. The extremal words at $T = 22$ are the lifts of the three classes of $(16, 8, 11)$, and in the slack rows the lift of the list of 16 of $(16, 9, 11)$ and the four cosets.

**Sampled, not exhausted.** The largest list containing a given pair of 22-sets (`fam`, one scan each, exhaustive for that pair): the lift of the pair of class (a) of $(16, 8, 11)$: 3; the pair of intervals $\{x < 22\}, \{x \ge 10\}$ (in the index order of $\mathbb{F}_2^5$): 3; four random pairs with $S_0 \cup S_1 = D$: 2 each, that is no third member exists for any word. This says that triples at $T = 22$ are rare and come from structure, and nothing about lists that contain none of the six pairs.

### 4.2 Rate 1/8

| family of words | $T = 9$ | $T = 10$ | $T = 11$ |
| --- | --- | --- | --- |
| strict tops (note 02; phantom degree 0 re-run here at $T = 11$) | 3 | 3 | 3 |
| phantom degree $\le 1$ | 4 | 4 | 3 |
| phantom degree $\le r$, largest $r$ run | 4 for $r \le 4$ (degree $\le 13$) | 4 for $r \le 5$ (degree $\le 15$) | 3 for $r \le 5$ (degree $\le 16$) |
| lists containing four, or five, of the six lifted Sidon lines | | 6 and 6 | |
| lower bound for all words | 6 | 6 (Proposition 5.3) | 3 |
| generic points / trivial | 5 / 4 | 4 / 4 | 3 / 3 |

At rate 1/8 the phantom degree of a word can be as large as $e - 1 = 20$ to 22, and the Sidon word itself has the largest possible phantom degree, so the low-phantom-degree families say little here: they show that the excess over tops at this rate does not come from polynomials of moderate degree. The lists of 4 at $T = 9, 10$ are multiset tops of mass $T + 1$ with a common core of two or three points; they equal the trivial list. The translation-invariant families, which were decisive at rate 1/2, are too large at rate 1/8 for one or two levels of scanning (dimension 14 for one translation). So at rate 1/8 and $n = 32$ the all-words maximum is only known to lie between 6 and the counting bounds (10 at $T = 11$ by the Johnson count, since $121 > 96$).

### 4.3 Rate 1/4

Not searched at $n = 32$. At rate 1/4 there is no window: the flats give $n - 1 = 31$ at $T = 15$, and the strict tops have 15 and 7 at $T = 14$ and $13$ (note 02). What this note adds are the exact rows of $n = 16$, which lift: 15 at $T = 14$ (the flats of $(16, 4, 7)$) and 3 at $T = 16$, the Johnson radius (the triangles of $(16, 4, 8)$). With slack 1 the orbit list of Proposition 5.5 has 32 members at $(k, T) = (9, 12)$.

### 4.4 Reading

At the fraction $11/16$ of rate 1/2 the list sizes are the same at $n = 16$ (exact, all words) and at $n = 32$ (all classes above): 3 genuine, 16 with slack 1. At the new fraction $21/32$ the multiset tops already reach 16. Together with the exact value 15 at $5/8$ for $n = 16$ and the lists of at least 28 at $5/8$ for $n = 32$ (note 02), this is the profile that note 12 Theorem A predicts for multiset tops: a bound $1/(16\epsilon^2)$ at $\tau = 5/8 + \epsilon$ that does not depend on $n$, approached quickly. No word that is not a top appears as an extremal word at $n = 32$ in any family searched.

## 5. Scaling of the non-top configurations

### 5.1 Two operations that carry lists between instances

**Lemma 5.1 (lifting, note 02 Lemma 3, and anti-shortening). [proved]** (a) If $V \subseteq D$ is a subspace and a word on the label space $\Lambda' = L_V(D)$ has $L$ codewords of degree $< k'$ at agreement $T'$, then its composition with $L_V$ has $L$ codewords of degree $< k'|V|$ at agreement $T'|V|$ on $D$. (b) If $P \subset D$ has $p$ points and a word $w'$ on the point set $D \setminus P$ has $L$ codewords $c'$ of degree $< k - p$ at agreement $T - p$, then the word equal to $Z_P w'$ outside $P$ and to $0$ on $P$ has the $L$ codewords $Z_P c'$ of degree $< k$ at agreement $T$. Conversely a list all of whose agreement sets contain $P$ arises in this way (note 02 Lemma 4).

*Proof.* (a) is note 02. (b): $Z_P c'$ vanishes on $P$ and agrees with $Z_P w'$ wherever $c'$ agrees with $w'$. $\square$

(a) keeps the rate and the agreement fraction. (b) does not keep the domain a subspace, which is why it does not reduce the subspace problem to smaller subspace problems, but it turns any list on any point set inside $D$ into a list on $D$. Both operations give lists of constant size.

### 5.2 The Sidon tangent lines

**Proposition 5.2 (the window point of rate 1/8 at $n = 16$). [proved]** For every set of 16 evaluation points in every field, a word has at most 6 polynomials of degree $\le 1$ at agreement $\ge 5$. On every 4-dimensional $\mathbb{F}_2$-subspace the bound is attained. So $\Lambda(5) = 6$ at $(n, k) = (16, 2)$ on every subspace domain, generic or real.

*Proof.* Members are lines through at least 5 of the 16 graph points, and two members share at most one graph point. Let $r_x$ be the number of members through the graph point over $x$. The members through one point cover disjoint sets of at least 4 other points, so $r_x \le 3$. If all $r_x \le 2$ then $5L \le \sum r_x \le 32$ and $L \le 6$. Otherwise fix $x$ with $r_x = 3$: its three lines cover 12 other points and leave a set $R$ of 3 points. Any other member meets each of the three lines in at most one point, so it has at least 2 of its 5 points in $R$. Two such members share at most one point, so they have exactly 2 points in $R$ each and different pairs: at most 3 such members, and $L \le 6$. The construction is the next proposition with $L = 6$ (a Sidon set of 6 elements in $\mathbb{F}_2^4$, whose 15 sums are the 15 nonzero vectors). $\square$

**Proposition 5.3 (Sidon lines with lifting and anti-shortening). [proved]** Let $V \subseteq D$ be a subspace, $\Lambda' = L_V(D)$ with $M' = n/|V|$ labels, $A \subset \Lambda'$ a Sidon set with $L$ elements (the sums $a + a'$, $a \ne a'$, are pairwise distinct) and $P' \subset \Lambda'$ a set of $p'$ labels disjoint from these sums. Let $w = Z_{P'}(y)\, a a'$ on the fibre of $y = a + a'$, $w = 0$ on the fibres of $P'$, and $w$ arbitrary elsewhere. Then the $L$ polynomials $c_a = Z_{P'}(L_V(X))\,(a\, L_V(X) + a^2)$, of degree $(p' + 1)|V|$, agree with $w$ on $(p' + L - 1)|V|$ points each. So with $k = (p' + 2)|V|$ and $T = k + (L - 3)|V|$,
$$\Lambda(T) \ge L \qquad\text{whenever}\qquad \tbinom{L}{2} + p' \le M' \text{ and } \mathbb{F}_2^{\log_2 M'} \text{ has a Sidon set of size } L .$$

*Proof.* At $y = a + a'$, $a y + a^2 = a a'$, symmetric in $a, a'$. The $c_a$ are distinct, vanish on the fibres of $P'$, and $c_a$ agrees with $w$ on the fibres of the $L - 1$ labels $a + a'$. $\square$

**[checked]** `18_sidon.py`, with the exact oracle, on the real shape: $(n, |V|, p', L) = (16, 1, 0, 6)$, $(32, 2, 0, 6)$, $(32, 1, 2, 7)$, $(32, 1, 14, 6)$, $(16, 1, 6, 5)$, $(32, 2, 6, 5)$: the oracle finds exactly $L$ codewords at agreement $T$ in each case (rates 1/8 and 1/2).

**Corollary 5.4 (the Sidon family does not scale). [proved]** In Proposition 5.3, $\tau - \rho = (L - 3)/M'$ and $\binom{L}{2} \le (1 - \rho) M' + 2$, hence $L - 1 < 2(1 - \rho)/(\tau - \rho) + 4/L$. More generally, a list in which every point outside a common core $P$ of the agreement sets lies in at most $j$ of them has $L \le j(n - |P|)/(T - |P|) \le j(n - k + 1)/(T - k + 1)$, that is $j$ times the trivial list. So lists of this type are bounded in terms of $(\rho, \tau)$ alone, by about twice the trivial list for the Sidon lines. In the rate-1/8 window the family gives 6 at $\tau = 5/16$ for every $n \ge 16$ (lift of $n = 16$) and nothing else: with 32 labels the largest Sidon set has 7 elements (exhaustive search, `18_sidon.py max 5`) and reaches only $\tau = 1/4$, and with more labels $\tau < 1/4$. At rate 1/2 it gives 5 at $\tau = 5/8$ and stays below $5/8$ otherwise.

*Proof.* The first inequality is $L(L-1) \le 2(1-\rho)M' + 4$ with $M' = (L-3)/(\tau - \rho)$. The second counts incidences outside $P$: each member has at least $T - |P|$ of them, and $|P| \le k - 1$. $\square$

This answers the question about the Sidon family: it is the $j = 2$ case of a configuration whose list is at most $j$ times the trivial one, it exists at every rate and on every domain that contains the needed sums, and it does not grow with $n$ at fixed $(\rho, \tau)$. A growing family needs points lying on an unbounded number of members: at agreement $\tau n$ the average point lies on $\tau L$ of them.

### 5.3 Triangles

**[proved]** Three lines in a label plane with prescribed vertex labels always exist (two free slopes, one condition), so by Lemma 5.1 every domain has lists of 3 of the form $Z_P(X) \cdot \ell_i(L_V(X))$, $i = 0, 1, 2$: each member agrees on $P$, on the fibres of its two vertices and on a third of the remaining points, which gives $T - k = \lfloor (n - k + |V| - 2)/3 \rfloor$ for $|P| = k - |V| - 1$. With $|V| = 1$ this is the generic-points value for a list of 3, and each doubling of $|V|$ gains a third of $|V|$ points. **[checked]** In all 71 extremal classes at $(k, T) = (4, 8)$ the three sets meet pairwise in $\{p, a, b\}$, $\{p, c, d\}$, $\{p, u, v\}$ with one common point $p$ and $a + b = c + d = u + v$, which is this construction with $P = \{p\}$ and $|V| = 2$. So the list of 3 at the Johnson radius of rate 1/4, against 2 for strict tops and 1 found by the annealing of note 02, is a triangle. Four or more lines in general position have more conditions than parameters ($\binom{L}{2}$ vertex labels against $2L - 3$ parameters), and need additive structure such as the Sidon sets above: this is why the generic-points value is the natural size of lists of unstructured words.

### 5.4 Multiset tops near $5n/8$ at rate 1/2

**[checked]** At rate 1/2 and at or above $5n/8$, every list found here with more than 3 members is a multiset top, except the orbit lists of section 5.5 with slack 1:

| $n$ | degree | $T$ | $\epsilon = T/n - 5/8$ | largest list | status | word | $1/(16\epsilon^2)$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 16 | $< n/2$ | 10 | 0 | 15 | exact, all words | $X^8 Z_C$, mass 11 | |
| 16 | $< n/2$ | 11 | $1/16$ | 3 | exact, all words | | 16 |
| 16 | $\le n/2$ | 11 | $1/16$ | 16 | exact, all words | $X^8 \ell(X)$, mass 12 | 16 |
| 32 | $< n/2$ | 20 | 0 | at least 28 (note 02, one padded word) | | | |
| 32 | $< n/2$ | 21 | $1/32$ | 16 | exact for phantom degree $\le$ 4 | $1_{H_i} + 1_B$, mass 23 | 64 |
| 32 | $< n/2$ | 22 | $1/16$ | 3 | exact in the families of section 4.1 | | 16 |
| 32 | $\le n/2$ | 21, 22 | $1/32$, $1/16$ | 16, 16 | exact for the fully invariant words | $X^{16}\ell(X)$, mass 24 | 64, 16 |

Their scaling is known: on a generic domain note 12 Theorem A bounds the multiset tops at $\tau = 5/8 + \epsilon$ by $\max(1/(16\epsilon^2),\ 1 + (2\tau - \tfrac12)/\epsilon)$ for every $n$ **[proved there]**, and note 01 constructs $3/(64\epsilon^2)$. So these lists are bounded at a fixed fraction inside the window and grow only as the fraction tends to $5/8$; at exactly $5n/8$ they grow with $n$ (15 at $n = 16$, and note 02 found 28 for one padded word at $n = 32$).

This settles the two $n = 16$ questions of the brief. *Rate 1/2, "11 against 7" at $(8, 10)$:* the truth is 15, attained by one word up to symmetry, the padded hyperplane word, a multiset top; it scales as multiset tops do. *Rate 1/4, "16 against 7" at $(4, 6)$:* these are lists of words that are not tops (phantom degree 9), 16 on the generic domain and 17 on the real shape are lower bounds, and the row is not exhausted. It lies at $3n/8$, under the flat family, which already has $n - 1$ members at $n/2 - 1$ for every $n$, so no threshold at rate 1/4 depends on it. The rows of rate 1/4 that matter are exact: 15 at $(4, 7)$, the flats, and 3 at $(4, 8)$, the triangles.

### 5.5 Orbit lists of translation-invariant words

The lists of 16 at $(9, 11)$ and at $(3, 5)$ (degree $\le n/2$ and degree $\le n/8$ at $n = 16$, that is slack 1) are one translation orbit each. The second one is not a top of any kind and has more than twice the multiset-top maximum (7), so it needs an explanation. It is the following counting fact.

**Proposition 5.5. [proved]** Let $J(k)$ be the set of exponents $j$, $k \le j < n$, with $\binom{j}{i}$ even for all $k \le i < j$. (a) On every subspace domain the words that are invariant modulo codewords under all translations by $D$ are, modulo codewords, the span of the $X^j$, $j \in J(k)$. (b) $J(2^\kappa) = \{2^a : \kappa \le a < N\}$ (linearized words), and $J(2^\kappa + 1) = \{2^\kappa + 2^b : 0 \le b < \kappa\} \cup \{2^a : \kappa < a < N\}$, with $N - 1$ elements: the words $X^{2^\kappa}\ell_1(X) + \ell_2(X)$ with $\ell_1, \ell_2$ linearized. (c) For every set $S$ of $T = k + |J(k)| - 1$ points there is a nonzero invariant word $w$ and a codeword $c$ with $w = c$ on $S$, and then for every $t \in D$ the word $w$ agrees on $S + t$ with the codeword $c(X + t) + w(X) - w(X + t)$. So $w$ has a list of $n / |\mathrm{Stab}|$ at agreement $k + |J(k)| - 1$, where $\mathrm{Stab}$ is the group of $t$ for which that codeword is $c$. With slack 1 this is $T = k + N - 2$.

*Proof.* (a) $w = \sum_{j \ge k} c_j X^j$ is invariant under $t$ if and only if for every $i \ge k$ the coefficient $\sum_{j > i} \binom{j}{i} t^{j - i} c_j$ of $X^i$ in $w(X + t) - w(X)$ vanishes. As a polynomial in $t$ it has degree $< n$ and must vanish on the $n$ elements of $D$, so it is zero: $c_j = 0$ unless $\binom{j}{i}$ is even for all $k \le i < j$. (b) is Lucas' theorem: an exponent with a bit $2^a$, $2^a \ge k$, and anything else has the odd binomial $\binom{j}{2^a}$, and for $j = 2^\kappa + j'$, $i = 2^\kappa + i'$, $\binom{j}{i} \equiv \binom{j'}{i'}$, which is even for all $0 < i' < j'$ exactly when $j'$ is a power of two. (c) There are $|J(k)| + k$ unknown coefficients of $(w, c)$ and $T$ conditions, one fewer, and $w = 0$ would give a codeword with $T \ge k$ roots. $\square$

**[checked]** $n = 16$: $J(9) = \{9, 10, 12\}$ and $T = 11$, $J(3) = \{3, 4, 8\}$ and $T = 5$: `18_sub ... fix 4`, exhaustive over the invariant words, finds exactly 16 in both cases, and at $T + 1$ only 4 and 2 (cosets). At $(9, 11)$ the twelfth root of $w - c$ is the sum of the other eleven (the coefficient of $X^{11}$ is zero), so it lies in $D$: if it is one of the eleven the list is the 16 translates and a multiset top of mass 12, and if not the member has agreement 12, its set is the complement of a 2-flat, and the orbit collapses to the four cosets of $(9, 12)$. At $(3, 5)$ the three extra roots only sum to an element of $D$, and the list of 16 is not a top. $n = 32$: $J(17) = \{17, 18, 20, 24\}$, $J(9) = \{9, 10, 12, 16\}$, $J(5) = \{5, 6, 8, 16\}$, so the orbit lists sit at $T = k + 3$: `18_orbit.py` builds the word from a random $S$ on the real shape, and the exact oracle finds 32 codewords at $(k, T) = (17, 20)$ and at $(9, 12)$, none of them a top, and 562 at $(5, 8)$ (where flats give more anyway). At $T = 21, 22$ ($k = 17$) and $T = 9, 10$ ($k = 5$) the exhaustive search over the invariant words finds only the lifts of the $n = 16$ lists, 16 members.

**Scaling. [proved]** The agreement of an orbit list exceeds $k$ by $|J(k)| - 1 \le N - 1$, a number of points that is logarithmic in $n$. So at a fixed fraction $\tau > \rho$ these lists disappear as $n$ grows: they are visible at $n = 16$ only because $N - 2 = 2$ points is an eighth of the domain there, and the non-top list of 16 at $(3, 5)$ does not scale. The same count applies to the words invariant under a subgroup $H$ of translations: $|H|$ members at $T - k = \dim - 1$. **[checked]** for $|H| = 2$, $n = 32$, $k = 16$ the invariant words are exactly the lifts from 16 points (dimension $8 = M/2$), and in general the lifts contribute $(1 - \rho) n / |H|$ dimensions, which makes $|H| \approx (1 - \rho)/(\tau - \rho)$: the trivial list size. I did not determine the dimension of the invariant words for all $H$ and $k$, so that orbit lists never beat the trivial list by a constant factor at fixed $\tau$ is **[conjectured]** beyond the cases computed (section 4.1: no list above 3 among all words invariant under one translation at $(32, 16, 22)$).

### 5.6 What a growing list of a non-top word would have to look like

**[proved]** from sections 1 and 5: (i) its word has phantom degree larger than whatever is exhausted (section 4), in particular not a polynomial of degree close to $T$; (ii) its points lie on an unbounded number of members, so it is not of polygon type, and its agreement exceeds $k$ by more than a logarithmic number of points, so it is not an orbit list of Proposition 5.5; (iii) by Corollary 1.3 the excess of its rank conditions must come from triples and larger subfamilies, since pairs carry no information on any domain; (iv) at $n = 16$ no such list exists in either window for genuine degree, because the exhaustive maxima there are attained by multiset tops or by polygons. I found no candidate mechanism, and none of the searches of section 4 found a list of a non-top word above the multiset values at $n = 32$.

## 6. The decisive question, and what a larger computation could settle

**Is there a family of arbitrary words whose list grows with $n$ at fixed $(\rho, \tau)$ inside a window?** None was found, and the answer supported by the data is no, **[conjectured]** (it is Conjecture G of note 12), on the following grounds.

1. *Exact, small.* At $n = 16$ the windows contain two points. At $(8, 11)$ the maximum over all words is 3, the strict-top value, on a generic domain, on the real shape, and in three small fields. At $(2, 5)$ it is 6 on every domain, by a proof, and the configuration is the Sidon hexagon.
2. *Every non-top list found that beats the tops is a polygon or an orbit list.* Polygons are bounded by a constant times the trivial list at fixed $(\rho, \tau)$ (Corollary 5.4, proved): the Sidon lines, the lists of 3 at $(4, 8)$, $(2, 6)$, $(5, 9)$, $(6, 10)$, the list of 4 at $(3, 7)$. Orbit lists of translation-invariant words have agreement $k + O(\log n)$ (Proposition 5.5, proved): the list of 16 at $(3, 5)$.
3. *Every other large list found is a multiset top*, at $n = 16$ (15, 16, 5, and the strict tops) and at $n = 32$ (6 and 16 at $T = 21$). For multiset tops note 12 proves bounds in the windows that do not depend on $n$.
4. *No growth between the two sizes at the same fraction.* $11/16$ at rate 1/2: 3 and 3 (16 and 16 with slack 1). $5/16$ at rate 1/8: 6 and at least 6, with no seventh member through four of the six lifted lines; with slack 1, 16 and 16 among the invariant words.

The lists do grow, and fast, as the fraction approaches the boundary of the window from inside: at rate 1/2, 3 at $\epsilon = 1/16$, 16 at $\epsilon = 1/32$, and unbounded at $\epsilon = 0$. Any list budget for a threshold $A = (5/8 + \epsilon)n$ has to be read off $1/(16\epsilon^2)$ and not off the strict-top values (3 or 4): at level 0 of the real system, with slack $\ell = 6$, a threshold a few points above $5n/8$ sits at $\epsilon \approx 2^{-22}$, where that bound is useless. A threshold at a fixed $\epsilon$, such as $0.64 n$ ($\epsilon = 0.015$, bound 278) is what the multiset theorem supports.

What is not settled, and what each next step costs (four cores of this machine):

| computation | what it would decide | estimated cost |
| --- | --- | --- |
| $(32, 16, 21)$, all words invariant under one translation | whether lifted words with non-lifted members beat 16 at the new window point | about 80 minutes (150 first members, 30 s each) |
| $(32, 16, 22)$, phantom degree $\le 6$ | one more step of the profile, which is 3 up to 5 | about 40 minutes and 3 GB |
| $(32, 16, 22)$, phantom degree 7 to 9 (all words) | the exact $\Lambda(22)$ at $n = 32$ | needs a third level: about $10^4$ times the above, out of reach |
| $(32, 16, 22)$, all words, by pairs | the same | about 5 CPU-years ($4 \cdot 10^6$ pair classes) |
| $(16, 4, 6)$ and $(16, 2, 4)$, all words | exact maxima below the windows (16 or 17, and 9, are lower bounds) | $(4, 6)$ at phantom degree $\le 6$: 10 minutes; all words: years |
| $(16, 8, 10)$ on the real shape, all words | whether the real shape has more than the 15 of the generic domain at $5n/8$ | about 300 CPU-hours with translations only |
| $(64, 32, 44)$, words invariant under a 4-element group of translations | growth at $11/16$ one size further | not estimated; the scan has $\binom{64}{20}$ leaves and needs a different enumeration |

The honest summary is that the all-words problem is closed at $n = 16$ (where it holds no surprise in the windows), and at $n = 32$ only inside linear families of dimension up to $2m + 1$. The complement of those families is where a counterexample to Conjecture G would have to live, and its words would have to be far from polynomial (phantom degree above 5 at $T = 22$), invariant under no translation, and neither polygons nor orbit lists.

## 7. Reproduction

All under `doc/whir_soundness_gap_notes/scripts/`. C with the system compiler, Python 3 without dependencies, nothing installed; binaries and outputs were kept outside the repository.

```
cc -O2 -mcpu=native -o ex  18_exhaust.c -lpthread
cc -O2 -mcpu=native -o sub 18_sub.c -lpthread
cc -O2 -mcpu=native -o lists02 02_lists.c        # note 02's oracle, for the independent check
cc -O2 -o ms16 12_multiset16.c                   # note 12's multiset enumeration
```

| script | what it does | time (4 threads) |
| --- | --- | --- |
| `18_gf.h` | $\mathrm{GF}(2^m)$, $m \in \{8..16, 20, 32, 64\}$, lazily reduced inner products | |
| `18_exhaust.c`: `ex k T dom seed threads [target [r]]` | exact $\Lambda(T)$ over all words at $n = 16$, extremal families and their classes; `dom` = `rand`, `real64`, `real10`, ...; `r` restricts to phantom degree $\le r$ | under 1 s to 15 s, except $(4, 7)$: 13.5 min |
| `18_run16.sh bin out dom seed seconds` | the sweep over all $(k, T)$ with a time limit per case | 25 min with a 40 s limit |
| `18_profile16.sh bin out dom seed seconds "k T" ...` | the phantom-degree runs of section 3.3: $r = 0, 1, \dots$ until the first run over the limit | 30 min for the 17 rows with a 100 s limit |
| `18_table16.py dir` | the tables of section 3 from the result files | |
| `18_results.txt` | the raw `RESULT` lines of every run and the printed classes of the main rows | |
| `18_verify16.py lists02 files...` | re-checks every recorded extremal word with note 02's oracle | seconds |
| `18_sub.c`: `sub N k T dom seed threads mode ...` | exact maximum over a linear family of words, $n = 16$ or 32; modes `fam`, `fix`, `osc`, `fixosc`, `word` (section 2.2); `VERBOSE=1` prints every node | 1 s to 7 min, see `18_run32.sh` |
| `18_run32.sh bin out [group]` | the runs of section 4 | about 80 min in all; the longest runs are `fix 1` (7 min), `osc 4` and `osc 5` at $T = 22$ (10 and 8 min) and `osc 4` at $T = 21$ (11 min) |
| `18_sidon.py sub N v p L` | Proposition 5.3, built on the real shape and checked with the exact oracle | seconds |
| `18_orbit.py sub N k [seed]` | Proposition 5.5 (c): the orbit list of a random set, built on the real shape and checked with the exact oracle | seconds |

Two runs are above the ten-minute guideline: $(k, T) = (4, 7)$ at $n = 16$ (13.5 minutes) and phantom degree $\le 4$ at $(32, 16, 21)$ (11 minutes, while another run shared the machine). Several runs were started side by side, so at times eight cores were in use.
