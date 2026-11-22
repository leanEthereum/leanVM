# 06. Changing the code: can leanVM's WHIR be rebuilt on a capacity-achieving code?

Researcher 06. Notation as in `doc/whir_soundness_gap.md` and `00-lead-notes.md`: $K = \mathrm{GF}(2^{64})$, $E = \mathrm{GF}(2^{128})$, level 0 has $2^\ell = 64$ lanes of degree $< k = 2^\kappa$ on $n = 2^{\kappa+R}$ points, rate $\rho = 2^{-R}$, and $t = \lceil 108/\log_2(n/(A-1))\rceil$ queries. The main profile is $\mu = 30$, $\kappa = 24$.

Every statement is tagged: **[lit]** proven in the literature (with the exact place, and how much of it I read), **[proved]** proved here, **[checked]** checked numerically (sizes given), **[estimate]** an unproved cost estimate, **[conj]** conjectured. Scripts: `scripts/06_frs_numbers.py` (all tables of sections 3 and 4) and `scripts/06_coset_domain_check.py` (section 6).

## 0. Verdict

1. **A capacity-achieving level 0 is feasible and provable today, in characteristic 2, and it is useless.** The design is forced: $2^\ell$ lanes, each encoded by an $m$-folded Reed-Solomon code, one Merkle leaf holding $2^\ell \cdot m$ field elements (section 2). Lists and mutual correlated agreement up to $1-\rho-\eta$ are proven for it with error about $n/|E|$ (section 1). But the folding parameter must be $m \ge 64$ just to match the Johnson radius at rate 1/2 and $m \approx 256$ to save 30% of the queries, so the leaf grows by $m$ while the query count drops by at most 2. For every $m$ that lowers the query count, level 0's proof bytes grow by 13 to 280 times and its Keccak count by 5 to 100 times (section 3).
2. **No subspace-design code, known or future, can help under the known proof technique** [proved, section 4]: any such code over the alphabet $E^m$ has $\tau(r) \ge 1 - m/r$, which caps the provable radius at about $(1-\rho)\bigl(1-\frac{2-\rho}{m+1-\rho}\bigr)$. Even a hypothetical optimal code costs more bytes and more Keccaks than today at every rate and every $m$ from 2 to 1024.
3. **The only codes that could pay are those with no alphabet blow-up** (plain RS with a better domain). There, what is proven is unusable for us: prime fields or characteristic larger than $k$ [BCP+26, Jer26, DKT26], random evaluation points with field size $n + k\,2^{10L/\eta}$ [AGL24] (numerically below Johnson at 128 bits), or explicit points in an extension tower with many pairwise coprime degrees [AGG26] (impossible inside $\mathrm{GF}(2^{128})$, section 1.3).
4. **The proven way to halve the queries is to square the rate.** Capacity at rate $\rho$ gives $\log_2(1/\rho)$ bits per query, exactly what Johnson gives at rate $\rho^2$. Any code change has to beat "level 0 at $R+R$ instead of $R$" (twice the commit work from $R=1$ to $R=2$), and none does.
5. **One free change is worth making for the swarm's other directions** (section 6): at $R \ge 2$ the domain can be any union of $2^R$ cosets of $S_\kappa$, at the same NTT cost and with the Annex B proof unchanged. Choosing coset representatives with no additive relation removes the flats of lead note 1 (lists of $2^{26}$ at agreement $n/2-1$ become lists of 3), so Johnson is no longer provably tight at rate 1/4, 1/8, 1/16 and at every later level. It proves nothing new by itself.

## 1. What is proven, with constants

### 1.1 Subspace-design codes: lists and MCA up to capacity

**Definition** [lit: GX13; ABF26 Def. 2.16; GG25 Def. 2.15]. An $F$-additive code $C \subseteq (F^m)^n$ is a $\tau$-subspace-design code if for every $r$ and every $F$-subspace $A \subseteq C$ with $\dim A \le r$: $\sum_i \dim A_i \le n\,\tau(r)\dim A$, where $A_i = \{a \in A : a_i = 0\}$.

**Folded RS** [lit: GK16; proof read in LXYYZ26 Lemma 4.17]. $\mathrm{FRS}_m$: a polynomial $f$ of degree $< k$, the symbol at $x$ is $(f(x), f(\gamma x), \dots, f(\gamma^{m-1}x))$, $n$ symbols, rate $\rho = k/(mn)$. If the $mn$ points are distinct and $\mathrm{ord}(\gamma) \ge k$, it is a $\tau$-subspace design with $\tau(r) = m\rho/(m-r+1)$ for $r \le m$. The proof is a folded Wronskian $\det(f_a(\gamma^b X))$, it uses nothing about the field, so it holds in characteristic 2.

**Lists** [lit: CZ25 Thm B.5, statement checked in the primary source; also ABF26 Thm 3.4, AGG26 Thm 2.4]. A $\tau$-subspace-design code is $(\delta, L)$ average-radius list decodable for $\delta < \frac{L}{L+1}(1 - \tau(L))$. For FRS: radius $\frac{L}{L+1}\bigl(1 - \frac{m\rho}{m-L+1}\bigr)$ with list $L \le m$.

**MCA** [lit: GG25 Thm 4.7, Cor. 3.9, Cor. 4.10, proofs read; LXYYZ26 Thm 4.14, statement and its derivation from their Thm 4.5 read, the proof of Thm 4.5 not checked]. In the sharpest published form, for lines ($\ell = 1$): pick integers $L, s \le m$ and a radius
$$\delta < \min\Bigl\{\tfrac{L}{L+1}\bigl(1-\tau(L)\bigr),\ 1 - \tau(s) - \tfrac{2-\tau(s)}{s+1}\Bigr\}.$$
Then the code has mutual correlated agreement at radius $\delta$, with zero agreement loss, with error $(\lfloor\delta n + 1\rfloor L + A)/|F|$, where $A = \lceil (t_1-1)(\delta(s-1)+\varepsilon_2)/\varepsilon_2\rceil + 1$, $t_1 = 1 + \lceil\delta/\varepsilon_1\rceil$ and $\varepsilon_1, \varepsilon_2$ are the two slacks in the minimum. GG25's own form is: FRS with $m > 4t^2$ has line MCA at $1-\rho-2/t$ with error $(nt + O(t^3))/|F|$. Here $n$ is the number of symbols (Merkle leaves), and $F$ is the field the challenge is drawn from. (The ECCC revision of GG25 states Cor. 4.9 with $\tau(t\ell+\ell)$ where its Thm 4.8 and the proof have $\tau(t\ell+t)$; ABF26 Thm 4.13 copies the former. I use the form whose proof I read.)

Numerically for us: $n \le 2^{25}/m$, $L \le 50$, $|F| = 2^{128}$, so the error is $2^{-110}$ to $2^{-102}$ and a fold round needs a 15 to 23 bit grind instead of 7 (section 3). The field is large enough; this is not the obstacle.

**Univariate multiplicity codes** [lit: GK16; LXYYZ26 Thm 4.11] have the same $\tau$ but need $\mathrm{char}(F) > k$. See 2.3 for characteristic 2.

**Concurrent** [lit, abstract and informal Thm 1.1 of v1 only]: Jeronimo, Liu, Rajpal, arXiv 2601.10047, FRS proximity gap at $1-\rho-\eta$ with error $O(n/\eta + \eta^{-3})/q$. The arXiv record now reads "withdrawn"; v1 is still served.

### 1.2 How large the folding parameter must be

[checked: `06_frs_numbers.py`, exact evaluation of the LXYYZ26 formula above with a 0.002 margin; level 0, $\kappa = 24$.] Symbol agreement threshold $A/n$ and queries $t$, per rate and $m$:

| $m$ | rate 1/2 | rate 1/4 | rate 1/8 | rate 1/16 |
| --- | --- | --- | --- | --- |
| Johnson, today | 0.707, 218 | 0.500, 109 | 0.354, 73 | 0.250, 55 |
| 8 | none | 0.722, 230 | 0.544, 123 | 0.431, 89 |
| 16 | 0.891, 648 | 0.599, 147 | 0.422, 87 | 0.314, 65 |
| 32 | 0.791, 319 | 0.500, 109 | 0.331, 68 | 0.230, 51 |
| 64 | 0.712, 221 | 0.427, 88 | 0.267, 57 | 0.175, 43 |
| 128 | 0.653, 176 | 0.375, 77 | 0.223, 50 | 0.138, 38 |
| 256 | 0.609, 152 | 0.338, 69 | 0.193, 46 | 0.114, 35 |
| 1024 | 0.556, 128 | 0.294, 62 | 0.159, 41 | 0.088, 31 |
| capacity | 0.500, 108 | 0.250, 54 | 0.125, 36 | 0.0625, 27 |

So FRS only reaches the Johnson radius at $m = 64$ (rate 1/2) or $m = 32$ (lower rates). With the list-decoding radius of CZ25 alone (no MCA is proven there) $m = 64$ would give 151, 73, 49, 38. This agrees with the literature's own instantiations: ABF26 Table 5 (rate 1/2, 128 bits, a 186-bit field) needs $t = 295$ at $m = 2^6$, 182 at $2^8$, 151 at $2^{10}$, against 259 for interleaved RS, and its argument sizes are always larger than RS; LXYYZ26 Table 3 runs FRS at $m = 32$, rate 1/2, with radius $0.21$ (below Johnson) and $t = 292$, and its proofs are 1.9 to 2.8 times FRI's at that rate (100-bit security). Both papers state that the gain of FRS today is a smaller field, not fewer queries, and both list "reduce $m$ from $O(1/\eta^2)$ to $O(1/\eta)$" as open (ABF26 section 7; LXYYZ26 Table 5 is explicitly conjectural).

### 1.3 Plain RS with special evaluation points

**Explicit RS subspace designs** [lit: Alrabiah, Goyal, Guruswami, ECCC TR26-262, statements of Thm 1.1, 4.2, 7.1, 7.2, 8.1 read, proof of Thm 4.4 read]. Plain RS over an extension $F/K_0$ is a $\tau$-subspace design over $K_0$ with $\tau(d) = (k-1)/n + (b/n)\log_2 d$ for $d \le r$ (Thm 4.2), where $b$ bounds, for each $\sigma_j$ of a generating set of $\mathrm{Gal}(F/K_0)$, the number of evaluation points that $\sigma_j$ moves (Def. 4.1(i)), and the points must avoid low-degree $K_0$-polynomials (Def. 4.1(ii)). The construction takes points in $g$ extensions of pairwise coprime degrees, so that each generator fixes all but a $1/g$ fraction. It then gets lists $O(1/\varepsilon)$ and line MCA over $F$ with error $O(n/\varepsilon + \varepsilon^{-3})/|F|$ at $1-\rho-\varepsilon$ (Cor. 8.3). This is the only known code with a one-element symbol and capacity guarantees in characteristic 2.

**It cannot be instantiated in $E$** [proved]. $\mathrm{Gal}(E/K_0)$ is cyclic of order a power of 2 for every subfield $K_0$, so any generating set contains a generator of the whole group, which fixes exactly $K_0$. Hence $b \ge \#\{i : \alpha_i \notin K_0\}$. And two points $\alpha_1 \ne \alpha_2$ in $K_0$ violate (ii): take $Q = \mathrm{span}_{K_0}(1, X)$, every $\alpha_i \in K_0$ is a root of $X - \alpha_i \in Q$, so $\sum_i \max_{q\in Q}\mathrm{mult}_{\alpha_i} q \ge 2 > 1 = \max\deg$. So $b \ge n-1$ and the bound of Thm 4.2 is $\tau(d) = 1$ for $d \ge 2$: the theorem is vacuous for every choice of points in a field of 2-power degree over $\mathbb{F}_2$. (This shows that the known sufficient condition gives nothing, not that no good point set exists.) Quantitatively the construction needs $g \ge 4\log_2(r)/\varepsilon$ coprime degrees for lists and (Thm 7.2, as I read the extracted text) $g \ge 2^r$ degrees that are products of two primes above $2^{r+1}g$ for the subspace design, with $r \ge 4/\varepsilon$. At $\varepsilon = 0.2$ the list-decoding condition alone asks for about 86 pairwise coprime degrees, an extension degree above $2^{500}$.

**Random evaluation points** [lit: AGL24 Thm 1.1, read only as quoted in ABF26 Thm 3.6 and Zhu26]. RS on $n$ uniform points of $F$ is list decodable to $\frac{L}{L+1}(1-\rho-\eta)$ with list $L$ when $|F| \ge n + k\,2^{10L/\eta}$. [checked] With $k = 2^{24}$ this gives at best radius 0.125 for points in $K$ and 0.205 for points in $E$ at rate 1/2 (Johnson: 0.293), and 0.50 at rate 1/16 (Johnson: 0.75). MCA for random RS [lit: GG25 Thm 5.20, statement only; GGSW26, abstract only] needs $q > C_2(\rho,\varepsilon)\,n$ and $n > C_1\varepsilon^{-9}$ with unspecified constants, holds with probability 2/3 over the points, and random points have no fast transform. Vacuous for us.

**Large characteristic** [lit, abstracts and comparison tables only]: every RS code over a prime field, on any domain, has $n^{O_\gamma(1)}$ lists and MCA error $n^{O_\gamma(1)}/q$ up to capacity (Brakensiek, Chen, Putterman, Zhang, Zheng; Jeronimo arXiv 2609.05870; Dao, Kominers, Thaler 2026), and lists linear in $n$ just beyond Johnson (Gabizon 2026). All need characteristic $p > \max(k-1, B)$: the method differentiates. In characteristic 2 the same statements are false on subspace domains [lit: DKTZ26; Zhu arXiv 2610.15815, superpolynomial lists at a fixed gap above every rate, robust under deleting a constant fraction of the full field; BKR10].

### 1.4 IOPPs built on these codes

- [lit, read] Li, Xing, Yao, Yuan, Zhu, "How to Fold Linear Error-Correcting Codes with Optimal Proximity Gaps", ePrint 2026/2133: a FRI-style IOPP for FRS and multiplicity codes. The fold is the usual even/odd fold, and the verifier opens the two FRS symbols at $\pm a$ to get the folded symbol at $a^2$, "row by row". It needs a prime field with a 2-smooth subgroup and $\gamma$ of odd order $> k$. This is exactly design (a) below with two lanes.
- [lit, read] ABF26 section 6.3.2: the toy reduction instantiated with FRS, Tables 4 and 5 quoted above.
- [lit, abstract only] Chai, Fan, ePrint 2026/858 ("FRI soundness above the Johnson bound", also for characteristic 2) proves $(1-\delta/2)^t$ per query, which at $\delta \to 1-\rho$ is the unique-decoding rate $(1+\rho)/2$, worse than Johnson. Not relevant.
- I found nothing on FRS or subspace-design codes with an additive FFT, and no WHIR or STIR variant at capacity other than the above.

## 2. The compatibility problem

### 2.1 The leaf is forced to be lanes times points

Let a level encode $f \in E^{h} \otimes E^{k'}$ ($h = 2^\ell$ lanes) with symbols in $E^s$, symbol $j$ being $s$ functionals $\varphi_{j,1..s}$. The verifier's query turns symbol $j$ into values $\langle w_{j,i}, f'\rangle$, $i \le m$, of the folded message $f' = \sum_u v_u(r) f_u$, where the fold coefficients $v(r) \in E^h$ depend on the challenges (and possibly on $j$, as for the affine combiner).

**Lemma 2.1** [proved]. (i) $s \ge h$ always, even if the target functionals depend on the challenge. (ii) If the target functionals $w_{j,1..m}$ do not depend on the challenge and are independent, then $\mathrm{span}_i\,\varphi_{j,i} \supseteq E^h \otimes \mathrm{span}_i\,w_{j,i}$, so $s \ge h\,m$ and the part of the code the verifier uses is the $h$-fold interleaving of the base code $g \mapsto (\langle w_{j,i}, g\rangle)_{j,i}$ with alphabet $E^m$.

Proof. The verifier computes $\langle v(r) \otimes w, f\rangle$ linearly from the symbol, so $v(r)\otimes w \in \Phi_j := \mathrm{span}_i\,\varphi_{j,i}$. The $v(r)$ span $E^h$ (for the multilinear and the affine fold already $r \in \{0,1\}^\ell$ gives a basis). (i): rank-one tensors $v_a \otimes w(v_a)$ with $v_a$ a basis are independent. (ii): $\Phi_j$ contains $v \otimes w_{j,i}$ for a spanning set of $v$, hence $E^h \otimes w_{j,i}$. $\square$

Consequences. Today's 64-element leaf is the minimum for six fold rounds per level. Bundling along a fiber of the folding map is the case $m = 1$ (isometric to interleaved RS, no gain). FRS bundles $x, \gamma x, \dots$ with $\gamma$ of large order are not fibers, and the only way to make them fold is to carry all $h$ lanes at each of the $m$ points: a leaf of $h\,m$ elements. Caveat: if the target functional may depend linearly on the challenge ($w = Bv$) the span of $\{v \otimes Bv\}$ is a symmetric-tensor space and $s$ can drop to $hm - m(m-1)/2$; nothing is proven about such codes and for $h = 64$ the saving is negligible.

### 2.2 (a) Interleaved FRS: works, and is covered by the theorems

Leaf at $x$: $(P_u(\gamma^j x))_{u < 2^\ell,\ j < m}$. The verifier folds the lanes at each of the $m$ points and gets the FRS symbol of the folded polynomial, i.e. $m$ consistency claims $P'(\gamma^j x) = c_{q,j}$ for the next level's batching. This is what LXYYZ26 does with two lanes.

**Lemma 2.2** [proved, from GK16 and AGG26 Thm 4.4]. The $h$-lane interleaving of $\mathrm{FRS}_m$ over $E$, as an $E$-additive code with alphabet $E^{hm}$, is a $\tau$-subspace design over $E$ with the same $\tau(r) = m\rho/(m-r+1)$, for every $h$.

Proof. Pack the lanes with a basis $b_1..b_h$ of a degree-$h$ extension $E'/E$: $(f_u)_u \mapsto \sum_u b_u f_u$ is an $E$-linear injection into $\mathrm{FRS}_m$ over $E'$ (same points, same $\gamma$), and a symbol of the image vanishes iff it vanishes in every lane. $\mathrm{FRS}_m$ over $E'$ is a $\tau$-subspace design over $E'$ (the Wronskian argument works over any field containing the points). AGG26 Thm 4.4 with $E_0 = E$, $E_1 = E'$ transfers the bound to $E$-subspaces: its hypothesis holds because $\mathrm{span}_{E'}(W \cap H_i) \subseteq (\mathrm{span}_{E'} W) \cap H_i$ for the $E'$-linear kernels $H_i$. $\square$

So the list bound of CZ25 and the line MCA of 1.1 hold for the interleaved code with no loss in the number of lanes (ABF26 uses the generic Lemma 2.10 and 4.7 instead, which lose a factor in the list and a factor $h$ in the error).

### 2.3 (b) Characteristic 2 and the additive NTT

- **FRS exists in $K$** [proved/checked]. $\gamma = x$ has order $2^{64}-1$ in $K$ [checked, `06_coset_domain_check.py`], so $\mathrm{ord}(\gamma) \ge k$. Bundles are disjoint if the starts $T$ lie on a line $c \cdot \mathrm{GF}(2^{32})$, $0 \notin T$: then $t'/t \in \mathrm{GF}(2^{32})$ while $\gamma^j \notin \mathrm{GF}(2^{32})$ for $0 < j < 2^{32}+1$ [proved]. $T$ can be an affine $\mathbb{F}_2$-subspace, so each $\gamma^j T$ is a coset of a subspace and the values stay in $K$ for $K$-valued lanes.
- **The encoder is the problem** [estimate]. The $m$ sets $\gamma^j T$ are cosets of $m$ different subspaces $\gamma^j V$; they lie in no common small subspace (their sum is all of $K$ for $m \ge 3$), and since $|T| = 2^R k/m < k$ each needs the residue of $P(\gamma^j X)$ modulo a degree-$|T|$ polynomial, which depends on all $k$ coefficients. The cheapest pipeline I found keeps the lane in the monomial basis and, for each $j$, scales the coefficients ($k$ multiplications), reduces modulo the subspace polynomial of $T$ (XOR only if $T$ is a Cantor subspace), converts to the novel basis and runs an NTT of size $|T|$. That is about $(m + 2^{R-1}\log_2|T|)\,k$ multiplications per lane against $2^{R-1}\kappa\,k$ today: about 3.5 times at $m = 64$, 11 times at $m = 256$ and 43 times at $m = 1024$ for $R = 1$, plus the XOR passes. One NTT suffices only when the whole point set is $\mathrm{GF}(2^{32})^\ast$ with $\gamma$ primitive in it, i.e. when $nm = 2^{32}-1$.
- **$\gamma$ of small order** (in a subfield, so that $\gamma D = D$ and nothing changes in the encoder) breaks the hypothesis $\mathrm{ord}(\gamma) \ge k$: the Wronskian of $f$ and $X^{\mathrm{ord}} f$ vanishes identically, and the subspace $\{c(X^{\mathrm{ord}})\,f : \deg c < d\}$ shows $\tau(d) \ge (1 - 1/d)(1-\rho)$ [proved], which exceeds $\rho$ for large $d$ at every rate below 1/2. No theorem remains; whether the lists stay small is open.
- **Multiplicity codes do not exist in characteristic 2** [proved]. With Hasse derivatives the order-$2^a$ symbol at $x$ is $f \bmod (X-x)^{2^a} = f \bmod (X^{2^a} - x^{2^a})$. Writing $f = \sum_{u<2^a} X^u f_u(X^{2^a})$ this residue is $\sum_u X^u f_u(x^{2^a})$, so the symbol is an invertible linear image of $(f_u(x^{2^a}))_u$: the code is isometric to the $2^a$-lane interleaved RS code on the domain $\{x^{2^a}\}$, again a subspace. Johnson, and the flats, apply unchanged.
- **Frobenius orbits** $x, x^2, x^4, \dots$ (free to encode on a Cantor subspace, which is Frobenius-closed) [proved]: the determinant $\det(f_a(X^{2^b}))_{a,b<d}$ is nonzero for independent $f_a$ and has degree at most $(k-1)(2^d-1)$, which gives only $\tau(d) \le \rho\,\frac{m(2^d-1)}{d(m-d+1)}$. The resulting list radius is below Johnson at each of our four rates ($0.64$ against $0.75$ at rate 1/16 with $m = 64$). The messages-over-$\mathbb{F}_2$ variant (one $E$-symbol per orbit) has the same $2^d$ loss.

### 2.4 (c) Queries that need no fold

Not sound, and not a saving when repaired [proved for the two orderings below; the cost remark is an estimate]. If the queries to a non-interleaved oracle come before the prover is bound to the folded message, a far word has no message: the prover interpolates an $f$ through the $t\,m < k$ opened values and proves the resulting true claims. If they come after the commitment to $f'$, Lemma 2.1 applies: a symbol that determines nothing about $f'$ cannot test it. The remaining option is code switching (commit $f$ under the capacity code, re-commit $f$ itself under a foldable code, query the first, prove the opened symbols against the second): sound with only list decodability of the first code, but the second oracle has the full size and needs its own Johnson-rate queries, so level 0's cost is paid twice.

### 2.5 (d) Capacity code at level 0 only

This is what design 3 does: only the level-0 code changes, the folded word is an $\mathrm{FRS}_m$ word over $E$, and its $m\,t_0$ consistency claims enter level 1, which stays plain interleaved RS. Later levels gain even less from FRS (few queries, low rates need $m \ge 32$).

## 3. The best design, and why it loses

**Protocol sketch (level 0).** Message $f : \{0,1\}^{\ell} \times \{0,1\}^{\kappa} \to K$, lane $P_u = \sum_e f(u,e) X^e$ in the monomial basis (column weights $y^e = \prod_b (y^{2^b})^{e_b}$ are still tensors). Domain: $n = 2^{\kappa+R}/m$ bundle starts $T$ as in 2.3, $\gamma = x$. Leaf at $t \in T$: $(P_u(\gamma^j t))_{u,j}$, $64m$ elements of $K$. Fold rounds use the scalar combiner $G + \alpha F$ (degrees do not grow, no high part, the prover sends two values per round). After the level-1 commitment and the OOD point, each query opens one leaf, folds it to $(w(\gamma^j t_q))_{j<m}$ and adds the $m$ claims $\langle W_{\gamma^j t_q}, f^{(1)}\rangle = c_{q,j}$ to the batch, so $J_1 = m\,t_0 + 2$.

**Soundness statement needed** [conj: the assembly below is not written out; every ingredient is lit or proved above]. The proof of Theorem `thm:rbr` with three substitutions: (1) "two codewords agree on at most $(k-1)/m$ symbols"; (2) the Johnson count replaced by $L$ from CZ25 Thm B.5 applied to the interleaved code via Lemma 2.2; (3) Lemma `lem:fold-list` with the line MCA of LXYYZ26 Thm 4.14 (zero loss, so one threshold $A$ for all rounds) and the claim residual of degree 2 in $\alpha$. Errors: fold round $(\lfloor\delta n+1\rfloor L + A)/|E| + 2L/|E|$, OOD $\binom{L}{2}\mu/|E|$, query $((A-1)/n)^{t}$, batching $(J-1)L/|E|$. Hypotheses to check: $\mathrm{ord}(\gamma) \ge k$, distinct points, $|E| > (L+1)^2$, the radius condition of 1.1. No new theorem is needed. A new theorem (an affine-combiner MCA with loss one for subspace-design codes) would only remove the 15 to 23 bit fold grinds.

**Queries and cost at level 0, $\mu = 30$** [checked: `06_frs_numbers.py`; bytes $= t(512m + 32\,\text{path})$, Keccaks $= t(\lceil 512m/136\rceil + \text{path})$, path $= \log_2 n - \lfloor\log_2 t\rfloor$]:

| rate | today $t$ | $m$ | FRS $t$ | fold grind | level-0 bytes | level-0 Keccaks |
| --- | --- | --- | --- | --- | --- | --- |
| 1/2 | 218 | 64 | 221 | 16 bits | x31 | x12 |
| 1/2 | 218 | 256 | 152 | 15 bits | x85 | x31 |
| 1/2 | 218 | 1024 | 128 | 15 bits | x284 | x104 |
| 1/4 | 109 | 64 | 88 | 19 bits | x23 | x8.7 |
| 1/4 | 109 | 256 | 69 | 18 bits | x73 | x26 |
| 1/8 | 73 | 64 | 57 | 21 bits | x22 | x8.1 |
| 1/8 | 73 | 256 | 46 | 20 bits | x71 | x25 |
| 1/16 | 55 | 64 | 43 | 22 bits | x21 | x7.6 |
| 1/16 | 55 | 256 | 35 | 22 bits | x68 | x24 |

Further costs: the encoder (2.3), $m$ times more consistency claims (each costs the verifier about $2\kappa$ multiplications in $E$ at the end), and a monomial-basis message. Reducing the lanes to keep the leaf at 64 elements does not help: $m \le 32$ gives no gain at rate 1/2, and fewer lanes mean a level-1 oracle $2^{6-\ell}$ times larger over $E$.

**Dominated by lowering the rate.** FRS at rate 1/2 with $m = 256$ (152 queries, 85 times the bytes, about 11 times the encoding) against plain RS at rate 1/4 (109 queries, 0.53 times the bytes, 2 times the encoding and hashing), both proven.

## 4. A barrier for every subspace-design code

**Proposition 4.1** [proved]. For any $\tau$-subspace-design code with alphabet $E^m$ and any $r \le \dim C$: $\tau(r) \ge 1 - m/r$ (and $\tau(r) \ge \rho - 1/n$ [lit: GG25 Lemma 2.16]).

Proof. $A_i$ is the kernel of a linear map $A \to E^m$, so $\dim A_i \ge \dim A - m$; average over $i$. $\square$

So under the theorem of 1.1, whose second condition is $\delta < 1 - \tau(s) - (2-\tau(s))/(s+1)$, the best any code over $E^m$ can reach is about $\delta = (1-\rho)\bigl(1 - \frac{2-\rho}{m+1-\rho}\bigr)$ (at $s = m/(1-\rho)$). Beating Johnson then needs about $m \ge 4, 5, 7, 9$ at rates 1/2 to 1/16. Evaluating the exact formula with $\tau = \max(\rho, 1-m/r)$ [checked]:

| rate | $m = 4$ | $m = 8$ | $m = 16$ | $m = 64$ |
| --- | --- | --- | --- | --- |
| 1/2 | $t = 187$, bytes x2.0, Keccaks x1.25 | 142, x2.8, x1.37 | 125, x4.6, x2.0 | 113, x16, x6.0 |
| 1/4 | 123, x2.6, x1.6 | 85, x3.2, x1.6 | 68, x4.8, x2.0 | 58, x16, x5.7 |
| 1/8 | 109, x3.4, x2.1 | 65, x3.6, x1.8 | 51, x5.3, x2.2 | 40, x16, x5.7 |
| 1/16 | 95, x3.8, x2.4 | 59, x4.2, x2.1 | 43, x5.6, x2.4 | 32, x16, x5.7 |

Every entry is above 1 in both metrics. The reason is structural: the level-0 leaf already carries 64 lanes (512 bytes, about as much as its Merkle path), any alphabet blow-up is paid 64 times over, and the query count can drop by at most 2. So the "improved parameters for subspace-design codes" open problem of ABF26, even fully solved, does not help leanVM unless the MCA theorem itself improves (with the list-decoding condition alone an optimal code with $m = 2$ would reach agreement 0.6 at rate 1/2, 147 queries: the same bytes as today and about 20% fewer level-0 Keccaks, and that is the best case).

## 5. Verdict in the terms of the brief

- **Feasible and provable today:** yes, interleaved FRS at level 0 with a scalar fold (section 3), in characteristic 2. It is strictly worse than the current protocol in proof size, verifier work, recursion cost and prover time, and strictly worse than lowering the rate.
- **Feasible but needs a new theorem:** a code with a one-element symbol. Candidates and the missing theorem are in section 7.
- **Not feasible in characteristic 2:** multiplicity codes (isometric to interleaved RS), the explicit RS subspace designs of AGG26 (need coprime extension degrees), the prime-field capacity theorems (need characteristic above $k$), and plain RS on subspace domains (Johnson is tight at rate 1/4, lead note 1).

## 6. Cheaper variants

**6.1 Lower the level-0 rate** [proved, it is the current theorem]. $R \to 2R$ gives the capacity query count of rate $2^{-R}$. Cost: the level-0 NTT and Merkle tree grow by $2^R$.

**6.2 A coset-union domain without additive structure** (free, proof unchanged, kills the flats).

*Fact A* [proved]. For any $c_0 = 0, c_1, \dots, c_{2^R-1} \in K$, distinct modulo $S_\kappa$, the code on $D_c = \bigcup_i (c_i + S_\kappa)$ is encoded by the same $2^R$ size-$2^\kappa$ NTTs as today (the twiddles of coset $i$ shift by $\widehat W_d(c_i)$, computed by the chain of Lemma `lem:chain`), the column weights of Lemma `lem:colweight` are unchanged (they are stated for any $x$), and Theorem `thm:rbr` holds verbatim: the Johnson bound is domain-free and [CWYZ26, Thm 4.10] is stated for any $D \subseteq K$ of size $n$. For $R = 1$ every such domain is a subspace, so this is a choice only for $R \ge 2$: level 0 at rates 1/4 and below, and every later level at every rate. I did not find any other use of the subspace structure of the PCS domain in Annex B (the duality of Annex D is LeanDA's). The Lean development fixes `domain κ R` and would need it generalized.

*Fact B* [proved]. Call the labels Sidon if no four distinct $c_i$ sum to an element of $S_\kappa$ (for example $c_i = x^{\kappa+i-1}$, $1 \le i < 2^R$, which needs $\kappa + 2^R \le 65$). Then every affine $\mathbb{F}_2$-subspace inside $D_c$ has dimension at most $\kappa+1$, and those of dimension $\kappa+1$ are exactly the $\binom{2^R}{2}$ unions of two cosets. Proof: the image of an affine subspace $a + V \subseteq D_c$ in $K/S_\kappa$ is an affine subspace inside the label set, hence of dimension at most 1, so $\dim(V \cap S_\kappa) \ge \dim V - 1$. $\square$

*Consequence* [proved]. The flats family of lead note 1 (one codeword $Q_V$ of degree $< k$ per linear subspace $V \subseteq D$ of size $2k$, all agreeing with $x^{2k-1}$ on $2\rho n - 1$ points) has $2^R - 1$ members on $D_c$ instead of $\binom{\kappa+R}{R-1}_2 \approx 2^{(R-1)(\kappa+1)}$: 3 instead of $2^{26}$ at rate 1/4. In the analysis degree $d \ge 2^\kappa$ the word $x^{2k}$ has one polynomial of degree $k$ per affine flat: $\binom{2^R}{2}$ (6, 28, 120) instead of about $2^{(R-1)(\kappa+2)}$.

*Check* [checked: `06_coset_domain_check.py`, $\mathrm{GF}(32)$, $k = 4$, $n = 16$, exhaustive over all $2^{20}$ polynomials of degree $< 4$]. Word $x^7$ at agreement $\ge 7 = n/2 - 1$: 15 codewords on the subspace domain, 3 on the Sidon domain. Over all monomial words $x^4..x^{30}$ the largest list at agreement $\ge 7$ is 15 against 3; at agreement $\ge 6$ both reach 16, the random-agreement level at this size. Word $x^8$ against all polynomials of degree exactly 4 at agreement 8: 30 against 6.

*What it does not do.* [proved, given the constructions cited] Two kinds of lists survive on $D_c$. (1) The coset-union lists of the main document (section 4.2) only need $D$ to be a union of cosets of a subspace $W \subseteq S_\kappa$: $\binom{2^{R+a}}{2^a+1}$ polynomials of degree $\le k$ at agreement $(1+2^{-a})\rho n$. (2) Each union $U$ of two cosets is an affine subspace of size $2k$ on which the code is a rate-1/2 code, so every rate-1/2 family of notes 01 and 05 that exists on all additive domains lives on $U$: lists of about $2^{30}$ at agreement $\tfrac58|U| = \tfrac54\rho n$. With a list budget of $2^{10}$ the known floors on $D_c$ are therefore about 65, 41, 32 queries at rates 1/4, 1/8, 1/16 (the main document's table), no longer the 108, 54, 36 that flats force on subspace domains. Families that need an affine subspace of dimension above $\kappa+1$ (the flats at $2\rho n$, and as far as I can tell the rate-1/4 family at $3n/8$ of note 05, Cor. 2.3, which complements inside a subspace domain) do not exist on $D_c$ as constructed; I did not re-examine each family of notes 01 and 05 [not checked]. No bound on lists beyond Johnson is known on $D_c$ [conj that they are smaller than on subspaces]; the change removes a proven obstruction and costs nothing, it does not lower a query count by itself.

**6.3 A punctured domain** [conj]. Evaluate on $2^{R+1}$ cosets and keep a structureless half of the points (a quadric, say). All known list constructions lose half their agreement and fall to or below capacity at rate 1/2. Cost: twice the NTT, same hashing. But the same NTT budget buys the honest rate $2^{-(R+1)}$ code with a proof (109 queries at $R = 1$), so this only saves half the Merkle hashing in exchange for a conjecture. Zhu26 Cor. 6.1 shows that deleting a small constant fraction of a full field does not help; a density-$2^{-39}$ subset of $K$ is far outside both that negative regime and the positive random regime.

**6.4 Expander-bundled leaves** (one Merkle path for $d$ points, each point in $c$ leaves). The hope is that a leaf query counts as $d$ point queries. [proved] From a $\mu$ fraction of good points a prover can always make a $\mu/c$ fraction of the leaves fully good (take the union of that many leaves), so $c$ cannot be small; [estimate] expander mixing only approaches $\mu^d$ when $c$ is in the tens. It multiplies the hashed data by $c$, and lowering the rate by a factor $c$ is better.

## 7. What new theorem would change the verdict

1. **Beyond-Johnson lists and MCA for plain RS on a structureless coset union $D_c$ over $\mathrm{GF}(2^{128})$** (section 6.2). Any gain is free (same leaf, same encoder). No technique is in sight: the hidden-derivative method needs characteristic above $k$, Guruswami-Sudan stops at Johnson, the Galois-determinant method needs many coprime extension degrees, and the coset-union lists cap the possible gain at the main document's floors.
2. **An MCA theorem for subspace-design codes at the list-decoding radius $\frac{L}{L+1}(1-\tau(L))$** with error $\mathrm{poly}(L)\,n/|E|$, together with a subspace design near $\tau(r) = \max(\rho, 1-m/r)$ for $m \le 2$. By section 4 this is the least that could break even.
3. Not needed: an affine-combiner MCA for FRS (saves grinding only), or smaller $m$ for FRS under the current MCA theorem (section 4 shows it cannot pay).

## References

- [ABF26] Arnon, Boneh, Fenzi. Open Problems in List Decoding and Correlated Agreement. ePrint 2026/680 (read: the 2026-04-30 version).
- [AGG26] Alrabiah, Goyal, Guruswami. Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding. ECCC TR26-262.
- [AGL24] Alrabiah, Guruswami, Li. Randomly punctured Reed-Solomon codes achieve list-decoding capacity over linear-sized fields. STOC 2024 (via ABF26 Thm 3.6).
- [BCP+26] Brakensiek, Chen, Putterman, Zhang, Zheng. List decoding every prime-field RS code up to capacity (via AGG26, DKT26, Jer26).
- [CZ25] Chen, Zhang. Explicit Folded Reed-Solomon and Multiplicity Codes Achieve Relaxed Generalized Singleton Bounds. arXiv 2408.15925.
- [DKT26] Dao, Kominers, Thaler. Reed-Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs. September 2026.
- [GG25] Goyal, Guruswami. Optimal Proximity Gaps for Subspace-Design Codes and (Random) Reed-Solomon Codes. ECCC TR25-166 rev. 1, ePrint 2025/2054.
- [GGSW26] Goyal, Guruswami, Sun, Wootters. Locality of Curve-Decoding and Improved Proximity Gaps. arXiv 2607.08516.
- [GK16] Guruswami, Kopparty. Explicit subspace designs. Combinatorica 2016 (via LXYYZ26 and ABF26).
- [Jer26] Jeronimo. Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed-Solomon Codes. arXiv 2609.05870.
- [JLR26] Jeronimo, Liu, Rajpal. Optimal Proximity Gap for Folded Reed-Solomon Codes via Subspace Designs. arXiv 2601.10047v1 (record now withdrawn).
- [LXYYZ26] Li, Xing, Yao, Yuan, Zhu. How to Fold Linear Error-Correcting Codes with Optimal Proximity Gaps. ePrint 2026/2133.
- [Zhu26] Zhu. Superpolynomial Lists for Reed-Solomon Codes over Binary Extension Fields. arXiv 2610.15815.
- [CWYZ26], [DKTZ26], [BKR10]: as in `doc/whir_soundness_gap.md`.
