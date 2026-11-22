# 29. The attack constructions, machine-checked in Lean 4

Researcher 29. This note says exactly which of the explicit constructions of notes 00, 01, 02 and 05 (the attack side: the Johnson radius cannot be beaten for today's protocol) are now checked by Lean 4 with Mathlib, how each Lean statement relates to the hand statement, what the formalization showed about the hand proofs, and what is not done. The sources are the library `Constructions` of the project in `lean/` (ten files under `lean/Constructions/`, about 2350 lines without the axiom checks; `lean/Constructions/README.md` for the build). Tags: **[machine-checked]** means the statement is a Lean theorem that compiles with no `sorry` and depends on Lean's three axioms only; **[not formalized]** means no Lean statement exists.

## 0. Summary

1. **Subspace polynomials** (brief item 1) are machine-checked: $L_V$ is additive, vanishes exactly on $V$, satisfies $L_{V + \{0, a\}} = L_V^2 + L_V(a) L_V$, is linearized, and $\deg(L_V - X^{|V|}) \le |V|/2$.
2. **The flats lemma** (item 2) is machine-checked, with the rate-1/4 statement: on every subspace domain of $n$ points in every field of characteristic two, the word $x \mapsto x^{n/2 - 1}$ has at least $n - 1$ polynomials of degree below $n/4$ at agreement $n/2 - 1$ (`flats_quarter`).
3. **The pole collapse and Lemma A** (item 3) are machine-checked over every field, for the affine combiner and for every polynomial combiner, with the count: a list of $L$ polynomials of degree at most $d + 1$ at agreement $T$ gives a pole pair with at least $L \cdot |K|$ bad challenges, when $(d+1)\binom L2 + n < |K|$ (`list_gives_bad_challenges`).
4. **Rate 1/2 at agreement $5n/8$** (item 4) is machine-checked in three forms: the word $L_P X^{n/4}$ of Corollary 2.2 of note 05 with at least $n - 2$ list members, in degree at most $n/2$ and, punctured, in degree below $n/2$ (`five_eighths_slack`, `five_eighths_genuine`); Theorem 5 of note 02 for the word $L_U^g$ in general parameters, one list member per admissible label set (`glued_list`), with at least $n/8 - 1$ members of $L_U^5$ (`glued_list_card`); and Theorem 2.1 (1) of note 05, every union of flats of the family shares the top of $X^{n/2} L_W$ (`flatUnion_five_eighths`), with the gap lemma (Lemma 1.1). **The exact count $56n - 392$ is not machine-checked.**
5. **Instantiation** (item 5): the end statements hold in `GaloisField 2 128` on a subspace of $2^{26}$ points (rate 1/4) and of $2^{25}$ points (rate 1/2), so no hypothesis is vacuous at the deployed sizes.
6. **No error was found in the hand proofs.** Section 4 lists one loosely worded claim (the degree of $Q_V$ is at most, not exactly, $2^{s-1} - 1$), the convention Lemma 1.1 needs, and the hypotheses that turned out to be unused.

## 1. How it was checked

Host `h4`, scratch directory `/data/whir_lean_scratch_29` (created for this, safe to delete). Lean `leanprover/lean4:v4.36.0`, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`; Mathlib tag `v4.36.0`, revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. Nothing was installed or built on the Mac.

- Run 1: each of the eleven modules compiled in dependency order with `lean -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false -o`, from an empty output directory, against the Mathlib already built in `/data/lean436/formal/Statement/.lake/packages` (read only). No output: no error, no warning.
- Run 2: a Lake project with the files of `lean/` (the repository's `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` unchanged) and the packages directory of note 22's scratch project copied in, build directory deleted, then `lake build Constructions`: `Build completed successfully (18272 jobs)`. The only message is Lake's advisory that `Subspace.lean` imports `Mathlib` without the module system. Only the library `Constructions` was built; `DeepFold`, `Interleave` and `Protocol` are other researchers' and are not imported.
- No `sorry`, `admit`, `axiom`, `native_decide` or `set_option` occurs in the sources. `Constructions/Axioms.lean` runs `#print axioms` under `#guard_msgs` on 79 statements, all those named in this note: each depends on `propext`, `Classical.choice`, `Quot.sound` and nothing else.
- Negative control (in the scratch project only): a theorem proved by `sorry` with the same axiom guard fails the Lake build, by the warning and by the guard.
- The files in the repository and the files built on `h4` have the same SHA-256 hashes (compared after the last build).

## 2. Definitions

`K` is a field; characteristic two is assumed only where said. A subspace is `V : AddSubgroup K` with `[Finite V]` (in characteristic two a finite additive subgroup is an $\mathbb{F}_2$-subspace). `pts V` is its set of points as a finset, `locator S` is $L_S = \prod_{s \in S}(X - s)$, `subPoly V` is $L_V$, `flat V a` is $a + V$.

- `agree D w P`: the points $x \in D$ with $P(x) = w(x)$.
- `RSList D w k T`: the set of polynomials $P$ with $\deg P < k$ and $|\mathrm{agree}| \ge T$. Sizes of lists are `Set.encard` in $\mathbb{N}\cup\{\infty\}$, so "at least $m$ members" is `(m : ℕ∞) ≤ (RSList D w k T).encard`.
- `Close D w d T`: some polynomial of degree at most $d$ agrees with $w$ on at least $T$ points of $D$.
- `affFold f₀ f₁ (α, β)` is $f_1 + (\alpha + \beta x) f_0$ (the convention of `DeepFold.agr`), `scalFold f₀ f₁ γ` is $f_1 + \gamma f_0$, `polyFold f₀ f₁ C` is $f_1 + C(x) f_0$; `poleWord β₀` is $1/(x - \beta_0)$ and `poleNum w β₀` is $w(x)/(x - \beta_0)$.
- `IsLinearized p`: every nonzero coefficient of `p` is at an exponent $2^i$.

## 3. What is stated and checked

### 3.1 Subspace polynomials (`Subspace.lean`)

Hand statement (note 00 section 1; note 01, proof of Lemma C; note 05 section 1.2): for an $\mathbb{F}_2$-subspace $V$ of size $2^s$, $L_V$ is linearized, $L_V = X^{2^s} + c_{s-1}X^{2^{s-1}} + \dots + c_0X$; $L_{a+V} = L_V(X) + L_V(a)$.

| Lean statement | content | status |
| --- | --- | --- |
| `subPoly_eval_eq_zero` | $L_V(x) = 0 \iff x \in V$ | **[machine-checked]** |
| `subPoly_comp_add` | $L_V(X + b) = L_V(X) + L_V(b)$ as polynomials, for every $b \in K$; any field | **[machine-checked]** |
| `subPoly_eval_add`, `subPolyHom` | $L_V(a + b) = L_V(a) + L_V(b)$; $L_V$ as an additive map; any field | **[machine-checked]** |
| `locator_coset` | $L_{a + V} = L_V - L_V(a)$; any field | **[machine-checked]** |
| `subPoly_adjoin` | $L_{W + \{0,a\}} = L_W^2 + L_W(a) L_W$ for $a \notin W$, characteristic two | **[machine-checked]** |
| `addSubgroup_induction` | induction on finite subspaces: from $\{0\}$, adjoining one element outside at a time | **[machine-checked]** |
| `exists_card_eq_two_pow` | $|V| = 2^s$ for some $s$ | **[machine-checked]** |
| `subPoly_isLinearized` | $L_V$ is linearized | **[machine-checked]** |
| `IsLinearized.aeval_add`, `subPoly_aeval_add` | $L_V(x + y) = L_V(x) + L_V(y)$ for $x, y$ in any commutative $K$-algebra, so as an identity of polynomials in two variables | **[machine-checked]** |
| `IsLinearized.natDegree_sub_le`, `natDegree_subPoly_sub_le` | $\deg(L_V - X^{|V|}) \le |V|/2$ | **[machine-checked]** |

Mathlib has no additive or linearized polynomials, subspace polynomials or Moore determinants (searched; its `RingTheory/Polynomial/Dickson.lean` is the Chebyshev-like family, which is unrelated). Additivity is proved without induction: $L_V(X + b) - L_V(X) - L_V(b)$ has degree below $|V|$ and vanishes on $V$. The linearized form is proved by the induction on the dimension the brief suggests.

### 3.2 The flats lemma (`Flats.lean`)

Hand statement (note 00 section 1): $Q_V = (L_V - X^{2^s})/X$ has degree $2^{s-1} - 1$ and $Q_V(x) = x^{2^s - 1}$ for $x \in V \setminus \{0\}$; distinct $V$ give distinct $Q_V$; at $R = 2$, $2^N - 1$ genuine codewords at agreement $n/2 - 1$. In Lean `flatPoly V` is $(X^{|V|} - L_V)/X$, the same polynomial in characteristic two.

| Lean statement | content | status |
| --- | --- | --- |
| `flatPoly_mul_X`, `flatPoly_eq` | $Q_V \cdot X = X^{|V|} - L_V$; $Q_V = X^{|V|-1} - \prod_{v \ne 0}(X - v)$; any field | **[machine-checked]** |
| `flatPoly_eval` | $Q_V(x) = x^{|V| - 1}$ for $x \in V$, $x \ne 0$; any field | **[machine-checked]** |
| `agree_flatPoly` | the agreement set with $x \mapsto x^{|V|-1}$ is exactly $V \setminus \{0\}$, for $|V| \ge 2$ | **[machine-checked]** |
| `flatPoly_natDegree_le`, `flatPoly_degree_lt` | $\deg Q_V \le |V|/2 - 1$; $\deg Q_V < 2^{s-1}$ for $|V| = 2^s$, $s \ge 1$ | **[machine-checked]** |
| `flatPoly_injective` | $V \ne V'$ of one size give $Q_V \ne Q_{V'}$ | **[machine-checked]** |
| `flats_list` | for every finite $D \subseteq K$ and $s \ge 1$: the list of $x \mapsto x^{2^s-1}$ at degree below $2^{s-1}$ and agreement $2^s - 1$ has at least as many members as $D$ contains subspaces of size $2^s$ | **[machine-checked]** |
| `card_hyperplanes_ge` | a subspace $D$ has at least $|D| - 1$ subspaces of half its size (kernels of the nonzero $\mathbb{F}_2$-functionals) | **[machine-checked]** |
| `flats_quarter` | $|D| = 2^{s+1}$, $s \ge 1$: at least $|D| - 1$ polynomials of degree below $2^{s-1} = n/4$ agree with $x \mapsto x^{2^s - 1}$ on at least $2^s - 1 = n/2 - 1$ points of $D$ | **[machine-checked]** |

```lean
theorem flats_quarter (D : AddSubgroup K) [Finite D] {s : ℕ} (hs : 1 ≤ s)
    (hD : Nat.card D = 2 ^ (s + 1)) :
    ((Nat.card D - 1 : ℕ) : ℕ∞) ≤
      (RSList (pts D) (fun x => x ^ (2 ^ s - 1)) (2 ^ (s - 1)) (2 ^ s - 1)).encard
```

For other rates `flats_list` reduces the count to the number of subspaces of size $2k$ in $D$; the Gaussian binomial $\binom{N}{R-1}_2$ is **[not formalized]** beyond the hyperplane case.

### 3.3 The pole collapse and Lemma A (`Pole.lean`)

Hand statements: note 00 section 3 ($(\alpha + \beta x) f_0 = \beta + (\alpha + \beta\beta_0) f_0$ for $f_0 = 1/(x - \beta_0)$), `doc/whir_soundness_gap.md` section 5 (every polynomial combiner collapses onto one scalar under a pole pair), note 01 Lemma A. Everything here holds over any field.

| Lean statement | content | status |
| --- | --- | --- |
| `pole_collapse` | $(\alpha + \beta x)/(x - \beta_0) = \beta + (\alpha + \beta\beta_0)/(x - \beta_0)$ for $x \ne \beta_0$ | **[machine-checked]** |
| `combiner_collapse` | $C(x)/(x - \beta_0) = q(x) + C(\beta_0)/(x - \beta_0)$ with $q = C \operatorname{div} (X - \beta_0)$, $\deg q = \deg C - 1$ | **[machine-checked]** |
| `affFold_pole`, `polyFold_pole` | the fold of a pole pair $(1/(x-\beta_0), f_1)$ is the scalar fold at $\alpha + \beta\beta_0$ plus $\beta$, respectively at $C(\beta_0)$ plus $q(x)$; any $f_1$ | **[machine-checked]** |
| `affFold_pole_close_iff` | for $\beta_0 \notin D$ and every $d, T$: the affine fold at $(\alpha, \beta)$ is $(d, T)$-close iff the scalar fold at $\gamma = \alpha + \beta\beta_0$ is | **[machine-checked]** |
| `polyFold_pole_close`, `polyFold_pole_close_iff` | a combiner $C$ of degree $r$: scalar-close at $C(\beta_0)$ implies close at degree $\max(d, r - 1)$; an equivalence at degree $d$ when $r \le d + 1$ | **[machine-checked]** |
| `card_bad_affFold_pole` | over a finite field the number of bad $(\alpha, \beta)$ is $|K|$ times the number of bad $\gamma$ | **[machine-checked]** |
| `card_agree_poleWord_le` | no polynomial of degree at most $d$ agrees with $1/(x - \beta_0)$ on more than $d + 1$ points of $D$ | **[machine-checked]** |
| `scalFold_pole_close_of_list`, `lemmaA`, `lemmaA_witness` | Lemma A: if $\deg C_i \le d + 1$ and $C_i = w$ on at least $T$ points, then for every $(\alpha, \beta)$ with $\alpha + \beta\beta_0 = -C_i(\beta_0)$ the fold of $(1/(x-\beta_0), w/(x-\beta_0))$ is $(d, T)$-close, with witness $\beta + (C_i - C_i(\beta_0))/(X - \beta_0)$ on the agreement set of $C_i$ | **[machine-checked]** |
| `lemmaA_card` | list members with distinct values at $\beta_0$ give $|\mathcal C| \cdot |K|$ bad challenges | **[machine-checked]** |
| `exists_pole_injOn` | if $m\binom{|\mathcal C|}{2} + |D| < |K|$ and the members have degree at most $m$, some $\beta_0 \notin D$ separates them | **[machine-checked]** |
| `list_gives_bad_challenges` | Lemma A as one statement, below | **[machine-checked]** |

```lean
theorem list_gives_bad_challenges [Fintype K] (D : Finset K) (w : K → K) {d T : ℕ}
    (𝒞 : Finset K[X]) (h𝒞 : ∀ Ci ∈ 𝒞, Ci.natDegree ≤ d + 1 ∧ T ≤ (agree D w Ci).card)
    (hK : (d + 1) * 𝒞.card.choose 2 + D.card < Fintype.card K) :
    ∃ β₀ : K, β₀ ∉ D ∧
      𝒞.card * Fintype.card K ≤
        (univ.filter (fun c : K × K =>
          Close D (affFold (poleWord β₀) (poleNum w β₀) c) d T)).card
```

With the flats (`flats_break_mca` in `Concrete.lean`): on a subspace domain of $n = 4k$ points in a finite field of characteristic two with $(k-1)\binom{n-1}{2} + n < |K|$, there is a pole pair whose first word agrees with every polynomial of degree at most $k - 2$ on at most $k - 1$ points, and whose affine fold agrees with a polynomial of degree at most $k - 2$ on at least $n/2 - 1$ points for at least $(n - 1)|K|$ of the $|K|^2$ challenges. **[machine-checked]**

### 3.4 Rate 1/2 at agreement $5n/8$

**(a) A fixed set and a free flat (`Padded.lean`).** Hand statements: note 01 Lemma C with one flat; note 05 Lemma 1.1 with a fixed set and a free flat; note 05 Corollary 2.2: for a hyperplane $H$ of $D$, $b \notin H$, $P \subseteq H$ of $3n/8$ points and each of the $2^N - 2$ affine hyperplanes $F$ of $b + H$, $L_{P \sqcup F} = L_P X^{n/4} + C_F$ with $\deg C_F \le n/2$.

| Lean statement | content | status |
| --- | --- | --- |
| `natDegree_locator_flat_sub_le` | $\deg(X^{|V|} - L_{a+V}) \le |V|/2$ | **[machine-checked]** |
| `padPoly_mem_RSList`, `agree_padPoly` | for $P$ and $F = a + V$ disjoint in $D$: $L_P(X^{|V|} - L_F)$ has degree at most $|P| + |V|/2$ and agrees with the word $L_P(x)x^{|V|}$ exactly on $P \cup F$ | **[machine-checked]** |
| `flat_direction`, `padPoly_injective` | distinct flats give distinct polynomials | **[machine-checked]** |
| `padded_flats_list` | $H$ a hyperplane of the subspace $D$, $|D| = n = 4q$, $P \subseteq H$ any set: the word $L_P(x)x^{q}$ has at least $n - 2$ polynomials of degree at most $|P| + n/8$ at agreement at least $|P| + n/4$ | **[machine-checked]** |
| `five_eighths_slack` | $|P| = 3n/8$: at least $n - 2$ polynomials of degree at most $n/2$ at agreement $5n/8$ | **[machine-checked]** |
| `five_eighths_genuine` | $|P| = 3n/8 - 1$: at least $n - 2$ polynomials of degree below $n/2$ at agreement $5n/8 - 1$ | **[machine-checked]** |

`padded_flats_list` is Corollary 2.2 with its count $2^N - 2$ and with $P$ of any size. The genuine variant is obtained by removing one point of the padding, which is the genuine variant of note 05 section 1.1 when the removed point is $0$.

**(b) The gap lemma and Theorem 2.1 (1) (`Gap.lean`, `UnionOfFlats.lean`).** Hand statements: note 05 Lemma 1.1 (if $L_{S_i} = A_i + B_i$ with $\deg B_i \le |S_i| - g_i$ then $L_S = \prod A_i + C$, $\deg C \le |S| - \min g_i$); Theorem 2.1 (1): every $S$ of size $5n/8$ that is a disjoint union of flats, each a coset of $W$ ($|W| = n/8$) or of size at least $n/4$, has $L_S = X^{n/2}L_W + C_S$ with $\deg C_S \le n/2$.

| Lean statement | content | status |
| --- | --- | --- |
| `HasGap.mul`, `gap_lemma`, `gap_lemma_locator` | Lemma 1.1, for products of polynomials and for locators of a disjoint union, with one common gap $g$; any field | **[machine-checked]** |
| `hasGap_coset`, `hasGap_flat` | the pieces: a coset of $W$ has top $L_W$ with gap $|W|$ (any field); a free flat $a + V$ has top $X^{|V|}$ with gap $|V|/2$ | **[machine-checked]** |
| `FlatUnion.card`, `FlatUnion.dvd`, `FlatUnion.hasGap` | for a disjoint union $S$ of $i$ cosets of $W$ and of flats of size at least $2|W|$ and total size $M$: $|S| = i|W| + M$, $2|W|$ divides $M$, and $L_S = L_W^i X^M + (\deg \le |S| - |W|)$ | **[machine-checked]** |
| `hasGap_subPoly_sq`, `hasGap_subPoly_odd_pow` | $L_W^2 = X^{2|W|} + (\deg \le |W|)$; $L_W^{2j+1}X^M$ has the top of $L_W X^{M + 2j|W|}$ | **[machine-checked]** |
| `FlatUnion.natDegree_le` | for an odd number of cosets: $\deg(L_S - X^{|S| - |W|}L_W) \le |S| - |W|$ | **[machine-checked]** |
| `flatUnion_five_eighths` | Theorem 2.1 (1): $|S| = 5|W|$ implies $\deg(L_S - X^{4|W|}L_W) \le 4|W|$ | **[machine-checked]** |
| `flatUnion_mem_RSList` | then $X^{4|W|}L_W - L_S$ is in the list of $x \mapsto x^{4|W|}L_W(x)$ at degree at most $4|W|$ and agreement $5|W|$, on any $D \supseteq S$ | **[machine-checked]** |

`FlatUnion W S i M` is an inductive predicate: the empty set; adding a coset of $W$ disjoint from what is there; adding a flat $b + V$ with $|V| \ge 2|W|$ disjoint from what is there. With $|W| = n/8$ it is the family $\mathcal F_W$ of Theorem 2.1 (flats of size at least $n/4$), and the parity argument of the proof ("$i$ is odd because the other pieces have sizes divisible by $n/4$") is `FlatUnion.dvd`. Parts (2) and (3) of Theorem 2.1 (the count $56(2^N - 7)$, the genuine codewords) are **[not formalized]**.

**(c) Theorem 5 of note 02 (`Glued.lean`, `GluedCount.lean`).** Hand statement: $W$ a hyperplane of $U$, $\eta_W$ the nonzero element of $L_W(U)$, $L_U = L_W^2 + \eta_W L_W$; for every $2g$-subset $Y$ of $L_W(D)$ with $\sum Y = g\eta_W$ the set $S = L_W^{-1}(Y)$ has $g|U|$ points and $\deg(L_U^g - Z_S) \le (g-1)|U|$; sets from different $W$ coincide only if they are unions of cosets of $U$; the count. In Lean $\eta_W$ is `(subPoly W).eval a` for any $a \in U \setminus W$, and `glued D W Y` is $D \cap L_W^{-1}(Y)$.

| Lean statement | content | status |
| --- | --- | --- |
| `subPoly_eq_comp` | $L_U = (X^2 + \eta X) \circ L_W$ | **[machine-checked]** |
| `locator_glued`, `card_glued` | $Z_S = V_Y(L_W)$ with $V_Y = \prod_{y \in Y}(X - y)$; $|S| = |Y| \cdot |W|$ | **[machine-checked]** |
| `natDegree_gluedPoly_le` | $|Y| = 2g$, $\sum Y = g\eta$: $\deg(L_U^g - Z_S) \le (2g - 2)|W|$ | **[machine-checked]** |
| `gluedPoly_mem_RSList`, `glued_list` | the word $L_U^g$ has at least as many polynomials of degree at most $(g-1)|U|$ at agreement $g|U|$ as there are such label sets $Y$, for one $W$ | **[machine-checked]** |
| `glued_five_eighths` | $g = 5$: label sets of ten labels with sum $\eta$, degree at most $4|U|$, agreement $5|U|$ | **[machine-checked]** |
| `glued_eq_imp_invariant` | members from two different hyperplanes of $U$ coincide only if the set is invariant under $U$ | **[machine-checked]** |
| `exists_label_set` | in a subspace of sixteen labels containing $\eta \ne 0$ there is a set of ten labels with sum $\eta$ that contains $\eta$ and not $0$ | **[machine-checked]** |
| `glued_list_card` | $|D| = n = 8|U|$: the word $L_U^5$ has at least $|U| - 1 = n/8 - 1$ polynomials of degree at most $n/2$ at agreement $5n/8$ | **[machine-checked]** |

The number $\nu = 504$ of admissible label sets per hyperplane, hence the count $56 + 448(n/8 - 1) = 56n - 392$, is **[not formalized]**. `glued_list` reduces the count for one hyperplane to a statement about ten-subsets of a group of order sixteen, and `glued_eq_imp_invariant` is the step that adds the counts of different hyperplanes; what is missing is that finite count (the kernel cannot decide it by enumeration without `native_decide`, and the character-sum proof was not attempted). The genuine variant ($35n - 245$) and the slack variant of Theorem 5 are **[not formalized]**.

### 3.5 Instantiation (`Concrete.lean`)

| Lean statement | content | status |
| --- | --- | --- |
| `exists_addSubgroup_card` | a finite subspace contains a subspace of every smaller size $2^m$ | **[machine-checked]** |
| `exists_domain_GF128` | `GaloisField 2 128` has a subspace of $2^m$ points for every $m \le 128$ | **[machine-checked]** |
| `flats_quarter_GF128` | a subspace $D$ of $2^{26}$ points with at least $2^{26} - 1$ polynomials of degree below $2^{24}$ agreeing with $x^{2^{25}-1}$ on at least $2^{25} - 1$ points | **[machine-checked]** |
| `flats_break_mca_GF128` | on such a $D$, a pair of words whose first word agrees with every polynomial of degree at most $2^{24} - 2$ on at most $2^{24} - 1$ points and whose affine fold is $(2^{24} - 2, 2^{25} - 1)$-close for at least $(2^{26} - 1) \cdot 2^{128}$ challenges | **[machine-checked]** |
| `five_eighths_slack_GF128`, `five_eighths_genuine_GF128` | a subspace of $2^{25}$ points and a word with at least $2^{25} - 2$ polynomials of degree at most $2^{24}$ at agreement $5 \cdot 2^{22}$, respectively of degree below $2^{24}$ at agreement $5 \cdot 2^{22} - 1$ | **[machine-checked]** |
| `glued_list_card_GF128` | subspaces $U \le D$ of $2^{22}$ and $2^{25}$ points with at least $2^{22} - 1$ polynomials of degree at most $2^{24}$ agreeing with $L_U^5$ on at least $5 \cdot 2^{22}$ points | **[machine-checked]** |

The general theorems are quantified over every finite additive subgroup of every field of characteristic two, so they apply to leanVM's domain $D_{\kappa,R}$; the instances only show that the hypotheses are satisfiable. The field is Mathlib's `GaloisField 2 128`, not the tower $K[y]/(y^2 + xy + 1)$ over $\mathbb{F}_2[x]/(x^{64} + x^4 + x^3 + x + 1)$, and the domain is some subspace of the right size, not the span of $1, x, \dots, x^{N-1}$ **[not formalized]**.

## 4. What formalizing showed about the hand proofs

No error and no missing hypothesis. The observations:

1. **The degree of $Q_V$ is at most $2^{s-1} - 1$, not equal to it** (note 00 section 1 says "has degree $2^{s-1} - 1$"). Equality needs $c_{s-1} \ne 0$, which fails for some subspaces: for $V = \mathrm{GF}(4)$, $L_V = X^4 + X$ and $Q_V = 1$. Only the upper bound is used, and the brief states it correctly.
2. **Additivity of $L_V$ does not use characteristic two.** `subPoly_comp_add`, `subPoly_eval_add` and `locator_coset` hold for every finite additive subgroup of every field (in characteristic zero only $\{0\}$ is finite). Characteristic two enters with the recursion on the dimension and the linearized form.
3. **The pole collapse holds over every field, with one sign**: the line of Lemma A is $\alpha + \beta\beta_0 = -C_i(\beta_0)$. For the affine combiner the collapse is an equivalence at every degree $d$ and every $T$, with no condition relating $d$, $T$ and $n$; for a combiner of degree $r$ it is an equivalence when $r \le d + 1$ and an implication at degree $\max(d, r-1)$ otherwise. The second word $f_1$ is arbitrary in the collapse.
4. **Lemma 1.1 needs a convention when a gap exceeds its piece.** "$\deg B_i \le |S_i| - g_i$" with a negative right side must mean $B_i = 0$ (a fixed set has gap $\infty$). The hand proof reads it that way. With natural-number subtraction the statement would be false (two pieces $A_i + c_i$ with constants $c_i$ and a gap larger than both sizes), so the Lean form states the gap on coefficients: `HasGap p A n g` is "the coefficient of $X^m$ in $p - A$ vanishes whenever $n < m + g$".
5. **Hypotheses that are never used.** Theorem 5: no relation between $g$, $\rho$, $M'$ and $n$ is needed for the degree bound (the condition "$g = \rho M' + 1$" only names the rate), and $D$ is any subspace containing $U$. Theorem 2.1 (1): $N \ge 4$, $|W| = n/8$ and $S \subseteq D$ are not needed; the statement holds for any odd number of cosets of any finite subspace $W$ with the word $X^{|S| - |W|}L_W$. Corollary 2.2: $|P| = 3n/8$ is not needed. Flats: `flats_list` needs of $D$ only that it contains the subspaces counted.
6. **The count of Lemma A.** The notes average over poles to keep most of the $L$ values $C_i(\beta_0)$ distinct. Lean has the clean case only: all values distinct for some pole outside $D$ when $(d+1)\binom{L}{2} + n < |K|$. For the flats family at $n = 2^{26}$ this needs a field larger than $2^{75}$, so it applies with poles in $E$ (`flats_break_mca_GF128`) and not with poles in $K = \mathrm{GF}(2^{64})$, where the notes' averaging bound is the right statement.

## 5. What is not machine-checked

- **The exact counts**: $56n - 392$ (Theorem 5, Theorem 2.1 (2)), $35n - 245$ (genuine), $\nu = 504$, the tree count $M_2(N)$, the Gaussian binomials for flats at rates below 1/4, the $2n - 2$ affine hyperplanes in degree at most $n/4$. Checked lower bounds: $n - 1$ (flats, rate 1/4), $n - 2$ (padded word, $5n/8$), $n/8 - 1$ (the word $L_U^5$, $5n/8$). **[not formalized]**
- **Theorem 2.1 (2), (3)**, the genuine and slack variants of Theorem 5, the completeness of the class in the formal model, Corollary 2.3 and Proposition 1.3 (complement duality) of note 05. **[not formalized]**
- **Lemma B and Lemma C of note 01 as stated** (Lemma C with several free flats and an arbitrary fixed set follows from `gap_lemma_locator`, `hasGap_flat` and `hasGap_self`, but is not stated), sections 3.2 to 3.9 of note 01, the averaging over poles after Lemma A. **[not formalized]**
- **Exact agreement** for the members of (b) and (c): `flatUnion_mem_RSList` and `gluedPoly_mem_RSList` prove agreement at least $5n/8$; that it is exactly $S$ is immediate from the locator but not stated. It is stated for the flats and for the padded flats.
- **The link to the protocol.** That a list at agreement $T$ breaks the protocol when the threshold is at or below $T$ (note 03), that the bad challenges of a pole pair are a constraint on the state function and not an attack, the term $\Gamma_{\mathrm{un}}$, and any connection to `formal/`. The Lean statements are about lists and about closeness of folds, over one field (the words, the polynomials, the pole and the challenges all in $K$). **[not formalized]**
- **leanVM's concrete field and domain** (section 3.5). **[not formalized]**

## 6. Reproduction

`lean/Constructions/README.md`. In short, on a build host: `cd doc/whir_soundness_gap_notes/lean && lake exe cache get && lake build Constructions`. The scratch project that was checked is `h4:/data/whir_lean_scratch_29/lakeproj`, with its log `lake-build.log` one directory up; `h4:/data/whir_lean_scratch_29/check.sh` is the single-file check of run 1.
