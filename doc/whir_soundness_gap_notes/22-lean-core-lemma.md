# 22. The DEEP fold lemma, machine-checked in Lean 4

Researcher 22. This note says exactly what of the DEEP fold lemma (note 07 Theorem 3 and Corollary 4, note 10 Theorem A, note 11 Lemmas D2 to D4, note 14 Lemmas E, L1, L2 and F) is now checked by Lean 4 with Mathlib, what is not, and how to reproduce the check. The sources are in `lean/` (about 2000 lines of Lean in ten files, `lean/README.md` for the build). Tags: **[machine-checked]** means the statement is a Lean theorem that compiles with no `sorry` and depends on Lean's three axioms only; **[not formalized]** means no Lean statement exists.

## 0. Summary

1. **The whole of Lemma F of note 14 is machine-checked**, both halves, with lanes, monomial lane weights, the weighted claim and the predicate $B$: `lemmaF_exc` (the bound on the exceptional set) and `lemmaF_round` (fewer than $K_0$ winning challenges outside it). So are Lemma D4 of note 11 with its constants (`lemmaD4_exc`, `lemmaD4_round`), Theorem 3 of note 07 in the single-lane case (`deepFold_theorem3`) and with lanes (`deepFoldL_theorem3`), Theorem A of note 10 in an abstract counting form (`card_Exc_mul_le`, `exists_big_class`), and every lemma they rest on: Lemma 1 and Lemma 2 of note 07, Lemmas 2.1 and 2.2 (a) to (c) of note 10, Lemmas D2 and D3 of note 11, Lemma E and Lemmas L1 and L2 of note 14.
2. **No error was found in the hand proofs.** Every step went through as written. Section 4 lists what the formalization does show: several hypotheses of the notes are not used, characteristic two is used in exactly one line, and two statements of note 10 are loosely worded (note 14 already states them correctly).
3. **Checked on `h4`** with Lean 4.36.0 and Mathlib `v4.36.0` (revision `fc4f59e577`, the one `formal/` pins), twice: against the Mathlib already built on the host, and as a fresh Lake project. Nothing was installed or built on the Mac.
4. **Not formalized**: the pinning lemma (Lemma P), the potential over the rounds of a level (Lemma T), the round-by-round theorem and knowledge soundness of note 14, the $\mathrm{eq}$-weight variant of notes 07 and 10, the tightness claims, and the link from the protocol's verifier checks to the conditions (p), (w), (b). Section 5.

## 1. How it was checked

Host `h4`, scratch directory `/data/whir_deepfold_lean_scratch` (created for this, 7.4 GB with the fetched Mathlib cache, safe to delete). Lean `leanprover/lean4:v4.36.0`, commit `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`; Mathlib tag `v4.36.0`, revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`; the other packages are in `lean/lake-manifest.json`.

- Run 1: each module compiled in dependency order with `lean -o`, from an empty output directory, against the Mathlib already built in `/data/lean436/formal/Statement/.lake/packages` (read only). No output: no error, no warning.
- Run 2: a fresh Lake project with the same files, `lake update` (fetches Mathlib and its cache into the scratch project), `lake build`: `Build completed successfully (18272 jobs)`. `lakefile.toml` sets `warningAsError`. The only messages are Lake's advisory that two files import `Mathlib` without the module system.
- No `sorry`, `admit`, `axiom` or `native_decide` occurs in the sources. `DeepFold/Axioms.lean` runs `#print axioms` under `#guard_msgs` on 50 statements, all those named in this note: each depends on `propext`, `Classical.choice`, `Quot.sound` and nothing else, and the build fails if that changes.
- `DeepFold/Axioms.lean` also instantiates `lemmaF_round` and `lemmaF_exc` at `GaloisField 2 128` with four lanes, so the typeclass hypotheses (a finite field of characteristic two) are satisfiable at the deployed size.

## 2. What is stated and checked

Notation of the Lean. `K` is a field (finite where counting is involved, of characteristic two only where said). `aff c` is $a_c = \alpha + \beta X$ for $c = (\alpha, \beta)$. A candidate is a pair `(c, P)`; with lanes `P : ι → K[X]` is a tuple indexed by a finite type `ι`. `Cons e z a b` is $P(z) = b + (\alpha + \beta z)\,a$, so $a = y^F$, $b = y^G$. `Delta e₁ e₂ e₃` is the determinant polynomial, `IsFold F G e` is $P = G + a_c F$ in `RatFunc K`.

### 2.1 The algebraic heart, single lane (scope item 1)

| Lean statement | content | notes | status |
| --- | --- | --- | --- |
| `Delta_eq_det` | `Delta` is $\det\begin{pmatrix} P_1 & 1 & a_1\\ P_2 & 1 & a_2\\ P_3 & 1 & a_3\end{pmatrix}$ | the brief | **[machine-checked]** |
| `Delta_char_two` | in characteristic two `Delta` is $Q = (a_2 + a_3)P_1 + (a_1 + a_3)P_2 + (a_1 + a_2)P_3$ | the $Q$ of all four notes | **[machine-checked]** |
| `Delta_eval_eq_zero` | three candidates consistent with one answer $(a, b)$ at $z$ have $\Delta(z) = 0$ | 07 L1 (a), 10 L2.1 (c), 11 D2 (a), 14 L1 (c) | **[machine-checked]** |
| `Delta_natDegree_le` | $\deg \Delta \le d + 1$ when $\deg P_i \le d$ | used in every note | **[machine-checked]** |
| `Delta_eq_zero_iff` | for $c_1 \ne c_2$: $\Delta = 0$ iff $P_3 = G + a_3 F$ with $F = (P_2 - P_1)/(a_2 - a_1)$, $G = P_1 - a_1 F$ | 07 L1 (b), 10 L2.1 (b), 11 D2 (b), 14 L1 (b) | **[machine-checked]** |
| `isFold_pair_left`, `isFold_pair_right`, `isFold_unique` | two candidates with $c_1 \ne c_2$ are folds of exactly one rational pair | 10 L2.1 (a), 14 L1 (a) | **[machine-checked]** |
| `Delta_eq_zero_iff_exists` | for $c_1 \ne c_2$: $\Delta = 0$ iff the three are folds of one common rational pair | 10 L2.1 (b) | **[machine-checked]** |
| `fold_anchor_dichotomy` | two folds of $(F, G)$ with different $\beta$ and degree at most $d$: either $F, G$ are polynomials with $\deg F < d$, $\deg G \le d$, or every fold of $(F, G)$ has its challenge on the line $\alpha + x_0\beta = \mathrm{const}$ through the pole $x_0$ | the proof of 07 L2 (i) | **[machine-checked]** |
| `class_trichotomy` | a set of folds of one rational pair, degree at most $d$: a polynomial pair of degrees $(< d, \le d)$, or all challenges on one line, or all with one $\beta$ | 10 L2.2 (a), (b), 14 L2 (a), (b), (c) | **[machine-checked]** |
| `class_poly_of_card_gt` | a class with more than $q$ elements is the class of a polynomial pair with $\deg F < d$, $\deg G \le d$ | 07 L2 (i), 11 D3 (i) | **[machine-checked]** |
| `card_agr_outside_le` | in the class of a polynomial pair at most $\binom{n - \lvert Z\rvert}{2}$ elements have two agreement columns outside $Z$ | 10 L2.2 (c), 14 L2 (c) | **[machine-checked]** |
| `agrPair_card_ge` | a class of a polynomial pair with more than $\binom n2$ elements, each agreeing on at least $A$ columns, has $\lvert Z\rvert \ge A - 1$ | 07 L2 (ii), 11 D3 (ii) | **[machine-checked]** |

`Delta_eval_eq_zero` needs no hypothesis on the challenges, and everything in this table holds over any field, with the signs of the determinant.

### 2.2 The probabilistic step (scope item 2)

Points are elements of a finite type `Pt`, candidates elements of a type `τ`; `dep` is a ternary relation ("in one class"), `van t₁ t₂ t₃ z` says the determinant of the triple vanishes at `z`, `cons t z m` that `t` is consistent with the answer `m` at `z`. `Ncount T dep van z` is $N(\mathbf z)$, the number of ordered triples of `T` that are not dependent and vanish at every $z_i$; `Exc T dep van s B` is $\{\mathbf z \in \mathrm{Pt}^s : N(\mathbf z) \ge B\}$.

| Lean statement | content | notes | status |
| --- | --- | --- | --- |
| `card_vanish_all_le`, `prob_vanish_all_le` | a nonzero polynomial of degree at most $D$ vanishes at all of $s$ points for at most $D^s$ of the $q^s$ vectors: probability at most $(D/q)^s$ | Schwartz-Zippel with independence | **[machine-checked]** |
| `sum_Ncount_le` | $\sum_{\mathbf z} N(\mathbf z) \le \lvert T\rvert^3 D^s$ if every non-dependent triple vanishes at no more than $D$ points | $\mathbb E[N] \le \lvert\mathcal T\rvert^3\epsilon^s$ | **[machine-checked]** |
| `card_Exc_mul_le`, `density_Exc_le` | Markov: $\lvert\mathrm{Exc}\rvert \cdot B \le \lvert T\rvert^3 D^s$, so the density is at most $\lvert T\rvert^3\epsilon^s/B$, $\epsilon = D/\lvert\mathrm{Pt}\rvert$ | 10 Theorem A, $\varepsilon_{\mathrm{pt}}$ | **[machine-checked]** |
| `card_nondep_triples_ge` | if every pair of $W$ has at most $M$ elements of $W$ dependent with it, at least $K(K-1)(K-M)$ ordered triples of $W$ are not dependent | 10 L2.1 (d), 14 L1 (d) | **[machine-checked]** |
| `exists_big_class` | for $\mathbf z \notin \mathrm{Exc}$ at threshold $K_0(K_0-1)(K_0-M)$ and every answer vector $m$: every $W \subseteq T$ with $\lvert W\rvert \ge K_0$, all $m$-consistent, has two distinct elements with more than $M$ elements of $W$ dependent with them | 10 Theorem A | **[machine-checked]** |
| `exists_big_class_quarter` | the same at threshold $\lceil K_0^3/4\rceil$, $K_0 \ge 26$: a class with at least $0.74\,\lvert W\rvert$ elements | 07 Theorem 3, first sentence | **[machine-checked]** |
| `quarter_cube_le` | $K_0^3 \le 4K_0(K_0-1)(K_0-M)$ for $K_0 \ge 26$, $M \le 0.74K_0$ | 10 section 2.2, comparison | **[machine-checked]** |

The abstract theorem uses no linear-space axiom: the count of `card_nondep_triples_ge` needs only that each ordered pair has at most $M$ dependent third elements. Uniqueness of the class through two elements (Lemma 2.1 (a)) is needed only to read `dep` as "in one class", which `Delta_eq_zero_iff` does.

The instantiation for one lane, with points in $K$:

| Lean statement | content | notes | status |
| --- | --- | --- | --- |
| `card_ExcD_mul_le`, `density_ExcD_le` | density of the exceptional set at most $\lvert T\rvert^3((d+1)/q)^s/B$ | 10 Theorem A, one lane | **[machine-checked]** |
| `card_T_le` | $\lvert T\rvert \le \Lambda q^2$ if every challenge has at most $\Lambda$ candidates | $\lvert\mathcal T\rvert \le \Lambda q^2$ | **[machine-checked]** |
| `deepFold_class` | outside the exceptional set, every $m$-consistent $W \subseteq T$ with distinct challenges and $\lvert W\rvert \ge K_0$ has more than $M$ folds of the rational pair of two of its elements | 10 Theorem A | **[machine-checked]** |
| `deepFold_theorem3` | with $M \ge \max(q, \binom n2)$: more than $M$ elements of $W$ are folds $G_0 + a_cF_0$ of one polynomial pair with $\deg F_0 < d$, $\deg G_0 \le d$, $\lvert Z\rvert \ge A - 1$, $F_0(z_i) = y^F_i$, $G_0(z_i) = y^G_i$ for all $i$ | 07 Theorem 3, 10 Theorem A consequence 1 | **[machine-checked]** |

### 2.3 Lanes with monomial weights, and the round with its claims (scope item 3, both parts)

`evL ex z U` is $\mathrm{ev}_z(U) = \sum_u \theta^{\mathrm{ex}(u)}U_u(\zeta)$ at $z = (\theta, \zeta)$ for an exponent map `ex : ι → ℕ`. The Lean assumes of `ex` only that it is injective with values at most `E` (in note 14, $\mathrm{ex} = e_j$ and $E = 2^\ell - 2^j$), and only for the bound on the exceptional set.

| Lean statement | content | notes | status |
| --- | --- | --- | --- |
| `evL_add`, `evL_mul`, `evL_halves` | (E1), (E3), (E2) | 14 Lemma E | **[machine-checked]** |
| `card_evL_zero_le` | (E4): a nonzero tuple of degree at most $\Delta$ vanishes at no more than $(\Delta + E)\,q$ of the $q^2$ points | 14 Lemma E | **[machine-checked]** |
| `evL_DeltaL_eq_zero`, `DeltaL_eq_zero_iff`, `isFoldL_unique` | L1 (c), (b), (a) with lanes | 14 L1, 11 D2 | **[machine-checked]** |
| `card_ExcL_mul_le`, `density_ExcL_le` | density of $\mathrm{Exc}$ at most $\lvert T\rvert^3\epsilon^s/B$ with $\epsilon = (d + 1 + E)/q$ | 14 Lemma F (1) | **[machine-checked]** |
| `classL_poly_of_card_gt`, `card_agrL_outside_le`, `exists_nearL` | L2 (a), (b), (c) with lanes, the near-tuple clause included | 14 L2, 11 D3 | **[machine-checked]** |
| `deepFoldL_theorem3` | Theorem 3 with lanes: the polynomial pair of tuples, its degrees, $\lvert Z\rvert \ge A - 1$, consistency with the answers, and an element of which it is a near tuple | first half of the proof of 11 D4 (2) | **[machine-checked]** |
| `card_quadric_zeros_le` | $a + b\alpha + c\alpha^2 + \beta(d + e\alpha)$ with $(a, b) \ne (0, 0)$ has at most $2q$ zeros in $K^2$ | the residual of `lem:fold-list` | **[machine-checked]** |
| `deepFoldL_fold_round` | Corollary 4 with lanes and the predicate $B$, for an explicit answer vector | 07 Corollary 4, 10 Theorem A consequence 2 | **[machine-checked]** |
| `deepFold_lemmaF` | Lemma F (2) for any finite set $T$ of candidates of degree at most $d$ and agreement at least $A$ | 14 Lemma F (2) | **[machine-checked]** |
| `mem_fullT` | $\mathcal T$ exists as a finite set: $(c, P) \in \mathcal T$ iff $\deg P_u \le d$ for all $u$ and $P$ agrees with $O_c$ on at least $A$ columns | the definition of $\mathcal T$ | **[machine-checked]** |
| `lemmaF_exc`, `lemmaF_round` | Lemma F (1) and (2) for $\mathcal T$ | 14 Lemma F | **[machine-checked]** |
| `lemmaD4_exc`, `lemmaD4_round` | Lemma D4 (1) and (2): threshold $\lceil K_0^3/4\rceil$, bound $4\Lambda^3q^6\epsilon^s/K_0^3$, $K_0 \ge 26$, $0.74K_0 \ge M$ | 11 Lemma D4, 07 Theorem 3 and Corollary 4 | **[machine-checked]** |

### 2.4 The two end statements, as Lean checks them

```lean
theorem lemmaF_exc (D : Finset K) (O₀ O₁ : K → ι → K) (d A : ℕ) {ex : ι → ℕ}
    (hex : Function.Injective ex) {E : ℕ} (hE : ∀ u, ex u ≤ E) (Λ : ℕ)
    (hΛ : ∀ c : K × K, ((fullT D O₀ O₁ d A).filter (fun e => e.1 = c)).card ≤ Λ)
    (s : ℕ) {B : ℕ} (hB : 0 < B) :
    ((ExcL (fullT D O₀ O₁ d A) ex s B).card : ℚ) / (Fintype.card (Fin s → K × K) : ℚ) ≤
      (Λ : ℚ) ^ 3 * (Fintype.card K : ℚ) ^ 6 *
        (((d + 1 + E : ℕ) : ℚ) / Fintype.card K) ^ s / B

theorem lemmaF_round [CharP K 2] (D : Finset K) (O₀ O₁ : K → ι → K) (d A : ℕ) (ex : ι → ℕ)
    (w : ℕ) {s K₀ M : ℕ} (hMq : 2 * Fintype.card K ≤ M) (hMn : D.card.choose 2 ≤ M)
    {z : Fin s → K × K}
    (hz : z ∉ ExcL (fullT D O₀ O₁ d A) ex s (K₀ * (K₀ - 1) * (K₀ - M)))
    (W₀ W₁ : (ι → K[X]) →ₗ[K] K) (σ : K) (v : Fin s → K)
    (B : (ι → K[X]) → (ι → K[X]) → Prop)
    (hyp : ∀ F₀ G₀ : ι → K[X], (∀ u, (F₀ u).degree < (d : WithBot ℕ)) →
      (∀ u, (G₀ u).natDegree ≤ d) → A ≤ (agrPairL D O₀ O₁ F₀ G₀).card + 1 → B F₀ G₀ →
      (∀ i, (z i).1 ^ w * evL ex (z i) F₀ + evL ex (z i) G₀ = v i) → W₀ F₀ + W₁ G₀ ≠ σ)
    (vG vF σ₀ σ₁ : K) (φm : Fin s → K) :
    (univ.filter (fun c : K × K => ∃ P : ι → K[X],
      (∀ u, (P u).natDegree ≤ d) ∧ A ≤ (agrL D O₀ O₁ (c, P)).card ∧
      (∀ i, evL ex (z i) P = v i + ((z i).1 ^ w + c.1 + c.2 * (z i).2) * φm i) ∧
      ((1 + c.1) • W₀ + c.1 • W₁) P =
        vG + c.1 * (vG + σ) + c.1 ^ 2 * vF + c.2 * σ₀ + c.1 * c.2 * (σ₀ + σ₁) ∧
      (∀ F₀ G₀ : ι → K[X], (∀ u, (F₀ u).natDegree ≤ d) → (∀ u, (G₀ u).natDegree ≤ d) →
        (agrL D O₀ O₁ (c, P) \ agrPairL D O₀ O₁ F₀ G₀).card ≤ 1 → B F₀ G₀))).card < K₀
```

Reading. `ExcL T ex s B` is the set of $\mathbf z \in (K^2)^s$ such that at least $B$ ordered triples of $T$ have pairwise different challenges, $Q \ne 0$ and $\mathrm{ev}_{z_i}(Q) = 0$ for all $i$: the $\mathrm{Exc}_j(O)$ of note 14 when $B = K_0(K_0-1)(K_0-M)$. It is a function of the words, the degree, the agreement, the exponents and the threshold, and of nothing else: the answers, the claim, the predicate and the prover message are quantified after `hz`, which is the order the protocol needs. `fullT D O₀ O₁ d A` is $\mathcal T$. `w` is $2^{j-1}$, so by `evL_halves` the left side in `hyp` is $\mathrm{ev}^{(j-1)}_{z_i}(U)$ for $U = (F_0, G_0)$. `agrPairL` is $Z$, and `A ≤ |Z| + 1` says $U \in \mathrm{List}(O; A-1, d)$. The four conjuncts after the list membership are (p), (w), (b) of Lemma F. `W₀ F₀ + W₁ G₀` is $\langle W, U\rangle$.

## 3. Where the Lean statements differ from the notes

None of these weakens what is proved.

1. **Any field, with signs.** Everything up to `deepFoldL_fold_round` is proved over an arbitrary field; `Delta` carries the signs of the determinant and equals the notes' $Q$ in characteristic two (`Delta_char_two`). Only `deepFold_lemmaF` and the statements of `Main.lean` that use it assume characteristic two.
2. **Any finite candidate set.** The theorems before `Main.lean` hold for any finite set $T$ of candidates with degree at most $d$ and agreement at least $A$, with the exceptional set of that $T$. `Main.lean` takes $T = \mathcal T$.
3. **$\deg F_0 \le d - 1$ is written `degree < d`**, which also covers $d = 0$ ($F_0 = 0$). In `hyp` the pairs range over $\deg F_0 < d$ only, a weaker hypothesis than the notes' "every $U \in \mathrm{List}(O; A-1, d)$", so the theorem is slightly stronger.
4. **$M$ is any integer with $M \ge \max(2q, \binom n2)$**, not that maximum itself.
5. **The weighted claim is two arbitrary $K$-linear functionals** on tuples. The identity $\langle\widehat W(\alpha,\cdot), G + \alpha F + \beta XF\rangle = v^\ast_G + \alpha(v^\ast_G + \sigma^\ast) + \dots$ is proved inside `deepFoldL_fold_round` from linearity alone, which confirms the remark after Lemma F that the low-part structure of the weights is not used.
6. **Exponents are abstract.** `ex` is any injective map bounded by `E`. The notes' $\epsilon = (d + 2^\ell - 1)/q$ is the case $E = 2^\ell - 2^j$ with $j \ge 1$; the Lean bound is $(d + 1 + E)/q$.
7. **Counting statements.** Probabilities are cardinalities of subsets of $\mathrm{Pt}^s$ divided by $\lvert\mathrm{Pt}\rvert^s$, in $\mathbb Q$; each has an integer form too (`card_Exc_mul_le`, `card_ExcL_mul_le`).
8. **Theorem 3's "$0.74\,\lvert W\rvert$"** is checked in the abstract form (`exists_big_class_quarter`) and its consequences in `lemmaD4_round`; I did not restate `deepFoldL_theorem3` with that conclusion.

## 4. What formalizing showed about the hand proofs

No error and no missing hypothesis. The observations, in decreasing order of interest:

1. **Hypotheses that are never used.** $d + 1 < A$ (note 07) and $d + 2 \le A$ (note 11): no step of Lemmas 1, 2, Theorem 3, Corollary 4 or Lemma F needs any relation between $A$, $d$ and $n$ (note 14 had already dropped it; even $A \le n$ is not needed). $M \ge 2$ and $K_0 > M$ in Theorem A: the count holds for every $M$ in truncated arithmetic, and for $K_0 \le M$ the threshold is zero, the exceptional set is everything and the statement is void. $K_0 \ge 30$ in note 07 and note 11: $K_0 \ge 26$ is what the comparison of the two thresholds needs.
2. **Characteristic two is used in one line only**: $\theta^w\varphi + (v + \theta^w\varphi) = v$, which turns condition (p) into consistency with the answer vector $y^F = \varphi$, $y^G = v + \theta^w\varphi$. The dependency lemma, the class structure, the counting, and even the residual computation with $\widehat W = (1 + \alpha)W_0 + \alpha W_1$ as a formula hold in every characteristic.
3. **Lemma 1 (a) needs no condition on the challenges, and Lemma 1 (b) needs only $c_1 \ne c_2$.** "Pairwise different" is used only so that $N$ counts what the notes say and so that a class has one element per challenge. In the Lean, "not dependent" is literally "pairwise different challenges and $Q \ne 0$", so `ExcL` is the notes' set and not a superset.
4. **Theorem A does not use the linear-space structure in the count.** Lemma 2.1 (d) is true for any ternary relation such that each ordered pair has at most $M$ related third elements. The first identity of 2.1 (d), $\sum_\rho k_\rho(k_\rho - 1) = K(K-1)$, is not needed and is not formalized.
5. **Loose wording in note 10, Lemma 2.2 (b) and (c)**: "(b) if $F$ is a polynomial tuple and $\deg F = d$ ... (c) otherwise $\deg F \le d - 1$" leaves out $\deg F > d$ and classes with fewer than two elements. Both are harmless ($\deg F > d$ cannot happen in a class with two elements, and a class with at most one element shares $\beta$), and note 14's L2 states it correctly ("at least two elements", "degree at least $d$"). The Lean form is the trichotomy `class_trichotomy`, valid for every set of folds.
6. **The hypothesis of Lemma F can be restricted** to pairs with $\deg F_0 < d$ (item 3 of section 3). This is what the proof produces and it is free.
7. **The order of quantifiers is as claimed.** The exceptional set is defined before, and independently of, the answer vector, the claim $(W, \sigma)$, the values $v$, the predicate $B$ and the prover message; Lean's binder order in `lemmaF_round` makes this a checked fact, not a remark.

## 5. What is not machine-checked

- **Lemma P (pinning) and Lemma T (potential)** of note 14 (Lemmas D5, D6 of note 11). Lemma P is a union bound over `card_evL_zero_le` and would be short; Lemma T is a Markov argument over challenge prefixes. **[not formalized]**
- **Theorem D', Theorem K and everything after section 3 of note 14**: the state function, the transitions, knowledge soundness, the interface with the outer protocol. **[not formalized]**
- **That the protocol's checks are (p), (w), (b).** The Lean takes the three conditions as formulas. That the verifier of Protocol D enforces them, that the honest prover satisfies them (completeness), and `lem:fold-list` and `lem:mulx` of Annex B as statements about the real weights are outside. **[not formalized]**
- **The exponent map $e_j$**: that $e_j(u) = \sum_{k > j}(1 - u_k)2^{k-1}$ is injective with maximum $2^\ell - 2^j$ is assumed in the form of `hex` and `hE`, not proved for that map. **[not formalized]**
- **The $\mathrm{eq}(r, u)$ lane weights** of notes 07 and 10 (points in $E^{\log_2 h} \times E$). Only note 14's monomial weights are formalized; one lane is common to both. **[not formalized]**
- **Tightness** (note 10 section 2.3), **Proposition 2.4** of note 10, **Lemma 0** of note 07 and **Lemma 2.2 (d)** of note 10 as separate statements (the argument of 2.2 (d) is checked inside `deepFoldL_theorem3` and `deepFoldL_fold_round`). **[not formalized]**
- **No connection to `formal/`.** The development is standalone on Mathlib; it does not use CompPoly, ArkLib or the Lean verifier, and the Lean-shaped statements of note 11 section 5 are not instantiated.

## 6. Reproduction

`lean/README.md`. In short, on a build host: `cd doc/whir_soundness_gap_notes/lean && lake exe cache get && lake build`. The toolchain is `lean/lean-toolchain`, the Mathlib revision is in `lean/lake-manifest.json`. The scratch project that was checked is `h4:/data/whir_deepfold_lean_scratch/lakeproj`, with its logs `lake-update.log` and `lake-build.log` one directory up.
