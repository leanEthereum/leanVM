# 47. The period descent in Lean 4: Theorem R, its base case and the three-wise Johnson bound

Researcher 47, round 7, Lean formalization. Tags: **[Lean]** the statement is a theorem of the Lean project `lean_descent/` of this directory, compiled in the final build of section 5 with no `sorry` and no axiom beyond `propext`, `Classical.choice`, `Quot.sound`; **[proved]** proved by hand in this note; **[checked]** computed, by the program named; **[quoted]** taken from an earlier note. Nothing here is conjectured except the hypotheses PL and DP of the notes, which stay hypotheses. Notation is that of notes 37, 39 and 46: $F$ a field of characteristic two, $D \subset F$ an $\mathbb{F}_2$-subspace of dimension $N$, $n = 2^N$, degree $< k$, agreement $T$, $\Delta = T - k + 1$, $L_U = \prod_{u \in U}(X - u)$. The sources are `lean_descent/PeriodDescent/*.lean`, and `lean_descent/README.md` describes them file by file.

## 0. Verdict

1. **Theorem R of note 46 is machine-checked as the referee states it. [Lean]** `PeriodDescent.theoremR`: for every field of characteristic two, every subspace $D$ with $2^N$ elements, $1 \le k \le T \le 2^N$, $f \ge 2$, $j_0 \le N - 1$: under PL$(f, j_0)$ every word has at most $\binom{f+1}{3}^{j_0} 2^{Nj_0 - j_0(j_0-1)/2}(B_{j_0} + 1)$ polynomials of degree $< k$ at agreement $T$. The hypothesis is the referee's, word for word (`PLsub`): all subspaces $U \le D$ with $2^j$ elements, $j < j_0$, all degree bounds $\kappa \le \lfloor(k-1)/2^j\rfloor$ ($\kappa = k - 1$ at $j = 0$), all words with blanks, all sets of more than $f$ members. `theoremR_top` is note 39 Theorem 1.3 at the last level ($B_J = n/\Delta$), and `theoremR_N25_f7` is the number: at $N = 25$, $k = 2^{24}$, $T = \lceil 0.64n\rceil$, $f = 7$, at most $2^{467}$ codewords.
2. **Everything under it is machine-checked too. [Lean]** The base case in three forms (note 37 Lemma 3.2 with multi-valued words and fibres; note 04 Theorem 1.2 for an affine space of any dimension $r$; a version that uses no linearity), the algebraic core of the descent step (decomposition, invariance, $c = c_0 + \varrho\,Q(q)$ exactly, degrees, the transformed word, the agreements exactly, the slack), the identification of the levels with subspace polynomials, the supersaturation lemma, the recursion and its closed form, the abstract induction, note 37 Theorem 3.5, and the three-wise Johnson bound of note 44 Lemma 5.2 with its closed form. 140 theorems in all, every one under an axiom check.
3. **Final build line:** `Build completed successfully (18276 jobs).`, exit status 0, on `h4` from an empty build directory, eight cores, nice 10, 18 seconds (Mathlib prebuilt). SHA-256 of all 18 files identical in the repository and in the copy built. A theorem proved by `sorry` fails the same build (`declaration uses sorry`, exit status 1).
4. **No error and no missing hypothesis found** in note 37 section 3, note 39 section 1, the referee's Theorem R, note 04 Theorem 1.2 or note 44 Lemma 5.2. What the formalization did find is in section 3: a sharper constant ($\binom f2$ in place of $\binom{f+1}{3}$, which lowers every conditional bound: $2^{466.4} \to 2^{432.4}$ for $f = 7$), three unused hypotheses of Theorem R, one redundant hypothesis of Lemma 5.2, and that Lemma 3.2 uses no linearity.
5. **What remains:** note 39 Lemma 1.4 and with it Corollary 1.5 and Corollary R0 (the passage from multi-valued to ordinary words), note 37 Corollary 3.6, the rest of note 44 section 5, and the numbers at $j_0 = 18, 19, 21$ (section 6).

## 1. Statement by statement

All Lean names are in the namespace `PeriodDescent`. "As stated" means that the Lean statement has the hypotheses and the conclusion of the hand statement and no more; differences are in the last column.

| hand statement | Lean statement | file | remarks |
| --- | --- | --- | --- |
| note 44 Lemma 5.2, the count $\sum_{\text{triples}} = \sum_x h_M(d_x)$ | `threewise_identity` | `Johnson3` | ordered triples of distinct indices, so both sides carry a factor 6: `H3 M d` $= d(d-1)(3M-4-d) = 6h_M(d)$ (`H3_eq_choose`) |
| the second differences of $h_M$ are $M - 1 - d \ge 0$ | `H3_tangent`, `H3_slope_nonneg` | `Johnson3` | as supporting lines through two consecutive integers |
| inequality (3): $n_e\hat h_M(Ma/n_e) \le \binom M3 c$ | `threewise_jensen` | `Johnson3` | division-free: for every integer $e < M$ the line through $(e, h_M(e))$, $(e+1, h_M(e+1))$, at $Ma/n_e$, times $6n_e$, is $\le M(M-1)(M-2)c$; $e = \lfloor Ma/n_e\rfloor$ is (3) |
| the closed form $M \le \max(1/(1-\alpha), \mathcal B/\mathcal A)$ | `threewise_johnson` (in $\mathbb Z$, cross-multiplied), `threewise_johnson_rat` (as stated, in $\mathbb Q$) | `Johnson3` | without $\alpha \ge \varrho$, without $M \ge 3$, for sets of at least $a$ points |
| note 37 Lemma 3.2 | `base_bound_nat` (in $\mathbb N$), `base_bound` (as stated) | `Base` | for any map $\ell$ with fibres of at most $m$ points; `list_bound_nat` for any family with the interpolation property |
| note 37 Lemma 3.2, the proof as written (affine spaces $H$ of dimension $r$) | `affine_bound`, `affine_poly_bound` | `Affine` | with the MDS property `finrank_add_card_common_zeros_le`, `card_common_zeros_le` |
| note 04 Theorem 1.2 | `affine_ordinary_bound` | `Affine` | any $r$; also `ordinary_bound` ($r = k$) and `collinear_bound` ($r = 1$) in `Base`; cross-multiplied in $\mathbb N$ |
| note 37 Proposition 1.1, first sentence: $c = c_0(q) + Xc_1(q)$ uniquely | `exists_decomp`, `decomp_unique`, `parts_eq` | `Core` | any field |
| note 46 section 1.2 step 1: invariance under $X \mapsto X + a$ | `comp_shift`, `invariant_iff_part1`, `invariant_iff_exists` | `Core` | $P(X + a) = P + a\,u_1(q)$; invariant iff $u_1 = 0$ iff $P \in F[q]$ |
| step 2: $\varrho = u/e_u(q')$, "exactly" | `rho`, `eGcd`, `rho_mul_eGcd`, `periodic_iff_exists`, `periodic_triple_iff` | `Core` | `Periodic a u v` is $v(X)u(X+a) = v(X+a)u(X)$ |
| step 3: $\deg\varrho + 2\deg Q = \deg(P_l - P_0)$ | `natDegree_mul_comp_qPoly`, `natDegree_le_of_descent`, `natDegree_rho_le` | `Core` | |
| step 4: the word $v'$, $\mathrm{agr}_{v'}(Q_l) = \mathrm{agr}_v(P_l) - z_0$ | `nextWord`, `nextWord_agree_iff`, `polyAgr_descent_eq`, `card_zeros_le` | `Step` | exact equality, $z_0$ independent of the member, $z_0 \le m\deg\varrho$ |
| step 5: the slack | `slack_arith`, `LevelPb.next_mem` | `Step` | |
| $L_{U'} = q'(L_U)$, $\lvert D/U\rvert = 2^{N-j}$, fibres of $2^j$ points | `IsLevel.exists_subspace`, `IsLevel.kernel_card`, `IsLevel.fiber_card_le`, `IsLevel.image_card_eq`, `IsLevel.dirs_card_le` | `Level` | |
| note 37 Proposition 3.3 | `LevelPb.descent_step` | `Step` | as stated: an injection of $M_{a'}$ into the members of a level-$(j+1)$ problem at the same slack |
| note 46 section 1.1: the property depends on the unordered triple; collinear members lie in every $M_{a'}$ | `Periodic.swap`, `Periodic.base_swap`, `periodic_of_const`, `BadTriple.exists_dir` | `Core`, `TheoremR` | |
| note 39 Lemma 1.2 | `supersaturation` | `Induction` | as stated; proved through `greedy_cover`, not by counting bad triples |
| note 39 Theorem 1.3, the recursion $a_j \le f + G2^{N-j}a_{j+1}$ and its closed form | `one_step`, `bnd`, `bnd_le`, `expo_eq`, `bnd_closed` | `Induction` | |
| Theorem R, abstract | `abstract_descent`, `abstract_descent_notes` | `Induction` | problems, levels, directions, a periodicity relation; no polynomials |
| note 46 Theorem R | `theoremR` with `BadTriple`, `PLsub`, `baseB` | `TheoremR` | as stated, with fewer hypotheses (section 3) |
| note 39 Theorem 1.3 at $j_0 = J$ | `theoremR_top` | `TheoremR` | for $k \le 2^{j_0}$: $B_{j_0} = n/\Delta$ |
| note 37 Corollary 3.4 and Theorem 3.5 | `abstract_descent_DP`, `DPsub`, `theorem35` | `Induction`, `Theorem35` | $2^{Nj_0 - j_0(j_0-1)/2}(j_0(B+2) + \lfloor n/\Delta\rfloor)$ for $k \le 2^{j_0}$, $j_0 \le N$ |
| note 39 "Numbers", note 46 "Numbers" | `bound_f7`, `bound_f16`, `bound_f133`, `bound_f134` and their `_lower`; `baseB_20_le`, `bound_f7_j20`, `bound_f16_j20`, `bound_f134_j20`; `theoremR_N25_f7`, `theoremR_N25_f7_j20` | `Numbers` | section 1.4 |

### 1.1 Theorem R

**[Lean]** The definitions and the statement, verbatim (`TheoremR.lean`; `polyAgr D ℓ v P` is $\#\{x \in D : v(x) = P(\ell(x))\}$, `subPoly U` is $L_U$, `IsSubspace D` says that $D$ contains $0$ and is closed under addition):

```lean
def BadTriple (D : Finset F) (ℓ : F[X]) (Pa Pb Pc : F[X]) : Prop :=
  (∃ t : F, Pc - Pa = C t * (Pb - Pa)) ∨
    ∃ a' ∈ D.image (fun x => ℓ.eval x), a' ≠ 0 ∧ Periodic a' (Pb - Pa) (Pc - Pa)

def PLsub (D : Finset F) (k Δ f j0 : ℕ) : Prop :=
  ∀ j < j0, ∀ U : Finset F, U ⊆ D → IsSubspace U → U.card = 2 ^ j →
    ∀ κ : ℕ, κ ≤ (k - 1) / 2 ^ j → (j = 0 → κ = k - 1) → ∀ v : F → Option F,
      ∀ S : Finset F[X],
        (∀ P ∈ S, P.natDegree ≤ κ ∧ 2 ^ j * κ + Δ ≤ polyAgr D (subPoly U) v P) → f < S.card →
        ∃ Pa ∈ S, ∃ Pb ∈ S, ∃ Pc ∈ S, Pa ≠ Pb ∧ Pa ≠ Pc ∧ Pb ≠ Pc ∧
          BadTriple D (subPoly U) Pa Pb Pc

noncomputable def baseB (n Δ m κmax : ℕ) : ℚ :=
  (Finset.range (κmax + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩
    (fun κ => ∏ i ∈ Finset.range (κ + 1),
      (((n : ℚ) - (m : ℚ) * i) / ((Δ : ℚ) + (m : ℚ) * ((κ : ℚ) - i))))

theorem theoremR (D : Finset F) (hD : IsSubspace D) (N k T f j0 : ℕ)
    (hN : D.card = 2 ^ N) (hk : 1 ≤ k) (hkT : k ≤ T) (hTn : T ≤ 2 ^ N) (hf : 2 ≤ f)
    (hj0 : j0 + 1 ≤ N) (hPL : PLsub D k (T - k + 1) f j0)
    (w : F → F) (S : Finset F[X]) (hdeg : ∀ P ∈ S, P.degree < k)
    (hagr : ∀ P ∈ S, T ≤ (D.filter (fun x => P.eval x = w x)).card) :
    (S.card : ℚ) ≤ (((f + 1).choose 3 : ℕ) : ℚ) ^ j0 * 2 ^ (N * j0 - j0 * (j0 - 1) / 2)
      * (baseB (2 ^ N) (T - k + 1) (2 ^ j0) ((k - 1) / 2 ^ j0) + 1)
```

Here `F` is any type with `[Field F] [CharP F 2]`, and `Periodic a u v` is `v * u.comp (X + C a) = v.comp (X + C a) * u` (`Core.lean`). The hand statement is Theorem R of note 46 section 1.5. The correspondence is: level-$j$ instance $(U, \kappa, v, \mathcal P)$ = the data `U`, `κ`, `v`, `S` of `PLsub`; "bad" = `BadTriple`; $B_{j_0}$ = `baseB (2^N) Δ (2^j0) ((k-1)/2^j0)`; the exponent `N * j0 - j0 * (j0 - 1) / 2` is in $\mathbb N$, where the division is exact and the subtraction does not truncate for $j_0 \le N$.

### 1.2 The descent step

**[Lean]** Note 37 Proposition 3.3 in one statement (`Step.lean`). A `LevelPb D k` is a level polynomial `ℓ` of level `j`, a degree bound `κ ≤ ⌊(k-1)/2^j⌋` and a word; `p.Mem Δ P` is "degree at most `κ` and agreement at least `2^j κ + Δ`":

```lean
theorem LevelPb.descent_step {D : Finset F} (hD : IsSubspace D) {k : ℕ} (Δ : ℕ) (p : LevelPb D k)
    {c0 c1 : F[X]} (h0 : p.Mem Δ c0) (h1 : p.Mem Δ c1) (h01 : c0 ≠ c1) {a : F}
    (ha : a ∈ (D.image (fun x => p.ℓ.eval x)).erase 0) :
    ∃ p' : LevelPb D k, p'.j = p.j + 1 ∧ ∃ φ : F[X] → F[X],
      (∀ c, p.Mem Δ c → Periodic a (c1 - c0) (c - c0) → p'.Mem Δ (φ c)) ∧
      (∀ c c', p.Mem Δ c → Periodic a (c1 - c0) (c - c0) → p.Mem Δ c' →
        Periodic a (c1 - c0) (c' - c0) → φ c = φ c' → c = c')
```

The problem `p'` is explicit (`LevelPb.next`): level polynomial $q_a \circ \ell$, degree bound $\lfloor(\kappa - \deg\varrho)/2\rfloor$, word `nextWord` $= (v - c_0\circ\ell)/(\varrho\circ\ell)$ with blanks where $v$ is blank or $\varrho(\ell(x)) = 0$, and $\varphi$ is $c \mapsto Q$. The pieces, each **[Lean]**:

```lean
theorem periodic_triple_iff {a : K} (ha : a ≠ 0) {c0 c1 : K[X]} (h01 : c0 ≠ c1) (c : K[X]) :
    Periodic a (c1 - c0) (c - c0) ↔ ∃ Q : K[X], c = c0 + rho a (c1 - c0) * Q.comp (qPoly a)

theorem polyAgr_descent_eq {a : F} {ℓ P P0 ϱ Q : F[X]} (h : P - P0 = ϱ * Q.comp (qPoly a))
    (D : Finset F) (v : F → Option F) :
    polyAgr D ℓ v P = polyAgr D ((qPoly a).comp ℓ) (nextWord ℓ P0 ϱ v) Q
      + (D.filter (fun x => ϱ.eval (ℓ.eval x) = 0 ∧ v x = some (P0.eval (ℓ.eval x)))).card

theorem slack_arith (m κ Δ d A A' : ℕ) (hd : d ≤ κ) (hA : m * κ + Δ ≤ A)
    (hA' : A ≤ A' + m * d) : 2 * m * ((κ - d) / 2) + Δ ≤ A'
```

`rho a u` is defined as $u_0/e\,(q) + X\,u_1/e\,(q)$ with $e = \gcd(u_0, u_1)$, a function of $a$ and $u = c_1 - c_0$ only, and `rho_mul_eGcd` is $u = \varrho\,e(q)$. The inequality that the induction needs is `slack_arith` with $m = 2^j$, $d = \deg\varrho$, $A = \mathrm{agr}_v(c)$ and $A' = \mathrm{agr}_{v'}(Q)$: the threshold $2^j\kappa + \Delta$ at level $j$ becomes $2^{j+1}\lfloor(\kappa - \deg\varrho)/2\rfloor + \Delta$ at level $j + 1$, with the same $\Delta$. It uses $\deg\varrho \le \kappa$ (`natDegree_rho_le`), which the notes use without saying so and which holds because $\varrho$ divides $c_1 - c_0$.

### 1.3 The base case and the three-wise Johnson bound

**[Lean]** (`Base.lean`, `Affine.lean`, `Johnson3.lean`)

```lean
theorem base_bound (D : Finset F) (ℓ : F[X]) (v : F → Option F) (κ m A : ℕ)
    (hfib : ∀ y, (D.filter (fun x => ℓ.eval x = y)).card ≤ m)
    (S : Finset F[X]) (hdeg : ∀ P ∈ S, P.natDegree ≤ κ) (hagr : ∀ P ∈ S, A ≤ polyAgr D ℓ v P)
    (hA : m * κ < A) (hn : m * κ ≤ D.card) :
    (S.card : ℚ) ≤ ∏ i ∈ Finset.range (κ + 1), (((D.card : ℚ) - m * i) / ((A : ℚ) - m * i))

theorem affine_ordinary_bound (D : Finset F) (w : F → F) (k T : ℕ) (W : Submodule F F[X])
    (hW : W ≤ degreeLT F k) (c0 : F[X]) (S : Finset F[X]) (hS : ∀ P ∈ S, P - c0 ∈ W)
    (hagr : ∀ P ∈ S, T ≤ (D.filter (fun x => P.eval x = w x)).card) :
    S.card * ∏ i ∈ Finset.Icc 1 (Module.finrank F W), (T - (k - i))
      ≤ ∏ i ∈ Finset.Icc 1 (Module.finrank F W), (D.card - (k - i))

theorem threewise_johnson (I : Finset ι) (Ω : Finset α) (S : ι → Finset α) (a c : ℕ)
    (hS : ∀ i ∈ I, S i ⊆ Ω) (ha : ∀ i ∈ I, a ≤ (S i).card)
    (hc : ∀ i ∈ I, ∀ j ∈ I, ∀ l ∈ I, i ≠ j → i ≠ l → j ≠ l →
      (S i ∩ S j).card + (S i ∩ S l).card + (S j ∩ S l).card ≤ c + (S i ∩ S j ∩ S l).card)
    (hA : (c : ℤ) * (Ω.card : ℤ) ^ 2 < (a : ℤ) ^ 2 * (3 * (Ω.card : ℤ) - a)) :
    (I.card : ℤ) * ((Ω.card : ℤ) - a) < Ω.card ∨
      (I.card : ℤ) * ((a : ℤ) ^ 2 * (3 * (Ω.card : ℤ) - a) - c * (Ω.card : ℤ) ^ 2)
        ≤ 3 * Ω.card * ((a : ℤ) ^ 2 + Ω.card * a - c * Ω.card)
```

`base_bound` is note 37 Lemma 3.2: $\prod_{i=0}^{\kappa}(n - mi)/(A - mi)$. There `D` is any finite set of points and `ℓ` any polynomial whose fibres on `D` have at most `m` points; `theoremR` uses it with the domain, $\ell = L_U$ and $m = 2^{j_0}$. `affine_ordinary_bound` is note 04 Theorem 1.2, $\prod_{i=1}^{r}(n - k + i)/(T - k + i)$, cross-multiplied with truncated subtraction (for $T < k - i$ the left side is $0$). `threewise_johnson` is the closed form of note 44 Lemma 5.2 multiplied by $n^3$: with $\alpha = a/n$, $\varrho = c/2n$, the hypothesis is $\alpha^2(3 - \alpha) > 2\varrho$ and the conclusion is $M < 1/(1 - \alpha)$ or $M \le 3(\alpha + \alpha^2 - 2\varrho)/(\alpha^2(3 - \alpha) - 2\varrho)$; `threewise_johnson_rat` has exactly these fractions and a `max`. For the lists of the brief take $c = 2k - 1$.

### 1.4 The numbers

**[Lean]** (`Numbers.lean`, by `norm_num`, `decide` and `omega` on numerals) $T = \lceil 0.64 \cdot 2^{25}\rceil = 21474837$ (`T_eq`), $\Delta = 4697622$ (`Delta_eq`), $NJ - J(J-1)/2 = 324$ (`expo_24`), $\binom83 = 56$, $\binom{17}{3} = 680$, $\binom{134}{3} = 392084$, $\binom{135}{3} = 400995$, and:

| $f$ | $j_0$ | Lean: the bound is | note 46 | theorem |
| --- | --- | --- | --- | --- |
| 7 | 24 | $> 2^{466}$ and $\le 2^{467}$ | $2^{466.4}$ | `bound_f7_lower`, `bound_f7`, `theoremR_N25_f7` |
| 16 | 24 | $> 2^{552}$ and $\le 2^{553}$ | $2^{552.9}$ | `bound_f16_lower`, `bound_f16` |
| 133 | 24 | $> 2^{772}$ and $\le 2^{773}$ | $2^{773.0}$ | `bound_f133_lower`, `bound_f133` |
| 134 | 24 | $> 2^{773}$ and $\le 2^{774}$ | $2^{773.7}$ | `bound_f134_lower`, `bound_f134` |
| 7 | 20 | $\le 2^{445}$ | $2^{444.5}$ | `baseB_20_le`, `bound_f7_j20`, `theoremR_N25_f7_j20` |
| 16 | 20 | $\le 2^{517}$ | $2^{516.5}$ | `bound_f16_j20` |
| 134 | 20 | $\le 2^{701}$ | $2^{700.6}$ | `bound_f134_j20` |

`theoremR_N25_f7` is the end-to-end statement: for every field of characteristic two and every subspace `D` with $2^{25}$ elements, `PLsub D (2^24) 4697622 7 24` implies that every word has at most $2^{467}$ polynomials of degree $< 2^{24}$ agreeing with it on at least $21474837$ points. `baseB_20_le` is $B_{20} \le 328734$ (the referee's "at most 328733 members" for the 32-point levels: the maximum over the 16 degrees is $328733.99$, at degree 13). **[checked]** `scripts/47_numbers.py` (exact rationals) reproduces every entry of the table of note 46 section 1.5 for $f = 7, 16, 133, 134$ and $j_0 = 24, 21, 20, 19, 18$ to the digits given there (it prints the levels 16 to 24).

### 1.5 The hypotheses can be met together

**[Lean]** (`Instance.lean`) `PLsub_one_of_prod_le`: if $\prod_{i<k}(n - i) \le f\prod_{i<k}(T - i)$ then PL$(f, 1)$ holds (no ordinary list has more than $f$ members, by the base bound). `concrete_K64`: `theoremR` applied on Mathlib's `GaloisField 2 64`, the domain being the whole field ($N = 64$), with $k = 2$, $T = 2^{64} - 1$, $f = 2$, $j_0 = 1$ and no hypothesis left. This is only a consistency check: the typeclass hypotheses, `IsSubspace`, the cardinality and `PLsub` are satisfiable together, so `theoremR` is not vacuous. It is not a parameter set of leanVM and it says nothing about PL in the windows.

## 2. How the Lean proofs differ from the hand proofs

The statements are those of the notes. Four proofs take another route, which makes them independent checks of the hand arguments.

1. **Proposition 3.3 without the fixed field.** The hand proof uses that the fixed field of $Y \mapsto Y + a'$ in $F(Y)$ is $F(q')$, coprimality of $p_l(q'), e_l(q')$ by a Bezout identity, and closure of $\{e : e(q') \mid u\}$ under lcm. The Lean proof never leaves $F[Y]$. With $u = u_0(q) + Yu_1(q)$ and $v = v_0(q) + Yv_1(q)$: $v(Y)u(Y + a) = v(Y + a)u(Y)$ iff $v_0u_1 = v_1u_0$ (`periodic_iff_parts`, from `comp_shift` and injectivity of $P \mapsto P(q)$). With $e = \gcd(u_0, u_1)$, $u_i = es_i$ and $As_0 + Bs_1 = 1$, the polynomial $Q = Av_0 + Bv_1$ satisfies $s_0Q = v_0$ and $s_1Q = v_1$, so $v = (s_0(q) + Ys_1(q))\,Q(q) = \varrho\,Q(q)$; the converse is a substitution. **[Lean]** `periodic_iff_exists`.
2. **Lemma 3.2 twice.** `pinned_bound` fixes the values of the members at $s$ points of the quotient and adds one point at each step; it needs only that two members that agree at $\kappa + 1$ points of the quotient are equal. `affine_bound` is the induction on the dimension of an affine space as in note 04, with the common zeros of the direction space bounded by the MDS property, proved from Lagrange interpolation and the rank theorem (`finrank_add_card_common_zeros_le`). Both give the product of the note for the whole code.
3. **Lemma 1.2 by a largest primitive sublist.** Section 3.1.
4. **The recursion unrolled through $a_j + 1$.** From $a_j \le f + G2^{N-j}a_{j+1}$ and $f + 1 \le G2^{N-j}$ one gets $a_j + 1 \le G2^{N-j}(a_{j+1} + 1)$, hence $a_0 + 1 \le G^{j_0}2^{Nj_0 - j_0(j_0-1)/2}(a_{j_0} + 1)$ with no geometric sum (`bnd_le`, `expo_eq`). The condition is $f + 1 \le 4G$ for $j_0 \le N - 1$; the referee's is $2f \le G2^{N-j_0+1}$.

In Lemma 5.2 the piecewise linear interpolation $\hat h_M$ is not defined: (3) is stated for every supporting line (`threewise_jensen`), and the closed form compares the line through $e = \lfloor Ma/n\rfloor$ and $e + 1$ with the cubic on $[e, e + 1]$ by the identity $n^2\bigl(nH(e) + (H(e+1) - H(e))(Ma - ne)\bigr) - Ma(Ma - n)(3Mn - 4n - Ma) = (Ma - ne)(n(e+1) - Ma)(n(3M - 4 - 2e) - Ma)$, $H = 6h_M$ (`threewise_closed_form_arith`).

## 3. Discrepancies and findings

**No statement of the notes under review is false, and no proof has a gap that the formalization had to repair.** The items below are what differs.

### 3.1 A sharper constant: $\binom f2$ in place of $\binom{f+1}{3}$

**[Lean; proved]** Let a list have the property that every sublist of more than $f$ members contains a bad triple, and let every pair have at most $W$ bad thirds. Take a largest sublist $S_0$ without bad triple. Then $\lvert S_0\rvert \le f$, and every member $c \notin S_0$ is a bad third of a pair of $S_0$: otherwise $S_0 \cup \{c\}$ would have no bad triple (a bad triple in it contains $c$, and badness does not depend on the order). So $L \le \lvert S_0\rvert + \binom{\lvert S_0\rvert}{2}W \le f + \binom f2 W$. This is `greedy_cover` and `one_step`. Note 39 Lemma 1.2 counts bad triples and gets $L \le 2 + \binom{f+1}{3}W$; the remark after it says that De Caen's bound would give "about $\binom f2$" and is not used. No Turán-type bound is needed.

Consequences, with the same hypothesis PL$(f, j_0)$: the recursion is $a_j \le f + \binom f2 2^{N-j}a_{j+1}$ and Theorem R holds with $\binom f2^{j_0}$ in place of $\binom{f+1}{3}^{j_0}$. **[Lean]** `abstract_descent_sharp`, `theoremR_sharp`; `bound_sharp_f7`: at $N = 25$, $f = 7$, $j_0 = 24$ the bound is at most $2^{433}$; `bound_sharp_f7_j20`: at most $2^{417}$ at $j_0 = 20$. **[checked, `scripts/47_numbers.py`]** The table of note 46 becomes:

| $f$ | $j_0 = 24$, notes | $j_0 = 24$, $\binom f2$ | best $j_0$, notes | best $j_0$, $\binom f2$ |
| --- | --- | --- | --- | --- |
| 7 | $2^{466.4}$ | $2^{432.4}$ | $2^{444.5}$ at 20 | $2^{416.2}$ at 20 |
| 16 | $2^{552.9}$ | $2^{492.8}$ | $2^{516.5}$ at 20 | $2^{466.5}$ at 20 |
| 133 | $2^{773.0}$ | $2^{641.4}$ | $2^{692.2}$ at 19 | $2^{588.1}$ at 19 |
| 134 | $2^{773.7}$ | $2^{641.9}$ | $2^{692.8}$ at 19 | $2^{588.5}$ at 19 |

The gain is $j_0\log_2\frac{f+1}{3}$ bits: 34 bits for $f = 7$ and 132 bits for $f = 134$ at $j_0 = 24$. Lemma 1.2 itself is not wrong and is proved as stated (`supersaturation`): from $L \le s + \binom s2 W$ with $s = \lvert S_0\rvert \ge 2$ and $W \ge 1$ one gets $L - 2 \le (\binom s3 + \binom s2)W = \binom{s+1}{3}W \le \binom{f+1}{3}W$. For lists only slightly longer than $f$ the count of the note can be better than the greedy one, so neither statement contains the other; for the recursion the greedy one is never worse.

### 3.2 Hypotheses of Theorem R that are not used

**[Lean]** `theoremR` assumes $k \ge 1$, $k \le T \le 2^N$, $f \ge 2$, $j_0 \le N - 1$. The conditions $k \ge 2$, $j_0 \ge 1$ and $j_0 \le J = \lceil\log_2 k\rceil$ of note 46 are not needed: beyond $J$ the degree bound is $0$ and the descent still applies. The conclusion can be taken one smaller, $\Lambda + 1 \le G^{j_0}2^{\dots}(B_{j_0} + 1)$ (`theoremR_gen`). `theorem35` (note 37 Theorem 3.5) needs $j_0 \le N$ and $k \le 2^{j_0}$ only, and its hypothesis only at the levels $j < j_0$ (the note asks it for $j \le J$).

### 3.3 Lemma 3.2

**[Lean]** `list_bound_nat`: the bound $L\prod_{i\le\kappa}(A - mi) \le \prod_{i\le\kappa}(n - mi)$ holds for any set of functions on the quotient two of which never agree at $\kappa + 1$ of its points, linear or not, and in this cross-multiplied form it needs no condition on $A$. The form with fractions (`base_bound`) assumes $A > m\kappa$ as the note does, and also $m\kappa \le n$, which the note leaves implicit. **[proved]** That is harmless for the note: there $m$ divides $n$, and for $m\kappa \ge n$ the factor $n - mi$ vanishes for $i = n/m$, so the product is $0$, which is right because $A > m\kappa \ge n$ leaves no member. For a general fibre size $m$ (the setting of `base_bound`) the product can be negative when $m\kappa > n$, and the extra hypothesis is needed.

### 3.4 Note 44 Lemma 5.2

**[Lean]** The hypothesis $\alpha \ge \varrho$ is redundant: $\mathcal A > 0$ gives $2\varrho < \alpha^2(3 - \alpha) \le 2\alpha$ for $\alpha \le 1$, because $2n^2 - 3an + a^2 = (2n - a)(n - a) \ge 0$. $M \ge 3$ is not needed (for $M \le 2$ the hypothesis on triples is empty and the conclusion still holds), the sets may have more than $a$ points, and in the first alternative the inequality is strict, $M < 1/(1 - \alpha)$.

### 3.5 Points that the formalization had to make explicit

None of these is an error; each is a line that a hand proof leaves to the reader and Lean does not. **[Lean]**

- $\deg\varrho \le \kappa$ in the slack inequality (section 1.2).
- The triple function is used in three roles (which member is the base point, which pair is "the pair"). The descent is applied to a bad triple with a prescribed pair, so badness must be invariant under the permutations of the three members: `Periodic.swap` and `Periodic.base_swap`, the two transpositions, for the cross-multiplied identity.
- A collinear third is periodic for every $a'$, and it lies in some $M_{a'}$ only if a nonzero direction exists, that is $j < N$ (`BadTriple.exists_dir`). This is item 1h of the referee's table.
- The levels are reached as $X \mapsto \ell^2 + a'\ell$; that these are the $L_U$, with $U' = U \cup (U + b)$, $L_U(b) = a'$, is `IsLevel.exists_subspace`. The hypothesis is asked of all subspaces $U \le D$ with $2^j$ elements and used only through this lemma.
- PL is applied to sublists (a sublist of a list of a level problem is a list of the same problem), which is why `PLsub` quantifies over all finite sets of members.

## 4. Modelling: is the Lean statement the intended one?

- **Domain.** `D : Finset F` with `IsSubspace D` ($0 \in D$, closed under addition) and `[CharP F 2]`. In characteristic two this is an $\mathbb{F}_2$-subspace; `D.card = 2 ^ N` is $\dim D = N$. No finiteness of $F$ is assumed.
- **Words.** `F → Option F`, read on `D` only; `none` is $\bot$. The original word of `theoremR` is `w : F → F`, without blanks.
- **Members and lists.** A list is any finite set `S` of polynomials each of which is a member. The conclusion bounds every such set, so it bounds the list.
- **Degrees.** `P.degree < k` in `theoremR` (so the zero polynomial is allowed); `P.natDegree ≤ κ` for the levels.
- **Periodicity.** Cross-multiplied, section 1.1. For $u \ne 0$ it is the equality $v/u = (v/u)(X + a)$ in $F(X)$; no statement in `RatFunc` is made.
- **Level polynomials.** `subPoly U` $= \prod_{u \in U}(X - u)$ for a finite set `U` with `IsSubspace U`, `U ⊆ D`, `U.card = 2 ^ j`. The values $L_U(D)$ are `D.image (fun x => (subPoly U).eval x)`.
- **Numbers.** $\binom{f+1}{3}$ is `(f + 1).choose 3`; the bound is in $\mathbb Q$; $B_{j_0}$ is a `Finset.sup'` over the degrees $0, \dots, \lfloor(k-1)/2^{j_0}\rfloor$.
- **Decidability.** The files use `open scoped Classical`; nothing is computed by the kernel except in `Numbers.lean`.

## 5. How it was checked

Nothing was installed or built on the Mac. All Lean runs were on `h4` (64 cores), inside `/data/whir_lean_scratch_47` only, with Lean 4.36.0 (commit `611c117b`), Lake 5.0.0 and Mathlib `v4.36.0` (revision `fc4f59e5`). `lean-toolchain` and `lake-manifest.json` are byte for byte those of `doc/deep_fold/lean` (SHA-256 `582a63f8...` and `bdd1190f...`), and `.lake/packages` was copied from `/data/whir_lean_scratch_final/final/lean/.lake/packages` (7.3 GB, Mathlib already built; nothing was downloaded). Lake did not rewrite the manifest.

1. **During development:** each file with `lake env lean -DwarningAsError=true -DautoImplicit=false -DrelaxedAutoImplicit=false`, then `lake build` of each module.
2. **Negative control:** a file `PeriodDescent/NegControl.lean` importing `PeriodDescent.TheoremR` with `theorem negative_control : (2 : Nat) + 2 = 5 := by sorry` was added to the copy on `h4`; `lake build PeriodDescent.NegControl` under the same `lakefile.toml` failed with `error: PeriodDescent/NegControl.lean:5:8: declaration uses sorry` and exit status 1. The file was then removed (it never existed in the repository). Log: `/data/whir_lean_scratch_47/neg-control.log`.
3. **Final build, the run to cite:** the repository copy synchronised to `/data/whir_lean_scratch_47/proj`, the build directory `.lake/build` removed, then `taskset -c 0-7 env LEAN_NUM_THREADS=8 nice -n 10 lake build` (2026-11-21 07:37 UTC): `Build completed successfully (18276 jobs).`, exit status 0, 18 seconds wall time, no line containing `error`. The only messages are Lake's advisory that the four files that import `Mathlib` directly (`Base.lean`, `Core.lean`, `Induction.lean`, `Johnson3.lean`) do so without the module system, which is not a Lean warning (`lakefile.toml` sets `warningAsError`). Twelve `.olean` files of `PeriodDescent/` were produced. Log: `/data/whir_lean_scratch_47/lake-build.log`.
4. **Axioms:** `PeriodDescent/Axioms.lean` has 140 checks `#guard_msgs in #print axioms`, one for every public theorem; the expected messages were produced by Lean and are compared at every build. 129 theorems depend on `propext`, `Classical.choice`, `Quot.sound`; 4 on `propext`, `Quot.sound`; 4 on `propext`; 3 on no axiom. None on `sorryAx` or anything else. The sources contain no `sorry`, `admit`, `axiom` or `native_decide`.
5. **Hashes:** the SHA-256 of each of the 18 files of `lean_descent/` (twelve files of `PeriodDescent/`, `PeriodDescent.lean`, `README.md`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `.gitignore`) is the same in the repository and in the copy built, after the build. The list is `/data/whir_lean_scratch_47/built.sha` (its own SHA-256 starts `6401a3a6`). First eight hex digits: `Affine.lean` fe6ca8e3, `Axioms.lean` 76ccdf59, `Base.lean` 24b8a8db, `Core.lean` 1d235856, `Induction.lean` 9beb9395, `Instance.lean` 8e662c0c, `Johnson3.lean` 20d92c62, `Level.lean` 4b3ab7d5, `Numbers.lean` a4e03b8c, `Step.lean` 1ae2c1c4, `Theorem35.lean` e89639cd, `TheoremR.lean` 2a0a583c, `PeriodDescent.lean` f3f37b4a, `README.md` 5be53d9d, `lakefile.toml` 38042272.

`Numbers.lean` sets `exponentiation.threshold 1000` for the theorems that evaluate powers of two beyond $2^{256}$; this lifts a guard of the elaborator and changes no axiom (item 4).

## 6. What remains

1. **Lemma 1.4 of note 39, Corollary 1.5 and Corollary R0 of note 46** (multi-valued words reduce to ordinary words with loss $2/\sigma$, at half the slack). Not formalized. It is an averaging over the choices of one point per coset; the Lean work would be a finite expectation over functions $D' \to D$ and Markov's inequality. Until then the machine-checked theorem is Theorem R with the hypothesis on multi-valued words, not Corollary R0.
2. **Note 37 Corollary 3.6** (bounded index): needs the iterated descent with $L_{\Pi^\ast}$ and the Gaussian binomial count of subspaces. `affine_ordinary_bound` is the counting step it ends with.
3. **Note 44 section 5 beyond Lemma 5.2:** Lemma 5.1 (a primitive triple under wP), Lemma 5.4 (the class of reachable problems, which needs $\hat h_M$ as a function), Theorem 5.5. With `threewise_johnson` and `abstract_descent` the remaining work for Theorem 5.5 is Lemma 5.4(2) and the bookkeeping of $(a, K, n_e)$ through `polyAgr_descent_eq`.
4. **Note 39 Proposition 1.6:** only (a) implies (b) (`supersaturation`); the other two implications are one line each and are not in the library.
5. **Numbers:** $j_0 = 18, 19, 21$ (they need $B_{18}, B_{19}, B_{21}$, products of up to 64 factors, feasible by the method of `baseB_20_le`), $f = 1000$, and the numbers of Corollary R0. They are **[checked]** by `scripts/47_numbers.py` and by note 46, not by Lean.
6. **Not attempted:** the interleaved case (the factor 2 of the brief is in `doc/deep_fold/lean`), any statement about leanVM's concrete tower, and of course PL and DP themselves.

## 7. Reproduction

- The project: `doc/whir_soundness_gap_notes/lean_descent/`, with `README.md`. On a build host: `cd doc/whir_soundness_gap_notes/lean_descent && lake exe cache get && lake build`.
- The copy that was built: `h4:/data/whir_lean_scratch_47/proj`, with `lake-build.log`, `neg-control.log` and `built.sha` one directory up.
- `scripts/47_numbers.py`: the bounds of Theorem R with exact rationals for $f = 7, 16, 133, 134$ and $j_0 = 16, \dots, 24$, with both constants. Python 3, no dependencies, under a second.

## References

Notes 04 (Theorem 1.2), 37 (section 3), 39 (section 1), 44 (Lemma 5.2) and 46 (section 1) of this directory; `doc/deep_fold/lean` for the conventions of the Lake project (nothing is imported from it). Mathlib `v4.36.0`. No other source was used.
