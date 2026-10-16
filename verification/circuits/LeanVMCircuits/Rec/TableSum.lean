module

public import LeanVMCircuits.Rec.AirBatch

@[expose] public section

/-!
The recursion leaf's table sumcheck over tables of different heights as a `Sumcheck.Inst`.

`Sumcheck.mvInst n P` is the honest instance of a polynomial `P` in `n` variables on the Boolean cube, binding variable `0` first: each round's polynomial is `P` summed over the cube in the variables after it, with no eq weight factored out, and its final value is `P` at the challenges. `mvInst_sum`: its sum is `P`'s sum over the cube (`cube`). `mvInst_ok`: it has degree `d` when `P` has degree at most `d` in each variable. `mvInst_final` and `mvInst_weight`: its final value along `r` is `P(r)` and no round factors out an eq weight.

`constraints::verify` runs `n` rounds, `n` the tallest table's `τ`, binding the variables from the highest down: round `j` binds variable `m = n - 1 - j` (`chi[m]`), a table of `2^τ` rows is active in the rounds with `τ > m`, where its weight takes `eq(ζ_m, r) = 1 + ζ_m + r`, and sits out the others, where its weight takes `r`. So table `T` is the polynomial `cornerEq ζ τ_T · S_T(mle_T)` in the cube's variables: `eq(ζ_j, x_j)` on its own variables `j < τ_T`, `x_j` on those it sits out, and its summand `S_T` (`summandPoly`, `TableSummand::batch`: its push form, `ξ` times its pull form, and its identities, identity `j` of `allIds` at `ξ^(2 + j)`) on its columns' multilinear extensions (`mle`). The table sits at the corner where the variables it sits out are one. `tableInst` is `mvInst` of the sum of the owned tables' polynomials with the variables reversed, so its challenge `r_j` is Rust's `chi[n - 1 - j]` (`chi`).

`tableInst_sum`: where every owned table's `τ` is at most `n`, the instance's sum is `AirLink.tableSum`, the batch's honest sum, with bus parts the forms' sums over the rows weighted by `eq(ζ[..τ_T], z)` (`formSums`); `corner_sum` is the step that makes the heights differ: summing over the cube a table's polynomial gives its own rows' sum, the variables it sits out summing to their corner. `tableInst_ok`: it has degree `d` for `d ≥ 3`. `tableInst_final`: its final value is `Σ_T weight_T · S_T` at the columns' extensions at `chi`, `weight_T` the verifier's fold (`foldWeight`, `foldWeight_eq`). `tableInst_weight`: no round factors out an eq weight, as `v.read_round(4, claim, None)` reads them.
-/

namespace LeanVMCircuits.Rec.Sumcheck

open MvPolynomial Finset Classical

variable {F : Type} [Field F]

/-- The Boolean cube `{0, 1}^n`. -/
noncomputable def cube (n : ℕ) : Finset (Fin n → F) := Fintype.piFinset fun _ => {0, 1}

theorem sum_cube_zero {M : Type} [AddCommMonoid M] (f : (Fin 0 → F) → M) :
    ∑ x ∈ cube 0, f x = f Fin.elim0 := by
  have h : (cube 0 : Finset (Fin 0 → F)) = {Fin.elim0} := by
    ext x
    simp only [cube, Fintype.mem_piFinset, mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ i => i.elim0⟩
  rw [h, sum_singleton]

/-- The cube in `n + 1` variables by its first variable. -/
theorem sum_cube_succ {M : Type} [AddCommMonoid M] (n : ℕ) (f : (Fin (n + 1) → F) → M) :
    ∑ y ∈ cube (n + 1), f y = ∑ x ∈ cube n, (f (Fin.cons 0 x) + f (Fin.cons 1 x)) := by
  have h := Finset.filter_piFinset_eq_map_consEquiv (fun _ : Fin (n + 1) => ({0, 1} : Finset F))
    (fun _ => True)
  simp only [filter_true] at h
  rw [cube, h, sum_map, sum_product, sum_pair zero_ne_one, ← sum_add_distrib]
  rfl

/-- The honest instance of `P` on the cube, binding variable `0` first: each round's polynomial the sum over the cube
of the variables after it, no eq weight factored out. -/
noncomputable def mvInst : (n : ℕ) → MvPolynomial (Fin n) F → Inst F n
  | 0, P => .leaf (eval Fin.elim0 P)
  | n + 1, P => .node none (∑ x ∈ cube n, (finSuccEquiv F n P).map (eval x))
      fun r => mvInst n (Polynomial.eval (C r) (finSuccEquiv F n P))

/-- Binding the first variable to `r`. -/
theorem eval_bind {n : ℕ} (P : MvPolynomial (Fin (n + 1)) F) (r : F) (x : Fin n → F) :
    eval x (Polynomial.eval (C r) (finSuccEquiv F n P)) = eval (Fin.cons r x) P := by
  rw [eval_eq_eval_mv_eval', Polynomial.eval_map, ← Polynomial.eval₂_at_apply (eval x) (C r), eval_C]

theorem round_eval {n : ℕ} (P : MvPolynomial (Fin (n + 1)) F) (r : F) :
    (∑ x ∈ cube n, (finSuccEquiv F n P).map (eval x)).eval r = ∑ x ∈ cube n, eval (Fin.cons r x) P := by
  rw [Polynomial.eval_finsetSum]
  refine sum_congr rfl fun x _ => ?_
  rw [eval_eq_eval_mv_eval']

/-- The instance's sum is `P`'s sum over the cube. -/
theorem mvInst_sum : ∀ {n : ℕ} (P : MvPolynomial (Fin n) F), (mvInst n P).sum = ∑ x ∈ cube n, eval x P
  | 0, P => by simp only [mvInst, Inst.sum, sum_cube_zero]
  | n + 1, P => by
    simp only [mvInst, Inst.sum, lin]
    rw [round_eval, round_eval, sum_cube_succ, sum_add_distrib]

/-- Binding the first variable does not raise another's degree. -/
theorem degreeOf_bind {n : ℕ} (P : MvPolynomial (Fin (n + 1)) F) (r : F) (i : Fin n) :
    degreeOf i (Polynomial.eval (C r) (finSuccEquiv F n P)) ≤ degreeOf i.succ P := by
  rw [Polynomial.eval_eq_sum_range]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun k _ => ?_)
  rw [← C_pow]
  exact (degreeOf_mul_C_le _ _ _).trans (degreeOf_coeff_finSuccEquiv P i k)

/-- The instance has degree `d` when `P` has degree at most `d` in each variable. -/
theorem mvInst_ok (d : ℕ) : ∀ {n : ℕ} (P : MvPolynomial (Fin n) F), (∀ i, degreeOf i P ≤ d) → (mvInst n P).ok d
  | 0, _, _ => trivial
  | n + 1, P, h => by
    refine ⟨?_, fun r => ⟨?_, mvInst_ok d _ fun i => (degreeOf_bind P r i).trans (h i.succ)⟩⟩
    · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
      exact (Polynomial.natDegree_map_le).trans ((natDegree_finSuccEquiv P).le.trans (h 0))
    · rw [mvInst_sum, round_eval]
      exact sum_congr rfl fun x _ => eval_bind P r x

/-- The instance's final value along `r` is `P(r)`. -/
theorem mvInst_final : ∀ {n : ℕ} (P : MvPolynomial (Fin n) F) (r : Fin n → F), (mvInst n P).final r = eval r P
  | 0, P, r => by simp only [mvInst, Inst.final]; rw [Subsingleton.elim r Fin.elim0]
  | n + 1, P, r => by
    simp only [mvInst, Inst.final]
    rw [mvInst_final, eval_bind, Fin.cons_self_tail]

/-- No round factors out an eq weight. -/
theorem mvInst_weight : ∀ {n : ℕ} (P : MvPolynomial (Fin n) F) (r : Fin n → F) (i : Fin n),
    (mvInst n P).weight r i = none
  | 0, _, _, i => i.elim0
  | n + 1, P, r, i => by
    simp only [mvInst, Inst.weight]
    refine Fin.cases rfl (fun j => ?_) i
    simp only [Fin.cases_succ]
    exact mvInst_weight _ _ _

/-- The cube is closed under reversing the variables. -/
theorem sum_cube_rev {M : Type} [AddCommMonoid M] (n : ℕ) (f : (Fin n → F) → M) :
    ∑ x ∈ cube n, f (x ∘ Fin.rev) = ∑ x ∈ cube n, f x := by
  refine sum_nbij' (fun x => x ∘ Fin.rev) (fun x => x ∘ Fin.rev) ?_ ?_ ?_ ?_ fun _ _ => rfl
  all_goals intro x hx
  · simp only [cube, Fintype.mem_piFinset, Function.comp_apply] at hx ⊢
    exact fun i => hx _
  · simp only [cube, Fintype.mem_piFinset, Function.comp_apply] at hx ⊢
    exact fun i => hx _
  · funext i; simp
  · funext i; simp

end LeanVMCircuits.Rec.Sumcheck

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec Model MvPolynomial Finset Classical Sumcheck

/-! Summands: quadratic forms in a row's columns. -/

/-- A quadratic form in a row's columns, with `E` coefficients: a constant, linear terms and products. A table's bus
forms and identities are such forms. -/
structure Quad where
  const : E := 0
  lin : List (ℕ × E) := []
  prods : List (ℕ × ℕ × E) := []

namespace Quad

/-- Its value at columns `col`. -/
noncomputable def eval (q : Quad) (col : ℕ → E) : E :=
  q.const + (q.lin.map fun t => t.2 * col t.1).sum + (q.prods.map fun t => t.2.2 * (col t.1 * col t.2.1)).sum

/-- It as a polynomial in column polynomials `col`. -/
noncomputable def poly {n : ℕ} (q : Quad) (col : ℕ → MvPolynomial (Fin n) E) : MvPolynomial (Fin n) E :=
  C q.const + (q.lin.map fun t => C t.2 * col t.1).sum + (q.prods.map fun t => C t.2.2 * (col t.1 * col t.2.1)).sum

theorem eval_poly {n : ℕ} (q : Quad) (col : ℕ → MvPolynomial (Fin n) E) (x : Fin n → E) :
    MvPolynomial.eval x (q.poly col) = q.eval fun c => MvPolynomial.eval x (col c) := by
  simp only [poly, eval, map_add, map_list_sum, List.map_map, Function.comp_def, map_mul, eval_C]

theorem degreeOf_list_sum {n : ℕ} (i : Fin n) (d : ℕ) :
    ∀ l : List (MvPolynomial (Fin n) E), (∀ p ∈ l, degreeOf i p ≤ d) → degreeOf i l.sum ≤ d
  | [], _ => by simp
  | p :: l, h => by
    rw [List.sum_cons]
    exact (degreeOf_add_le _ _ _).trans (max_le (h p (by simp))
      (degreeOf_list_sum i d l fun q hq => h q (by simp [hq])))

/-- On column polynomials of degree at most one in a variable, the form has degree at most two in it. -/
theorem degreeOf_poly {n : ℕ} (q : Quad) (col : ℕ → MvPolynomial (Fin n) E) (i : Fin n)
    (h : ∀ c, degreeOf i (col c) ≤ 1) : degreeOf i (q.poly col) ≤ 2 := by
  unfold poly
  refine (degreeOf_add_le _ _ _).trans (max_le ((degreeOf_add_le _ _ _).trans (max_le ?_ ?_)) ?_)
  · rw [degreeOf_C]; omega
  · refine degreeOf_list_sum i 2 _ fun p hp => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hp
    refine (degreeOf_mul_le _ _ _).trans ?_
    rw [degreeOf_C]
    have := h t.1
    omega
  · refine degreeOf_list_sum i 2 _ fun p hp => ?_
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hp
    refine (degreeOf_mul_le _ _ _).trans ?_
    rw [degreeOf_C, zero_add]
    refine (degreeOf_mul_le _ _ _).trans ?_
    have := h t.1
    have := h t.2.1
    omega

end Quad

/-- An identity as a form, its word coefficients embedded. -/
noncomputable def ofId (id : Identity) : Quad where
  lin := id.linear.map fun t => (t.1, emb (ofWord t.2))
  prods := id.prods.map fun t => (t.1, t.2.1, emb (ofWord t.2.2))

theorem ofId_eval (id : Identity) (row : ℕ → K) : (ofId id).eval (fun c => emb (row c)) = emb (id.eval row) := by
  simp only [Quad.eval, ofId, Identity.eval, List.map_map, Function.comp_def, zero_add, emb, map_add, map_list_sum,
    map_mul]

/-! The table sumcheck's polynomial. -/

/-- The owned tables, the table sumcheck's airs (`RecLayout::airs`). -/
def owned : Finset Table := {.emul, .exk, .hash, .split, .cast}

theorem mem_owned_of_ids {T : Table} {id : Identity} (h : id ∈ ids T) : T ∈ owned := by
  cases T <;> simp_all [owned, ids]

/-- A table's weight polynomial in the `n`-variable cube: `eq(ζ_j, x_j) = 1 + ζ_j + x_j` on its own variables
`j < τ`, and `x_j` on those it sits out. -/
noncomputable def cornerEq {n : ℕ} (ζ : Fin n → E) (τ : ℕ) : MvPolynomial (Fin n) E :=
  ∏ j : Fin n, if (j : ℕ) < τ then 1 + C (ζ j) + X j else X j

/-- Column `c` of table `T`'s multilinear extension over its own variables. -/
noncomputable def mle (n : ℕ) (w : Witness) (T : Table) (c : ℕ) : MvPolynomial (Fin n) E :=
  ∑ z ∈ range (2 ^ tauOf w T), eqPoly n (tauOf w T) z * C (emb (w.cols T z c))

/-- Table `T`'s summand at `ξ` on columns `col` (`TableSummand::batch`): its push form, `ξ` times its pull form, and
each identity `j` of `allIds` it owns at `ξ^(2 + j)`. -/
noncomputable def summandAt (forms : Fin 2 → Table → Quad) (ξ : E) (T : Table) (col : ℕ → E) : E :=
  (forms 0 T).eval col + ξ * (forms 1 T).eval col +
    ∑ j : Fin allIds.length with allIds[j].1 = T, ξ ^ (2 + (j : ℕ)) * (ofId allIds[j].2).eval col

/-- The summand as a polynomial in column polynomials. -/
noncomputable def summandPoly {n : ℕ} (forms : Fin 2 → Table → Quad) (ξ : E) (T : Table)
    (col : ℕ → MvPolynomial (Fin n) E) : MvPolynomial (Fin n) E :=
  (forms 0 T).poly col + C ξ * (forms 1 T).poly col +
    ∑ j : Fin allIds.length with allIds[j].1 = T, C (ξ ^ (2 + (j : ℕ))) * (ofId allIds[j].2).poly col

theorem eval_summandPoly {n : ℕ} (forms : Fin 2 → Table → Quad) (ξ : E) (T : Table)
    (col : ℕ → MvPolynomial (Fin n) E) (x : Fin n → E) :
    MvPolynomial.eval x (summandPoly forms ξ T col) = summandAt forms ξ T fun c => MvPolynomial.eval x (col c) := by
  simp only [summandPoly, summandAt, map_add, map_mul, map_sum, eval_C, Quad.eval_poly]

/-- The table sumcheck's polynomial: each owned table's weight polynomial times its summand on its columns'
extensions. -/
noncomputable def tablePoly (n : ℕ) (w : Witness) (ζ : Fin n → E) (forms : Fin 2 → Table → Quad) (ξ : E) :
    MvPolynomial (Fin n) E :=
  ∑ T ∈ owned, cornerEq ζ (tauOf w T) * summandPoly forms ξ T (mle n w T)

/-- The honest instance of the table sumcheck: `tablePoly` with its variables reversed, so round `j` binds Rust's
variable `n - 1 - j`. -/
noncomputable def tableInst (n : ℕ) (w : Witness) (ζ : Fin n → E) (forms : Fin 2 → Table → Quad) (ξ : E) :
    Inst E n :=
  mvInst n (rename Fin.rev (tablePoly n w ζ forms ξ))

/-- The point `chi` of Rust's variables the challenges `r` make: round `j`'s challenge at `chi[n - 1 - j]`. -/
def chi {n : ℕ} (r : Fin n → E) : Fin n → E := r ∘ Fin.rev

/-! Degree. -/

theorem degreeOf_X_le {n : ℕ} (i j : Fin n) : degreeOf i (X j : MvPolynomial (Fin n) E) ≤ if i = j then 1 else 0 := by
  rw [degreeOf_X]

theorem degreeOf_factor_le {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) E) (hp : degreeOf i p = 0) :
    degreeOf i (p + X j) ≤ if i = j then 1 else 0 :=
  (degreeOf_add_le _ _ _).trans (max_le (by rw [hp]; exact Nat.zero_le _) (degreeOf_X_le i j))

/-- A product of factors, factor `j` of degree at most one in variable `j` and zero in the others. -/
theorem degreeOf_prod_factors {n : ℕ} (i : Fin n) (f : Fin n → MvPolynomial (Fin n) E)
    (h : ∀ j, degreeOf i (f j) ≤ if i = j then 1 else 0) : degreeOf i (∏ j, f j) ≤ 1 := by
  refine (degreeOf_prod_le _ _ _).trans ?_
  calc ∑ j, degreeOf i (f j) ≤ ∑ j : Fin n, (if i = j then 1 else 0) := sum_le_sum fun j _ => h j
    _ = 1 := by simp

theorem degreeOf_one_add_C {n : ℕ} (i : Fin n) (a : E) : degreeOf i ((1 : MvPolynomial (Fin n) E) + C a) = 0 := by
  rw [← C_1, ← C_add, degreeOf_C]

theorem degreeOf_cornerEq {n : ℕ} (ζ : Fin n → E) (τ : ℕ) (i : Fin n) : degreeOf i (cornerEq ζ τ) ≤ 1 := by
  refine degreeOf_prod_factors i _ fun j => ?_
  by_cases h : (j : ℕ) < τ
  · rw [if_pos h]; exact degreeOf_factor_le i j _ (degreeOf_one_add_C i _)
  · rw [if_neg h]; exact degreeOf_X_le i j

theorem degreeOf_eqPoly {n τ z : ℕ} (i : Fin n) : degreeOf i (eqPoly n τ z : MvPolynomial (Fin n) E) ≤ 1 := by
  refine degreeOf_prod_factors i _ fun j => ?_
  by_cases h : (j : ℕ) < τ
  · rw [if_pos h]
    by_cases hb : z.testBit j = true
    · rw [if_pos hb]; exact degreeOf_X_le i j
    · rw [if_neg hb]; exact degreeOf_factor_le i j _ (by rw [← C_1, degreeOf_C])
  · rw [if_neg h, ← C_1, degreeOf_C]; exact Nat.zero_le _

theorem degreeOf_mle (n : ℕ) (w : Witness) (T : Table) (c : ℕ) (i : Fin n) : degreeOf i (mle n w T c) ≤ 1 := by
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun z _ => ?_)
  exact (degreeOf_mul_C_le _ _ _).trans (degreeOf_eqPoly i)

theorem degreeOf_tablePoly (n : ℕ) (w : Witness) (ζ : Fin n → E) (forms : Fin 2 → Table → Quad) (ξ : E)
    (i : Fin n) : degreeOf i (tablePoly n w ζ forms ξ) ≤ 3 := by
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun T _ => ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  have h1 := degreeOf_cornerEq ζ (tauOf w T) i
  have hcol := fun c => degreeOf_mle n w T c i
  have h2 : degreeOf i (summandPoly forms ξ T (mle n w T)) ≤ 2 := by
    unfold summandPoly
    refine (degreeOf_add_le _ _ _).trans (max_le ((degreeOf_add_le _ _ _).trans (max_le ?_ ?_)) ?_)
    · exact Quad.degreeOf_poly _ _ i hcol
    · refine (degreeOf_mul_le _ _ _).trans ?_
      rw [degreeOf_C, zero_add]
      exact Quad.degreeOf_poly _ _ i hcol
    · refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun j _ => ?_)
      refine (degreeOf_mul_le _ _ _).trans ?_
      rw [degreeOf_C, zero_add]
      exact Quad.degreeOf_poly _ _ i hcol
  omega

/-- The instance has degree `d` for every `d ≥ 3`. -/
theorem tableInst_ok (n : ℕ) (w : Witness) (ζ : Fin n → E) (forms : Fin 2 → Table → Quad) (ξ : E) {d : ℕ}
    (hd : 3 ≤ d) : (tableInst n w ζ forms ξ).ok d := by
  refine mvInst_ok d _ fun i => ?_
  have h := degreeOf_rename_of_injective (p := tablePoly n w ζ forms ξ) Fin.rev_injective (Fin.rev i)
  rw [Fin.rev_rev] at h
  rw [h]
  exact (degreeOf_tablePoly n w ζ forms ξ _).trans hd

/-- No round factors out an eq weight. -/
theorem tableInst_weight (n : ℕ) (w : Witness) (ζ : Fin n → E) (forms : Fin 2 → Table → Quad) (ξ : E)
    (r : Fin n → E) (i : Fin n) : (tableInst n w ζ forms ξ).weight r i = none :=
  mvInst_weight _ r i

/-! The sum: each table's rows, the variables it sits out at their corner. -/

/-- The cube is the rows' points `bitPoint n Z`, `Z < 2^n`. -/
theorem bitPoint_injOn (n : ℕ) : Set.InjOn (bitPoint n) (range (2 ^ n) : Set ℕ) := by
  intro a ha b hb h
  simp only [coe_range, Set.mem_Iio] at ha hb
  refine Nat.eq_of_testBit_eq fun j => ?_
  by_cases hj : j < n
  · have := congrFun h ⟨j, hj⟩
    simp only [bitPoint] at this
    by_cases h1 : a.testBit j <;> by_cases h2 : b.testBit j <;> simp_all
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem cube_eq_image (n : ℕ) : (cube n : Finset (Fin n → E)) = (range (2 ^ n)).image (bitPoint n) := by
  symm
  refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
  · obtain ⟨z, -, rfl⟩ := mem_image.mp hx
    simp only [cube, Fintype.mem_piFinset, bitPoint]
    intro j
    split_ifs <;> simp
  · rw [card_image_of_injOn (bitPoint_injOn n), card_range, cube, Fintype.card_piFinset]
    simp [card_pair (zero_ne_one (α := E))]

theorem sum_cube_bits {M : Type} [AddCommMonoid M] (n : ℕ) (f : (Fin n → E) → M) :
    ∑ x ∈ cube n, f x = ∑ Z ∈ range (2 ^ n), f (bitPoint n Z) := by
  rw [cube_eq_image, sum_image (bitPoint_injOn n)]

/-- Summing over the rows of `2^n` a function of the low `τ` bits that the bits from `τ` up all gate: the low rows'
sum. -/
theorem corner_sum {τ : ℕ} (g : ℕ → E) : ∀ n, τ ≤ n →
    ∑ Z ∈ range (2 ^ n), (∏ j : Fin n, if τ ≤ (j : ℕ) then bitPoint n Z j else 1) * g (Z % 2 ^ τ) =
      ∑ z ∈ range (2 ^ τ), g z := by
  intro n hn
  induction n with
  | zero =>
    have : τ = 0 := by omega
    subst this
    simp
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hn with h | h
    · subst h
      refine sum_congr rfl fun Z hZ => ?_
      rw [Finset.prod_eq_one fun j _ => if_neg (by omega), one_mul, Nat.mod_eq_of_lt (mem_range.mp hZ)]
    · have hn' : τ ≤ n := by omega
      rw [pow_succ, mul_two, sum_range_add]
      have hlow : ∀ Z ∈ range (2 ^ n), (∏ j : Fin (n + 1), if τ ≤ (j : ℕ) then bitPoint (n + 1) Z j else 1) = 0 := by
        intro Z hZ
        refine Finset.prod_eq_zero (i := Fin.last n) (mem_univ _) ?_
        simp only [Fin.val_last, if_pos hn', bitPoint, Nat.testBit_lt_two_pow (mem_range.mp hZ)]
        simp
      rw [sum_congr rfl fun Z hZ => by rw [hlow Z hZ, zero_mul], sum_const_zero, zero_add, ← ih hn']
      refine sum_congr rfl fun Z hZ => ?_
      have hZ' := mem_range.mp hZ
      congr 1
      · rw [Fin.prod_univ_castSucc]
        simp only [Fin.val_last, if_pos hn', bitPoint, Fin.val_castSucc, Nat.testBit_two_pow_add_eq,
          Nat.testBit_lt_two_pow hZ', Bool.not_false, ↓reduceIte, mul_one]
        refine prod_congr rfl fun j _ => ?_
        simp only [Nat.testBit_two_pow_add_gt j.isLt]
      · congr 1
        rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 hn'), zero_add, Nat.mod_mod]

theorem rowEq_mod {n : ℕ} (ζ : Fin n → E) (τ Z : ℕ) : rowEq ζ τ (Z % 2 ^ τ) = rowEq ζ τ Z := by
  unfold rowEq
  refine prod_congr rfl fun j _ => ?_
  by_cases h : (j : ℕ) < τ
  · simp [h, Nat.testBit_mod_two_pow]
  · simp [h]

theorem eval_eqPoly_mod {n τ z Z : ℕ} (hτ : τ ≤ n) (hz : z < 2 ^ τ) :
    MvPolynomial.eval (bitPoint n Z) (eqPoly n τ z : MvPolynomial (Fin n) E) =
      if z = Z % 2 ^ τ then 1 else 0 := by
  rw [← eval_eqPoly hτ hz (Nat.mod_lt _ (by positivity))]
  simp only [eqPoly, map_prod]
  refine prod_congr rfl fun j _ => ?_
  by_cases h : (j : ℕ) < τ
  · by_cases hb : z.testBit j <;> simp [h, hb, bitPoint, Nat.testBit_mod_two_pow]
  · simp [h]

theorem eval_mle {n : ℕ} {w : Witness} {T : Table} (hτ : tauOf w T ≤ n) (Z c : ℕ) :
    MvPolynomial.eval (bitPoint n Z) (mle n w T c) = emb (w.cols T (Z % 2 ^ tauOf w T) c) := by
  simp only [mle, map_sum, map_mul, eval_C]
  rw [sum_congr rfl fun z hz => by rw [eval_eqPoly_mod hτ (mem_range.mp hz)]]
  simp [Nat.mod_lt _ (show 0 < 2 ^ tauOf w T by positivity)]

theorem eval_cornerEq {n : ℕ} (ζ : Fin n → E) (τ Z : ℕ) :
    MvPolynomial.eval (bitPoint n Z) (cornerEq ζ τ) =
      (∏ j : Fin n, if τ ≤ (j : ℕ) then bitPoint n Z j else 1) * rowEq ζ τ (Z % 2 ^ τ) := by
  rw [rowEq_mod]
  simp only [cornerEq, rowEq, map_prod, ← prod_mul_distrib]
  refine prod_congr rfl fun j _ => ?_
  by_cases h : (j : ℕ) < τ
  · simp only [h, if_true, show ¬ τ ≤ (j : ℕ) by omega, if_false, one_mul, map_add, map_one, eval_C, eval_X,
      bitPoint]
    split_ifs
    · rw [add_assoc, add_comm (ζ j), ← add_assoc, one_add_one, zero_add]
    · rw [add_zero]
  · simp only [h, if_false, show τ ≤ (j : ℕ) by omega, if_true, mul_one, eval_X]

/-- One table's polynomial summed over the cube: its rows' sum weighted by `eq(ζ[..τ], z)`. -/
theorem table_cube_sum {n : ℕ} (w : Witness) (ζ : Fin n → E) (forms : Fin 2 → Table → Quad) (ξ : E) {T : Table}
    (hτ : tauOf w T ≤ n) :
    ∑ x ∈ cube n, MvPolynomial.eval x (cornerEq ζ (tauOf w T) * summandPoly forms ξ T (mle n w T)) =
      ∑ z ∈ range (2 ^ tauOf w T), rowEq ζ (tauOf w T) z * summandAt forms ξ T fun c => emb (w.cols T z c) := by
  rw [sum_cube_bits, ← corner_sum (fun z => rowEq ζ (tauOf w T) z * summandAt forms ξ T fun c => emb (w.cols T z c))
    n hτ]
  refine sum_congr rfl fun Z _ => ?_
  rw [map_mul, eval_cornerEq, eval_summandPoly]
  simp only [eval_mle hτ]
  ring

theorem allIds_mem_ids (j : Fin allIds.length) : allIds[j].2 ∈ ids allIds[j].1 := by
  have h := List.getElem_mem (l := allIds) j.isLt
  simp only [allIds, List.mem_flatMap, List.mem_map] at h
  obtain ⟨T, -, id, hid, he⟩ := h
  have he' : allIds[j] = (T, id) := he.symm
  rw [he']
  exact hid

/-- The bus forms' honest sums: each side's forms over every owned table's rows, weighted by `eq(ζ[..τ_T], z)`. -/
noncomputable def formSums {n : ℕ} (w : Witness) (ζ : Fin n → E) (forms : Fin 2 → Table → Quad) : Fin 2 → E :=
  fun i => ∑ T ∈ owned, ∑ z ∈ range (2 ^ tauOf w T), rowEq ζ (tauOf w T) z * (forms i T).eval fun c => emb (w.cols T z c)

/-- The instance's sum is the batch's honest sum `tableSum` at the forms' honest sums: the table sumcheck over tables
of different heights sums each table's own rows. Only the owned tables' `τ` need be at most `n`: the public table is
in no summand. -/
theorem tableInst_sum {n : ℕ} (w : Witness) (ζ : Fin n → E) (forms : Fin 2 → Table → Quad) (ξ : E)
    (htau : ∀ T ∈ owned, tauOf w T ≤ n) : (tableInst n w ζ forms ξ).sum = tableSum w ζ (formSums w ζ forms) ξ := by
  rw [tableInst, mvInst_sum]
  simp only [eval_rename]
  rw [sum_cube_rev n (fun x => MvPolynomial.eval x (tablePoly n w ζ forms ξ))]
  simp only [tablePoly, map_sum]
  rw [sum_comm, sum_congr rfl fun T hT => table_cube_sum w ζ forms ξ (htau T hT)]
  simp only [summandAt, mul_add, sum_add_distrib, mul_sum, tableSum, formSums]
  congr 1
  · congr 1
    all_goals exact sum_congr rfl fun T _ => sum_congr rfl fun z _ => by ring
  · rw [← sum_fiberwise_of_maps_to (s := univ) (t := owned) (g := fun j : Fin allIds.length => allIds[j].1)
      (fun j _ => mem_owned_of_ids (allIds_mem_ids j))]
    refine sum_congr rfl fun T _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun j hj => ?_
    have hT : allIds[j].1 = T := (mem_filter.mp hj).2
    rw [coef, mul_sum, ← hT]
    refine sum_congr rfl fun z _ => ?_
    rw [ofId_eval]
    ring

/-! The final value: the verifier's weights. -/

/-- A table's weight as `constraints::verify` folds it: from one, round `j` (variable `m = n - 1 - j`) multiplies by
`1 + ζ_m + r_j` where the table is active (`τ > m`) and by `r_j` where it sits out. -/
noncomputable def foldWeight {n : ℕ} (ζ : Fin n → E) (τ : ℕ) (r : Fin n → E) : E :=
  (List.finRange n).foldl (fun acc j => if (Fin.rev j : ℕ) < τ then acc * (1 + ζ (Fin.rev j) + r j) else acc * r j) 1

theorem foldl_mul_eq {n : ℕ} (f : Fin n → E) (l : List (Fin n)) (a : E) :
    l.foldl (fun acc j => acc * f j) a = a * (l.map f).prod := by
  induction l generalizing a with
  | nil => simp
  | cons j l ih => rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

/-- The verifier's fold is the weight polynomial at `chi`. -/
theorem foldWeight_eq {n : ℕ} (ζ : Fin n → E) (τ : ℕ) (r : Fin n → E) :
    foldWeight ζ τ r = MvPolynomial.eval (chi r) (cornerEq ζ τ) := by
  have hf : foldWeight ζ τ r = (List.finRange n).foldl
      (fun acc j => acc * (if (Fin.rev j : ℕ) < τ then 1 + ζ (Fin.rev j) + r j else r j)) 1 := by
    unfold foldWeight
    congr 1
    funext acc j
    split_ifs <;> rfl
  rw [hf, foldl_mul_eq, one_mul, ← Fin.prod_univ_def]
  simp only [cornerEq, map_prod, chi]
  refine Fintype.prod_equiv Fin.revPerm _ _ fun j => ?_
  simp only [Fin.revPerm_apply]
  split_ifs <;> simp only [map_add, map_one, eval_C, eval_X, Function.comp_apply, Fin.rev_rev]

/-- The instance's final value along `r`: each owned table's weight (`foldWeight`) times its summand at its columns'
extensions at `chi`, the values the verifier's column claims name. -/
theorem tableInst_final (n : ℕ) (w : Witness) (ζ : Fin n → E) (forms : Fin 2 → Table → Quad) (ξ : E)
    (r : Fin n → E) :
    (tableInst n w ζ forms ξ).final r =
      ∑ T ∈ owned, foldWeight ζ (tauOf w T) r * summandAt forms ξ T fun c => MvPolynomial.eval (chi r) (mle n w T c) := by
  rw [tableInst, mvInst_final, eval_rename]
  simp only [tablePoly, map_sum, map_mul, eval_summandPoly, foldWeight_eq]
  rfl

end LeanVMCircuits.Rec.AirLink

namespace LeanVMCircuits.Rec.AirLink

open LeanVMCircuits.Rec LeanVMCircuits.Blake2s Model Finset Edges Classical

/-! The committed witness at a layout. -/

/-- The committed witness at a layout's heights `2^τ_T` (`RecLayout`): the owned tables' columns the committed ones,
and the public table's four value columns the verifier's own (`FixedColumns::public_values`, `TableArgument::of`),
each public row's constant or statement word. -/
noncomputable def committedAt (s : State) (st : ℕ → Fin 4 → K) (taus : Table → ℕ) (cols : Table → ℕ → ℕ → K) :
    Witness where
  height T := 2 ^ taus T
  cols T z c := if T = .pub then (if h : z < s.pub.size ∧ c < 4 then srcVal st s.pub[z].2 ⟨c, h.2⟩ else 0)
    else cols T z c

/-- The layout's heights hold the circuit's rows, each `τ` within `MAX_TAU = 32` (`RecLayout::from_taus`). -/
def LayoutFits (s : State) (taus : Table → ℕ) : Prop := ∀ T, (rowsOf s T).size ≤ 2 ^ taus T ∧ taus T ≤ 32

theorem committedAt_fits {s : State} {st : ℕ → Fin 4 → K} {taus : Table → ℕ} {cols : Table → ℕ → ℕ → K}
    (h : LayoutFits s taus) (T : Table) :
    (rowsOf s T).size ≤ (committedAt s st taus cols).height T ∧ (committedAt s st taus cols).height T ≤ 2 ^ 32 :=
  ⟨(h T).1, Nat.pow_le_pow_right (by norm_num) (h T).2⟩

/-- The public columns are the verifier's at the statement. -/
theorem committedAt_pub (s : State) (st : ℕ → Fin 4 → K) (taus : Table → ℕ) (cols : Table → ℕ → ℕ → K) {z : ℕ}
    (hz : z < s.pub.size) (i : Fin 4) : (committedAt s st taus cols).cols .pub z i = srcVal st s.pub[z].2 i := by
  simp [committedAt, hz]

theorem tauOf_committedAt (s : State) (st : ℕ → Fin 4 → K) (taus : Table → ℕ) (cols : Table → ℕ → ℕ → K)
    (T : Table) : tauOf (committedAt s st taus cols) T = taus T :=
  Nat.clog_pow 2 _ (by norm_num)

/-- Non-vacuity of `LayoutFits`: every table at `τ = 32` fits a circuit with at most `2^32` rows per table. -/
example (s : State) (h : ∀ T, (rowsOf s T).size ≤ 2 ^ 32) : LayoutFits s fun _ => 32 := fun T => ⟨h T, le_rfl⟩

/-! The premise with the table sumcheck's instance. -/

section Tree

variable {ι Ω : Type}

/-- Child `v`'s committed witness at outcome `ω`: at its layout's heights `taus v`, its columns `cols v ω`, its public
columns the verifier's at the statement its parent reads. -/
noncomputable def witAt (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State) (slot : ι → ℕ)
    (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val) (taus : ι → Table → ℕ) (cols : ι → Ω → Table → ℕ → ℕ → K)
    (v : ι) (ω : Ω) : Witness :=
  committedAt (t v) (treeStmt T cert slot stRoot val v ω) (taus v) (cols v ω)

/-- The premise with the table sumcheck's honest instance: where the parent's circuit is satisfied, every check's
inputs are true, no compression collides and the parent's verifier reads statement `st`, child `v`'s committed witness
at its layout (`witAt`) has its hash rows' packed witnesses (`Flocked`); the table sumcheck's input claim, the bus
totals `tot` at the batch's draw `(ζ, ξ)` as `σ_0 + ξ σ_1`, is the sum of its honest instance `tableInst` on that
witness with the bus forms `qforms`; and the bus GKR's root claims `roots` are the witness's honest roots at its draw,
which the verifier holds equal. The heights and the public columns are no longer asked: they are the layout's and the
verifier's (`checksGiveInst_of_table`). -/
def ChecksGiveTable [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (P : RecParts ι Ω) (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E)
    (qforms : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → Table → Quad)
    (tot : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → E) (roots : ι → Ω → Fin 2 → E) (draw : ι → Ω → Fin 5 → E)
    (taus : ι → Table → ℕ) (cols : ι → Ω → Table → ℕ → ℕ → K) : Prop :=
  ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω,
    Sat (treeStmt T cert slot stRoot val (T.parent v) ω) (t (T.parent v)) (val (T.parent v) ω) →
    (∀ j < P.J v, P.inOk v j ω) → ω ∉ P.crBad v →
    ((cert (T.parent v)).children.getD (slot v) default).inst.VerifiesAt (cert (T.parent v)).calls
      (os (T.parent v)) (val (T.parent v) ω) (treeStmt T cert slot stRoot val v ω) L.len →
    Flocked (t v) (witAt T cert t slot stRoot val taus cols v ω) ∧
    tot v ω (bdraw v ω).1 0 + (bdraw v ω).2 * tot v ω (bdraw v ω).1 1 =
      (tableInst (n v) (witAt T cert t slot stRoot val taus cols v ω) (bdraw v ω).1
        (qforms v ω (bdraw v ω).1) (bdraw v ω).2).sum ∧
    roots v ω 0 = pullRoot (t v) (witAt T cert t slot stRoot val taus cols v ω) (draw v ω) ∧
    roots v ω 1 = pushRoot (t v) (witAt T cert t slot stRoot val taus cols v ω) (draw v ω) ∧
    roots v ω 0 = roots v ω 1

/-- `ChecksGiveInst` from `ChecksGiveTable` at layouts holding the children's rows with every owned table's `τ` at
most the sumcheck's rounds: the heights fit (`committedAt_fits`), the public columns are the verifier's
(`committedAt_pub`), and the instance's sum is the batch's honest sum at the forms' honest sums (`tableInst_sum`). -/
theorem checksGiveInst_of_table [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (P : RecParts ι Ω) (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E)
    (qforms : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → Table → Quad)
    (tot : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → E) (roots : ι → Ω → Fin 2 → E) (draw : ι → Ω → Fin 5 → E)
    (taus : ι → Table → ℕ) (cols : ι → Ω → Table → ℕ → ℕ → K)
    (hfit : ∀ v ∈ T.nodes, LayoutFits (t v) (taus v)) (hn : ∀ v ∈ T.nodes, ∀ T' ∈ owned, taus v T' ≤ n v)
    (h : ChecksGiveTable T cert t os L slot stRoot val P n bdraw qforms tot roots draw taus cols) :
    ChecksGiveInst T cert t os L slot stRoot val P n bdraw
      (fun v ω ζ => formSums (witAt T cert t slot stRoot val taus cols v ω) ζ (qforms v ω ζ)) tot roots draw
      (witAt T cert t slot stRoot val taus cols) := by
  intro v hv hne ω hps hin hcr hver
  obtain ⟨hfl, hsum, h0, h1, heq⟩ := h v hv hne ω hps hin hcr hver
  refine ⟨committedAt_fits (hfit v hv), fun z hz i => committedAt_pub _ _ _ _ hz i, hfl, ?_, h0, h1, heq⟩
  rw [hsum, tableInst_sum]
  intro T' hT'
  rw [witAt, tauOf_committedAt]
  exact hn v hv T' hT'

/-- `ChecksGiveRows` from `ChecksGiveTable`, the constraint batch's event the batch's draw event at the forms' honest
sums less the totals: `checksGiveInst_of_table`, `checksGiveBatch_of_inst`, `checksGiveRows_of_batch`. -/
theorem checksGiveRows_of_table [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (P : RecParts ι Ω) (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E)
    (qforms : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → Table → Quad)
    (tot : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → E) (roots : ι → Ω → Fin 2 → E) (draw : ι → Ω → Fin 5 → E)
    (taus : ι → Table → ℕ) (cols : ι → Ω → Table → ℕ → ℕ → K)
    (hfit : ∀ v ∈ T.nodes, LayoutFits (t v) (taus v)) (hn : ∀ v ∈ T.nodes, ∀ T' ∈ owned, taus v T' ≤ n v)
    (h : ChecksGiveTable T cert t os L slot stRoot val P n bdraw qforms tot roots draw taus cols) :
    ChecksGiveRows T cert t os L slot stRoot val P
      (fun v => batchBad (witAt T cert t slot stRoot val taus cols v)
        (fun ω ζ i => formSums (witAt T cert t slot stRoot val taus cols v ω) ζ (qforms v ω ζ) i - tot v ω ζ i)
        (bdraw v))
      draw (witAt T cert t slot stRoot val taus cols) :=
  checksGiveRows_of_batch T cert t os L slot stRoot val P n bdraw _ draw _
    (checksGiveBatch_of_inst T cert t os L slot stRoot val P n bdraw _ tot roots draw _
      (checksGiveInst_of_table T cert t os L slot stRoot val P n bdraw qforms tot roots draw taus cols hfit hn h))

/-- Non-vacuity of `ChecksGiveTable`: parts whose one check per child has its conclusion as its inputs meet it. -/
theorem checksGiveTable_claims [Fintype Ω] (T : TreeSound.Tree ι) (cert : ι → EdgeCert) (t : ι → State)
    (os : ι → Array (List ℕ)) (L : Layout) (slot : ι → ℕ) (stRoot : Ω → ℕ → Fin 4 → K) (val : ι → Ω → Val)
    (n : ι → ℕ) (bdraw : (v : ι) → Ω → (Fin (n v) → E) × E)
    (qforms : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → Table → Quad)
    (tot : (v : ι) → Ω → (Fin (n v) → E) → Fin 2 → E) (roots : ι → Ω → Fin 2 → E) (draw : ι → Ω → Fin 5 → E)
    (taus : ι → Table → ℕ) (cols : ι → Ω → Table → ℕ → ℕ → K) (outOk : ι → ℕ → Ω → Prop)
    (testBad : ι → ℕ → Finset Ω) (pcsBad crBad : ι → Finset Ω) :
    ChecksGiveTable T cert t os L slot stRoot val
      ⟨fun _ => 1, fun v _ ω =>
        Flocked (t v) (witAt T cert t slot stRoot val taus cols v ω) ∧
        tot v ω (bdraw v ω).1 0 + (bdraw v ω).2 * tot v ω (bdraw v ω).1 1 =
          (tableInst (n v) (witAt T cert t slot stRoot val taus cols v ω) (bdraw v ω).1
            (qforms v ω (bdraw v ω).1) (bdraw v ω).2).sum ∧
        roots v ω 0 = pullRoot (t v) (witAt T cert t slot stRoot val taus cols v ω) (draw v ω) ∧
        roots v ω 1 = pushRoot (t v) (witAt T cert t slot stRoot val taus cols v ω) (draw v ω) ∧
        roots v ω 0 = roots v ω 1, outOk, testBad, pcsBad, crBad⟩ n bdraw qforms tot roots draw taus cols :=
  fun _ _ _ _ _ hin _ _ => hin 0 Nat.one_pos

end Tree

end LeanVMCircuits.Rec.AirLink

namespace LeanVMCircuits.Rec.Bind

open LeanVMCircuits.Rec Model Sumcheck

/-! The table sumcheck as the certificate names it. -/

namespace TableCert

variable {tc : TableCert} {scs : Array SumcheckCert} {tops : Array TopCert} {odds : Array OddCert}
  {cs : Array Call} {rl : Array Bool} {os : Array (List ℕ)} {st : ℕ → Fin 4 → K} {val : Val}

/-- What a passing `TableCert` gives where the calls hold: its sumcheck is closed by a residual, reads no eq weight in
any round, and its input claim is `σ_0 + ξ σ_1` of the named totals at the named `ξ`; and a GKR first layer reads the
named root as both trees' value. -/
theorem sem (hF : Facts cs rl os st val) (h : tc.okIn scs tops odds cs rl os = true) :
    ∃ sc, scs[tc.sc]? = some sc ∧ sc.resid ≠ [] ∧ (∀ i, (sc.rounds.getD i default).weight = none) ∧
      Model.ev val sc.claim0 = Model.ev val tc.xi * Model.ev val tc.tot1 + Model.ev val tc.tot0 ∧
      ((∃ t ∈ tops, t.values = [tc.root, tc.root]) ∨ ∃ t ∈ odds, t.values = [tc.root, tc.root]) := by
  unfold okIn at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨hsc, hcalls⟩, hroot⟩ := h
  split at hsc
  · rename_i sc hsome
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true, Option.isNone_iff_eq_none,
      beq_iff_eq] at hsc
    obtain ⟨⟨hres, hw⟩, hout⟩ := hsc
    have hj : Model.ev val (o os tc.target) = Model.ev val tc.xi * Model.ev val tc.tot1 + Model.ev val tc.tot0 :=
      holds_of_mem hF hcalls (List.mem_singleton_self _)
    refine ⟨sc, hsome, hres, fun i => ?_, hout ▸ hj, ?_⟩
    · by_cases hi : i < sc.rounds.length
      · rw [List.getD_eq_getElem _ _ hi]
        exact hw _ (List.getElem_mem hi)
      · rw [List.getD_eq_default _ _ (by omega)]
        rfl
    · simp only [Array.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hroot
      rcases hroot with ⟨i, hi, hv, -⟩ | ⟨i, hi, hv, -⟩
      · exact Or.inl ⟨_, Array.getElem_mem hi, hv⟩
      · exact Or.inr ⟨_, Array.getElem_mem hi, hv⟩
  · exact absurd hsc (by simp)

/-- The named sumcheck's rounds read no eq weight, as the honest instance `tableInst` has none: the eq-weight field of
`SumcheckAnswers` holds for it at every challenge vector. -/
theorem answers_weight (hF : Facts cs rl os st val) (h : tc.okIn scs tops odds cs rl os = true) {sc : SumcheckCert}
    (hsc : scs[tc.sc]? = some sc) (w : AirLink.Witness) (ζ : Fin sc.rounds.length → E)
    (qforms : Fin 2 → Model.Table → AirLink.Quad) (ξ : E) (f : ℕ → E) (r : Fin sc.rounds.length → E)
    (i : Fin sc.rounds.length) :
    (sc.rounds.getD i default).weight.map f = (AirLink.tableInst sc.rounds.length w ζ qforms ξ).weight r i := by
  obtain ⟨sc', hsc', -, hw, -⟩ := sem hF h
  rw [hsc] at hsc'
  cases hsc'
  rw [hw i, AirLink.tableInst_weight]
  rfl

/-- The named sumcheck's input claim is its honest instance's sum exactly when the named totals' `σ_0 + ξ σ_1` is: the
table conjunct of `AirLink.ChecksGiveTable` with `tot` and `ξ` read off the certificate is the named check's input
claim's truth. -/
theorem claim_iff (hF : Facts cs rl os st val) (h : tc.okIn scs tops odds cs rl os = true) {sc : SumcheckCert}
    (hsc : scs[tc.sc]? = some sc) (x : E) :
    Model.ev val sc.claim0 = x ↔ Model.ev val tc.tot0 + Model.ev val tc.xi * Model.ev val tc.tot1 = x := by
  obtain ⟨sc', hsc', -, -, hc, -⟩ := sem hF h
  rw [hsc] at hsc'
  cases hsc'
  rw [hc, add_comm]

end TableCert

/-- Mutation tests of `TableCert.okIn`: a certificate naming the input claim's `mul_add` of the totals and a first
layer reading `[root, root]` passes, and swapping the totals, naming another claim, a round with an eq weight, or a
first layer reading two roots fails. -/
example : ({ sc := 0, target := 1, xi := 1, tot0 := 3, tot1 := 2, root := 7 } : TableCert).okIn
    #[{ (default : SumcheckCert) with claim0 := 9, resid := [(0, 0, 0)], rounds := [default] }]
    #[{ (default : TopCert) with values := [7, 7], claimZero := 0 }] #[] #[.zero, .mulAdd 1 2 3] #[] #[[], [9]] = true := by
  decide +kernel

example : ({ sc := 0, target := 1, xi := 1, tot0 := 2, tot1 := 3, root := 7 } : TableCert).okIn
    #[{ (default : SumcheckCert) with claim0 := 9, resid := [(0, 0, 0)], rounds := [default] }]
    #[{ (default : TopCert) with values := [7, 7], claimZero := 0 }] #[] #[.zero, .mulAdd 1 2 3] #[] #[[], [9]] = false := by
  decide

example : ({ sc := 0, target := 1, xi := 1, tot0 := 3, tot1 := 2, root := 7 } : TableCert).okIn
    #[{ (default : SumcheckCert) with claim0 := 8, resid := [(0, 0, 0)], rounds := [default] }]
    #[{ (default : TopCert) with values := [7, 7], claimZero := 0 }] #[] #[.zero, .mulAdd 1 2 3] #[] #[[], [9]] = false := by
  decide

example : ({ sc := 0, target := 1, xi := 1, tot0 := 3, tot1 := 2, root := 7 } : TableCert).okIn
    #[{ (default : SumcheckCert) with claim0 := 9, resid := [(0, 0, 0)], rounds := [{ (default : RoundCert) with weight := some 4 }] }]
    #[{ (default : TopCert) with values := [7, 7], claimZero := 0 }] #[] #[.zero, .mulAdd 1 2 3] #[] #[[], [9]] = false := by
  decide

example : ({ sc := 0, target := 1, xi := 1, tot0 := 3, tot1 := 2, root := 7 } : TableCert).okIn
    #[{ (default : SumcheckCert) with claim0 := 9, resid := [(0, 0, 0)], rounds := [default] }]
    #[{ (default : TopCert) with values := [7, 6], claimZero := 0 }] #[] #[.zero, .mulAdd 1 2 3] #[] #[[], [9]] = false := by
  decide +kernel

end LeanVMCircuits.Rec.Bind
