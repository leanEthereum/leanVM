/-
The descent step on level problems: note 37 Proposition 3.3, steps 3 to 5 of section 1.2 of the
referee report (note 46).

A level problem is a level polynomial `ℓ` of level `j` (`Level.lean`), a degree bound `κ` and a
word `v : F → Option F` (only its values on `D` matter, `none` is the blank); a member at slack `Δ`
is a polynomial `P` of degree at most `κ` with `#{x ∈ D : v(x) = P(ℓ(x))} ≥ 2^j κ + Δ`
(`LevelPb`, `LevelPb.Mem`).

For two members `c₀ ≠ c₁` and a nonzero value `a` of `ℓ` on `D`, with `ϱ = rho a (c₁ - c₀)`:

* `nextWord`: the word `v' = (v - c₀ ∘ ℓ) / (ϱ ∘ ℓ)`, blank where `v` is blank or `ϱ(ℓ(x)) = 0`.
* `nextWord_agree_iff`: off the zeros of `ϱ ∘ ℓ`, `c ∘ ℓ` agrees with `v` at `x` if and only if
  `Q ∘ ℓ'` agrees with `v'` at `x`, for `c = c₀ + ϱ Q(q)` and `ℓ' = q ∘ ℓ`.
* `polyAgr_descent_eq`: `agr_v(c) = agr_{v'}(Q) + z₀`, with
  `z₀ = #{x ∈ D : ϱ(ℓ(x)) = 0, v(x) = c₀(ℓ(x))}` the same for all members.
* `card_zeros_le`: `z₀ ≤ m deg ϱ` when the fibres of `ℓ` have at most `m` points.
* `slack_arith`: the inequality the induction needs: from `A ≥ m κ + Δ`, `deg ϱ ≤ κ` and
  `A ≤ A' + m deg ϱ` to `A' ≥ 2 m ⌊(κ - deg ϱ) / 2⌋ + Δ`. The slack `Δ` is preserved.
* `LevelPb.next`, `LevelPb.next_mem`, `descentMap`, `descentMap_injOn`: the problem of level
  `j + 1`, the map `c ↦ Q` from the members periodic for `(c₀, c₁, a)` to its members, and its
  injectivity.
* `LevelPb.descent_step`: note 37 Proposition 3.3 as one statement.
-/
import PeriodDescent.Level
import PeriodDescent.Base

open Polynomial Finset
open scoped Classical

namespace PeriodDescent

variable {F : Type*} [Field F]

/-! ### The word of the next level -/

/-- The word `v' = (v - c₀ ∘ ℓ) / (ϱ ∘ ℓ)`, blank where `v` is blank or `ϱ(ℓ(x)) = 0`. -/
noncomputable def nextWord (ℓ P0 ϱ : F[X]) (v : F → Option F) : F → Option F := fun x =>
  if ϱ.eval (ℓ.eval x) = 0 then none
  else (v x).map (fun w => (w - P0.eval (ℓ.eval x)) / ϱ.eval (ℓ.eval x))

theorem nextWord_of_eval_eq_zero {ℓ P0 ϱ : F[X]} {v : F → Option F} {x : F}
    (hx : ϱ.eval (ℓ.eval x) = 0) : nextWord ℓ P0 ϱ v x = none := by
  unfold nextWord
  simp only [hx, ↓reduceIte]

/-- Off the zeros of `ϱ ∘ ℓ`: `c ∘ ℓ` agrees with `v` at `x` if and only if `Q ∘ (q ∘ ℓ)` agrees
with `v'` at `x`. -/
theorem nextWord_agree_iff {a : F} {ℓ P P0 ϱ Q : F[X]} (h : P - P0 = ϱ * Q.comp (qPoly a))
    (v : F → Option F) (x : F) (hx : ϱ.eval (ℓ.eval x) ≠ 0) :
    v x = some (P.eval (ℓ.eval x))
      ↔ nextWord ℓ P0 ϱ v x = some (Q.eval (((qPoly a).comp ℓ).eval x)) := by
  unfold nextWord
  simp only [hx, ↓reduceIte, eval_comp]
  rcases v x with _ | w
  · simp
  · simp only [Option.map_some, Option.some.injEq]
    exact agree_iff_of_ne_zero h (ℓ.eval x) w hx

/-- **The agreements, exactly.** `agr_v(c) = agr_{v'}(Q) + z₀`, where `z₀` counts the points with
`ϱ(ℓ(x)) = 0` at which `v` takes the value of `c₀`: it is the same for all `c = c₀ + ϱ Q(q)`. -/
theorem polyAgr_descent_eq {a : F} {ℓ P P0 ϱ Q : F[X]} (h : P - P0 = ϱ * Q.comp (qPoly a))
    (D : Finset F) (v : F → Option F) :
    polyAgr D ℓ v P = polyAgr D ((qPoly a).comp ℓ) (nextWord ℓ P0 ϱ v) Q
      + (D.filter (fun x => ϱ.eval (ℓ.eval x) = 0 ∧ v x = some (P0.eval (ℓ.eval x)))).card := by
  unfold polyAgr
  have hdisj : Disjoint
      (D.filter (fun x => nextWord ℓ P0 ϱ v x = some (Q.eval (((qPoly a).comp ℓ).eval x))))
      (D.filter (fun x => ϱ.eval (ℓ.eval x) = 0 ∧ v x = some (P0.eval (ℓ.eval x)))) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    have h0 := (Finset.mem_filter.mp h2).2.1
    have hv := (Finset.mem_filter.mp h1).2
    rw [nextWord_of_eval_eq_zero h0] at hv
    exact absurd hv (by simp)
  rw [← Finset.card_union_of_disjoint hdisj]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hx, hv⟩
    by_cases h0 : ϱ.eval (ℓ.eval x) = 0
    · right
      exact ⟨hx, h0, by rw [hv, eval_eq_of_eval_rho_eq_zero h _ h0]⟩
    · left
      exact ⟨hx, (nextWord_agree_iff h v x h0).mp hv⟩
  · rintro (⟨hx, hv⟩ | ⟨hx, h0, hv⟩)
    · have h0 : ϱ.eval (ℓ.eval x) ≠ 0 := by
        intro h0
        rw [nextWord_of_eval_eq_zero h0] at hv
        exact absurd hv (by simp)
      exact ⟨hx, (nextWord_agree_iff h v x h0).mpr hv⟩
    · exact ⟨hx, by rw [hv, eval_eq_of_eval_rho_eq_zero h _ h0]⟩

/-- The points of `D` over the roots of `ϱ` number at most `m deg ϱ`, when the fibres of `ℓ` on
`D` have at most `m` points. -/
theorem card_zeros_le (D : Finset F) (ℓ : F[X]) (m : ℕ)
    (hfib : ∀ y, (D.filter (fun x => ℓ.eval x = y)).card ≤ m) {ϱ : F[X]} (hϱ : ϱ ≠ 0) :
    (D.filter (fun x => ϱ.eval (ℓ.eval x) = 0)).card ≤ m * ϱ.natDegree := by
  have h1 : (D.filter (fun x => ϱ.eval (ℓ.eval x) = 0)).card
      = ∑ y ∈ ϱ.roots.toFinset,
          ((D.filter (fun x => ϱ.eval (ℓ.eval x) = 0)).filter (fun x => ℓ.eval x = y)).card :=
    Finset.card_eq_sum_card_fiberwise fun x hx =>
      Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr
        ((mem_roots hϱ).mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2))
  have h2 : ∀ y ∈ ϱ.roots.toFinset,
      ((D.filter (fun x => ϱ.eval (ℓ.eval x) = 0)).filter (fun x => ℓ.eval x = y)).card ≤ m :=
    fun y _ => (Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans (hfib y)
  rw [h1]
  calc ∑ y ∈ ϱ.roots.toFinset,
        ((D.filter (fun x => ϱ.eval (ℓ.eval x) = 0)).filter (fun x => ℓ.eval x = y)).card
      ≤ ϱ.roots.toFinset.card • m := Finset.sum_le_card_nsmul _ _ _ h2
    _ ≤ ϱ.natDegree * m :=
        Nat.mul_le_mul_right m ((Multiset.toFinset_card_le _).trans (card_roots' ϱ))
    _ = m * ϱ.natDegree := mul_comm _ _

/-- The agreement drops by at most `m deg ϱ`. -/
theorem polyAgr_descent_le {a : F} {ℓ P P0 ϱ Q : F[X]} (h : P - P0 = ϱ * Q.comp (qPoly a))
    (hϱ : ϱ ≠ 0) (D : Finset F) (v : F → Option F) (m : ℕ)
    (hfib : ∀ y, (D.filter (fun x => ℓ.eval x = y)).card ≤ m) :
    polyAgr D ℓ v P
      ≤ polyAgr D ((qPoly a).comp ℓ) (nextWord ℓ P0 ϱ v) Q + m * ϱ.natDegree := by
  rw [polyAgr_descent_eq h D v]
  refine Nat.add_le_add_left ?_ _
  refine (Finset.card_le_card fun x hx => ?_).trans (card_zeros_le D ℓ m hfib hϱ)
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.1⟩

/-- **The slack does not decrease.** With `m` the fibre size, `κ` the degree bound, `d = deg ϱ`,
`A` the agreement of a member and `A'` the agreement of its image: if `A ≥ m κ + Δ`, `d ≤ κ` and
`A ≤ A' + m d`, then `A' ≥ 2 m ⌊(κ - d) / 2⌋ + Δ`. -/
theorem slack_arith (m κ Δ d A A' : ℕ) (hd : d ≤ κ) (hA : m * κ + Δ ≤ A)
    (hA' : A ≤ A' + m * d) : 2 * m * ((κ - d) / 2) + Δ ≤ A' := by
  have h1 : 2 * ((κ - d) / 2) ≤ κ - d := Nat.mul_div_le _ _
  generalize (κ - d) / 2 = e at h1 ⊢
  have h2 : m * (d + 2 * e) ≤ m * κ := Nat.mul_le_mul_left m (by omega)
  have h3 : m * (d + 2 * e) = m * d + 2 * m * e := by ring
  omega

/-! ### Level problems -/

/-- A level problem of the list problem "degree `< k`" on `D` (note 37 Definition 3.1; a level-`j`
instance of Theorem R of note 46, without its list): a level polynomial `ℓ` of level `j`, a degree
bound `κ ≤ ⌊(k - 1) / 2^j⌋` (`κ = k - 1` at level `0`), and a word `v` with blanks. -/
structure LevelPb (D : Finset F) (k : ℕ) where
  /-- the level -/
  j : ℕ
  /-- the level polynomial, `L_U` for a subspace `U ⊆ D` with `2^j` elements -/
  ℓ : F[X]
  /-- the degree bound -/
  κ : ℕ
  /-- the word; `none` is the blank -/
  v : F → Option F
  hℓ : IsLevel D j ℓ
  hκ : κ ≤ (k - 1) / 2 ^ j
  hκ0 : j = 0 → κ = k - 1

/-- `P` is a member of the level problem at slack `Δ`: degree at most `κ`, and agreement at least
`2^j κ + Δ`. -/
def LevelPb.Mem {D : Finset F} {k : ℕ} (p : LevelPb D k) (Δ : ℕ) (P : F[X]) : Prop :=
  P.natDegree ≤ p.κ ∧ 2 ^ p.j * p.κ + Δ ≤ polyAgr D p.ℓ p.v P

/-- The problem of the next level, for two members `c₀, c₁` and a nonzero value `a` of `ℓ` on
`D`: level polynomial `q_a ∘ ℓ`, degree bound `⌊(κ - deg ϱ) / 2⌋`, word `nextWord`. -/
noncomputable def LevelPb.next {D : Finset F} {k : ℕ} (p : LevelPb D k) (c0 c1 : F[X]) (a : F)
    (ha : a ∈ D.image (fun x => p.ℓ.eval x)) (ha0 : a ≠ 0) : LevelPb D k where
  j := p.j + 1
  ℓ := (qPoly a).comp p.ℓ
  κ := (p.κ - (rho a (c1 - c0)).natDegree) / 2
  v := nextWord p.ℓ c0 (rho a (c1 - c0)) p.v
  hℓ := IsLevel.succ p.hℓ ha ha0
  hκ := by
    calc (p.κ - (rho a (c1 - c0)).natDegree) / 2 ≤ p.κ / 2 :=
          Nat.div_le_div_right (Nat.sub_le _ _)
      _ ≤ (k - 1) / 2 ^ p.j / 2 := Nat.div_le_div_right p.hκ
      _ = (k - 1) / 2 ^ (p.j + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
  hκ0 := fun h => absurd h (Nat.succ_ne_zero _)

/-- The map `c ↦ Q` with `c = c₀ + ϱ Q(q)` (zero when there is no such `Q`). -/
noncomputable def descentMap (a : F) (c0 ϱ : F[X]) (c : F[X]) : F[X] :=
  if h : ∃ Q : F[X], c - c0 = ϱ * Q.comp (qPoly a) then h.choose else 0

theorem descentMap_spec {a : F} {c0 ϱ c : F[X]} (h : ∃ Q : F[X], c - c0 = ϱ * Q.comp (qPoly a)) :
    c - c0 = ϱ * (descentMap a c0 ϱ c).comp (qPoly a) := by
  unfold descentMap
  split_ifs
  exact h.choose_spec

/-- The map `c ↦ Q` is injective on the polynomials of the form `c₀ + ϱ Q(q)`. -/
theorem descentMap_injOn {a : F} {c0 ϱ c c' : F[X]}
    (h : ∃ Q : F[X], c - c0 = ϱ * Q.comp (qPoly a))
    (h' : ∃ Q : F[X], c' - c0 = ϱ * Q.comp (qPoly a))
    (heq : descentMap a c0 ϱ c = descentMap a c0 ϱ c') : c = c' := by
  have h1 := descentMap_spec h
  have h2 := descentMap_spec h'
  rw [heq] at h1
  linear_combination h1 - h2

section CharTwo

variable [CharP F 2]

/-- **Note 37 Proposition 3.3: members go to members.** Let `c₀ ≠ c₁` be members of a level
problem at slack `Δ` and `a` a nonzero value of `ℓ` on `D`. If `c` is a member and
`c = c₀ + ϱ Q(q)`, `ϱ = rho a (c₁ - c₀)`, then `Q` is a member of the next problem at the same
slack `Δ`. -/
theorem LevelPb.next_mem {D : Finset F} (hD : IsSubspace D) {k : ℕ} (Δ : ℕ) (p : LevelPb D k)
    {c0 c1 c : F[X]} (h0 : p.Mem Δ c0) (h1 : p.Mem Δ c1) (h01 : c0 ≠ c1) (a : F)
    (ha : a ∈ D.image (fun x => p.ℓ.eval x)) (ha0 : a ≠ 0) (hc : p.Mem Δ c) {Q : F[X]}
    (hQ : c - c0 = rho a (c1 - c0) * Q.comp (qPoly a)) :
    (p.next c0 c1 a ha ha0).Mem Δ Q := by
  have hu : c1 - c0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h01)
  have hϱ := rho_ne_zero a hu
  have hd : (rho a (c1 - c0)).natDegree ≤ p.κ :=
    (natDegree_rho_le a hu).trans ((natDegree_sub_le c1 c0).trans (max_le h1.1 h0.1))
  constructor
  · show Q.natDegree ≤ (p.κ - (rho a (c1 - c0)).natDegree) / 2
    refine natDegree_le_of_descent a hϱ ?_
    rw [← hQ]
    exact (natDegree_sub_le c c0).trans (max_le hc.1 h0.1)
  · show 2 ^ (p.j + 1) * ((p.κ - (rho a (c1 - c0)).natDegree) / 2) + Δ
      ≤ polyAgr D ((qPoly a).comp p.ℓ) (nextWord p.ℓ c0 (rho a (c1 - c0)) p.v) Q
    have h2 := polyAgr_descent_le hQ hϱ D p.v (2 ^ p.j) (p.hℓ.fiber_card_le hD)
    have h3 := slack_arith (2 ^ p.j) p.κ Δ _ _ _ hd hc.2 h2
    have e : 2 ^ (p.j + 1) = 2 * 2 ^ p.j := by
      rw [pow_succ]
      ring
    rw [e]
    exact h3

/-- **Note 37 Proposition 3.3 (difference descent).** Let `c₀ ≠ c₁` be two members of a level
problem `p` of level `j` at slack `Δ`, and `a` a nonzero value of its level polynomial on `D`.
There are a level problem `p'` of level `j + 1` (same domain, same field, same `k`) and a map `φ`
that sends the members of `p` whose function `(c - c₀) / (c₁ - c₀)` has the period `a` to members
of `p'` at the same slack `Δ`, injectively. -/
theorem LevelPb.descent_step {D : Finset F} (hD : IsSubspace D) {k : ℕ} (Δ : ℕ) (p : LevelPb D k)
    {c0 c1 : F[X]} (h0 : p.Mem Δ c0) (h1 : p.Mem Δ c1) (h01 : c0 ≠ c1) {a : F}
    (ha : a ∈ (D.image (fun x => p.ℓ.eval x)).erase 0) :
    ∃ p' : LevelPb D k, p'.j = p.j + 1 ∧ ∃ φ : F[X] → F[X],
      (∀ c, p.Mem Δ c → Periodic a (c1 - c0) (c - c0) → p'.Mem Δ (φ c)) ∧
      (∀ c c', p.Mem Δ c → Periodic a (c1 - c0) (c - c0) → p.Mem Δ c' →
        Periodic a (c1 - c0) (c' - c0) → φ c = φ c' → c = c') := by
  have ha' := Finset.mem_of_mem_erase ha
  have ha0 := Finset.ne_of_mem_erase ha
  have hu : c1 - c0 ≠ 0 := sub_ne_zero.mpr (Ne.symm h01)
  refine ⟨p.next c0 c1 a ha' ha0, rfl, descentMap a c0 (rho a (c1 - c0)), ?_, ?_⟩
  · intro c hc hper
    have hex := (periodic_iff_exists ha0 hu (c - c0)).mp hper
    exact p.next_mem hD _ h0 h1 h01 a ha' ha0 hc (descentMap_spec hex)
  · intro c c' _ hper _ hper' heq
    exact descentMap_injOn ((periodic_iff_exists ha0 hu (c - c0)).mp hper)
      ((periodic_iff_exists ha0 hu (c' - c0)).mp hper') heq

end CharTwo

end PeriodDescent
