module

public import Quantum.Xmss.Hybrid.SchemeSeed

@[expose] public section

/-!
# Hiding the scheme seed: the staged swap, its good set and its bad fraction

* `stage1`, `stageN`: exchanges of `h`-cells with extra slots, fiberwise over data the exchange
  preserves, built over abstract types.
* `schemeSplit : Tab ≃ Pub × MasterSeed`: the table with three extra uniform slots. Stage `0` moves
  the seed derivation's output to slot `0`, stage `A` the parameter's to slot `1`, stage `B` the
  chain starts' to the slots `2` (when their capacities are distinct), and `splitSeed` splits the
  scheme seed off slot `0`. The hidden coordinate is the scheme seed (`schemeSplit_snd`); when the
  hidden capacities `posOf` are distinct, the public part gives the parameter, the chain starts'
  hashes, and `h` off those capacities (`schemeSplit_transfer`).
* `schemeGood Q`: the hidden capacities are distinct and no computation `Q i` of the parameter and
  the chain starts' hashes reads `h` at one. On it the challenger's data is a function of the
  public part (`schemeData_eq_of_mem`).
* `schemeGood_frac_le`: the fraction outside it is at most the bad permutations, the collisions
  `|A|² (G + 1) / |Z|`, and per computation `qs₀ᵢ / 2^256 + (G + 1) qᵢ / |Z|` (seed derivation) plus
  `qs₁ᵢ / 2^256 + |B| (G + 1) qᵢ / |Z|` (seed-keyed cells).
* `avg_hiddenMass_schemeSeed_le_of_schemeData`: the scheme-seed mass bound averaged over the table.
-/

open Matrix
open scoped ENNReal ComplexOrder

universe u v w

namespace Quantum.Xmss.Hybrid

open Quantum Quantum.Sponge

/-! ## Exchanges over abstract types -/

section stage

variable {X Z J W : Type*} [AddCommGroup X]

/-- **Exchange one cell with a slot, fiberwise**: the cell `pos w` takes the slot value, and the
slot takes the cell value shifted by `sh w`, for the data `w` the exchange preserves. -/
def stage1 [DecidableEq Z] (pos : W → Z) (sh : W → X) : ((Z → X) × X) × W ≃ ((Z → X) × X) × W :=
  fiberEquiv Prod.snd (fun w ↦ (xch1 (pos w) (sh w)).prodCongr (Equiv.refl W)) fun _ _ ↦ rfl

theorem stage1_apply [DecidableEq Z] (pos : W → Z) (sh : W → X) (h : Z → X) (u : X) (w : W) :
    stage1 pos sh ((h, u), w) = ((Function.update h (pos w) u, sh w + h (pos w)), w) :=
  rfl

open scoped Classical in
/-- **Exchange cells with slots, fiberwise**: the cells `pos w` take the slot values and the slots
the cell values shifted by `sh w`, when the cells are distinct; otherwise nothing moves. -/
noncomputable def stageN (pos : W → J → Z) (sh : W → J → X) :
    ((Z → X) × (J → X)) × W ≃ ((Z → X) × (J → X)) × W :=
  fiberEquiv Prod.snd (fun w ↦ (if hw : Function.Injective (pos w) then xch (pos w) hw (sh w)
    else Equiv.refl _).prodCongr (Equiv.refl W)) fun _ _ ↦ rfl

theorem stageN_snd (pos : W → J → Z) (sh : W → J → X) (t : ((Z → X) × (J → X)) × W) :
    (stageN pos sh t).2 = t.2 :=
  rfl

theorem stageN_apply_of_injective (pos : W → J → Z) (sh : W → J → X) (p : (Z → X) × (J → X))
    (w : W) (hw : Function.Injective (pos w)) :
    stageN pos sh (p, w) = (xch (pos w) hw (sh w) p, w) := by
  classical
  change ((if hw' : Function.Injective (pos w) then xch (pos w) hw' (sh w)
    else Equiv.refl _).prodCongr (Equiv.refl W)) (p, w) = _
  rw [dite_eq_left hw]
  rfl

theorem stageN_eq_mk (pos : W → J → Z) (sh : W → J → X) (p : (Z → X) × (J → X)) (w : W) :
    stageN pos sh (p, w) = ((stageN pos sh (p, w)).1, w) :=
  Prod.ext rfl rfl

theorem xch_snd_mk (pos : J → Z) (hpos : Function.Injective pos) (sh : J → X) (h : Z → X)
    (u : J → X) (a : J) : (xch pos hpos sh (h, u)).2 a = sh a + h (pos a) :=
  rfl

theorem xch_fst_mk_of_notMem (pos : J → Z) (hpos : Function.Injective pos) (sh : J → X)
    (h : Z → X) (u : J → X) {z : Z} (hz : ∀ a, pos a ≠ z) : (xch pos hpos sh (h, u)).1 z = h z :=
  xch_fst_of_notMem pos hpos sh (h, u) hz

end stage

/-! ## Sums in coordinates, over abstract types -/

section sums

variable {M : Type*} [AddCommMonoid M]

/-- A sum over a type in four coordinates. -/
theorem sum_eq_sum_coords {Ω S K T : Type*} [Fintype Ω] [Fintype S] [Fintype K] [Fintype T]
    (e : ((Ω × S) × K) × K ≃ T) (F : T → M) :
    ∑ x, F x = ∑ ω, ∑ s, ∑ k, ∑ k', F (e (((ω, s), k), k')) := by
  calc ∑ x, F x = ∑ c, F (e c) := (Fintype.sum_equiv e _ _ fun _ ↦ rfl).symm
    _ = _ := by simp only [Fintype.sum_prod_type]

theorem card_eq_coords {Ω S K T : Type*} [Fintype Ω] [Fintype S] [Fintype K] [Fintype T]
    (e : ((Ω × S) × K) × K ≃ T) :
    Fintype.card T = Fintype.card Ω * Fintype.card S * (Fintype.card K * Fintype.card K) := by
  rw [← Fintype.card_congr e, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod]
  ring

/-- A sum of a function of the first coordinate. -/
theorem sum_fst_eq {α γ : Type*} [Fintype α] [Fintype γ] (f : α → M) :
    ∑ x : α × γ, f x.1 = Fintype.card γ • ∑ a, f a := by
  rw [Fintype.sum_prod_type, Finset.smul_sum]
  simp only [Finset.sum_const, Finset.card_univ]

/-- Moving an outer sum inside two others. -/
theorem sum_comm_three {A Ω S : Type*} [Fintype A] [Fintype Ω] [Fintype S] (f : A → Ω → S → M) :
    ∑ a, ∑ ω, ∑ s, f a ω s = ∑ ω, ∑ s, ∑ a, f a ω s := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ω _ ↦ Finset.sum_comm

/-- The uniform average of a function of the first coordinate. -/
theorem inv_card_mul_sum_fst {α γ : Type*} [Fintype α] [Fintype γ] [Nonempty γ] (f : α → ℝ≥0∞) :
    (Fintype.card (α × γ) : ℝ≥0∞)⁻¹ * ∑ x : α × γ, f x.1 =
      (Fintype.card α : ℝ≥0∞)⁻¹ * ∑ a, f a := by
  have hγ : (Fintype.card γ : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [sum_fst_eq, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inr hγ), mul_assoc,
    ← mul_assoc _ (Fintype.card γ : ℝ≥0∞), ENNReal.inv_mul_cancel hγ (ENNReal.natCast_ne_top _),
    one_mul]

/-- A double sum of terms at most `c d`. -/
theorem sum_sum_le_mul {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℕ) (c d : ℕ)
    (h : ∀ a b, f a b ≤ c * d) :
    ∑ a, ∑ b, f a b ≤ Fintype.card α * Fintype.card β * c * d := by
  calc ∑ a, ∑ b, f a b ≤ ∑ _a : α, ∑ _b : β, c * d :=
        Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ h a b
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

/-- A count of a function of the first coordinate. -/
theorem card_mul_sum_fst_eq {α γ : Type*} [Fintype α] [Fintype γ] (c : α → ℕ) (P N : ℕ)
    (h : P * ∑ a, c a = Fintype.card α * N) :
    P * ∑ x : α × γ, c x.1 = Fintype.card (α × γ) * N := by
  rw [sum_fst_eq, smul_eq_mul, Fintype.card_prod, mul_left_comm, h]
  ring

/-- **Assembling a bad fraction**: a count `a` bounded by parts, each at most `N` times its
fraction, is at most `N` times the sum of the fractions. -/
theorem inv_mul_le_of_parts {ι : Type*} [Fintype ι] {N a p c : ℕ} {d e : ι → ℕ}
    {A B : ℝ≥0∞} {C D : ι → ℝ≥0∞} (hN : N ≠ 0) (ha : a ≤ p + (c + ∑ i, (d i + e i)))
    (hp : (p : ℝ≥0∞) ≤ N * A) (hc : (c : ℝ≥0∞) ≤ N * B)
    (hd : ∀ i, (d i : ℝ≥0∞) ≤ N * C i) (he : ∀ i, (e i : ℝ≥0∞) ≤ N * D i) :
    (N : ℝ≥0∞)⁻¹ * a ≤ A + B + ∑ i, (C i + D i) := by
  have h1 : (a : ℝ≥0∞) ≤ N * (A + B + ∑ i, (C i + D i)) := by
    calc (a : ℝ≥0∞) ≤ ((p + (c + ∑ i, (d i + e i)) : ℕ) : ℝ≥0∞) := by exact_mod_cast ha
      _ = p + (c + ∑ i, ((d i : ℝ≥0∞) + e i)) := by simp only [Nat.cast_add, Nat.cast_sum]
      _ ≤ N * A + (N * B + ∑ i, (N * C i + N * D i)) :=
          add_le_add hp (add_le_add hc (Finset.sum_le_sum fun i _ ↦ add_le_add (hd i) (he i)))
      _ = _ := by simp only [mul_add, Finset.mul_sum, add_assoc]
  calc (N : ℝ≥0∞)⁻¹ * a ≤ (N : ℝ≥0∞)⁻¹ * (N * (A + B + ∑ i, (C i + D i))) := by gcongr
    _ = _ := ENNReal.inv_mul_cancel_left (Nat.cast_ne_zero.mpr hN) (ENNReal.natCast_ne_top _)

end sums

/-! ## Collisions of the hidden capacities, over abstract types -/

section collide

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

open scoped Classical

/-- **Distinct cells rarely collide in capacity**: for a permutation with rate counts at most `G`,
the capacities of the cells `cell a` (distinct) collide for at most `|A|² (G + 1) / |Z|` of the
keys `k, k'`. -/
theorem card_mul_sum_not_injective_capOf_le {A : Type*} [Fintype A] [DecidableEq A]
    (π : Equiv.Perm (X × Z))
    (G : ℕ) (cell : A → X) (hcell : Function.Injective cell) :
    Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z,
        (if PermGood π G ∧ ¬Function.Injective (fun a ↦ capOf k k' π (cell a)) then 1 else 0) ≤
      Fintype.card (X → Z) * Fintype.card (X → Z) *
        (Fintype.card A * Fintype.card A * (G + 1)) := by
  by_cases hG : PermGood π G
  · have hle : ∀ k k' : X → Z,
        (if PermGood π G ∧ ¬Function.Injective (fun a ↦ capOf k k' π (cell a)) then 1 else 0) ≤
          ∑ a : A, ∑ b : A,
            (if a ≠ b ∧ capOf k k' π (cell a) = capOf k k' π (cell b) then 1 else 0) := by
      intro k k'
      split_ifs with h
      · obtain ⟨-, hn⟩ := h
        simp only [Function.Injective, not_forall] at hn
        obtain ⟨a, b, hab, hne⟩ := hn
        have h1 : (if a ≠ b ∧ capOf k k' π (cell a) = capOf k k' π (cell b) then 1 else 0) = 1 :=
          ite_eq_left ⟨hne, hab⟩
        calc 1 = (if a ≠ b ∧ capOf k k' π (cell a) = capOf k k' π (cell b) then 1 else 0) :=
              h1.symm
          _ ≤ ∑ b' : A,
              (if a ≠ b' ∧ capOf k k' π (cell a) = capOf k k' π (cell b') then 1 else 0) :=
              Finset.single_le_sum (f := fun b' ↦
                (if a ≠ b' ∧ capOf k k' π (cell a) = capOf k k' π (cell b') then 1 else 0))
                (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ b)
          _ ≤ _ := Finset.single_le_sum (f := fun a' ↦ ∑ b' : A,
              (if a' ≠ b' ∧ capOf k k' π (cell a') = capOf k k' π (cell b') then 1 else 0))
              (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
      · exact Nat.zero_le _
    have hab : ∀ a b : A, Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z,
        (if a ≠ b ∧ capOf k k' π (cell a) = capOf k k' π (cell b) then 1 else 0) ≤
          Fintype.card (X → Z) * Fintype.card (X → Z) * (G + 1) := by
      intro a b
      by_cases h : a = b
      · simp [h]
      · have hc := card_mul_sum_capOf_eq_le π G hG (hcell.ne h)
        simpa only [ne_eq, h, not_false_eq_true, true_and] using hc
    calc Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z,
          (if PermGood π G ∧ ¬Function.Injective (fun a ↦ capOf k k' π (cell a)) then 1 else 0)
        ≤ Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z, ∑ a : A, ∑ b : A,
            (if a ≠ b ∧ capOf k k' π (cell a) = capOf k k' π (cell b) then 1 else 0) := by
          gcongr with k _ k' _
          exact hle k k'
      _ = ∑ a : A, ∑ b : A, Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z,
            (if a ≠ b ∧ capOf k k' π (cell a) = capOf k k' π (cell b) then 1 else 0) := by
          rw [sum_comm_four]
          simp only [Finset.mul_sum]
      _ ≤ ∑ _a : A, ∑ _b : A, Fintype.card (X → Z) * Fintype.card (X → Z) * (G + 1) :=
          Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ hab a b
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
  · simp [hG]

end collide

/-! ## The staged swap on leanXMSS tables -/

section split

open HashSig LeanXmss

/-- The extra slots: the scheme seed's, the parameter's, and the chain starts'. -/
abbrev SeedSlots : Type := X × X × (CsIdx → X)

/-- The tables with the extra slots. -/
abbrev Tab : Type := HonestTable × SeedSlots

/-- The public part: a table, and the slots without the first `256` bits of the scheme seed's. -/
abbrev Pub : Type := HonestTable × ((Fin 832 → ZMod 2) × X × (CsIdx → X))

/-- The data a one-slot stage preserves: `k`, `k'`, `π`, `S₀` and the two other slots. -/
abbrev Rest₁ : Type := (X → Z) × (X → Z) × Equiv.Perm (X × Z) × MasterSeed × X × (CsIdx → X)

/-- The data stage `B` preserves: `k`, `k'`, `π`, `S₀` and the slots `0` and `1`. -/
abbrev RestB : Type := (X → Z) × (X → Z) × Equiv.Perm (X × Z) × MasterSeed × X × X

/-- Stage `0`'s view of a table: `h` with slot `0`, and the rest. -/
def shuf0 : Tab ≃ ((Z → X) × X) × Rest₁ where
  toFun t := ((t.1.keys.1, t.2.1),
    t.1.keys.2.1, t.1.keys.2.2, t.1.perm, t.1.masterSeed, t.2.2.1, t.2.2.2)
  invFun p := (⟨(p.1.1, p.2.1, p.2.2.1), p.2.2.2.1, p.2.2.2.2.1⟩,
    p.1.2, p.2.2.2.2.2.1, p.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Stage `A`'s view of a table: `h` with slot `1`, and the rest. -/
def shufA : Tab ≃ ((Z → X) × X) × Rest₁ where
  toFun t := ((t.1.keys.1, t.2.2.1),
    t.1.keys.2.1, t.1.keys.2.2, t.1.perm, t.1.masterSeed, t.2.1, t.2.2.2)
  invFun p := (⟨(p.1.1, p.2.1, p.2.2.1), p.2.2.2.1, p.2.2.2.2.1⟩,
    p.2.2.2.2.2.1, p.1.2, p.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Stage `B`'s view of a table: `h` with the slots `2`, and the rest. -/
def shufB : Tab ≃ ((Z → X) × (CsIdx → X)) × RestB where
  toFun t := ((t.1.keys.1, t.2.2.2),
    t.1.keys.2.1, t.1.keys.2.2, t.1.perm, t.1.masterSeed, t.2.1, t.2.2.1)
  invFun p := (⟨(p.1.1, p.2.1, p.2.2.1), p.2.2.2.1, p.2.2.2.2.1⟩,
    p.2.2.2.2.2.1, p.2.2.2.2.2.2, p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem shuf0_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (u₀ u₁ : X) (u₂ : CsIdx → X) :
    shuf0 (⟨(h, k, k'), π, S₀⟩, (u₀, u₁, u₂)) = ((h, u₀), (k, k', π, S₀, u₁, u₂)) :=
  rfl

theorem shuf0_symm_apply (h : Z → X) (u₀ : X) (k k' : X → Z) (π : Equiv.Perm (X × Z))
    (S₀ : MasterSeed) (u₁ : X) (u₂ : CsIdx → X) :
    shuf0.symm ((h, u₀), (k, k', π, S₀, u₁, u₂)) = (⟨(h, k, k'), π, S₀⟩, (u₀, u₁, u₂)) :=
  rfl

theorem shufA_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (u₀ u₁ : X) (u₂ : CsIdx → X) :
    shufA (⟨(h, k, k'), π, S₀⟩, (u₀, u₁, u₂)) = ((h, u₁), (k, k', π, S₀, u₀, u₂)) :=
  rfl

theorem shufA_symm_apply (h : Z → X) (u₁ : X) (k k' : X → Z) (π : Equiv.Perm (X × Z))
    (S₀ : MasterSeed) (u₀ : X) (u₂ : CsIdx → X) :
    shufA.symm ((h, u₁), (k, k', π, S₀, u₀, u₂)) = (⟨(h, k, k'), π, S₀⟩, (u₀, u₁, u₂)) :=
  rfl

theorem shufB_symm_apply (p : (Z → X) × (CsIdx → X)) (k k' : X → Z) (π : Equiv.Perm (X × Z))
    (S₀ : MasterSeed) (u₀ u₁ : X) :
    shufB.symm (p, (k, k', π, S₀, u₀, u₁)) = (⟨(p.1, k, k'), π, S₀⟩, (u₀, u₁, p.2)) :=
  rfl

/-- Stage `0`'s cell: the seed derivation's capacity. -/
def pos0 (w : Rest₁) : Z :=
  capOf w.1 w.2.1 w.2.2.1 (seedCell w.2.2.2.1)

/-- Stage `0`'s shift: the seed derivation's rate. -/
def sh0 (w : Rest₁) : X :=
  rateOf w.1 w.2.2.1 (seedCell w.2.2.2.1)

/-- Stage `A`'s cell: the parameter derivation's capacity, for the scheme seed in slot `0`. -/
def posA (w : Rest₁) : Z :=
  capOf w.1 w.2.1 w.2.2.1 (skCell 0 (out256 w.2.2.2.2.1) none)

/-- Stage `A`'s shift: the parameter derivation's rate. -/
def shA (w : Rest₁) : X :=
  rateOf w.1 w.2.2.1 (skCell 0 (out256 w.2.2.2.2.1) none)

/-- Stage `B`'s cells: the chain starts' capacities, for the scheme seed in slot `0` and the
parameter in slot `1`. -/
def posB (w : RestB) (j : CsIdx) : Z :=
  capOf w.1 w.2.1 w.2.2.1 (skCell (trunc128 w.2.2.2.2.2) (out256 w.2.2.2.2.1) (some j))

/-- Stage `B`'s shifts: the chain starts' rates. -/
def shB (w : RestB) (j : CsIdx) : X :=
  rateOf w.1 w.2.2.1 (skCell (trunc128 w.2.2.2.2.2) (out256 w.2.2.2.2.1) (some j))

theorem pos0_apply (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed) (u₁ : X)
    (u₂ : CsIdx → X) : pos0 (k, k', π, S₀, u₁, u₂) = capOf k k' π (seedCell S₀) :=
  rfl

theorem sh0_apply (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed) (u₁ : X)
    (u₂ : CsIdx → X) : sh0 (k, k', π, S₀, u₁, u₂) = rateOf k π (seedCell S₀) :=
  rfl

theorem posA_apply (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed) (u₀ : X)
    (u₂ : CsIdx → X) : posA (k, k', π, S₀, u₀, u₂) = capOf k k' π (skCell 0 (out256 u₀) none) :=
  rfl

theorem shA_apply (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed) (u₀ : X)
    (u₂ : CsIdx → X) : shA (k, k', π, S₀, u₀, u₂) = rateOf k π (skCell 0 (out256 u₀) none) :=
  rfl

/-- **Stage `0`**: the seed derivation's capacity takes slot `0`, which takes its output. -/
def stage0 : Tab ≃ Tab :=
  (shuf0.trans (stage1 pos0 sh0)).trans shuf0.symm

/-- **Stage `A`**: the parameter derivation's capacity takes slot `1`, which takes its output. -/
def stageA : Tab ≃ Tab :=
  (shufA.trans (stage1 posA shA)).trans shufA.symm

/-- **Stage `B`**: the chain starts' capacities take the slots `2`, which take their outputs, when
the capacities are distinct. -/
noncomputable def stageB : Tab ≃ Tab :=
  (shufB.trans (stageN posB shB)).trans shufB.symm

theorem stage0_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (u₀ u₁ : X) (u₂ : CsIdx → X) :
    stage0 (⟨(h, k, k'), π, S₀⟩, (u₀, u₁, u₂)) =
      (⟨(Function.update h (capOf k k' π (seedCell S₀)) u₀, k, k'), π, S₀⟩,
        (rateOf k π (seedCell S₀) + h (capOf k k' π (seedCell S₀)), u₁, u₂)) := by
  rw [stage0, Equiv.trans_apply, Equiv.trans_apply, shuf0_apply, stage1_apply, shuf0_symm_apply,
    pos0_apply, sh0_apply]

theorem stageA_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (u₀ u₁ : X) (u₂ : CsIdx → X) :
    stageA (⟨(h, k, k'), π, S₀⟩, (u₀, u₁, u₂)) =
      (⟨(Function.update h (capOf k k' π (skCell 0 (out256 u₀) none)) u₁, k, k'), π, S₀⟩,
        (u₀, rateOf k π (skCell 0 (out256 u₀) none) +
          h (capOf k k' π (skCell 0 (out256 u₀) none)), u₂)) := by
  rw [stageA, Equiv.trans_apply, Equiv.trans_apply, shufA_apply, stage1_apply, shufA_symm_apply,
    posA_apply, shA_apply]

theorem shufB_apply (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (u₀ u₁ : X) (u₂ : CsIdx → X) :
    shufB (⟨(h, k, k'), π, S₀⟩, (u₀, u₁, u₂)) = ((h, u₂), (k, k', π, S₀, u₀, u₁)) :=
  rfl

theorem posB_apply (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed) (u₀ u₁ : X)
    (j : CsIdx) :
    posB (k, k', π, S₀, u₀, u₁) j = capOf k k' π (skCell (trunc128 u₁) (out256 u₀) (some j)) :=
  rfl

theorem shB_apply (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed) (u₀ u₁ : X)
    (j : CsIdx) :
    shB (k, k', π, S₀, u₀, u₁) j = rateOf k π (skCell (trunc128 u₁) (out256 u₀) (some j)) :=
  rfl

/-- Stage `B` keeps `k`, `k'`, `π`, `S₀` and the slots `0` and `1`. -/
theorem stageB_exists (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed)
    (u₀ u₁ : X) (u₂ : CsIdx → X) : ∃ (h' : Z → X) (u₂' : CsIdx → X),
    stageB (⟨(h, k, k'), π, S₀⟩, (u₀, u₁, u₂)) = (⟨(h', k, k'), π, S₀⟩, (u₀, u₁, u₂')) := by
  rw [stageB, Equiv.trans_apply, Equiv.trans_apply, shufB_apply, stageN_eq_mk, shufB_symm_apply]
  exact ⟨_, _, rfl⟩

/-- Stage `B` when the chain starts' capacities are distinct. -/
theorem stageB_apply_of_injective (h : Z → X) (k k' : X → Z) (π : Equiv.Perm (X × Z))
    (S₀ : MasterSeed) (u₀ u₁ : X) (u₂ : CsIdx → X)
    (hinj : Function.Injective (posB (k, k', π, S₀, u₀, u₁))) :
    stageB (⟨(h, k, k'), π, S₀⟩, (u₀, u₁, u₂)) =
      (⟨((xch (posB (k, k', π, S₀, u₀, u₁)) hinj (shB (k, k', π, S₀, u₀, u₁)) (h, u₂)).1, k, k'),
        π, S₀⟩,
        (u₀, u₁,
          (xch (posB (k, k', π, S₀, u₀, u₁)) hinj (shB (k, k', π, S₀, u₀, u₁)) (h, u₂)).2)) := by
  rw [stageB, Equiv.trans_apply, Equiv.trans_apply, shufB_apply,
    stageN_apply_of_injective _ _ _ _ hinj, shufB_symm_apply]

/-- The scheme seed's slot split into the scheme seed (its first `256` bits) and the rest. -/
def seedSlotEquiv : X ≃ MasterSeed × (Fin 832 → ZMod 2) :=
  (Fin.appendEquiv 256 832).symm.trans ((bitsEquiv 256).symm.prodCongr (Equiv.refl _))

theorem seedSlotEquiv_fst (v : X) : (seedSlotEquiv v).1 = out256 v :=
  rfl

/-- The scheme seed split off slot `0`. -/
def splitSeed : Tab ≃ Pub × MasterSeed where
  toFun t := ((t.1, (seedSlotEquiv t.2.1).2, t.2.2.1, t.2.2.2), (seedSlotEquiv t.2.1).1)
  invFun p := (p.1.1, seedSlotEquiv.symm (p.2, p.1.2.1), p.1.2.2.1, p.1.2.2.2)
  left_inv t := by
    obtain ⟨L, u₀, u₁, u₂⟩ := t
    simp only [Prod.mk.eta, Equiv.symm_apply_apply]
  right_inv p := by
    obtain ⟨⟨L, r, u₁, u₂⟩, S⟩ := p
    simp only [Equiv.apply_symm_apply]

theorem splitSeed_apply (L : HonestTable) (u₀ u₁ : X) (u₂ : CsIdx → X) :
    splitSeed (L, (u₀, u₁, u₂)) = ((L, (seedSlotEquiv u₀).2, u₁, u₂), out256 u₀) :=
  rfl

/-- **The staged swap**: the table with its extra slots as the public part and the scheme seed. -/
noncomputable def schemeSplit : Tab ≃ Pub × MasterSeed :=
  stage0.trans (stageA.trans (stageB.trans splitSeed))

theorem schemeSplit_apply (t : Tab) : schemeSplit t = splitSeed (stageB (stageA (stage0 t))) :=
  rfl

/-! ### The transfer facts -/

/-- The parameter read off the public part. -/
def pubParam (p : Pub) : PublicParameter :=
  trunc128 p.2.2.1

/-- The chain starts' hashes read off the public part. -/
def pubCs (p : Pub) (j : CsIdx) : HashOutput :=
  out256 (p.2.2.2 j)

/-- The hidden capacities: the seed derivation's (`none`) and the seed-keyed cells'. -/
def posOf (p : Pub) (S : MasterSeed) (a : Option (Option CsIdx)) : Z :=
  capOf p.1.keys.2.1 p.1.keys.2.2 p.1.perm (hidCell (pubParam p) S p.1.masterSeed a)

/-- The hash of a chain start's derivation. -/
def csHash (L : HonestTable) (j : CsIdx) : HashOutput :=
  L.hash (csInput L.param L.seed j)

theorem chainStart_eq_csHash (L : HonestTable) (l : Layer) (e : KeyIndex) (i : ChainIndex) :
    L.chainStart l e i = hashHalfForChain i.val (csHash L (l, e, chainPair i)) :=
  rfl

theorem param_eq (L : HonestTable) : L.param = truncateHash (L.hash (paramInput L.seed)) :=
  rfl

theorem seedRound_eq (k k' : X → Z) (π : Equiv.Perm (X × Z)) (S₀ : MasterSeed) :
    seedRound k k' π S₀ = (rateOf k π (seedCell S₀), capOf k k' π (seedCell S₀)) :=
  rfl

theorem skCell_none (P : PublicParameter) (S : MasterSeed) :
    skCell P S none = firstCell (paramInput S) :=
  rfl

theorem skCell_some (P : PublicParameter) (S : MasterSeed) (j : CsIdx) :
    skCell P S (some j) = firstCell (csInput P S j) :=
  rfl

/-- The seed derivation's capacity. -/
def cap0 (t : Tab) : Z :=
  capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm (seedCell t.1.masterSeed)

/-- Slot `0` after stage `0`: the seed derivation's output. -/
def slot0 (t : Tab) : X :=
  rateOf t.1.keys.2.1 t.1.perm (seedCell t.1.masterSeed) + t.1.keys.1 (cap0 t)

/-- The parameter derivation's capacity, for the scheme seed in slot `0`. -/
def capP (t : Tab) : Z :=
  capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm (skCell 0 (out256 (slot0 t)) none)

/-- Slot `1` after stage `A`: the parameter derivation's output. -/
def slot1 (t : Tab) : X :=
  rateOf t.1.keys.2.1 t.1.perm (skCell 0 (out256 (slot0 t)) none) +
    Function.update t.1.keys.1 (cap0 t) t.2.1 (capP t)

/-- `h` after stage `A`. -/
def hA (t : Tab) : Z → X :=
  Function.update (Function.update t.1.keys.1 (cap0 t) t.2.1) (capP t) t.2.2.1

/-- The data stage `B` sees after stages `0` and `A`. -/
abbrev wB (t : Tab) : RestB :=
  (t.1.keys.2.1, t.1.keys.2.2, t.1.perm, t.1.masterSeed, slot0 t, slot1 t)

theorem stageA_stage0 (t : Tab) : stageA (stage0 t) =
    (⟨(hA t, t.1.keys.2.1, t.1.keys.2.2), t.1.perm, t.1.masterSeed⟩,
      (slot0 t, slot1 t, t.2.2.2)) := by
  obtain ⟨⟨⟨h, k, k'⟩, π, S₀⟩, u₀, u₁, u₂⟩ := t
  rw [stage0_apply, stageA_apply]
  rfl

/-- After stage `0`, slot `0` holds the scheme seed. -/
theorem out256_slot0 (t : Tab) : out256 (slot0 t) = t.1.seed := by
  simp only [seed_eq_seedRound, seedRound_eq, slot0, cap0]

theorem schemeSplit_exists (t : Tab) : ∃ (h' : Z → X) (u₂' : CsIdx → X),
    schemeSplit t = ((⟨(h', t.1.keys.2.1, t.1.keys.2.2), t.1.perm, t.1.masterSeed⟩,
      (seedSlotEquiv (slot0 t)).2, slot1 t, u₂'), t.1.seed) := by
  obtain ⟨h', u₂', hB⟩ := stageB_exists (hA t) t.1.keys.2.1 t.1.keys.2.2 t.1.perm t.1.masterSeed
    (slot0 t) (slot1 t) t.2.2.2
  refine ⟨h', u₂', ?_⟩
  rw [schemeSplit_apply, stageA_stage0, hB, splitSeed_apply, out256_slot0]

/-- The staged swap when the chain starts' capacities are distinct. -/
theorem schemeSplit_of_injective (t : Tab) (hinj : Function.Injective (posB (wB t))) :
    schemeSplit t = ((⟨((xch (posB (wB t)) hinj (shB (wB t)) (hA t, t.2.2.2)).1, t.1.keys.2.1,
      t.1.keys.2.2), t.1.perm, t.1.masterSeed⟩, (seedSlotEquiv (slot0 t)).2, slot1 t,
      (xch (posB (wB t)) hinj (shB (wB t)) (hA t, t.2.2.2)).2), t.1.seed) := by
  rw [schemeSplit_apply, stageA_stage0, stageB_apply_of_injective _ _ _ _ _ _ _ _ hinj,
    splitSeed_apply, out256_slot0]

/-- **The hidden coordinate is the scheme seed.** -/
theorem schemeSplit_snd (t : Tab) : (schemeSplit t).2 = t.1.seed := by
  obtain ⟨_, _, he⟩ := schemeSplit_exists t
  rw [he]

theorem schemeSplit_keys_snd (t : Tab) : (schemeSplit t).1.1.keys.2 = t.1.keys.2 := by
  obtain ⟨_, _, he⟩ := schemeSplit_exists t
  rw [he]

theorem schemeSplit_perm (t : Tab) : (schemeSplit t).1.1.perm = t.1.perm := by
  obtain ⟨_, _, he⟩ := schemeSplit_exists t
  rw [he]

theorem schemeSplit_masterSeed (t : Tab) : (schemeSplit t).1.1.masterSeed = t.1.masterSeed := by
  obtain ⟨_, _, he⟩ := schemeSplit_exists t
  rw [he]

theorem pubParam_schemeSplit (t : Tab) : pubParam (schemeSplit t).1 = trunc128 (slot1 t) := by
  obtain ⟨_, _, he⟩ := schemeSplit_exists t
  rw [he]
  rfl

theorem posOf_schemeSplit (t : Tab) (a : Option (Option CsIdx)) :
    posOf (schemeSplit t).1 (schemeSplit t).2 a = capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
      (hidCell (trunc128 (slot1 t)) t.1.seed t.1.masterSeed a) := by
  obtain ⟨_, _, he⟩ := schemeSplit_exists t
  rw [he]
  rfl

/-- **The transfer facts**: when the hidden capacities are distinct, the public part gives the
parameter, the chain starts' hashes, and `h` off the hidden capacities. -/
theorem schemeSplit_transfer (t : Tab)
    (hinj : Function.Injective (posOf (schemeSplit t).1 (schemeSplit t).2)) :
    pubParam (schemeSplit t).1 = t.1.param ∧ pubCs (schemeSplit t).1 = csHash t.1 ∧
      ∀ z, (∀ a, posOf (schemeSplit t).1 (schemeSplit t).2 a ≠ z) →
        (schemeSplit t).1.1.keys.1 z = t.1.keys.1 z := by
  have hpos := posOf_schemeSplit t
  have hinj' : Function.Injective fun a ↦ capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
      (hidCell (trunc128 (slot1 t)) t.1.seed t.1.masterSeed a) :=
    fun a b hab ↦ hinj ((hpos a).trans (hab.trans (hpos b).symm))
  have hz0P : capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm (firstCell (paramInput t.1.seed)) ≠
      capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm (seedCell t.1.masterSeed) := fun h ↦
    absurd (hinj' (a₁ := some none) (a₂ := none) h) (by simp)
  have hslot : slot1 t = rateOf t.1.keys.2.1 t.1.perm (firstCell (paramInput t.1.seed)) +
      t.1.keys.1 (capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm (firstCell (paramInput t.1.seed))) := by
    rw [slot1, capP, out256_slot0, skCell_none, cap0, Function.update_of_ne hz0P]
  have hP : trunc128 (slot1 t) = t.1.param := by
    rw [hslot, param_eq, hash_of_lt t.1 (paramInput t.1.seed)
      (by rw [length_paramInput]; norm_num), trunc128]
  have hh₁ : hA t = Function.update (Function.update t.1.keys.1
      (capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm (seedCell t.1.masterSeed)) t.2.1)
      (capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm (firstCell (paramInput t.1.seed))) t.2.2.1 := by
    rw [hA, capP, out256_slot0, skCell_none, cap0]
  have hBpos : ∀ j, posB (wB t) j = capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
      (skCell (trunc128 (slot1 t)) t.1.seed (some j)) := fun j ↦ by
    rw [posB_apply, out256_slot0]
  have hBsh : ∀ j, shB (wB t) j =
      rateOf t.1.keys.2.1 t.1.perm (skCell (trunc128 (slot1 t)) t.1.seed (some j)) := fun j ↦ by
    rw [shB_apply, out256_slot0]
  have hBinj : Function.Injective (posB (wB t)) := fun j j' hj ↦ by
    rw [hBpos, hBpos] at hj
    exact Option.some_injective _ (Option.some_injective _
      (hinj' (a₁ := some (some j)) (a₂ := some (some j')) hj))
  have hsplit := schemeSplit_of_injective t hBinj
  have hne0 : ∀ j, capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
      (skCell (trunc128 (slot1 t)) t.1.seed (some j)) ≠
      capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm (seedCell t.1.masterSeed) := fun j h ↦
    absurd (hinj' (a₁ := some (some j)) (a₂ := none) h) (by simp)
  have hneP : ∀ j, capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
      (skCell (trunc128 (slot1 t)) t.1.seed (some j)) ≠
      capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm (firstCell (paramInput t.1.seed)) := fun j h ↦
    absurd (hinj' (a₁ := some (some j)) (a₂ := some none) h) (by simp)
  refine ⟨(pubParam_schemeSplit t).trans hP, funext fun j ↦ ?_, fun z hz ↦ ?_⟩
  · rw [hsplit]
    show out256 ((xch (posB (wB t)) hBinj (shB (wB t)) (hA t, t.2.2.2)).2 j) = _
    rw [xch_snd_mk, hBpos, hBsh, hh₁, Function.update_of_ne (hneP j),
      Function.update_of_ne (hne0 j), csHash,
      hash_of_lt t.1 (csInput t.1.param t.1.seed j) (by rw [length_csInput]; norm_num), ← hP]
    rfl
  · have hz' : ∀ a, capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm
        (hidCell (trunc128 (slot1 t)) t.1.seed t.1.masterSeed a) ≠ z :=
      fun a ↦ (hpos a).symm.trans_ne (hz a)
    have hzP : z ≠ capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm (firstCell (paramInput t.1.seed)) :=
      (hz' (some none)).symm
    have hz0 : z ≠ capOf t.1.keys.2.1 t.1.keys.2.2 t.1.perm (seedCell t.1.masterSeed) :=
      (hz' none).symm
    rw [hsplit]
    show (xch (posB (wB t)) hBinj (shB (wB t)) (hA t, t.2.2.2)).1 z = _
    rw [xch_fst_mk_of_notMem _ _ _ _ _ fun j ↦ (hBpos j).trans_ne (hz' (some (some j))), hh₁,
      Function.update_of_ne hzP, Function.update_of_ne hz0]

/-! ### The challenger's data and the good set -/

variable {ι : Type} {β : ι → Type}

/-- **The challenger's honest data**: the honest evaluations of hash computations `Q i` of the
parameter and the chain starts' hashes. -/
def schemeData (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (L : HonestTable) : ∀ i, β i × List (SpongeRead X Z) :=
  fun i ↦ honestEval L.keys L.perm (Q i L.param (csHash L))

/-- The same computations from the public part. -/
def pubData (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (p : Pub) : ∀ i, β i × List (SpongeRead X Z) :=
  fun i ↦ honestEval p.1.keys p.1.perm (Q i (pubParam p) (pubCs p))

/-- Good coordinates: distinct hidden capacities, none read by the computations from the public
part. -/
def GoodPS (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (x : Pub × MasterSeed) : Prop :=
  Function.Injective (posOf x.1 x.2) ∧ ∀ i a, posOf x.1 x.2 a ∉ hCells (pubData Q x.1 i).2

open scoped Classical in
/-- **The good set** of the staged swap. Irreducible: its membership does not unfold to the
enumeration of all tables. -/
@[irreducible]
noncomputable def schemeGood
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) : Finset Tab :=
  Finset.univ.filter fun t ↦ GoodPS Q (schemeSplit t)

theorem mem_schemeGood
    {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)} {t : Tab} :
    t ∈ schemeGood Q ↔ GoodPS Q (schemeSplit t) := by
  unfold schemeGood
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **On the good set, the challenger's data is a function of the public part.** -/
theorem schemeData_eq_of_mem
    {Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)} {t : Tab}
    (ht : t ∈ schemeGood Q) : schemeData Q t.1 = pubData Q (schemeSplit t).1 := by
  obtain ⟨hinj, hread⟩ := mem_schemeGood.mp ht
  obtain ⟨hP, hC, hh⟩ := schemeSplit_transfer t hinj
  funext i
  have hr := hread i
  change ∀ a, posOf _ _ a ∉ hCells (honestEval (schemeSplit t).1.1.keys (schemeSplit t).1.1.perm
    (Q i (pubParam (schemeSplit t).1) (pubCs (schemeSplit t).1))).2 at hr
  change honestEval t.1.keys t.1.perm (Q i t.1.param (csHash t.1)) =
    honestEval (schemeSplit t).1.1.keys (schemeSplit t).1.1.perm
      (Q i (pubParam (schemeSplit t).1) (pubCs (schemeSplit t).1))
  rw [hP, hC, schemeSplit_perm] at hr ⊢
  refine honestEval_congr (t := (schemeSplit t).1.1.keys) (t' := t.1.keys) t.1.perm _
    fun e he ↦ ?_
  have ha := honestEval_answeredBy t.1.perm (schemeSplit t).1.1.keys _ e he
  cases e with
  | h z a =>
    have hz : ∀ b, posOf (schemeSplit t).1 (schemeSplit t).2 b ≠ z :=
      fun b hb ↦ hr b (mem_hCells.mpr ⟨a, hb ▸ he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← hh z hz]
    exact ha
  | k x a =>
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← schemeSplit_keys_snd t]
    exact ha
  | k' x a =>
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [← schemeSplit_keys_snd t]
    exact ha

/-! ### The bad fraction -/

open scoped Classical

variable (G : ℕ)

/-- A good permutation and colliding hidden capacities. -/
noncomputable def collInd (x : Pub × MasterSeed) : ℕ :=
  if PermGood x.1.1.perm G ∧ ¬Function.Injective (posOf x.1 x.2) then 1 else 0

/-- A good permutation and a computation reading `h` at the hidden capacity `a`. -/
noncomputable def hitInd
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (i : ι)
    (a : Option (Option CsIdx)) (x : Pub × MasterSeed) : ℕ :=
  if PermGood x.1.1.perm G ∧ posOf x.1 x.2 a ∈ hCells (pubData Q x.1 i).2 then 1 else 0

/-- The coordinates other than `k`, `k'` and one seed: `π`, `h`, the public slots, and the other
seed. -/
abbrev Coord : Type :=
  Equiv.Perm (X × Z) × (Z → X) × ((Fin 832 → ZMod 2) × X × (CsIdx → X)) × MasterSeed

/-- Coordinates with the scheme seed `S` second (and `S₀` in `Coord`). -/
def coordS : ((Coord × MasterSeed) × (X → Z)) × (X → Z) ≃ Pub × MasterSeed where
  toFun c := ((⟨(c.1.1.1.2.1, c.1.2, c.2), c.1.1.1.1, c.1.1.1.2.2.2⟩, c.1.1.1.2.2.1), c.1.1.2)
  invFun x := ((((x.1.1.perm, x.1.1.keys.1, x.1.2, x.1.1.masterSeed), x.2), x.1.1.keys.2.1),
    x.1.1.keys.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coordinates with the master seed `S₀` second (and `S` in `Coord`). -/
def coord0 : ((Coord × MasterSeed) × (X → Z)) × (X → Z) ≃ Pub × MasterSeed where
  toFun c := ((⟨(c.1.1.1.2.1, c.1.2, c.2), c.1.1.1.1, c.1.1.2⟩, c.1.1.1.2.2.1), c.1.1.1.2.2.2)
  invFun x := ((((x.1.1.perm, x.1.1.keys.1, x.1.2, x.2), x.1.1.masterSeed), x.1.1.keys.2.1),
    x.1.1.keys.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_tab_eq : Fintype.card Tab = Fintype.card Coord * Fintype.card MasterSeed *
    (Fintype.card (X → Z) * Fintype.card (X → Z)) := by
  rw [Fintype.card_congr schemeSplit, card_eq_coords coordS]

/-- The computation `Q i` of the public slots in coordinates. -/
def coordQ (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) (i : ι)
    (ω : Coord) : OracleComp HashSpec (β i) :=
  Q i (trunc128 ω.2.2.1.2.1) fun j ↦ out256 (ω.2.2.1.2.2 j)

/-- Its reads with the keys `ω.2.1, k, k'`, with their bound. -/
def coordR (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (q : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (i : ι) (k k' : X → Z) (ω : Coord) : {r : List (SpongeRead X Z) // r.length ≤ q i} :=
  ⟨(honestEval (ω.2.1, k, k') ω.1 (coordQ Q i ω)).2, hq i _ _ _ _⟩

theorem coordR_update_k
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (q : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (i : ι) (k k' : X → Z) (ω : Coord) (x : X) (w : Z)
    (hx : x ∉ kCells (coordR Q q hq i (Function.update k x w) k' ω).1) :
    coordR Q q hq i (Function.update k x w) k' ω = coordR Q q hq i k k' ω :=
  Subtype.ext (congrArg Prod.snd
    (honestEval_update_k_of_not_mem (coordQ Q i ω) ω.1 ω.2.1 k k' hx))

theorem coordR_update_k'
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (q : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (i : ι) (k k' : X → Z) (ω : Coord) (x : X) (a : Z)
    (hx : x ∉ k'Cells (coordR Q q hq i k (Function.update k' x a) ω).1) :
    coordR Q q hq i k (Function.update k' x a) ω = coordR Q q hq i k k' ω :=
  Subtype.ext (congrArg Prod.snd
    (honestEval_update_k'_of_not_mem (coordQ Q i ω) ω.1 ω.2.1 k k' hx))

theorem collInd_coordS (ω : Coord) (S : MasterSeed) (k k' : X → Z) :
    collInd G (coordS (((ω, S), k), k')) =
      (if PermGood ω.1 G ∧ ¬Function.Injective (fun a ↦ capOf k k' ω.1
        (hidCell (trunc128 ω.2.2.1.2.1) S ω.2.2.2 a)) then 1 else 0) :=
  rfl

theorem card_mul_sum_coordS_collInd :
    Fintype.card Z * ∑ ω : Coord, ∑ S : MasterSeed, ∑ k : X → Z, ∑ k' : X → Z,
        collInd G (coordS (((ω, S), k), k')) =
      ∑ ω : Coord, ∑ S : MasterSeed, Fintype.card Z * ∑ k : X → Z, ∑ k' : X → Z,
        (if PermGood ω.1 G ∧ ¬Function.Injective (fun a ↦ capOf k k' ω.1
          (hidCell (trunc128 ω.2.2.1.2.1) S ω.2.2.2 a)) then 1 else 0) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  simp only [collInd_coordS]

/-- **Collisions**: at most `|A|² (G + 1) / |Z|` of the coordinates have a good permutation and
colliding hidden capacities. -/
theorem card_mul_sum_collInd_le :
    Fintype.card Z * ∑ x, collInd G x ≤ Fintype.card Tab *
      (Fintype.card (Option (Option CsIdx)) * Fintype.card (Option (Option CsIdx)) * (G + 1)) := by
  rw [sum_eq_sum_coords coordS (collInd G), card_tab_eq, card_mul_sum_coordS_collInd]
  exact sum_sum_le_mul _ _ _ fun ω S ↦
    card_mul_sum_not_injective_capOf_le ω.1 G _ (hidCell_injective _ S ω.2.2.2)

/-- **The seed derivation's capacity is rarely read**: at most `qs₀ / 2^256 + (G + 1) q / |Z|`. -/
theorem sum_hitInd_none_le
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (q qs₀ : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs₀ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter SeedShaped).card ≤ qs₀ i) (i : ι) :
    ((∑ x, hitInd G Q i none x : ℕ) : ℝ≥0∞) ≤
      Fintype.card Tab * ((qs₀ i : ℝ≥0∞) / 2 ^ 256 + (G + 1) * q i / Fintype.card Z) := by
  have h := sum_capOf_mem_le (Ω := Coord) (Sd := MasterSeed) (A := Unit) (fun ω ↦ ω.1)
    (fun _ _ s ↦ seedCell s) (coordR Q q hq i) (fun r ↦ kCells r.1) (fun r ↦ k'Cells r.1)
    (fun r ↦ hCells r.1) (coordR_update_k Q q hq i) (coordR_update_k' Q q hq i) G (q i) (qs₀ i)
    (fun r ↦ (card_k'Cells_le r.1).trans r.2) (fun r ↦ (card_hCells_le r.1).trans r.2)
    (fun k k' ω ↦ by
      simp only [Fintype.sum_unique]
      exact (sum_ite_mem_le_card_filter seedCell seedCell_injective _ SeedShaped
        seedShaped_seedCell).trans (hqs₀ i _ _ _ _))
  simp only [Fintype.sum_unique] at h
  calc ((∑ x, hitInd G Q i none x : ℕ) : ℝ≥0∞)
      = ((∑ ω : Coord, ∑ s : MasterSeed, ∑ k : X → Z, ∑ k' : X → Z,
          hitInd G Q i none (coord0 (((ω, s), k), k')) : ℕ) : ℝ≥0∞) := by
        rw [sum_eq_sum_coords coord0 (hitInd G Q i none)]
    _ ≤ _ := h
    _ = _ := by
        rw [card_tab_eq, card_masterSeed, Fintype.card_unit, Nat.cast_one, one_mul, Nat.cast_pow,
          Nat.cast_ofNat]

/-- **The seed-keyed cells' capacities are rarely read**: at most
`qs₁ / 2^256 + |B| (G + 1) q / |Z|`, `B = Option CsIdx`. -/
theorem sum_hitInd_some_le
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (q qs₁ : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs₁ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs₁ i) (i : ι) :
    ((∑ b, ∑ x, hitInd G Q i (some b) x : ℕ) : ℝ≥0∞) ≤
      Fintype.card Tab * ((qs₁ i : ℝ≥0∞) / 2 ^ 256 +
        Fintype.card (Option CsIdx) * (G + 1) * q i / Fintype.card Z) := by
  have h := sum_capOf_mem_le (Ω := Coord) (Sd := MasterSeed) (A := Option CsIdx)
    (fun ω ↦ ω.1) (fun b ω S ↦ skCell (trunc128 ω.2.2.1.2.1) S b) (coordR Q q hq i)
    (fun r ↦ kCells r.1) (fun r ↦ k'Cells r.1) (fun r ↦ hCells r.1) (coordR_update_k Q q hq i)
    (coordR_update_k' Q q hq i) G (q i) (qs₁ i)
    (fun r ↦ (card_k'Cells_le r.1).trans r.2) (fun r ↦ (card_hCells_le r.1).trans r.2)
    (fun k k' ω ↦ by
      rw [← Fintype.sum_prod_type']
      exact (sum_ite_mem_le_card_filter (fun p : MasterSeed × Option CsIdx ↦
        skCell (trunc128 ω.2.2.1.2.1) p.1 p.2) (skCell_injective _) _
        (fun x ↦ ∃ S b, skCell (trunc128 ω.2.2.1.2.1) S b = x)
        fun p ↦ ⟨p.1, p.2, rfl⟩).trans (hqs₁ i _ _ _ _))
  calc ((∑ b, ∑ x, hitInd G Q i (some b) x : ℕ) : ℝ≥0∞)
      = ((∑ ω : Coord, ∑ s : MasterSeed, ∑ b : Option CsIdx, ∑ k : X → Z, ∑ k' : X → Z,
          hitInd G Q i (some b) (coordS (((ω, s), k), k')) : ℕ) : ℝ≥0∞) := by
        refine congrArg Nat.cast ?_
        rw [← sum_comm_three]
        exact Finset.sum_congr rfl fun b _ ↦ sum_eq_sum_coords coordS (hitInd G Q i (some b))
    _ ≤ _ := h
    _ = _ := by
        rw [card_tab_eq, card_masterSeed, Nat.cast_pow, Nat.cast_ofNat]

/-- The tables outside the good set: a bad permutation, a collision, or a read hit. -/
theorem card_sub_card_schemeGood_le [Fintype ι]
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i)) :
    Fintype.card Tab - (schemeGood Q).card ≤
      (∑ t : Tab, if ¬PermGood t.1.perm G then 1 else 0) +
        ((∑ x, collInd G x) +
          ∑ i, ((∑ x, hitInd G Q i none x) + ∑ b, ∑ x, hitInd G Q i (some b) x)) := by
  refine (card_sub_card_le_sum (schemeGood Q) (fun t ↦ (if ¬PermGood t.1.perm G then 1 else 0) +
    (collInd G (schemeSplit t) + ∑ i, (hitInd G Q i none (schemeSplit t) +
      ∑ b, hitInd G Q i (some b) (schemeSplit t)))) fun t ht ↦ ?_).trans_eq ?_
  · by_cases hG : PermGood t.1.perm G
    · have hG' : PermGood (schemeSplit t).1.1.perm G := by rw [schemeSplit_perm]; exact hG
      rw [mem_schemeGood] at ht
      by_cases hinj : Function.Injective (posOf (schemeSplit t).1 (schemeSplit t).2)
      · obtain ⟨i, a, ha⟩ : ∃ i a, posOf (schemeSplit t).1 (schemeSplit t).2 a ∈
            hCells (pubData Q (schemeSplit t).1 i).2 := by
          by_contra hne
          exact ht ⟨hinj, fun i a ha ↦ hne ⟨i, a, ha⟩⟩
        have h1 : 1 ≤ hitInd G Q i a (schemeSplit t) := by
          rw [hitInd, ite_eq_left (And.intro hG' ha)]
        have h2 : hitInd G Q i none (schemeSplit t) + ∑ b, hitInd G Q i (some b) (schemeSplit t) ≤
            ∑ i', (hitInd G Q i' none (schemeSplit t) +
              ∑ b, hitInd G Q i' (some b) (schemeSplit t)) :=
          Finset.single_le_sum (f := fun i' ↦ hitInd G Q i' none (schemeSplit t) +
            ∑ b, hitInd G Q i' (some b) (schemeSplit t)) (fun _ _ ↦ Nat.zero_le _)
            (Finset.mem_univ i)
        have h3 : 1 ≤ hitInd G Q i none (schemeSplit t) +
            ∑ b, hitInd G Q i (some b) (schemeSplit t) := by
          cases a with
          | none => omega
          | some b =>
            have h4 : hitInd G Q i (some b) (schemeSplit t) ≤
                ∑ b', hitInd G Q i (some b') (schemeSplit t) :=
              Finset.single_le_sum (f := fun b' ↦ hitInd G Q i (some b') (schemeSplit t))
                (fun _ _ ↦ Nat.zero_le _) (by simp)
            omega
        omega
      · have h1 : collInd G (schemeSplit t) = 1 := by
          rw [collInd, ite_eq_left (And.intro hG' hinj)]
        omega
    · have h1 : (if ¬PermGood t.1.perm G then 1 else 0) = 1 := ite_eq_left hG
      omega
  · rw [Finset.sum_add_distrib]
    refine congrArg (HAdd.hAdd _) ?_
    rw [Fintype.sum_equiv schemeSplit (fun t ↦ collInd G (schemeSplit t) +
        ∑ i, (hitInd G Q i none (schemeSplit t) + ∑ b, hitInd G Q i (some b) (schemeSplit t)))
      (fun x ↦ collInd G x + ∑ i, (hitInd G Q i none x + ∑ b, hitInd G Q i (some b) x))
      fun _ ↦ rfl, Finset.sum_add_distrib (f := collInd G),
      Finset.sum_comm (f := fun x i ↦ hitInd G Q i none x + ∑ b, hitInd G Q i (some b) x)]
    refine congrArg (HAdd.hAdd _) ?_
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun x b ↦ hitInd G Q i (some b) x)]

/-- The tables with a bad permutation are the fraction of bad permutations. -/
theorem card_mul_sum_tab_not_permGood :
    Fintype.card (Equiv.Perm (X × Z)) * ∑ t : Tab, (if ¬PermGood t.1.perm G then 1 else 0) =
      Fintype.card Tab *
        (Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card :=
  card_mul_sum_fst_eq (γ := SeedSlots) (fun L : HonestTable ↦ if ¬PermGood L.perm G then 1 else 0)
    _ _ (card_mul_sum_not_permGood G)

/-- **The bad fraction of the staged swap**: the fraction of tables outside `schemeGood Q` is at
most the fraction of permutations with a rate count above `G`, plus the collisions
`|A|² (G + 1) / |Z|` (`A = Option (Option CsIdx)`), plus per computation
`qs₀ᵢ / 2^256 + (G + 1) qᵢ / |Z|` and `qs₁ᵢ / 2^256 + |B| (G + 1) qᵢ / |Z|` (`B = Option CsIdx`),
where `qᵢ` bounds the reads of `Q i`, `qs₀ᵢ` its reads at seed-shaped `k`-cells and `qs₁ᵢ` its reads
at seed-keyed cells. -/
theorem schemeGood_frac_le [Fintype ι]
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (q qs₀ qs₁ : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs₀ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter SeedShaped).card ≤ qs₀ i)
    (hqs₁ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs₁ i) :
    (Fintype.card Tab : ℝ≥0∞)⁻¹ * ((Fintype.card Tab - (schemeGood Q).card : ℕ) : ℝ≥0∞) ≤
      ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        ((Fintype.card (Option (Option CsIdx)) * Fintype.card (Option (Option CsIdx)) * (G + 1) :
          ℕ) : ℝ≥0∞) / Fintype.card Z +
        ∑ i, ((qs₀ i : ℝ≥0∞) / 2 ^ 256 + (G + 1) * q i / Fintype.card Z +
          ((qs₁ i : ℝ≥0∞) / 2 ^ 256 +
            Fintype.card (Option CsIdx) * (G + 1) * q i / Fintype.card Z)) := by
  exact inv_mul_le_of_parts Fintype.card_ne_zero (card_sub_card_schemeGood_le G Q)
    (natCast_le_mul_div_of_mul_le Fintype.card_ne_zero (card_mul_sum_tab_not_permGood G).le)
    (natCast_le_mul_div_of_mul_le Fintype.card_ne_zero (card_mul_sum_collInd_le G))
    (sum_hitInd_none_le G Q q qs₀ hq hqs₀) (sum_hitInd_some_le G Q q qs₁ hq hqs₁)

end split

/-! ## The scheme-seed cells, averaged over the table -/

section bound

open HashSig LeanXmss
open scoped Classical

variable {M : Type} [Fintype M] [DecidableEq M] {Λ : LocalSig.{u, v}} (I : Λ.Interp)
  {Ω : QReg → Type w} {A : QReg}

/-- **The scheme-seed cells, end to end.** Let the run of runtime 2 depend on the table only through
`π` and the challenger's honest data `schemeData Q` (computations of the parameter and the chain
starts' hashes, with at most `qᵢ` reads, `qs₀ᵢ` at seed-shaped and `qs₁ᵢ` at seed-keyed `k`-cells).
Then the mass of its `j`-th call at the cells `seedKeyCells S` of the scheme seed, averaged over the
uniform table, is at most `2^-256` plus the bad fraction of `schemeGood_frac_le`. -/
theorem avg_hiddenMass_schemeSeed_le_of_schemeData {ι : Type} [Fintype ι] {β : ι → Type} (G : ℕ)
    (Q : ∀ i, PublicParameter → (CsIdx → HashOutput) → OracleComp HashSpec (β i))
    (q qs₀ qs₁ : ι → ℕ)
    (hq : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput), (honestEval t π (Q i P Cs)).2.length ≤ q i)
    (hqs₀ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter SeedShaped).card ≤ qs₀ i)
    (hqs₁ : ∀ i (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (P : PublicParameter)
      (Cs : CsIdx → HashOutput),
      ((kCells (honestEval t π (Q i P Cs)).2).filter fun x ↦ ∃ S b, skCell P S b = x).card ≤
        qs₁ i)
    (m₀ : M)
    (y : Equiv.Perm (X × Z) → (∀ i, β i × List (SpongeRead X Z)) →
      QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρ : Equiv.Perm (X × Z) → (∀ i, β i × List (SpongeRead X Z)) →
      Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ π d, (ρ π d).PosSemidef) (hρ₁ : ∀ π d, ENNReal.ofReal (ρ π d).trace.re ≤ 1)
    (j : ℕ) :
    (Fintype.card HonestTable : ℝ≥0∞)⁻¹ * ∑ L : HonestTable, (runtime2 X Z m₀).queryWeight I
        (hiddenMass ∅ (seedKeyCells L.seed) ∅) (y L.perm (schemeData Q L))
        (ρ L.perm (schemeData Q L)) j ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ +
        (((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z)) +
          ((Fintype.card (Option (Option CsIdx)) * Fintype.card (Option (Option CsIdx)) *
            (G + 1) : ℕ) : ℝ≥0∞) / Fintype.card Z +
          ∑ i, ((qs₀ i : ℝ≥0∞) / 2 ^ 256 + (G + 1) * q i / Fintype.card Z +
            ((qs₁ i : ℝ≥0∞) / 2 ^ 256 +
              Fintype.card (Option CsIdx) * (G + 1) * q i / Fintype.card Z))) := by
  set F : HonestTable → ℝ≥0∞ := fun L ↦ (runtime2 X Z m₀).queryWeight I
    (hiddenMass ∅ (seedKeyCells L.seed) ∅) (y L.perm (schemeData Q L))
    (ρ L.perm (schemeData Q L)) j
  have h := avg_hiddenMass_schemeSeed_le I schemeSplit m₀
    (fun t : Tab ↦ y t.1.perm (schemeData Q t.1)) (fun t ↦ ρ t.1.perm (schemeData Q t.1))
    (fun _ ↦ hρ _ _) (fun _ ↦ hρ₁ _ _) (fun p ↦ y p.1.perm (pubData Q p))
    (fun p ↦ ρ p.1.perm (pubData Q p)) (fun _ ↦ hρ _ _) (fun _ ↦ hρ₁ _ _) (schemeGood Q)
    (fun t ht ↦ by
      rw [schemeData_eq_of_mem ht, schemeSplit_perm]
      exact ⟨rfl, rfl⟩) j
  have hs : ∑ t : Tab, (runtime2 X Z m₀).queryWeight I
      (hiddenMass ∅ (seedKeyCells (schemeSplit t).2) ∅) (y t.1.perm (schemeData Q t.1))
      (ρ t.1.perm (schemeData Q t.1)) j = ∑ t : Tab, F t.1 :=
    Finset.sum_congr rfl fun t _ ↦ congrArg (fun S ↦ (runtime2 X Z m₀).queryWeight I
      (hiddenMass ∅ (seedKeyCells S) ∅) (y t.1.perm (schemeData Q t.1))
      (ρ t.1.perm (schemeData Q t.1)) j) (schemeSplit_snd t)
  rw [hs, inv_card_mul_sum_fst F] at h
  exact h.trans (add_le_add_right (schemeGood_frac_le G Q q qs₀ qs₁ hq hqs₀ hqs₁) _)

end bound

end Quantum.Xmss.Hybrid

end
