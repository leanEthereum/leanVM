module

public import Quantum.Sphincs.Assembly.GoodTables

@[expose] public section

/-!
# leanSPHINCS's static fraction

The masked hybrid pays GoodTables' `staticFrac`: the fraction of ReparamFull's coordinates `YS`
whose template data fail `SphStatic` (HmsgCovers' `HStatic`, `TrialsOff` and ChgRevStatic's
`ChgStatic`). `HStatic` and `TrialsOff` depend on Reparam's public coordinates and values only.

* **Rates** (`frac_hRateBad_le`): the `H_msg` first blocks `(R, a)` are distinct
  (`dLabCell_injective`), so their rates collide for at most `|R × DLab|² / |X|` of `π`.
* **Capacities** (`frac_hCapBad_le`): at distinct rates the capacities are translates by the
  independent values of `k'` (ChgRevLoad's `blkCap`), so six of them share one for at most
  `|R × DLab|⁶ / |Z|⁵` of `k'` (`card_pow_mul_sum_not_capLoad5_le`).
* `frac_not_static_le_keccak`: with TrialsOff's `2^-400`, at most `2^-249` of `YS` fail any
  condition implied by `HStatic` and `TrialsOff`.
* `staticFrac_le` (Security's `hFrac`): with ChgRevStatic's `frac_chgStatic_le_keccak`
  (`2^-128 + 2^-199`), `staticFrac ≤ 2^-127`.
-/

open scoped ENNReal

open Quantum Quantum.Sponge Sphincs
open HashSig (Digest Message PublicParameter Randomizer)
open Quantum.Xmss (X Z)
open Quantum.Xmss.Hybrid (card_mul_sum_not_injective_rate_le card_mul_sum_equiv_prod_le
  natCast_le_mul_div_of_mul_le)
open Quantum.Xmss.Assembly (XW card_filter_le_add_of_imp inv_card_mul_card_filter_comp_fst
  rnCard_X rnCard_Z)
open Quantum.Sphincs.Hybrid (DLab dLabCell dLabCell_injective card_dLab)

namespace Quantum.Sphincs.Assembly

/-- A count of zeros (over abstract types: the kernel never multiplies concrete cards). -/
theorem mul_sum_le_of_eq_zero {P : Type*} [Fintype P] (c N d : ℕ) (F : P → ℕ)
    (h : ∀ p, F p = 0) : c * ∑ p, F p ≤ N * d := by
  rw [Finset.sum_eq_zero fun p _ ↦ h p, mul_zero]
  exact Nat.zero_le _

/-- A pointwise implication between filters of all points (over abstract types: no membership
binder over the concrete coordinates). -/
theorem card_filter_univ_le_of_imp {Y : Type*} [Fintype Y] (p q : Y → Prop) [DecidablePred p]
    [DecidablePred q] (h : ∀ y, p y → q y) :
    (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card :=
  Finset.card_le_card fun y hy ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact h y hy

/-- A union bound over two indicators (named, so that no instance or sum is unfolded). -/
theorem card_filter_le_sum_add_sum {Y : Type*} [Fintype Y] (P : Y → Prop) [DecidablePred P]
    (f g : Y → ℕ) (h : ∀ y, P y → 1 ≤ f y + g y) :
    (Finset.univ.filter P).card ≤ ∑ y, f y + ∑ y, g y := by
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  by_cases hP : P y
  · rw [ite_eq_left hP]
    exact h y hP
  · rw [ite_eq_right hP]
    exact Nat.zero_le _

/-! ## Six blocks at one capacity, over abstract types -/

section generic

variable {X Z B : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
  [Fintype B] [DecidableEq B]

/-- **At most five blocks share a capacity.** -/
def CapLoad5 (cap : B → Z) : Prop :=
  ∀ z : Z, ∃ T : Finset B, T.card ≤ 5 ∧ ∀ b, cap b = z → b ∈ T

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup Z] in
/-- **Six blocks at one capacity**: off `CapLoad5`, a block and five others at its capacity. -/
theorem exists_five_of_not_capLoad5 {cap : B → Z} (h : ¬CapLoad5 cap) :
    ∃ b₁, ∃ J ∈ (Finset.univ.erase b₁).powersetCard 5, ∀ b ∈ J, cap b = cap b₁ := by
  classical
  unfold CapLoad5 at h
  push Not at h
  obtain ⟨z, hz⟩ := h
  set F := Finset.univ.filter fun b ↦ cap b = z
  have h6 : 5 < F.card := by
    by_contra hc
    obtain ⟨b, hb, hbF⟩ := hz F (not_lt.mp hc)
    exact hbF (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
  obtain ⟨b₁, hb₁⟩ := Finset.card_pos.mp (Nat.zero_lt_of_lt h6)
  have he : 5 ≤ (F.erase b₁).card := by
    rw [Finset.card_erase_of_mem hb₁]
    omega
  obtain ⟨J, hJ, hJc⟩ := Finset.exists_subset_card_eq he
  have hz₁ : cap b₁ = z := (Finset.mem_filter.mp hb₁).2
  refine ⟨b₁, J, Finset.mem_powersetCard.mpr ⟨fun b hb ↦ ?_, hJc⟩, fun b hb ↦ ?_⟩
  · exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp (hJ hb)).1, Finset.mem_univ _⟩
  · rw [hz₁]
    exact (Finset.mem_filter.mp (Finset.mem_erase.mp (hJ hb)).2).2

/-- The capacity translate putting block `b` at block `b₁`'s capacity (a singleton). -/
def capSing (rate : B → X) (base : B → Z) (b₁ b : B) (g : X → Z) : Finset Z :=
  {blkCap rate base g b₁ - base b}

/-- **Six blocks at one capacity** at distinct rates: at most `|B|⁶ / |Z|⁵` of the functions. -/
theorem card_pow_mul_sum_not_capLoad5_le (rate : B → X) (base : B → Z)
    [∀ g : X → Z, Decidable (CapLoad5 (blkCap rate base g))] (hr : Function.Injective rate) :
    Fintype.card Z ^ 5 * ∑ g : X → Z, (if ¬CapLoad5 (blkCap rate base g) then 1 else 0) ≤
      Fintype.card (X → Z) * Fintype.card B ^ 6 := by
  set P : B → Finset (Finset B) := fun b₁ ↦ (Finset.univ.erase b₁).powersetCard 5 with hP
  set f : (X → Z) → B → Finset B → ℕ := fun g b₁ J ↦
    if ∀ b ∈ J, g (rate b) ∈ capSing rate base b₁ b g then 1 else 0
  have hpt : ∀ b₁, ∀ J ∈ P b₁, Fintype.card Z ^ 5 * ∑ g : X → Z, f g b₁ J ≤
      Fintype.card (X → Z) := by
    intro b₁ J hJ
    obtain ⟨hJs, hJc⟩ := Finset.mem_powersetCard.mp hJ
    have h' := card_pow_mul_sum_forall_le rate hr (capSing rate base b₁) 1 J
      (fun _ _ _ ↦ (Finset.card_singleton _).le) fun b _ b' hb' g w ↦ by
        have hne : rate b₁ ≠ rate b' := fun e ↦ (Finset.mem_erase.mp (hJs hb')).1 (hr e).symm
        unfold capSing
        rw [blkCap_update_of_ne rate base g hne]
    rw [hJc, one_pow, one_mul] at h'
    convert h'
  have hle : ∀ g : X → Z, (if ¬CapLoad5 (blkCap rate base g) then 1 else 0) ≤
      ∑ b₁, ∑ J ∈ P b₁, f g b₁ J := by
    intro g
    by_cases h : CapLoad5 (blkCap rate base g)
    · rw [ite_eq_right (not_not_intro h)]
      exact Nat.zero_le _
    · rw [ite_eq_left h]
      obtain ⟨b₁, J, hJ, hall⟩ := exists_five_of_not_capLoad5 h
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ b₁))
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hJ)
      have hm : ∀ b ∈ J, g (rate b) ∈ capSing rate base b₁ b g :=
        fun b hb ↦ Finset.mem_singleton.mpr ((blkCap_eq_iff' rate base g b _).mp (hall b hb))
      show 1 ≤ f g b₁ J
      exact (ite_eq_left hm).symm.le
  calc Fintype.card Z ^ 5 * ∑ g : X → Z, (if ¬CapLoad5 (blkCap rate base g) then 1 else 0)
      ≤ Fintype.card Z ^ 5 * ∑ g : X → Z, ∑ b₁, ∑ J ∈ P b₁, f g b₁ J :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum fun g _ ↦ hle g)
    _ = ∑ b₁, ∑ J ∈ P b₁, Fintype.card Z ^ 5 * ∑ g : X → Z, f g b₁ J := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b₁ _ ↦ Finset.sum_comm
    _ ≤ ∑ b₁, ∑ _J ∈ P b₁, Fintype.card (X → Z) :=
        Finset.sum_le_sum fun b₁ _ ↦ Finset.sum_le_sum fun J hJ ↦ hpt b₁ J hJ
    _ ≤ ∑ _b₁ : B, Fintype.card B ^ 5 * Fintype.card (X → Z) := by
        refine Finset.sum_le_sum fun b₁ _ ↦ ?_
        rw [Finset.sum_const, smul_eq_mul, hP, Finset.card_powersetCard]
        exact Nat.mul_le_mul_right _ ((Nat.choose_le_pow _ _).trans
          (Nat.pow_le_pow_left (Finset.card_le_univ _) _))
    _ = Fintype.card (X → Z) * Fintype.card B ^ 6 := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
        ring

end generic

/-! ## The `H_msg` static condition over Reparam's public coordinates and values -/

section hstatic

/-- Reparam's public coordinates `(h, PK.seed, π, k, k')` and its values. -/
abbrev YH : Type := ((Z → X) × XW) × (ValPos → Digest)

/-- The coordinates beside `π`. -/
abbrev RestPH : Type := ((Z → X) × PublicParameter × (X → Z) × (X → Z)) × (ValPos → Digest)

/-- The coordinates beside `k'`. -/
abbrev RestKH : Type :=
  ((Z → X) × PublicParameter × Equiv.Perm (X × Z) × (X → Z)) × (ValPos → Digest)

noncomputable instance instFintypeRestPH : Fintype RestPH :=
  instFintypeProd _ _

noncomputable instance instFintypeRestKH : Fintype RestKH :=
  instFintypeProd _ _

/-- The coordinates with `π` first. -/
def ePH : Equiv.Perm (X × Z) × RestPH ≃ YH where
  toFun c := ((c.2.1.1, c.2.1.2.1, c.1, c.2.1.2.2.1, c.2.1.2.2.2), c.2.2)
  invFun y := (y.1.2.2.1, ((y.1.1, y.1.2.1, y.1.2.2.2.1, y.1.2.2.2.2), y.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The coordinates with `k'` first. -/
def eKH : (X → Z) × RestKH ≃ YH where
  toFun c := ((c.2.1.1, c.2.1.2.1, c.2.1.2.2.1, c.2.1.2.2.2, c.1), c.2.2)
  invFun y := (y.1.2.2.2.2, ((y.1.1, y.1.2.1, y.1.2.2.1, y.1.2.2.2.1), y.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `H_msg` rates are distinct at Reparam's public coordinates and values. -/
def HRateInjY (y : YH) : Prop :=
  HmsgRateInj (sPub y.1.2 y.1.1) (y.2 rootPos)

/-- At most five `H_msg` inputs share a capacity at Reparam's public coordinates and values. -/
def HCapLoadY (y : YH) : Prop :=
  HmsgCapLoad (sPub y.1.2 y.1.1) (y.2 rootPos)

/-- HmsgCovers' `HStatic` at Reparam's public coordinates and values. -/
def HStaticY (y : YH) : Prop :=
  HStatic (sPub y.1.2 y.1.1) (y.2 rootPos)

open scoped Classical in
/-- The `H_msg` rates collide (named indicator). -/
noncomputable def hRateBad (y : YH) : ℕ :=
  if ¬HRateInjY y then 1 else 0

open scoped Classical in
/-- The `H_msg` rates are distinct and six inputs share a capacity (named indicator). -/
noncomputable def hCapBad (y : YH) : ℕ :=
  if HRateInjY y ∧ ¬HCapLoadY y then 1 else 0

/-- **The `H_msg` rates collide** for at most `|R × DLab|² / |X|` of the coordinates. -/
theorem frac_hRateBad_le :
    (Fintype.card YH : ℝ≥0∞)⁻¹ * ((∑ y : YH, hRateBad y : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card (Randomizer × DLab) * Fintype.card (Randomizer × DLab) : ℕ) : ℝ≥0∞) /
        Fintype.card X := by
  have h : Fintype.card X * ∑ y : YH, hRateBad y ≤
      Fintype.card YH * (Fintype.card (Randomizer × DLab) * Fintype.card (Randomizer × DLab)) :=
    card_mul_sum_equiv_prod_le ePH _ _ hRateBad fun r ↦ by
      refine le_trans (Nat.mul_le_mul_left _ (Finset.sum_le_sum fun π _ ↦ ?_))
        (card_mul_sum_not_injective_rate_le
          (fun c : Randomizer × DLab ↦ (dLabCell c.2 r.1.2.1 (r.2 rootPos) c.1,
            r.1.2.2.1 (dLabCell c.2 r.1.2.1 (r.2 rootPos) c.1)))
          fun a b hab ↦ dLabCell_injective _ _ (congrArg Prod.fst hab))
      exact ite_one_le_ite_one fun h ↦ h
  have h1 := natCast_le_mul_div_of_mul_le Fintype.card_ne_zero h
  have hN : (Fintype.card YH : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine (mul_le_mul' le_rfl h1).trans ?_
  rw [ENNReal.inv_mul_cancel_left hN (ENNReal.natCast_ne_top _)]

open scoped Classical in
/-- **Six `H_msg` inputs share a capacity** at distinct rates for at most `|R × DLab|⁶ / |Z|⁵`
of the coordinates. -/
theorem frac_hCapBad_le :
    (Fintype.card YH : ℝ≥0∞)⁻¹ * ((∑ y : YH, hCapBad y : ℕ) : ℝ≥0∞) ≤
      ((Fintype.card (Randomizer × DLab) ^ 6 : ℕ) : ℝ≥0∞) / (Fintype.card Z ^ 5 : ℕ) := by
  have h : Fintype.card Z ^ 5 * ∑ y : YH, hCapBad y ≤
      Fintype.card YH * Fintype.card (Randomizer × DLab) ^ 6 :=
    card_mul_sum_equiv_prod_le eKH _ _ hCapBad fun r ↦ by
      by_cases hI : Function.Injective fun c : Randomizer × DLab ↦
          (r.1.2.2.1 (dLabCell c.2 r.1.2.1 (r.2 rootPos) c.1,
            r.1.2.2.2 (dLabCell c.2 r.1.2.1 (r.2 rootPos) c.1))).1
      · refine le_trans (Nat.mul_le_mul_left _ (Finset.sum_le_sum fun g _ ↦ ?_))
          (card_pow_mul_sum_not_capLoad5_le _
            (fun c : Randomizer × DLab ↦ (r.1.2.2.1 (dLabCell c.2 r.1.2.1 (r.2 rootPos) c.1,
              r.1.2.2.2 (dLabCell c.2 r.1.2.1 (r.2 rootPos) c.1))).2) hI)
        refine ite_one_le_ite_one fun h hc ↦ h.2 fun z ↦ ?_
        obtain ⟨T, hT, hm⟩ := hc z
        exact ⟨T, hT, fun R a e ↦ hm (R, a) e⟩
      · exact mul_sum_le_of_eq_zero _ _ _ _ fun g ↦ ite_eq_right fun h ↦ hI h.1
  have hd : Fintype.card Z ^ 5 ≠ 0 := pow_ne_zero _ Fintype.card_ne_zero
  have h1 := natCast_le_mul_div_of_mul_le hd h
  have hN : (Fintype.card YH : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine (mul_le_mul' le_rfl h1).trans ?_
  rw [ENNReal.inv_mul_cancel_left hN (ENNReal.natCast_ne_top _)]

open scoped Classical in
/-- **`HStatic` fails** only where the rates collide or six inputs share a capacity. -/
theorem card_not_hStaticY_le :
    (Finset.univ.filter fun y : YH ↦ ¬HStaticY y).card ≤
      ∑ y : YH, hRateBad y + ∑ y : YH, hCapBad y :=
  card_filter_le_sum_add_sum (fun y : YH ↦ ¬HStaticY y) hRateBad hCapBad fun y h ↦ by
    by_cases h1 : HRateInjY y
    · have h2 : ¬HCapLoadY y := fun h2 ↦ h ⟨h1, h2⟩
      unfold hCapBad
      rw [ite_eq_left ⟨h1, h2⟩]
      exact Nat.le_add_left _ _
    · unfold hRateBad
      rw [ite_eq_left h1]
      exact Nat.le_add_right _ _

end hstatic

/-! ## The static fraction -/

section frac

/-- Off `HStatic` or `TrialsOff` at Reparam's public coordinates and values. -/
def StaticBadY (y : YH) : Prop :=
  ¬(HStaticY y ∧ TrialsOff y.1.2 y.1.1 y.2)

set_option exponentiation.threshold 4096 in
theorem card_randomizer_dLab : Fintype.card (Randomizer × DLab) = 2 ^ 385 := by
  have hR : Fintype.card Randomizer = 2 ^ 128 := by
    rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
    rfl
  rw [Fintype.card_prod, card_dLab, hR]
  norm_num

set_option exponentiation.threshold 4096 in
/-- The rate term at Keccak's sizes. -/
theorem hRateTerm_le_keccak :
    ((Fintype.card (Randomizer × DLab) * Fintype.card (Randomizer × DLab) : ℕ) : ℝ≥0∞) /
        Fintype.card X ≤ ENNReal.ofReal (1 / 2 ^ 318) := by
  rw [card_randomizer_dLab, rnCard_X,
    Quantum.Xmss.Hybrid.R0.natCast_div_eq_ofReal _ _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  norm_num

set_option exponentiation.threshold 4096 in
/-- The capacity term at Keccak's sizes. -/
theorem hCapTerm_le_keccak :
    ((Fintype.card (Randomizer × DLab) ^ 6 : ℕ) : ℝ≥0∞) / (Fintype.card Z ^ 5 : ℕ) ≤
      ENNReal.ofReal (1 / 2 ^ 250) := by
  rw [card_randomizer_dLab, rnCard_Z,
    Quantum.Xmss.Hybrid.R0.natCast_div_eq_ofReal _ _ (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  push_cast
  norm_num

open scoped Classical in
/-- **The static fraction over Reparam's public coordinates and values**: at most
`2^-318 + 2^-250 + 2^-400`. -/
theorem frac_staticBadY_le :
    ((Finset.univ.filter StaticBadY).card : ℝ≥0∞) / Fintype.card YH ≤
      ENNReal.ofReal (1 / 2 ^ 318) + ENNReal.ofReal (1 / 2 ^ 250) +
        ENNReal.ofReal (1 / 2 ^ 400) := by
  have hc := card_filter_le_add_of_imp StaticBadY (fun y : YH ↦ ¬HStaticY y)
    (fun y : YH ↦ ¬TrialsOff y.1.2 y.1.1 y.2) fun y h ↦ by
      by_cases h1 : HStaticY y
      · exact Or.inr fun h2 ↦ h ⟨h1, h2⟩
      · exact Or.inl h1
  have hS := (Nat.cast_le (α := ℝ≥0∞)).mpr card_not_hStaticY_le
  have hR := frac_hRateBad_le.trans hRateTerm_le_keccak
  have hC := frac_hCapBad_le.trans hCapTerm_le_keccak
  have hT : (Fintype.card YH : ℝ≥0∞)⁻¹ *
      (Finset.univ.filter fun y : YH ↦ ¬TrialsOff y.1.2 y.1.1 y.2).card ≤
      ENNReal.ofReal (1 / 2 ^ 400) :=
    trialsOff_frac_le_keccak
  calc ((Finset.univ.filter StaticBadY).card : ℝ≥0∞) / Fintype.card YH
      ≤ (Fintype.card YH : ℝ≥0∞)⁻¹ *
          (((∑ y : YH, hRateBad y : ℕ) : ℝ≥0∞) + ((∑ y : YH, hCapBad y : ℕ) : ℝ≥0∞) +
            (Finset.univ.filter fun y : YH ↦ ¬TrialsOff y.1.2 y.1.1 y.2).card) := by
        rw [ENNReal.div_eq_inv_mul]
        refine mul_le_mul' le_rfl ((Nat.cast_le.mpr hc).trans ?_)
        rw [Nat.cast_add]
        gcongr
        exact hS.trans_eq (Nat.cast_add _ _)
    _ = (Fintype.card YH : ℝ≥0∞)⁻¹ * ((∑ y : YH, hRateBad y : ℕ) : ℝ≥0∞) +
          (Fintype.card YH : ℝ≥0∞)⁻¹ * ((∑ y : YH, hCapBad y : ℕ) : ℝ≥0∞) +
          (Fintype.card YH : ℝ≥0∞)⁻¹ *
            (Finset.univ.filter fun y : YH ↦ ¬TrialsOff y.1.2 y.1.1 y.2).card := by
        rw [mul_add, mul_add]
    _ ≤ _ := add_le_add (add_le_add hR hC) hT

theorem hStatic_psiE_iff (y : YS) :
    HStatic (pubP (psiE y).1) (rootV (psiE y).2.1) ↔ HStaticY y.1 := by
  rw [pubP]
  exact Iff.rfl

theorem trialsOff_psiE_iff (y : YS) :
    TrialsOff (pubP (psiE y).1).xw (pubP (psiE y).1).keys.1 (valsOf (psiE y).2.1) ↔
      TrialsOff y.1.1.2 y.1.1.1 y.1.2 := by
  rw [pubP, sPub_xw, sPub_keys_fst]
  exact Iff.rfl

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The static fraction at Keccak's sizes**: for a static condition `S₀` implied by HmsgCovers'
`HStatic` and `TrialsOff` at the template data, at most `2^-249` of ReparamFull's coordinates are
off `S₀` (the rates `2^-318`, six `H_msg` inputs at one capacity `2^-250`, TrialsOff's
`2^-400`). -/
theorem frac_not_static_le_keccak (S₀ : PP → ((s : HPos) → XD s) → Prop)
    (hS : ∀ p v, HStatic (pubP p) (rootV v) → TrialsOff (pubP p).xw (pubP p).keys.1 (valsOf v) →
      S₀ p v) :
    (Fintype.card YS : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : YS ↦ ¬S₀ (psiE y).1 (psiE y).2.1).card ≤
      ENNReal.ofReal (1 / 2 ^ 249) := by
  have hsub : (Finset.univ.filter fun y : YS ↦ ¬S₀ (psiE y).1 (psiE y).2.1).card ≤
      (Finset.univ.filter fun y : YS ↦ StaticBadY y.1).card := by
    refine card_filter_univ_le_of_imp (fun y : YS ↦ ¬S₀ (psiE y).1 (psiE y).2.1)
      (fun y : YS ↦ StaticBadY y.1) fun y hy h ↦ hy ?_
    exact hS (psiE y).1 (psiE y).2.1 ((hStatic_psiE_iff y).mpr h.1)
      ((trialsOff_psiE_iff y).mpr h.2)
  have he : (Fintype.card YS : ℝ≥0∞)⁻¹ *
      (Finset.univ.filter fun y : YS ↦ StaticBadY y.1).card =
      ((Finset.univ.filter StaticBadY).card : ℝ≥0∞) / Fintype.card YH :=
    inv_card_mul_card_filter_comp_fst (Equiv.refl YS) StaticBadY
  calc (Fintype.card YS : ℝ≥0∞)⁻¹ *
        (Finset.univ.filter fun y : YS ↦ ¬S₀ (psiE y).1 (psiE y).2.1).card
      ≤ (Fintype.card YS : ℝ≥0∞)⁻¹ *
          (Finset.univ.filter fun y : YS ↦ StaticBadY y.1).card := by
        exact mul_le_mul' le_rfl (Nat.cast_le.mpr hsub)
    _ = _ := he
    _ ≤ _ := frac_staticBadY_le
    _ ≤ ENNReal.ofReal (1 / 2 ^ 249) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)

/-- HmsgCovers' `HStatic` and `TrialsOff` at the template data. -/
def HTStatic (p : PP) (v : (s : HPos) → XD s) : Prop :=
  HStatic (pubP p) (rootV v) ∧ TrialsOff (pubP p).xw (pubP p).keys.1 (valsOf v)

set_option exponentiation.threshold 4096 in
open scoped Classical in
/-- **The static fraction** (Security's `stageFrac_le_stageCap`): at most `2^-127` (`HStatic` and
`TrialsOff` `2^-249`, ChgRevStatic's `ChgStatic` `2^-128 + 2^-199`). -/
theorem staticFrac_le : staticFrac ≤ ENNReal.ofReal (1 / 2 ^ 127) := by
  have hc := card_filter_le_add_of_imp (fun y : YS ↦ ¬SphStatic (psiE y).1 (psiE y).2.1)
    (fun y : YS ↦ ¬HTStatic (psiE y).1 (psiE y).2.1)
    (fun y : YS ↦ ¬ChgStatic (pubP (psiE y).1) (rootV (psiE y).2.1)) fun y h ↦ by
      by_cases h1 : HTStatic (psiE y).1 (psiE y).2.1
      · exact Or.inr fun h2 ↦ h ⟨h1.1, h1.2, h2⟩
      · exact Or.inl h1
  have h1 := frac_not_static_le_keccak HTStatic fun _ _ h1 h2 ↦ ⟨h1, h2⟩
  calc staticFrac
      ≤ (Fintype.card YS : ℝ≥0∞)⁻¹ *
            (Finset.univ.filter fun y : YS ↦ ¬HTStatic (psiE y).1 (psiE y).2.1).card +
          (Fintype.card YS : ℝ≥0∞)⁻¹ * (Finset.univ.filter fun y : YS ↦
            ¬ChgStatic (pubP (psiE y).1) (rootV (psiE y).2.1)).card := by
        unfold staticFrac
        rw [← mul_add]
        exact mul_le_mul' le_rfl ((Nat.cast_le.mpr hc).trans_eq (Nat.cast_add _ _))
    _ ≤ ENNReal.ofReal (1 / 2 ^ 249) +
          (ENNReal.ofReal (1 / 2 ^ 128) + ENNReal.ofReal (1 / 2 ^ 199)) :=
        add_le_add h1 frac_chgStatic_le_keccak
    _ ≤ ENNReal.ofReal (1 / 2 ^ 127) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by norm_num)

end frac

end Quantum.Sphincs.Assembly

end
