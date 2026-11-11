module

public import Qrom.HidingAvg

@[expose] public section

/-!
# The hiding hybrid

Two families of games `g₁ g₂ : (K → Z) → Qrom.OvGame`, indexed by hidden data `h`, with the same
side ports and the same initial side state, whose hashes differ only on the protected inputs
`Prot h s x`: averaged over `h` and over the random function `G`, the probability of any event of
the first family is at most that of the second, up to the protected masses:
`√Pr₁ ≤ √Pr₂ + n √(4 ε tr ρ)` for a program with at most `n` calls in all
(`Qrom.OvGame.hiding_le`), when the second family reads the hidden data only through the keys
revealed in the current side state, and at most a fraction `ε` of the unrevealed values protect any
input. The proof is the square-root hybrid for each `h` and `G`, the per-call cost
(`Qrom.OvGame.krausWeight_sub_le`), the ℓ² Minkowski inequality over `h` and `G`, and the averaged
protected mass (`Qrom.OvGame.sum_queryWeight_protMass_le`).
-/

open Matrix OracleSpec
open scoped Kronecker ENNReal ComplexOrder

universe u v w

set_option linter.unusedSectionVars false

namespace Qrom

open Quantum Quantum.MatrixMap

namespace OvGame

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {S P : Type} [Fintype S] [DecidableEq S] {Res : P → Type} [∀ j, Fintype (Res j)]
  [∀ j, DecidableEq (Res j)]
variable {K Z : Type} [Fintype K] [DecidableEq K] [Fintype Z] [DecidableEq Z] [Nonempty Z]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- The probability of an event of a family of games, averaged over the hidden data and the
random function. -/
noncomputable def avgProb (g : (K → Z) → OvGame X Y S P Res) (I : L.Interp)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A)
    (f : (K → Z) → (X → Y) → (Σ u, W u) → Bool) : ℝ≥0∞ :=
  ∑ h, ∑ G, ((Fintype.card (K → Z) : ℝ≥0∞) * Fintype.card (X → Y))⁻¹ *
    ((g h).sampled G).evalDistMap I x ρ (f h G) {true}

variable (g₁ g₂ : (K → Z) → OvGame X Y S P Res) (rev : (K → Z) → S → Finset K)
  (Prot : (K → Z) → S → X → Prop) [∀ h s, DecidablePred (Prot h s)]

/-- The per-`(h, G)` hybrid. -/
theorem rpow_evalDistMap_le_hybrid (htr : ∀ h, (g₁ h).trans = (g₂ h).trans)
    (hov : ∀ h s x, ¬ Prot h s x → (g₁ h).ov s x = (g₂ h).ov s x)
    (hinit12 : ∀ h, (g₁ h).init = (g₂ h).init) (I : L.Interp)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) (h : K → Z) (G : X → Y)
    (f : (Σ u, W u) → Bool) :
    ((g₁ h).sampled G).evalDistMap I x ρ f {true} ^ (2⁻¹ : ℝ) ≤
      ((g₂ h).sampled G).evalDistMap I x ρ f {true} ^ (2⁻¹ : ℝ) +
        ∑' j, (4 * ((g₂ h).sampled G).queryWeight I (protMass (Prot h)) x
          (ρ.matrix ⊗ₖ ((g₂ h).sampled G).init.matrix) j) ^ (2⁻¹ : ℝ) := by
  have hR : (g₁ h).sampled G = QuantumRuntime.mk (QReg.of (S × Unit))
      ((g₂ h).sampled G).init ((g₁ h).sampled G).step := by
    simp only [sampled, tabRuntime, hinit12 h]
  have hb := QuantumRuntime.rpow_inv_two_outcomeLawWith_le' I ((g₂ h).sampled G).init
    ((g₂ h).sampled_branch G) ((g₁ h).sampled_branch G) x ρ f
    (measurableSet_singleton true)
  rw [hR]
  refine hb.trans (add_le_add le_rfl (ENNReal.tsum_le_tsum fun j ↦ ?_))
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  rw [← QuantumRuntime.queryWeight_const_mul]
  exact QuantumRuntime.queryWeight_mono _ I (fun i σ hσ ↦
    krausWeight_sub_le (g₁ := g₁ h) (g₂ := g₂ h) (Prot h) G (htr h) (hov h) i hσ) x
    (ρ.prod ((g₂ h).sampled G).init).posSemidef j

/-- **The hiding hybrid.** -/
theorem hiding_le (htr : ∀ h, (g₁ h).trans = (g₂ h).trans)
    (hov : ∀ h s x, ¬ Prot h s x → (g₁ h).ov s x = (g₂ h).ov s x)
    (hinit12 : ∀ h, (g₁ h).init = (g₂ h).init)
    (hself : ∀ h h' s, (∀ k ∈ rev h s, h k = h' k) → rev h' s = rev h s)
    (hmono : ∀ h j s, rev h s ⊆ rev h ((g₂ h).trans j s).2)
    (hlocal : ∀ h h' s, (∀ k ∈ rev h s, h k = h' k) → (g₂ h).ov s = (g₂ h').ov s)
    (hlocalTr : ∀ h h' j s, (∀ k ∈ rev h ((g₂ h).trans j s).2, h k = h' k) →
      (g₂ h).trans j s = (g₂ h').trans j s)
    (hinit : ∀ h h', (g₂ h).init = (g₂ h').init) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hprot : ∀ h s x, ((Finset.univ.filter fun b ↦ Prot (merge (rev h s) h b) s x).card : ℝ) ≤
      ε * Fintype.card ({k // k ∉ rev h s} → Z))
    (I : L.Interp) (n : ℕ) (x : QuantumComp L (ovSpec X Y S P Res) W A)
    (hx : x.IsTotalQueryBound n) (ρ : SubState A) (f : (K → Z) → (X → Y) → (Σ u, W u) → Bool) :
    avgProb g₁ I x ρ f ^ (2⁻¹ : ℝ) ≤ avgProb g₂ I x ρ f ^ (2⁻¹ : ℝ) +
      n * (4 * ENNReal.ofReal ε * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) := by
  set c : ℝ≥0∞ := ((Fintype.card (K → Z) : ℝ≥0∞) * Fintype.card (X → Y))⁻¹ with hc
  set QW : ℕ → (K → Z) × (X → Y) → ℝ≥0∞ := fun j k ↦
    ((g₂ k.1).sampled k.2).queryWeight I (protMass (Prot k.1)) x
      (ρ.matrix ⊗ₖ ((g₂ k.1).sampled k.2).init.matrix) j
  have havg : ∀ g : (K → Z) → OvGame X Y S P Res, avgProb g I x ρ f =
      ∑' k : (K → Z) × (X → Y), c * ((g k.1).sampled k.2).evalDistMap I x ρ (f k.1 k.2) {true} := by
    intro g
    rw [tsum_fintype, Fintype.sum_prod_type]
    rfl
  -- the hybrid, scaled by `c`, for every `(h, G)`
  have hk : ∀ k : (K → Z) × (X → Y),
      (c * ((g₁ k.1).sampled k.2).evalDistMap I x ρ (f k.1 k.2) {true}) ^ (2⁻¹ : ℝ) ≤
        (c * ((g₂ k.1).sampled k.2).evalDistMap I x ρ (f k.1 k.2) {true}) ^ (2⁻¹ : ℝ) +
          ∑' j, (c * (4 * QW j k)) ^ (2⁻¹ : ℝ) := by
    intro k
    have h1 := rpow_evalDistMap_le_hybrid g₁ g₂ Prot htr hov hinit12 I x ρ k.1 k.2 (f k.1 k.2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    simp only [ENNReal.mul_rpow_of_nonneg c _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
    rw [ENNReal.tsum_mul_left, ← mul_add]
    exact mul_le_mul_right h1 _
  have hsum := Quantum.rpow_inv_two_tsum_le_of_le_add_tsum hk
  rw [havg, havg]
  refine hsum.trans (add_le_add le_rfl ?_)
  -- the protected masses
  have hmass : ∀ j, ∑' k, c * (4 * QW j k) ≤ 4 * ENNReal.ofReal ε * ENNReal.ofReal ρ.matrix.trace.re := by
    intro j
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, tsum_fintype, Fintype.sum_prod_type,
      Finset.sum_comm]
    have htrace : ∀ k : (K → Z) × (X → Y), ((g₂ k.1).sampled k.2).queryWeight I
        (fun _ σ ↦ ENNReal.ofReal σ.trace.re) x (ρ.matrix ⊗ₖ ((g₂ k.1).sampled k.2).init.matrix) j ≤
        ENNReal.ofReal ρ.matrix.trace.re := by
      intro k
      refine (QuantumRuntime.queryWeight_le_ofReal_trace _ I (fun _ _ _ ↦ le_rfl) x
        (ρ.prod ((g₂ k.1).sampled k.2).init).posSemidef j).trans_eq ?_
      congr 2
      simp [Matrix.trace_kronecker, SubState.matrix_basis, SubState.matrix_prod]
    calc c * (4 * ∑ G, ∑ h, QW j (h, G))
        ≤ c * (4 * ∑ G : X → Y, ENNReal.ofReal ε * ∑ h : K → Z, ENNReal.ofReal ρ.matrix.trace.re) := by
          gcongr with G
          refine (sum_queryWeight_protMass_le rev g₂ Prot hself hmono hlocal hlocalTr hinit hε0 hprot I G x ρ j).trans ?_
          gcongr with h
          exact htrace (h, G)
      _ = c * (Fintype.card (K → Z) * Fintype.card (X → Y)) *
            (4 * ENNReal.ofReal ε * ENNReal.ofReal ρ.matrix.trace.re) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ = _ := by
          rw [hc, ENNReal.inv_mul_cancel (by simp)
            (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)), one_mul]
  have hzero : ∀ j ∉ Finset.range n, (∑' k, c * (4 * QW j k)) ^ (2⁻¹ : ℝ) = 0 := by
    intro j hj
    have : ∀ k, QW j k = 0 := fun k ↦
      QuantumRuntime.queryWeight_eq_zero_of_isTotalQueryBound _ I hx (by simpa using hj) _
    simp [this, ENNReal.zero_rpow_of_pos]
  rw [tsum_eq_sum hzero]
  calc ∑ j ∈ Finset.range n, (∑' k, c * (4 * QW j k)) ^ (2⁻¹ : ℝ)
      ≤ ∑ _j ∈ Finset.range n, (4 * ENNReal.ofReal ε * ENNReal.ofReal ρ.matrix.trace.re) ^
          (2⁻¹ : ℝ) := Finset.sum_le_sum fun j _ ↦ ENNReal.rpow_le_rpow (hmass j) (by norm_num)
    _ = _ := by simp

end OvGame

end Qrom
