module

public import Qrom.HidingMain

@[expose] public section

/-!
# Events of the leaf and the side state

A game's win condition may read the side state at the end of the run (the signing log), which
lives in the runtime's register, not in the leaf. `Qrom.OvGame.sideW` weighs each leaf `p` by the
part of its joint post-state whose side state `s` satisfies `ev p s`. An event that does not read
the side state has the probability of the corresponding leaf event
(`Qrom.OvGame.sideW_const`), and the hiding hybrid holds for these events too
(`Qrom.OvGame.hiding_side_le`): the square-root hybrid takes any contraction on the leaves.
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
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- The projector onto the side states satisfying `e`. -/
def evProj (e : S → Bool) : Matrix (S × Unit) (S × Unit) ℂ :=
  diagonal fun t ↦ if e t.1 then 1 else 0

theorem evProj_conjTranspose (e : S → Bool) : (evProj e)ᴴ = evProj e := by
  rw [evProj, diagonal_conjTranspose]
  congr 1
  funext t
  by_cases h : e t.1 <;> simp [h]

theorem evProj_mul_self (e : S → Bool) : evProj e * evProj e = evProj e := by
  rw [evProj, diagonal_mul_diagonal]
  congr 1
  funext t
  by_cases h : e t.1 <;> simp [h]

theorem posSemidef_one_sub_one_kronecker_evProj {n : Type*} [Fintype n] [DecidableEq n]
    (e : S → Bool) :
    (1 - ((1 : Matrix n n ℂ) ⊗ₖ evProj e)ᴴ * ((1 : Matrix n n ℂ) ⊗ₖ evProj e)).PosSemidef := by
  have h1 : ((1 : Matrix n n ℂ) ⊗ₖ evProj e)ᴴ * ((1 : Matrix n n ℂ) ⊗ₖ evProj e) =
      (1 : Matrix n n ℂ) ⊗ₖ evProj e := by
    rw [conjTranspose_kronecker, conjTranspose_one, evProj_conjTranspose, ← mul_kronecker_mul,
      Matrix.one_mul, evProj_mul_self]
  have h2 : (1 : Matrix (n × (S × Unit)) (n × (S × Unit)) ℂ) - (1 : Matrix n n ℂ) ⊗ₖ evProj e =
      (1 : Matrix n n ℂ) ⊗ₖ evProj (fun s ↦ !e s) := by
    ext ⟨a, t⟩ ⟨b, t'⟩
    simp only [Matrix.sub_apply, kroneckerMap_apply, Matrix.one_apply, evProj, diagonal_apply]
    rcases eq_or_ne a b with rfl | hab
    · rcases eq_or_ne t t' with rfl | htt
      · by_cases he : e t.1 <;> simp [he]
      · simp [htt]
    · simp [hab]
  rw [h1, h2]
  have h3 : (1 : Matrix n n ℂ) ⊗ₖ evProj (fun s ↦ !e s) =
      ((1 : Matrix n n ℂ) ⊗ₖ evProj (fun s ↦ !e s))ᴴ * ((1 : Matrix n n ℂ) ⊗ₖ evProj (fun s ↦ !e s)) := by
    rw [conjTranspose_kronecker, conjTranspose_one, evProj_conjTranspose, ← mul_kronecker_mul,
      Matrix.one_mul, evProj_mul_self]
  rw [h3]
  exact posSemidef_conjTranspose_mul_self _

/-- The weight, in the game `g` with the function `G`, of the leaves and side states satisfying
`ev`. -/
noncomputable def sideW (g : OvGame X Y S P Res) (G : X → Y) (I : L.Interp)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) (ev : (Σ u, W u) → S → Bool) :
    ℝ≥0∞ :=
  ∑' p, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ evProj (ev p))
    ((g.sampled G).jointPost I x ρ p).matrix).trace.re

/-- An event that does not read the side state has the probability of the leaf event. -/
theorem sideW_const (g : OvGame X Y S P Res) (G : X → Y) (I : L.Interp)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) (f : (Σ u, W u) → Bool) :
    sideW g G I x ρ (fun p _ ↦ f p) = (g.sampled G).evalDistMap I x ρ f {true} := by
  rw [sideW, QuantumRuntime.evalDistMap_apply _ _ _ _ _ (measurableSet_singleton true)]
  refine tsum_congr fun p ↦ ?_
  by_cases hf : f p
  · have h1 : evProj (S := S) (fun _ ↦ f p) = 1 := by
      rw [evProj, ← diagonal_one]
      congr 1
      funext t
      simp [hf]
    rw [h1, one_kronecker_one, MatrixMap.conj_apply, Matrix.one_mul, conjTranspose_one,
      Matrix.mul_one]
    simp [hf]
  · have h0 : evProj (S := S) (fun _ ↦ f p) = 0 := by
      rw [evProj, ← diagonal_zero]
      congr 1
      funext t
      simp [hf]
    rw [h0, kronecker_zero, MatrixMap.conj_apply, Matrix.zero_mul, Matrix.zero_mul]
    simp [hf]

/-! ## Hiding for events of the leaf and the side state -/

section hidingSide

variable {K Z : Type} [Fintype K] [DecidableEq K] [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- The weight of an event of the leaf and the side state, averaged over the hidden data and the
random function. -/
noncomputable def avgSide (g : (K → Z) → OvGame X Y S P Res) (I : L.Interp)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A)
    (ev : (K → Z) → (X → Y) → (Σ u, W u) → S → Bool) : ℝ≥0∞ :=
  ∑ h, ∑ G, ((Fintype.card (K → Z) : ℝ≥0∞) * Fintype.card (X → Y))⁻¹ *
    sideW (g h) G I x ρ (ev h G)

variable (g₁ g₂ : (K → Z) → OvGame X Y S P Res) (rev : (K → Z) → S → Finset K)
  (Prot : (K → Z) → S → X → Prop) [∀ h s, DecidablePred (Prot h s)]

/-- The per-`(h, G)` hybrid for events of the leaf and the side state. -/
theorem rpow_sideW_le_hybrid (htr : ∀ h, (g₁ h).trans = (g₂ h).trans)
    (hov : ∀ h s x, ¬ Prot h s x → (g₁ h).ov s x = (g₂ h).ov s x)
    (hinit12 : ∀ h, (g₁ h).init = (g₂ h).init) (I : L.Interp)
    (x : QuantumComp L (ovSpec X Y S P Res) W A) (ρ : SubState A) (h : K → Z) (G : X → Y)
    (ev : (Σ u, W u) → S → Bool) :
    sideW (g₁ h) G I x ρ ev ^ (2⁻¹ : ℝ) ≤ sideW (g₂ h) G I x ρ ev ^ (2⁻¹ : ℝ) +
      ∑' j, (4 * ((g₂ h).sampled G).queryWeight I (protMass (Prot h)) x
        (ρ.matrix ⊗ₖ ((g₂ h).sampled G).init.matrix) j) ^ (2⁻¹ : ℝ) := by
  have hb := QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le' I ((g₂ h).sampled G).init
    ((g₁ h).sampled G).init ((g₂ h).sampled_branch G) ((g₁ h).sampled_branch G) x
    (fun p ↦ (1 : Matrix p.1 p.1 ℂ) ⊗ₖ evProj (ev p))
    (fun p ↦ posSemidef_one_sub_one_kronecker_evProj (ev p))
    (ρ.prod ((g₂ h).sampled G).init).posSemidef
  simp only [sideW, QuantumRuntime.matrix_jointPost]
  have hq : ∀ j, (QuantumRuntime.mk (QReg.of (S × Unit)) ((g₂ h).sampled G).init
      ((g₂ h).sampled G).step).queryWeight I
      (QuantumRuntime.krausWeight fun i r ↦ (g₂ h).sampKraus G i r - (g₁ h).sampKraus G i r) x
      (ρ.matrix ⊗ₖ ((g₂ h).sampled G).init.matrix) j ^ (2⁻¹ : ℝ) ≤
      (4 * ((g₂ h).sampled G).queryWeight I (protMass (Prot h)) x
        (ρ.matrix ⊗ₖ ((g₂ h).sampled G).init.matrix) j) ^ (2⁻¹ : ℝ) := by
    intro j
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [← QuantumRuntime.queryWeight_const_mul]
    exact QuantumRuntime.queryWeight_mono _ I (fun i σ hσ ↦
      krausWeight_sub_le (g₁ := g₁ h) (g₂ := g₂ h) (Prot h) G (htr h) (hov h) i hσ) x
      (ρ.prod ((g₂ h).sampled G).init).posSemidef j
  rw [SubState.matrix_prod] at hb
  rw [hinit12 h]
  exact hb.trans (add_le_add le_rfl (ENNReal.tsum_le_tsum hq))

/-- **The hiding hybrid for events of the leaf and the side state.** -/
theorem hiding_side_le (htr : ∀ h, (g₁ h).trans = (g₂ h).trans)
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
    (hx : x.IsTotalQueryBound n) (ρ : SubState A)
    (ev : (K → Z) → (X → Y) → (Σ u, W u) → S → Bool) :
    avgSide g₁ I x ρ ev ^ (2⁻¹ : ℝ) ≤ avgSide g₂ I x ρ ev ^ (2⁻¹ : ℝ) +
      n * (4 * ENNReal.ofReal ε * ENNReal.ofReal ρ.matrix.trace.re) ^ (2⁻¹ : ℝ) := by
  set c : ℝ≥0∞ := ((Fintype.card (K → Z) : ℝ≥0∞) * Fintype.card (X → Y))⁻¹ with hc
  set QW : ℕ → (K → Z) × (X → Y) → ℝ≥0∞ := fun j k ↦
    ((g₂ k.1).sampled k.2).queryWeight I (protMass (Prot k.1)) x
      (ρ.matrix ⊗ₖ ((g₂ k.1).sampled k.2).init.matrix) j
  have havg : ∀ g : (K → Z) → OvGame X Y S P Res, avgSide g I x ρ ev =
      ∑' k : (K → Z) × (X → Y), c * sideW (g k.1) k.2 I x ρ (ev k.1 k.2) := by
    intro g
    rw [tsum_fintype, Fintype.sum_prod_type]
    rfl
  have hk : ∀ k : (K → Z) × (X → Y),
      (c * sideW (g₁ k.1) k.2 I x ρ (ev k.1 k.2)) ^ (2⁻¹ : ℝ) ≤
        (c * sideW (g₂ k.1) k.2 I x ρ (ev k.1 k.2)) ^ (2⁻¹ : ℝ) +
          ∑' j, (c * (4 * QW j k)) ^ (2⁻¹ : ℝ) := by
    intro k
    have h1 := rpow_sideW_le_hybrid g₁ g₂ Prot htr hov hinit12 I x ρ k.1 k.2 (ev k.1 k.2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    simp only [ENNReal.mul_rpow_of_nonneg c _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
    rw [ENNReal.tsum_mul_left, ← mul_add]
    exact mul_le_mul_right h1 _
  have hsum := Quantum.rpow_inv_two_tsum_le_of_le_add_tsum hk
  rw [havg, havg]
  refine hsum.trans (add_le_add le_rfl ?_)
  have hmass : ∀ j, ∑' k, c * (4 * QW j k) ≤
      4 * ENNReal.ofReal ε * ENNReal.ofReal ρ.matrix.trace.re := by
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

end hidingSide

end OvGame

end Qrom
