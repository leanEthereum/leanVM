module

public import Quantum.Qrom.Xmss.Costs.Regrind

@[expose] public section

/-!
# Re-grinds: the empty read cells of selected keys

Without leaf reuse, an empty trial read cell of a selected key (`selWt`) costs at most `1/|Y|`
per unit of trace. In the decompressed basis the key's selection is by the trial's own search,
at a trial the search already read (`cell_eq_of_rgInv`: the trials before the read are no
codewords), so the decompressed cell holds the value recorded at that read; the compression maps
the empty cell to the uniform superposition, whose overlap with one value is `1/|Y|`
(`re_trace_empty_le`).

## Main statements

* `re_trace_empty_le`: on a register whose decompressed form holds a fixed value at a cell on the
  blocks of a memory event, the compressed weight of "the cell is empty and the event holds" is at
  most `tr σ / |Y|`.
* `trialW_selWt_le`: at a trial read on the invariant, `selWt` weighs at most `tr σ / |Y|`.
* `selPre_le_card`: `selPre A θ ≤ K / |Y|`; `selPre_le_small`: `selPre A θ ≤ 2^-128 K`, against an
  adversary that reuses no leaf, with at most `K` classical calls.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder

namespace Quantum.Qrom.Xmss

open Quantum QuantumRuntime Quantum.Sponge Quantum.Xmss.Hybrid HashSig LeanXmss
open Quantum.Xmss.Assembly (recSpec runtimeR extWeight extCls NoBot
  totalWeight_le_of_forallQueries)
open Quantum.Xmss.Hybrid (totalWeight_const_mul_weight)

attribute [local irreducible] xmssRom

/- Instance search for the register's decidable equality exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## The empty cell against one value -/

section cell

theorem cellCompress_mul_noneInd_mul (Y : Type) [Fintype Y] [DecidableEq Y] :
    cellCompress Y * diagonal (fun o : Option Y ↦ if o = none then (1 : ℂ) else 0) *
      cellCompress Y = cellUnifProj Y := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, Fintype.sum_option]
  rcases a with _ | y <;> rcases b with _ | y' <;> simp [cellUnifProj]

/-- **The empty cell against one value.** Let `e` split a cell off the register, `C` an involution
with `C (empty ∧ p) C = U ⊗ p` (`U` the uniform superposition on the cell, `p` an event on the
rest). On a positive semidefinite `σ` whose decompressed form holds the value `y₀` at the cell
wherever `p` holds, the weight of "the cell is empty and `p` holds" is at most `tr σ / |Y|`. -/
theorem re_trace_empty_le {N Y R : Type} [Fintype N] [DecidableEq N] [Fintype Y] [DecidableEq Y]
    (e : N ≃ Option Y × R) {C : Matrix N N ℂ} (hCC : C * C = 1) (hCh : Cᴴ = C) (p : R → Prop)
    [DecidablePred p]
    (hD : C * diagonal (fun a ↦ if (e a).1 = none ∧ p (e a).2 then (1 : ℂ) else 0) * C =
      liftCell e (cellUnifProj Y) * diagonal (fun a ↦ if p (e a).2 then (1 : ℂ) else 0))
    (y₀ : Y) {σ : Matrix N N ℂ} (hσ : σ.PosSemidef)
    (hdec : ∀ a b, (C * σ * C) a b ≠ 0 → p (e a).2 → (e a).1 = some y₀) :
    (∑ a, if (e a).1 = none ∧ p (e a).2 then (σ a a).re else 0) ≤
      (Fintype.card Y : ℝ)⁻¹ * σ.trace.re := by
  classical
  set σ' := C * σ * C with hσ'
  have hσ'psd : σ'.PosSemidef := by
    have h := hσ.mul_mul_conjTranspose_same C
    rwa [hCh] at h
  have hre' : ∀ a, 0 ≤ (σ' a a).re := fun a ↦ (Complex.nonneg_iff.1 hσ'psd.diag_nonneg).1
  set f : N → ℂ := fun a ↦ if (e a).1 = none ∧ p (e a).2 then (1 : ℂ) else 0
  set P : N → ℂ := fun a ↦ if p (e a).2 then (1 : ℂ) else 0
  have hlhs : (∑ a, if (e a).1 = none ∧ p (e a).2 then (σ a a).re else 0) =
      (diagonal f * σ).trace.re := by
    rw [Matrix.trace, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Matrix.diag_apply, diagonal_mul]
    by_cases h : (e a).1 = none ∧ p (e a).2
    · simp only [f, h, and_self, ite_true, one_mul]
    · simp only [f, h, ite_false, zero_mul, Complex.zero_re]
  have hcomp : (diagonal f * σ).trace = (C * diagonal f * C * σ').trace := by
    have h : C * diagonal f * C * (C * σ * C) = C * (diagonal f * σ) * C := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc C C (σ * C), hCC, Matrix.one_mul]
    rw [hσ', h, Matrix.trace_mul_comm (C * (diagonal f * σ)) C,
      ← Matrix.mul_assoc C C (diagonal f * σ), hCC, Matrix.one_mul]
  have htr : σ.trace = σ'.trace := by
    rw [hσ', Matrix.trace_mul_comm (C * σ) C, ← Matrix.mul_assoc C C σ, hCC, Matrix.one_mul]
  -- The off-diagonal terms vanish.
  have hoff : ∀ a b, b ≠ a → (liftCell e (cellUnifProj Y) * diagonal P) a b * σ' b a = 0 := by
    intro a b hba
    rw [mul_diagonal, liftCell_apply]
    by_contra hne
    have hP : P b ≠ 0 := fun h ↦ hne (by rw [h, mul_zero, zero_mul])
    have hpb : p (e b).2 := by
      by_contra h
      exact hP (by simp only [P, h, ite_false])
    have hR : (e a).2 = (e b).2 := by
      by_contra h
      exact hne (by rw [Matrix.one_apply_ne h, mul_zero, zero_mul, zero_mul])
    have hσba : σ' b a ≠ 0 := fun h ↦ hne (by rw [h, mul_zero])
    have hb := hdec b a hσba hpb
    have hσab : σ' a b ≠ 0 := by
      have h := hσ'psd.isHermitian.apply a b
      intro h0
      rw [h0, star_eq_zero] at h
      exact hσba h
    have ha := hdec a b hσab (hR ▸ hpb)
    exact hba (e.injective (Prod.ext (hb.trans ha.symm) hR.symm))
  have hdiag : ∀ a, (liftCell e (cellUnifProj Y) * diagonal P) a a =
      ((if ((e a).1).isSome ∧ p (e a).2 then (Fintype.card Y : ℝ)⁻¹ else 0 : ℝ) : ℂ) := by
    intro a
    rw [mul_diagonal, liftCell_apply, Matrix.one_apply_eq, mul_one]
    rcases hc : (e a).1 with _ | y
    · simp [cellUnifProj]
    · by_cases hp : p (e a).2
      · simp only [cellUnifProj, of_apply, cellUniform_some, cellAmp_mul_self, P, hp, ite_true,
          mul_one, Option.isSome_some, and_self]
        push_cast
        rfl
      · simp [P, hp]
  rw [hlhs, hcomp, hD, htr, Matrix.trace, Matrix.trace, Complex.re_sum, Complex.re_sum,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, Matrix.mul_apply,
    Finset.sum_eq_single a (fun b _ hba ↦ hoff a b hba) (fun h ↦ absurd (Finset.mem_univ a) h),
    hdiag, Complex.re_ofReal_mul]
  have hN : 0 ≤ (Fintype.card Y : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  split_ifs
  · exact le_rfl
  · rw [zero_mul]
    exact mul_nonneg hN (hre' a)

end cell

/-! ## A trial read on the invariant -/

section trial

variable {θ : HPos → Digest}

/-- **The read cell of a selected key holds the recorded value**: within a search, the key's
selection is a trial of the search at or after the current one, so the current trial was read. -/
theorem cell_eq_of_rgInv {l : Layer} {e : KeyIndex} {msg : MsgBytes} {base : Randomizer} {j : ℕ}
    {rd : HashDomain → Option HashOutput} {s : RReg SelMem}
    (hs : s ∈ rgInv θ (.srch l e msg base j, rd)) (hsel : s.2.2.2 l e ≠ none) :
    s.1.1 (trialCell (tabOf θ).param l e msg base j) =
      some ((rd (trialCell (tabOf θ).param l e msg base j)).getD 0) := by
  obtain ⟨⟨hnb, hmsg, hrd, -⟩, -, hcur, hpre⟩ := hs
  set z := trialCell (tabOf θ).param l e msg base j with hz
  obtain ⟨sel, hs'⟩ := Option.ne_none_iff_exists'.mp hsel
  obtain ⟨j', h1, h2, h3, h4, h5⟩ := hcur sel hs'
  have hrdz : rd z ≠ none := by
    rcases lt_trichotomy j' j with hlt | rfl | hgt
    · have h := (hpre j' hlt).2
      rw [← h1, ← h3] at h
      exact absurd h4 h
    · rw [hz, ← h1]
      exact h2
    · exact (h5 j hgt).1
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hrdz
  have hv := (hrd z y hy).2
  have hW : s.2.1.1 z = none := hmsg z l e (slotOf_trialCell _ l e msg base j)
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp (hnb.1 z)
  have hv' : hvw s z = y' := by
    show ((s.2.1.1 z).or (s.1.1 z)).getD 0 = y'
    rw [hW, hy']
    rfl
  rw [hy', hy, Option.getD_some, ← hv, hv']

/-- The memory blocks of the hardwired register commute with the compression. -/
theorem compress_mul_diagonal_mem (d : Hw HashOutput HashDomain × QMem → ℂ) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg HashOutput HashDomain QMem) *
        diagonal (fun a : Unit × RReg SelMem ↦ d a.2.2) =
      diagonal (fun a : Unit × RReg SelMem ↦ d a.2.2) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg HashOutput HashDomain QMem) := by
  ext a b
  rw [mul_diagonal, diagonal_mul]
  by_cases h : a.2.2 = b.2.2
  · rw [h, mul_comm]
  · have h0 : ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg HashOutput HashDomain QMem) a b = 0 := by
      rw [kroneckerMap_apply, compressReg, kroneckerMap_apply, Matrix.one_apply_ne h, mul_zero,
        mul_zero]
    rw [h0, zero_mul, mul_zero]

/-- **The empty read cells of a selected key at a trial read on the invariant** weigh at most
`tr σ / |Y|`. -/
theorem trialW_selWt_le {μ : RgMode} {c : HwRead HashOutput HashDomain QMem}
    (hok : rgRdOk (tabOf θ).param μ.1 c)
    {σ : Matrix (Unit × RReg SelMem) (Unit × RReg SelMem) ℂ} (hσ : σ.PosSemidef)
    (hs : QuerySupportedOn (fun m : Unit × RReg SelMem ↦ m.2) (rgInv θ μ)
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg HashOutput HashDomain QMem) σ)) :
    trialW selWt c σ ≤
      ENNReal.ofReal ((Fintype.card HashOutput : ℝ)⁻¹) * ENNReal.ofReal σ.trace.re := by
  obtain ⟨σ₀, rd⟩ := μ
  cases σ₀ with
  | free => exact hok.elim
  | srch l e msg base j =>
    set z := trialCell (tabOf θ).param l e msg base j with hz
    have hc : c = trialRead z l e := hok
    subst hc
    rw [trialW_trialRead _ (slotOf_trialCell _ l e msg base j)]
    set C := (1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg HashOutput HashDomain QMem with hC
    have hCh : Cᴴ = C := conjTranspose_one_kron_compressReg
    set E := lensH Unit QMem z with hE
    let p : _ → Prop := fun r : Unit × ((({j // j ≠ z} → Option HashOutput) ×
      (Database HashOutput HashDomain × Database HashOutput HashDomain)) ×
        (Hw HashOutput HashDomain × QMem)) ↦ r.2.2.2.2 l e ≠ none
    have hP : diagonal (fun a : Unit × RReg SelMem ↦ if p (E a).2 then (1 : ℂ) else 0) =
        diagonal (fun a : Unit × RReg SelMem ↦
          (fun w : Hw HashOutput HashDomain × QMem ↦ if w.2.2 l e ≠ none then (1 : ℂ) else 0)
            a.2.2) := rfl
    have hsplit : diagonal (fun a : Unit × RReg SelMem ↦
        if (E a).1 = none ∧ p (E a).2 then (1 : ℂ) else 0) =
        liftCell E (diagonal fun o : Option HashOutput ↦ if o = none then (1 : ℂ) else 0) *
          diagonal (fun a : Unit × RReg SelMem ↦ if p (E a).2 then (1 : ℂ) else 0) := by
      rw [liftCell_diagonal, diagonal_mul_diagonal]
      congr 1
      funext a
      by_cases h1 : (E a).1 = none <;> by_cases h2 : p (E a).2 <;> simp [h1, h2]
    have hD : C * diagonal (fun a : Unit × RReg SelMem ↦
        if (E a).1 = none ∧ p (E a).2 then (1 : ℂ) else 0) * C =
        liftCell E (cellUnifProj HashOutput) *
          diagonal (fun a : Unit × RReg SelMem ↦ if p (E a).2 then (1 : ℂ) else 0) := by
      have hcomm : C * diagonal (fun a : Unit × RReg SelMem ↦
          (fun w : Hw HashOutput HashDomain × QMem ↦ if w.2.2 l e ≠ none then (1 : ℂ) else 0)
            a.2.2) = diagonal (fun a : Unit × RReg SelMem ↦
          (fun w : Hw HashOutput HashDomain × QMem ↦ if w.2.2 l e ≠ none then (1 : ℂ) else 0)
            a.2.2) * C := compress_mul_diagonal_mem
        (fun w : Hw HashOutput HashDomain × QMem ↦ if w.2.2 l e ≠ none then (1 : ℂ) else 0)
      have hG : C * liftCell E (diagonal fun o : Option HashOutput ↦
          if o = none then (1 : ℂ) else 0) * C = liftCell E (cellUnifProj HashOutput) := by
        rw [hE, ← cellCompress_mul_noneInd_mul]
        exact conj_lensH z _
      rw [hsplit, Matrix.mul_assoc C, Matrix.mul_assoc, hP, ← hcomm]
      simp only [← Matrix.mul_assoc]
      rw [hG]
    have hdec : ∀ a b, (C * σ * C) a b ≠ 0 → p (E a).2 →
        (E a).1 = some ((rd z).getD 0) := by
      intro a b hab hpa
      have h := hs a b (by rw [MatrixMap.conj_apply, hCh]; exact hab)
      exact cell_eq_of_rgInv h.1 hpa
    have key := re_trace_empty_le E one_kron_compressReg_mul_self hCh p hD ((rd z).getD 0) hσ
      hdec
    have he : ∑ q, selWt z l e q.2 * (σ q q).re =
        ∑ a : Unit × RReg SelMem, if (E a).1 = none ∧ p (E a).2 then (σ a a).re else 0 := by
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      unfold selWt
      by_cases h1 : q.2.1.1 z = none ∧ q.2.2.2.2 l e ≠ none
      · have h2 : (E q).1 = none ∧ p (E q).2 := h1
        rw [ite_eq_left h1, ite_eq_left h2, one_mul]
      · have h2 : ¬((E q).1 = none ∧ p (E q).2) := h1
        rw [ite_eq_right h1, ite_eq_right h2, zero_mul]
    rw [he, ← ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _))]
    exact ENNReal.ofReal_le_ofReal key

end trial

/-! ## The prefix -/

/-- **The empty read cells of selected keys along the prefix**: against an adversary that reuses
no leaf, with at most `K` classical calls, `selPre A θ ≤ K / |Y|`. -/
theorem selPre_le_card (A : Adversary) (hleaf : NoLeafReuse A) (θ : HPos → Digest) {K : ℕ}
    (hK : IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0) K) :
    selPre A θ ≤ ENNReal.ofReal ((Fintype.card HashOutput : ℝ)⁻¹) * K := by
  unfold selPre preTot
  refine (totalWeight_le_of_forallQueries (runtimeR m0Q) .instruments
    (fun i σ ↦ ∃ μ, rgOkZ θ μ i ∧
      QuerySupportedOn (fun m : (RSpec SelMem).In i × RReg SelMem ↦ m.2) (rgInv θ μ)
        (MatrixMap.conj ((1 : Matrix ((RSpec SelMem).In i) ((RSpec SelMem).In i) ℂ) ⊗ₖ
          compressReg HashOutput HashDomain QMem) σ))
    (fun _ _ _ h ↦ h)
    (w' := fun i σ ↦ ENNReal.ofReal ((Fintype.card HashOutput : ℝ)⁻¹) * trW i σ)
    (fun i σ hσ hI ↦ ?_) (prefixQ A θ) initQ_posSemidef (forallQueries_rgInv θ hleaf)).trans ?_
  · rcases i with ((p | c) | c) | T
    · exact zero_le
    · obtain ⟨μ, hok, hs⟩ := hI
      exact trialW_selWt_le hok hσ hs
    · exact zero_le
    · exact zero_le
  · exact (le_of_eq (totalWeight_const_mul_weight (runtimeR m0Q) .instruments
      (ENNReal.ofReal ((Fintype.card HashOutput : ℝ)⁻¹)) trW (prefixQ A θ) initQ)).trans
      (mul_le_mul_of_nonneg_left (totalWeight_trW_le _ hK) zero_le)

theorem inv_card_hashOutput_le : (Fintype.card HashOutput : ℝ)⁻¹ ≤ (2 ^ 128 : ℝ)⁻¹ := by
  rw [card_hashOutput, Nat.cast_pow, Nat.cast_ofNat]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))

/-- **The empty read cells of selected keys along the prefix**, at `2^-128` per classical call. -/
theorem selPre_le_small (A : Adversary) (hleaf : NoLeafReuse A) (θ : HPos → Digest) {K : ℕ}
    (hK : IFreeM.IsChargeBound (prefixQ A θ) (portCharge fun i ↦
      if extCls HashOutput HashDomain QMem (recSpec HPos SelMem) i then 1 else 0) K) :
    selPre A θ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * K := by
  refine (selPre_le_card A hleaf θ hK).trans (mul_le_mul_of_nonneg_right ?_ zero_le)
  refine (ENNReal.ofReal_le_ofReal inv_card_hashOutput_le).trans_eq ?_
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]

end Quantum.Qrom.Xmss

end
