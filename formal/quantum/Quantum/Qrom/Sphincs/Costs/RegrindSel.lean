module

public import Quantum.Qrom.Sphincs.Costs.Regrind
public import Quantum.Qrom.Xmss.Costs.RegrindSel

@[expose] public section

/-!
# Re-grinds: the empty read cells of selected keys

An empty trial read cell of a selected key (`selWt`) costs at most `1/|Y × Y|` per unit of trace.
In the decompressed basis the key's selection is the first codeword trial of its search, at or
after the read trial, so the search already read the cell (`cell_eq_of_invG`) and the
decompressed cell holds the pair recorded at that read; the compression maps the empty cell to
the uniform superposition, whose overlap with one pair is `1/|Y × Y|` (leanXMSS's
`Quantum.Qrom.Xmss.re_trace_empty_le`).

## Main statements

* `trialW_selWt_leG`: at a trial read on the invariant, `selWt` weighs at most `tr σ / |Y × Y|`.
* `selPre_le_cardG`: `selPre pol A θ ≤ K / |Y × Y|`; `selPre_le_small`:
  `selPre pol A θ ≤ 2^-128 K`, with at most `K` classical calls.
-/

open Matrix IPFunctor
open scoped ENNReal Kronecker ComplexOrder
open HashSig hiding PublicKey
open Sphincs hiding HashDomain

namespace Quantum.Qrom.Sphincs

open Quantum QuantumRuntime Quantum.Sponge
open Quantum.Sphincs (Key)
open Quantum.Xmss.Assembly (recSpec runtimeR extWeight extCls NoBot
  totalWeight_le_of_forallQueries)
open Quantum.Xmss.Hybrid (totalWeight_const_mul_weight)

attribute [local irreducible] sphincsRom

/- Instance search for the register's decidable equality exceeds the default size. -/
set_option synthInstance.maxSize 2000

/-! ## A trial read on the invariant -/

section trial

variable {θ : TVals}

/-- **The read cell of a selected key holds the recorded pair**: the key's selection is a trial
of its search at or after the read one, so the read trial was read before. -/
theorem cell_eq_of_invG {μ : RgModeG} {s : RegQ} (hs : s ∈ rgInvG θ μ) {K : Key} {j : ℕ}
    (hc : curG θ μ.1 (tcG θ K j) = some (K, j)) (hsel : s.2.2.2 K ≠ none) :
    s.1.1 (tcG θ K j) = some ((μ.2 (tcG θ K j)).getD 0) := by
  obtain ⟨hnb, hhw, hrd, hsl⟩ := globG_of_inv hs
  have hpre := noPreG_of_curG hs hc
  obtain ⟨sel, hs'⟩ := Option.ne_none_iff_exists'.mp hsel
  obtain ⟨j', h1, h2, h3, h4, h5⟩ := hsl K sel hs'
  have hrdz : μ.2 (tcG θ K j) ≠ none := by
    rcases lt_trichotomy j' j with hlt | rfl | hgt
    · have h := (hpre j' hlt).2
      rw [← h1, ← h3] at h
      exact absurd h4 h
    · rw [← h1]
      exact h2
    · exact (h5 j hgt).1
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.mp hrdz
  have hv := (hrd _ y hy).2
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.mp (hnb.1 (tcG θ K j))
  have hv' : hvwS s (tcG θ K j) = y' := by
    show ((s.2.1.1 (tcG θ K j)).or (s.1.1 (tcG θ K j))).getD 0 = y'
    rw [hhw K j, hy']
    rfl
  rw [hy', hy, Option.getD_some, ← hv, hv']

/-- The memory blocks of the hardwired register commute with the compression. -/
theorem compress_mul_diagonal_memG (d : Hw PairOut Qrom.HashDomain × QMem → ℂ) :
    ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg PairOut Qrom.HashDomain QMem) *
        diagonal (fun a : Unit × RegQ ↦ d a.2.2) =
      diagonal (fun a : Unit × RegQ ↦ d a.2.2) *
        ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg PairOut Qrom.HashDomain QMem) := by
  ext a b
  rw [mul_diagonal, diagonal_mul]
  by_cases h : a.2.2 = b.2.2
  · rw [h, mul_comm]
  · have h0 : ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg PairOut Qrom.HashDomain QMem) a b = 0 := by
      rw [kroneckerMap_apply, compressReg, kroneckerMap_apply, Matrix.one_apply_ne h, mul_zero,
        mul_zero]
    rw [h0, zero_mul, mul_zero]

/-- **The empty read cells of a selected key at a trial read on the invariant** weigh at most
`tr σ / |Y × Y|`. -/
theorem trialW_selWt_leG {μ : RgModeG} {c : HwRead PairOut Qrom.HashDomain QMem}
    (hok : RdOkG θ μ.1 c) {σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ} (hσ : σ.PosSemidef)
    (hs : QuerySupportedOn (fun m : Unit × RegQ ↦ m.2) (rgInvG θ μ)
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg PairOut Qrom.HashDomain QMem) σ)) :
    trialW (pkQ θ) selWt c σ ≤
      ENNReal.ofReal ((Fintype.card PairOut : ℝ)⁻¹) * ENNReal.ofReal σ.trace.re := by
  obtain ⟨K, j, hc, rfl⟩ := hok
  rw [trialW_trialRead _ (slotOf_tcG θ K j)]
  set z := tcG θ K j with hz
  set C := (1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg PairOut Qrom.HashDomain QMem with hC
  have hCh : Cᴴ = C := conjTranspose_one_kron_compressReg
  set E := lensH Unit QMem z with hE
  let p : _ → Prop := fun r : Unit × ((({j // j ≠ z} → Option PairOut) ×
    (Database PairOut Qrom.HashDomain × Database PairOut Qrom.HashDomain)) ×
      (Hw PairOut Qrom.HashDomain × QMem)) ↦ r.2.2.2.2 K ≠ none
  have hP : diagonal (fun a : Unit × RegQ ↦ if p (E a).2 then (1 : ℂ) else 0) =
      diagonal (fun a : Unit × RegQ ↦
        (fun w : Hw PairOut Qrom.HashDomain × QMem ↦ if w.2.2 K ≠ none then (1 : ℂ) else 0)
          a.2.2) := rfl
  have hsplit : diagonal (fun a : Unit × RegQ ↦
      if (E a).1 = none ∧ p (E a).2 then (1 : ℂ) else 0) =
      liftCell E (diagonal fun o : Option PairOut ↦ if o = none then (1 : ℂ) else 0) *
        diagonal (fun a : Unit × RegQ ↦ if p (E a).2 then (1 : ℂ) else 0) := by
    rw [liftCell_diagonal, diagonal_mul_diagonal]
    congr 1
    funext a
    by_cases h1 : (E a).1 = none <;> by_cases h2 : p (E a).2 <;> simp [h1, h2]
  have hD : C * diagonal (fun a : Unit × RegQ ↦
      if (E a).1 = none ∧ p (E a).2 then (1 : ℂ) else 0) * C =
      liftCell E (cellUnifProj PairOut) *
        diagonal (fun a : Unit × RegQ ↦ if p (E a).2 then (1 : ℂ) else 0) := by
    have hcomm : C * diagonal (fun a : Unit × RegQ ↦
        (fun w : Hw PairOut Qrom.HashDomain × QMem ↦ if w.2.2 K ≠ none then (1 : ℂ) else 0)
          a.2.2) = diagonal (fun a : Unit × RegQ ↦
        (fun w : Hw PairOut Qrom.HashDomain × QMem ↦ if w.2.2 K ≠ none then (1 : ℂ) else 0)
          a.2.2) * C := compress_mul_diagonal_memG
      (fun w : Hw PairOut Qrom.HashDomain × QMem ↦ if w.2.2 K ≠ none then (1 : ℂ) else 0)
    have hG : C * liftCell E (diagonal fun o : Option PairOut ↦
        if o = none then (1 : ℂ) else 0) * C = liftCell E (cellUnifProj PairOut) := by
      rw [hE, ← Quantum.Qrom.Xmss.cellCompress_mul_noneInd_mul]
      exact conj_lensH z _
    rw [hsplit, Matrix.mul_assoc C, Matrix.mul_assoc, hP, ← hcomm]
    simp only [← Matrix.mul_assoc]
    rw [hG]
  have hdec : ∀ a b, (C * σ * C) a b ≠ 0 → p (E a).2 →
      (E a).1 = some ((μ.2 z).getD 0) := by
    intro a b hab hpa
    have h := hs a b (by rw [MatrixMap.conj_apply, hCh]; exact hab)
    exact cell_eq_of_invG h.1 hc hpa
  have key := Quantum.Qrom.Xmss.re_trace_empty_le E one_kron_compressReg_mul_self hCh p hD
    ((μ.2 z).getD 0) hσ hdec
  have he : ∑ q, selWt z K q.2 * (σ q q).re =
      ∑ a : Unit × RegQ, if (E a).1 = none ∧ p (E a).2 then (σ a a).re else 0 := by
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    unfold selWt
    by_cases h1 : q.2.1.1 z = none ∧ q.2.2.2.2 K ≠ none
    · have h2 : (E q).1 = none ∧ p (E q).2 := h1
      rw [ite_eq_left h1, ite_eq_left h2, one_mul]
    · have h2 : ¬((E q).1 = none ∧ p (E q).2) := h1
      rw [ite_eq_right h1, ite_eq_right h2, zero_mul]
  rw [he, ← ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact ENNReal.ofReal_le_ofReal key

end trial

/-! ## The prefix -/

/-- **The empty read cells of selected keys along the prefix**: with at most `K` classical calls,
`selPre pol A θ ≤ K / |Y × Y|`. -/
theorem selPre_le_cardG (pol : DigestPolicy) (A : SAdversary) (θ : TVals) {K : ℕ}
    (hK : IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0) K) :
    selPre pol A θ ≤ ENNReal.ofReal ((Fintype.card PairOut : ℝ)⁻¹) * K := by
  unfold selPre preTot
  refine (totalWeight_le_of_forallQueries (runtimeR m0Q) .instruments
    (fun i σ ↦ ∃ μ, rgOkZG θ μ i ∧
      QuerySupportedOn (fun m : (RSpecS SelMem).In i × RegQ ↦ m.2) (rgInvG θ μ)
        (MatrixMap.conj ((1 : Matrix ((RSpecS SelMem).In i) ((RSpecS SelMem).In i) ℂ) ⊗ₖ
          compressReg PairOut Qrom.HashDomain QMem) σ))
    (fun _ _ _ h ↦ h)
    (w' := fun i σ ↦ ENNReal.ofReal ((Fintype.card PairOut : ℝ)⁻¹) * trW i σ)
    (fun i σ hσ hI ↦ ?_) (prefixQ pol A θ) initQ_posSemidef
    (forallQueries_rgInvG θ pol A)).trans ?_
  · rcases i with ((p | c) | c) | T
    · exact zero_le
    · obtain ⟨μ, hok, hs⟩ := hI
      exact trialW_selWt_leG hok hσ hs
    · exact zero_le
    · exact zero_le
  · exact (le_of_eq (totalWeight_const_mul_weight (runtimeR m0Q) .instruments
      (ENNReal.ofReal ((Fintype.card PairOut : ℝ)⁻¹)) trW (prefixQ pol A θ) initQ)).trans
      (mul_le_mul_of_nonneg_left (totalWeight_trW_le _ hK) zero_le)

theorem inv_card_pairOut_leG : (Fintype.card PairOut : ℝ)⁻¹ ≤ (2 ^ 128 : ℝ)⁻¹ := by
  rw [← pairFiber_div_card_real, inv_eq_one_div]
  gcongr
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)

/-- **The empty read cells of selected keys along the prefix**, at `2^-128` per classical call. -/
theorem selPre_le_small (pol : DigestPolicy) (A : SAdversary) (θ : TVals) {K : ℕ}
    (hK : IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0) K) :
    selPre pol A θ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * K := by
  refine (selPre_le_cardG pol A θ hK).trans (mul_le_mul_of_nonneg_right ?_ zero_le)
  refine (ENNReal.ofReal_le_ofReal inv_card_pairOut_leG).trans_eq ?_
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]

end Quantum.Qrom.Sphincs

end
