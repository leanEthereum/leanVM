module

public import Quantum.Qrom.Sphincs.Costs.RegrindInv
public import Quantum.Qrom.Xmss.Costs.Regrind

@[expose] public section

/-!
# Re-grinds: the recorded hits of the selected digests

A recorded trial read cell whose pair hits its key's selected digest (`recSWt`) costs at most
`2^-128` per unit of trace: in the decompressed basis the hit has no weight (`not_hitG_of_inv`:
a selection is the first codeword trial of the key's own search, the trials before the read no
codewords, and the search stops at its selection), and Persistence converts the recorded weight
of a one-digest content predicate (`Quantum.Sponge.re_trace_recH_le_of_dec`, leanXMSS's
`Costs/Regrind`).

## Main statements

* `trialW_recSWt_leG`: at a trial read presented an operator on the invariant, `recSWt` weighs at
  most `2^-128 tr σ`.
* `recSPre_le`: `recSPre pol A θ ≤ 2^-128 K` with at most `K` classical calls.
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

-- Keep elaboration from unfolding `univ` of the large `Fin` types.
attribute [local irreducible] Fin.fintype

/-! ## A trial read on the invariant -/

section trial

variable {θ : TVals}

/-- The content of a recorded hit of key `K` at the cell `z`, read from the memory. -/
def HitG (z : Qrom.HashDomain) (K : Key) (w : Hw PairOut Qrom.HashDomain × QMem)
    (o : Option PairOut) : Prop :=
  ∃ y sel, o = some y ∧ w.2.2 K = some sel ∧ sel.1 ≠ z ∧ pairDigest y = sel.2

open scoped Classical in
theorem cellFrac_hitG_le (z : Qrom.HashDomain) (K : Key) (w : Hw PairOut Qrom.HashDomain × QMem) :
    cellFrac (HitG z K w) ≤ (2 ^ 128 : ℝ)⁻¹ := by
  unfold cellFrac
  rw [← pairFiber_div_card_real]
  gcongr
  unfold HitG
  rcases hw : w.2.2 K with _ | sel
  · simp
  · exact_mod_cast (Finset.card_le_card fun y hy ↦ by
      rw [Finset.mem_filter] at hy ⊢
      obtain ⟨y', sel', h1, h2, -, h4⟩ := hy.2
      cases h1
      cases h2
      exact ⟨Finset.mem_univ _, h4⟩).trans (card_fiber_pairDigest_le sel.2)

/-- **No decompressed hit at a trial read**: the key's selection is the first codeword trial of
its search, the trials before the read no codewords, so the read cell's pair does not have the
selected digest. -/
theorem not_hitG_of_inv {μ : RgModeG} {s : RegQ} (hs : s ∈ rgInvG θ μ) {K : Key} {j : ℕ}
    (hc : curG θ μ.1 (tcG θ K j) = some (K, j)) :
    (s.1.1 (tcG θ K j)).isSome ∧ ¬HitG (tcG θ K j) K s.2 (s.1.1 (tcG θ K j)) := by
  obtain ⟨hnb, hhw, -, hsel⟩ := globG_of_inv hs
  have hpre := noPreG_of_curG hs hc
  refine ⟨hnb.1 _, ?_⟩
  rintro ⟨y, sel, hy, hs', hne, ht⟩
  have hv : hvwS s (tcG θ K j) = y := by
    show (((s.2.1.1 (tcG θ K j)).or (s.1.1 (tcG θ K j))).getD 0) = y
    rw [hhw K j, hy]
    rfl
  obtain ⟨j', h1, -, h3, h4, h5⟩ := hsel K sel hs'
  rcases lt_trichotomy j' j with hlt | rfl | hgt
  · have h := (hpre j' hlt).2
    rw [← h1, ← h3] at h
    exact h h4
  · exact hne h1
  · have h := (h5 j hgt).2
    rw [hv, ht] at h
    exact h h4

/-- **The recorded hits at a trial read on the invariant** weigh at most `2^-128 tr σ`. -/
theorem trialW_recSWt_leG {μ : RgModeG} {c : HwRead PairOut Qrom.HashDomain QMem}
    (hok : RdOkG θ μ.1 c) {σ : Matrix (Unit × RegQ) (Unit × RegQ) ℂ} (hσ : σ.PosSemidef)
    (hs : QuerySupportedOn (fun m : Unit × RegQ ↦ m.2) (rgInvG θ μ)
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg PairOut Qrom.HashDomain QMem) σ)) :
    trialW (pkQ θ) recSWt c σ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * ENNReal.ofReal σ.trace.re := by
  classical
  obtain ⟨K, j, hc, rfl⟩ := hok
  rw [trialW_trialRead _ (slotOf_tcG θ K j)]
  have hconv := re_trace_recH_le_of_dec (tcG θ K j) (HitG (tcG θ K j) K)
    (fun _ ⟨_, _, h, _⟩ ↦ by cases h) (cellFrac_hitG_le _ K) hσ
    (hs.mono fun s hs' ↦ not_hitG_of_inv hs' hc)
  have he : ∑ q, recSWt (tcG θ K j) K q.2 * (σ q q).re =
      ∑ q : Unit × RegQ, if HitG (tcG θ K j) K q.2.2 (q.2.1.1 (tcG θ K j)) then (σ q q).re
        else 0 := by
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    unfold recSWt
    by_cases h1 : RecHitQ (tcG θ K j) K q.2
    · have h2 : HitG (tcG θ K j) K q.2.2 (q.2.1.1 (tcG θ K j)) := h1
      rw [ite_eq_left h1, ite_eq_left h2, one_mul]
    · have h2 : ¬HitG (tcG θ K j) K q.2.2 (q.2.1.1 (tcG θ K j)) := h1
      rw [ite_eq_right h1, ite_eq_right h2, zero_mul]
  rw [he]
  refine (ENNReal.ofReal_le_ofReal hconv).trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

end trial

/-! ## The prefix -/

/-- **The recorded hits of the selected digests along the prefix**: with at most `K` classical
calls, `recSPre pol A θ ≤ 2^-128 K`. -/
theorem recSPre_le (pol : DigestPolicy) (A : SAdversary) (θ : TVals) {K : ℕ}
    (hK : IFreeM.IsChargeBound (prefixQ pol A θ) (portCharge fun i ↦
      if extCls PairOut Qrom.HashDomain QMem (recSpec TPos SelMem) i then 1 else 0) K) :
    recSPre pol A θ ≤ (2 ^ 128 : ℝ≥0∞)⁻¹ * K := by
  unfold recSPre preTot
  refine (totalWeight_le_of_forallQueries (runtimeR m0Q) .instruments
    (fun i σ ↦ ∃ μ, rgOkZG θ μ i ∧
      QuerySupportedOn (fun m : (RSpecS SelMem).In i × RegQ ↦ m.2) (rgInvG θ μ)
        (MatrixMap.conj ((1 : Matrix ((RSpecS SelMem).In i) ((RSpecS SelMem).In i) ℂ) ⊗ₖ
          compressReg PairOut Qrom.HashDomain QMem) σ))
    (fun _ _ _ h ↦ h) (w' := fun i σ ↦ (2 ^ 128 : ℝ≥0∞)⁻¹ * trW i σ) (fun i σ hσ hI ↦ ?_)
    (prefixQ pol A θ) initQ_posSemidef (forallQueries_rgInvG θ pol A)).trans ?_
  · rcases i with ((p | c) | c) | T
    · exact zero_le
    · obtain ⟨μ, hok, hs⟩ := hI
      exact trialW_recSWt_leG hok hσ hs
    · exact zero_le
    · exact zero_le
  · exact (le_of_eq (totalWeight_const_mul_weight (runtimeR m0Q) .instruments
      ((2 ^ 128 : ℝ≥0∞)⁻¹) trW (prefixQ pol A θ) initQ)).trans
      (mul_le_mul_of_nonneg_left (totalWeight_trW_le _ hK) zero_le)

end Quantum.Qrom.Sphincs

end
