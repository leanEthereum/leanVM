/-
  LeanVM.Guest.B1.Tables.VtFitsC

  `verify_tables`' selectors' placements fit the push side's depth (`VtFits`).
-/

module

public import LeanVM.Guest.B1.Tables.VtPlaced

/-!
# The placements fit

The push layout's sizes are the push blocks' log-heights `vtKs` (`vtKs_push`), so its depth `μ`
is the log of their total: every push block's log-height is at most `μ`, its offset plus its size
at most the total, and its offset aligned (`stackOffsets_dvd`). The count blocks share their
owners' log-heights, each owner with no more count blocks than push blocks, so the count side's
total is at most the push side's.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
theorem selBlk_split : ∀ i < 65, selBlk.getD i 0 = if i < 37 then i else 74 + (i - 37) := by
  decide +kernel

/-- Each owner has no more count blocks than push blocks. -/
theorem count_le_push (f : ℕ → ℕ) : (layoutCountOwners.map f).sum ≤ (layoutPushOwners.map f).sum := by
  simp only [layoutCountOwners, layoutPushOwners, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  omega

set_option maxHeartbeats 4000000 in
/-- **The selectors' placements fit the push depth** (`VtFits`). -/
theorem vt_fits : VtFits := by
  intro bytecode hb logMem rowsN h16 hlm32 hrl hτ29 τs μ
  obtain ⟨-, -, -, -, hpl, -, -, -⟩ := layoutOf_blocks bytecode hb logMem rowsN hrl
  have hS : [0, logMem, 18] ++ (layoutOf bytecode logMem rowsN).push.map (·.logRows) =
      (List.range 37).map (vtKs logMem τs) := by rw [hpl, vtKs_push]
  have hμ : μ = log2Ceil (((List.range 37).map (vtKs logMem τs)).map (2 ^ ·)).sum := by
    show (busLayout [0, logMem, 18] _).depth = _
    rw [busLayout_depth, hS]
  have hT := le_two_pow_log2Ceil (((List.range 37).map (vtKs logMem τs)).map (2 ^ ·)).sum
  rw [← hμ] at hT
  have single : ∀ b < 37, vtKs logMem τs b ≤ μ := fun b hb' => by
    have := single_le_sum_map ((List.range 37).map (vtKs logMem τs)) b (by simp; exact hb')
    rw [getD_map_range _ _ hb'] at this
    rw [hμ]; exact le_log2Ceil_of_two_pow_le this
  have hτμ : ∀ t < 6, τs t ≤ μ := by
    intro t ht
    interval_cases t
    · exact single 3 (by omega)
    · exact single 8 (by omega)
    · exact single 13 (by omega)
    · exact single 16 (by omega)
    · exact single 21 (by omega)
    · exact single 26 (by omega)
  refine ⟨single 1 (by omega), single 2 (by omega), hτμ, fun i hi => ?_⟩
  rw [selBlk_split i hi]
  by_cases h37 : i < 37
  · rw [ite_pos' h37]
    have hb := stackOffsets_bound ((List.range 37).map (vtKs logMem τs)) (c := i) (by simp; exact h37)
    have hd := stackOffsets_dvd ((List.range 37).map (vtKs logMem τs)) (c := i) (by simp; exact h37)
    rw [getD_map_range _ _ h37] at hb hd
    have hp := Nat.one_le_two_pow (n := vtKs logMem τs i)
    refine ⟨single i h37, ?_, ?_⟩
    · rw [selOff, ite_pos' h37, pushOff]; omega
    · rw [selOff, ite_pos' h37, pushOff]; exact hd
  · rw [ite_neg' h37]
    have hj : i - 37 < 28 := by omega
    have hb := stackOffsets_bound ((List.range 28).map fun j => vtKs logMem τs (74 + j)) (c := i - 37)
      (by simp; exact hj)
    have hd := stackOffsets_dvd ((List.range 28).map fun j => vtKs logMem τs (74 + j)) (c := i - 37)
      (by simp; exact hj)
    rw [getD_map_range _ _ hj] at hb hd
    have hCT : (((List.range 28).map fun j => vtKs logMem τs (74 + j)).map (2 ^ ·)).sum ≤
        (((List.range 37).map (vtKs logMem τs)).map (2 ^ ·)).sum := by
      rw [vtKs_count, vtKs_push, List.map_append, List.sum_append, List.map_map, List.map_map]
      have := count_le_push (fun t => 2 ^ τs t)
      exact le_trans this (Nat.le_add_left _ _)
    have hp := Nat.one_le_two_pow (n := vtKs logMem τs (74 + (i - 37)))
    refine ⟨?_, ?_, ?_⟩
    · rw [hμ]; exact le_log2Ceil_of_two_pow_le (by omega)
    · rw [selOff, ite_neg' h37, countOff]; omega
    · rw [selOff, ite_neg' h37, countOff]; exact hd

end
end LeanVM.Guest.B1.VerifySub
