/-
  LeanVM.Guest.B1.Tables.VtC.FEvals

  `Vt/Evals.lean` on the window `VtF`: an evaluation's read, packing and copy, and the sponge
  after the evaluations.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.FBase
public import LeanVM.Guest.B1.Tables.Vt.Evals

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The evaluations' and permutations' statements lie in the window. -/
theorem vtEval_inF : ∀ k < 159, vtFLo ≤ (vtEvalData.getD k (0, 0)).1 ∧
    (vtEvalData.getD k (0, 0)).1 + (vtEvalT (vtEvalData.getD k (0, 0)).2 k).length ≤ vtFHi := by
  decide +kernel

theorem vtPerm_inF : ∀ j < 39, vtFLo ≤ (vtPermData.getD j (0, 0)).1 ∧
    (vtPermData.getD j (0, 0)).1 + 1 ≤ vtFHi := by
  decide +kernel

/-- **Evaluation `k`**, on the window. -/
theorem vt_evalF {rd : Reader} {σ : Val} (h : VtF rd σ) {k : ℕ} (hk : k < 159) :
    LoadHolds rd (σ (.n 2625)) k (σ (.n (vtEvB k))) ∧
      FsPackOk σ (.n (vtEvB k)) (vtEvB k + 1) dsObserve ∧
      σ (.n (vtEvB k + 10)) = σ (.n (vtEvB k)) := by
  obtain ⟨_, hs⟩ := h.sliceAt _ _ (vtEval_check k hk) (vtEval_inF k hk)
  unfold vtEvalT at hs
  rw [tb_holdsList_append_noRet (by simp [fsNextT, fsPackT]; rfl), holds_fsNextT] at hs
  obtain ⟨⟨⟨hl, hp⟩, -⟩, hr⟩ := hs
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hr
  exact ⟨hl, hp, hr⟩

/-- **Permutation `j`'s state**, on the window. -/
theorem vt_evals_fsF {rd : Reader} {σ : Val} (h : VtF rd σ) :
    ∀ j < 39, (⟨vtCapV σ 0, []⟩ : Fs).absorbAll ((vtEvs σ).take (4 * (j + 1))) dsObserve =
      ⟨vtCapV σ j, (((vtEvs σ).drop (4 * j)).take 4).map (·, dsObserve)⟩ ∧
      vtCapV σ (j + 1) = capOf (Fs.perm ⟨vtCapV σ j,
        (((vtEvs σ).drop (4 * j)).take 4).map (·, dsObserve)⟩) := by
  have hperm : ∀ j < 39, vtCapV σ (j + 1) = capOf (Fs.perm ⟨vtCapV σ j,
      (((vtEvs σ).drop (4 * j)).take 4).map (·, dsObserve)⟩) := by
    intro j hj
    have hk := h.atomAt _ _ (vtPerm_check j hj) (vtPerm_inF j hj)
    obtain ⟨hcan, -, hC⟩ := ly_keccak hk
    have cell : ∀ i < 4, σ (.n (vtEvB (4 * j + i) + 7)) =
        (Keccak.scalarCells (σ (.n (vtEvB (4 * j + i)))) dsObserve).1 ∧
        σ (.n (vtEvB (4 * j + i) + 9)) =
        (Keccak.scalarCells (σ (.n (vtEvB (4 * j + i)))) dsObserve).2 := by
      intro i hi
      apply tb_pack_cells (vt_evalF h (k := 4 * j + i) (by omega)).2.1
      apply hcan
      simp only [List.map_append, List.mem_append, List.map_flatMap, List.mem_flatMap,
        List.mem_range, List.map_cons, List.map_nil, List.mem_cons]
      exact Or.inl ⟨i, hi, Or.inl rfl⟩
    have c0 := cell 0 (by norm_num)
    simp only [Nat.add_zero] at c0
    have hin : ((((List.range 4).flatMap fun i ↦ [V.n (vtEvB (4 * j + i) + 7),
        .n (vtEvB (4 * j + i) + 9)]) ++ vtPermCap j).map σ) =
        rateOf ((((vtEvs σ).drop (4 * j)).take 4).map (·, dsObserve)) ++ vtCapV σ j := by
      rw [vt_four_eq σ hj, rateOf_eq_cells _ (by simp)]
      simp only [vtCapV, List.range_succ, List.range_zero, List.nil_append,
        List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
        pendCells, List.length_cons, List.length_nil, List.cons_append, List.append_nil,
        Nat.add_zero, c0.1, c0.2, (cell 1 (by norm_num)).1, (cell 1 (by norm_num)).2, (cell 2 (by norm_num)).1,
        (cell 2 (by norm_num)).2, (cell 3 (by norm_num)).1, (cell 3 (by norm_num)).2]
      rfl
    rw [hin] at hC
    rw [show vtCapV σ (j + 1) = (lyCap (vtPermData.getD j (0, 0)).2).map σ by
      simp [vtCapV, vtPermCap], hC]
    rfl
  intro j hj
  refine ⟨?_, hperm j hj⟩
  induction j with
  | zero =>
    rw [absorbAll_short _ _ _ (by simp [vtEvs])]
    simp [vtEvs]
  | succ j ih =>
    have ih' := ih (by omega)
    rw [show 4 * (j + 1 + 1) = 4 * (j + 1) + 4 by ring, List.take_add,
      fs_absorbAll_append, ih', tb_absorbAll_full' _ (by simp [vtEvs]; omega) _
        (by simp [vtEvs]; omega) (by simp), ← hperm j (by omega)]

end
end LeanVM.Guest.B1.Tables
