/-
  LeanVM.Guest.B1.Tables.Vt.Evals

  `verify_tables`' table evaluations: the 153 words read after the table sumcheck, their
  claims, and the carried sponge after them, from which the public input's challenge is squeezed.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.EvalsT
public import LeanVM.Guest.B1.Gkr.Root

/-!
# The table evaluations (G:2635-2646, 2725)

`vt_eval`: evaluation `k`'s read at `col_eval_words` (the cursor `σ 2647`), packing and copy.
`vt_evals_fs`: from the last round's sponge, the 153 words absorbed leave the sponge whose
capacity permutation `j` reads; `vt_evals`: the public input's challenge `rm` is the squeeze after
them, the returned capacity the sponge after it.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The 153 evaluations' values. -/
def vtEvs (σ : Val) : List E := (List.range 153).map fun k ↦ σ (.n (vtEvB k))

/-- The capacity before permutation `j`. -/
def vtCapV (σ : Val) (j : ℕ) : List E := (vtPermCap j).map σ

theorem vtEvs_length (σ : Val) : (vtEvs σ).length = 153 := by simp [vtEvs]

theorem vtEvs_getD (σ : Val) {k : ℕ} (hk : k < 153) : (vtEvs σ).getD k 0 = σ (.n (vtEvB k)) := by
  simp [vtEvs, List.getD_eq_getElem?_getD, hk]

/-- **Evaluation `k`.** -/
theorem vt_eval {rd : Reader} {σ : Val} (h : VtH rd σ) {k : ℕ} (hk : k < 153) :
    LoadHolds rd (σ (.n 2647)) k (σ (.n (vtEvB k))) ∧
      FsPackOk σ (.n (vtEvB k)) (vtEvB k + 1) dsObserve ∧
      σ (.n (vtEvB k + 3)) = σ (.n (vtEvB k)) := by
  obtain ⟨_, hs⟩ := h.sliceAt _ _ (vtEval_check k hk)
  unfold vtEvalT at hs
  rw [tb_holdsList_append_noRet (by simp [fsNextT, fsPackT]; rfl), holds_fsNextT] at hs
  obtain ⟨⟨⟨hl, hp⟩, -⟩, hr⟩ := hs
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hr
  exact ⟨hl, hp, hr⟩

theorem vt_four_eq (σ : Val) {j : ℕ} (hj : j < 38) :
    ((vtEvs σ).drop (4 * j)).take 4 = [σ (.n (vtEvB (4 * j))), σ (.n (vtEvB (4 * j + 1))),
      σ (.n (vtEvB (4 * j + 2))), σ (.n (vtEvB (4 * j + 3)))] := by
  apply List.ext_getElem (by simp [vtEvs]; omega)
  intro i h1 h2
  simp only [List.length_take, List.length_drop, vtEvs, List.length_map, List.length_range] at h1
  simp only [List.getElem_take, List.getElem_drop, vtEvs, List.getElem_map, List.getElem_range]
  have : i < 4 := by omega
  interval_cases i <;> rfl

theorem fs_absorbAll_append (s : Fs) (l1 l2 : List E) (t : ℕ) :
    s.absorbAll (l1 ++ l2) t = (s.absorbAll l1 t).absorbAll l2 t := by
  simp [Fs.absorbAll, List.foldl_append]

/-- **Permutation `j`'s state.** After `4(j + 1)` evaluations the sponge carries `vtCapV j` with
the last four waiting, and permutation `j`'s capacity outputs are its permutation's. -/
theorem vt_evals_fs {rd : Reader} {σ : Val} (h : VtH rd σ) :
    ∀ j < 38, (⟨vtCapV σ 0, []⟩ : Fs).absorbAll ((vtEvs σ).take (4 * (j + 1))) dsObserve =
      ⟨vtCapV σ j, (((vtEvs σ).drop (4 * j)).take 4).map (·, dsObserve)⟩ ∧
      vtCapV σ (j + 1) = capOf (Fs.perm ⟨vtCapV σ j,
        (((vtEvs σ).drop (4 * j)).take 4).map (·, dsObserve)⟩) := by
  -- permutation `j`'s facts
  have hperm : ∀ j < 38, vtCapV σ (j + 1) = capOf (Fs.perm ⟨vtCapV σ j,
      (((vtEvs σ).drop (4 * j)).take 4).map (·, dsObserve)⟩) := by
    intro j hj
    have hk := h.atomAt _ _ (vtPerm_check j hj)
    obtain ⟨-, hC⟩ := ly_keccak hk
    have cell : ∀ i < 4, σ (.n (vtEvB (4 * j + i) + 1)) =
        (Keccak.scalarCells (σ (.n (vtEvB (4 * j + i)))) dsObserve).1 ∧
        σ (.n (vtEvB (4 * j + i) + 2)) =
        (Keccak.scalarCells (σ (.n (vtEvB (4 * j + i)))) dsObserve).2 := by
      intro i hi
      have e := fsPackT_cells (vt_eval h (k := 4 * j + i) (by omega)).2.1
      exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
    have c0 := cell 0 (by norm_num)
    simp only [Nat.add_zero] at c0
    have hin : ((((List.range 4).flatMap fun i ↦ [V.n (vtEvB (4 * j + i) + 1),
        .n (vtEvB (4 * j + i) + 2)]) ++ vtPermCap j).map σ) =
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
