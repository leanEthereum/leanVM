/-
  LeanVM.Guest.B1.Terminal.TermWeight

  `check_opening_terminal` complete, placed, within its bound, by a tree within its weights: its
  callees by name within their words (`completeAt_flatDepRBPR`), each callee's weight by its
  certificate or, `check_opening_terminal_loop0`'s and `ring_switch_weight`'s, by its words.
-/

module

public import LeanVM.Guest.B1.Terminal.TermCompleteB
public import LeanVM.Guest.B1.Terminal.KidsDepBT
public import LeanVM.Guest.Budget.Weighs
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.LitRef

/-!
# The terminal within its weights

`termNames D`: the terminal's callees' names, in call order (the column selectors' by the columns'
sizes `D.KC`). `termWs`: their weight bounds. `term_weight_le`: a node of `Budget.FlatShape` for
`termNames`, `termBs` weighs at most its frame's weight and `termWs` at each `ω i`.
`check_opening_terminal_completeAtBWE` (`Exact/Terminal.lean`): `check_opening_terminal` within its bound, by a
tree within those weights.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **The terminal's callees' names**, in call order. -/
def termNames (D : TermData) : List String :=
  ["eq_prefix_chain", "eq_prefix_chain", name% «check_opening_terminal_loop0», "selector_tables"] ++
    (List.range Tables.nCommittedCols).map (fun c => Tables.lName "column_selector" (D.KC.getD c 0)) ++
    ["eq_prefix_chain", "ring_switch_weight", "eq_prefix_chain"]

/-- **The terminal's callees' weight bounds**, in call order. -/
def termWs {ι : Type} (Weqc W15 Wst Wcs Wrsw : ι → ℕ) (i : ι) : List ℕ :=
  [Weqc i, Weqc i, W15 i, Wst i] ++ List.replicate Tables.nCommittedCols (Wcs i) ++ [Weqc i, Wrsw i, Weqc i]

theorem termKids_names (Lin : Main.Layout) (D : TermData) (b0 : ℕ) :
    List.Forall₂ (fun k n ↦ ∀ pv, (k pv).f = n) (termKids Lin D b0) (termNames D) := by
  unfold termKids termNames
  refine List.rel_append (List.rel_append ?_ ?_) ?_
  · exact .cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) .nil)))
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr fun _ _ _ => rfl
  · exact .cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) .nil))

/-- **The terminal's node weighs at most** its frame's weight and `termWs` at each `ω i`. -/
theorem term_weight_le {ι : Type} (ω : ι → String → ℕ) (Weqc W15 Wst Wcs Wrsw : ι → ℕ)
    (hEqcW : ∀ i, WeightLe coreProgram (ω i) "eq_prefix_chain" fun _ => Weqc i)
    (hStW : ∀ i, WeightLe coreProgram (ω i) "selector_tables" fun _ => Wst i)
    (hCsW : ∀ i, ∀ κ' < 31, WeightLe coreProgram (ω i) (Tables.lName "column_selector" κ')
      fun _ => Wcs i)
    {K15 Brs Beqc Bcs : ℕ}
    (h15W : ∀ i (rd : Reader) (t : Tree) (args rets : List E),
        t.name = name% «check_opening_terminal_loop0» →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ (32 * K15 + fs name% «check_opening_terminal_loop0») → t.weight (ω i) ≤ W15 i)
    (hrswW : ∀ i (rd : Reader) (t : Tree) (args rets : List E), t.name = "ring_switch_weight" →
      t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.total fs ≤ fs "ring_switch_weight" + lit% termRswChain + Brs → t.weight (ω i) ≤ Wrsw i)
    {D : TermData} (hKC : ∀ c < Tables.nCommittedCols, D.KC.getD c 0 < 31) {t : Tree}
    (h : Budget.FlatShape coreProgram "check_opening_terminal"
      (List.zipWith (Budget.NamedWithin fs) (termNames D) (termBs fs Beqc K15 Bcs Brs)) t)
    {rd : Reader} {args rets : List E} (hv : t.Valid coreProgram rd args rets)
    (hb : t.BufsOk coreProgram) (i : ι) :
    t.weight (ω i) ≤ ω i "check_opening_terminal" + (termWs Weqc W15 Wst Wcs Wrsw i).sum := by
  refine Budget.FlatShape.weight_le (ω i) _ h hv hb
    (by simp [termNames, termBs, termWs, Tables.nCommittedCols]) ?_
  intro j hT hW rd' t' args' rets' hv' hb' hTj
  rw [List.getElem_zipWith] at hTj
  obtain ⟨hn, htot⟩ := hTj
  have hj : j < 101 := by simpa [termWs, Tables.nCommittedCols] using hW
  by_cases h4 : j < 4
  · interval_cases j <;>
      simp only [termNames, termBs, termWs, List.append_assoc, List.cons_append,
        List.getElem_cons_zero, List.getElem_cons_succ] at hn htot ⊢
    · exact hEqcW i rd' t' args' rets' hn hv' hb'
    · exact hEqcW i rd' t' args' rets' hn hv' hb'
    · exact h15W i rd' t' args' rets' hn hv' hb' htot
    · exact hStW i rd' t' args' rets' hn hv' hb'
  by_cases h98 : j < 98
  · have e1 : (termNames D)[j]'(by simp [termNames, Tables.nCommittedCols]; omega) =
        Tables.lName "column_selector" (D.KC.getD (j - 4) 0) := by
      simp only [termNames, List.append_assoc]
      rw [List.getElem_append_right (by simp; omega), List.getElem_append_left
        (by simp [Tables.nCommittedCols]; omega)]
      simp
    have e2 : (termWs Weqc W15 Wst Wcs Wrsw i)[j]'hW = Wcs i := by
      simp only [termWs, List.append_assoc]
      rw [List.getElem_append_right (by simp; omega), List.getElem_append_left
        (by simp [Tables.nCommittedCols]; omega)]
      simp
    rw [e1] at hn
    rw [e2]
    exact hCsW i _ (hKC _ (by simp [Tables.nCommittedCols]; omega)) rd' t' args' rets' hn hv' hb'
  · have hj' : j = 98 ∨ j = 99 ∨ j = 100 := by omega
    rcases hj' with rfl | rfl | rfl <;>
      simp [termNames, termBs, termWs, Tables.nCommittedCols, List.getElem_append_right] at hn htot ⊢
    · exact hEqcW i rd' t' args' rets' hn hv' hb'
    · exact hrswW i rd' t' args' rets' hn hv' hb' htot
    · exact hEqcW i rd' t' args' rets' hn hv' hb'

end
end LeanVM.Guest.B1.VerifySub
