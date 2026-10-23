/-
  LeanVM.Guest.B1.Da.VerifyColumn

  B1 for `da_verify_column__L0` and `__L1` (G:2971-2997): one column of the matrix.
-/

module

public import LeanVM.Guest.B1.Da.Column

/-!
# `da_verify_column__L{store}`

`da_verify_column(xb, n_blob, n_pad, gap, g_log_pad, prefix_bases, coltree, rowbase, hashes,
counters)` reads the vector hash's state at `hashes·xb²`, absorbs the column's weights
(`da_vector_dispatch`), stores the next state at `hashes·(xb·g)²`, runs the row loop over the
`n_blob` rows of a fresh `node` tree (`RowCell`) and the gap loop over the padding rows
(`GapStep`), hashes the tree at the depth `g_log_pad` selects, and stores its root at
`coltree·xb²`. The tree's pointer is a hint: the meaning quantifies it.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- Row `x` of a column in Spec terms: `RowStep` with the cell check's meaning. -/
def RowCell (store : Bool) (rd : Reader) (lv rb xb node pb x : E) : Prop :=
  ∃ d0 d1 s R a, Meaning_da_verify_cell rd [lv] [d0, d1, s] ∧ LoadHolds rd (rb * x) 0 R ∧
    LoadHolds rd (R * xb) 0 a ∧ LoadHolds rd (R * xb) 1 (a + s) ∧ CellsAt rd (node * (x * x)) [d0, d1] ∧
    (store = true → ∃ P, LoadHolds rd (pb * x) 0 P ∧ CellsAt rd (P * (xb * xb)) [d0, d1])

/-- A `mul_range(1, W)` loop's iterations: `W = g^m`, `m` the first positive exponent reaching
`W`, and the body at every `j < m`. -/
def LoopTo (W : E) (B : ℕ → Prop) : Prop :=
  ∃ m, 0 < m ∧ W = gen ^ m ∧ (∀ j, 0 < j → j < m → gen ^ j ≠ W) ∧ ∀ j < m, B j

theorem rowStep_iff_cell {store : Bool} {rd : Reader} {lv rb xb node pb x : E} :
    RowStep store rd lv rb xb node pb (coreProgram.Rel rd) x ↔ RowCell store rd lv rb xb node pb x := by
  unfold RowStep RowCell; simp only [da_verify_cell_iff]

theorem row_loop_meaning (store : Bool) (rd : Reader) (W lv rb xb node pb : E) :
    coreProgram.Rel rd (rowName store) [1, W, lv, rb, xb, node, pb] [] ↔
      LoopTo W fun j => RowCell store rd lv rb xb node pb (gen ^ j) := by
  have := row_loop_iff store rd W lv rb xb node pb 0
  rw [pow_zero] at this
  rw [this]; unfold LoopTo; simp only [rowStep_iff_cell, Nat.zero_le, true_implies]

theorem gap_loop_meaning (store : Bool) (rd : Reader) (W node nb : E) :
    coreProgram.Rel rd (gapName store) [1, W, node, nb] [] ↔
      LoopTo W fun j => GapStep rd node nb (gen ^ j) := by
  have := gap_loop_iff store rd W node nb 0
  rw [pow_zero] at this
  rw [this]; unfold LoopTo; simp only [Nat.zero_le, true_implies]

/-- **`da_verify_column__L{store}`**. -/
def Meaning_da_verify_column (store : Bool) (rd : Reader) (args rets : List E) : Prop :=
  ∃ xb nb np gap glp pb ct rb hs ctr, args = [xb, nb, np, gap, glp, pb, ct, rb, hs, ctr] ∧
    rets = [] ∧ ∃ h0 h1 o0 o1 lv node c0 c1,
      CellsAt rd (hs * (xb * xb)) [h0, h1] ∧
      Meaning_da_vector_dispatch rd [xb, h0, h1, ctr] [o0, o1, lv] ∧
      CellsAt rd (hs * (xb * gen * (xb * gen))) [o0, o1] ∧
      IsInK nb ∧ (nb ≠ 1 → LoopTo nb fun j => RowCell store rd lv rb xb node pb (gen ^ j)) ∧
      IsInK gap ∧ (gap ≠ 1 → LoopTo gap fun j => GapStep rd node nb (gen ^ j)) ∧
      (∃ k < 11, glp = gen ^ k ∧ Meaning_da_levels k rd [node] [c0, c1]) ∧
      CellsAt rd (ct * (xb * xb)) [c0, c1]

/-- The specialization's name. -/
def colName (store : Bool) : String := if store then "da_verify_column__L1" else "da_verify_column__L0"

/-- `da_verify_column__L{store}`'s body. -/
def colBody (store : Bool) : List Stmt :=
  [.atom (.mul (.n 10) (.n 0) (.n 0)), .atom (.mul (.n 11) (.n 8) (.n 10)),
   .atom (.load (.n 12) (.n 11) 0), .atom (.load (.n 13) (.n 11) 1),
   .call "da_vector_dispatch" [.n 0, .n 12, .n 13, .n 9] [.n 14, .n 15, .n 16],
   .atom (.const (.n 17) (word 2 0 0)), .atom (.mul (.n 18) (.n 0) (.n 17)),
   .atom (.mul (.n 19) (.n 18) (.n 18)), .atom (.mul (.n 20) (.n 8) (.n 19)),
   .atom (.load (.n 14) (.n 20) 0), .atom (.load (.n 15) (.n 20) 1),
   .atom (.mul (.n 21) (.n 2) (.n 2)), .atom (.mul (.n 22) (.n 21) (.n 21)),
   .atom (.hint (.allocDyn (.n 23) (.n 22))),
   .atom (.const (.n 24) (word 1 0 0)), .atom (.add (.n 25) (.n 24) (.n 1)),
   .atom (.const (.n 26) (word 1 0 0)),
   .callIf (.n 25) (rowName store) [.n 26, .n 1, .n 16, .n 7, .n 0, .n 23, .n 5],
   .atom (.const (.n 27) (word 1 0 0)), .atom (.add (.n 28) (.n 27) (.n 3)),
   .atom (.const (.n 29) (word 1 0 0)),
   .callIf (.n 28) (gapName store) [.n 29, .n 3, .n 23, .n 1],
   .dispatch (.n 4) dlNames [.n 23] [.n 30, .n 31],
   .atom (.mul (.n 32) (.n 0) (.n 0)), .atom (.mul (.n 33) (.n 6) (.n 32)),
   .atom (.load (.n 30) (.n 33) 0), .atom (.load (.n 31) (.n 33) 1),
   .ret []]

set_option maxRecDepth 100000 in
theorem find_col (store : Bool) : coreProgram.find? (colName store) =
    some ⟨colName store, [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9], colBody store⟩ := by
  cases store
  · exact Program.find?_of_indexOf? (j := 915) (by decide +kernel) rfl
  · exact Program.find?_of_indexOf? (j := 914) (by decide +kernel) rfl

theorem isInK_one_add {a : E} : IsInK (1 + a) ↔ IsInK a := by
  have h1 : IsInK (1 : E) := by rw [← pow_zero gen]; exact isInK_gen_pow 0
  exact isInK_add_left h1

theorem one_add_ne_zero {a : E} : 1 + a ≠ 0 ↔ a ≠ 1 :=
  not_congr (e_add_eq_zero_iff.trans eq_comm)

theorem dlNames_length : dlNames.length = 11 := rfl

/-- The tree dispatch on `g^k`, `k < 11`. -/
theorem dl_dispatch {rd : Reader} {glp node c0 c1 : E} :
    (∃ (j : ℕ) (h : j < dlNames.length), glp = ofK (gpow j) ∧ coreProgram.Rel rd dlNames[j] [node] [c0, c1]) ↔
      ∃ k < 11, glp = gen ^ k ∧ Meaning_da_levels k rd [node] [c0, c1] := by
  constructor
  · rintro ⟨j, hj, hg, hr⟩
    rw [dlNames_length] at hj
    rw [← List.getD_eq_getElem _ ""] at hr
    exact ⟨j, hj, by rw [hg, gen_pow_eq_ofK], (da_levels_iff j (by omega) _ _).mp hr⟩
  · rintro ⟨k, hk, hg, hm⟩
    refine ⟨k, by rw [dlNames_length]; exact hk, by rw [hg, gen_pow_eq_ofK], ?_⟩
    rw [← List.getD_eq_getElem _ ""]
    exact (da_levels_iff k (by omega) _ _).mpr hm

theorem da_verify_column_iff (store : Bool) (rd : Reader) (args rets : List E) :
    coreProgram.Rel rd (colName store) args rets ↔ Meaning_da_verify_column store rd args rets := by
  rw [rel_of_find (find_col store)]
  simp only [Fn.Sem, colBody, Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil,
    true_and, word_one, word_gen]
  constructor
  · rintro ⟨σ, hp, m10, m11, l12, l13, hdisp, c17, m18, m19, m20, l14, l15, m21, m22, c24, a25, c26,
      hk25, hrow, c27, a28, c29, hk28, hgap, hdl, m32, m33, l30, l31, hret⟩
    subst hp hret
    rw [a25, c24] at hk25 hrow
    rw [a28, c27] at hk28 hgap
    rw [c26] at hrow
    rw [c29] at hgap
    rw [m11, m10] at l12 l13
    rw [m20, m19, m18, c17] at l14 l15
    rw [m33, m32] at l30 l31
    refine ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, σ (.n 12), σ (.n 13), σ (.n 14), σ (.n 15),
      σ (.n 16), σ (.n 23), σ (.n 30), σ (.n 31), cellsAt_two.mpr ⟨l12, l13⟩,
      (da_vector_dispatch_iff rd _ _).mp hdisp, cellsAt_two.mpr ⟨l14, l15⟩, isInK_one_add.mp hk25,
      fun h => (row_loop_meaning store rd _ _ _ _ _ _).mp (hrow (one_add_ne_zero.mpr h)),
      isInK_one_add.mp hk28,
      fun h => (gap_loop_meaning store rd _ _ _).mp (hgap (one_add_ne_zero.mpr h)),
      dl_dispatch.mp hdl, cellsAt_two.mpr ⟨l30, l31⟩⟩
  · rintro ⟨xb, nb, np, gap, glp, pb, ct, rb, hs, ctr, rfl, rfl, h0, h1, o0, o1, lv, node, c0, c1,
      h12, hdisp, h14, hk1, hrow, hk3, hgap, hdl, h30⟩
    obtain ⟨l12, l13⟩ := cellsAt_two.mp h12
    obtain ⟨l14, l15⟩ := cellsAt_two.mp h14
    obtain ⟨l30, l31⟩ := cellsAt_two.mp h30
    refine ⟨listVal [xb, nb, np, gap, glp, pb, ct, rb, hs, ctr, xb * xb, hs * (xb * xb), h0, h1, o0, o1,
      lv, gen, xb * gen, xb * gen * (xb * gen), hs * (xb * gen * (xb * gen)), np * np,
      np * np * (np * np), node, 1, 1 + nb, 1, 1, 1 + gap, 1, c0, c1, xb * xb, ct * (xb * xb)], rfl, ?_⟩
    simp only [listVal, List.getD_cons_succ, List.getD_cons_zero, true_and, and_true]
    exact ⟨l12, l13, (da_vector_dispatch_iff rd _ _).mpr hdisp, l14, l15, isInK_one_add.mpr hk1,
      fun h => (row_loop_meaning store rd _ _ _ _ _ _).mpr (hrow (one_add_ne_zero.mp h)),
      isInK_one_add.mpr hk3, fun h => (gap_loop_meaning store rd _ _ _).mpr (hgap (one_add_ne_zero.mp h)),
      dl_dispatch.mpr hdl, l30, l31⟩

/-- **The column tree's depth is below `11`**: the bound group K's checker assumes at
`da_verify_column`'s argument `4`. -/
theorem da_verify_column_glp_lt {store : Bool} {rd : Reader} {args : List E}
    (h : coreProgram.Rel rd (colName store) args []) : ∃ k < 11, args.getD 4 0 = gen ^ k := by
  obtain ⟨_, _, _, _, glp, _, _, _, _, _, rfl, -, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -,
    ⟨k, hk, hg, -⟩, -⟩ := (da_verify_column_iff store rd args []).mp h
  exact ⟨k, hk, hg⟩

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1
export Digest (RowCell LoopTo Meaning_da_verify_column colName da_verify_column_iff
  da_verify_column_glp_lt)
end LeanVM.Guest.B1
