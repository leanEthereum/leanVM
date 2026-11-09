module

public import LeanVM.Guest.Fast.SpWotsTablesCheck
public import LeanVM.Guest.Fast.Wots

/-!
# `sp_wots`' chain starts, computable

`spStartAt K i` (`B1/Sig/SpWotsLayout.lean`) is where chain `i`'s start is hinted in the template
when group `p = i / 3` takes arm `K p`, a function of the template's generators; the guest numbers
it `spRen` of that. At the arms the digit hints name (`spK w p`: the exponent of group `p`'s digit
word, its cell `spRen (spState p).2.2`, searched by `logG`), it is the cell the shared codeword
reader reads off `sp_wots`' tables (`cwCell 21 spSel spFirst spRest spLast w i`, `Fast/Wots.lean`:
the selector's exponent searched by `logGT`, the start its selector plus the table's entry):
**`spStartAt_eq_cwCell`**.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.B1.Sig

@[expose] public section

/-- The arm group `p` of `sp_wots`' codeword takes on the valuation `w`: its digit word's
exponent, at its cell in the guest's numbering. -/
noncomputable def spK (w : Val) (p : Nat) : Nat := logG (w (spRen (.n (spState p).2.2))) (4 ^ spN p)

theorem getD_map_range_list {α : Type} {f : ℕ → α} {n k : ℕ} {d : α} (hk : k < n) :
    ((List.range n).map f).getD k d = f k := by
  simp [List.getD_eq_getElem?_getD, hk]

theorem spRen_n (x : Nat) : spRen (.n x) = .n (spR x) := rfl

/-- Renumbering an entry of a list of lists is reading the renumbered lists. -/
theorem spRen_getD (L : List (List V)) (k r : Nat) :
    spRen ((L.getD k []).getD r (.n 0)) = ((L.map (·.map spRen)).getD k []).getD r (.n 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[k]? with
  | none => simp [spRen_n, spR]
  | some l =>
    simp only [Option.map_some, Option.getD_some, List.getElem?_map]
    cases l[r]? with
    | none => simp [spRen_n, spR]
    | some v => rfl

/-- **Chain `i`'s start, renumbered, is the tables' cell.** -/
theorem spStartAt_eq_cwCell (w : Val) {i : Nat} (hi : i < 64) :
    spRen (spStartAt (spK w) i) = .n (cwCell 21 spSel spFirst spRest spLast w i) := by
  have hp : i / 3 < 22 := by omega
  have hn : 4 ^ spN (i / 3) ≤ 256 := by unfold spN; split_ifs <;> norm_num
  have hK : spK w (i / 3) < 4 ^ spN (i / 3) := logG_lt _ (by positivity)
  have hr : i % 3 < spN (i / 3) := by
    unfold spN; split_ifs with h
    · omega
    · have : i = 63 := by omega
      subst this; norm_num
  rw [spStartAt_eq_getD _ i hK hr, spRen_getD, spGroupStarts (i / 3) hp, getD_map_range_list hK,
    getD_map_range_list hr]
  have hs := spSel_eq (i / 3) hp
  unfold cwCell spK
  simp only [spRen_n, ← hs]
  rw [logG_eq_logGT _ hn]
  unfold spTabOf spN
  by_cases h : i / 3 < 21
  · by_cases h0 : i / 3 = 0
    · simp [h0]
    · simp [h, h0]
  · have h21 : i / 3 = 21 := by omega
    simp [h21]

end
end LeanVM.Guest.Fast
