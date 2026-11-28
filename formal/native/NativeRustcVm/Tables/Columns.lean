module

public import NativeVm.Model.Tables

/-!
# `tableColumnClaims` table by table

Table `i`'s claims (`claimsOf`: its values on its global columns, at its point); the claims of the
tables before `i` and the first `j` of table `i`'s (`pre`), one more claim at a time (`pre_succ`,
`pre_next`); all of them (`pre_six`), each prefix shorter than the whole (`length_pre_lt`).
-/

namespace NativeRustcVm.Tables

open NativeVm.Model

@[expose] public section

/-- A table's claims: its values on the columns from `b`, at its point. -/
def cf (b : Nat) (e : Array EW × Array EW) : List ColumnClaimW :=
  (e.2.zipIdx.map fun (v, col) ↦ (⟨b + col, e.1, v⟩ : ColumnClaimW)).toList

/-- Table `i`'s claims. -/
def claimsOf (ev : Array (Array EW × Array EW)) (i : Nat) : List ColumnClaimW :=
  cf (globalColumnBasesW.getD i 0) (ev.getD i (#[], #[]))

/-- The claims of the tables before `i` and the first `j` of table `i`'s. -/
def pre (ev : Array (Array EW × Array EW)) (i j : Nat) : List ColumnClaimW :=
  (List.range i).flatMap (claimsOf ev) ++ (claimsOf ev i).take j

end

public section

variable {ev : Array (Array EW × Array EW)}

theorem bases_eq : globalColumnBasesW = #[5, 18, 31, 38, 52, 66] := by decide +kernel

theorem tableColumnClaims_eq (h : ev.size = 6) :
    (tableColumnClaims ev).toList = (List.range 6).flatMap (claimsOf ev) := by
  rcases ev with ⟨l⟩
  simp only [List.size_toArray] at h
  match l, h with
  | [a, b, c, d, e, f], _ =>
    simp [tableColumnClaims, claimsOf, cf, bases_eq, List.range_succ]

theorem length_claimsOf (i : Nat) : (claimsOf ev i).length = (ev.getD i (#[], #[])).2.size := by
  simp [claimsOf, cf]

theorem getElem_claimsOf (i j : Nat) (hj : j < (claimsOf ev i).length) :
    (claimsOf ev i)[j] = ⟨globalColumnBasesW.getD i 0 + j, (ev.getD i (#[], #[])).1,
      (ev.getD i (#[], #[])).2[j]'(by rw [length_claimsOf] at hj; exact hj)⟩ := by
  simp [claimsOf, cf]

theorem pre_succ (i j : Nat) (hj : j < (claimsOf ev i).length) :
    pre ev i (j + 1) = pre ev i j ++ [(claimsOf ev i)[j]] := by
  unfold pre
  rw [List.take_add_one, List.getElem?_eq_getElem hj, List.append_assoc]
  rfl

theorem pre_next (i : Nat) : pre ev i (claimsOf ev i).length = pre ev (i + 1) 0 := by
  simp [pre, List.range_succ]

theorem pre_six (h : ev.size = 6) : pre ev 6 0 = (tableColumnClaims ev).toList := by
  simp [pre, tableColumnClaims_eq h]

theorem length_pre_mono {i i' : Nat} (h : i ≤ i') : (pre ev i 0).length ≤ (pre ev i' 0).length := by
  induction i', h using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ n _ ih =>
    refine le_trans ih ?_
    simp [pre, List.range_succ]

theorem length_pre_lt {i j : Nat} (hi : i < 6) (hj : j < (claimsOf ev i).length) (h : ev.size = 6) :
    (pre ev i j).length < (tableColumnClaims ev).size := by
  have h1 : (pre ev i j).length < (pre ev i (j + 1)).length := by
    rw [pre_succ i j hj]; simp
  have h2 : (pre ev i (j + 1)).length ≤ (pre ev i (claimsOf ev i).length).length := by
    simp only [pre, List.length_append, List.length_take]; omega
  rw [pre_next] at h2
  have h3 := length_pre_mono (ev := ev) (show i + 1 ≤ 6 by omega)
  rw [pre_six h] at h3
  simp only [Array.length_toList] at h3
  omega

end

end NativeRustcVm.Tables
