/-
  LeanVM.Guest.B1.Digest.Basic

  Shared lemmas of the digest family: straight-line bodies, the padding cells of a whole-cell
  message, digests as cells.
-/

module

public import LeanVM.Guest.B1.Digest.Interface

/-!
# Digests: shared lemmas

* `holdsList_atoms_ret`: a body of atoms then a `ret` holds exactly when every atom does and the
  returned words are the continuation's.
* `padCells_getD_lt`, `padCells_getD_last`: the cells a whole-cell message of `16 m` bytes is
  absorbed from are its cells, then the padding cell `0x01 … 0x80` (`padCellWord`).
* `digestScalars_ofCells`: two cells' lanes are the digest of those cells.
* `VDec.vDecEq` (scoped): equality of values by their indices first, for the checkers.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace VDec

/-- Equality of values by their indices first: the checkers' searches pass over most atoms on a
differing index, which the derived instance compares last. -/
scoped instance (priority := high) vDecEq : DecidableEq V := fun a b =>
  decidable_of_iff (a.idx = b.idx ∧ a.tag = b.tag ∧ a.path = b.path) (by
    cases a; cases b; simp only [V.mk.injEq]; tauto)

end VDec

/-! ## Straight-line bodies -/

theorem holdsList_atoms_ret {C : CallRel} {rd : Reader} {σ : Val} (as : List Atom) (vs : List V)
    (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsList C rd σ (as.map Stmt.atom ++ [Stmt.ret vs]) next kret ↔
      (∀ a ∈ as, a.Holds rd σ) ∧ kret (vs.map σ) := by
  induction as with
  | nil => simp [Stmt.HoldsList, Stmt.Holds]
  | cons a as ih =>
    simp only [List.map_cons, List.cons_append, Stmt.HoldsList, Stmt.Holds, List.forall_mem_cons,
      ih, and_assoc]

theorem forall_mem_flatMap_range {α : Type} {n : ℕ} {f : ℕ → List α} {P : α → Prop} :
    (∀ a ∈ (List.range n).flatMap f, P a) ↔ ∀ i < n, ∀ a ∈ f i, P a := by
  simp only [List.mem_flatMap, List.mem_range, forall_exists_index, and_imp]
  exact ⟨fun h i hi a ha => h a i hi ha, fun h a i hi ha => h i hi a ha⟩

/-! ## `y` and `y⁻¹` -/

/-- `y` and `y⁻¹` as the guest's words. -/
abbrev wY : E := word 0 1
abbrev wYi : E := word 2 1

/-! ## The padding of a whole-cell message -/

/-- The padding cell of a message of whole cells, `len = 16 m` with `16 m ≡ 8 (mod 136)`, … in
general `byteCell len 1 + byteCell (136 B - 1) 0x80` when both bytes fall in cell `m`. -/
theorem padCells_getD_lt (cells : List E) (len : ℕ) {i : ℕ} (hi : i < cells.length)
    (h1 : i ≠ len / 16) (h2 : i ≠ (rate * (len / rate + 1) - 1) / 16) :
    (padCells cells len).getD i 0 = cells.getD i 0 := by
  unfold padCells xorByte
  rw [List.getD_eq_getElem?_getD, List.getElem?_modify, List.getElem?_modify,
    List.getElem?_append_left hi]
  simp [Ne.symm h1, Ne.symm h2, List.getD_eq_getElem?_getD]

/-! ## Digests as cells -/

theorem digestScalars_ofCells (a b : E) :
    digestHalves #v[(a.limb 0).lane, (a.limb 1).lane, (b.limb 0).lane, (b.limb 1).lane] =
      (a, b) := by
  simp only [digestHalves, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, K.ofLane_lane]
  rw [← eq_ofLimbs a, ← eq_ofLimbs b]

end
end LeanVM.Guest.B1.Digest
