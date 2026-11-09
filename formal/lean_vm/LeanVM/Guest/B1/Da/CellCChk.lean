/-
  LeanVM.Guest.B1.Da.CellCChk

  `da_verify_cell`, evaluated (by kernel evaluation): its values defined in order, no store, the
  template's side conditions its assertions on symbols and its loads of weights, the chain's
  inputs canonical from the packed cells.
-/

module

public import LeanVM.Guest.B1.Da.Cell
public import LeanVM.Guest.B1.Fwd.Canon

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- An `assert_in_k` of two symbols. -/
def isSymInK : Atom → Bool
  | .assertInK x y => decide (x = .n x.idx) && decide (1 ≤ x.idx) && decide (x.idx ≤ 256) &&
      decide (y = .n y.idx) && decide (1 ≤ y.idx) && decide (y.idx ≤ 256)
  | _ => false

/-- A load of weight `i < 256` through the argument. -/
def isWeightLoad : Atom → Bool
  | .load _ p i => decide (p = .n 0) && decide (i < 256)
  | _ => false

/-- The symbols' hint. -/
def symHint : Atom := .hint (.witness "da_symbols" (.stack ((List.range 256).map fun j => V.n (j + 1))))

/-- **`da_verify_cell`, evaluated.** -/
def cellCOk (fn : Fn) : Bool :=
  (chk 1 fn.body).isSome && (storesOf 1 fn.body).isEmpty && canonChk [] tmplA &&
  tmplA.all (fun a => !needsSide a || isSymInK a || isWeightLoad a) &&
  match splitBody fn.body with
  | some (A, _) => canonChk ((List.range 128).map packV) (A.drop 1280) &&
      (A.drop 1280).all (fun a => !needsSide a) && decide (A.take 1 = [symHint])
  | none => false

set_option maxRecDepth 100000 in
theorem cellc_ok : cellCOk Data.core30 = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
