/-
  LeanVM.Guest.B1.Da.CellCChk

  `da_verify_cell`, evaluated (by kernel evaluation): its values defined in order, no store, the
  template's side conditions its loads of weights.
-/

module

public import LeanVM.Guest.B1.Da.Cell
public import LeanVM.Guest.B1.Fwd.Canon

namespace LeanVM.Guest.B1.Da

open LeanVM.Guest.Core LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest

@[expose] public section

/-- A load of weight `i < 128` through the argument. -/
def isWeightLoad : Atom → Bool
  | .load _ p i => decide (p = .n 0) && decide (i < 128)
  | _ => false

/-- The symbols' hint. -/
def symHint : Atom := .hint (.witness "da_symbols" (.stack ((List.range 128).map fun j => V.n (j + 1))))

/-- **`da_verify_cell`, evaluated.** -/
def cellCOk (fn : Fn) : Bool :=
  (chk 1 fn.body).isSome && (storesOf 1 fn.body).isEmpty &&
  tmplA.all (fun a => !needsSide a || isWeightLoad a) &&
  match splitBody fn.body with
  | some (A, _) => (A.drop 384).all (fun a => !needsSide a) && decide (A.take 1 = [symHint])
  | none => false

set_option maxRecDepth 100000 in
theorem cellc_ok : cellCOk fn% «da_verify_cell» = true := by decide +kernel

end
end LeanVM.Guest.B1.Da
