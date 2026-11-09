/-
  LeanVM.Guest.B1.Sig.SpWotsRen0

  The guest's numbering of `sp_wots`'s template is undone by `spUn` on the values of the copies, the powers and digit groups 0 to 4:
  no value the template names is one its steps without an address constant leave unused.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsRenDefs

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

theorem spRen_slice_0 : (Stmt.valsList ((spBodyT.drop 0).take 12)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_12 : (Stmt.valsList ((spBodyT.drop 12).take 10)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_22 : (Stmt.valsList ((spBodyT.drop 22).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_27 : (Stmt.valsList ((spBodyT.drop 27).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_32 : (Stmt.valsList ((spBodyT.drop 32).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_37 : (Stmt.valsList ((spBodyT.drop 37).take 5)).all spUnOK = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
