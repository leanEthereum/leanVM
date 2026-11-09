/-
  LeanVM.Guest.B1.Sig.SpWotsRen1

  The guest's numbering of `sp_wots`'s template is undone by `spUn` on the values of digit groups 5 to 10:
  no value the template names is one its steps without an address constant leave unused.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsRenDefs

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

theorem spRen_slice_42 : (Stmt.valsList ((spBodyT.drop 42).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_47 : (Stmt.valsList ((spBodyT.drop 47).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_52 : (Stmt.valsList ((spBodyT.drop 52).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_57 : (Stmt.valsList ((spBodyT.drop 57).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_62 : (Stmt.valsList ((spBodyT.drop 62).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_67 : (Stmt.valsList ((spBodyT.drop 67).take 5)).all spUnOK = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
