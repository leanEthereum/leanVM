/-
  LeanVM.Guest.B1.Sig.SpWotsRen2

  The guest's numbering of `sp_wots`'s template is undone by `spUn` on the values of digit groups 11 to 16:
  no value the template names is one its steps without an address constant leave unused.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsRenDefs

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

theorem spRen_slice_72 : (Stmt.valsList ((spBodyT.drop 72).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_77 : (Stmt.valsList ((spBodyT.drop 77).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_82 : (Stmt.valsList ((spBodyT.drop 82).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_87 : (Stmt.valsList ((spBodyT.drop 87).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_92 : (Stmt.valsList ((spBodyT.drop 92).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_97 : (Stmt.valsList ((spBodyT.drop 97).take 5)).all spUnOK = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
