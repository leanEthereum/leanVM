/-
  LeanVM.Guest.B1.Sig.SpWotsRen3

  The guest's numbering of `sp_wots`'s template is undone by `spUn` on the values of digit groups 17 to 21, the checks and the leaf:
  no value the template names is one its steps without an address constant leave unused.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsRenDefs
public import LeanVM.Guest.B1.Sig.SpWotsData1

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

theorem spRen_slice_102 : (Stmt.valsList ((spBodyT.drop 102).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_107 : (Stmt.valsList ((spBodyT.drop 107).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_112 : (Stmt.valsList ((spBodyT.drop 112).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_117 : (Stmt.valsList ((spBodyT.drop 117).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_slice_122 : (Stmt.valsList ((spBodyT.drop 122).take 5)).all spUnOK = true := by
  decide +kernel

theorem spRen_tail : (Stmt.valsList (spTailOf (spLeafKOf (word 1 (2 ^ 63))))).all spUnOK = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
