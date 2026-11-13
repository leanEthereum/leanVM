/-
  LeanVM.Guest.B1.Sig.SpWotsRen3

  The guest's numbering of `sp_wots`'s template is undone by `spUn` on the values of statements 96 to 126, the checks and the leaf, in runs of 8:
  no value the template names is one its steps without an address constant leave unused.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsRenDefs
public import LeanVM.Guest.B1.Sig.SpWotsData1

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Parameters

@[expose] public section

set_option maxRecDepth 100000 in
theorem spRen_run_96 : (Stmt.valsList ((spBodyT.drop 96).take 8)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_104 : (Stmt.valsList ((spBodyT.drop 104).take 8)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_112 : (Stmt.valsList ((spBodyT.drop 112).take 8)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_120 : (Stmt.valsList ((spBodyT.drop 120).take 7)).all spUnOK = true := by
  decide +kernel

theorem spRen_tail : (Stmt.valsList (spTailOf (spLeafKOf (word 1 (2 ^ 63))))).all spUnOK = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
