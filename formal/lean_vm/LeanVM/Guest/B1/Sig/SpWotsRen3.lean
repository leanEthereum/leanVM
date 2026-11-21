/-
  LeanVM.Guest.B1.Sig.SpWotsRen3

  The guest's numbering of `sp_wots`'s template is undone by `spUn` on the values of statements 98 to 105 (dispatches 14 to 21), one a run, and the tail:
  no value the template names is one its steps without an address constant leave unused.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsRenDefs
public import LeanVM.Guest.B1.Sig.SpWotsData1

namespace LeanVM.Guest.B1.Sig

open LeanVM.Core LeanVM.Parameters

@[expose] public section

set_option maxRecDepth 100000 in
theorem spRen_run_98 : (Stmt.valsList ((spBodyT.drop 98).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_99 : (Stmt.valsList ((spBodyT.drop 99).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_100 : (Stmt.valsList ((spBodyT.drop 100).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_101 : (Stmt.valsList ((spBodyT.drop 101).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_102 : (Stmt.valsList ((spBodyT.drop 102).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_103 : (Stmt.valsList ((spBodyT.drop 103).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_104 : (Stmt.valsList ((spBodyT.drop 104).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_105 : (Stmt.valsList ((spBodyT.drop 105).take 1)).all spUnOK = true := by
  decide +kernel

theorem spRen_tail : (Stmt.valsList (spTailOf (spLeafKOf (word 1 (2 ^ 63))))).all spUnOK = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
