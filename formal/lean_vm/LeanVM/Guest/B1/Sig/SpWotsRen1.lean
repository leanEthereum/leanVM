/-
  LeanVM.Guest.B1.Sig.SpWotsRen1

  The guest's numbering of `sp_wots`'s template is undone by `spUn` on the values of statements 84 to 90 (dispatches 0 to 6), one a run:
  no value the template names is one its steps without an address constant leave unused.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsRenDefs

namespace LeanVM.Guest.B1.Sig

open LeanVM.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem spRen_run_84 : (Stmt.valsList ((spBodyT.drop 84).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_85 : (Stmt.valsList ((spBodyT.drop 85).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_86 : (Stmt.valsList ((spBodyT.drop 86).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_87 : (Stmt.valsList ((spBodyT.drop 87).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_88 : (Stmt.valsList ((spBodyT.drop 88).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_89 : (Stmt.valsList ((spBodyT.drop 89).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_90 : (Stmt.valsList ((spBodyT.drop 90).take 1)).all spUnOK = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
