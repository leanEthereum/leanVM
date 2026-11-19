/-
  LeanVM.Guest.B1.Sig.SpWotsRen2

  The guest's numbering of `sp_wots`'s template is undone by `spUn` on the values of statements 91 to 97 (dispatches 7 to 13), one a run:
  no value the template names is one its steps without an address constant leave unused.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsRenDefs

namespace LeanVM.Guest.B1.Sig

open LeanVM.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem spRen_run_91 : (Stmt.valsList ((spBodyT.drop 91).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_92 : (Stmt.valsList ((spBodyT.drop 92).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_93 : (Stmt.valsList ((spBodyT.drop 93).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_94 : (Stmt.valsList ((spBodyT.drop 94).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_95 : (Stmt.valsList ((spBodyT.drop 95).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_96 : (Stmt.valsList ((spBodyT.drop 96).take 1)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_97 : (Stmt.valsList ((spBodyT.drop 97).take 1)).all spUnOK = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
