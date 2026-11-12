/-
  LeanVM.Guest.B1.Sig.SpWotsRen2

  The guest's numbering of `sp_wots`'s template is undone by `spUn` on the values of statements 64 to 95, in runs of 8:
  no value the template names is one its steps without an address constant leave unused.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsRenDefs

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem spRen_run_64 : (Stmt.valsList ((spBodyT.drop 64).take 8)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_72 : (Stmt.valsList ((spBodyT.drop 72).take 8)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_80 : (Stmt.valsList ((spBodyT.drop 80).take 8)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_88 : (Stmt.valsList ((spBodyT.drop 88).take 8)).all spUnOK = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
