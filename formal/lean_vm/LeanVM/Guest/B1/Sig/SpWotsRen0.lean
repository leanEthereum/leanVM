/-
  LeanVM.Guest.B1.Sig.SpWotsRen0

  The guest's numbering of `sp_wots`'s template is undone by `spUn` on the values of statements 0 to 31, in runs of 8:
  no value the template names is one its steps without an address constant leave unused.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsRenDefs

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem spRen_run_0 : (Stmt.valsList ((spBodyT.drop 0).take 8)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_8 : (Stmt.valsList ((spBodyT.drop 8).take 8)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_16 : (Stmt.valsList ((spBodyT.drop 16).take 8)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_24 : (Stmt.valsList ((spBodyT.drop 24).take 8)).all spUnOK = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
