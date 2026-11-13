/-
  LeanVM.Guest.B1.Sig.SpWotsRen1

  The guest's numbering of `sp_wots`'s template is undone by `spUn` on the values of statements 32 to 63, in runs of 8:
  no value the template names is one its steps without an address constant leave unused.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsRenDefs

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem spRen_run_32 : (Stmt.valsList ((spBodyT.drop 32).take 8)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_40 : (Stmt.valsList ((spBodyT.drop 40).take 8)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_48 : (Stmt.valsList ((spBodyT.drop 48).take 8)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_56 : (Stmt.valsList ((spBodyT.drop 56).take 8)).all spUnOK = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
