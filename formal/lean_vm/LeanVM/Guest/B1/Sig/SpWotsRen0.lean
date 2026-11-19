/-
  LeanVM.Guest.B1.Sig.SpWotsRen0

  The guest's numbering of `sp_wots`'s template is undone by `spUn` on the values of statements 0 to 83 (what the body sets before its dispatches), in runs of 8:
  no value the template names is one its steps without an address constant leave unused.
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsRenDefs

namespace LeanVM.Guest.B1.Sig

open LeanVM.Core

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

set_option maxRecDepth 100000 in
theorem spRen_run_64 : (Stmt.valsList ((spBodyT.drop 64).take 8)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_72 : (Stmt.valsList ((spBodyT.drop 72).take 8)).all spUnOK = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spRen_run_80 : (Stmt.valsList ((spBodyT.drop 80).take 4)).all spUnOK = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
