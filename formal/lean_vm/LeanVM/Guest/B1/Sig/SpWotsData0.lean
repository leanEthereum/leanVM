/-
  LeanVM.Guest.B1.Sig.SpWotsData0

  `sp_wots` in the guest's core IR agrees with the template `spBody` on the copies, the powers and digit groups 0 to 10 (statements 0 to 71).
-/

module

public import LeanVM.Guest.Data.Core07
public import LeanVM.Guest.B1.Sig.SpWotsLayout
public import LeanVM.Guest.B1.Common.Basic

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! The copies, the powers and digit groups 0 to 10 (statements 0 to 71),
compared by `stmtsEqb` in runs, each its own kernel evaluation to bound its memory. -/

set_option maxRecDepth 100000 in
theorem spBody_run_0 :
    stmtsEqb ((Data.core19.body.drop 0).take 8) ((spBody.drop 0).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_8 :
    stmtsEqb ((Data.core19.body.drop 8).take 8) ((spBody.drop 8).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_16 :
    stmtsEqb ((Data.core19.body.drop 16).take 8) ((spBody.drop 16).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_24 :
    stmtsEqb ((Data.core19.body.drop 24).take 8) ((spBody.drop 24).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_32 :
    stmtsEqb ((Data.core19.body.drop 32).take 8) ((spBody.drop 32).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_40 :
    stmtsEqb ((Data.core19.body.drop 40).take 8) ((spBody.drop 40).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_48 :
    stmtsEqb ((Data.core19.body.drop 48).take 8) ((spBody.drop 48).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_56 :
    stmtsEqb ((Data.core19.body.drop 56).take 8) ((spBody.drop 56).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_64 :
    stmtsEqb ((Data.core19.body.drop 64).take 8) ((spBody.drop 64).take 8) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
