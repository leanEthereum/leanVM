/-
  LeanVM.Guest.B1.Sig.SpWotsData0

  `sp_wots` in the guest's core IR agrees with the template `spBody` on the copies, the powers, the digit words' hints and range checks, the padding run and dispatches 0 to 10 (statements 0 to 94).
-/

module

public import LeanVM.Guest.Pack.sp_wots.Core
public import LeanVM.Guest.B1.Sig.SpWotsLayout
public import LeanVM.Guest.B1.Common.Basic

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Core

@[expose] public section

/-! The copies, the powers, the hints, the range checks, the padding run and the hoisted constant
(statements 0 to 83) in runs of 8, then dispatches 0 to 10 (statements 84 to 94) one a run, compared by
`stmtsEqb`, each its own kernel evaluation to bound its memory. -/

set_option maxRecDepth 100000 in
theorem spBody_run_0 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 0).take 8) ((spBody.drop 0).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_8 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 8).take 8) ((spBody.drop 8).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_16 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 16).take 8) ((spBody.drop 16).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_24 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 24).take 8) ((spBody.drop 24).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_32 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 32).take 8) ((spBody.drop 32).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_40 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 40).take 8) ((spBody.drop 40).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_48 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 48).take 8) ((spBody.drop 48).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_56 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 56).take 8) ((spBody.drop 56).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_64 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 64).take 8) ((spBody.drop 64).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_72 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 72).take 8) ((spBody.drop 72).take 8) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_80 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 80).take 4) ((spBody.drop 80).take 4) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_84 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 84).take 1) ((spBody.drop 84).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_85 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 85).take 1) ((spBody.drop 85).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_86 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 86).take 1) ((spBody.drop 86).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_87 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 87).take 1) ((spBody.drop 87).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_88 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 88).take 1) ((spBody.drop 88).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_89 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 89).take 1) ((spBody.drop 89).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_90 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 90).take 1) ((spBody.drop 90).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_91 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 91).take 1) ((spBody.drop 91).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_92 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 92).take 1) ((spBody.drop 92).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_93 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 93).take 1) ((spBody.drop 93).take 1) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_94 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop 94).take 1) ((spBody.drop 94).take 1) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
