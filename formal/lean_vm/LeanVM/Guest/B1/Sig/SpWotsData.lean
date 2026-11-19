/-
  LeanVM.Guest.B1.Sig.SpWotsData

  `sp_wots` in the guest's core IR is the template `spBody`.
-/

module

public import LeanVM.Guest.Pack.sp_wots.Core
public import LeanVM.Guest.B1.Sig.SpWotsLayout
import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Sig.SpWotsData0
import LeanVM.Guest.B1.Sig.SpWotsData1

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Core

@[expose] public section

/-- **`sp_wots`'s body is the template**, renumbered as the guest numbers it, checked by the kernel
in runs of `stmtsEqb` (`spBody_run_*`) and the leaf (`spBody_drop_106`). -/
theorem spBody_eq : (Fn.«sp_wots».core).body = spBody := by
  have h105 := drop_eq_of_take (stmtsEqb_sound spBody_run_105) spBody_drop_106
  have h104 := drop_eq_of_take (stmtsEqb_sound spBody_run_104) h105
  have h103 := drop_eq_of_take (stmtsEqb_sound spBody_run_103) h104
  have h102 := drop_eq_of_take (stmtsEqb_sound spBody_run_102) h103
  have h101 := drop_eq_of_take (stmtsEqb_sound spBody_run_101) h102
  have h100 := drop_eq_of_take (stmtsEqb_sound spBody_run_100) h101
  have h99 := drop_eq_of_take (stmtsEqb_sound spBody_run_99) h100
  have h98 := drop_eq_of_take (stmtsEqb_sound spBody_run_98) h99
  have h97 := drop_eq_of_take (stmtsEqb_sound spBody_run_97) h98
  have h96 := drop_eq_of_take (stmtsEqb_sound spBody_run_96) h97
  have h95 := drop_eq_of_take (stmtsEqb_sound spBody_run_95) h96
  have h94 := drop_eq_of_take (stmtsEqb_sound spBody_run_94) h95
  have h93 := drop_eq_of_take (stmtsEqb_sound spBody_run_93) h94
  have h92 := drop_eq_of_take (stmtsEqb_sound spBody_run_92) h93
  have h91 := drop_eq_of_take (stmtsEqb_sound spBody_run_91) h92
  have h90 := drop_eq_of_take (stmtsEqb_sound spBody_run_90) h91
  have h89 := drop_eq_of_take (stmtsEqb_sound spBody_run_89) h90
  have h88 := drop_eq_of_take (stmtsEqb_sound spBody_run_88) h89
  have h87 := drop_eq_of_take (stmtsEqb_sound spBody_run_87) h88
  have h86 := drop_eq_of_take (stmtsEqb_sound spBody_run_86) h87
  have h85 := drop_eq_of_take (stmtsEqb_sound spBody_run_85) h86
  have h84 := drop_eq_of_take (stmtsEqb_sound spBody_run_84) h85
  have h80 := drop_eq_of_take (stmtsEqb_sound spBody_run_80) h84
  have h72 := drop_eq_of_take (stmtsEqb_sound spBody_run_72) h80
  have h64 := drop_eq_of_take (stmtsEqb_sound spBody_run_64) h72
  have h56 := drop_eq_of_take (stmtsEqb_sound spBody_run_56) h64
  have h48 := drop_eq_of_take (stmtsEqb_sound spBody_run_48) h56
  have h40 := drop_eq_of_take (stmtsEqb_sound spBody_run_40) h48
  have h32 := drop_eq_of_take (stmtsEqb_sound spBody_run_32) h40
  have h24 := drop_eq_of_take (stmtsEqb_sound spBody_run_24) h32
  have h16 := drop_eq_of_take (stmtsEqb_sound spBody_run_16) h24
  have h8 := drop_eq_of_take (stmtsEqb_sound spBody_run_8) h16
  have h0 := drop_eq_of_take (stmtsEqb_sound spBody_run_0) h8
  rwa [List.drop_zero, List.drop_zero] at h0

end
end LeanVM.Guest.B1.Sig
