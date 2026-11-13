/-
  LeanVM.Guest.B1.Sig.SpWotsData

  `sp_wots` in the guest's core IR is the template `spBody`.
-/

module

public import LeanVM.Guest.Data.Names
public import LeanVM.Guest.B1.Sig.SpWotsLayout
import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Sig.SpWotsData0
import LeanVM.Guest.B1.Sig.SpWotsData1

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`sp_wots`'s body is the template**, renumbered as the guest numbers it, checked by the kernel
in runs of `stmtsEqb` (`spBody_run_*`) and the leaf (`spBody_drop_127`). -/
theorem spBody_eq : (fn% «sp_wots»).body = spBody := by
  have h120 := drop_eq_of_take (stmtsEqb_sound spBody_run_120) spBody_drop_127
  have h112 := drop_eq_of_take (stmtsEqb_sound spBody_run_112) h120
  have h104 := drop_eq_of_take (stmtsEqb_sound spBody_run_104) h112
  have h96 := drop_eq_of_take (stmtsEqb_sound spBody_run_96) h104
  have h88 := drop_eq_of_take (stmtsEqb_sound spBody_run_88) h96
  have h80 := drop_eq_of_take (stmtsEqb_sound spBody_run_80) h88
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
