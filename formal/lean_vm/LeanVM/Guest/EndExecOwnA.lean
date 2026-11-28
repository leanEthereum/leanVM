/-
  LeanVM.Guest.EndExecOwnA

  The functions' own residual families (`CoreMode.FnReg.fams`), sound at the honest instances of b2c's
  aligned tree: each function's `SoundA.fams_okA`.
-/

module

public import LeanVM.Guest.CoreMode.Gen.FnFams
public import LeanVM.Guest.CoreMode.Fn.certify_stack.SoundA
public import LeanVM.Guest.CoreMode.Fn.column_selector.SoundA
public import LeanVM.Guest.CoreMode.Fn.da_pad.SoundA
public import LeanVM.Guest.CoreMode.Fn.da_verify.SoundA
public import LeanVM.Guest.CoreMode.Fn.keccak_layer.SoundA
public import LeanVM.Guest.CoreMode.Fn.level_positions.SoundA
public import LeanVM.Guest.CoreMode.Fn.link_rounds.SoundA
public import LeanVM.Guest.CoreMode.Fn.open_stacked.SoundA
public import LeanVM.Guest.CoreMode.Fn.ring_rows.SoundA
public import LeanVM.Guest.CoreMode.Fn.rs_eq_run.SoundA
public import LeanVM.Guest.CoreMode.Fn.squeeze_packed.SoundA
public import LeanVM.Guest.CoreMode.Fn.verify_keccak.SoundA
public import LeanVM.Guest.CoreMode.Fn.verify_sub.SoundA

namespace LeanVM.Guest.EndExec

open LeanVM.Guest LeanVM.Guest.Core

public section

/-- **Every function's own family holds** at its honest instances, aligned (`OwnOkA`). -/
theorem fams_okA {al : String → Bool} {D : Ref → RefD} : ∀ c ∈ CoreMode.FnReg.fams, OwnOkA al D c :=
  CoreMode.FnReg.all_append (CoreMode.FnReg.all_append (CoreMode.FnReg.all_append (CoreMode.FnReg.all_append
    (CoreMode.FnReg.all_append (CoreMode.FnReg.all_append (CoreMode.FnReg.all_append
    (CoreMode.FnReg.all_append (CoreMode.FnReg.all_append (CoreMode.FnReg.all_append (CoreMode.FnReg.all_append
    (CoreMode.FnReg.all_append (CoreMode.FnReg.all_append CoreMode.Own.certify_stack.fams_okA
    CoreMode.Own.column_selector.fams_okA)
    CoreMode.Own.da_pad.fams_okA)
    CoreMode.Own.da_verify.fams_okA)
    CoreMode.Own.keccak_layer.fams_okA)
    CoreMode.Own.level_positions.fams_okA)
    CoreMode.Own.link_rounds.fams_okA)
    CoreMode.Own.open_stacked.fams_okA)
    CoreMode.Own.ring_rows.fams_okA)
    CoreMode.Own.rs_eq_run.fams_okA)
    CoreMode.Own.squeeze_packed.fams_okA)
    CoreMode.Own.verify_keccak.fams_okA)
    CoreMode.Own.verify_sub.fams_okA) CoreMode.FnReg.all_nil

end

end LeanVM.Guest.EndExec
