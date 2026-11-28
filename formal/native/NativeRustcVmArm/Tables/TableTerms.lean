module

public import NativeRustcVmArm.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmArm.Code.Vm.ConstraintsW.Names
public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.Evaluate.Names
public import NativeRustcVmArm.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmArm.Code.Vm.TableTerms.Names
public import NativeRustcVmArm.Tables.TableTerms.Entry
public import NativeRustcVmArm.Tables.TableTerms.Loop

/-!
# `table_terms` meets its contract

`entry` (`b0`: the prologue, the arguments saved, the loop head before table `0`), `loop` (`b1` to
`b13` for each of the six tables: its evaluations read, its constraints, its forms, its weighted
summand added to the running sum, its point copied; a failed read leaves with `None`, `b15`), the
exit (`b14`: `Some` of the sum; `b16`: the epilogue).
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Tables
open NativeRustcVmArm.Vm.TableTerms

public section

variable [Host] {k : Nat}

/-- **`table_terms` meets its contract.** -/
theorem tableTerms_spec (hp : Placed code k)
    (hrs : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.TStateReadScalars.entryLabel) (ReadScalarsPre a s) (ReadScalarsPost a s))
    (hcw : Spec (Labels.label NativeRustcVmArm.Vm.ConstraintsW.entryLabel) ConstraintsWPre ConstraintsWPost)
    (hdot : Spec (Labels.label NativeRustcVmArm.Vm.Dot.entryLabel) DotPre DotPost)
    (hev : ∀ f, Spec (Labels.label NativeRustcVmArm.Vm.Evaluate.entryLabel) (EvaluatePre f) (EvaluatePost f))
    (hext : Spec (Labels.label NativeRustcVmArm.Vm.BufEW30Extend.entryLabel) (BufEWExtendPre 30) (BufEWExtendPost 30))
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {a : DecArea} {s : TState} {heights : Array Nat} {forms : Array (Array FormW)} :
    Spec (Labels.label NativeRustcVmArm.Vm.TableTerms.entryLabel) (TableTermsPre a s heights forms)
      (TableTermsPost a s heights forms) := by
  intro m0 h
  rw [lbl_entry hp]
  have hh : heights.size = 6 := (Pre.hts h).1
  have hf : forms.size = 6 := (Pre.fms h).size
  exact entry hp h fun m H ↦
    loop hp h hh hf ⟨hrs, hcw, hdot, hev, hext, hmul⟩ 5 0 rfl _ _ m H

end

end NativeRustcVmArm.Tables.TableTerms
