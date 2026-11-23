module

public import NativeRustcVmX64.Tables.TableSumcheck.Terms
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmX64.Code.Vm.TableSumcheck.Names
public import NativeRustcVmX64.Code.Vm.TableTerms.Names
public import NativeRustcVmX64.Code.Vm.TableWeights.Names

/-!
# `table_sumcheck` meets its contract (x86-64)

`start` (`b0`: the prologue, `n` the heights' maximum), `plain` (`b1`, `b2`: the plain sumcheck
of `n` rounds), `rev` (`b3` to `b9`: the challenges reversed in place), `weights` (`b10`:
`table_weights`), `terms` (`b11` to `b13`: `table_terms`, the final check, the exit).
-/

namespace NativeRustcVmX64.Tables.TableSumcheck

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeVm.Model NativeRustcVm.Tables NativeRustcVm.Bus NativeRustcVmX64.Vm.TableSumcheck

public section

variable [Host] {k : Nat}

/-- **`table_sumcheck` meets its contract.** -/
theorem tableSumcheck_spec (hp : Placed code k)
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    (hw : Spec (Labels.label NativeRustcVmX64.Vm.TableWeights.entryLabel) TableWeightsPre TableWeightsPost)
    (htt : ∀ a s heights forms, Spec (Labels.label NativeRustcVmX64.Vm.TableTerms.entryLabel)
      (TableTermsPre a s heights forms) (TableTermsPost a s heights forms))
    {a : DecArea} {s : TState} {heights : Array Nat} {bus : BusResultW} :
    Spec (Labels.label NativeRustcVmX64.Vm.TableSumcheck.entryLabel) (TableSumcheckPre a s heights bus)
      (TableSumcheckPost a s heights bus) := by
  intro m0 h
  rw [lbl_entry hp]
  refine start hp h fun d hb H ↦ plain hp h hsc hb H fun xs c s1 d' S ↦ ?_
  have hsz : xs.size = nR heights :=
    NativeRustcVmX64.Bus.BytecodeShare.sumcheckPlain_size S.run
  have hres : res s heights bus m0 = ((tableTerms (arrE m0 (cpA m0) 2) (arrE m0 (fpA m0) 3)
      xs.reverse (tableRows heights bus.forms (tableWeights heights bus.point xs.reverse))).run
        s1).bind fun q ↦ if q.1.1 == c then some (q.1.2, q.2) else none := by
    have hr := S.run
    unfold nR at hr
    unfold res
    rw [tableSumcheck_run, hr]
    rfl
  exact rev hp h S fun d2 K hpt ↦ weights hp h hw hsz K hpt fun d3 W ↦
    terms hp h htt hsz hres W

end

end NativeRustcVmX64.Tables.TableSumcheck
