module

public import NativeRustcVmArm.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmArm.Code.Vm.TableSumcheck.Names
public import NativeRustcVmArm.Code.Vm.TableTerms.Names
public import NativeRustcVmArm.Code.Vm.TableWeights.Names
public import NativeRustcVmArm.Tables.TableSumcheck.Sum
public import NativeRustcVmArm.Tables.TableSumcheck.Terms

/-!
# `table_sumcheck` meets its contract

`start` (`b0`: the prologue, `n` the heights' maximum), `sum` (`b1`, `b2`: the plain sumcheck of
`n` rounds), `rev` (`b3` to `b5`: the challenges reversed in place), `weights` (`b6`:
`table_weights`), `terms` (`b7` to `b11`: `table_terms`, the final check, the exit).
-/

namespace NativeRustcVmArm.Tables.TableSumcheck

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TableSumcheck
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model NativeRustcVm.Tables
open NativeRustcVmArm.Sumcheck (Ctx)

public section

variable [Host] {k : Nat}

/-- **`table_sumcheck` meets its contract.** -/
theorem tableSumcheck_spec (hp : Placed code k)
    (hsc : ∀ a s, Spec (Labels.label NativeRustcVmArm.Vm.SumcheckOfSumcheckPlain.entryLabel) (SumcheckPlainPre a s)
      (SumcheckPlainPost a s))
    (hw : Spec (Labels.label NativeRustcVmArm.Vm.TableWeights.entryLabel) TableWeightsPre TableWeightsPost)
    (htt : ∀ a s heights forms, Spec (Labels.label NativeRustcVmArm.Vm.TableTerms.entryLabel)
      (TableTermsPre a s heights forms) (TableTermsPost a s heights forms))
    {a : DecArea} {s : TState} {heights : Array Nat} {bus : BusResultW} :
    Spec (Labels.label NativeRustcVmArm.Vm.TableSumcheck.entryLabel) (TableSumcheckPre a s heights bus)
      (TableSumcheckPost a s heights bus) := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmArm.Vm.TableSumcheck.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.TableSumcheck.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.TableSumcheck.entryOffset) NativeRustcVmArm.Vm.TableSumcheck.entry_at]
  have hpre' := hpre
  obtain ⟨hS, hrc, -, hts0, htok, -, -, -, -, hH, -⟩ := hpre'
  have cx : Ctx m0 m0.regs.X0.toBitVec a tableSumcheckStack 720 :=
    Bus.Gkr.ctx_of hS hrc hts0 htok N_ge rfl
  have hn30 : heights.foldl max 0 ≤ 30 := foldl_max_le heights hH.1 hH.2.1
  refine start hp hpre fun m hfr hx h25 hts ↦ ?_
  refine sum hp hsc hpre rfl hn30 hfr hx h25 hts fun m3 xs c s1 hfr3 rg3 hr hts3 hsz hel hcl ↦ ?_
  have hlen : xs.toList.length = heights.foldl max 0 := by simp [hsz]
  have hres : res s heights bus m0 = ((tableTerms (arrE m0 m0.regs.X3 2) (arrE m0 m0.regs.X4 3)
      xs.reverse (tableRows heights bus.forms (tableWeights heights bus.point xs.reverse))).run
        s1).bind fun q ↦ if q.1.1 == c then some (q.1.2, q.2) else none := by
    rw [res, tableSumcheck_run, hr]; rfl
  refine rev hp hS cx hn30 hlen (fun m' hR ↦ weights hp hw hpre hn30 hsz hR fun m2 hW ↦
    terms hp htt hpre hn30 hsz hres hW) ⟨hfr3, rg3, hts3, fun i hi ↦ ?_, hcl⟩
  rw [rv_zero (by omega), hel i (by omega)]
  simp

end

end NativeRustcVmArm.Tables.TableSumcheck
