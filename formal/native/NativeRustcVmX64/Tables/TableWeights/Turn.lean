module

public import NativeRustcVmX64.Tables.TableWeights.Loop
public import NativeRustcVmX64.Code.Vm.EWMul.Names

/-!
# `table_weights`: a whole turn, the entry and the exit (x86-64)

`turn`: from the loop head after `c` coordinates to the head after `c + 1` or the exit.
`entry_step`: the prologue (`b0`) into the loop (`b1`) or, for an empty point, to the exit with
the weights `1` (`b12`). `exit_step`: the weights stored at `out` (`b13a`), the epilogue
(`b13b`).
-/

namespace NativeRustcVmX64.Tables.TableWeights

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Tables NativeRustcVmX64.Arrays
open NativeRustcVmX64.Vm.TableWeights NativeRustcVmX64.Field
open NativeRustcVm (wordOf wordsOf ewsOf)

public section

variable [Host] {k : Nat}

/-- **A turn of the loop.** -/
theorem turn (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmX64.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : TableWeightsPre m0) {c : Nat} {st : MachineState}
    (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b10Offset)) (hI : It m0 c st.data) :
    Eventually (step1 Host.exe) (fun st' ↦ (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b10Offset) ∧ It m0 (c + 1) st'.data) ∨
      (st'.pc = Host.addrOf (k + NativeRustcVmX64.Vm.TableWeights.b13Offset) ∧ Fin m0 st'.data)) st := by
  have hS := hpre.1
  refine Eventually.bind (head_step hp hpre hpc hI) fun st1 ⟨hpc1, h1⟩ ↦ ?_
  refine Eventually.bind (pre3_step hp hmul hpre hpc1 h1) fun st2 ⟨hpc2, h2⟩ ↦ ?_
  refine Eventually.bind (mid_step hmul hS (j := 1) le_rfl (by omega) (hb4 hp) run_b4
    (after_eq run_b4 ▸ b4_ok) hpc2 h2) fun st3 ⟨hpc3, h3⟩ ↦ ?_
  refine Eventually.bind (mid_step hmul hS (j := 2) (by omega) (by omega) (hb5 hp) run_b5
    (after_eq run_b5 ▸ b5_ok) hpc3 h3) fun st4 ⟨hpc4, h4⟩ ↦ ?_
  refine Eventually.bind (mid_step hmul hS (j := 3) (by omega) (by omega) (hb6 hp) run_b6
    (after_eq run_b6 ▸ b6_ok) hpc4 h4) fun st5 ⟨hpc5, h5⟩ ↦ ?_
  refine Eventually.bind (mid_step hmul hS (j := 4) (by omega) le_rfl (hb7 hp) run_b7
    (after_eq run_b7 ▸ b7_ok) hpc5 h5) fun st6 ⟨hpc6, h6⟩ ↦ ?_
  refine Eventually.bind (last_step hp hmul hS hpc6 h6) fun st7 ⟨hpc7, h7⟩ ↦ ?_
  exact turn_step hp hpre hpc7 h7

end

end NativeRustcVmX64.Tables.TableWeights
