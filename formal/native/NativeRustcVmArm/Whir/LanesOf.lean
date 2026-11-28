module

public import NativeRustcVmArm.Code.Vm.LanesOf.Names
public import NativeRustcVmArm.Whir.LanesOf.PairsRun
public import NativeRustcVmArm.Whir.LanesOf.RevRun

/-!
# `lanes_of`

No frame, no call. `b0` branches on `index`: a later level (`pairs`, from `b1`) copies the row's
pairs, two lanes a turn then one (`Pairs`); level `0` (`rev`, from `b5`) writes the row's words
reversed, four lanes a turn then one (`Rev`). Each returns `None` past 64 lanes; the lanes are the
model's (`lanes_pair`, `lanes_rev`).
-/

namespace NativeRustcVmArm.Whir.LanesOf

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.LanesOf

public section

variable [Host] {k : Nat}

/-- **`lanes_of`'s contract.** -/
theorem lanesOf_spec (hp : Placed code k) : Spec (label NativeRustcVmArm.Vm.LanesOf.entryLabel) LanesOfPre LanesOfPost := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmArm.Vm.LanesOf.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b0Offset) from hp.label NativeRustcVmArm.Vm.LanesOf.entry_at]
  have hb0 : ∀ f, Body m0 f 0 m0 := fun f ↦ ⟨fr_entry, lanes_zero f, rfl, rfl, rfl⟩
  refine exec_then (inf hp b0_in_code (by simp [b0])) run_b0 (Env.wf_nil _) (match_nil _)
    fun s hm hpc ↦ ?_
  have hk := after_eq run_b0 ▸ b0_keeps
  have e2 : s.data.regs.X2 = m0.regs.X2 := reg_kept hm (r := .X2) rfl
  have hc : (SBool.cmp .eq .W64 (.reg .X0) (.lit 0)).eval (Env.ofMachine m0 []) =
      decide (m0.regs.X0.toNat = 0) := by
    sym_simp
    rw [Env.ofMachine_regs, bv_beq_toNat, toNat_ofNat_lt (by decide)]
    rfl
  by_cases h0 : m0.regs.X0.toNat = 0
  · have hpc' := pc_taken hpc (by rw [hc]; simp [h0])
    rw [hp.label (j := NativeRustcVmArm.Vm.LanesOf.b5Offset) NativeRustcVmArm.Vm.LanesOf.label_5_at] at hpc'
    exact goto hpc' (rev hp hpre h0 ((hb0 _).of_regsS hm hk.1 hk.2 rfl rfl rfl) e2)
  · have hpc' := pc_fall hpc (by rw [hc]; simp [h0])
    exact goto hpc' (pairs hp hpre h0 ((hb0 _).of_regsS hm hk.1 hk.2 rfl rfl rfl) e2)

end

end NativeRustcVmArm.Whir.LanesOf
