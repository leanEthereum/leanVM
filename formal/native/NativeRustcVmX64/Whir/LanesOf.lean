module

public import NativeRustcVmX64.Whir.LanesOf.Rev
public import NativeRustcVmX64.Whir.LanesOf.Pairs
public import NativeRustcVmX64.Code.Vm.LanesOf.Names

/-!
# `lanes_of` on x86-64

`b0` pushes RBX and branches on `index`: a later level (`pairs`, from `b1`) copies the row's pairs,
two lanes a turn then one; level `0` (`rev`, from `b5`) writes the row's words reversed, one lane a
turn. Each returns `None` past 64 lanes; the lanes are the model's (`lanes_pair`, `lanes_rev`).
-/

namespace NativeRustcVmX64.Whir.LanesOf

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.LanesOf
open NativeRustcVmX64.Transcript (frameEnv)

public section

variable [Host] {k : Nat}

/-- **`lanes_of`'s contract.** -/
theorem lanesOf_spec (hp : Placed code k) :
    Spec (Labels.label NativeRustcVmX64.Vm.LanesOf.entryLabel) LanesOfPre LanesOfPost := by
  intro m0 hpre
  rw [show Labels.label NativeRustcVmX64.Vm.LanesOf.entryLabel = Host.addrOf (k + NativeRustcVmX64.Vm.LanesOf.b0Offset) from hp.label NativeRustcVmX64.Vm.LanesOf.entry_at]
  have hwf := wf1 (st := m0) (vars := fun _ ↦ 0) (ret := 0) hpre fun _ h ↦ h
  refine exec_then (inf hp b0_in_code (by simp [b0])) run_b0 hwf (by intro l h; cases h)
    Field.match_frame fun st hm hpc ↦ ?_
  have hm0 : Match (frameEnv m0 m0 8 []) (after b0 entryS) st.data := by
    rw [after_eq run_b0]; exact hm
  simp only [PcOk] at hpc
  rw [Arrays.eval_test, Arrays.eval_reg, bv_beq_ofNat _ (by decide)] at hpc
  obtain ⟨hT, hF⟩ := Arrays.pc_cond hpc
  by_cases h0 : (reg m0 .rdi).toNat = 0
  · exact rev hp hpre h0 hm0 ((hT (decide_eq_true h0)).trans (hp.label NativeRustcVmX64.Vm.LanesOf.label_1_at))
  · exact pairs hp hpre h0 hm0 (hF fun h ↦ h0 (of_decide_eq_true h))

end

end NativeRustcVmX64.Whir.LanesOf
