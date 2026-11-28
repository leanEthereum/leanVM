module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldR3

/-!
# `keccak_open`'s fold: round 4

Two rows, unrolled (`b78` to `b87`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen

@[expose] public section

/-- After `b80`, `b85`: `k79` and the counter X26 zeroed. -/
def k79z : List (XReg × Sym) := k79 ++ [(.X26, .lit 0)]

end

public section

variable [NativeRustcArm.Host] {k : Nat} {c : Cx} {m0 : MachineData} {rows : Array (Array EW)}

/-- **Round 4**: two rows from `b78` to `b88`. -/
theorem round4 (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b78Offset)) (hmid : Mid c m0 s.data)
    (hk : KAt m0 (varsOf c.sl 4 0) k78 s.data)
    (hrw : ElemsAt s.data.dmem (rwA m0) (Fr c.sl rows 4) 4096) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b88Offset) ∧ Mid c m0 s'.data ∧
      KAt m0 (varsOf c.sl 4 0) k79 s'.data ∧
      ElemsAt s'.data.dmem (rwA m0) (Fr c.sl rows 5) 4096) s := by
  rw [← F_zero] at hrw
  refine (rowD hp hmul hmemcpy ok hsz hrow (t := 4) (i := 0) (vars := varsOf c.sl 4 0)
    (by decide) (by decide) rfl rfl
    (by decide) (by decide) b78_in_code (List.cons_ne_nil _ _) run_b78 (ksA' := k79)
    (vA := .ptr 2 0) (by decide) (evP2 0)
    (by decide) (by decide) rfl b79_in_code (List.cons_ne_nil _ _) run_b79 (ksB' := k79)
    (vB := .ptr 2 1024) (by decide) (evP2 1024)
    (by decide) (by decide) rfl b80_in_code (List.cons_ne_nil _ _) run_b80 rfl (ksZ' := k79z)
    (by decide) (kI := k79) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl b81_in_code (List.cons_ne_nil _ _) run_b81 (by decide) rfl rfl (by decide) rfl
    rfl b82_in_code (List.cons_ne_nil _ _) run_b82 (lblAt hp b81_in_code) rfl rfl rfl
    (by decide) rfl hpc hmid hk hrw).bind fun s1 ⟨hpc1, hmid1, hk1, hrw1⟩ ↦ ?_
  refine (rowD hp hmul hmemcpy ok hsz hrow (t := 4) (i := 1) (vars := varsOf c.sl 4 0)
    (by decide) (by decide) rfl rfl
    (by decide) (by decide) b83_in_code (List.cons_ne_nil _ _) run_b83 (ksA' := k79)
    (vA := .ptr 2 2048) (by decide) (evP2 2048)
    (by decide) (by decide) rfl b84_in_code (List.cons_ne_nil _ _) run_b84 (ksB' := k79)
    (vB := .ptr 2 3072) (by decide) (evP2 3072)
    (by decide) (by decide) rfl b85_in_code (List.cons_ne_nil _ _) run_b85 rfl (ksZ' := k79z)
    (by decide) (kI := k79) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl b86_in_code (List.cons_ne_nil _ _) run_b86 (by decide) rfl rfl (by decide) rfl
    rfl b87_in_code (List.cons_ne_nil _ _) run_b87 (lblAt hp b86_in_code) rfl rfl rfl
    (by decide) rfl hpc1 hmid1 hk1 hrw1).mono
    fun s2 ⟨hpc2, hmid2, hk2, hrw2⟩ ↦ ⟨hpc2, hmid2, hk2, ?_⟩
  rw [show 1 + 1 = half 4 from rfl, F_half] at hrw2
  exact hrw2

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
