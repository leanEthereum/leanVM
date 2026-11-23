module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldRow
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Exec2

/-!
# `keccak_open`'s fold: round 2

Eight rows, unrolled (`b18` to `b57`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen

@[expose] public section

/-- After `b20`, `b25`: `k20` and the counter X26 zeroed. -/
def k20z : List (XReg × Sym) := k20 ++ [(.X26, .lit 0)]
/-- After `b30`: `k30` and the counter X27 zeroed. -/
def k30z : List (XReg × Sym) := k30 ++ [(.X27, .lit 0)]
/-- After `b35`, `b40`, …: `k38` and the counter X29 zeroed. -/
def k38z : List (XReg × Sym) := k38 ++ [(.X29, .lit 0)]

end

public section

variable [NativeRustcArm.Host] {k : Nat} {c : Cx} {m0 : MachineData} {rows : Array (Array EW)}

/-- **Round 2's rows 0 and 1.** -/
theorem round2a (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b18Offset)) (hmid : Mid c m0 s.data)
    (hk : KAt m0 (varsOf c.sl 2 0) kP s.data)
    (hrw : ElemsAt s.data.dmem (rwA m0) (F c.sl rows 2 0 0) 4096) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b28Offset) ∧ Mid c m0 s'.data ∧
      KAt m0 (varsOf c.sl 2 0) k20 s'.data ∧
      ElemsAt s'.data.dmem (rwA m0) (F c.sl rows 2 2 0) 4096) s := by
  refine (rowD hp hmul hmemcpy ok hsz hrow (t := 2) (i := 0) (vars := varsOf c.sl 2 0)
    (by decide) (by decide) rfl rfl
    (by decide) (by decide) b18_in_code (List.cons_ne_nil _ _) run_b18 (ksA' := k19)
    (vA := .ptr 2 0) (by decide) (evP2 0)
    (by decide) (by decide) rfl b19_in_code (List.cons_ne_nil _ _) run_b19 (ksB' := k20)
    (vB := .ptr 2 1024) (by decide) (evP2 1024)
    (by decide) (by decide) rfl b20_in_code (List.cons_ne_nil _ _) run_b20 rfl (ksZ' := k20z)
    (by decide) (kI := k20) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl b21_in_code (List.cons_ne_nil _ _) run_b21 (by decide) rfl rfl (by decide) rfl
    rfl b22_in_code (List.cons_ne_nil _ _) run_b22 (lblAt hp b21_in_code) rfl rfl rfl
    (by decide) rfl hpc hmid hk hrw).bind fun s1 ⟨hpc1, hmid1, hk1, hrw1⟩ ↦ ?_
  exact rowD hp hmul hmemcpy ok hsz hrow (t := 2) (i := 1) (vars := varsOf c.sl 2 0)
    (by decide) (by decide) rfl rfl
    (by decide) (by decide) b23_in_code (List.cons_ne_nil _ _) run_b23 (ksA' := k20)
    (vA := .ptr 2 2048) (by decide) (evP2 2048)
    (by decide) (by decide) rfl b24_in_code (List.cons_ne_nil _ _) run_b24 (ksB' := k20)
    (vB := .ptr 2 3072) (by decide) (evP2 3072)
    (by decide) (by decide) rfl b25_in_code (List.cons_ne_nil _ _) run_b25 rfl (ksZ' := k20z)
    (by decide) (kI := k20) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl b26_in_code (List.cons_ne_nil _ _) run_b26 (by decide) rfl rfl (by decide) rfl
    rfl b27_in_code (List.cons_ne_nil _ _) run_b27 (lblAt hp b26_in_code) rfl rfl rfl
    (by decide) rfl hpc1 hmid1 hk1 hrw1

/-- **Round 2's rows 2 and 3.** -/
theorem round2b (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b28Offset)) (hmid : Mid c m0 s.data)
    (hk : KAt m0 (varsOf c.sl 2 0) k20 s.data)
    (hrw : ElemsAt s.data.dmem (rwA m0) (F c.sl rows 2 2 0) 4096) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b38Offset) ∧ Mid c m0 s'.data ∧
      KAt m0 (varsOf c.sl 2 0) k38 s'.data ∧
      ElemsAt s'.data.dmem (rwA m0) (F c.sl rows 2 4 0) 4096) s := by
  refine (rowD hp hmul hmemcpy ok hsz hrow (t := 2) (i := 2) (vars := varsOf c.sl 2 0)
    (by decide) (by decide) rfl rfl
    (by decide) (by decide) b28_in_code (List.cons_ne_nil _ _) run_b28 (ksA' := k29)
    (vA := .ptr 2 4096) (by decide) (evP2 4096)
    (by decide) (by decide) rfl b29_in_code (List.cons_ne_nil _ _) run_b29 (ksB' := k30)
    (vB := .ptr 2 5120) (by decide) (evP2 5120)
    (by decide) (by decide) rfl b30_in_code (List.cons_ne_nil _ _) run_b30 rfl (ksZ' := k30z)
    (by decide) (kI := k30) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl b31_in_code (List.cons_ne_nil _ _) run_b31 (by decide) rfl rfl (by decide) rfl
    rfl b32_in_code (List.cons_ne_nil _ _) run_b32 (lblAt hp b31_in_code) rfl rfl rfl
    (by decide) rfl hpc hmid hk hrw).bind fun s1 ⟨hpc1, hmid1, hk1, hrw1⟩ ↦ ?_
  exact rowD hp hmul hmemcpy ok hsz hrow (t := 2) (i := 3) (vars := varsOf c.sl 2 0)
    (by decide) (by decide) rfl rfl
    (by decide) (by decide) b33_in_code (List.cons_ne_nil _ _) run_b33 (ksA' := k34)
    (vA := .ptr 2 6144) (by decide) (evP2 6144)
    (by decide) (by decide) rfl b34_in_code (List.cons_ne_nil _ _) run_b34 (ksB' := k35)
    (vB := .ptr 2 7168) (by decide) (evP2 7168)
    (by decide) (by decide) rfl b35_in_code (List.cons_ne_nil _ _) run_b35 rfl (ksZ' := k38z)
    (by decide) (kI := k38) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl b36_in_code (List.cons_ne_nil _ _) run_b36 (by decide) rfl rfl (by decide) rfl
    rfl b37_in_code (List.cons_ne_nil _ _) run_b37 (lblAt hp b36_in_code) rfl rfl rfl
    (by decide) rfl hpc1 hmid1 hk1 hrw1

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
