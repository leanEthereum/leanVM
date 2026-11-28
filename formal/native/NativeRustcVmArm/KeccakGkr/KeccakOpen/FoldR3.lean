module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldR2
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Exec3

/-!
# `keccak_open`'s fold: round 3

Four rows, unrolled (`b58` to `b77`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen

@[expose] public section

/-- After `b70`: `k73` and the counter X28 zeroed. -/
def k73z : List (XReg × Sym) := k73 ++ [(.X28, .lit 0)]
/-- Round 3's last row's registers. -/
def k76 : List (XReg × Sym) :=
  [(.X22, V0), (.X23, V1), (.X24, A0), (.X25, B0), (.X27, A0), (.X29, P)]
/-- After `b75`: `k76` and the counter X26 zeroed. -/
def k76z : List (XReg × Sym) := k76 ++ [(.X26, .lit 0)]

end

public section

variable [NativeRustcArm.Host] {k : Nat} {c : Cx} {m0 : MachineData} {rows : Array (Array EW)}

/-- **Round 3's rows 0 and 1.** -/
theorem round3a (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b58Offset)) (hmid : Mid c m0 s.data)
    (hk : KAt m0 (varsOf c.sl 3 0) k58 s.data)
    (hrw : ElemsAt s.data.dmem (rwA m0) (F c.sl rows 3 0 0) 4096) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b68Offset) ∧ Mid c m0 s'.data ∧
      KAt m0 (varsOf c.sl 3 0) k38 s'.data ∧
      ElemsAt s'.data.dmem (rwA m0) (F c.sl rows 3 2 0) 4096) s := by
  refine (rowD hp hmul hmemcpy ok hsz hrow (t := 3) (i := 0) (vars := varsOf c.sl 3 0)
    (by decide) (by decide) rfl rfl
    (by decide) (by decide) b58_in_code (List.cons_ne_nil _ _) run_b58 (ksA' := k38)
    (vA := .ptr 2 0) (by decide) (evP2 0)
    (by decide) (by decide) rfl b59_in_code (List.cons_ne_nil _ _) run_b59 (ksB' := k38)
    (vB := .ptr 2 1024) (by decide) (evP2 1024)
    (by decide) (by decide) rfl b60_in_code (List.cons_ne_nil _ _) run_b60 rfl (ksZ' := k38z)
    (by decide) (kI := k38) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl b61_in_code (List.cons_ne_nil _ _) run_b61 (by decide) rfl rfl (by decide) rfl
    rfl b62_in_code (List.cons_ne_nil _ _) run_b62 (lblAt hp b61_in_code) rfl rfl rfl
    (by decide) rfl hpc hmid hk hrw).bind fun s1 ⟨hpc1, hmid1, hk1, hrw1⟩ ↦ ?_
  exact rowD hp hmul hmemcpy ok hsz hrow (t := 3) (i := 1) (vars := varsOf c.sl 3 0)
    (by decide) (by decide) rfl rfl
    (by decide) (by decide) b63_in_code (List.cons_ne_nil _ _) run_b63 (ksA' := k38)
    (vA := .ptr 2 2048) (by decide) (evP2 2048)
    (by decide) (by decide) rfl b64_in_code (List.cons_ne_nil _ _) run_b64 (ksB' := k38)
    (vB := .ptr 2 3072) (by decide) (evP2 3072)
    (by decide) (by decide) rfl b65_in_code (List.cons_ne_nil _ _) run_b65 rfl (ksZ' := k38z)
    (by decide) (kI := k38) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl b66_in_code (List.cons_ne_nil _ _) run_b66 (by decide) rfl rfl (by decide) rfl
    rfl b67_in_code (List.cons_ne_nil _ _) run_b67 (lblAt hp b66_in_code) rfl rfl rfl
    (by decide) rfl hpc1 hmid1 hk1 hrw1

/-- **Round 3's rows 2 and 3.** -/
theorem round3b (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b68Offset)) (hmid : Mid c m0 s.data)
    (hk : KAt m0 (varsOf c.sl 3 0) k38 s.data)
    (hrw : ElemsAt s.data.dmem (rwA m0) (F c.sl rows 3 2 0) 4096) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b78Offset) ∧ Mid c m0 s'.data ∧
      KAt m0 (varsOf c.sl 3 0) k76 s'.data ∧
      ElemsAt s'.data.dmem (rwA m0) (F c.sl rows 3 4 0) 4096) s := by
  refine (rowD hp hmul hmemcpy ok hsz hrow (t := 3) (i := 2) (vars := varsOf c.sl 3 0)
    (by decide) (by decide) rfl rfl
    (by decide) (by decide) b68_in_code (List.cons_ne_nil _ _) run_b68 (ksA' := k38)
    (vA := .ptr 2 4096) (by decide) (evP2 4096)
    (by decide) (by decide) rfl b69_in_code (List.cons_ne_nil _ _) run_b69 (ksB' := k70)
    (vB := .ptr 2 5120) (by decide) (evP2 5120)
    (by decide) (by decide) rfl b70_in_code (List.cons_ne_nil _ _) run_b70 rfl (ksZ' := k73z)
    (by decide) (kI := k73) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl b71_in_code (List.cons_ne_nil _ _) run_b71 (by decide) rfl rfl (by decide) rfl
    rfl b72_in_code (List.cons_ne_nil _ _) run_b72 (lblAt hp b71_in_code) rfl rfl rfl
    (by decide) rfl hpc hmid hk hrw).bind fun s1 ⟨hpc1, hmid1, hk1, hrw1⟩ ↦ ?_
  exact rowD hp hmul hmemcpy ok hsz hrow (t := 3) (i := 3) (vars := varsOf c.sl 3 0)
    (by decide) (by decide) rfl rfl
    (by decide) (by decide) b73_in_code (List.cons_ne_nil _ _) run_b73 (ksA' := k74)
    (vA := .ptr 2 6144) (by decide) (evP2 6144)
    (by decide) (by decide) rfl b74_in_code (List.cons_ne_nil _ _) run_b74 (ksB' := k75)
    (vB := .ptr 2 7168) (by decide) (evP2 7168)
    (by decide) (by decide) rfl b75_in_code (List.cons_ne_nil _ _) run_b75 rfl (ksZ' := k76z)
    (by decide) (kI := k76) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl b76_in_code (List.cons_ne_nil _ _) run_b76 (by decide) rfl rfl (by decide) rfl
    rfl b77_in_code (List.cons_ne_nil _ _) run_b77 (lblAt hp b76_in_code) rfl rfl rfl
    (by decide) rfl hpc1 hmid1 hk1 hrw1

/-- **Round 3**: four rows from `b58` to `b78`. -/
theorem round3 (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b58Offset)) (hmid : Mid c m0 s.data)
    (hk : KAt m0 (varsOf c.sl 3 0) k58 s.data)
    (hrw : ElemsAt s.data.dmem (rwA m0) (Fr c.sl rows 3) 4096) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b78Offset) ∧ Mid c m0 s'.data ∧
      KAt m0 (varsOf c.sl 3 0) k76 s'.data ∧
      ElemsAt s'.data.dmem (rwA m0) (Fr c.sl rows 4) 4096) s := by
  rw [← F_zero] at hrw
  refine (round3a hp hmul hmemcpy ok hsz hrow hpc hmid hk hrw).bind
    fun s1 ⟨hpc1, hmid1, hk1, hrw1⟩ ↦ ?_
  refine (round3b hp hmul hmemcpy ok hsz hrow hpc1 hmid1 hk1 hrw1).mono
    fun s2 ⟨hpc2, hmid2, hk2, hrw2⟩ ↦ ⟨hpc2, hmid2, hk2, ?_⟩
  rw [show (4 : Nat) = half 3 from rfl, F_half] at hrw2
  exact hrw2

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
