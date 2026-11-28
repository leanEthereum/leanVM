module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldR2

/-!
# `keccak_open`'s fold: round 2's rows 4 to 7, the round
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen

public section

variable [NativeRustcArm.Host] {k : Nat} {c : Cx} {m0 : MachineData} {rows : Array (Array EW)}

/-- **Round 2's rows 4 and 5.** -/
theorem round2c (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b38Offset)) (hmid : Mid c m0 s.data)
    (hk : KAt m0 (varsOf c.sl 2 0) k38 s.data)
    (hrw : ElemsAt s.data.dmem (rwA m0) (F c.sl rows 2 4 0) 4096) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b48Offset) ∧ Mid c m0 s'.data ∧
      KAt m0 (varsOf c.sl 2 0) k38 s'.data ∧
      ElemsAt s'.data.dmem (rwA m0) (F c.sl rows 2 6 0) 4096) s := by
  refine (rowD hp hmul hmemcpy ok hsz hrow (t := 2) (i := 4) (vars := varsOf c.sl 2 0)
    (by decide) (by decide) rfl rfl
    (by decide) (by decide) b38_in_code (List.cons_ne_nil _ _) run_b38 (ksA' := k38)
    (vA := .ptr 2 8192) (by decide) (evP2 8192)
    (by decide) (by decide) rfl b39_in_code (List.cons_ne_nil _ _) run_b39 (ksB' := k38)
    (vB := .ptr 2 9216) (by decide) (evP2 9216)
    (by decide) (by decide) rfl b40_in_code (List.cons_ne_nil _ _) run_b40 rfl (ksZ' := k38z)
    (by decide) (kI := k38) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl b41_in_code (List.cons_ne_nil _ _) run_b41 (by decide) rfl rfl (by decide) rfl
    rfl b42_in_code (List.cons_ne_nil _ _) run_b42 (lblAt hp b41_in_code) rfl rfl rfl
    (by decide) rfl hpc hmid hk hrw).bind fun s1 ⟨hpc1, hmid1, hk1, hrw1⟩ ↦ ?_
  exact rowD hp hmul hmemcpy ok hsz hrow (t := 2) (i := 5) (vars := varsOf c.sl 2 0)
    (by decide) (by decide) rfl rfl
    (by decide) (by decide) b43_in_code (List.cons_ne_nil _ _) run_b43 (ksA' := k38)
    (vA := .ptr 2 10240) (by decide) (evP2 10240)
    (by decide) (by decide) rfl b44_in_code (List.cons_ne_nil _ _) run_b44 (ksB' := k38)
    (vB := .ptr 2 11264) (by decide) (evP2 11264)
    (by decide) (by decide) rfl b45_in_code (List.cons_ne_nil _ _) run_b45 rfl (ksZ' := k38z)
    (by decide) (kI := k38) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl b46_in_code (List.cons_ne_nil _ _) run_b46 (by decide) rfl rfl (by decide) rfl
    rfl b47_in_code (List.cons_ne_nil _ _) run_b47 (lblAt hp b46_in_code) rfl rfl rfl
    (by decide) rfl hpc1 hmid1 hk1 hrw1

/-- **Round 2's rows 6 and 7.** -/
theorem round2d (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b48Offset)) (hmid : Mid c m0 s.data)
    (hk : KAt m0 (varsOf c.sl 2 0) k38 s.data)
    (hrw : ElemsAt s.data.dmem (rwA m0) (F c.sl rows 2 6 0) 4096) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b58Offset) ∧ Mid c m0 s'.data ∧
      KAt m0 (varsOf c.sl 2 0) k38 s'.data ∧
      ElemsAt s'.data.dmem (rwA m0) (F c.sl rows 2 8 0) 4096) s := by
  refine (rowD hp hmul hmemcpy ok hsz hrow (t := 2) (i := 6) (vars := varsOf c.sl 2 0)
    (by decide) (by decide) rfl rfl
    (by decide) (by decide) b48_in_code (List.cons_ne_nil _ _) run_b48 (ksA' := k38)
    (vA := .ptr 2 12288) (by decide) (evP2 12288)
    (by decide) (by decide) rfl b49_in_code (List.cons_ne_nil _ _) run_b49 (ksB' := k38)
    (vB := .ptr 2 13312) (by decide) (evP2 13312)
    (by decide) (by decide) rfl b50_in_code (List.cons_ne_nil _ _) run_b50 rfl (ksZ' := k38z)
    (by decide) (kI := k38) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl b51_in_code (List.cons_ne_nil _ _) run_b51 (by decide) rfl rfl (by decide) rfl
    rfl b52_in_code (List.cons_ne_nil _ _) run_b52 (lblAt hp b51_in_code) rfl rfl rfl
    (by decide) rfl hpc hmid hk hrw).bind fun s1 ⟨hpc1, hmid1, hk1, hrw1⟩ ↦ ?_
  exact rowD hp hmul hmemcpy ok hsz hrow (t := 2) (i := 7) (vars := varsOf c.sl 2 0)
    (by decide) (by decide) rfl rfl
    (by decide) (by decide) b53_in_code (List.cons_ne_nil _ _) run_b53 (ksA' := k38)
    (vA := .ptr 2 14336) (by decide) (evP2 14336)
    (by decide) (by decide) rfl b54_in_code (List.cons_ne_nil _ _) run_b54 (ksB' := k38)
    (vB := .ptr 2 15360) (by decide) (evP2 15360)
    (by decide) (by decide) rfl b55_in_code (List.cons_ne_nil _ _) run_b55 rfl (ksZ' := k38z)
    (by decide) (kI := k38) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl b56_in_code (List.cons_ne_nil _ _) run_b56 (by decide) rfl rfl (by decide) rfl
    rfl b57_in_code (List.cons_ne_nil _ _) run_b57 (lblAt hp b56_in_code) rfl rfl rfl
    (by decide) rfl hpc1 hmid1 hk1 hrw1

/-- **Round 2**: eight rows from `b18` to `b58`. -/
theorem round2 (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b18Offset)) (hmid : Mid c m0 s.data)
    (hk : KAt m0 (varsOf c.sl 2 0) kP s.data)
    (hrw : ElemsAt s.data.dmem (rwA m0) (Fr c.sl rows 2) 4096) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b58Offset) ∧ Mid c m0 s'.data ∧
      KAt m0 (varsOf c.sl 2 0) k38 s'.data ∧
      ElemsAt s'.data.dmem (rwA m0) (Fr c.sl rows 3) 4096) s := by
  rw [← F_zero] at hrw
  refine (round2a hp hmul hmemcpy ok hsz hrow hpc hmid hk hrw).bind
    fun s1 ⟨hpc1, hmid1, hk1, hrw1⟩ ↦ ?_
  refine (round2b hp hmul hmemcpy ok hsz hrow hpc1 hmid1 hk1 hrw1).bind
    fun s2 ⟨hpc2, hmid2, hk2, hrw2⟩ ↦ ?_
  refine (round2c hp hmul hmemcpy ok hsz hrow hpc2 hmid2 hk2 hrw2).bind
    fun s3 ⟨hpc3, hmid3, hk3, hrw3⟩ ↦ ?_
  refine (round2d hp hmul hmemcpy ok hsz hrow hpc3 hmid3 hk3 hrw3).mono
    fun s4 ⟨hpc4, hmid4, hk4, hrw4⟩ ↦ ⟨hpc4, hmid4, hk4, ?_⟩
  rw [show (8 : Nat) = half 2 from rfl, F_half] at hrw4
  exact hrw4

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
