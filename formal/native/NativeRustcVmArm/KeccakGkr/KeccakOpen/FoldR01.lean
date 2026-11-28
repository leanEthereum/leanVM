module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldLoop
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.Exec1

/-!
# `keccak_open`'s fold: rounds 0 and 1

Each loops over its rows (`LoopI`): round 0 over 32 (`b5` to `b10`), round 1 over 16 (`b12` to
`b17`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen

@[expose] public section

/-- **A looped round at row `i`**. -/
def LoopI [Labels] (c : Cx) (m0 : MachineData) (rows : Array (Array EW)) (t i : Nat)
    (st : MachineData) : Prop :=
  Mid c m0 st ∧ KAt m0 (varsOf c.sl t i) kO st ∧ ElemsAt st.dmem (rwA m0) (F c.sl rows t i 0) 4096

/-- After `b7`: round 0's inner loop's start. -/
def kZ0 : List (XReg × Sym) :=
  [(.X22, V0), (.X23, V1), (.X24, .bin .add .W64 P (.var 3)), (.X25, .var 3), (.X26, .var 2),
    (.X27, A0), (.X28, B0), (.X29, .lit 0)]

/-- After `b14`: round 1's inner loop's start. -/
def kZ1 : List (XReg × Sym) :=
  [(.X19, .lit 0), (.X22, V0), (.X23, V1), (.X24, .bin .add .W64 P (.var 3)), (.X25, .var 3),
    (.X26, .var 2), (.X27, A0), (.X28, B0), (.X29, P)]

end

public section

variable [NativeRustcArm.Host] {k : Nat} {c : Cx} {m0 : MachineData} {rows : Array (Array EW)}

/-- **A row of round 0.** -/
theorem row0 (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    (i : Nat) (s : MachineState) (hi : i < 32) (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b5Offset))
    (hI : LoopI c m0 rows 0 i s.data) :
    Eventually (step1 Host.exe) (fun s' ↦
      (i + 1 < 32 ∧ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b5Offset) ∧ LoopI c m0 rows 0 (i + 1) s'.data) ∨
      (i + 1 = 32 ∧ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b11Offset) ∧ LoopI c m0 rows 0 (i + 1) s'.data)) s := by
  obtain ⟨hmid, hk, hrw⟩ := hI
  refine (rowL hp hmul hmemcpy ok hsz hrow (t := 0) (i := i) (vars := varsOf c.sl 0 i)
    (by decide) hi rfl rfl rfl
    (by decide) (by decide) b5_in_code (List.cons_ne_nil _ _) run_b5 (ksA' := kM)
    (vA := src0) (by decide) (ev_src0 (by omega))
    (by decide) (by decide) rfl b6_in_code (List.cons_ne_nil _ _) run_b6 (ksB' := kM)
    (vB := .bin .add .W64 src0 (.lit 1024)) (by decide) (ev_src1 (by omega))
    (by decide) (by decide) rfl b7_in_code (List.cons_ne_nil _ _) run_b7 rfl (ksZ' := kZ0)
    (by decide) (kI := kLp) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl b8_in_code (List.cons_ne_nil _ _) run_b8 (by decide) rfl rfl (by decide) rfl rfl
    rfl b9_in_code (List.cons_ne_nil _ _) run_b9 (lblAt hp b8_in_code) rfl rfl rfl
    (by decide) rfl hpc hmid hk hrw).bind fun s1 ⟨hpc1, hmid1, hk1, hrw1⟩ ↦ ?_
  refine (rowTail hp ok (t := 0) (n := 32) (by decide) (by omega) (by decide) b10_in_code
    (List.cons_ne_nil _ _) run_b10 rfl (by decide) (lblAt hp b5_in_code) hpc1 hmid1
    (hk1.sub (by decide))).mono fun s2 ⟨hpc2, hmid2, hk2, hd2⟩ ↦ ?_
  have hI2 : LoopI c m0 rows 0 (i + 1) s2.data := ⟨hmid2, hk2, by rw [hd2]; exact hrw1⟩
  rcases hpc2 with ⟨h, hpc2⟩ | ⟨h, hpc2⟩
  · exact Or.inl ⟨h, hpc2, hI2⟩
  · exact Or.inr ⟨h, by rw [hpc2, Nat.add_assoc]; rfl, hI2⟩

/-- **A row of round 1.** -/
theorem row1 (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    (i : Nat) (s : MachineState) (hi : i < 16) (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b12Offset))
    (hI : LoopI c m0 rows 1 i s.data) :
    Eventually (step1 Host.exe) (fun s' ↦
      (i + 1 < 16 ∧ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b12Offset) ∧ LoopI c m0 rows 1 (i + 1) s'.data) ∨
      (i + 1 = 16 ∧ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b18Offset) ∧ LoopI c m0 rows 1 (i + 1) s'.data)) s := by
  obtain ⟨hmid, hk, hrw⟩ := hI
  refine (rowL hp hmul hmemcpy ok hsz hrow (t := 1) (i := i) (vars := varsOf c.sl 1 i)
    (by decide) hi rfl rfl rfl
    (by decide) (by decide) b12_in_code (List.cons_ne_nil _ _) run_b12 (ksA' := kM)
    (vA := src0) (by decide) (ev_src0 (by omega))
    (by decide) (by decide) rfl b13_in_code (List.cons_ne_nil _ _) run_b13 (ksB' := kM)
    (vB := .bin .add .W64 src0 (.lit 1024)) (by decide) (ev_src1 (by omega))
    (by decide) (by decide) rfl b14_in_code (List.cons_ne_nil _ _) run_b14 rfl (ksZ' := kZ1)
    (by decide) (kI := kLp) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rfl b15_in_code (List.cons_ne_nil _ _) run_b15 (by decide) rfl rfl (by decide) rfl rfl
    rfl b16_in_code (List.cons_ne_nil _ _) run_b16 (lblAt hp b15_in_code) rfl rfl rfl
    (by decide) rfl hpc hmid hk hrw).bind fun s1 ⟨hpc1, hmid1, hk1, hrw1⟩ ↦ ?_
  refine (rowTail hp ok (t := 1) (n := 16) (by decide) (by omega) (by decide) b17_in_code
    (List.cons_ne_nil _ _) run_b17 rfl (by decide) (lblAt hp b12_in_code) hpc1 hmid1
    (hk1.sub (by decide))).mono fun s2 ⟨hpc2, hmid2, hk2, hd2⟩ ↦ ?_
  have hI2 : LoopI c m0 rows 1 (i + 1) s2.data := ⟨hmid2, hk2, by rw [hd2]; exact hrw1⟩
  rcases hpc2 with ⟨h, hpc2⟩ | ⟨h, hpc2⟩
  · exact Or.inl ⟨h, hpc2, hI2⟩
  · exact Or.inr ⟨h, by rw [hpc2, Nat.add_assoc]; rfl, hI2⟩

/-- **Round 0**: its 32 rows. -/
theorem round0 (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b5Offset)) (hI : LoopI c m0 rows 0 0 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b11Offset) ∧
      LoopI c m0 rows 0 32 s'.data) s :=
  loopN (P := LoopI c m0 rows 0) (row0 hp hmul hmemcpy ok hsz hrow) (by decide) hpc hI

/-- **Round 1**: its 16 rows. -/
theorem round1 (hp : Placed code k)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) (ok : Ok c.a m0)
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b12Offset)) (hI : LoopI c m0 rows 1 0 s.data) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b18Offset) ∧
      LoopI c m0 rows 1 16 s'.data) s :=
  loopN (P := LoopI c m0 rows 1) (row1 hp hmul hmemcpy ok hsz hrow) (by decide) hpc hI

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
