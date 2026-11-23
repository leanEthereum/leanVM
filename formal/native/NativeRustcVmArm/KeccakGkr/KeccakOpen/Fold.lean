module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldR01
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldR2c
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldR5

/-!
# `keccak_open`: the fold

From the start of round 0's loop (`b5`, after `b4`) to `b93`: the rows folded six times, round by
round (`round0`, `b11`, `round1`, `round2` to `round5`).
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen

public section

variable [NativeRustcArm.Host] {k : Nat}

/-- **The fold**: from `b5` with round 0's registers and the rows to `b93`, the rows folded. -/
theorem fold_run (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost)
    {c : Cx} {m0 : MachineData} {rows : Array (Array EW)} (ok : Ok c.a m0)
    (hsz : rows.size = 64) (hrow : ∀ r < 64, (rows.getD r #[]).size = 64)
    {s : MachineState} (hpc : s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b5Offset)) (hmid : Mid c m0 s.data)
    (h29 : s.data.regs.X29.toBitVec = rwA m0)
    (h27 : s.data.regs.X27.toBitVec = fbA m0 + BitVec.ofNat 64 80)
    (h28 : s.data.regs.X28.toBitVec = fbA m0 + BitVec.ofNat 64 1104)
    (h22 : s.data.regs.X22 = (c.sl.getD 0 0).c0) (h23 : s.data.regs.X23 = (c.sl.getD 0 0).c1)
    (h25 : s.data.regs.X25 = 0) (h26 : s.data.regs.X26 = 0)
    (hrw : ElemsAt s.data.dmem (rwA m0) (Fr c.sl rows 0) 4096) :
    Eventually (step1 Host.exe) (fun s' ↦ s'.pc = Host.addrOf (k + NativeRustcVmArm.Vm.KeccakOpen.b93Offset) ∧ Mid c m0 s'.data ∧
      ElemsAt s'.data.dmem (rwA m0) (Fr c.sl rows 6) 4096) s := by
  have hk0 : KAt m0 (varsOf c.sl 0 0) kO s.data := by
    refine KAt.of_reg hmid.body.sp fun p hp ↦ ?_
    rcases mem_kO hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show s.data.regs.X29.toBitVec = rwA m0 + BitVec.ofInt 64 0
      rw [h29, ofInt0, NativeRustcVm.addr_add_zero]
    · show s.data.regs.X27.toBitVec = fbA m0 + BitVec.ofInt 64 80
      rw [h27, show BitVec.ofInt 64 80 = BitVec.ofNat 64 80 by decide]
    · show s.data.regs.X28.toBitVec = fbA m0 + BitVec.ofInt 64 1104
      rw [h28, show BitVec.ofInt 64 1104 = BitVec.ofNat 64 1104 by decide]
    · show s.data.regs.X22.toBitVec = (c.sl.getD 0 0).c0.toBitVec
      rw [h22]
    · show s.data.regs.X23.toBitVec = (c.sl.getD 0 0).c1.toBitVec
      rw [h23]
    · show s.data.regs.X26.toBitVec = BitVec.ofNat 64 0
      rw [h26]; rfl
    · show s.data.regs.X25.toBitVec = BitVec.ofNat 64 (1024 * 0)
      rw [h25]; rfl
  rw [← F_zero] at hrw
  -- round 0
  refine (round0 hp hmul hmemcpy ok hsz hrow hpc ⟨hmid, hk0, hrw⟩).bind
    fun s1 ⟨hpc1, hmid1, hk1, hrw1⟩ ↦ ?_
  have hsl1 : 1 < c.sl.size := by rw [hmid1.sl_size]; decide
  -- `b11`: round 1's challenge
  refine (zeroBlock hp ok (ks' := kS1) (vars := varsOf c.sl 1 0) (by decide) hsl1 rfl rfl
    b11_in_code (List.cons_ne_nil _ _) run_b11 rfl (by decide) hpc1 hmid1
    (KAt.revar (hk1.sub (show subK kP kO = true by decide)) (by decide))).bind
    fun s2 ⟨hpc2, hmid2, hk2, hd2⟩ ↦ ?_
  have hrw2 : ElemsAt s2.data.dmem (rwA m0) (F c.sl rows 1 0 0) 4096 := by
    rw [hd2, F_zero, ← F_half]
    exact hrw1
  refine (round1 hp hmul hmemcpy ok hsz hrow (hpc2.trans (by rw [Nat.add_assoc]; rfl))
    ⟨hmid2, kO_zero hk2, hrw2⟩).bind fun s3 ⟨hpc3, hmid3, hk3, hrw3⟩ ↦ ?_
  rw [show (16 : Nat) = half 1 from rfl, F_half] at hrw3
  -- rounds 2 to 5
  refine (round2 hp hmul hmemcpy ok hsz hrow hpc3 hmid3
    (KAt.revar (hk3.sub (show subK kP kO = true by decide)) (by decide)) hrw3).bind
    fun s4 ⟨hpc4, hmid4, hk4, hrw4⟩ ↦ ?_
  refine (round3 hp hmul hmemcpy ok hsz hrow hpc4 hmid4
    (KAt.revar (hk4.sub (show subK k58 k38 = true by decide)) (by decide)) hrw4).bind
    fun s5 ⟨hpc5, hmid5, hk5, hrw5⟩ ↦ ?_
  refine (round4 hp hmul hmemcpy ok hsz hrow hpc5 hmid5
    (KAt.revar (hk5.sub (show subK k78 k76 = true by decide)) (by decide)) hrw5).bind
    fun s6 ⟨hpc6, hmid6, hk6, hrw6⟩ ↦ ?_
  exact round5 hp hmul hmemcpy ok hsz hrow hpc6 hmid6
    (KAt.revar (hk6.sub (show subK k88 k79 = true by decide)) (by decide)) hrw6

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
