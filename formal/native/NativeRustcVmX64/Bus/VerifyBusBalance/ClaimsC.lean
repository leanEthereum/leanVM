module

public import NativeRustcVmX64.Bus.VerifyBusBalance.ClaimsB
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmX64.Code.Vm.BytecodeShare.Names
public import NativeRustcVmX64.Code.Vm.ComputedBytecodeValue.Names
public import NativeRustcVmX64.Code.Vm.Kpow.Names
public import NativeRustcVmX64.Code.Vm.PushClaim.Names
public import NativeRustcVmX64.Code.Vm.VerifyBusBalanceClosure0.Names

/-!
# `verify_bus_balance`'s last three claims and the bytecode point's zeroing (x86-64)

From `b28` (`k + NativeRustcVmX64.Vm.VerifyBusBalance.b28Offset`), the first claim pushed: `b28` to `b34` check each `push_claim` and push
the next three (`pushBlk`, `pushTest`); `b35` to `b37` zero the bytecode point, 17 rounds of
`NativeRustcVmX64.Vm.VerifyBusBalance.label_17` (`loop_spec`); then the bytecode share (`claimsB_spec`).
-/

namespace NativeRustcVmX64.Bus.VerifyBusBalance

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyBusBalance
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Bus.Gkr
open NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Bus NativeRustcVm.Layout

public section
variable [Host] {a : DecArea} {s0 : TState} {L : LayoutW} {m0 : MachineData} {k : Nat}

/-- A state of the zeroing loop's rounds. -/
theorem match_l2 {d : MachineData} (fr : St m0 104 d) {i : Nat}
    (hrax : reg d .rax = BitVec.ofNat 64 (56 + 64 * i)) {ret : BitVec 64} :
    Match (frameEnv m0 d 5520 [] (fun _ ↦ 0) ret) (l2S i) d :=
  match_ofMachine ⟨rfl, trivial⟩ ⟨fr.frame.rsp_eval, hrax, trivial⟩ trivial trivial trivial

/-- **The bytecode point's zeroing**, from round `i` (`NativeRustcVmX64.Vm.VerifyBusBalance.label_17`, `k + NativeRustcVmX64.Vm.VerifyBusBalance.b36Offset`). -/
theorem loop_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hbs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.BytecodeShare.entryLabel) (BytecodeSharePre a s) (BytecodeSharePost a s))
    (hcbv : Spec (Labels.label NativeRustcVmX64.Vm.ComputedBytecodeValue.entryLabel) ComputedBytecodeValuePre
      ComputedBytecodeValuePost)
    (hkp : Spec (Labels.label NativeRustcVmX64.Vm.Kpow.entryLabel) KpowPre KpowPost)
    (hfc : Spec (Labels.label NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label NativeRustcVmX64.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63))
    {w pt tv mem : Array EW} {beta mf bf : EW} {s3 : TState}
    (hrun : (verifyBusBalance L).run s0 =
      ((bytecodeShare w (pt.extract 0 L.logBytecode)).run s3).bind fun y4 ↦
        ((computedBytecodeValue L.bytecode y4.1.2.1 y4.1.2.2).run y4.2).bind fun y5 ↦
          some (resultOf L w beta pt tv mem mf bf y4.1.1 y4.1.2.1, y5.2)) :
    ∀ n i, i + n = 16 → ∀ d, ClSt a L m0 w pt tv mem beta mf bf s3 (claimsOf L pt mem mf bf) d →
      reg d .rax = BitVec.ofNat 64 (56 + 64 * i) →
      Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b36Offset)⟩ := by
  have hS := pre_stack h
  intro n
  induction n with
  | zero =>
    intro i hi d A hrax
    obtain ⟨S, hx, hmid, hw, -, hk, -⟩ := of_ok36 (ok36_all i (by omega))
    have hwf := wf0 h A.fr.frame.kept (vars := fun _ ↦ 0) (ret := 0)
    refine exec_then (infix_of b36_in_code (by simp [b36]) hp) hx hwf nofun (match_l2 A.fr hrax)
      fun st1 hm1 hpc1 ↦ ?_
    have fr1 : St m0 104 st1.data := St.blk A.fr hS hwf hm1 hmid fun q hq ↦ wr0 hS hw (by omega) hq
    have hs1 := blk_same hS hwf hm1 hw (by omega)
    have sm1 := A.sm.of_keep (keepIv_block hwf hm1 (writesIn_of_mid hmid)
      (lo := 624) (hi := 1744) (fun w hw' hr ↦ by have := hw w hw'; omega) (by decide) (by decide))
    obtain ⟨hts1, hcl1⟩ := tc_keep h (hm1.kept hwf) hs1 (fun q hq ↦ .inl (frame_stack hS hq))
      A.ts A.cl
    have A1 := A.regs fr1 sm1 (fun r hr ↦ hk.reg hm1 (clRegs_cs r hr).2.1) hts1 hcl1
    simp only [PcOk, SBool.eval, show i = 16 by omega, decide_true, ↓reduceIte] at hpc1
    refine at_pc (hpc1.trans (hp.label (label_of_infix b38_in_code rfl)))
      (share_spec hp h hbs hcbv hkp hfc hacc hext A1.fr hrun A1.sm A1.xbx A1.x13 A1.x14 A1.xbp
        A1.x12 A1.ts A1.cl)
  | succ n ih =>
    intro i hi d A hrax
    obtain ⟨S, hx, hmid, hw, -, hk, hra⟩ := of_ok36 (ok36_all i (by omega))
    have hwf := wf0 h A.fr.frame.kept (vars := fun _ ↦ 0) (ret := 0)
    refine exec_then (infix_of b36_in_code (by simp [b36]) hp) hx hwf nofun (match_l2 A.fr hrax)
      fun st1 hm1 hpc1 ↦ ?_
    have fr1 : St m0 104 st1.data := St.blk A.fr hS hwf hm1 hmid fun q hq ↦ wr0 hS hw (by omega) hq
    have hs1 := blk_same hS hwf hm1 hw (by omega)
    have sm1 := A.sm.of_keep (keepIv_block hwf hm1 (writesIn_of_mid hmid)
      (lo := 624) (hi := 1744) (fun w hw' hr ↦ by have := hw w hw'; omega) (by decide) (by decide))
    obtain ⟨hts1, hcl1⟩ := tc_keep h (hm1.kept hwf) hs1 (fun q hq ↦ .inl (frame_stack hS hq))
      A.ts A.cl
    have A1 := A.regs fr1 sm1 (fun r hr ↦ hk.reg hm1 (clRegs_cs r hr).2.1) hts1 hcl1
    have hne : decide (i = 16) = false := by simp only [decide_eq_false_iff_not]; omega
    simp only [PcOk, SBool.eval, hne, Bool.false_eq_true, ↓reduceIte] at hpc1
    rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b36Offset + b36.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b37Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b36_next]] at hpc1
    have hrax1 : reg st1.data .rax = BitVec.ofNat 64 (56 + 64 * i) := hm1.regs .rax _ hra
    obtain ⟨S2, hx2, hmid2, hw2, -, hk2, hra2⟩ := of_ok37 (ok37_all i (by omega))
    have hwf2 := wf0 h fr1.frame.kept (vars := fun _ ↦ 0) (ret := 0)
    refine exec_at (infix_of b37_in_code (by simp [b37]) hp) hx2 hwf2 nofun hpc1
      (match_l2 fr1 hrax1) fun st2 hm2 hpc2 ↦ ?_
    have fr2 : St m0 104 st2.data := St.blk fr1 hS hwf2 hm2 hmid2 fun q hq ↦ wr0 hS hw2 (by omega) hq
    have hs2 := blk_same hS hwf2 hm2 hw2 (by omega)
    have sm2 := A1.sm.of_keep (keepIv_block hwf2 hm2 (writesIn_of_mid hmid2)
      (lo := 624) (hi := 1744) (fun w hw' hr ↦ by have := hw2 w hw'; omega) (by decide) (by decide))
    obtain ⟨hts2, hcl2⟩ := tc_keep h (hm2.kept hwf2) hs2 (fun q hq ↦ .inl (frame_stack hS hq))
      A1.ts A1.cl
    have A2 := A1.regs fr2 sm2 (fun r hr ↦ hk2.reg hm2 (clRegs_cs r hr).2.1) hts2 hcl2
    simp only [PcOk] at hpc2
    refine at_pc (hpc2.trans (hp.label (label_of_infix b36_in_code rfl)))
      (ih (i + 1) (by omega) st2.data A2 ?_)
    rw [show reg st2.data .rax = _ from hm2.regs .rax _ hra2]
    show BitVec.ofNat 64 (120 + 64 * i) = _
    congr 1
    omega

/-- **The last three claims and the zeroing** (`b28`, `k + NativeRustcVmX64.Vm.VerifyBusBalance.b28Offset`). -/
theorem claimsB_spec (hp : Placed code k) (h : VerifyBusBalancePre a s0 L m0)
    (hpc : ∀ cs, Spec (Labels.label NativeRustcVmX64.Vm.PushClaim.entryLabel) (PushClaimPre cs) (PushClaimPost cs))
    (hbs : ∀ s, Spec (Labels.label NativeRustcVmX64.Vm.BytecodeShare.entryLabel) (BytecodeSharePre a s) (BytecodeSharePost a s))
    (hcbv : Spec (Labels.label NativeRustcVmX64.Vm.ComputedBytecodeValue.entryLabel) ComputedBytecodeValuePre
      ComputedBytecodeValuePost)
    (hkp : Spec (Labels.label NativeRustcVmX64.Vm.Kpow.entryLabel) KpowPre KpowPost)
    (hfc : Spec (Labels.label NativeRustcVmX64.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost)
    (hacc : ∀ L rows bl F SL, Spec (Labels.label NativeRustcVmX64.Vm.AccumulateSide.entryLabel)
      (AccumulateSidePre L rows bl F SL) (AccumulateSidePost L rows bl F SL))
    (hext : Spec (Labels.label NativeRustcVmX64.Vm.BufEW63Extend.entryLabel) (BufEWExtendPre 63) (BufEWExtendPost 63))
    {w pt tv mem : Array EW} {beta mf bf : EW} {s3 : TState}
    (hrun : (verifyBusBalance L).run s0 =
      ((bytecodeShare w (pt.extract 0 L.logBytecode)).run s3).bind fun y4 ↦
        ((computedBytecodeValue L.bytecode y4.1.2.1 y4.1.2.2).run y4.2).bind fun y5 ↦
          some (resultOf L w beta pt tv mem mf bf y4.1.1 y4.1.2.1, y5.2))
    {d : MachineData}
    (A : ClSt a L m0 w pt tv mem beta mf bf s3
      #[⟨LeanVM.Protocol.Verifier.memory0, pt.extract 0 L.logMemory, mem.getD 0 0⟩] d)
    (hal : boolRet d = 1) :
    Eventually (step1 Host.exe) (Goal a s0 L m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.VerifyBusBalance.b28Offset)⟩ := by
  have hS := pre_stack h
  have lm := (pre_lay h).log_memory_le
  have lb := (pre_lay h).log_bytecode_le
  refine pushTest hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b28Offset) (infix_of b28_in_code (by simp [b28]) hp) rfl exit_b28 ok_b28
    A hal fun d1 A1 ↦ ?_
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b28Offset + 2 = k + NativeRustcVmX64.Vm.VerifyBusBalance.b29Offset from by simpa only [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b28_length, NativeRustcVmX64.Vm.VerifyBusBalance.b28Length] using congrArg (k + ·) NativeRustcVmX64.Vm.VerifyBusBalance.b28_next]
  have mw1 := mem_words A1.sm.hmem A1.sm.msz (i := 1) (by omega)
  refine pushBlk h hpc (j := NativeRustcVmX64.Vm.VerifyBusBalance.b29Offset) (infix_of b29_in_code (by simp [b29]) hp) rfl exit_b29 ok_b29
    A1 (by simp [claimCap]) lm A1.xbp mw1.1 mw1.2 (by decide) fun d2 A2 hal2 ↦ ?_
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b29Offset + 7 = k + NativeRustcVmX64.Vm.VerifyBusBalance.b30Offset from by simpa only [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b29_length, NativeRustcVmX64.Vm.VerifyBusBalance.b29Length] using congrArg (k + ·) NativeRustcVmX64.Vm.VerifyBusBalance.b29_next]
  refine pushTest hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b30Offset) (infix_of b30_in_code (by simp [b30]) hp) rfl exit_b30 ok_b30
    A2 hal2 fun d3 A3 ↦ ?_
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b30Offset + 2 = k + NativeRustcVmX64.Vm.VerifyBusBalance.b31Offset from by simpa only [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b30_length, NativeRustcVmX64.Vm.VerifyBusBalance.b30Length] using congrArg (k + ·) NativeRustcVmX64.Vm.VerifyBusBalance.b30_next]
  refine pushBlk h hpc (j := NativeRustcVmX64.Vm.VerifyBusBalance.b31Offset) (infix_of b31_in_code (by simp [b31]) hp) rfl exit_b31 ok_b31
    A3 (by simp [claimCap]) lm A3.xbp A3.sm.w168 A3.sm.w160 (by decide) fun d4 A4 hal4 ↦ ?_
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b31Offset + 7 = k + NativeRustcVmX64.Vm.VerifyBusBalance.b32Offset from by simpa only [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b31_length, NativeRustcVmX64.Vm.VerifyBusBalance.b31Length] using congrArg (k + ·) NativeRustcVmX64.Vm.VerifyBusBalance.b31_next]
  refine pushTest hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b32Offset) (infix_of b32_in_code (by simp [b32]) hp) rfl exit_b32 ok_b32
    A4 hal4 fun d5 A5 ↦ ?_
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b32Offset + 2 = k + NativeRustcVmX64.Vm.VerifyBusBalance.b33Offset from by simpa only [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b32_length, NativeRustcVmX64.Vm.VerifyBusBalance.b32Length] using congrArg (k + ·) NativeRustcVmX64.Vm.VerifyBusBalance.b32_next]
  refine pushBlk h hpc (j := NativeRustcVmX64.Vm.VerifyBusBalance.b33Offset) (infix_of b33_in_code (by simp [b33]) hp) rfl exit_b33 ok_b33
    A5 (by simp [claimCap]) lb A5.x12 A5.sm.w152 A5.sm.w144 (by decide) fun d6 A6 hal6 ↦ ?_
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b33Offset + 7 = k + NativeRustcVmX64.Vm.VerifyBusBalance.b34Offset from by simpa only [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b33_length, NativeRustcVmX64.Vm.VerifyBusBalance.b33Length] using congrArg (k + ·) NativeRustcVmX64.Vm.VerifyBusBalance.b33_next]
  refine pushTest hp h (j := NativeRustcVmX64.Vm.VerifyBusBalance.b34Offset) (infix_of b34_in_code (by simp [b34]) hp) rfl exit_b34 ok_b34
    A6 hal6 fun d7 A7 ↦ ?_
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b34Offset + 2 = k + NativeRustcVmX64.Vm.VerifyBusBalance.b35Offset from by simpa only [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b34_length, NativeRustcVmX64.Vm.VerifyBusBalance.b34Length] using congrArg (k + ·) NativeRustcVmX64.Vm.VerifyBusBalance.b34_next]
  -- `b35`: the zeroing's counter.
  have hwf := wf0 h A7.fr.frame.kept (vars := fun _ ↦ 0) (ret := 0)
  refine exec_then (infix_of b35_in_code (by simp [b35]) hp) exit_b35 hwf nofun (match_fS A7.fr)
    fun st8 hm8 hpc8 ↦ ?_
  obtain ⟨hmid8, hmem8, hrax8, hk8⟩ := ok_b35
  have fr8 := (A7.fr.block0 hS N_ge hwf hm8 hmid8 slots_le (by simp [hmem8])).1
  have hd8 : st8.data.dmem = d7.dmem := hm8.dmem_eq hwf hmem8
  have A8 := A7.regs fr8 (hd8 ▸ A7.sm) (fun r hr ↦ hk8.reg hm8 (clRegs_cs r hr).2.1) (hd8 ▸ A7.ts)
    (hd8 ▸ A7.cl)
  simp only [PcOk] at hpc8
  rw [show k + NativeRustcVmX64.Vm.VerifyBusBalance.b35Offset + b35.length = k + NativeRustcVmX64.Vm.VerifyBusBalance.b36Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.VerifyBusBalance.b35_next]] at hpc8
  exact at_pc hpc8 (loop_spec hp h hbs hcbv hkp hfc hacc hext hrun 16 0 rfl st8.data A8
    (hm8.regs .rax _ hrax8))

end

end NativeRustcVmX64.Bus.VerifyBusBalance
