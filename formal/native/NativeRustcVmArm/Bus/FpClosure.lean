module

public import NativeRustcVmArm.Code.Vm.Fingerprints.Names
public import NativeRustcVmArm.Code.Vm.VerifyBusBalanceClosure0.Names
public import NativeRustcVmArm.Bus.FpClosure.Exec
public import NativeRustcVmArm.Bus.Common

/-!
# `verify_bus_balance::{closure#0}`

`b0` reads its environment (the slices' addresses and lengths, the share's address), saves X30 in
its 64-byte frame, passes the share's limb 1 and its own arguments on the stack and calls
`fingerprints`; `b1` returns (`fpClosure_spec`).
-/

namespace NativeRustcVmArm.Bus.FpClosure

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalanceClosure0
open NativeVm.Model NativeRustcVmArm.Ring
open NativeRustcVmArm.Layout (infix_of)
open NativeRustcVm (ewsOf wordOf ewOf)

public section

/-- The frame's saved register. -/
abbrev slots : List (Nat × XReg) := [(48, .X30)]

/-- The callee-saved registers it does not save. -/
abbrev keep : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]

theorem keep_callee : ∀ r ∈ keep, calleeSaved r = true := by decide

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 64 := by decide

variable [Host] {k : Nat}

theorem hb0 (hp : Placed code k) :
    b0a.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyBusBalanceClosure0.b0Offset) ∧ b0b.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.VerifyBusBalanceClosure0.b0Offset + 6) := by
  have h := infix_of b0_in_code (by simp [b0]) hp
  rw [← List.take_append_drop 6 b0] at h
  exact h.append

/-- **The closure's contract.** -/
theorem fpClosure_spec (hp : Placed code k)
    (hfp : Spec (Labels.label NativeRustcVmArm.Vm.Fingerprints.entryLabel) FingerprintsPre FingerprintsPost) :
    Spec (Labels.label NativeRustcVmArm.Vm.VerifyBusBalanceClosure0.entryLabel) FpClosurePre FpClosurePost := by
  rintro m0 ⟨hS, hER, hES, hW, hM, hML, hBL, hSh, hOR, hOS⟩
  have hN : fpClosureStack ≤ m0.regs.SP.toNat := hS.2.1
  have hle : 64 + fingerprintsStack ≤ fpClosureStack := Nat.le_refl _
  have hF : 64 ≤ fpClosureStack := by omega
  obtain ⟨hb0a, hb0b⟩ := hb0 hp
  -- `b0a`: the environment's words.
  have hwf0 : (Env.ofMachine m0 [(base m0 64, 64), (m0.regs.X1.toBitVec, 56)]).WF :=
    Bus.wf_frame2 hS hF (fun _ h ↦ h) hER hES
  have hm0 : Match (Env.ofMachine m0 [(base m0 64, 64), (m0.regs.X1.toBitVec, 56)]) s0 m0 :=
    match_ofMachine (sregions := [(64, true), (56, false)])
      (regions := [(base m0 64, 64), (m0.regs.X1.toBitVec, 56)])
      ⟨rfl, fun _ ↦ Bus.base_aligned hS hF rfl, rfl, nofun, trivial⟩
      (by simp only [Sym.eval, Env.base_ofMachine_eq, List.getElem?_cons_zero, Option.map_some,
            Option.getD_some]
          rw [show BitVec.ofInt 64 64 = BitVec.ofNat 64 64 from rfl]; exact base_add_eq.symm)
      ⟨by simp [Sym.eval]; rfl, trivial⟩ trivial trivial trivial
  rw [show Labels.label NativeRustcVmArm.Vm.VerifyBusBalanceClosure0.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.VerifyBusBalanceClosure0.b0Offset) from hp.label (j := NativeRustcVmArm.Vm.VerifyBusBalanceClosure0.entryOffset) NativeRustcVmArm.Vm.VerifyBusBalanceClosure0.entry_at]
  refine exec_then hb0a run_b0a hwf0 hm0 fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = m0.dmem := hm1.dmem_eq hwf0 rfl
  have LE : ∀ i, (Sym.load 1 (8 * i) 8).eval
      (Env.ofMachine m0 [(base m0 64, 64), (m0.regs.X1.toBitVec, 56)]) = (envWord m0 i).toBitVec :=
    fun i ↦ Bus.load_r1 m0 _ _ 64 56 (8 * i)
  have e1x8 : st1.data.regs.getXReg .X8 = envWord m0 0 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X8 _ rfl).trans (LE 0))
  have e1x9 : st1.data.regs.getXReg .X9 = envWord m0 1 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X9 _ rfl).trans (LE 1))
  have e1x10 : st1.data.regs.getXReg .X10 = envWord m0 2 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X10 _ rfl).trans (LE 2))
  have e1x11 : st1.data.regs.getXReg .X11 = envWord m0 3 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X11 _ rfl).trans (LE 3))
  have e1x12 : st1.data.regs.getXReg .X12 = envWord m0 4 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X12 _ rfl).trans (LE 4))
  have e1x13 : st1.data.regs.getXReg .X13 = envWord m0 5 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X13 _ rfl).trans (LE 5))
  have e1x14 : st1.data.regs.getXReg .X14 = envWord m0 6 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X14 _ rfl).trans (LE 6))
  have K1 : Bus.KeepRegs ([.X0, .X2, .X3, .X4, .X5, .X6, .X30] ++ keep) m0 st1.data :=
    Bus.KeepRegs.of_block hm1 rfl
  have hsp1 : st1.data.regs.SP.toBitVec = base m0 64 := by rw [hm1.sp]; simp [Sym.eval]
  -- `b0b`: the share's words, the stack arguments, the call.
  have hwf1 : (Env.ofMachine st1.data [(base m0 64, 64), ((envWord m0 6).toBitVec, 16)]).WF :=
    Bus.wf_frame2 hS hF (by rw [hd1]; exact fun _ h ↦ h) hSh.1 hSh.2
  have hm1' := Bus.match_frame2 (m := st1.data) (r := .X14) (n := 16) hS hF rfl hsp1
  rw [e1x14] at hm1'
  refine exec_at hb0b run_b0b hwf1 hpc1 hm1' fun st2 hm2 hpc2 ↦ ?_
  have K2 : Bus.KeepRegs ([.X0] ++ keep) st1.data st2.data := Bus.KeepRegs.of_block hm2 rfl
  have hfr2 : Fr m0 64 fpClosureStack slots keep (fun _ ↦ False) st2.data := {
    sp := by rw [hm2.sp]; simp [Sym.eval]
    keep := fun r hr ↦ (K2 r (by simp [hr])).trans (K1 r (by simp [hr]))
    slots := fun p hp ↦ by
      simp only [List.mem_singleton] at hp
      subst hp
      have h := Bus.wordAt_write hm2 (r := 0) (o := 48) rfl (by omega) (v := .reg .X30)
        (by decide)
      simp only [Sym.eval, Env.ofMachine_regs, K1 .X30 (by simp)] at h
      exact h
    same := fun q hq ↦ by
      rw [hm2.get?_mem0 hwf1 fun hW ↦ hq (.inl (Bus.frame_inRange hN hF
        (Bus.Written.inRange (r := 0) rfl (Bus.frame_mapped hS hF).2 (by decide) hW))),
        Env.ofMachine_mem0, hd1]
    kept := fun p hp ↦ hm2.kept hwf1 p (by rw [Env.ofMachine_mem0, hd1]; exact hp) }
  have e2x0 : st2.data.regs.X0 = m0.regs.X0 :=
    (UInt64.toBitVec_inj.mp (hm2.regs .X0 _ rfl)).trans (K1 .X0 (by simp))
  have e2x1 : st2.data.regs.X1 = envWord m0 0 :=
    (UInt64.toBitVec_inj.mp (hm2.regs .X1 _ rfl)).trans e1x8
  have e2x2 : st2.data.regs.X2 = envWord m0 1 :=
    (UInt64.toBitVec_inj.mp (hm2.regs .X2 _ rfl)).trans e1x9
  have e2x3 : st2.data.regs.X3 = envWord m0 2 :=
    (UInt64.toBitVec_inj.mp (hm2.regs .X3 _ rfl)).trans e1x10
  have e2x4 : st2.data.regs.X4 = envWord m0 3 :=
    (UInt64.toBitVec_inj.mp (hm2.regs .X4 _ rfl)).trans e1x11
  have e2x5 : st2.data.regs.X5 = envWord m0 4 :=
    (UInt64.toBitVec_inj.mp (hm2.regs .X5 _ rfl)).trans e1x12
  have e2x6 : st2.data.regs.X6 = envWord m0 5 :=
    (UInt64.toBitVec_inj.mp (hm2.regs .X6 _ rfl)).trans e1x13
  have L1 := Bus.load_r1 st1.data (base m0 64) (envWord m0 6).toBitVec 64 16
  rw [hd1] at L1
  have e2x7 : st2.data.regs.X7 = wordOf m0.dmem ((envWord m0 6).toBitVec + BitVec.ofNat 64 0) :=
    UInt64.toBitVec_inj.mp ((hm2.regs .X7 _ rfl).trans (L1 0))
  -- The stack arguments.
  have hsa : ∀ (o : Nat) (v : Sym), o + 8 ≤ 64 →
      (∀ i < 8, findWrite 0 (o + i) (after b0b s1).mem = some (v, i)) →
      stackArg st2.data o = UInt64.ofBitVec (v.eval
        (Env.ofMachine st1.data [(base m0 64, 64), ((envWord m0 6).toBitVec, 16)])) := by
    intro o v ho hw
    unfold stackArg
    rw [hfr2.sp]
    exact NativeRustcVm.wordOf_of_wordAt
      (Bus.wordAt_write hm2 (r := 0) (o := o) rfl ho (by rw [← Bus.after_eq run_b0b]; exact hw))
  have hs0 : stackArg st2.data 0 =
      wordOf m0.dmem ((envWord m0 6).toBitVec + BitVec.ofNat 64 8) := by
    rw [hsa 0 (.load 1 8 8) (by omega) (by decide)]
    exact UInt64.toBitVec_inj.mp (L1 8)
  have hs8 : stackArg st2.data 8 = m0.regs.X2 := by
    rw [hsa 8 (.reg .X2) (by omega) (by decide)]
    exact K1 .X2 (by simp)
  have hs16 : stackArg st2.data 16 = m0.regs.X3 := by
    rw [hsa 16 (.reg .X3) (by omega) (by decide)]
    exact K1 .X3 (by simp)
  have hs24 : stackArg st2.data 24 = m0.regs.X4 := by
    rw [hsa 24 (.reg .X4) (by omega) (by decide)]
    exact K1 .X4 (by simp)
  have hs32 : stackArg st2.data 32 = m0.regs.X5 := by
    rw [hsa 32 (.reg .X5) (by omega) (by decide)]
    exact K1 .X5 (by simp)
  have hs40 : stackArg st2.data 40 = m0.regs.X6 := by
    rw [hsa 40 (.reg .X6) (by omega) (by decide)]
    exact K1 .X6 (by simp)
  have hshare : (⟨st2.data.regs.X7, stackArg st2.data 0⟩ : EW) =
      ewOf m0.dmem (envWord m0 6).toBitVec := by
    rw [e2x7, hs0]
    simp [ewOf]
  -- The inputs, as at the entry.
  have hw : ewsOf st2.data.dmem (envWord m0 0).toBitVec 5 = ewsOf m0.dmem (envWord m0 0).toBitVec 5 :=
    Bus.Fr.ewsOf_eq hfr2 hS hW.1.2 hW.2 fun _ _ h ↦ h
  have hmem : ewsOf st2.data.dmem (envWord m0 1).toBitVec 2 =
      ewsOf m0.dmem (envWord m0 1).toBitVec 2 :=
    Bus.Fr.ewsOf_eq hfr2 hS hM.1.2 hM.2 fun _ _ h ↦ h
  have hml : slice st2.data (envWord m0 2) (envWord m0 3) = slice m0 (envWord m0 2) (envWord m0 3) :=
    Bus.Fr.slice_eq hfr2 hS hML fun _ _ h ↦ h
  have hbl : slice st2.data (envWord m0 4) (envWord m0 5) = slice m0 (envWord m0 4) (envWord m0 5) :=
    Bus.Fr.slice_eq hfr2 hS hBL fun _ _ h ↦ h
  have hpre : FingerprintsPre st2.data ∧ st2.data.regs.X0 = m0.regs.X0 := by
    refine ⟨⟨hfr2.stackOk hS rfl hle, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, e2x0⟩
    · rw [e2x1]; exact ⟨Bus.Fr.readable hfr2 hW.1, Bus.Fr.offStack hfr2 hS hW.2 hle⟩
    · rw [e2x2]; exact ⟨Bus.Fr.readable hfr2 hM.1, Bus.Fr.offStack hfr2 hS hM.2 hle⟩
    · rw [e2x3, e2x4]; exact ⟨Bus.Fr.readable hfr2 hML.1, Bus.Fr.offStack hfr2 hS hML.2 hle⟩
    · rw [e2x5, e2x6]; exact ⟨Bus.Fr.readable hfr2 hBL.1, Bus.Fr.offStack hfr2 hS hBL.2 hle⟩
    · have := (Bus.local_ok (o := 0) (n := 48) hS hle (by omega) hfr2.kept hfr2.sp).1
      rw [hfr2.sp]
      simpa using this
    · rw [e2x0]; exact Bus.Fr.readable hfr2 hOR
    · rw [e2x0]; exact Bus.Fr.offStack hfr2 hS hOS hle
  have hout : ∀ q, InRange m0.regs.X0.toBitVec 48 q → ¬InRange (base m0 64) 64 q := by
    intro q hq hq'
    have hA := apart_frame hN hF hOS
    rw [Sym.inRange_iff hOR.2] at hq
    rw [Sym.inRange_iff (Bus.frame_mapped hS hF).2] at hq'
    unfold Apart at hA
    omega
  refine Fr.leaf (Bus.Fr.mono hfr2 (outs' := fun q ↦ InRange m0.regs.X0.toBitVec 48 q) fun _ h ↦ h.elim)
    hN hle keep_callee slots_le hout (Bus.Spec.withFact hfp fun m ↦ m.regs.X0 = m0.regs.X0)
    (fun m m' h ↦ ⟨NativeRustcVm.SameOutside.mono h.1.2.1 fun q hq ↦ hq.elim
      (fun h' ↦ .inr (by rw [← h.2]; exact h')) .inl, h.1.2.2⟩) hpc2 hpre
    fun m3 hfr3 hq3 hcs3 ↦ ?_
  -- `b1`: the epilogue.
  have hwf3 := Bus.wf_frame (F := 64) hS hF hfr3.kept
  have hm3 := Bus.match_frame (m := m3) hS hF rfl hfr3.sp
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) run_b1 hwf3 rfl hm3
    fun st4 hm4 hpc4 ↦ ?_
  obtain ⟨hret, hsaved⟩ := hfr3.exit hm4 hwf3 (by decide)
  have hd4 : st4.data.dmem = m3.dmem := hm4.dmem_eq hwf3 rfl
  refine .done _ ⟨by simp only [PcOk] at hpc4; rw [hpc4, hret], ?_, ?_, hsaved⟩
  · have hq := hq3.1.1
    simp only [e2x0, e2x1, e2x2, e2x3, e2x4, e2x5, e2x6, hw, hmem, hml, hbl, hshare, hs8, hs16,
      hs24, hs32, hs40] at hq
    rw [hd4]
    exact hq
  · intro p hp
    rw [hd4]
    exact Bus.Fr.changes hfr3 (fun _ h ↦ h) p hp

end

end NativeRustcVmArm.Bus.FpClosure
