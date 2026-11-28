module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.KeccakGkr.KeccakOpen.FoldBase

/-!
# `keccak_open`'s fold: an entry's two blocks

An inner loop's load block (`stepL`): entry `j` of the two buffers, the challenge times their sum
by `EW::mul`. Its store block (`stepS`): the product plus the first buffer's entry into the rows.
-/

namespace NativeRustcVmArm.KeccakGkr.KeccakOpen

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVmArm.Arrays
open NativeRustcVmArm.Vm.KeccakOpen

@[expose] public section

/-- A load block's result: the challenge's limbs from `cx0`, `cx1` in X0, X1, the second buffer's
entry plus the first's in X2, X3, the first's in `lo0`, `lo1`, SP kept, nothing written. -/
def LSh (cx0 cx1 lo0 lo1 : XReg) (S0 SL : SState) : Bool :=
  SL.reg .X0 == some (.reg cx0) && SL.reg .X1 == some (.reg cx1) &&
    SL.reg .X2 == some (.bin .eor .W64 (.load 1 0 8) (.load 0 0 8)) &&
    SL.reg .X3 == some (.bin .eor .W64 (.load 1 8 8) (.load 0 8 8)) &&
    SL.reg lo0 == some (.load 0 0 8) && SL.reg lo1 == some (.load 0 8 8) &&
    calleeSaved lo0 && calleeSaved lo1 && SL.sp == S0.sp && SL.mem.isEmpty

end

public section

variable [NativeRustcArm.Host] {k : Nat} {c : Cx} {m0 : MachineData}

/-- **A load block and `EW::mul`.** -/
theorem stepL (hp : Placed code k) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (ok : Ok c.a m0) {bL : List Directive} {kL : Nat} (hin : bL.IsInfixAt code kL)
    (hne : bL ≠ []) {S0 SL : SState} (hx : exec bL S0 = some (SL, .call NativeRustcVmArm.Vm.EWMul.entryLabel))
    {cx0 cx1 lo0 lo1 : XReg} (hsh : LSh cx0 cx1 lo0 lo1 S0 SL = true)
    {j : Nat} (hj : j < 64) {fa fb : Nat → EW} {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + kL)) (hmid : Mid c m0 s.data)
    (hm : Match (Env.ofMachine s.data (bufR m0 j)) S0 s.data)
    (hA : ElemsAt s.data.dmem (fbA m0 + BitVec.ofNat 64 80) fa 64)
    (hB : ElemsAt s.data.dmem (fbA m0 + BitVec.ofNat 64 1104) fb 64) :
    Eventually (step1 Host.exe) (fun s2 ↦ s2.pc = Host.addrOf (k + kL + bL.length) ∧
      Mid c m0 s2.data ∧ SameOutside s.data.dmem s2.data.dmem (MulR m0) ∧
      (⟨s2.data.regs.X0, s2.data.regs.X1⟩ : EW) =
        ⟨s.data.regs.getXReg cx0, s.data.regs.getXReg cx1⟩ * (fb j + fa j) ∧
      s2.data.regs.getXReg lo0 = (fa j).c0 ∧ s2.data.regs.getXReg lo1 = (fa j).c1 ∧
      ∀ r v, calleeSaved r = true → SL.reg r = some v →
        (s2.data.regs.getXReg r).toBitVec = v.eval (Env.ofMachine s.data (bufR m0 j))) s := by
  have hn := ok.nums
  have hS := ok.stack
  have hwf := wf_buf ok hmid.body hj
  simp only [LSh, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hsh
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, hc0⟩, hc1⟩, h6⟩, h7⟩ := hsh
  refine exec_at (hin.trans hp.1 hne) hx hwf hpc hm fun s1 hm1 hpc1 ↦ ?_
  have hb1 : Body m0 s1.data :=
    hmid.body.of_block hm hm1 hwf rfl all_slots (by simp [keepsAll, h6, h7])
  have hd1 : s1.data.dmem = s.data.dmem := hm1.dmem_eq hwf h7
  have hmid1 := hmid.of_dmem hb1 hd1
  have ha : NativeRustcVm.EWAt s.data.dmem
      (fbA m0 + BitVec.ofNat 64 (80 + 16 * j) + BitVec.ofNat 64 0) (fa j) := by
    rw [NativeRustcVm.addr_add_zero, ← NativeRustcVm.addr_add_add]; exact hA j hj
  have hb : NativeRustcVm.EWAt s.data.dmem
      (fbA m0 + BitVec.ofNat 64 (1104 + 16 * j) + BitVec.ofNat 64 0) (fb j) := by
    rw [NativeRustcVm.addr_add_zero, ← NativeRustcVm.addr_add_add]; exact hB j hj
  obtain ⟨la0, la1⟩ := load_ew (env := Env.ofMachine s.data (bufR m0 j)) (r := 0) (o := 0) ha
  obtain ⟨lb0, lb1⟩ := load_ew (env := Env.ofMachine s.data (bufR m0 j)) (r := 1) (o := 0) hb
  have la1' : (Env.ofMachine s.data (bufR m0 j)).load 0 8 8 = (fa j).c1.toBitVec := la1
  have lb1' : (Env.ofMachine s.data (bufR m0 j)).load 1 8 8 = (fb j).c1.toBitVec := lb1
  have e0 : s1.data.regs.X0 = s.data.regs.getXReg cx0 :=
    UInt64.toBitVec_inj.mp (hm1.regs .X0 _ h0)
  have e1 : s1.data.regs.X1 = s.data.regs.getXReg cx1 :=
    UInt64.toBitVec_inj.mp (hm1.regs .X1 _ h1)
  have e2 : s1.data.regs.X2 = (fb j + fa j).c0 := by
    apply UInt64.toBitVec_inj.mp
    have := hm1.regs .X2 _ h2
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, lb0, la0] at this
    exact this
  have e3 : s1.data.regs.X3 = (fb j + fa j).c1 := by
    apply UInt64.toBitVec_inj.mp
    have := hm1.regs .X3 _ h3
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, lb1', la1'] at this
    exact this
  refine call_then hpc1 hmul (hb1.stackOk hS (by decide) (by decide)) fun s2 hpc2 hpost ↦ ?_
  obtain ⟨hp0, hp1, hsame, hsv⟩ := hpost
  have hb2 : Body m0 s2.data :=
    hb1.call hS (n := ewMulStack) (by decide) slots_le' ok.wsOff hsame (fun _ h ↦ Or.inl h) hsv
  have hmid2 : Mid c m0 s2.data :=
    hmid1.keep hn hb2 hsv.2.2 hsame fun q h ↦ mulR_safe hn (mulR_of hn hb1 h)
  refine .done _ ⟨hpc2, hmid2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hd1]
    exact NativeRustcVm.SameOutside.mono hsame fun q h ↦ mulR_of hn hb1 h
  · rw [hp0, hp1, e0, e1, e2, e3]
    rfl
  · rw [hsv.1 lo0 hc0]
    exact UInt64.toBitVec_inj.mp ((hm1.regs lo0 _ h4).trans la0)
  · rw [hsv.1 lo1 hc1]
    exact UInt64.toBitVec_inj.mp ((hm1.regs lo1 _ h5).trans la1')
  · intro r v hr hv
    rw [hsv.1 r hr]
    exact hm1.regs r v hv

/-- **A store block**: the product plus the first buffer's entry at `o + C` of the rows. -/
theorem stepS (hp : Placed code k) (ok : Ok c.a m0) {bS : List Directive} {kS : Nat}
    (hin : bS.IsInfixAt code kS) (hne : bS ≠ []) {S0 SS : SState} {x : Exit}
    (hx : exec bS S0 = some (SS, x)) {lo0 lo1 : XReg} {C : Nat}
    (hmem : SS.mem = [⟨0, C + 8, 8, .bin .eor .W64 (.reg .X1) (.reg lo1)⟩,
      ⟨0, C, 8, .bin .eor .W64 (.reg .X0) (.reg lo0)⟩]) (hsp : SS.sp = S0.sp)
    {o : Nat} (ho : o + C + 16 ≤ 65536) {s : MachineState}
    (hpc : s.pc = Host.addrOf (k + kS)) (hmid : Mid c m0 s.data)
    (hm : Match (Env.ofMachine s.data [(rwA m0 + BitVec.ofNat 64 o, C + 16)]) S0 s.data) :
    Eventually (step1 Host.exe) (fun s3 ↦
      Match (Env.ofMachine s.data [(rwA m0 + BitVec.ofNat 64 o, C + 16)]) SS s3.data ∧
      PcOk (Env.ofMachine s.data [(rwA m0 + BitVec.ofNat 64 o, C + 16)]) x
        (Host.addrOf (k + kS + bS.length)) s3 ∧ Mid c m0 s3.data ∧
      SameOutside s.data.dmem s3.data.dmem (fun q ↦ (rwA m0).toNat + (o + C) ≤ q.toNat ∧
        q.toNat < (rwA m0).toNat + (o + C) + 16) ∧
      NativeRustcVm.EWAt s3.data.dmem (rwA m0 + BitVec.ofNat 64 (o + C))
        ⟨s.data.regs.X0 ^^^ s.data.regs.getXReg lo0,
          s.data.regs.X1 ^^^ s.data.regs.getXReg lo1⟩) s := by
  have hn := ok.nums
  have hrW := hn.rW
  obtain ⟨hrm, hrw⟩ := rows_ok ok hmid.body (o := o) (n := C + 16) (by omega)
  have hwf := wf_one hrm hrw
  have eb : (rwA m0 + BitVec.ofNat 64 o).toNat = (rwA m0).toNat + o :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  refine exec_at (hin.trans hp.1 hne) hx hwf hpc hm fun s3 hm3 hpc3 ↦ ?_
  have hwr : ∀ q, Written (Env.ofMachine s.data [(rwA m0 + BitVec.ofNat 64 o, C + 16)]) SS q →
      (rwA m0).toNat + (o + C) ≤ q.toNat ∧ q.toNat < (rwA m0).toNat + (o + C) + 16 := by
    rintro q ⟨w, hw, b, sz, hb, h1, h2⟩
    rw [hmem] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;>
    · simp only [Env.ofMachine_regions, List.getElem?_cons_zero, Option.some.injEq,
        Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      dsimp only at h1 h2
      omega
  have hb3 : Body m0 s3.data :=
    hmid.body.write ok.stack (by decide) slots_le' ok.wsOff hm hm3 hwf rfl all_slots
      (by simp [keepsRegs, hsp]) fun q hq ↦ rows_inAny ok (by have := hwr q hq; omega)
  have hso : SameOutside s.data.dmem s3.data.dmem
      (Written (Env.ofMachine s.data [(rwA m0 + BitVec.ofNat 64 o, C + 16)]) SS) :=
    hm3.sameOutside hwf
  refine .done _ ⟨hm3, hpc3, hmid.keep hn hb3 (hm3.kept hwf) hso fun q hq ↦ ?_,
    NativeRustcVm.SameOutside.mono hso hwr, ?_⟩
  · have := hwr q hq
    unfold Safe
    omega
  · have h := KeccakGkr.Match.ewAt_write2 hm3 (pre := []) (ws := []) (r := 0) (o := C)
      (o' := C + 8) (v0 := .bin .eor .W64 (.reg .X0) (.reg lo0))
      (v1 := .bin .eor .W64 (.reg .X1) (.reg lo1)) (by rw [hmem]; rfl) rfl (fun _ h ↦ nomatch h)
      (b := rwA m0 + BitVec.ofNat 64 o) (sz := C + 16) rfl (Nat.le_refl _)
    rw [NativeRustcVm.addr_add_add] at h
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs] at h
    exact h

end

end NativeRustcVmArm.KeccakGkr.KeccakOpen
