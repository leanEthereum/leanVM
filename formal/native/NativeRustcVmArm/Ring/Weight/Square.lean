module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Ring.Weight.Step

/-!
# `ring_weight`: the powers squared

After each coefficient's product the powers are squared in place, one per turn of a two-block
loop: a block loading the power at register `p` and calling `EW::mul` (`b17`, `b23`), one
storing the square and stepping `p` (`b18`, `b24`); both checked by `decide` on their literal
results (`sqA`, `sqB`). `SqI`: the first `j` powers squared, the callee-saved registers but `p`
as at the loop's start (`ref`); `sqLoop`: all squared (`SqDone`).
-/

namespace NativeRustcVmArm.Ring.Weight

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Arrays (calleeRegs mem_calleeRegs)

@[expose] public section

/-- The loading block: no write, SP kept, the power in X0, X1 and X2, X3, the callee-saved
registers kept. -/
def sqA (p : XReg) (S : SState) : Bool :=
  S.mem.isEmpty && S.sp == .sp && S.reg .X0 == some (.load 0 0 8) &&
    S.reg .X1 == some (.load 0 8 8) && S.reg .X2 == some (.load 0 0 8) &&
    S.reg .X3 == some (.load 0 8 8) &&
    calleeRegs.all fun r ↦ ((sqS p).reg r).isSome && S.reg r == (sqS p).reg r

/-- The storing block: X0, X1 stored at the power, nothing else written, SP kept, `p` the next
power, the other callee-saved registers kept. -/
def sqB (p : XReg) (S : SState) : Bool :=
  (List.range 8).all (fun i ↦ findWrite 0 (0 + i) S.mem == some (.reg .X0, i) &&
      findWrite 0 (8 + i) S.mem == some (.reg .X1, i)) &&
    S.mem.all (fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 16)) && S.sp == .sp &&
    S.reg p == some (.ptr 0 16) &&
    calleeRegs.all fun r ↦ r == p || (((sqS p).reg r).isSome && S.reg r == (sqS p).reg r)

/-- **The squares' loop, turn `j`**: powers `l < j` squared, the others `P`'s; `p` at power `j`;
the callee-saved registers but `p` as in `ref`. -/
structure SqI (m0 : MachineData) (p : XReg) (P : Array EW) (ref : MachineData) (j : Nat)
    (m : MachineData) : Prop where
  fr : WFr m0 m
  lt : j < nR m0
  ptr : (m.regs.getXReg p).toBitVec = slotA m0 j
  regs : ∀ r ∈ calleeRegs, r ≠ p → m.regs.getXReg r = ref.regs.getXReg r
  done : ∀ l < j, NativeRustcVm.EWAt m.dmem (slotA m0 l) (P.getD l 0 * P.getD l 0)
  todo : ∀ l, j ≤ l → l < nR m0 → NativeRustcVm.EWAt m.dmem (slotA m0 l) (P.getD l 0)

/-- **The powers squared.** -/
structure SqDone (m0 : MachineData) (p : XReg) (P : Array EW) (ref : MachineData)
    (m : MachineData) : Prop where
  fr : WFr m0 m
  regs : ∀ r ∈ calleeRegs, r ≠ p → m.regs.getXReg r = ref.regs.getXReg r
  sq : ∀ l < nR m0, NativeRustcVm.EWAt m.dmem (slotA m0 l) (P.getD l 0 * P.getD l 0)

end

public section

variable {m0 : MachineData}

theorem calleeRegs_cs : ∀ r ∈ calleeRegs, calleeSaved r = true := by decide

theorem slotA_toNat (h : RingWeightPre m0) {j : Nat} (hj : j ≤ 36) :
    (slotA m0 j).toNat = m0.regs.SP.toNat - 688 + 16 + 16 * j := by
  rw [frame_toNat h (by omega)]
  omega

theorem slot_win (h : RingWeightPre m0) {m : MachineData} (hfr : WFr m0 m) {j : Nat}
    (hj : j < nR m0) : (Env.ofMachine m [(slotA m0 j, 16)]).WF :=
  win_wf1 (frame_win h hfr (by have := n36 h; omega) (by decide))

theorem slot_apart (h : RingWeightPre m0) {j l : Nat} (hj : j < 36) (hl : l < 36) (hjl : l ≠ j) :
    (slotA m0 l).toNat + 16 ≤ (slotA m0 j).toNat ∨ (slotA m0 j).toNat + 16 ≤ (slotA m0 l).toNat := by
  rw [slotA_toNat h (by omega), slotA_toNat h (by omega)]
  omega

theorem slot_nw (h : RingWeightPre m0) {l : Nat} (hl : l < 36) : (slotA m0 l).toNat + 16 ≤ 2 ^ 64 := by
  rw [slotA_toNat h (by omega)]
  have := m0.regs.SP.toNat_lt
  omega

theorem slot_next {j : Nat} : slotA m0 j + BitVec.ofInt 64 16 = slotA m0 (j + 1) := by
  rw [show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, addr_eq (z := 16 + 16 * (j + 1)) (by omega)]

theorem slot_eq_iff (h : RingWeightPre m0) {j n : Nat} (hj : j ≤ 36) (hn : n ≤ 36) :
    slotA m0 j = slotA m0 n ↔ j = n := by
  constructor
  · intro e
    have := congrArg BitVec.toNat e
    rw [slotA_toNat h hj, slotA_toNat h hn] at this
    have := hN h
    rw [stack_eq] at this
    omega
  · rintro rfl; rfl

section
variable [Labels]

theorem reg_keep {env : Env} {S0 S : SState} {m m' : MachineData} (hm0 : Match env S0 m)
    (hm : Match env S m') {r : XReg} (h : (S0.reg r).isSome = true ∧ S.reg r = S0.reg r) :
    m'.regs.getXReg r = m.regs.getXReg r := by
  obtain ⟨hs, he⟩ := h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  exact Match.reg_eq hm0 hm hv (he.trans hv)

theorem sqS_match {m : MachineData} {p : XReg} {j : Nat}
    (hp : (m.regs.getXReg p).toBitVec = slotA m0 j) :
    Match (Env.ofMachine m [(slotA m0 j, 16)]) (sqS p) m :=
  match_ofMachine ⟨rfl, nofun, trivial⟩ rfl
    ⟨by
      show _ = slotA m0 j + BitVec.ofInt 64 (0 : Nat)
      rw [ofInt_lit, NativeRustcVm.addr_add_zero, hp], trivial⟩
    trivial trivial trivial

end

variable [Host]

/-- **A turn of the squares' loop.** -/
theorem sqTurn (h : RingWeightPre m0) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {p : XReg} (hpc : calleeSaved p = true) {P : Array EW} {ref : MachineData}
    (href : (ref.regs.getXReg .X22).toBitVec = slotA m0 (nR m0)) (hp22 : p ≠ .X22)
    {iA iB : Nat} {dA dB : List Directive} {SA SB : SState} {L : Label}
    (hkA : dA.IsInfixAt Host.prog iA) (hrA : exec dA (sqS p) = some (SA, .call NativeRustcVmArm.Vm.EWMul.entryLabel))
    (hA : sqA p SA = true) (hiB : iA + dA.length = iB) (hkB : dB.IsInfixAt Host.prog iB)
    (hrB : exec dB (sqS p) = some (SB, .cond (.not (.cmp .eq .W64 (.ptr 0 16) (.reg .X22))) L))
    (hB : sqB p SB = true) (hL : Labels.label L = Host.addrOf iA) {j : Nat} {m : MachineData}
    (hI : SqI m0 p P ref j m) :
    Eventually (step1 Host.exe) (fun st ↦ (st.pc = Host.addrOf iA ∧ ∃ j', SqI m0 p P ref j' st.data ∧
        nR m0 - j' < nR m0 - j) ∨
      (st.pc = Host.addrOf (iB + dB.length) ∧ SqDone m0 p P ref st.data)) ⟨m, Host.addrOf iA⟩ := by
  have hn := n36 h
  have hj := hI.lt
  have hpr : p ∈ calleeRegs := mem_calleeRegs hpc
  simp only [sqA, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, List.all_eq_true] at hA
  obtain ⟨⟨⟨⟨⟨⟨hAm, hAsp⟩, hA0⟩, hA1⟩, hA2⟩, hA3⟩, hAc⟩ := hA
  simp only [sqB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at hB
  obtain ⟨⟨⟨⟨hBw, hBm⟩, hBsp⟩, hBp⟩, hBc⟩ := hB
  have hwf := slot_win h hI.fr hj
  have hm := sqS_match hI.ptr
  have hx : NativeRustcVm.ewOf m.dmem (slotA m0 j) = P.getD j 0 :=
    NativeRustcVm.ewOf_of_ewAt (hI.todo j (le_refl _) hj)
  refine mulStep h hmul hkA hrA hI.fr hm hwf hAm hAsp fun st m2 hm1 hfr1 hfr2 hq hcs ↦ ?_
  rw [hiB]
  have hd1 : st.dmem = m.dmem := hm1.dmem_eq hwf hAm
  have e0 : st.regs.getXReg .X0 = (P.getD j 0).c0 := reg_of hm1 hA0 (by
    rw [load_c0 rfl 0, NativeRustcVm.addr_add_zero, hx])
  have e1 : st.regs.getXReg .X1 = (P.getD j 0).c1 := reg_of hm1 hA1 (by
    rw [show (8 : Nat) = 0 + 8 from rfl, load_c1 rfl 0, NativeRustcVm.addr_add_zero, hx])
  have e2 : st.regs.getXReg .X2 = (P.getD j 0).c0 := reg_of hm1 hA2 (by
    rw [load_c0 rfl 0, NativeRustcVm.addr_add_zero, hx])
  have e3 : st.regs.getXReg .X3 = (P.getD j 0).c1 := reg_of hm1 hA3 (by
    rw [show (8 : Nat) = 0 + 8 from rfl, load_c1 rfl 0, NativeRustcVm.addr_add_zero, hx])
  have hsq : (⟨m2.regs.X0, m2.regs.X1⟩ : EW) = P.getD j 0 * P.getD j 0 := by
    rw [hq.1, hq.2.1]
    show EW.mul ⟨st.regs.getXReg .X0, st.regs.getXReg .X1⟩ ⟨st.regs.getXReg .X2, st.regs.getXReg .X3⟩ = _
    rw [e0, e1, e2, e3]
    rfl
  have hreg2 : ∀ r ∈ calleeRegs, m2.regs.getXReg r = m.regs.getXReg r := fun r hr ↦ by
    rw [hcs r (calleeRegs_cs r hr)]
    exact reg_keep hm hm1 (hAc r hr)
  have hm2 := sqS_match (m := m2) (p := p) (j := j) (by rw [hreg2 p hpr]; exact hI.ptr)
  have hwf2 := slot_win h hfr2 hj
  refine exec_then hkB hrB hwf2 hm2 fun st3 hm3 hpc3 ↦ ?_
  have hW : ∀ w ∈ SB.mem, w.r = 0 ∧ w.off + w.n ≤ 16 := fun w hw ↦ by
    have := hBm w hw
    simp only [decide_eq_true_eq] at this
    exact this
  have hfr3 : WFr m0 st3.data :=
    frWin h hfr2 hm2 hm3 hwf2 hBsp (r := 0) rfl (by omega) (by omega) hW
  have hreg3 : ∀ r ∈ calleeRegs, r ≠ p → st3.data.regs.getXReg r = ref.regs.getXReg r := by
    intro r hr hrp
    have := hBc r hr
    rcases this with hrp' | hk
    · exact absurd (XReg.eq_of_beq hrp') hrp
    · rw [reg_keep hm2 hm3 hk, hreg2 r hr]
      exact hI.regs r hr hrp
  have hj' : NativeRustcVm.EWAt st3.data.dmem (slotA m0 j) (P.getD j 0 * P.getD j 0) := by
    have := ew_write hm3 (r := 0) (o := 0) (b := slotA m0 j) (sz := 16) rfl (by omega)
      (v0 := .reg .X0) (v1 := .reg .X1) (fun i hi ↦ (hBw i hi).1) (fun i hi ↦ (hBw i hi).2)
    simp only [Sym.eval, Env.ofMachine_regs, UInt64.ofBitVec_toBitVec,
      NativeRustcVm.addr_add_zero] at this
    rw [← hsq]
    exact this
  have keep : ∀ l, l < nR m0 → l ≠ j → ∀ x, NativeRustcVm.EWAt m.dmem (slotA m0 l) x →
      NativeRustcVm.EWAt st3.data.dmem (slotA m0 l) x := fun l hl hlj x hx ↦ by
    have hx2 := ew_call h hfr1 hq (o := 16 + 16 * l) (by omega) (by rw [hd1]; exact hx)
    exact ew_keep hm3 hwf2 (r := 0) rfl hW hx2 (slot_nw h (by omega))
      (slot_apart h (by omega) (by omega) hlj)
  have hptr3 : (st3.data.regs.getXReg p).toBitVec = slotA m0 (j + 1) := by
    rw [reg_bv hm3 hBp rfl]
    exact slot_next
  simp only [PcOk] at hpc3
  have hc := NativeRustcVmArm.Arrays.pc_cond hpc3
  have h22 : (m2.regs.getXReg .X22).toBitVec = slotA m0 (nR m0) := by
    rw [hreg2 .X22 (by simp [calleeRegs]), hI.regs .X22 (by simp [calleeRegs]) (Ne.symm hp22)]
    exact href
  have he : (SBool.not (SBool.cmp .eq .W64 (.ptr 0 16) (.reg .X22))).eval
      (Env.ofMachine m2 [(slotA m0 j, 16)]) = true ↔ j + 1 ≠ nR m0 := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Env.ofMachine_regs, Sym.low_W64,
      Bool.not_eq_true', Bool.eq_false_iff, ne_eq, beq_iff_eq]
    rw [show (Env.ofMachine m2 [(slotA m0 j, 16)]).base 0 = slotA m0 j from rfl, slot_next, h22,
      slot_eq_iff h (by omega) (by omega)]
  by_cases hlast : j + 1 = nR m0
  · refine .done _ (.inr ⟨hc.2 (fun e ↦ he.mp e hlast), hfr3, hreg3, fun l hl ↦ ?_⟩)
    by_cases hlj : l = j
    · subst hlj; exact hj'
    · exact keep l hl hlj _ (hI.done l (by omega))
  · refine .done _ (.inl ⟨(hc.1 (he.mpr hlast)).trans hL, j + 1, ⟨hfr3, by omega, hptr3, hreg3,
      fun l hl ↦ ?_, fun l hl1 hl2 ↦ keep l hl2 (by omega) _ (hI.todo l (by omega) hl2)⟩, by omega⟩)
    by_cases hlj : l = j
    · subst hlj; exact hj'
    · exact keep l (by omega) hlj _ (hI.done l (by omega))

/-- **The squares' loop.** -/
theorem sqLoop (h : RingWeightPre m0) (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {p : XReg} (hpc : calleeSaved p = true) {P : Array EW} {ref : MachineData}
    (href : (ref.regs.getXReg .X22).toBitVec = slotA m0 (nR m0)) (hp22 : p ≠ .X22)
    {iA iB : Nat} {dA dB : List Directive} {SA SB : SState} {L : Label}
    (hkA : dA.IsInfixAt Host.prog iA) (hrA : exec dA (sqS p) = some (SA, .call NativeRustcVmArm.Vm.EWMul.entryLabel))
    (hA : sqA p SA = true) (hiB : iA + dA.length = iB) (hkB : dB.IsInfixAt Host.prog iB)
    (hrB : exec dB (sqS p) = some (SB, .cond (.not (.cmp .eq .W64 (.ptr 0 16) (.reg .X22))) L))
    (hB : sqB p SB = true) (hL : Labels.label L = Host.addrOf iA) {m : MachineData}
    (hI : SqI m0 p P ref 0 m) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (iB + dB.length) ∧
      SqDone m0 p P ref st.data) ⟨m, Host.addrOf iA⟩ :=
  Sym.loop (I := fun n st ↦ st.pc = Host.addrOf iA ∧ ∃ j, n = nR m0 - j ∧ SqI m0 p P ref j st.data)
    (fun _ _ ⟨hpc', _, hn, hI⟩ ↦ at_pc hpc' ((sqTurn h hmul hpc href hp22 hkA hrA hA hiB hkB hrB
      hB hL hI).mono fun _ h' ↦ h'.elim (fun ⟨hp', j', hI', hlt⟩ ↦ .inr ⟨_, hn ▸ hlt, hp', j',
        rfl, hI'⟩) .inl))
    ⟨rfl, 0, rfl, hI⟩

end

end NativeRustcVmArm.Ring.Weight
