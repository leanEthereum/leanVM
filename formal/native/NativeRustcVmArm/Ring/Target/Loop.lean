module

public import NativeRustcVmArm.Code.Vm.RingPsi.Names
public import NativeRustcVmArm.Code.Vm.RingTarget.Names
public import NativeRustcVmArm.Ring.Target.Ends

/-!
# `ring_target`: the prologue and the images loop

The prologue (`b0`) saves the registers and starts the loop: `s` in X20, `f` in X21, `g` in X19,
the counter `16 i` in X22, the images' buffer (frame byte `1232`) in X23 (`Inv`). Each turn
(`b1`, `b2`) computes `Ψ(s_i)` (`ring_psi`) and stores it at the buffer's element `i`.
-/

namespace NativeRustcVmArm.Ring.Target

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingTarget

@[expose] public section

/-- **At the loop's head**, turn `i`: the first `i` images in the buffer. -/
structure Inv (m0 : MachineData) (i : Nat) (m : MachineData) : Prop where
  fr : TFr m0 m
  x19 : m.regs.getXReg .X19 = m0.regs.X2
  x20 : m.regs.getXReg .X20 = m0.regs.X0
  x21 : m.regs.getXReg .X21 = m0.regs.X1
  x22 : (m.regs.getXReg .X22).toBitVec = BitVec.ofNat 64 (16 * i)
  x23 : (m.regs.getXReg .X23).toBitVec = fb m0 + BitVec.ofNat 64 1232
  le : i ≤ 64
  img : NativeRustcVm.EWsAt m.dmem (fb m0 + BitVec.ofNat 64 1232) ((imgs m0).toList.take i)

/-- `b2`'s writes: the element's two words. -/
def storeOk (S : SState) : Bool :=
  S.mem.all (fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 16)) &&
    (List.range 8).all (fun j ↦ findWrite 0 (0 + j) S.mem == some (.reg .X0, j) &&
      findWrite 0 (8 + j) S.mem == some (.reg .X1, j)) &&
    S.reg .X19 == some (.reg .X19) && S.reg .X20 == some (.reg .X20) &&
    S.reg .X21 == some (.reg .X21) && S.reg .X23 == some (.reg .X23) &&
    S.reg .X22 == some (.bin .add .W64 (.reg .X22) (.lit 16)) && S.sp == .sp

/-- `b2`'s exit: back to the head unless the counter reached `1024`. -/
def storeExit : Exit :=
  .cond (.not (.cmp .eq .W64 (.bin .add .W64 (.reg .X22) (.lit 16)) (.lit 1024))) NativeRustcVmArm.Vm.RingTarget.label_1

end

public section

variable {m0 : MachineData}

theorem imgs_length : (imgs m0).toList.length = 64 := by simp [imgs, sl, arr, coeffCount]

theorem imgs_getElem {i : Nat} (hi : i < (imgs m0).toList.length) :
    (imgs m0).toList[i] =
      ringPsi (NativeRustcVm.ewOf m0.dmem (sA m0 + BitVec.ofNat 64 (16 * i))) (gl m0) := by
  simp [imgs, sl, arr, sA]

/-- Bytes apart from the stack are the entry's in every state of the frame. -/
theorem P.same (h : P m0) {m : MachineData} (hfr : TFr m0 m) {a : BitVec 64} {n : Nat}
    (ha : Apart a n (stackBelow m0 ringTargetStack) ringTargetStack) (hw : NoWrap a n) {j : Nat}
    (hj : j < n) : m.dmem.get? (a + BitVec.ofNat 64 j) = m0.dmem.get? (a + BitVec.ofNat 64 j) :=
  hfr.same _ fun hq ↦ hq.elim (fun hq ↦ NativeRustcVm.Apart.not_inRange_add ha hw
    (base_noWrap h.hN) hj hq) id

theorem reg_of [Labels] {env : Env} {S : SState} {m : MachineData} (hm : Match env S m) {r : XReg}
    {v : Sym} (h : S.reg r = some v) {w : UInt64} (hv : v.eval env = w.toBitVec) :
    m.regs.getXReg r = w :=
  UInt64.toBitVec_inj.mp ((hm.regs r v h).trans hv)

variable [Host] {k : Nat}

/-- **The prologue** (`b0`). -/
theorem stepEntry (h : P m0) {i : Nat} (hk : b0.IsInfixAt Host.prog i) {R : MachineState → Prop}
    (cont : ∀ m1, Inv m0 0 m1 → Eventually (step1 Host.exe) R ⟨m1, Host.addrOf (i + b0.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf i⟩ := by
  have hwf : (Env.ofMachine m0 [(fb m0, 2352)]).WF :=
    Env.wf_of ⟨⟨frame_mapped h.st (by decide), h.fbw⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine m0 [(fb m0, 2352)]) entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned h.st (by decide) (by decide), trivial⟩
      (by
        show m0.regs.SP.toBitVec = fb m0 + BitVec.ofInt 64 (2352 : Nat)
        rw [BitVec.ofInt_natCast, base_add_eq])
      trivial trivial trivial trivial
  refine exec_then hk run_b0 hwf hm fun st hm1 hpc ↦ ?_
  simp only [PcOk] at hpc
  obtain ⟨d, pc⟩ := st
  simp only at hpc hm1
  subst hpc
  refine cont d {
    fr := Fr.ofPrologue (rs := []) h.hN (by decide) hm1 hwf rfl (by decide) slots_le (by decide)
      (fun _ h ↦ by cases h)
    x19 := reg_of hm1 rfl rfl
    x20 := reg_of hm1 rfl rfl
    x21 := reg_of hm1 rfl rfl
    x22 := by rw [hm1.regs .X22 _ rfl]; rfl
    x23 := by rw [hm1.regs .X23 _ rfl]; rfl
    le := by decide
    img := NativeRustcVm.ewsAt_nil _ _ }

/-- **The call of `ring_psi`** (`b1`): `Ψ(s_i)` in X0, X1. -/
theorem stepPsi (hp : Placed code k) (h : P m0)
    (hpsi : Spec (Labels.label NativeRustcVmArm.Vm.RingPsi.entryLabel) RingPsiPre RingPsiPost) {i : Nat} {m : MachineData}
    (hI : Inv m0 i m) (hi : i < 64) {R : MachineState → Prop}
    (cont : ∀ m2, Inv m0 i m2 → (⟨m2.regs.X0, m2.regs.X1⟩ : EW) =
        (imgs m0).toList[i]'(by rw [imgs_length]; exact hi) →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b2Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b1Offset)⟩ := by
  have hsw := h.sw
  unfold NoWrap at hsw
  have hsA : (sA m0 + BitVec.ofNat 64 (16 * i)).toNat = (sA m0).toNat + 16 * i :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have hwf : (Env.ofMachine m [(sA m0 + BitVec.ofNat 64 (16 * i), 16)]).WF :=
    Env.wf_of ⟨⟨fun j hj ↦ by
        rw [NativeRustcVm.addr_add_add]; exact hI.fr.kept _ (h.sm _ (by omega)),
      by unfold NoWrap; rw [hsA]; omega⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine m [(sA m0 + BitVec.ofNat 64 (16 * i), 16)]) psiS m :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl trivial trivial trivial
      ⟨by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
        rw [hI.x20, hI.x22]
        show _ = sA m0 + BitVec.ofNat 64 (16 * i) + BitVec.ofInt 64 0
        simp [sA], trivial⟩
  refine exec_then (hb b1_in_code (by simp [b1]) hp) run_b1 hwf hm fun st hm1 hpc ↦ ?_
  have hfr1 : TFr m0 st.data := hI.fr.ofBlock hm hm1 hwf rfl rfl rfl fun _ h ↦ by cases h
  have e2 : st.data.regs.X2 = m0.regs.X2 :=
    reg_of hm1 (r := .X2) (v := .reg .X19) rfl (by simp [Sym.eval, hI.x19])
  have hs0 : ∀ o, o + 8 ≤ 16 → NativeRustcVm.wordOf m.dmem (sA m0 + BitVec.ofNat 64 (16 * i + o)) =
      NativeRustcVm.wordOf m0.dmem (sA m0 + BitVec.ofNat 64 (16 * i + o)) := fun o ho ↦
    NativeRustcVm.wordOf_congr fun j hj ↦ by
      rw [NativeRustcVm.addr_add_add]
      exact P.same h hI.fr h.ss h.sw (by omega)
  have e0 : st.data.regs.X0 =
      (NativeRustcVm.ewOf m0.dmem (sA m0 + BitVec.ofNat 64 (16 * i))).c0 :=
    reg_of hm1 (r := .X0) (v := .load 0 0 8) rfl (by
      simp only [Sym.eval]
      rw [load_eq_wordOf]
      show _ = (NativeRustcVm.wordOf m0.dmem _).toBitVec
      rw [show (Env.ofMachine m [(sA m0 + BitVec.ofNat 64 (16 * i), 16)]).base 0 =
        sA m0 + BitVec.ofNat 64 (16 * i) from rfl, NativeRustcVm.addr_add_add, Nat.add_zero]
      exact congrArg UInt64.toBitVec (by simpa using hs0 0 (by omega)))
  have e1 : st.data.regs.X1 =
      (NativeRustcVm.ewOf m0.dmem (sA m0 + BitVec.ofNat 64 (16 * i))).c1 :=
    reg_of hm1 (r := .X1) (v := .load 0 8 8) rfl (by
      simp only [Sym.eval]
      rw [load_eq_wordOf]
      show _ = (NativeRustcVm.wordOf m0.dmem (_ + BitVec.ofNat 64 8)).toBitVec
      rw [show (Env.ofMachine m [(sA m0 + BitVec.ofNat 64 (16 * i), 16)]).base 0 =
        sA m0 + BitVec.ofNat 64 (16 * i) from rfl, NativeRustcVm.addr_add_add]
      exact congrArg UInt64.toBitVec (hs0 8 (by omega)))
  refine Fr.leaf hfr1 h.hN (N' := ringPsiStack) (by decide) (fun _ h ↦ by cases h) slots_le
    (fun _ h ↦ h.elim) hpsi
    (fun _ _ hq ↦ ⟨NativeRustcVm.SameOutside.mono hq.2.1 fun q hq ↦ hq.elim
      (fun h0 ↦ absurd h0 (by unfold InRange; omega)) .inl, hq.2.2⟩) hpc
    ⟨hfr1.stackOk h.st (by decide) (by decide), by
      rw [e2]
      exact ⟨⟨fun j hj ↦ hfr1.kept _ (h.gm j hj), h.gw⟩, hfr1.apart h.hN h.gs (by decide)⟩⟩
    fun m2 hfr2 hq hcs ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.RingTarget.b1Offset + b1.length = k + NativeRustcVmArm.Vm.RingTarget.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b1_next]]
  have hc : ∀ r, calleeSaved r = true → m2.regs.getXReg r = st.data.regs.getXReg r := hcs
  have hgl : arr st.data st.data.regs.X2 ringWidth = gl m0 := by
    rw [e2]
    unfold gl arr
    rw [NativeRustcVm.ewsOf_congr (a := m0.regs.X2.toBitVec) (n := ringWidth) fun j hj ↦
      P.same h hfr1 h.gs h.gw (by unfold ringWidth at hj; omega)]
  refine cont m2 {
    fr := hfr2
    x19 := (hc .X19 rfl).trans ((Match.reg_eq hm hm1 (v := .reg .X19) rfl rfl).trans hI.x19)
    x20 := (hc .X20 rfl).trans ((Match.reg_eq hm hm1 (v := .reg .X20) rfl rfl).trans hI.x20)
    x21 := (hc .X21 rfl).trans ((Match.reg_eq hm hm1 (v := .reg .X21) rfl rfl).trans hI.x21)
    x22 := by rw [hc .X22 rfl, Match.reg_eq hm hm1 (v := .reg .X22) rfl rfl]; exact hI.x22
    x23 := by rw [hc .X23 rfl, Match.reg_eq hm hm1 (v := .reg .X23) rfl rfl]; exact hI.x23
    le := hI.le
    img := ?_ } ?_
  · -- the images stored so far: not in the callee's stack
    have hd : st.data.dmem = m.dmem := hm1.dmem_eq hwf rfl
    have hfbN := h.fbN
    have hfbw := h.fbw
    unfold NoWrap at hfbw
    have hSP := m0.regs.SP.toNat_lt
    have hN := h.hN
    rw [stack_eq] at hN
    have hps : ringPsiStack = 640 := rfl
    have hnw : NoWrap (base m0 (2352 + ringPsiStack)) ringPsiStack := by
      unfold NoWrap; rw [base_toNat (by omega)]; omega
    refine NativeRustcVm.BytesAt.of_sameOutside (by rw [hd]; exact hI.img) hq.2.1 fun j hj ↦ ?_
    rw [NativeRustcVm.length_ewsBytes, List.length_take, imgs_length] at hj
    rw [NativeRustcVm.addr_add_add]
    rintro (hq' | hq')
    · unfold InRange at hq'; omega
    · rw [stackBelow_eq hfr1.sp (N' := ringPsiStack) (by omega), Sym.inRange_iff hnw,
        base_toNat (by omega), NativeRustcVm.toNat_add_ofNat (by omega), hfbN] at hq'
      omega
  · show ewRet m2 = _
    rw [hq.1, ewArg, e0, e1, hgl, imgs_getElem]

end

end NativeRustcVmArm.Ring.Target
