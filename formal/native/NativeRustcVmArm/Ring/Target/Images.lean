module

public import NativeRustcVmArm.Code.Vm.RingPsi.Names
public import NativeRustcVmArm.Code.Vm.RingTarget.Names
public import NativeRustcVmArm.Ring.Target.Loop

/-!
# `ring_target`: the images loop

A turn stores `Ψ(s_i)` at the buffer's element `i` and counts on (`b2`, `stepStore`); the loop
(`images`) runs the 64 turns from the prologue's state to `Inv m0 64` after the loop (`b3`).
-/

namespace NativeRustcVmArm.Ring.Target

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingTarget

public section

variable {m0 : MachineData} [Host] {k : Nat}

/-- **The store** (`b2`): `Ψ(s_i)` (X0, X1) at the buffer's element `i`, the counter on, back to
the head unless the 64 images are done. -/
theorem stepStore (h : P m0) {i' : Nat} {ds : List Directive} {S' : SState}
    (hk : ds.IsInfixAt Host.prog i') (hrun : exec ds storeS = some (S', storeExit))
    (hS : storeOk S' = true) {i : Nat} {m : MachineData} (hI : Inv m0 i m) (hi : i < 64)
    (hv : (⟨m.regs.X0, m.regs.X1⟩ : EW) = (imgs m0).toList[i]'(by rw [imgs_length]; exact hi))
    {R : MachineState → Prop}
    (hnext : ∀ m1, Inv m0 (i + 1) m1 → i + 1 < 64 →
      Eventually (step1 Host.exe) R ⟨m1, Labels.label NativeRustcVmArm.Vm.RingTarget.label_1⟩)
    (hdone : ∀ m1, Inv m0 64 m1 →
      Eventually (step1 Host.exe) R ⟨m1, Host.addrOf (i' + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf i'⟩ := by
  have hfbN := h.fbN
  have hfbw := h.fbw
  unfold NoWrap at hfbw
  have hN := h.hN
  rw [stack_eq] at hN
  have hSP := m0.regs.SP.toNat_lt
  have hfb : (fb m0).toNat = (base m0 2352).toNat := rfl
  have ha : (fb m0 + BitVec.ofNat 64 (1232 + 16 * i)).toNat = (fb m0).toNat + (1232 + 16 * i) :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have hwf : (Env.ofMachine m [(fb m0 + BitVec.ofNat 64 (1232 + 16 * i), 16)]).WF :=
    Env.wf_of ⟨⟨fun j hj ↦ by
        rw [NativeRustcVm.addr_add_add]
        exact hI.fr.kept _ (frame_mapped h.st (by decide) _ (by omega)),
      by unfold NoWrap; rw [ha]; omega⟩, trivial⟩ (List.pairwise_singleton _ _)
  have hm : Match (Env.ofMachine m [(fb m0 + BitVec.ofNat 64 (1232 + 16 * i), 16)]) storeS m :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl trivial trivial trivial
      ⟨by
        simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
        rw [hI.x23, hI.x22]
        show _ = fb m0 + BitVec.ofNat 64 (1232 + 16 * i) + BitVec.ofInt 64 0
        rw [NativeRustcVm.addr_add_add]
        simp, trivial⟩
  refine exec_then hk hrun hwf hm fun st hm1 hpc ↦ ?_
  simp only [storeOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨hmem, hw⟩, h19⟩, h20⟩, h21⟩, h23⟩, h22⟩, hsp⟩ := hS
  have hwr : ∀ q, Written (Env.ofMachine m [(fb m0 + BitVec.ofNat 64 (1232 + 16 * i), 16)]) S' q →
      (fb m0).toNat + (1232 + 16 * i) ≤ q.toNat ∧ q.toNat < (fb m0).toNat + (1232 + 16 * i) + 16 :=
    fun q ⟨w, hwm, b, sz, hb, h1, h2⟩ ↦ by
      obtain ⟨hr, hn⟩ := hmem w hwm
      rw [hr] at hb
      simp only [Env.ofMachine, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      rw [ha] at h1 h2
      omega
  have hfr : TFr m0 st.data := by
    refine hI.fr.step (W := Written (Env.ofMachine m [(fb m0 + BitVec.ofNat 64 (1232 + 16 * i),
        16)]) S') (Match.sp_eq hm hm1 (by rw [hsp]; rfl)) (fun _ h ↦ by cases h) (hm1.kept hwf)
      (hm1.sameOutside hwf) (fun q hq ↦ .inl ?_) fun p hp j hj hq ↦ ?_
    · have := hwr q hq
      rw [Sym.inRange_iff (base_noWrap h.hN), base_toNat h.hN, stack_eq]
      omega
    · have := hwr _ hq
      have h1 := slots_ge p hp
      have h2 := slots_le p hp
      rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by omega)] at this
      omega
  have hx : (Sym.bin .add .W64 (.reg .X22) (.lit 16)).eval
      (Env.ofMachine m [(fb m0 + BitVec.ofNat 64 (1232 + 16 * i), 16)]) =
        BitVec.ofNat 64 (16 * (i + 1)) := by
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    rw [hI.x22, show 16 * (i + 1) = 16 * i + 16 by omega, BitVec.ofNat_add]
  have hI' : Inv m0 (i + 1) st.data := {
    fr := hfr
    x19 := reg_of hm1 h19 (by simp only [Sym.eval, Env.ofMachine_regs, hI.x19])
    x20 := reg_of hm1 h20 (by simp only [Sym.eval, Env.ofMachine_regs, hI.x20])
    x21 := reg_of hm1 h21 (by simp only [Sym.eval, Env.ofMachine_regs, hI.x21])
    x22 := by rw [hm1.regs .X22 _ h22, hx]
    x23 := by rw [hm1.regs .X23 _ h23]; simp only [Sym.eval, Env.ofMachine_regs, hI.x23]
    le := hi
    img := by
      have htake : (imgs m0).toList.take (i + 1) = (imgs m0).toList.take i ++
          [(imgs m0).toList[i]'(by rw [imgs_length]; exact hi)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by rw [imgs_length]; exact hi)]
        rfl
      have hlen : ((imgs m0).toList.take i).length = i := by
        rw [List.length_take, imgs_length]; omega
      rw [htake, NativeRustcVm.ewsAt_append, NativeRustcVm.ewsAt_singleton, hlen,
        NativeRustcVm.addr_add_add, ← hv]
      refine ⟨NativeRustcVm.BytesAt.of_sameOutside hI.img (hm1.sameOutside hwf) fun j hj hq ↦ ?_,
        ?_⟩
      · rw [NativeRustcVm.length_ewsBytes, List.length_take, imgs_length] at hj
        have := hwr _ hq
        rw [NativeRustcVm.addr_add_add, NativeRustcVm.toNat_add_ofNat (by omega)] at this
        omega
      · have w0 := hm1.bytesAt_write (r := 0) (o := 0) (n := 8)
          (b := fb m0 + BitVec.ofNat 64 (1232 + 16 * i)) (sz := 16) rfl (by omega)
          (v := .reg .X0) fun j hj ↦ (hw j hj).1
        have w1 := hm1.bytesAt_write (r := 0) (o := 8) (n := 8)
          (b := fb m0 + BitVec.ofNat 64 (1232 + 16 * i)) (sz := 16) rfl (by omega)
          (v := .reg .X1) fun j hj ↦ (hw j hj).2
        rw [wordBytes_reg] at w0 w1
        rw [NativeRustcVm.ewAt_iff, NativeRustcVm.addr_add_add]
        rw [NativeRustcVm.addr_add_zero] at w0
        rw [NativeRustcVm.addr_add_add] at w1
        exact ⟨w0, w1⟩ }
  have hcv : (SBool.not (.cmp .eq .W64 (.bin .add .W64 (.reg .X22) (.lit 16)) (.lit 1024))).eval
      (Env.ofMachine m [(fb m0 + BitVec.ofNat 64 (1232 + 16 * i), 16)]) =
        !(BitVec.ofNat 64 (16 * (i + 1)) == BitVec.ofNat 64 1024) := by
    simp only [SBool.eval, CmpOp.apply, low_W64, hx]
    rfl
  simp only [PcOk, storeExit, hcv] at hpc
  obtain ⟨d, pc⟩ := st
  simp only at hpc hI'
  subst hpc
  by_cases hl : i + 1 = 64
  · rw [show 16 * (i + 1) = 1024 by omega]
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [hl] at hI'
    exact hdone d hI'
  · have hc : (!(BitVec.ofNat 64 (16 * (i + 1)) == BitVec.ofNat 64 1024)) = true := by
      rw [Bool.not_eq_true', beq_eq_false_iff_ne]
      intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at this
      omega
    rw [hc]
    exact hnext d hI' (by omega)

theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.RingTarget.b2Offset) :=
  hb b2_in_code (by simp [b2]) hp

/-- **A turn** of the images loop. -/
theorem turn (hp : Placed code k) (h : P m0)
    (hpsi : Spec (Labels.label NativeRustcVmArm.Vm.RingPsi.entryLabel) RingPsiPre RingPsiPost) {i : Nat} {m : MachineData}
    (hI : Inv m0 i m) (hi : i < 64) :
    Eventually (step1 Host.exe) (fun st ↦
      (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b1Offset) ∧ Inv m0 (i + 1) st.data ∧ i + 1 < 64) ∨
        (st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b3Offset) ∧ Inv m0 64 st.data)) ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b1Offset)⟩ :=
  stepPsi hp h hpsi hI hi fun m2 hI2 hv ↦
    stepStore h (hb2 hp) run_b2 (by decide) hI2 hi hv
      (fun m1 h1 hlt ↦ by
        rw [show Labels.label NativeRustcVmArm.Vm.RingTarget.label_1 = Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b1Offset) from hp.label (j := NativeRustcVmArm.Vm.RingTarget.b1Offset) NativeRustcVmArm.Vm.RingTarget.label_1_at]
        exact .done _ (.inl ⟨rfl, h1, hlt⟩))
      fun m1 h1 ↦ by
        rw [show k + NativeRustcVmArm.Vm.RingTarget.b2Offset + b2.length = k + NativeRustcVmArm.Vm.RingTarget.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b2_next]]
        exact .done _ (.inr ⟨rfl, h1⟩)

/-- **The images loop**: from the prologue's state to the 64 images stored. -/
theorem images (hp : Placed code k) (h : P m0)
    (hpsi : Spec (Labels.label NativeRustcVmArm.Vm.RingPsi.entryLabel) RingPsiPre RingPsiPost) {m : MachineData}
    (hI : Inv m0 0 m) {R : MachineState → Prop}
    (cont : ∀ m', Inv m0 64 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b3Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b1Offset)⟩ := by
  refine Eventually.bind (p := fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b3Offset) ∧ Inv m0 64 st.data) ?_
    fun ⟨m', pc⟩ ⟨hpc, hI'⟩ ↦ by
      simp only at hpc hI'
      subst hpc
      exact cont m' hI'
  refine Sym.loop (I := fun n st ↦ ∃ i, n = 64 - i ∧ i < 64 ∧ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b1Offset) ∧
    Inv m0 i st.data) (fun n st ⟨i, hn, hi, hpc, hI⟩ ↦ ?_) ⟨0, rfl, by decide, rfl, hI⟩
  obtain ⟨mm, pc⟩ := st
  simp only at hpc hI
  subst hpc
  refine (turn hp h hpsi hI hi).mono fun st hst ↦ ?_
  rcases hst with ⟨hpc, hI', hlt⟩ | hD
  · exact .inr ⟨64 - (i + 1), by omega, ⟨i + 1, rfl, hlt, hpc, hI'⟩⟩
  · exact .inl hD

end

end NativeRustcVmArm.Ring.Target
