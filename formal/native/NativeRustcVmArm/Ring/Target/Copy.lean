module

public import NativeRustcVmArm.Code.Vm.Memcpy.Names
public import NativeRustcVmArm.Ring.Target.Images

/-!
# `ring_target`: the images' copy

After the loop, `b3` copies the 64 images to frame byte `208` (`memcpy`): the state `St m0 D4`
the turns start from (`stepCopy`), `f`'s words read in every state of the frame (`holds_fD`).
-/

namespace NativeRustcVmArm.Ring.Target

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingTarget

public section

variable {m0 : MachineData}

/-- `f`'s element `p`'s words, in every state of the frame. -/
theorem fword [Labels] (h : P m0) {m : MachineData} (hfr : TFr m0 m) {p : Nat} (hp : p < 8) :
    tval (rsT m0) m (.load 1 (16 * p) 8) = tv m0 (fI p) ∧
      tval (rsT m0) m (.load 1 (16 * p + 8) 8) = tv m0 (fI p + 1) := by
  have hw : ∀ o, o + 8 ≤ 128 → NativeRustcVm.wordOf m.dmem (fA m0 + BitVec.ofNat 64 o) =
      NativeRustcVm.wordOf m0.dmem (fA m0 + BitVec.ofNat 64 o) := fun o ho ↦
    NativeRustcVm.wordOf_congr fun j hj ↦ by
      rw [NativeRustcVm.addr_add_add]
      exact P.same h hfr h.fs h.fw (by omega)
  have e := tv_f (m0 := m0) hp
  have e0 : tv m0 (fI p) = ((fl m0).getD p 0).c0 := congrArg EW.c0 e
  have e1 : tv m0 (fI p + 1) = ((fl m0).getD p 0).c1 := congrArg EW.c1 e
  have hg : (fl m0).getD p 0 =
      NativeRustcVm.ewOf m0.dmem (fA m0 + BitVec.ofNat 64 (16 * p)) := by
    simp [fl, arr, fA, ringWidth, hp]
  rw [e0, e1, hg]
  refine ⟨?_, ?_⟩
  · unfold tval
    simp only [Sym.eval]
    rw [load_eq_wordOf]
    show UInt64.ofBitVec (NativeRustcVm.wordOf m.dmem (fA m0 + BitVec.ofNat 64 (16 * p))).toBitVec = _
    rw [hw _ (by omega)]
    rfl
  · unfold tval
    simp only [Sym.eval]
    rw [load_eq_wordOf]
    show UInt64.ofBitVec (NativeRustcVm.wordOf m.dmem (fA m0 + BitVec.ofNat 64 (16 * p + 8))).toBitVec = _
    rw [hw _ (by omega), ← NativeRustcVm.addr_add_add]
    rfl

/-- **`f`'s words** hold in every state of the frame. -/
theorem holds_fD [Labels] (h : P m0) {m : MachineData} (hfr : TFr m0 m) :
    Holds (rsT m0) (tv m0) fD m := by
  intro q hq
  simp only [fD, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact (fword h hfr (p := 0) (by decide)).1
  · exact (fword h hfr (p := 0) (by decide)).2
  · exact (fword h hfr (p := 1) (by decide)).1
  · exact (fword h hfr (p := 1) (by decide)).2
  · exact (fword h hfr (p := 2) (by decide)).1
  · exact (fword h hfr (p := 2) (by decide)).2
  · exact (fword h hfr (p := 3) (by decide)).1
  · exact (fword h hfr (p := 3) (by decide)).2
  · exact (fword h hfr (p := 4) (by decide)).1
  · exact (fword h hfr (p := 4) (by decide)).2
  · exact (fword h hfr (p := 5) (by decide)).1
  · exact (fword h hfr (p := 5) (by decide)).2
  · exact (fword h hfr (p := 6) (by decide)).1
  · exact (fword h hfr (p := 6) (by decide)).2
  · exact (fword h hfr (p := 7) (by decide)).1
  · exact (fword h hfr (p := 7) (by decide)).2

variable [Host] {k : Nat}

/-- **The copy** (`b3`): the images at frame byte `208`, the turns' first description. -/
theorem stepCopy (hp : Placed code k) (h : P m0)
    (hmemcpy : Spec (Labels.label NativeRustcVmArm.Vm.Memcpy.entryLabel) MemcpyPre MemcpyPost) {m : MachineData}
    (hI : Inv m0 64 m) {R : MachineState → Prop}
    (cont : ∀ m', St m0 D4 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b4Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingTarget.b3Offset)⟩ := by
  have hwf := envT_wf h hI.fr
  have hfbN := h.fbN
  have hfbw := h.fbw
  unfold NoWrap at hfbw
  have hN := h.hN
  rw [stack_eq] at hN
  have hSP := m0.regs.SP.toNat_lt
  have hfb : (fb m0).toNat = (base m0 2352).toNat := rfl
  refine exec_then (hb b3_in_code (by simp [b3]) hp) run_b3 hwf (matchT2 hI.fr h)
    fun st hm1 hpc ↦ ?_
  have hfr1 : TFr m0 st.data := hI.fr.ofBlock (matchT2 hI.fr h) hm1 hwf rfl rfl rfl
    fun _ h ↦ by cases h
  have e0 : st.data.regs.X0.toBitVec = fb m0 + BitVec.ofNat 64 208 := by
    rw [show st.data.regs.X0 = st.data.regs.getXReg .X0 from rfl, hm1.regs .X0 _ rfl]
    rfl
  have e1 : st.data.regs.X1.toBitVec = fb m0 + BitVec.ofNat 64 1232 := by
    rw [show st.data.regs.X1 = st.data.regs.getXReg .X1 from rfl, hm1.regs .X1 _ rfl]
    rfl
  have e2 : st.data.regs.X2 = 1024 := by
    apply UInt64.toBitVec_inj.mp
    rw [show st.data.regs.X2 = st.data.regs.getXReg .X2 from rfl, hm1.regs .X2 _ rfl]
    rfl
  have h208 : (fb m0 + BitVec.ofNat 64 208).toNat = (fb m0).toNat + 208 :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have h1232 : (fb m0 + BitVec.ofNat 64 1232).toNat = (fb m0).toNat + 1232 :=
    NativeRustcVm.toNat_add_ofNat (by omega)
  have hpre : MemcpyPre st.data := by
    show Mapped _ _ st.data.regs.X2.toNat ∧ _
    rw [e0, e1, e2, show (1024 : UInt64).toNat = 1024 from rfl]
    refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_, ?_, ?_, ?_⟩
    · rw [NativeRustcVm.addr_add_add]
      exact hfr1.kept _ (frame_mapped h.st (by decide) _ (by omega))
    · rw [NativeRustcVm.addr_add_add]
      exact hfr1.kept _ (frame_mapped h.st (by decide) _ (by omega))
    · unfold NoWrap; rw [h208]; omega
    · unfold NoWrap; rw [h1232]; omega
    · unfold Apart; rw [h208, h1232]; omega
  refine Eventually.bind (Spec.apply hmemcpy hpc.1 hpre) fun ⟨m2, pc⟩ ⟨hpc2, hq⟩ ↦ ?_
  simp only at hpc2 hq
  rw [hpc2, hpc.2, show k + NativeRustcVmArm.Vm.RingTarget.b3Offset + b3.length = k + NativeRustcVmArm.Vm.RingTarget.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingTarget.b3_next]]
  obtain ⟨-, hcp, hso, hS⟩ := hq
  rw [e0, e2, show (1024 : UInt64).toNat = 1024 from rfl] at hcp hso
  rw [e1] at hcp
  have hfr2 : TFr m0 m2 := by
    refine hfr1.step (W := InRange (fb m0 + BitVec.ofNat 64 208) 1024) hS.2.1
      (fun _ h ↦ by cases h) hS.2.2 hso (fun q hq ↦ .inl ?_) fun p hp j hj hq ↦ ?_
    · have hnw : NoWrap (fb m0 + BitVec.ofNat 64 208) 1024 := by unfold NoWrap; rw [h208]; omega
      rw [Sym.inRange_iff hnw, h208] at hq
      rw [Sym.inRange_iff (base_noWrap h.hN), base_toNat h.hN, stack_eq]
      omega
    · have hnw : NoWrap (fb m0 + BitVec.ofNat 64 208) 1024 := by unfold NoWrap; rw [h208]; omega
      have h1 := slots_ge p hp
      have h2 := slots_le p hp
      rw [Sym.inRange_iff hnw, h208, NativeRustcVm.addr_add_add,
        NativeRustcVm.toNat_add_ofNat (by omega)] at hq
      omega
  have hd : st.data.dmem = m.dmem := hm1.dmem_eq hwf rfl
  have hsrc : bytesOf st.data.dmem (fb m0 + BitVec.ofNat 64 1232) 1024 =
      (imgs m0).toList.flatMap NativeRustcVm.ewBytes := by
    have := Hasher.bytesOf_of_bytesAt (d := st.data.dmem) (a := fb m0 + BitVec.ofNat 64 1232)
      (bs := (imgs m0).toList.flatMap NativeRustcVm.ewBytes) (by
        rw [hd]
        have := hI.img
        rwa [List.take_of_length_le (by rw [imgs_length])] at this)
    rwa [NativeRustcVm.length_ewsBytes, imgs_length] at this
  rw [hsrc] at hcp
  have h21 : m2.regs.getXReg .X21 = m0.regs.X1 :=
    (hS.1 .X21 rfl).trans ((Match.reg_eq (matchT2 hI.fr h) hm1 (v := .reg .X21) rfl rfl).trans
      hI.x21)
  refine cont m2 ⟨hfr2, fun q hq ↦ ?_, hcp⟩
  simp only [D4, bD, List.mem_cons] at hq
  rcases hq with rfl | rfl | rfl | hq
  · rfl
  · rfl
  · show UInt64.ofBitVec (m2.regs.getXReg .X21).toBitVec = tv m0 fPtr
    rw [h21, tv_fPtr]
    rfl
  · exact holds_fD h hfr2 q hq

end

end NativeRustcVmArm.Ring.Target
