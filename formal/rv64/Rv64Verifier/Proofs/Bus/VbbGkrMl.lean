import Rv64Verifier.Proofs.Bus.VbbGkrSm

/-!
# `verify_bus_balance`: one `multilinear_eval` of an iteration

From its entry to the test of its tag (`0x80006a58`, `0x80006abc` or `0x80006b1c`, `tagStep`),
then on, the value at `S - 600`, or out through `0x80006c0c` (`mleRun`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- The test of a `multilinear_eval`'s tag at `S - 608`. -/
theorem tagStep {s t : MachineState} (hpre : BusBalancePre s)
    (sp : t.getReg .x2 = s.getReg .x2 - 1344) {nx : Word}
    (hpc : (t.pc = 0x80006a58 ∧ nx = 0x80006a60) ∨ (t.pc = 0x80006abc ∧ nx = 0x80006ac4) ∨
      (t.pc = 0x80006b1c ∧ nx = 0x80006b24)) :
    ∃ t', Reaches Image.code t t' ∧ (∀ a, t'.getMem a = t.getMem a) ∧
      (∀ r ∈ ([.x2, .x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
        List Reg), t'.getReg r = t.getReg r) ∧
      (t.getMem (s.getReg .x2 - BitVec.ofNat 64 608) ≠ 0 → t'.pc = 0x80006c0c) ∧
      (t.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0 → t'.pc = nx) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have e736 : t.getReg .x2 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rcases hpc with ⟨hpc, rfl⟩ | ⟨hpc, rfl⟩ | ⟨hpc, rfl⟩
  · obtain ⟨t', hr, h'⟩ := Sym.BlockSpec.reaches b80006a58_spec hpc (by
      rv_eval [sp]
      valid_access hval [hb1])
    exact ⟨t', hr, b80006a58_mem_same h', fun r hr ↦ b80006a58_keeps h' r (mem_of_mem hr _),
      fun hc ↦ b80006a58_pc_taken h' (by rw [e736]; exact hc),
      fun hc ↦ b80006a58_pc_not_taken h' (by rw [e736]; exact hc)⟩
  · obtain ⟨t', hr, h'⟩ := Sym.BlockSpec.reaches b80006abc_spec hpc (by
      rv_eval [sp]
      valid_access hval [hb1])
    exact ⟨t', hr, b80006abc_mem_same h', fun r hr ↦ b80006abc_keeps h' r (mem_of_mem hr _),
      fun hc ↦ b80006abc_pc_taken h' (by rw [e736]; exact hc),
      fun hc ↦ b80006abc_pc_not_taken h' (by rw [e736]; exact hc)⟩
  · obtain ⟨t', hr, h'⟩ := Sym.BlockSpec.reaches b80006b1c_spec hpc (by
      rv_eval [sp]
      valid_access hval [hb1])
    exact ⟨t', hr, b80006b1c_mem_same h', fun r hr ↦ b80006b1c_keeps h' r (mem_of_mem hr _),
      fun hc ↦ b80006b1c_pc_taken h' (by rw [e736]; exact hc),
      fun hc ↦ b80006b1c_pc_not_taken h' (by rw [e736]; exact hc)⟩

/-- `values`' first elements at `P` keep their values through a step writing the frame. -/
theorem StepR.eListP {s v w : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (st : StepR s v w A) (hA : FrameW s A) {P : Word}
    (hP : heapNext s ≤ P.toNat ∧ P.toNat + 72 ≤ heapNext v) {m : Nat} (hm : m ≤ 3) :
    eListAt w P m = eListAt v P m := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hh := st.heap.hi
  have hmo := st.mono
  simp only [heapNext, heapEnd] at hP hh hmo
  refine eListAt_congr fun i hi ↦ ?_
  have bw (j : Nat) (hj : j + 8 ≤ 24) : w.getMem (P + BitVec.ofNat 64 (24 * i) +
      BitVec.ofNat 64 j) = v.getMem (P + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 j) := by
    refine st.word hpre (fun y hy hy' ↦ ?_) (Or.inr ⟨?_, ?_⟩)
    · have := hA y hy'
      addr_omega [this, hy, hb1, hP, hh, hmo, hi, hj, hm]
    · simp only [heapNext]; addr_omega [hP, hi, hj, hm]
    · simp only [heapNext]; addr_omega [hP, hi, hj, hm]
  exact eAt_congr (by simpa using bw 0 (by omega)) (bw 8 (by omega)) (bw 16 (by omega))

/-- A step writing only the frame's scratch keeps `MB`. -/
theorem MB.stepF {s u v w : MachineState} {k : Start} {cnt : E} {P : Word} {n : ℕ}
    {x y c2 : List E} {xp : Word} {vs : List E} {A : Word → Prop} (hpre : BusBalancePre s)
    (h : MB s u v k cnt P n x y c2 xp vs) (st : StepR s v w A) (hA : ∀ a, A a → Scratch s a)
    (hmiss : ∀ a, A a → ¬ Within a (s.getReg .x2 - BitVec.ofNat 64 720) 24 ∧
      ¬ Within a (s.getReg .x2 - 160) 8 ∧ ¬ Within a (s.getReg .x2 - 1128) 8 ∧
      ¬ Within a (s.getReg .x2 - 1280) 8 ∧ ¬ Within a (s.getReg .x2 - 1120) 8 ∧
      ¬ Within a (s.getReg .x2 - 1144) 8 ∧ ¬ Within a (s.getReg .x2 - 1112) 8)
    (hr : ∀ r ∈ ([.x19, .x20, .x22, .x23, .x24, .x25] : List Reg), w.getReg r = v.getReg r) :
    MB s u w k cnt P n x y c2 xp vs := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have fA : FrameW s A := fun a ha ↦ Scratch.frameW hpre a (hA a ha)
  have hA' : ∀ a, A a → Within a (s.getReg .x2 - 1344) 1240 ∨ Within a P 72 :=
    fun a ha ↦ Or.inl (fA a ha)
  have wd (j : Nat) (hj : j = 160 ∨ j = 1128 ∨ j = 1280 ∨ j = 1120 ∨ j = 1144 ∨ j = 1112) :
      w.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    st.word hpre (fun y hy hs ↦ by
      obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hmiss y hs
      rcases hj with hj | hj | hj | hj | hj | hj <;> subst hj
      · exact n2 (by addr_omega [hy, hb1])
      · exact n3 (by addr_omega [hy, hb1])
      · exact n4 (by addr_omega [hy, hb1])
      · exact n5 (by addr_omega [hy, hb1])
      · exact n6 (by addr_omega [hy, hb1])
      · exact n7 (by addr_omega [hy, hb1]))
      (Or.inl (by addr_omega [hb1, hj]))
  have hP := h.ctx.heapP
  refine {
    ctx := h.ctx.step hpre (st.weaken hA)
    hu := h.hu
    hP := h.hP
    x20 := by rw [hr .x20 (by decide)]; exact h.x20
    x24 := by rw [hr .x24 (by decide)]; exact h.x24
    x23 := by rw [hr .x23 (by decide)]; exact h.x23
    layers := by
      rw [show s.getReg .x2 - 1128 = s.getReg .x2 - BitVec.ofNat 64 1128 from rfl, wd 1128 (by omega)]
      exact h.layers
    valuesPtr := by
      rw [show s.getReg .x2 - 1280 = s.getReg .x2 - BitVec.ofNat 64 1280 from rfl, wd 1280 (by omega)]
      exact h.valuesPtr
    len := by
      rw [show s.getReg .x2 - 160 = s.getReg .x2 - BitVec.ofNat 64 160 from rfl, wd 160 (by omega)]
      exact h.len
    pushed := by rw [st.eListP hpre fA ⟨hP.1, hP.2.1⟩ h.vlen]; exact h.pushed
    vlen := h.vlen
    xv := by
      rw [show s.getReg .x2 - 1120 = s.getReg .x2 - BitVec.ofNat 64 1120 from rfl,
        show s.getReg .x2 - 1144 = s.getReg .x2 - BitVec.ofNat 64 1144 from rfl,
        wd 1120 (by omega), wd 1144 (by omega)]
      exact h.xv.keepP hpre h.hu h.hP st hA'
    yv := h.yv.keepP hpre h.hu h.hP st hA' (by omega) (by omega) fun y hy hs ↦ (hmiss y hs).1 hy
    ylen := h.ylen
    y19 := by
      rw [hr .x19 (by decide), h.y19]
      exact (st.word hpre (fun y hy hs ↦ (hmiss y hs).1 (by addr_omega [hy, hb1]))
        (Or.inl (by addr_omega [hb1]))).symm
    y22 := by
      rw [hr .x22 (by decide), h.y22]
      exact (st.word hpre (fun y hy hs ↦ (hmiss y hs).1 (by addr_omega [hy, hb1]))
        (Or.inl (by addr_omega [hb1]))).symm
    pal := h.pal
    ch2 := by
      rw [show s.getReg .x2 - 1112 = s.getReg .x2 - BitVec.ofNat 64 1112 from rfl,
        wd 1112 (by omega), hr .x25 (by decide)]
      exact h.ch2.keepP hpre h.hu h.hP st hA'
    l2 := h.l2
    step := h.step.join (st.weaken fun a ha ↦ Or.inl (hA a ha)) }

/-- A `multilinear_eval` of a child `c` at `y`, through its tag's test. -/
theorem mleRun (hME : FunSpec Image.code 0x8000d28c
      (fun s ↦ Vbb.MleEvalPre s ∧ Rv64Verifier.Proofs.Multilinear.Bridges.MleEnds s)
      Vbb.MleEvalPost)
    {bev : MachineState → Word → List E → Option E} {s u w₀ : MachineState} {k : Start} {cnt : E}
    {P : Word} {n : ℕ} {x y c2 : List E} {xp : Word} {vs c : List E} (hpre : BusBalancePre s)
    (h : MB s u w₀ k cnt P n x y c2 xp vs) (hpc : w₀.pc = 0x8000d28c) {nx : Word}
    (hx1 : (w₀.getReg .x1 = 0x80006a58 ∧ nx = 0x80006a60) ∨
      (w₀.getReg .x1 = 0x80006abc ∧ nx = 0x80006ac4) ∨
      (w₀.getReg .x1 = 0x80006b1c ∧ nx = 0x80006b24))
    (h10 : w₀.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608)
    (hc : HeapVec u w₀ (w₀.getReg .x11) (w₀.getReg .x12) c) (hl : c.length = 2 ^ stepOf n)
    (h13 : w₀.getReg .x13 = vecPtr w₀ (s.getReg .x2 - BitVec.ofNat 64 720))
    (h14 : w₀.getReg .x14 = vecLen w₀ (s.getReg .x2 - BitVec.ofNat 64 720))
    (hnone : multilinearEvalRust c y = none →
      ∀ T, TranscriptAt s (s.getReg .x12) T → (prog bev s).run T = none) :
    ∃ w, Reaches Image.code w₀ w ∧ (Done bev s w ∨ Dead Image.code w ∨ ∃ e,
      multilinearEvalRust c y = some e ∧ w.pc = nx ∧ MB s u w k cnt P n x y c2 xp vs ∧
      eAt w (s.getReg .x2 - BitVec.ofNat 64 600) = e ∧
      (∀ r ∈ ([.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
        List Reg), w.getReg r = w₀.getReg r) ∧
      (∀ T, TranscriptAt w₀ (s.getReg .x12) T → TranscriptAt w (s.getReg .x12) T) ∧
      ∀ p l (c' : List E), HeapVec u w₀ p l c' → HeapVec u w p l c') := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have C := h.ctx
  have hu := h.hu
  have yr : NewVecR s w₀ (vecCap w₀ (s.getReg .x2 - BitVec.ofNat 64 720))
      (vecPtr w₀ (s.getReg .x2 - BitVec.ofNat 64 720))
      (vecLen w₀ (s.getReg .x2 - BitVec.ofNat 64 720)) y :=
    NewVecR.toS hu ⟨h.yv.vec.len, h.yv.buf, h.yv.elems⟩
  have yl : 0 < (vecLen w₀ (s.getReg .x2 - BitVec.ofNat 64 720)).toNat := by
    have := congrArg List.length h.yv.elems
    rw [vecEs, eListAt_length, h.ylen] at this
    have := stepOf_le n
    omega
  obtain ⟨cc, hcr⟩ := hc
  have cl : 0 < (w₀.getReg .x12).toNat := by
    have := congrArg List.length hcr.elems
    rw [eListAt_length, hl] at this
    have := Nat.two_pow_pos (stepOf n)
    omega
  obtain ⟨v₁, hr₁, ⟨hpc₁, hp₁, st₁, hv₁, tr₁⟩ | hd⟩ :=
    mleCall hME hpre C.inv (Reaches.refl w₀) hpc h10 (hcr.toS hu) cl rfl rfl yr yl h13 h14
  swap
  · exact ⟨v₁, hr₁, Or.inr (Or.inl hd)⟩
  have I₁ := C.inv.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₁
  have hpcN : (v₁.pc = 0x80006a58 ∧ nx = 0x80006a60) ∨ (v₁.pc = 0x80006abc ∧ nx = 0x80006ac4) ∨
      (v₁.pc = 0x80006b1c ∧ nx = 0x80006b24) := by
    rw [hpc₁, returnAddress_eq]
    rcases hx1 with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩
    · exact Or.inl ⟨by rw [e]; decide, rfl⟩
    · exact Or.inr (Or.inl ⟨by rw [e]; decide, rfl⟩)
    · exact Or.inr (Or.inr ⟨by rw [e]; decide, rfl⟩)
  obtain ⟨t, hrt, mt, kt, ptT, ptN⟩ := tagStep hpre I₁.sp hpcN
  have sA (a : Word) (ha : Within a (s.getReg .x2 - BitVec.ofNat 64 608) 32) : Scratch s a :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))))
  have st : StepR s w₀ t (Within · (s.getReg .x2 - BitVec.ofNat 64 608) 32) :=
    st₁.join (StepR.same mt I₁.heap (kt .x2 (by decide)))
  have It := I₁.same mt (kt .x2 (by decide))
  have Ct := C.step hpre (st.weaken sA)
  have rg (r : Reg) (hr : r ∈ ([.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26,
      .x27] : List Reg)) : t.getReg r = w₀.getReg r := by
    rw [kt r (mem_of_mem hr _), hp₁ r (mem_of_mem hr _)]
  rcases hm : multilinearEvalRust c y with _ | e
  · rw [hm] at hv₁
    dsimp only at hv₁
    obtain ⟨t', hrt', hd⟩ := errMle hpre Ct (ptT hv₁) (hnone hm)
    exact ⟨t', hr₁.trans (hrt.trans hrt'), Or.inl hd⟩
  rw [hm] at hv₁
  dsimp only at hv₁
  refine ⟨t, hr₁.trans hrt, Or.inr (Or.inr ⟨e, rfl, ptN hv₁.1,
    h.stepF hpre st sA (fun a ha ↦ ⟨fun hw ↦ by addr_omega [ha, hw, hb1],
      fun hw ↦ by addr_omega [ha, hw, hb1], fun hw ↦ by addr_omega [ha, hw, hb1],
      fun hw ↦ by addr_omega [ha, hw, hb1], fun hw ↦ by addr_omega [ha, hw, hb1],
      fun hw ↦ by addr_omega [ha, hw, hb1], fun hw ↦ by addr_omega [ha, hw, hb1]⟩)
      (fun r hr ↦ rg r (mem_of_mem hr _)), ?_, rg, fun T hT ↦ TranscriptAt.same hpre I₁ mt (tr₁ T hT),
      fun p l c' hc ↦ hc.keepP hpre hu h.hP st fun a ha ↦ Or.inl (by addr_omega [ha, hb1])⟩)⟩
  rw [← hv₁.2]
  exact eAt_congr (by rw [mt]; exact congrArg v₁.getMem (by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]))
    (by rw [mt]; exact congrArg v₁.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]))
    (by rw [mt]; exact congrArg v₁.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]))

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
