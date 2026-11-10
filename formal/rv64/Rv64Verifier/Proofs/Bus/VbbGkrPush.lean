import Rv64Verifier.Proofs.Bus.VbbGkrMl

/-!
# `verify_bus_balance`: an iteration's first two pushes into `values`

A value at `S - 600` pushed into `values` at `P` (its capacity at least three, so `grow_one` is
never called), its length at `S - 160`, then the next `multilinear_eval`'s arguments
(`push0Step` from `0x80006a60`, `push1Step` from `0x80006ac4`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A push: a step writing `values`' length and its first 72 bytes keeps `MB`. -/
theorem MB.push {s u v w : MachineState} {k : Start} {cnt : E} {P : Word} {n : ℕ}
    {x y c2 : List E} {xp : Word} {vs vs' : List E} (hpre : BusBalancePre s)
    (h : MB s u v k cnt P n x y c2 xp vs)
    (st : StepR s v w fun a ↦ Within a (s.getReg .x2 - 160) 8 ∨ Within a P 72)
    (hr : ∀ r ∈ ([.x19, .x20, .x22, .x23, .x24, .x25] : List Reg), w.getReg r = v.getReg r)
    (hlen : w.getMem (s.getReg .x2 - 160) = BitVec.ofNat 64 vs'.length)
    (hpush : eListAt w P vs'.length = vs') (hvl : vs'.length ≤ 3) :
    MB s u w k cnt P n x y c2 xp vs' := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hP := h.ctx.heapP
  have hPe : P.toNat + 72 ≤ 2013265920 := hP.2.2
  have hA' : ∀ a, (Within a (s.getReg .x2 - 160) 8 ∨ Within a P 72) →
      Within a (s.getReg .x2 - 1344) 1240 ∨ Within a P 72 :=
    fun a ha ↦ ha.imp_left fun h ↦ by addr_omega [h, hb1]
  have wd (j : Nat) (hj : j = 720 ∨ j = 712 ∨ j = 704 ∨ j = 1128 ∨ j = 1280 ∨ j = 1120 ∨
      j = 1144 ∨ j = 1112) :
      w.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = v.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    st.word hpre (fun y hy hs ↦ by
      rcases hs with hs | hs <;> rcases hj with hj | hj | hj | hj | hj | hj | hj | hj <;> subst hj <;>
        addr_omega [hy, hs, hb1, hPe])
      (Or.inl (by addr_omega [hb1, hj]))
  have e712 : s.getReg .x2 - BitVec.ofNat 64 720 + 8 = s.getReg .x2 - BitVec.ofNat 64 712 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e704 : s.getReg .x2 - BitVec.ofNat 64 720 + 16 = s.getReg .x2 - BitVec.ofNat 64 704 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  refine {
    ctx := h.ctx.stepV hpre (st.weaken fun a ha ↦ ha.imp_left fun h ↦
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [h, hb1])))))))
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
    len := hlen
    pushed := hpush
    vlen := hvl
    xv := by
      rw [show s.getReg .x2 - 1120 = s.getReg .x2 - BitVec.ofNat 64 1120 from rfl,
        show s.getReg .x2 - 1144 = s.getReg .x2 - BitVec.ofNat 64 1144 from rfl,
        wd 1120 (by omega), wd 1144 (by omega)]
      exact h.xv.keepP hpre h.hu h.hP st hA'
    yv := h.yv.keepP hpre h.hu h.hP st hA' (by omega) (by omega) fun y hy hs ↦ by
      rcases hs with hs | hs <;> addr_omega [hy, hs, hb1, hPe]
    ylen := h.ylen
    y19 := by
      rw [hr .x19 (by decide), h.y19]
      simp only [vecPtr]
      rw [e712, wd 712 (by omega)]
    y22 := by
      rw [hr .x22 (by decide), h.y22]
      simp only [vecLen]
      rw [e704, wd 704 (by omega)]
    pal := h.pal
    ch2 := by
      rw [show s.getReg .x2 - 1112 = s.getReg .x2 - BitVec.ofNat 64 1112 from rfl,
        wd 1112 (by omega), hr .x25 (by decide)]
      exact h.ch2.keepP hpre h.hu h.hP st hA'
    l2 := h.l2
    step := h.step.join (st.weaken fun a ha ↦ ha.imp_left fun h ↦
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [h, hb1]))))))) }

/-- `values`' capacity at least three. -/
theorem Ctx.capNe {s t : MachineState} {k : Start} {cnt : E} {P : Word} (hpre : BusBalancePre s)
    (C : Ctx s t k cnt P) {c : Word} (hc : c.toNat < 3) : t.getMem (t.getReg .x2 + 1168) ≠ c := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rw [C.inv.sp, show s.getReg .x2 - 1344 + 1168 = s.getReg .x2 - 176 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
  intro h0
  have := C.cap
  rw [vecCap, h0] at this
  omega

/-- The first push and the second `multilinear_eval`'s arguments, from `0x80006a60`. -/
theorem push0Step {s u t : MachineState} {k : Start} {cnt : E} {P : Word} {n : ℕ}
    {x y c1 c2 : List E} {xp : Word} {e : E} (hpre : BusBalancePre s)
    (h : MB s u t k cnt P n x y c2 xp []) (hpc : t.pc = 0x80006a60)
    (he : eAt t (s.getReg .x2 - BitVec.ofNat 64 600) = e) (h8 : t.getReg .x8 = xp)
    (hc1 : HeapVec u t (t.getReg .x26) (t.getReg .x21) c1) :
    ∃ w, Reaches Image.code t w ∧ w.pc = 0x8000d28c ∧ MB s u w k cnt P n x y c2 xp [e] ∧
      w.getReg .x1 = 0x80006abc ∧ w.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608 ∧
      w.getReg .x27 = xp ∧ HeapVec u w (w.getReg .x11) (w.getReg .x12) c1 ∧
      w.getReg .x13 = w.getReg .x19 ∧ w.getReg .x14 = w.getReg .x22 ∧
      ∀ T, TranscriptAt t (s.getReg .x12) T → TranscriptAt w (s.getReg .x12) T := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have C := h.ctx
  have sp := C.inv.sp
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006a60_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80006a60_keeps h₁
  have m₁ := b80006a60_mem_same h₁
  have pc₁ := b80006a60_pc_taken h₁ (C.capNe hpre (by decide))
  have I₁ := C.inv.same m₁ (k₁ .x2 (by decide))
  have sp₁ := I₁.sp
  have vp₁ : t₁.getMem (s.getReg .x2 - 1280) = P := by rw [m₁]; exact h.valuesPtr
  have hPb := C.heapP
  have hPe : P.toNat + 72 ≤ 2013265920 := hPb.2.2
  have hPs : 536870912 ≤ P.toNat := by
    have := hpre.heap.lo; have hb' := hPb.1; simp only [heapNext, heapStart] at this hb' ⊢; omega
  have hal := h.pal
  have hheap : ValidMemRange P 9 :=
    heapRange hal (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006a8c_spec pc₁ (by
    rv_eval [sp₁, vp₁]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hheap [hPs, hPe, hal]
      | addr_omega [hb1, hPs, hPe])
  have k₂ := b80006a8c_keeps h₂
  have fr₂ : DFrame t₁ t₂ fun a ↦ Within a (s.getReg .x2 - 160) 8 ∨ Within a P 24 := fun a ha ↦
    h₂.frame a (by
      rv_eval [sp₁, vp₁]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; addr_omega [hb1, hPs, hPe]))
  have stP : StepR s t₁ t₂ fun a ↦ Within a (s.getReg .x2 - 160) 8 ∨ Within a P 72 :=
    StepR.ofDFrame I₁.heap fr₂ (fun a ha ↦ ha.imp_right fun h ↦ by addr_omega [h, hPe])
      (fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb1, hPe])
      (k₂ .x2 (by decide))
  have st : StepR s t t₂ fun a ↦ Within a (s.getReg .x2 - 160) 8 ∨ Within a P 72 :=
    (StepR.same m₁ C.inv.heap (k₁ .x2 (by decide))).join stP
  have rg (r : Reg) (hr : r ∈ ([.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26] : List Reg)) :
      t₂.getReg r = t.getReg r := by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have m3 := b80006a8c_m3 h₂
  have m2 := b80006a8c_m2 h₂
  have m1 := b80006a8c_m1 h₂
  have m0 := b80006a8c_m_x2_1184 h₂
  rw [sp₁, show s.getReg .x2 - 1344 + 64 = s.getReg .x2 - 1280 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], vp₁] at m3 m2 m1
  rw [sp₁, show s.getReg .x2 - 1344 + 1184 = s.getReg .x2 - 160 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], k₁ .x24 (by decide), h.x24] at m0
  have hpush : eListAt t₂ P [e].length = [e] := by
    show [eAt t₂ (P + BitVec.ofNat 64 (24 * 0))] = [e]
    rw [show P + BitVec.ofNat 64 (24 * 0) = P by simp, ← he]
    refine congrArg (· :: []) (eAt_congr ?_ ?_ ?_)
    · rw [m3, b80006a60_x8 h₁, sp]
      exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    · rw [m2, b80006a60_x9 h₁, sp]
      exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    · rw [m1, b80006a60_x18 h₁, sp]
      exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have M := h.push hpre st (fun r hr ↦ rg r (mem_of_mem hr _)) (by rw [m0]; rfl) hpush
    (by simp)
  refine ⟨t₂, hr₁.trans hr₂, b80006a8c_pc h₂, M, b80006a8c_x1 h₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [b80006a8c_x10 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  · rw [k₂ .x27 (by decide), b80006a60_x27 h₁, h8]
  · rw [b80006a8c_x11 h₂, b80006a8c_x12 h₂, k₁ .x26 (by decide), k₁ .x21 (by decide)]
    exact hc1.keepP hpre h.hu h.hP st fun a ha ↦ ha.imp_left fun h ↦ by addr_omega [h, hb1]
  · rw [b80006a8c_x13 h₂, k₂ .x19 (by decide)]
  · rw [b80006a8c_x14 h₂, k₂ .x22 (by decide)]
  · intro T hT
    have hm := st.mono
    exact Inv.transcriptS hpre I₁ stP.heap (fr₂.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb1])
      · refine Or.inr (Or.inr ⟨?_, ?_⟩) <;> simp only [heapNext] at hPb hm ⊢ <;>
          addr_omega [ha, hPb.1, hPb.2.1, hm]) (TranscriptAt.same hpre C.inv m₁ hT)

/-- The second push and the third `multilinear_eval`'s arguments, from `0x80006ac4`. -/
theorem push1Step {s u t : MachineState} {k : Start} {cnt : E} {P : Word} {n : ℕ}
    {x y c2 : List E} {xp : Word} {v0 e : E} (hpre : BusBalancePre s)
    (h : MB s u t k cnt P n x y c2 xp [v0]) (hpc : t.pc = 0x80006ac4)
    (he : eAt t (s.getReg .x2 - BitVec.ofNat 64 600) = e) :
    ∃ w, Reaches Image.code t w ∧ w.pc = 0x8000d28c ∧ MB s u w k cnt P n x y c2 xp [v0, e] ∧
      w.getReg .x1 = 0x80006b1c ∧ w.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608 ∧
      w.getReg .x27 = t.getReg .x27 ∧ w.getReg .x21 = P ∧
      HeapVec u w (w.getReg .x11) (w.getReg .x12) c2 ∧
      w.getReg .x13 = w.getReg .x19 ∧ w.getReg .x14 = w.getReg .x22 ∧
      ∀ T, TranscriptAt t (s.getReg .x12) T → TranscriptAt w (s.getReg .x12) T := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have C := h.ctx
  have sp := C.inv.sp
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006ac4_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80006ac4_keeps h₁
  have m₁ := b80006ac4_mem_same h₁
  have pc₁ := b80006ac4_pc_taken h₁ (by rw [h.x24]; exact C.capNe hpre (by decide))
  have I₁ := C.inv.same m₁ (k₁ .x2 (by decide))
  have sp₁ := I₁.sp
  have pp₁ : t₁.getMem (s.getReg .x2 - 168) = P := by
    rw [m₁]
    have := C.ptr
    simp only [vecPtr] at this
    rw [show s.getReg .x2 - 176 + 8 = s.getReg .x2 - 168 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at this
    exact this
  have hPb := C.heapP
  have hPe : P.toNat + 72 ≤ 2013265920 := hPb.2.2
  have hPs : 536870912 ≤ P.toNat := by
    have := hpre.heap.lo; have hb' := hPb.1; simp only [heapNext, heapStart] at this hb' ⊢; omega
  have hal := h.pal
  have hheap : ValidMemRange P 9 :=
    heapRange hal (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006ae4_spec pc₁ (by
    rv_eval [sp₁, pp₁]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hheap [hPs, hPe, hal]
      | addr_omega [hb1, hPs, hPe])
  have k₂ := b80006ae4_keeps h₂
  have fr₂ : DFrame t₁ t₂ fun a ↦ Within a (s.getReg .x2 - 160) 8 ∨ Within a (P + 24) 24 :=
    fun a ha ↦ h₂.frame a (by
      rv_eval [sp₁, pp₁]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; addr_omega [hb1, hPs, hPe]))
  have stP : StepR s t₁ t₂ fun a ↦ Within a (s.getReg .x2 - 160) 8 ∨ Within a P 72 :=
    StepR.ofDFrame I₁.heap fr₂ (fun a ha ↦ ha.imp_right fun h ↦ by addr_omega [h, hPe])
      (fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb1, hPe])
      (k₂ .x2 (by decide))
  have st : StepR s t t₂ fun a ↦ Within a (s.getReg .x2 - 160) 8 ∨ Within a P 72 :=
    (StepR.same m₁ C.inv.heap (k₁ .x2 (by decide))).join stP
  have rg (r : Reg) (hr : r ∈ ([.x19, .x20, .x22, .x23, .x24, .x25, .x27] : List Reg)) :
      t₂.getReg r = t.getReg r := by
    rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have m3 := b80006ae4_m3 h₂
  have m2 := b80006ae4_m2 h₂
  have m1 := b80006ae4_m1 h₂
  have m0 := b80006ae4_m_x2_1184 h₂
  rw [sp₁, show s.getReg .x2 - 1344 + 1176 = s.getReg .x2 - 168 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], pp₁] at m3 m2 m1
  rw [sp₁, show s.getReg .x2 - 1344 + 1184 = s.getReg .x2 - 160 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m0
  have p0 (j : Nat) (hj : j + 8 ≤ 24) : t₂.getMem (P + BitVec.ofNat 64 j) =
      t.getMem (P + BitVec.ofNat 64 j) := by
    rw [fr₂ _ fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb1, hPe, hj], m₁]
  have hpush : eListAt t₂ P [v0, e].length = [v0, e] := by
    show [eAt t₂ (P + BitVec.ofNat 64 (24 * 0)), eAt t₂ (P + BitVec.ofNat 64 (24 * 1))] = [v0, e]
    have h0 : eAt t₂ (P + BitVec.ofNat 64 (24 * 0)) = v0 := by
      have hp := h.pushed
      change [eAt t (P + BitVec.ofNat 64 (24 * 0))] = [v0] at hp
      rw [← List.singleton_inj.mp hp]
      refine eAt_congr ?_ ?_ ?_
      · simpa using p0 0 (by omega)
      · rw [show P + BitVec.ofNat 64 (24 * 0) + 8 = P + BitVec.ofNat 64 8 by simp]
        exact p0 8 (by omega)
      · rw [show P + BitVec.ofNat 64 (24 * 0) + 16 = P + BitVec.ofNat 64 16 by simp]
        exact p0 16 (by omega)
    have h1 : eAt t₂ (P + BitVec.ofNat 64 (24 * 1)) = e := by
      rw [← he]
      refine eAt_congr ?_ ?_ ?_
      · rw [show P + BitVec.ofNat 64 (24 * 1) = P + 24 by rfl, m3, b80006ac4_x8 h₁, sp]
        exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
      · rw [show P + BitVec.ofNat 64 (24 * 1) + 8 = P + 32 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hPe], m2, b80006ac4_x9 h₁, sp]
        exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
      · rw [show P + BitVec.ofNat 64 (24 * 1) + 16 = P + 40 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hPe], m1, b80006ac4_x18 h₁, sp]
        exact congrArg t.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    rw [h0, h1]
  have M := h.push hpre st (fun r hr ↦ rg r (mem_of_mem hr _)) (by rw [m0]; rfl) hpush
    (by simp)
  refine ⟨t₂, hr₁.trans hr₂, b80006ae4_pc h₂, M, b80006ae4_x1 h₂, ?_, rg .x27 (by decide), ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [b80006ae4_x10 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  · rw [b80006ae4_x21 h₂, sp₁, show s.getReg .x2 - 1344 + 1176 = s.getReg .x2 - 168 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1], pp₁]
  · have e1 : t₂.getMem (s.getReg .x2 - 1112) = t.getMem (s.getReg .x2 - 1112) :=
      st.word hpre (fun y hy hs ↦ by rcases hs with hs | hs <;> addr_omega [hy, hs, hb1, hPe])
        (Or.inl (by addr_omega [hb1]))
    have := M.ch2
    rw [e1, rg .x25 (by decide)] at this
    rw [b80006ae4_x11 h₂, b80006ae4_x12 h₂, sp₁, show s.getReg .x2 - 1344 + 232 =
      s.getReg .x2 - 1112 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m₁, k₁ .x25 (by decide)]
    exact this
  · rw [b80006ae4_x13 h₂, k₂ .x19 (by decide)]
  · rw [b80006ae4_x14 h₂, k₂ .x22 (by decide)]
  · intro T hT
    have hm := st.mono
    exact Inv.transcriptS hpre I₁ stP.heap (fr₂.mono fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl (by addr_omega [ha, hb1])
      · refine Or.inr (Or.inr ⟨?_, ?_⟩) <;> simp only [heapNext] at hPb hm ⊢ <;>
          addr_omega [ha, hPb.1, hPb.2.1, hm, hPe]) (TranscriptAt.same hpre C.inv m₁ hT)

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
