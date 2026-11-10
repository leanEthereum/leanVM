import Rv64Verifier.Proofs.Bus.VbbGkrPush

/-!
# `verify_bus_balance`: an iteration's last push and `concat`

From `0x80006b24`: the third value pushed into `values` (`0x80006630`), `[y, x]` built at
`S - 608`, `concat` into `S - 248`, the registers reset and the layer count decreased
(`0x80006680`): the loop's invariant again (`ccStep`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem _root_.Rv64Verifier.Runtime.VecOk.move {t : MachineState} {a b : Word} {size align : Nat}
    (h : VecOk t b size align) (h0 : t.getMem a = t.getMem b)
    (h8 : t.getMem (a + 8) = t.getMem (b + 8)) (h16 : t.getMem (a + 16) = t.getMem (b + 16)) :
    VecOk t a size align := by
  obtain ⟨hr, hl⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [RawVecOk, vecPtr, vecCap] at hr ⊢; rw [h0, h8]; exact hr
  · simp only [vecLen, vecCap] at hl ⊢; rw [h0, h16]; exact hl

theorem stepOf_pos (n : ℕ) : 0 < stepOf n := by unfold stepOf; split <;> omega

/-- The third push, `concat`, and the loop's head or exit, from `0x80006b24`. -/
theorem ccStep (hCC : ConcatSpec) {bev : MachineState → Word → List E → Option E}
    {s u t : MachineState} {k : Start} {cnt : E} {P : Word} {n : ℕ} {x y c2 : List E} {xp : Word}
    {v0 v1 v2 : E} (hpre : BusBalancePre s) (h : MB s u t k cnt P n x y c2 xp [v0, v1])
    (hpc : t.pc = 0x80006b24) (he : eAt t (s.getReg .x2 - BitVec.ofNat 64 600) = v2)
    (h27 : t.getReg .x27 = xp) (h21 : t.getReg .x21 = P)
    (hvb : NewBuf s u P ((vecCap u (s.getReg .x2 - 176)).toNat * 24) 8) (hn : 0 < n)
    (htr : Tracks (prog bev s) (s.getReg .x12) s t
      (gkrLoopM (n - stepOf n) ⟨[v0, v1, v2], y ++ x⟩ >>= tail bev s k cnt)) :
    ∃ z, Reaches Image.code t z ∧ (Dead Image.code z ∨
      Loop bev s z k cnt P (z.getMem (s.getReg .x2 - 248)) (n - stepOf n) ⟨[v0, v1, v2], y ++ x⟩ ∧
        z.pc = if n - stepOf n = 0 then 0x80006c7c else 0x8000669c) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have C := h.ctx
  have sp := C.inv.sp
  have hu := h.hu
  have hPb := C.heapP
  have hPe : P.toNat + 72 ≤ 2013265920 := hPb.2.2
  have hPs : 536870912 ≤ P.toNat := by
    have := hpre.heap.lo; have hb' := hPb.1; simp only [heapNext, heapStart] at this hb' ⊢; omega
  have hal := h.pal
  have hheap : ValidMemRange P 9 :=
    heapRange hal (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have hbs : 536870912 ≤ heapNext s := by have := hpre.heap.lo; simp only [heapStart] at this; exact this
  -- `0x80006b24`: the third value in registers, `s3 := P`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006b24_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80006b24_keeps h₁
  have m₁ := b80006b24_mem_same h₁
  have pc₁ := b80006b24_pc_taken h₁ (C.capNe hpre (by decide))
  have I₁ := C.inv.same m₁ (k₁ .x2 (by decide))
  have sp₁ := I₁.sp
  have x19₁ : t₁.getReg .x19 = P := by rw [b80006b24_x19 h₁, h21]
  -- `0x80006630`: the push, `[y, x]` at `S - 608`
  obtain ⟨t₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006630_spec pc₁ (by
    rv_eval [sp₁, x19₁]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hheap [hPs, hPe, hal]
      | addr_omega [hb1, hPs, hPe])
  have k₂ := b80006630_keeps h₂
  have fr₂ : DFrame t₁ t₂ fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 608) 48 ∨
      Within a (s.getReg .x2 - 160) 8 ∨ Within a (P + 48) 24 := fun a ha ↦
    h₂.frame a (by
      rv_eval [sp₁, x19₁]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; addr_omega [hb1, hPs, hPe]))
  have hB : ∀ a, (Within a (s.getReg .x2 - BitVec.ofNat 64 608) 48 ∨
      Within a (s.getReg .x2 - 160) 8 ∨ Within a P 72) →
      Within a (s.getReg .x2 - 1344) 1240 ∨ Within a P 72 := fun a ha ↦ by
    rcases ha with ha | ha | ha
    · exact Or.inl (by addr_omega [ha, hb1])
    · exact Or.inl (by addr_omega [ha, hb1])
    · exact Or.inr ha
  have hBS : ∀ a, (Within a (s.getReg .x2 - BitVec.ofNat 64 608) 48 ∨
      Within a (s.getReg .x2 - 160) 8 ∨ Within a P 72) → Scratch s a ∨ Within a P 72 :=
    fun a ha ↦ by
    rcases ha with ha | ha | ha
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1])))))))
    · exact Or.inr ha
  have st₂ : StepR s t₁ t₂ fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 608) 48 ∨
      Within a (s.getReg .x2 - 160) 8 ∨ Within a P 72 :=
    StepR.ofDFrame I₁.heap fr₂ (fun a ha ↦ by
      rcases ha with ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (by addr_omega [ha, hPe])))
      (fun i hi hw ↦ by rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb1, hPe])
      (k₂ .x2 (by decide))
  have stB : StepR s t t₂ fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 608) 48 ∨
      Within a (s.getReg .x2 - 160) 8 ∨ Within a P 72 :=
    (StepR.same m₁ C.inv.heap (k₁ .x2 (by decide))).join st₂
  have C₂ := C.stepV hpre (stB.weaken hBS)
  have I₂ := C₂.inv
  have sp₂ := I₂.sp
  have nW (j : Nat) (hj : 1000 ≤ j ∧ j ≤ 1336 ∨ 696 ≤ j ∧ j ≤ 720) :
      t₂.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = t.getMem (s.getReg .x2 - BitVec.ofNat 64 j) := by
    rw [fr₂ _ fun i hi hw ↦ by rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb1, hPe, hj], m₁]
  have m744 := b80006630_m_x2_744 h₂
  have m752 := b80006630_m_x2_752 h₂
  have m760 := b80006630_m_x2_760 h₂
  have m768 := b80006630_m_x2_768 h₂
  have m776 := b80006630_m_x2_776 h₂
  have m736 := b80006630_m_x2_736 h₂
  have m3 := b80006630_m_x2_1184 h₂
  have m48 := b80006630_m_x19_48 h₂
  have m56 := b80006630_m_x19_56 h₂
  have m64 := b80006630_m_x19_64 h₂
  rw [sp₁, show s.getReg .x2 - 1344 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 624 =
    s.getReg .x2 - BitVec.ofNat 64 720 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m₁] at m736
  rw [sp₁, show s.getReg .x2 - 1344 + 744 = s.getReg .x2 - BitVec.ofNat 64 608 + 8 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 632 =
    s.getReg .x2 - BitVec.ofNat 64 712 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m₁] at m744
  rw [sp₁, show s.getReg .x2 - 1344 + 752 = s.getReg .x2 - BitVec.ofNat 64 608 + 16 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 640 =
    s.getReg .x2 - BitVec.ofNat 64 704 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m₁] at m752
  rw [sp₁, show s.getReg .x2 - 1344 + 760 = s.getReg .x2 - BitVec.ofNat 64 608 + 24 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 224 =
    s.getReg .x2 - BitVec.ofNat 64 1120 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m₁] at m760
  rw [sp₁, show s.getReg .x2 - 1344 + 768 = s.getReg .x2 - BitVec.ofNat 64 608 + 24 + 8 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], k₁ .x27 (by decide), h27] at m768
  rw [sp₁, show s.getReg .x2 - 1344 + 776 = s.getReg .x2 - BitVec.ofNat 64 608 + 24 + 16 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 200 =
    s.getReg .x2 - BitVec.ofNat 64 1144 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1], m₁] at m776
  rw [sp₁, show s.getReg .x2 - 1344 + 1184 = s.getReg .x2 - 160 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m3
  rw [x19₁, b80006b24_x8 h₁, sp, show s.getReg .x2 - 1344 + 744 = s.getReg .x2 - BitVec.ofNat 64 600 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m48
  rw [x19₁, b80006b24_x9 h₁, sp, show s.getReg .x2 - 1344 + 752 =
    s.getReg .x2 - BitVec.ofNat 64 600 + 8 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m56
  rw [x19₁, b80006b24_x18 h₁, sp, show s.getReg .x2 - 1344 + 760 =
    s.getReg .x2 - BitVec.ofNat 64 600 + 16 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m64
  -- the two parts
  have yv₂ := h.yv.keepP hpre hu h.hP stB hB (by omega) (by omega) fun y hy hs ↦ by
    rcases hs with hs | hs | hs <;> addr_omega [hy, hs, hb1, hPe]
  have xv₂ := h.xv.keepP hpre hu h.hP stB hB
  have y0 : t₂.getMem (s.getReg .x2 - BitVec.ofNat 64 720) = t.getMem (s.getReg .x2 - BitVec.ofNat 64 720) :=
    nW 720 (by omega)
  have y8 : t₂.getMem (s.getReg .x2 - BitVec.ofNat 64 720 + 8) =
      t.getMem (s.getReg .x2 - BitVec.ofNat 64 712) := by
    rw [show s.getReg .x2 - BitVec.ofNat 64 720 + 8 = s.getReg .x2 - BitVec.ofNat 64 712 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]; exact nW 712 (by omega)
  have y16 : t₂.getMem (s.getReg .x2 - BitVec.ofNat 64 720 + 16) =
      t.getMem (s.getReg .x2 - BitVec.ofNat 64 704) := by
    rw [show s.getReg .x2 - BitVec.ofNat 64 720 + 16 = s.getReg .x2 - BitVec.ofNat 64 704 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]; exact nW 704 (by omega)
  have left : VecOk t₂ (s.getReg .x2 - BitVec.ofNat 64 608) 24 8 :=
    yv₂.vec.move (m736.trans y0.symm) (m744.trans y8.symm) (m752.trans y16.symm)
  have right : VecOk t₂ (s.getReg .x2 - BitVec.ofNat 64 608 + 24) 24 8 := by
    have hb := xv₂.buf
    have hl := xv₂.le
    simp only [NewBuf] at hb
    refine ⟨?_, ?_⟩
    · simp only [RawVecOk, Buf, vecPtr, vecCap]
      rw [m768, m760]
      refine ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨?_, ?_⟩⟩
      · simp only [heapStart]; have := h'.1; omega
      · exact h'.2
    · simp only [vecLen, vecCap]
      rw [m776, m760]
      exact hl
  have ey : vecEs t₂ (s.getReg .x2 - BitVec.ofNat 64 608) = y := by
    rw [← yv₂.elems]
    simp only [vecEs, vecPtr, vecLen]
    rw [m744, m752, y8, y16]
  have ex : vecEs t₂ (s.getReg .x2 - BitVec.ofNat 64 608 + 24) = x := by
    rw [← xv₂.elems]
    simp only [vecEs, vecPtr, vecLen]
    rw [m768, m776]
    rfl
  -- `concat`
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := concatStack) hpre I₂ (k := 248) (n := 24)
    (by omega) (by omega) (by omega) (by decide)
  obtain ⟨p1, p2, p3⟩ := frameSlot (m := concatStack) hpre I₂ (k := 608) (n := 48)
    (by omega) (by omega) (by omega) (by decide)
  have h10₂ : t₂.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 248 := by
    rw [b80006630_x10 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have h11₂ : t₂.getReg .x11 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    rw [b80006630_x11 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have pre : ConcatPre t₂ := {
    heap := I₂.heap
    out := by rw [h10₂]; exact o1
    parts := by rw [h11₂]; exact p1
    left := by rw [h11₂]; exact left
    right := by rw [h11₂]; exact right
    stack := hpre.stack.sub 1344 sp₂ (by decide) (by decide) (by decide) (by decide) (by decide)
    outStack := by rw [h10₂]; exact o3
    partsStack := by rw [h11₂]; exact p3
    outFree := by rw [h10₂]; exact o2
    partsFree := by rw [h11₂]; exact p2 }
  obtain ⟨v, hrv, ⟨hpcv, hpv, post⟩ | hd⟩ :=
    hCC.call (hr₁.trans hr₂) (b80006630_pc h₂) pre
  swap
  · exact ⟨v, hrv, Or.inl hd⟩
  have hsl : stackLo t₂ concatStack = s.getReg .x2 - BitVec.ofNat 64 1616 := by
    simp only [stackLo, sp₂, show concatStack = 272 from rfl]
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have frv : DFrame t₂ v fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 248) 24 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 1616) 272 ∨ Within a nextAddr 8 ∨ Fresh t₂ v a :=
    post.frame.mono fun a ha ↦ by
      rw [h10₂, hsl, show concatStack = 272 from rfl] at ha; exact ha
  have stV : StepR s t₂ v (Within · (s.getReg .x2 - BitVec.ofNat 64 248) 24) :=
    ⟨frv.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ha))), post.heap, post.mono, hpv.reg .x2⟩
  have C₃ := C₂.step hpre (stV.weaken fun a ha ↦
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))))))
  have spv := C₃.inv.sp
  have hcv := post.value
  rw [h10₂, h11₂, ey, ex] at hcv
  -- `0x80006680`
  obtain ⟨z, hrz, hz⟩ := Sym.BlockSpec.reaches b80006680_spec
    (by rw [hpcv, returnAddress_eq, b80006630_x1 h₂]; decide) (by
      rv_eval [spv]
      and_intros <;> valid_access hval [hb1])
  have kz := b80006680_keeps hz
  have mz := b80006680_mem_same hz
  have Cz := C₃.step hpre (StepR.same mz C₃.inv.heap (kz .x2 (by decide)) (A := fun _ ↦ False)
    |>.weaken fun _ h ↦ h.elim)
  have vW (j : Nat) (hj : 1000 ≤ j ∧ j ≤ 1336 ∨ j = 160) :
      z.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = t₂.getMem (s.getReg .x2 - BitVec.ofNat 64 j) := by
    rw [mz, stV.word hpre (fun y hy hs ↦ by addr_omega [hy, hs, hb1, hj])
      (Or.inl (by addr_omega [hb1, hj]))]
  have rgz (r : Reg) (hr : r ∈ ([.x20, .x23, .x24] : List Reg)) : z.getReg r = t.getReg r := by
    rw [kz r (mem_of_mem hr _), hpv r (mem_of_mem hr _), k₂ r (mem_of_mem hr _),
      k₁ r (mem_of_mem hr _)]
  have x19z : z.getReg .x19 = P := by
    rw [kz .x19 (by decide), hpv .x19 (by decide), k₂ .x19 (by decide), x19₁]
  have hnz : heapNext z = heapNext v := by simp only [heapNext, mz]
  -- `values`
  have stAll : StepR s u z fun a ↦ Scratch s a ∨ Within a P 72 :=
    h.step.join ((stB.weaken hBS).join ((stV.weaken fun a ha ↦ Or.inl
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))))))).join
      (StepR.same mz C₃.inv.heap (kz .x2 (by decide)))))
  have capz : vecCap z (s.getReg .x2 - 176) = vecCap u (s.getReg .x2 - 176) :=
    stAll.word hpre (fun y hy hs ↦ by
      rcases hs with hs | hs
      · exact Scratch.miss hpre (j := 176) (n := 8) (by omega) (by omega)
          (by intro i h1 h2; omega) y hy hs
      · addr_omega [hy, hs, hb1, hPe]) (Or.inl (by addr_omega [hb1]))
  have hmz := stAll.mono
  have hbz : NewBuf s z P ((vecCap z (s.getReg .x2 - 176)).toNat * 24) 8 := by
    rw [capz]
    simp only [NewBuf] at hvb ⊢
    exact ⟨hvb.1, hvb.2.imp_right fun h' ↦ ⟨h'.1, by omega⟩⟩
  have lenz : vecLen z (s.getReg .x2 - 176) = 3 := by
    show z.getMem (s.getReg .x2 - 176 + 16) = 3
    rw [show s.getReg .x2 - 176 + 16 = s.getReg .x2 - BitVec.ofNat 64 160 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1], vW 160 (by omega)]
    exact m3
  have hp := h.pushed
  change [eAt t (P + BitVec.ofNat 64 (24 * 0)), eAt t (P + BitVec.ofNat 64 (24 * 1))] = [v0, v1]
    at hp
  have q0 := (List.cons.inj hp).1
  have q1 := (List.cons.inj (List.cons.inj hp).2).1
  have pw (i : Nat) (hi : i < 2) :
      eAt t₂ (P + BitVec.ofNat 64 (24 * i)) = eAt t (P + BitVec.ofNat 64 (24 * i)) :=
    eAt_congr ((fr₂ _ fun j hj hw ↦ by rcases hw with hw | hw | hw <;> addr_omega [hw, hj, hi, hb1, hPe]).trans (m₁ _))
      ((fr₂ _ fun j hj hw ↦ by rcases hw with hw | hw | hw <;> addr_omega [hw, hj, hi, hb1, hPe]).trans (m₁ _))
      ((fr₂ _ fun j hj hw ↦ by rcases hw with hw | hw | hw <;> addr_omega [hw, hj, hi, hb1, hPe]).trans (m₁ _))
  have e5 : eAt t₂ (P + BitVec.ofNat 64 (24 * 2)) = v2 := by
    rw [← he]
    refine eAt_congr ?_ ?_ ?_
    · rw [show P + BitVec.ofNat 64 (24 * 2) = P + 48 from rfl]; exact m48
    · rw [show P + BitVec.ofNat 64 (24 * 2) + 8 = P + 56 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hPe]]; exact m56
    · rw [show P + BitVec.ofNat 64 (24 * 2) + 16 = P + 64 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hPe]]; exact m64
  have e3 : eListAt t₂ P 3 = [v0, v1, v2] := by
    show [eAt t₂ (P + BitVec.ofNat 64 (24 * 0)), eAt t₂ (P + BitVec.ofNat 64 (24 * 1)),
      eAt t₂ (P + BitVec.ofNat 64 (24 * 2))] = [v0, v1, v2]
    rw [pw 0 (by omega), pw 1 (by omega), q0, q1, e5]
  have ez : eListAt z P 3 = [v0, v1, v2] := by
    rw [← e3, ← stV.eListP hpre (fun a ha ↦ by addr_omega [ha, hb1])
      ⟨C₂.heapP.1, C₂.heapP.2.1⟩ (Nat.le_refl 3)]
    exact eListAt_congr fun i _ ↦ eAt_congr (mz _) (mz _) (mz _)
  have Vz : NewVecE s z (s.getReg .x2 - 176) [v0, v1, v2] := by
    have cz := Cz.cap
    have pz := Cz.ptr
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simp only [RawVecOk, Buf]
      rw [pz]
      have hb := hbz
      simp only [NewBuf] at hb
      refine ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨?_, h'.2⟩⟩
      simp only [heapStart]; have := h'.1; omega
    · rw [lenz]; exact cz
    · rw [pz]; exact hbz
    · simp only [vecEs]
      rw [pz, lenz]
      exact ez
  -- the point
  have Pz : NewVecR s z (z.getMem (s.getReg .x2 - 248)) (z.getReg .x27) (z.getReg .x21) (y ++ x) := by
    have hb := hcv.buf
    have hl := hcv.vec.len
    have hel := hcv.elems
    have hm2 := I₂.mono
    rw [b80006680_x27 hz, b80006680_x21 hz, spv, show s.getReg .x2 - 1344 + 1104 =
      s.getReg .x2 - BitVec.ofNat 64 248 + 8 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
      show s.getReg .x2 - 1344 + 1112 = s.getReg .x2 - BitVec.ofNat 64 248 + 16 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], mz]
    simp only [NewBuf, vecPtr, vecCap, vecLen, vecEs] at hb hl hel
    refine ⟨hl, ⟨hb.1, hb.2.imp_right fun h' ↦ ⟨by omega, by rw [hnz]; exact h'.2⟩⟩, ?_⟩
    rw [← hel]
    exact eListAt_congr fun i _ ↦ eAt_congr (mz _) (mz _) (mz _)
  have hyx : y ++ x ≠ [] := by
    have hy : y ≠ [] := List.ne_nil_of_length_pos (h.ylen ▸ stepOf_pos n)
    simp only [ne_eq, List.append_eq_nil_iff, not_and]
    exact fun h0 ↦ absurd h0 hy
  have pLo := Pz.ptrLo_ne hyx
  -- the layers left
  have rgv (r : Reg) (hr : r ∈ ([.x20, .x23, .x24] : List Reg)) : v.getReg r = t.getReg r := by
    rw [hpv r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have hl1128 : (v.getMem (v.getReg .x2 + (216 : Word))).toNat = n := by
    rw [spv, show s.getReg .x2 - 1344 + 216 = s.getReg .x2 - BitVec.ofNat 64 1128 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1], stV.word hpre (fun y hy hs ↦ by
        addr_omega [hy, hs, hb1]) (Or.inl (by addr_omega [hb1])), nW 1128 (by omega)]
    exact h.layers
  have h23 : (v.getReg .x23).toNat = stepOf n := by rw [rgv .x23 (by decide)]; exact h.x23
  have hst := stepOf_le n
  have hsn : stepOf n ≤ n := by unfold stepOf; split <;> omega
  have hx25 : (z.getReg .x25).toNat = n - stepOf n := by
    rw [b80006680_x25 hz, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), hl1128, h23]
  refine ⟨z, hrv.trans hrz, Or.inr ⟨{
    inv := Cz.inv
    kept := Cz.kept
    fence := Cz.fence
    x9 := b80006680_x9 hz
    x19 := x19z
    x20 := by rw [rgz .x20 (by decide)]; exact h.x20
    x22 := by rw [b80006680_x22 hz, rgv .x20 (by decide), h.x20]
    x24 := by rw [rgz .x24 (by decide)]; exact h.x24
    x25 := hx25
    cnt2 := Cz.cnt2
    pushPtr := Cz.pushPtr
    ptr := Cz.ptr
    point := Pz
    values := Vz
    len := rfl
    tracks := htr.keep fun T hT ↦ by
      have T₁ := TranscriptAt.same hpre C.inv m₁ hT
      have hm := stB.mono
      have T₂ := Inv.transcriptS hpre I₁ st₂.heap (fr₂.mono fun a ha ↦ by
        rcases ha with ha | ha | ha
        · exact Or.inl (by addr_omega [ha, hb1])
        · exact Or.inl (by addr_omega [ha, hb1])
        · refine Or.inr (Or.inr ⟨?_, ?_⟩) <;> simp only [heapNext] at hPb hm ⊢ <;>
            addr_omega [ha, hPb.1, hPb.2.1, hm, hPe]) T₁
      have T₃ := I₂.transcript hpre post.heap (frv.mono fun a ha ↦ by
        rcases ha with ha | ha | ha | ha
        · exact Or.inl (by addr_omega [ha, hb1])
        · exact Or.inl (by addr_omega [ha, hb1])
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr ha)) T₂
      exact TranscriptAt.same hpre C₃.inv mz T₃
    pointLo := pLo }, ?_⟩⟩
  by_cases h0 : n - stepOf n = 0
  · simp only [h0, ↓reduceIte]
    exact b80006680_pc_taken hz (by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), hl1128, h23]
      simpa using h0)
  · simp only [h0, ↓reduceIte]
    exact b80006680_pc_not_taken hz fun he0 ↦ h0 (by
      have := congrArg BitVec.toNat he0
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega), hl1128, h23] at this
      simpa using this)

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
