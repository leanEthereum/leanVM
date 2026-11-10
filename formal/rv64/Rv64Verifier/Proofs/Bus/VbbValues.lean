import Rv64Verifier.Proofs.Bus.VbbHead

/-!
# `verify_bus_balance`: the GKR loop's start, the first `next_scalar` to `0x80006610`

`shared` and `count`, each `next_scalar` into `S - 608` (an `Err` exits through `0x80007104`),
`shared`'s limbs kept in `s11`, `s5`, `s0`, `count`'s at `S - 1224`, `S - 1232` and in `s1`; then
`values = vec![shared, shared, count]` in a new 72-byte buffer, its `Vec` at `S - 176`.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem eAt_eOf3 (u : MachineState) (a : Word) :
    eAt u a = eOf3 (u.getMem a) (u.getMem (a + 8)) (u.getMem (a + 16)) := rfl

/-- A block that writes only `B`, in `A`, apart from `NEXT`. -/
theorem StepR.ofDFrame {s v w : MachineState} {A B : Word → Prop} (hh : HeapOk v)
    (hf : DFrame v w B) (hA : ∀ a, B a → A a) (hn : ∀ i < 8, ¬ B (nextAddr + BitVec.ofNat 64 i))
    (sp : w.getReg .x2 = v.getReg .x2) : StepR s v w A := by
  have he : heapNext w = heapNext v := by simp only [heapNext]; rw [hf nextAddr hn]
  exact ⟨hf.mono fun a ha ↦ Or.inl (hA a ha), ⟨he ▸ hh.lo, he ▸ hh.hi⟩, he.ge, sp⟩

/-- The first `next_scalar`, to the second's entry. -/
structure Shared (s u w : MachineState) : Prop where
  inv : Inv s w
  regs : ∀ r ∈ ([.x9, .x18, .x19, .x20, .x22, .x24, .x25] : List Reg), w.getReg r = u.getReg r
  x1 : w.getReg .x1 = 0x80006580
  x10 : w.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608
  x11 : w.getReg .x11 = s.getReg .x12
  countLen : w.getMem (s.getReg .x2 - 1248) = u.getReg .x8
  step : StepR s u w fun a ↦ Within a (s.getReg .x2 - 608) 32 ∨ Within a (s.getReg .x2 - 1248) 8

theorem sharedStep (hN : NextScalarSpec) {bev : MachineState → Word → List E → Option E}
    {s u : MachineState} {K : E → TM BusResultRust} (hpre : BusBalancePre s) (h : Inv s u)
    (hpc : u.pc = 0x8000c720) (hx1 : u.getReg .x1 = 0x80006558)
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608) (h11 : u.getReg .x11 = s.getReg .x12)
    (hx18 : u.getReg .x18 = s.getReg .x10) (hx20 : u.getReg .x20 = s.getReg .x12)
    (htr : Tracks (prog bev s) (s.getReg .x12) s u (TM.nextScalar >>= K)) :
    ∃ w, Reaches Image.code u w ∧ (Done bev s w ∨ Dead Image.code w ∨
      (w.pc = 0x8000c720 ∧ Shared s u w ∧ Tracks (prog bev s) (s.getReg .x12) s w
        (K (eOf3 (w.getReg .x27) (w.getReg .x21) (w.getReg .x8))))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  obtain ⟨v, hrv, ⟨hpcv, hp, st, J, herr, hok⟩ | hd⟩ :=
    nextScalarCall hN hpre h (Reaches.refl u) hpc h10 h11 (by omega) (by omega) (by omega)
  swap
  · exact ⟨v, hrv, Or.inr (Or.inl hd)⟩
  have sp := J.sp
  have hpc' : v.pc = 0x80006558 := by rw [hpcv, returnAddress_eq, hx1]; decide
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006558_spec hpc' (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80006558_keeps h₁
  have m₁ := b80006558_mem_same h₁
  have I₁ := J.same m₁ (k₁ .x2 (by decide))
  have e736 : s.getReg .x2 - 1344 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x18₁ : u₁.getReg .x18 = s.getReg .x10 := by
    rw [k₁ .x18 (by decide), hp .x18 (by decide), hx18]
  by_cases ht : v.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0
  swap
  · have hpc₁ := b80006558_pc_taken h₁ (by rw [sp, e736]; exact ht)
    obtain ⟨t, hrt, hdone⟩ := errDone (bev := bev) hpre I₁ x18₁ hpc₁ (htr.fail (herr ht))
    exact ⟨t, hrv.trans (hr₁.trans hrt), Or.inl hdone⟩
  have hpc₁ := b80006558_pc_not_taken h₁ (by rw [sp, e736]; exact ht)
  have x20₁ : u₁.getReg .x20 = s.getReg .x12 := by
    rw [k₁ .x20 (by decide), hp .x20 (by decide), hx20]
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006568_spec hpc₁ (by
    rv_eval [sp, k₁ .x2 (by decide)]
    and_intros <;> valid_access hval [hb1])
  have k₂ := b80006568_keeps h₂
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 1344 := I₁.sp
  have fr₂ := b80006568_frame h₂ (by rw [sp₁]; addr_omega [hb1])
  rw [sp₁, show s.getReg .x2 - 1344 + 96 = s.getReg .x2 - 1248 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at fr₂
  have st₂ : StepR s u₁ u₂ (Within · (s.getReg .x2 - 1248) 8) :=
    StepR.ofMemFrame I₁.heap fr₂ (fun _ h ↦ h) (by addr_omega [hb1]) (k₂ .x2 (by decide))
  have I₂ := I₁.afterR hpre (frameW_slot hpre (k := 1248) (n := 8) (by omega) (by omega)) st₂
  have if₀ := inFrame hpre (k := 608) (n := 32) (by omega) (by omega)
  -- the scalar's limbs
  have w0 : u₂.getReg .x27 = v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 8) := by
    rw [k₂ .x27 (by decide), b80006558_x27 h₁, sp]
    exact congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have w1 : u₂.getReg .x21 = v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 8 + 8) := by
    rw [k₂ .x21 (by decide), b80006558_x21 h₁, sp]
    exact congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have w2 : u₂.getReg .x8 = v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 8 + 16) := by
    rw [b80006568_x8 h₂, sp₁, m₁]
    exact congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  refine ⟨u₂, hrv.trans (hr₁.trans hr₂), Or.inr (Or.inr ⟨b80006568_pc h₂, {
    inv := I₂
    regs := fun r hr ↦ by
      rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _), hp r (mem_of_mem hr _)]
    x1 := b80006568_x1 h₂
    x10 := by rw [b80006568_x10 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x11 := (b80006568_x11 h₂).trans x20₁
    countLen := by
      have := b80006568_m_x2_96 h₂
      rw [sp₁, show s.getReg .x2 - 1344 + 96 = s.getReg .x2 - 1248 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at this
      rw [this, k₁ .x8 (by decide), hp .x8 (by decide)]
    step := ((st.toR.trans (StepR.same m₁ J.heap (k₁ .x2 (by decide)))).trans st₂).weaken
      fun a ha ↦ by
        rcases ha with (ha | ha) | ha
        · exact Or.inl ha
        · exact False.elim ha
        · exact Or.inr ha }, ?_⟩)⟩
  rw [w0, w1, w2, ← eAt_eOf3]
  refine (htr.bind (hok ht)).keep fun T hT ↦ ?_
  exact I₁.transcript hpre I₂.heap ((DFrame.of_memFrame fr₂).mono fun a ha ↦
    Or.inl (by addr_omega [ha, hb1])) (TranscriptAt.same hpre J m₁ hT)

/-- The second `next_scalar`, to the allocator's entry. -/
structure Count (s w y : MachineState) : Prop where
  inv : Inv s y
  regs : ∀ r ∈ ([.x8, .x18, .x19, .x20, .x21, .x22, .x24, .x25, .x27] : List Reg),
    y.getReg r = w.getReg r
  x1 : y.getReg .x1 = 0x800065c0
  x10 : y.getReg .x10 = 8
  x11 : y.getReg .x11 = 72
  pushLen : y.getMem (s.getReg .x2 - 1264) = w.getReg .x9
  layout : y.getMem (s.getReg .x2 - 1240) = w.getReg .x19
  step : StepR s w y fun a ↦ Within a (s.getReg .x2 - 608) 32 ∨
    Within a (s.getReg .x2 - 1264) 8 ∨ Within a (s.getReg .x2 - 1240) 24

theorem countStep (hN : NextScalarSpec) {bev : MachineState → Word → List E → Option E}
    {s w : MachineState} {K : E → TM BusResultRust} (hpre : BusBalancePre s) (h : Inv s w)
    (hpc : w.pc = 0x8000c720) (hx1 : w.getReg .x1 = 0x80006580)
    (h10 : w.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608) (h11 : w.getReg .x11 = s.getReg .x12)
    (hx18 : w.getReg .x18 = s.getReg .x10)
    (htr : Tracks (prog bev s) (s.getReg .x12) s w (TM.nextScalar >>= K)) :
    ∃ y, Reaches Image.code w y ∧ (Done bev s y ∨ Dead Image.code y ∨
      (y.pc = 0x80000284 ∧ Count s w y ∧ Tracks (prog bev s) (s.getReg .x12) s y
        (K (eOf3 (y.getMem (s.getReg .x2 - 1224)) (y.getMem (s.getReg .x2 - 1232))
          (y.getReg .x9))))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  obtain ⟨v, hrv, ⟨hpcv, hp, st, J, herr, hok⟩ | hd⟩ :=
    nextScalarCall hN hpre h (Reaches.refl w) hpc h10 h11 (by omega) (by omega) (by omega)
  swap
  · exact ⟨v, hrv, Or.inr (Or.inl hd)⟩
  have sp := J.sp
  have hpc' : v.pc = 0x80006580 := by rw [hpcv, returnAddress_eq, hx1]; decide
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006580_spec hpc' (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80006580_keeps h₁
  have m₁ := b80006580_mem_same h₁
  have I₁ := J.same m₁ (k₁ .x2 (by decide))
  have e736 : s.getReg .x2 - 1344 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  by_cases ht : v.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0
  swap
  · have hpc₁ := b80006580_pc_not_taken h₁ (by rw [sp, e736]; exact ht)
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006590_spec hpc₁ trivial
    have m₂ := b80006590_mem_same h₂
    have I₂ := I₁.same m₂ ((b80006590_keeps h₂) .x2 (by decide))
    obtain ⟨t, hrt, hdone⟩ := errDone (bev := bev) hpre I₂
      (by rw [b80006590_keeps h₂ .x18 (by decide), k₁ .x18 (by decide), hp .x18 (by decide), hx18])
      (b80006590_pc h₂) (htr.fail (herr ht))
    exact ⟨t, hrv.trans (hr₁.trans (hr₂.trans hrt)), Or.inl hdone⟩
  have hpc₁ := b80006580_pc_taken h₁ (by rw [sp, e736]; exact ht)
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 1344 := I₁.sp
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000659c_spec hpc₁ (by
    rv_eval [sp₁]
    and_intros <;> valid_access hval [hb1])
  have k₂ := b8000659c_keeps h₂
  have fr₂ : DFrame u₁ u₂ fun a ↦ Within a (s.getReg .x2 - 1264) 8 ∨
      Within a (s.getReg .x2 - 1240) 24 := fun a ha ↦
    h₂.frame a (by
      rv_eval [sp₁]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; addr_omega [hb1]))
  have st₂ : StepR s u₁ u₂ fun a ↦ Within a (s.getReg .x2 - 1264) 8 ∨
      Within a (s.getReg .x2 - 1240) 24 :=
    StepR.ofDFrame I₁.heap fr₂ (fun _ h ↦ h) (fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hb1]) (k₂ .x2 (by decide))
  have I₂ := I₁.afterR hpre (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb1]) st₂
  have c0 : u₂.getMem (s.getReg .x2 - 1224) = v.getMem (s.getReg .x2 - 1344 + 744) := by
    have := b8000659c_m_x2_120 h₂
    rw [sp₁, show s.getReg .x2 - 1344 + 120 = s.getReg .x2 - 1224 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1], b80006580_x11 h₁, sp] at this
    exact this
  have c1 : u₂.getMem (s.getReg .x2 - 1232) = v.getMem (s.getReg .x2 - 1344 + 752) := by
    have := b8000659c_m_x2_112 h₂
    rw [sp₁, show s.getReg .x2 - 1344 + 112 = s.getReg .x2 - 1232 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1], b80006580_x12 h₁, sp] at this
    exact this
  have c2 : u₂.getReg .x9 = v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 8 + 16) := by
    rw [b8000659c_x9 h₂, sp₁, m₁]
    exact congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have hcnt : eOf3 (u₂.getMem (s.getReg .x2 - 1224)) (u₂.getMem (s.getReg .x2 - 1232))
      (u₂.getReg .x9) = eAt v (s.getReg .x2 - BitVec.ofNat 64 608 + 8) := by
    rw [eAt_eOf3, c2]
    rw [c0, c1, show s.getReg .x2 - 1344 + 744 = s.getReg .x2 - BitVec.ofNat 64 608 + 8 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
      show s.getReg .x2 - 1344 + 752 = s.getReg .x2 - BitVec.ofNat 64 608 + 8 + 8 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
  refine ⟨u₂, hrv.trans (hr₁.trans hr₂), Or.inr (Or.inr ⟨b8000659c_pc h₂, {
    inv := I₂
    regs := fun r hr ↦ by
      rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _), hp r (mem_of_mem hr _)]
    x1 := b8000659c_x1 h₂
    x10 := b8000659c_x10 h₂
    x11 := b8000659c_x11 h₂
    pushLen := by
      have := b8000659c_m_x2_80 h₂
      rw [sp₁, show s.getReg .x2 - 1344 + 80 = s.getReg .x2 - 1264 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1], k₁ .x9 (by decide), hp .x9 (by decide)] at this
      exact this
    layout := by
      have := b8000659c_m_x2_104 h₂
      rw [sp₁, show s.getReg .x2 - 1344 + 104 = s.getReg .x2 - 1240 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1], k₁ .x19 (by decide), hp .x19 (by decide)] at this
      exact this
    step := ((st.toR.trans (StepR.same m₁ J.heap (k₁ .x2 (by decide)))).trans st₂).weaken
      fun a ha ↦ by
        rcases ha with (ha | ha) | ha
        · exact Or.inl ha
        · exact False.elim ha
        · exact Or.inr ha }, ?_⟩)⟩
  rw [hcnt]
  refine (htr.bind (hok ht)).keep fun T hT ↦ ?_
  exact I₁.transcript hpre I₂.heap (fr₂.mono fun a ha ↦
    Or.inl (by rcases ha with ha | ha <;> addr_omega [ha, hb1])) (TranscriptAt.same hpre J m₁ hT)

/-- The allocation of `values`' buffer and its `Vec` at `S - 176`, to the depth's test. -/
structure Values (s y z : MachineState) : Prop where
  inv : Inv s z
  regs : ∀ r ∈ ([.x8, .x9, .x18, .x20, .x21, .x22, .x24, .x25, .x27] : List Reg),
    z.getReg r = y.getReg r
  x11 : z.getReg .x11 = y.getMem (s.getReg .x2 - 1224)
  x12 : z.getReg .x12 = y.getMem (s.getReg .x2 - 1232)
  x13 : z.getReg .x13 = y.getReg .x9
  x19 : z.getReg .x19 = vecPtr z (s.getReg .x2 - 176)
  above : heapNext y ≤ (vecPtr z (s.getReg .x2 - 176)).toNat
  out : z.getMem (s.getReg .x2 - 1312) = y.getReg .x18
  values : NewVecE s z (s.getReg .x2 - 176)
    [eOf3 (y.getReg .x27) (y.getReg .x21) (y.getReg .x8),
      eOf3 (y.getReg .x27) (y.getReg .x21) (y.getReg .x8),
      eOf3 (y.getMem (s.getReg .x2 - 1224)) (y.getMem (s.getReg .x2 - 1232)) (y.getReg .x9)]
  step : StepR s y z fun a ↦ Within a (s.getReg .x2 - 1312) 8 ∨ Within a (s.getReg .x2 - 176) 24
  branch : (z.pc = 0x80006b54 ∧ z.getReg .x25 = 0) ∨ (z.pc = 0x80006614 ∧ z.getReg .x25 ≠ 0)
  transcript : ∀ T, TranscriptAt y (s.getReg .x12) T → TranscriptAt z (s.getReg .x12) T

theorem valuesStep (hA : AllocSpec) {s y : MachineState} (hpre : BusBalancePre s) (h : Inv s y)
    (hpc : y.pc = 0x80000284) (hx1 : y.getReg .x1 = 0x800065c0) (h10 : y.getReg .x10 = 8)
    (h11 : y.getReg .x11 = 72) :
    ∃ z, Reaches Image.code y z ∧ (Dead Image.code z ∨ Values s y z) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := allocCall hA h (Reaches.refl y) hpc h10
  swap
  · exact ⟨v, hrv, Or.inl hd⟩
  have hpc' : v.pc = 0x800065c0 := by rw [hpcv, returnAddress_eq, hx1]; decide
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800065c0_spec hpc' trivial
  have k₁ := b800065c0_keeps h₁
  have m₁ := b800065c0_mem_same h₁
  by_cases hz : v.getReg .x10 = 0
  · obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800065c4_spec
      (b800065c0_pc_not_taken h₁ hz) trivial
    exact ⟨u₂, hrv.trans (hr₁.trans hr₂), Or.inl (dead_of_fetch (by
      rw [b800065c4_pc h₂]; exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  have hpc₁ := b800065c0_pc_taken h₁ hz
  have al : (v.getReg .x10).toNat % 8 = 0 := by have := post.aligned; rw [h10] at this; exact this
  have ab := post.above
  have nx : heapNext v = (v.getReg .x10).toNat + 72 := by
    have := post.next; rw [h11] at this; exact this
  have hhv := post.heap.hi
  have hly := h.heap.lo
  have hmo := h.mono
  have x10₁ : u₁.getReg .x10 = v.getReg .x10 := k₁ .x10 (by decide)
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 1344 := by
    rw [k₁ .x2 (by decide), hp .x2 (by decide), h.sp]
  simp only [heapNext, heapEnd, heapStart] at nx hhv hly ab hmo
  have hlo : 536870912 ≤ (v.getReg .x10).toNat := by omega
  have hhi : (v.getReg .x10).toNat + 72 ≤ 2013265920 := by omega
  have hheap : ValidMemRange (v.getReg .x10) 9 :=
    heapRange al (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  obtain ⟨z, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800065c8_spec hpc₁ (by
    rv_eval [sp₁, x10₁]
    and_intros <;> first
      | valid_access hval [hb1]
      | valid_access hheap [hlo, hhi, al]
      | addr_omega [hb1, hlo, hhi])
  have k₂ := b800065c8_keeps h₂
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have fr : DFrame u₁ z fun a ↦ Within a (s.getReg .x2 - 1312) 8 ∨
      Within a (s.getReg .x2 - 176) 24 ∨ Within a (v.getReg .x10) 72 := fun a ha ↦
    h₂.frame a (by
      rv_eval [sp₁, x10₁]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; addr_omega [hb1, hlo, hhi]))
  have hnz : z.getMem nextAddr = v.getMem nextAddr := by
    rw [fr nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hx, hb1, hlo, hhi], m₁]
  have hmem (a : Word) (ha : ∀ i < 8, ¬ (Within (a + BitVec.ofNat 64 i) (s.getReg .x2 - 1312) 8 ∨
      Within (a + BitVec.ofNat 64 i) (s.getReg .x2 - 176) 24 ∨
      Within (a + BitVec.ofNat 64 i) (v.getReg .x10) 72)) (hn : a ≠ nextAddr) :
      z.getMem a = y.getMem a := by
    rw [fr a ha, m₁, post.mem a hn]
  have hn₂ : heapNext z = heapNext v := by simp only [heapNext, hnz]
  have F₀ : DFrame y z fun a ↦ Within a (s.getReg .x2 - 1312) 8 ∨
      Within a (s.getReg .x2 - 176) 24 ∨ Within a nextAddr 8 ∨ Fresh y z a :=
    fun a ha ↦ hmem a (fun i hi hw ↦ ha i hi (by
        rcases hw with hw | hw | hw
        · exact Or.inl hw
        · exact Or.inr (Or.inl hw)
        · refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩)) <;> simp only [heapNext, hnz] <;>
            addr_omega [hw, ab, nx, hhi]))
      (fun he ↦ ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; exact Or.inr (Or.inr (Or.inl (by addr_omega [])))))
  have F : DFrame y z fun a ↦ (Within a (s.getReg .x2 - 1312) 8 ∨
      Within a (s.getReg .x2 - 176) 24) ∨ Within a (s.getReg .x12 + 8) 344 ∨
      Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨ Fresh y z a :=
    F₀.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (Or.inl ha)
      · exact Or.inl (Or.inr ha)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ha)))
  have st : StepR s y z fun a ↦ Within a (s.getReg .x2 - 1312) 8 ∨
      Within a (s.getReg .x2 - 176) 24 :=
    ⟨F, ⟨by rw [hn₂]; exact post.heap.lo, by rw [hn₂]; exact post.heap.hi⟩,
      by simp only [heapNext, hnz]; omega,
      by rw [k₂ .x2 (by decide), k₁ .x2 (by decide), hp .x2 (by decide)]⟩
  have ry (r : Reg) (hr : r ∈ calleeSaved) : u₁.getReg r = y.getReg r := by
    rw [k₁ r (mem_of_mem hr _), hp r hr]
  have ym (a : Word) (hn : a ≠ nextAddr) : u₁.getMem a = y.getMem a := by rw [m₁, post.mem a hn]
  have ea (a b : Word) (hk : b.toNat ≤ 1344) (ha : a.toNat = (s.getReg .x2).toNat - 1344 + b.toNat) :
      z.getMem a = z.getMem (u₁.getReg .x2 + b) := by
    rw [sp₁]
    exact congrArg z.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1, ha, hk])
  have hptr : vecPtr z (s.getReg .x2 - 176) = v.getReg .x10 := by
    rw [vecPtr, ea _ 1176 (by decide) (by addr_omega [hb1]), b800065c8_m_x2_1176 h₂, x10₁]
  have hcap : vecCap z (s.getReg .x2 - 176) = 3 := by
    rw [vecCap, ea _ 1168 (by decide) (by addr_omega [hb1]), b800065c8_m_x2_1168 h₂]
  have hlen : vecLen z (s.getReg .x2 - 176) = 3 := by
    rw [vecLen, ea _ 1184 (by decide) (by addr_omega [hb1]), b800065c8_m_x2_1184 h₂]
  have h3 : (3 : Word).toNat = 3 := rfl
  have hnzv : heapNext z = (v.getReg .x10).toNat + 72 := by
    rw [hn₂]; simp only [heapNext]; exact nx
  have c0 : y.getMem (s.getReg .x2 - 1224) = u₁.getMem (u₁.getReg .x2 + 120) := by
    rw [sp₁, ym _ (by addr_omega [hb1])]
    exact congrArg y.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have c1 : y.getMem (s.getReg .x2 - 1232) = u₁.getMem (u₁.getReg .x2 + 112) := by
    rw [sp₁, ym _ (by addr_omega [hb1])]
    exact congrArg y.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  refine ⟨z, hrv.trans (hr₁.trans hr₂), Or.inr {
    inv := h.afterR hpre (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb1]) st
    regs := fun r hr ↦ by rw [k₂ r (mem_of_mem hr _), ry r (mem_of_mem hr _)]
    x11 := by rw [b800065c8_x11 h₂, c0]
    x12 := by rw [b800065c8_x12 h₂, c1]
    x13 := by rw [b800065c8_x13 h₂, ry .x9 (by decide)]
    x19 := by rw [b800065c8_x19 h₂, hptr, x10₁]
    above := by rw [hptr]; simp only [heapNext]; omega
    out := by
      rw [ea _ 32 (by decide) (by addr_omega [hb1]), b800065c8_m_x2_32 h₂,
        ry .x18 (by decide)]
    values := ⟨⟨⟨by rw [hptr]; exact al, Or.inr ⟨by rw [hptr]; simp only [heapStart]; omega,
        by rw [hptr, hcap, h3, hnzv]⟩⟩, by rw [hlen, hcap]⟩,
      ⟨by rw [hptr]; exact al, Or.inr ⟨by rw [hptr]; simp only [heapNext]; omega,
        by rw [hptr, hcap, h3, hnzv]⟩⟩, ?_⟩
    step := st
    branch := by
      by_cases h25 : u₁.getReg .x25 = 0
      · exact Or.inl ⟨b800065c8_pc_taken h₂ h25, by rw [k₂ .x25 (by decide)]; exact h25⟩
      · exact Or.inr ⟨b800065c8_pc_not_taken h₂ h25, by rw [k₂ .x25 (by decide)]; exact h25⟩
    transcript := fun T hT ↦ h.transcript hpre st.heap (F₀.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inl (by addr_omega [ha, hb1])
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr ha)) hT }⟩
  rw [vecEs, hptr, hlen, h3, eListAt_three, eAt_eOf3, eAt_eOf3, eAt_eOf3, ← x10₁]
  have p32 : u₁.getReg .x10 + 24 + 8 = u₁.getReg .x10 + 32 := by rw [BitVec.add_assoc]; rfl
  have p40 : u₁.getReg .x10 + 24 + 16 = u₁.getReg .x10 + 40 := by rw [BitVec.add_assoc]; rfl
  have p56 : u₁.getReg .x10 + 48 + 8 = u₁.getReg .x10 + 56 := by rw [BitVec.add_assoc]; rfl
  have p64 : u₁.getReg .x10 + 48 + 16 = u₁.getReg .x10 + 64 := by rw [BitVec.add_assoc]; rfl
  rw [p32, p40, p56, p64, b800065c8_m_x10_0 h₂, b800065c8_m_x10_8 h₂, b800065c8_m_x10_16 h₂,
    b800065c8_m_x10_24 h₂, b800065c8_m_x10_32 h₂, b800065c8_m_x10_40 h₂, b800065c8_m_x10_48 h₂,
    b800065c8_m_x10_56 h₂, b800065c8_m_x10_64 h₂, ← c0, ← c1, ry .x27 (by decide),
    ry .x21 (by decide), ry .x8 (by decide), ry .x9 (by decide)]

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
