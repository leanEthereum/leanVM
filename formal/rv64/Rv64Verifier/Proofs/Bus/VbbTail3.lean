import Rv64Verifier.Proofs.Bus.VbbTail2

/-!
# `verify_bus_balance` past the GKR loop: the final counts, to `0x80006ca0`

`memory_final` and `bytecode_final`, each `next_scalar` into `S - 608` (an `Err` written through
`s2`), the first's limbs kept in `s9`, `s6`, `s7`, the second's in `s10`, `a1` and at `S - 584`.
`scalarsStage` composes the check, `next_scalars(3)` and these two: at `0x80006ca0` (`Scalars`)
the code runs `rest`.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `memory_final`, to the second `next_scalar`'s entry. -/
structure MemFinal (s y z : MachineState) : Prop where
  inv : Inv s z
  regs : ∀ r ∈ ([.x8, .x9, .x18, .x19, .x20, .x21, .x24, .x26, .x27] : List Reg),
    z.getReg r = y.getReg r
  x1 : z.getReg .x1 = 0x80006c3c
  x10 : z.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608
  x11 : z.getReg .x11 = s.getReg .x12
  step : StepR s y z (Within · (s.getReg .x2 - 608) 32)

theorem memFinalStep (hN : NextScalarSpec) {bev : MachineState → Word → List E → Option E}
    {s y : MachineState} {K : E → TM BusResultRust} (hpre : BusBalancePre s) (h : Inv s y)
    (hpc : y.pc = 0x8000c720) (hx1 : y.getReg .x1 = 0x80006be8)
    (h10 : y.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608) (h11 : y.getReg .x11 = s.getReg .x12)
    (hx18 : y.getReg .x18 = s.getReg .x10) (hx20 : y.getReg .x20 = s.getReg .x12)
    (htr : Tracks (prog bev s) (s.getReg .x12) s y (TM.nextScalar >>= K)) :
    ∃ z, Reaches Image.code y z ∧ (Done bev s z ∨ Dead Image.code z ∨
      (z.pc = 0x8000c720 ∧ MemFinal s y z ∧ Tracks (prog bev s) (s.getReg .x12) s z
        (K (eOf3 (z.getReg .x25) (z.getReg .x22) (z.getReg .x23))))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  obtain ⟨v, hrv, ⟨hpcv, hp, st, J, herr, hok⟩ | hd⟩ :=
    nextScalarCall hN hpre h (Reaches.refl y) hpc h10 h11 (by omega) (by omega) (by omega)
  swap
  · exact ⟨v, hrv, Or.inr (Or.inl hd)⟩
  have sp := J.sp
  have hpc' : v.pc = 0x80006be8 := by rw [hpcv, returnAddress_eq, hx1]; decide
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006be8_spec hpc' (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80006be8_keeps h₁
  have m₁ := b80006be8_mem_same h₁
  have I₁ := J.same m₁ (k₁ .x2 (by decide))
  have e736 : s.getReg .x2 - 1344 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x18₁ : u₁.getReg .x18 = s.getReg .x10 := by
    rw [k₁ .x18 (by decide), hp .x18 (by decide), hx18]
  by_cases ht : v.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0
  swap
  · have pc₁ := b80006be8_pc_not_taken h₁ (by rw [sp, e736]; exact ht)
    have ho := hpre.out
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006bf8_spec pc₁ (by
      rv_eval [x18₁]
      and_intros <;> exact Region.valid ho (by addr_omega [ho]) (by addr_omega [ho])
        (by addr_omega [ho]))
    obtain ⟨t, hrt, hdone⟩ := errDoneAt (bev := bev) hpre I₁ x18₁ (by omega)
      (b80006bf8_frame h₂ (by rw [x18₁]; addr_omega [ho])) ((b80006bf8_keeps h₂) .x2 (by decide))
      (b80006bf8_pc h₂) (b80006bf8_m_x18_0 h₂) (htr.fail (herr ht))
    exact ⟨t, hrv.trans (hr₁.trans (hr₂.trans hrt)), Or.inl hdone⟩
  have pc₁ := b80006be8_pc_taken h₁ (by rw [sp, e736]; exact ht)
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 1344 := I₁.sp
  obtain ⟨z, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006c28_spec pc₁ (by
    rv_eval [sp₁]
    valid_access hval [hb1])
  have k₂ := b80006c28_keeps h₂
  have m₂ := b80006c28_mem_same h₂
  have I₂ := I₁.same m₂ (k₂ .x2 (by decide))
  have a0 : v.getMem (s.getReg .x2 - 1344 + 744) =
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 8) :=
    congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have a1 : v.getMem (s.getReg .x2 - 1344 + 752) =
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 8 + 8) :=
    congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have a2 : v.getMem (s.getReg .x2 - 1344 + 760) =
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 8 + 16) :=
    congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have hv : eOf3 (z.getReg .x25) (z.getReg .x22) (z.getReg .x23) =
      eAt v (s.getReg .x2 - BitVec.ofNat 64 608 + 8) := by
    rw [eAt_eOf3, k₂ .x25 (by decide), k₂ .x22 (by decide), b80006c28_x23 h₂, b80006be8_x25 h₁,
      b80006be8_x22 h₁, sp₁, m₁, sp, a0, a1, a2]
  refine ⟨z, hrv.trans (hr₁.trans hr₂), Or.inr (Or.inr ⟨b80006c28_pc h₂, {
    inv := I₂
    regs := fun r hr ↦ by
      rw [k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _), hp r (mem_of_mem hr _)]
    x1 := b80006c28_x1 h₂
    x10 := by rw [b80006c28_x10 h₂, sp₁, e736]
    x11 := by rw [b80006c28_x11 h₂, k₁ .x20 (by decide), hp .x20 (by decide), hx20]
    step := ((st.toR.trans (StepR.same m₁ J.heap (k₁ .x2 (by decide)))).trans
      (StepR.same m₂ I₁.heap (k₂ .x2 (by decide)))).weaken fun a ha ↦ by
        rcases ha with (ha | ha) | ha
        · exact ha
        · exact False.elim ha
        · exact False.elim ha }, ?_⟩)⟩
  rw [hv]
  exact (htr.bind (hok ht)).keep fun T hT ↦
    TranscriptAt.same hpre I₁ m₂ (TranscriptAt.same hpre J m₁ hT)

/-- `bytecode_final`, to `0x80006ca0`. -/
structure BcFinal (s z q : MachineState) : Prop where
  inv : Inv s q
  regs : ∀ r ∈ ([.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x27] : List Reg),
    q.getReg r = z.getReg r
  step : StepR s z q (Within · (s.getReg .x2 - 608) 32)

theorem bcFinalStep (hN : NextScalarSpec) {bev : MachineState → Word → List E → Option E}
    {s z : MachineState} {K : E → TM BusResultRust} (hpre : BusBalancePre s) (h : Inv s z)
    (hpc : z.pc = 0x8000c720) (hx1 : z.getReg .x1 = 0x80006c3c)
    (h10 : z.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608) (h11 : z.getReg .x11 = s.getReg .x12)
    (hx18 : z.getReg .x18 = s.getReg .x10)
    (htr : Tracks (prog bev s) (s.getReg .x12) s z (TM.nextScalar >>= K)) :
    ∃ q, Reaches Image.code z q ∧ (Done bev s q ∨ Dead Image.code q ∨
      (q.pc = 0x80006ca0 ∧ BcFinal s z q ∧ Tracks (prog bev s) (s.getReg .x12) s q
        (K (eOf3 (q.getReg .x26) (q.getReg .x11) (q.getMem (s.getReg .x2 - 584)))))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  obtain ⟨v, hrv, ⟨hpcv, hp, st, J, herr, hok⟩ | hd⟩ :=
    nextScalarCall hN hpre h (Reaches.refl z) hpc h10 h11 (by omega) (by omega) (by omega)
  swap
  · exact ⟨v, hrv, Or.inr (Or.inl hd)⟩
  have sp := J.sp
  have hpc' : v.pc = 0x80006c3c := by rw [hpcv, returnAddress_eq, hx1]; decide
  obtain ⟨q, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006c3c_spec hpc' (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80006c3c_keeps h₁
  have m₁ := b80006c3c_mem_same h₁
  have I₁ := J.same m₁ (k₁ .x2 (by decide))
  have e736 : s.getReg .x2 - 1344 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x18₁ : q.getReg .x18 = s.getReg .x10 := by
    rw [k₁ .x18 (by decide), hp .x18 (by decide), hx18]
  by_cases ht : v.getMem (s.getReg .x2 - BitVec.ofNat 64 608) = 0
  swap
  · have pc₁ := b80006c3c_pc_not_taken h₁ (by rw [sp, e736]; exact ht)
    have ho := hpre.out
    obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006c4c_spec pc₁ (by
      rv_eval [x18₁]
      and_intros <;> exact Region.valid ho (by addr_omega [ho]) (by addr_omega [ho])
        (by addr_omega [ho]))
    obtain ⟨t, hrt, hdone⟩ := errDoneAt (bev := bev) hpre I₁ x18₁ (by omega)
      (b80006c4c_frame h₂ (by rw [x18₁]; addr_omega [ho])) ((b80006c4c_keeps h₂) .x2 (by decide))
      (b80006c4c_pc h₂) (b80006c4c_m_x18_0 h₂) (htr.fail (herr ht))
    exact ⟨t, hrv.trans (hr₁.trans (hr₂.trans hrt)), Or.inl hdone⟩
  have pc₁ := b80006c3c_pc_taken h₁ (by rw [sp, e736]; exact ht)
  have a0 : v.getMem (s.getReg .x2 - 1344 + 744) =
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 8) :=
    congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have a1 : v.getMem (s.getReg .x2 - 1344 + 752) =
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 8 + 8) :=
    congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have a2 : v.getMem (s.getReg .x2 - 584) =
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + 8 + 16) :=
    congrArg v.getMem (by apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
  have hv : eOf3 (q.getReg .x26) (q.getReg .x11) (q.getMem (s.getReg .x2 - 584)) =
      eAt v (s.getReg .x2 - BitVec.ofNat 64 608 + 8) := by
    rw [eAt_eOf3, b80006c3c_x26 h₁, b80006c3c_x11 h₁, m₁, sp, a0, a1, a2]
  refine ⟨q, hrv.trans hr₁, Or.inr (Or.inr ⟨pc₁, {
    inv := I₁
    regs := fun r hr ↦ by rw [k₁ r (mem_of_mem hr _), hp r (mem_of_mem hr _)]
    step := (st.toR.trans (StepR.same m₁ J.heap (k₁ .x2 (by decide)))).weaken fun a ha ↦ by
      rcases ha with ha | ha
      · exact ha
      · exact False.elim ha }, ?_⟩)⟩
  rw [hv]
  exact (htr.bind (hok ht)).keep fun T hT ↦ TranscriptAt.same hpre J m₁ hT

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
