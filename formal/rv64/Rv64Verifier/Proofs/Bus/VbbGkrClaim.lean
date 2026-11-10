import Rv64Verifier.Proofs.Bus.VbbGkrCalls

/-!
# `verify_bus_balance`: an iteration's combiner and claim

From the loop's head: `duplex`, the sponge's first three lanes into `S - 128` (the inlined
`sample`, the combiner), `poly_eval(values, combiner)` into `S - 152` (the claim), to
`try_allocate_in`'s entry.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  LeanVM.Protocol.Compile
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `try_allocate_in`'s entry: the combiner at `S - 128`, the claim at `S - 152`. -/
structure AtAlloc (s u v : MachineState) (k : Start) (cnt : E) (P c : Word) (st : GkrState)
    (comb : E) : Prop where
  ctx : Ctx s v k cnt P
  regs : ∀ r ∈ ([.x9, .x19, .x20, .x21, .x24, .x25, .x27] : List Reg), v.getReg r = u.getReg r
  x1 : v.getReg .x1 = 0x800066f4
  x10 : v.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608
  x11 : v.getReg .x11 = u.getReg .x21
  x12 : v.getReg .x12 = 0
  x13 : v.getReg .x13 = 8
  x14 : v.getReg .x14 = 32
  combAt : eAt v (s.getReg .x2 - BitVec.ofNat 64 128) = comb
  claimAt : eAt v (s.getReg .x2 - BitVec.ofNat 64 152) = polyEvalRust st.values comb
  point : NewVecR s v c (u.getReg .x27) (u.getReg .x21) st.point
  step : StepR s u v (Scratch s)

theorem combStep (hD : DuplexSpec) (hPE : MultilinearContracts.PolyEvalSpec)
    {bev : MachineState → Word → List E → Option E} {s u : MachineState} {k : Start} {cnt : E}
    {P c : Word} {n : ℕ} {st : GkrState} {K : E → TM BusResultRust} (hpre : BusBalancePre s)
    (h : Loop bev s u k cnt P c n st) (hpc : u.pc = 0x8000669c)
    (htr : Tracks (prog bev s) (s.getReg .x12) s u (TM.sample >>= K)) :
    ∃ v, Reaches Image.code u v ∧ (Dead Image.code v ∨ ∃ comb, v.pc = 0x800049ac ∧
      AtAlloc s u v k cnt P c st comb ∧ Tracks (prog bev s) (s.getReg .x12) s v (K comb)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hS := hpre.self.self
  have ss := hpre.selfStack
  rw [stackLo_eq] at ss
  have C := h.ctx
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000669c_spec hpc trivial
  have k₁ := b8000669c_keeps h₁
  have m₁ := b8000669c_mem_same h₁
  have I₁ := h.inv.same m₁ (k₁ .x2 (by decide))
  obtain ⟨v₁, hrv₁, ⟨hpcv₁, hp₁, st₁, tr₁⟩ | hd⟩ :=
    duplexCall hD hpre I₁ hr₁ (b8000669c_pc h₁) (by rw [b8000669c_x10 h₁, h.x22])
  swap
  · exact ⟨v₁, hrv₁, Or.inl hd⟩
  have J₁ := I₁.afterR hpre (fun _ h ↦ False.elim h) st₁
  have sp₁ : v₁.getReg .x2 = s.getReg .x2 - 1344 := J₁.sp
  have rg₁ (r : Reg) (hr : r ∈ ([.x9, .x19, .x20, .x21, .x24, .x25, .x27] : List Reg)) :
      v₁.getReg r = u.getReg r := by
    rw [hp₁ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have x20₁ : v₁.getReg .x20 = s.getReg .x12 := (rg₁ .x20 (by decide)).trans h.x20
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b800066a8_spec
    (by rw [hpcv₁, returnAddress_eq, b8000669c_x1 h₁]; decide) (by
      rv_eval [sp₁, x20₁]
      and_intros <;> first
        | valid_access hval [hb1]
        | exact Region.valid hS (by addr_omega [hS]) (by addr_omega [hS]) (by addr_omega [hS]))
  have k₂ := b800066a8_keeps h₂
  have fr₂ := b800066a8_frame h₂ (by rw [sp₁]; addr_omega [hb1])
  rw [sp₁, show s.getReg .x2 - 1344 + 1216 = s.getReg .x2 - BitVec.ofNat 64 128 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at fr₂
  have st₂ : StepR s v₁ u₂ (Within · (s.getReg .x2 - BitVec.ofNat 64 128) 24) :=
    StepR.ofMemFrame J₁.heap fr₂ (fun _ h ↦ h) (by addr_omega [hb1]) (k₂ .x2 (by decide))
  have J₂ := J₁.afterR hpre (frameW_slot hpre (k := 128) (n := 24) (by omega) (by omega)) st₂
  -- the lanes
  have l0 := b800066a8_m_x2_1216 h₂
  have l1 := b800066a8_m_x2_1224 h₂
  have l2 := b800066a8_m_x2_1232 h₂
  rw [sp₁, x20₁, show s.getReg .x2 - 1344 + 1216 = s.getReg .x2 - BitVec.ofNat 64 128 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l0
  rw [sp₁, x20₁, show s.getReg .x2 - 1344 + 1224 = s.getReg .x2 - BitVec.ofNat 64 128 + 8 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
    show s.getReg .x12 + 144 = s.getReg .x12 + 8 + 128 + 8 by bv_omega] at l1
  rw [sp₁, x20₁, show s.getReg .x2 - 1344 + 1232 = s.getReg .x2 - BitVec.ofNat 64 128 + 16 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
    show s.getReg .x12 + 152 = s.getReg .x12 + 8 + 128 + 16 by bv_omega] at l2
  rw [show s.getReg .x12 + 136 = s.getReg .x12 + 8 + 128 by bv_omega] at l0
  have hcomb : eAt u₂ (s.getReg .x2 - BitVec.ofNat 64 128) =
      eAt v₁ (s.getReg .x12 + 8 + 128) := eAt_congr l0 l1 l2
  -- `values` at `poly_eval`'s entry
  have st₀₂ : StepR s u u₂ fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 128) 24 :=
    (((StepR.same m₁ h.inv.heap (k₁ .x2 (by decide))).trans st₁).trans st₂).weaken
      fun a ha ↦ by
        rcases ha with (ha | ha) | ha
        · exact False.elim ha
        · exact False.elim ha
        · exact ha
  have hv₂ := h.values.keepR hpre st₀₂ (frameW_slot hpre (k := 128) (n := 24) (by omega)
    (by omega)) (by addr_omega [hb1]) fun y hy hy' ↦ by addr_omega [hy, hy', hb1]
  have hP := C.heapP
  have hlo := hpre.heap.lo
  have hP8 : P.toNat % 8 = 0 := by have := h.values.buf.1; rwa [h.ptr] at this
  have hvals : eListAt u₂ P 3 = st.values := by
    have e := hv₂.elems
    have hl := h.len
    have ep : vecPtr u₂ (s.getReg .x2 - 176) = P := by
      rw [vecPtr, st₀₂.word hpre (fun y hy hy' ↦ by addr_omega [hy, hy', hb1])
        (Or.inl (by addr_omega [hb1]))]
      exact h.ptr
    rw [vecEs, ep] at e
    have h3 : (vecLen u₂ (s.getReg .x2 - 176)).toNat = 3 := by
      rw [← hl, ← e, eListAt_length]
    rw [h3] at e
    exact e
  obtain ⟨v₃, hrv₃, ⟨hpcv₃, hp₃, st₃, hval₃, tr₃⟩ | hd⟩ :=
    polyEvalCall hPE hpre J₂ (hrv₁.trans hr₂) (b800066a8_pc h₂) (k := 152) (j := 128) (a := P)
      (by rw [b800066a8_x10 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
      (by rw [b800066a8_x11 h₂, rg₁ .x19 (by decide)]; exact h.x19)
      (b800066a8_x12 h₂)
      (by rw [b800066a8_x13 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (heapRange hP8 (by simp only [heapStart, heapNext] at hlo hP ⊢; omega) (by
        simp only [heapEnd] at hP ⊢; omega))
      (by simp only [heapEnd] at hP; addr_omega [hP, hb1])
      (by simp only [heapEnd] at hP; addr_omega [hP, hb1])
  swap
  · exact ⟨v₃, hrv₃, Or.inl hd⟩
  have J₃ := J₂.afterR hpre (frameW_slot hpre (k := 152) (n := 24) (by omega) (by omega)) st₃
  have sp₃ : v₃.getReg .x2 = s.getReg .x2 - 1344 := J₃.sp
  obtain ⟨u₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800066d8_spec
    (by rw [hpcv₃, returnAddress_eq, b800066a8_x1 h₂]; decide) trivial
  have k₄ := b800066d8_keeps h₄
  have m₄ := b800066d8_mem_same h₄
  have st₄ : ∀ {A : Word → Prop}, StepR s v₃ u₄ A := StepR.same m₄ J₃.heap (k₄ .x2 (by decide))
  have stAll : StepR s u u₄ (Scratch s) :=
    ((st₀₂.trans st₃).trans (st₄ (A := fun _ ↦ False))).weaken fun a ha ↦ by
      rcases ha with (ha | ha) | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1]))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1]))))))
      · exact False.elim ha
  have rg (r : Reg) (hr : r ∈ ([.x9, .x19, .x20, .x21, .x24, .x25, .x27] : List Reg)) :
      u₄.getReg r = u.getReg r := by
    rw [k₄ r (mem_of_mem hr _), hp₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _),
      rg₁ r (mem_of_mem hr _)]
  refine ⟨u₄, hrv₃.trans hr₄, Or.inr ⟨eAt u₂ (s.getReg .x2 - BitVec.ofNat 64 128),
    b800066d8_pc h₄, {
    ctx := C.step hpre stAll
    regs := rg
    x1 := b800066d8_x1 h₄
    x10 := by rw [b800066d8_x10 h₄, sp₃]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x11 := by rw [b800066d8_x11 h₄, hp₃ .x21 (by decide), k₂ .x21 (by decide)]
              exact rg₁ .x21 (by decide)
    x12 := b800066d8_x12 h₄
    x13 := b800066d8_x13 h₄
    x14 := b800066d8_x14 h₄
    combAt := by
      rw [(st₄ (A := fun _ ↦ False)).eAtFrame hpre (by omega) (by omega) fun _ _ h ↦ h]
      exact st₃.eAtFrame hpre (by omega) (by omega) fun y hy hy' ↦ by addr_omega [hy, hy', hb1]
    claimAt := by
      rw [(st₄ (A := fun _ ↦ False)).eAtFrame hpre (by omega) (by omega) fun _ _ h ↦ h, hval₃,
        hvals]
    point := h.point.keepG hpre stAll (Scratch.frameW hpre)
    step := stAll }, ?_⟩⟩
  refine ((htr.bind (v := u₂) fun T hT ↦ ⟨{ T with sponge := spDuplex T.sponge }, ?_, ?_⟩).keep
    fun T hT ↦ tr₃ T hT).keep fun T hT ↦ TranscriptAt.same hpre J₃ m₄ hT
  · have hs : spongeAt v₁ (s.getReg .x12 + 8) = spDuplex T.sponge :=
      (tr₁ T (TranscriptAt.same hpre h.inv m₁ hT)).sponge
    have hc : challengeOf (spDuplex T.sponge).state = eAt u₂ (s.getReg .x2 - BitVec.ofNat 64 128) := by
      rw [← hs, hcomb]
      exact challengeOf_stateAt' v₁ _
    have e1 : (spSqueeze T.sponge).2 = spDuplex T.sponge := rfl
    have e2 : (spSqueeze T.sponge).1 = challengeOf (spDuplex T.sponge).state := rfl
    show some ((spSqueeze T.sponge).1, { T with sponge := (spSqueeze T.sponge).2 }) = _
    rw [e1, e2, hc]
  · exact J₁.transcript hpre J₂.heap ((DFrame.of_memFrame fr₂).mono fun a ha ↦
      Or.inl (by addr_omega [ha, hb1])) (tr₁ T (TranscriptAt.same hpre h.inv m₁ hT))

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
