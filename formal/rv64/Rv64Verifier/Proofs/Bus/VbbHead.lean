import Rv64Verifier.Proofs.Bus.VbbCalls
import Rv64Verifier.Proofs.Transcript.SamplesModel

/-!
# `verify_bus_balance`: the challenges, `0x800064f4` to the first `next_scalar`

`alphas = samples(4)` into `S - 912`, `eq_kernel(alphas)` into `S - 888`, then the inlined
`sample`: `duplex`, the state's first three lanes kept at `S - 1192`, `S - 1200`, `S - 1184`
(`beta`), and the loop's depth `mem(S - 1032)` in `s9`.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  LeanVM.Protocol.Compile
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem Inv.same {s v w : MachineState} (h : Inv s v) (hm : ∀ a, w.getMem a = v.getMem a)
    (sp : w.getReg .x2 = v.getReg .x2) : Inv s w := by
  have hn : heapNext w = heapNext v := by simp only [heapNext, hm]
  refine ⟨sp.trans h.sp, ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩, by rw [hn]; exact h.mono,
    (h.frame.trans (DFrame.of_same hm fun _ ↦ False) fun _ h ↦ h.elim).mono fun a ha ↦
      W.mono hn.ge ha, fun i hi ↦ by rw [hm]; exact h.saved i hi⟩

theorem TranscriptAt.same {s v w : MachineState} (hpre : BusBalancePre s) (h : Inv s v)
    (hm : ∀ a, w.getMem a = v.getMem a) {T : TState} (hT : TranscriptAt v (s.getReg .x12) T) :
    TranscriptAt w (s.getReg .x12) T :=
  (DFrame.of_same hm fun _ ↦ False).transcriptAt hT (h.tok hpre) (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) (fun _ _ h ↦ h) (fun _ _ h ↦ h)

theorem frameW_slot {s : MachineState} (hpre : BusBalancePre s) {k n : Nat} (hk1 : 104 + n ≤ k)
    (hk2 : k ≤ 1344) : FrameW s (Within · (s.getReg .x2 - BitVec.ofNat 64 k) n) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro a ha
  addr_omega [ha, hb1, hk1, hk2]

/-- The calls of `samples(4)` and `eq_kernel`. -/
structure Alphas (s v₀ v : MachineState) (al : List E) : Prop where
  inv : Inv s v
  regs : ∀ r ∈ calleeSaved, v.getReg r = v₀.getReg r
  step : StepR s v₀ v (Within · (s.getReg .x2 - 912) 48)
  alphas : NewVecE s v (s.getReg .x2 - 912) al
  weights : NewVecE s v (s.getReg .x2 - 888) (eqKernelRust al)
  len : al.length = 4
  run : ∀ T, TranscriptAt v₀ (s.getReg .x12) T →
    ∃ T', (TM.samples 4).run T = some (al, T') ∧ TranscriptAt v (s.getReg .x12) T'

theorem alphasStep (hS : SamplesSpec) (hEK : Vbb.EqKernelSpec) {s v₀ : MachineState}
    (hpre : BusBalancePre s) (L : AfterLayouts s v₀) (hpc : v₀.pc = 0x800064f4) :
    ∃ v, Reaches Image.code v₀ v ∧
      ((v.pc = 0x8000651c ∧ ∃ al, Alphas s v₀ v al) ∨ Dead Image.code v) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have I₀ := L.inv
  have sp₀ := I₀.sp
  -- `samples(4)`
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800064f4_spec hpc trivial
  have k₁ := b800064f4_keeps h₁
  have m₁ := b800064f4_mem_same h₁
  have I₁ := I₀.same m₁ (k₁ .x2 (by decide))
  have x10₁ : u₁.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 912 := by
    rw [b800064f4_x10 h₁, sp₀]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  obtain ⟨v₁, hrv₁, ⟨hpcv₁, hp₁, st₁, J₁, val₁⟩ | hd⟩ :=
    samplesCall hS hpre I₁ hr₁ (b800064f4_pc h₁) x10₁
      ((b800064f4_x11 h₁).trans L.regs.x20) (by omega) (by omega) (by omega)
  swap
  · exact ⟨v₁, hrv₁, Or.inr hd⟩
  replace val₁ : ∀ T, TranscriptAt u₁ (s.getReg .x12) T → ∃ xs T',
      (TM.samples 4).run T = some (xs, T') ∧
        NewVecE u₁ v₁ (s.getReg .x2 - BitVec.ofNat 64 912) xs ∧
        TranscriptAt v₁ (s.getReg .x12) T' := fun T hT ↦ by
    rw [b800064f4_x12 h₁] at val₁; exact val₁ T hT
  obtain ⟨al, T₀, e₀, hal, -⟩ := val₁ (canonT u₁ (s.getReg .x12)) (canonT_at _ _)
  have hlen : al.length = 4 := by
    rw [samples_run] at e₀
    cases e₀
    exact sqs_length _ _
  have run₁ : ∀ T, TranscriptAt u₁ (s.getReg .x12) T →
      ∃ T', (TM.samples 4).run T = some (al, T') ∧ TranscriptAt v₁ (s.getReg .x12) T' := by
    intro T hT
    obtain ⟨xs, T', e, hxs, hT'⟩ := val₁ T hT
    rw [show xs = al from hxs.elems.symm.trans hal.elems] at e
    exact ⟨T', e, hT'⟩
  have hal' := hal.widen I₁.mono
  -- `eq_kernel(alphas)`
  have sp₁ : v₁.getReg .x2 = s.getReg .x2 - 1344 := J₁.sp
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006508_spec
    (by rw [hpcv₁, returnAddress_eq, b800064f4_x1 h₁]; decide) (by
      rv_eval [sp₁]
      and_intros <;> valid_access hval [hb1])
  have k₂ := b80006508_keeps h₂
  have m₂ := b80006508_mem_same h₂
  have I₂ := J₁.same m₂ (k₂ .x2 (by decide))
  have st₂ : StepR s v₁ u₂ (fun _ ↦ False) := StepR.same m₂ J₁.heap (k₂ .x2 (by decide))
  have fw0 : FrameW s fun _ ↦ False := fun _ h ↦ h.elim
  have hin912 : (s.getReg .x2 - 1344).toNat ≤ (s.getReg .x2 - BitVec.ofNat 64 912).toNat ∧
      (s.getReg .x2 - BitVec.ofNat 64 912).toNat + 24 ≤ (s.getReg .x2).toNat := by
    addr_omega [hb1]
  have hal₂ := hal'.keepR hpre st₂ fw0 hin912 fun _ _ h ↦ h
  have hl4 : (vecLen u₂ (s.getReg .x2 - BitVec.ofNat 64 912)).toNat = 4 := by
    have := hal₂.elems
    rw [vecEs] at this
    rw [← hlen, ← this, eListAt_length]
  have e904 : s.getReg .x2 - 1344 + 440 = s.getReg .x2 - BitVec.ofNat 64 912 + 8 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e896 : s.getReg .x2 - 1344 + 448 = s.getReg .x2 - BitVec.ofNat 64 912 + 16 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  obtain ⟨v₂, hrv₂, ⟨hpcv₂, hp₂, st₃, hw⟩ | hd⟩ :=
    eqKernelCall hEK hpre I₂ (hrv₁.trans hr₂) (b80006508_pc h₂) (k := 888)
      (by rw [b80006508_x10 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
      (by omega) (by omega) (by omega) hal₂
      (by rw [b80006508_x11 h₂, sp₁, e904, vecPtr, m₂])
      (by rw [b80006508_x12 h₂, sp₁, e896, vecLen, m₂])
      (by omega) (by omega)
  swap
  · exact ⟨v₂, hrv₂, Or.inr hd⟩
  have if₃ := inFrame hpre (k := 888) (n := 24) (by omega) (by omega)
  have J₂ := I₂.after hpre if₃ st₃
  refine ⟨v₂, hrv₂, Or.inl ⟨by rw [hpcv₂, returnAddress_eq, b80006508_x1 h₂]; decide, al, {
    inv := J₂
    regs := fun r hr ↦ by
      rw [hp₂ r hr, k₂ r (mem_of_mem hr _), hp₁ r hr, k₁ r (mem_of_mem hr _)]
    step := ((((StepR.same m₁ I₀.heap (k₁ .x2 (by decide))).trans st₁.toR).trans st₂).trans
      st₃.toR).weaken fun a ha ↦ by
        rcases ha with ((ha | ha) | ha) | ha
        · exact False.elim ha
        · addr_omega [ha, hb1]
        · exact False.elim ha
        · addr_omega [ha, hb1]
    alphas := hal₂.keepR hpre st₃.toR (frameW_slot hpre (by omega) (by omega)) hin912
      fun y hy hy' ↦ by addr_omega [hy, hy', hb1]
    weights := hw
    len := hlen
    run := fun T hT ↦ by
      obtain ⟨T', e, hT'⟩ := run₁ T (TranscriptAt.same hpre I₀ m₁ hT)
      exact ⟨T', e, st₃.transcript hpre I₂ if₃ (TranscriptAt.same hpre J₁ m₂ hT')⟩ }⟩⟩

theorem challengeOf_stateAt' (u : MachineState) (a : Word) :
    challengeOf (stateAt u a) = eAt u a := by
  simp only [challengeOf, lane_stateAt u a (by decide : 0 < 25),
    lane_stateAt u a (by decide : 1 < 25), lane_stateAt u a (by decide : 2 < 25), Nat.mul_zero,
    Nat.mul_one, Nat.reduceMul, add_ofNat_zero]
  rfl

/-- The inlined `sample`, to the first `next_scalar`'s entry. -/
structure Beta (s v u : MachineState) : Prop where
  inv : Inv s u
  regs : ∀ r ∈ ([.x8, .x9, .x18, .x19, .x20, .x24] : List Reg), u.getReg r = v.getReg r
  x1 : u.getReg .x1 = 0x80006558
  x10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608
  x11 : u.getReg .x11 = s.getReg .x12
  x22 : u.getReg .x22 = s.getReg .x12 + 8
  x25 : u.getReg .x25 = v.getMem (s.getReg .x2 - 1032)
  step : StepR s v u (Within · (s.getReg .x2 - 1200) 24)
  run : ∀ T, TranscriptAt v (s.getReg .x12) T → ∃ T', TM.sample.run T =
    some (eOf3 (u.getMem (s.getReg .x2 - 1192)) (u.getMem (s.getReg .x2 - 1200))
      (u.getMem (s.getReg .x2 - 1184)), T') ∧ TranscriptAt u (s.getReg .x12) T'

theorem betaStep (hD : DuplexSpec) {s v : MachineState} (hpre : BusBalancePre s) (h : Inv s v)
    (hpc : v.pc = 0x8000651c) (hx20 : v.getReg .x20 = s.getReg .x12) :
    ∃ u, Reaches Image.code v u ∧ ((u.pc = 0x8000c720 ∧ Beta s v u) ∨ Dead Image.code u) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hS := hpre.self.self
  have ss := hpre.selfStack
  rw [stackLo_eq] at ss
  have sp := h.sp
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000651c_spec hpc trivial
  have k₁ := b8000651c_keeps h₁
  have m₁ := b8000651c_mem_same h₁
  have I₁ := h.same m₁ (k₁ .x2 (by decide))
  obtain ⟨v₁, hrv₁, ⟨hpcv₁, hp₁, st₁, tr₁⟩ | hd⟩ :=
    duplexCall hD hpre I₁ hr₁ (b8000651c_pc h₁) (by rw [b8000651c_x10 h₁, hx20])
  swap
  · exact ⟨v₁, hrv₁, Or.inr hd⟩
  have J₁ := I₁.afterR hpre (fun _ h ↦ False.elim h) st₁
  have sp₁ : v₁.getReg .x2 = s.getReg .x2 - 1344 := J₁.sp
  have x20₁ : v₁.getReg .x20 = s.getReg .x12 := by
    rw [hp₁ .x20 (by decide), k₁ .x20 (by decide), hx20]
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b8000652c_spec
    (by rw [hpcv₁, returnAddress_eq, b8000651c_x1 h₁]; decide) (by
      rv_eval [sp₁, x20₁]
      and_intros <;> first
        | valid_access hval [hb1]
        | exact Region.valid hS (by addr_omega [hS]) (by addr_omega [hS]) (by addr_omega [hS])
        | addr_omega [hS, ss, hb1])
  have k₂ := b8000652c_keeps h₂
  have fr₂ := b8000652c_frame h₂ (by rw [sp₁]; addr_omega [hb1])
  have e144 : v₁.getReg .x2 + 144 = s.getReg .x2 - 1200 := by
    rw [sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rw [e144] at fr₂
  have st₂ : StepR s v₁ u₂ (Within · (s.getReg .x2 - 1200) 24) :=
    StepR.ofMemFrame J₁.heap fr₂ (fun _ h ↦ h) (by addr_omega [hb1]) (k₂ .x2 (by decide))
  have J₂ := J₁.afterR hpre (frameW_slot hpre (k := 1200) (n := 24) (by omega) (by omega)) st₂
  have m0 := b8000652c_m_x2_152 h₂
  have m1 := b8000652c_m_x2_144 h₂
  have m2 := b8000652c_m_x2_160 h₂
  rw [sp₁, x20₁, show s.getReg .x2 - 1344 + 152 = s.getReg .x2 - 1192 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m0
  rw [sp₁, x20₁, show s.getReg .x2 - 1344 + 144 = s.getReg .x2 - 1200 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m1
  rw [sp₁, x20₁, show s.getReg .x2 - 1344 + 160 = s.getReg .x2 - 1184 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m2
  have x25 : u₂.getReg .x25 = v.getMem (s.getReg .x2 - 1032) := by
    rw [b8000652c_x25 h₂, sp₁, show s.getReg .x2 - 1344 + 312 = s.getReg .x2 - 1032 by
      apply BitVec.eq_of_toNat_eq; addr_omega [hb1], ← m₁]
    exact st₁.word hpre (fun _ _ h ↦ h) (Or.inl (by addr_omega [hb1]))
  refine ⟨u₂, hrv₁.trans hr₂, Or.inl ⟨b8000652c_pc h₂, {
    inv := J₂
    regs := fun r hr ↦ by
      rw [k₂ r (mem_of_mem hr _), hp₁ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
    x1 := b8000652c_x1 h₂
    x10 := by rw [b8000652c_x10 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
    x11 := (b8000652c_x11 h₂).trans x20₁
    x22 := by rw [k₂ .x22 (by decide), hp₁ .x22 (by decide), b8000651c_x22 h₁, hx20]
    x25 := x25
    step := ((StepR.same m₁ h.heap (k₁ .x2 (by decide))).trans (st₁.trans st₂)).weaken
      fun a ha ↦ by
        rcases ha with ha | ha | ha
        · exact False.elim ha
        · exact False.elim ha
        · exact ha
    run := fun T hT ↦ ⟨{ T with sponge := spDuplex T.sponge }, ?_, ?_⟩ }⟩⟩
  · have hs : spongeAt v₁ (s.getReg .x12 + 8) = spDuplex T.sponge :=
      (tr₁ T (TranscriptAt.same hpre h m₁ hT)).sponge
    have hc : challengeOf (spDuplex T.sponge).state = eOf3 (u₂.getMem (s.getReg .x2 - 1192))
        (u₂.getMem (s.getReg .x2 - 1200)) (u₂.getMem (s.getReg .x2 - 1184)) := by
      rw [← hs]
      show challengeOf (stateAt v₁ (s.getReg .x12 + 8 + 128)) = _
      rw [challengeOf_stateAt', m0, m1, m2]
      unfold Rv64Verifier.eAt eOf3
      have a1 : s.getReg .x12 + 8 + 128 = s.getReg .x12 + 136 := by bv_omega
      have a2 : s.getReg .x12 + 136 + 8 = s.getReg .x12 + 144 := by bv_omega
      have a3 : s.getReg .x12 + 136 + 16 = s.getReg .x12 + 152 := by bv_omega
      rw [a1, a2, a3]
    have e1 : (spSqueeze T.sponge).2 = spDuplex T.sponge := rfl
    have e2 : (spSqueeze T.sponge).1 = challengeOf (spDuplex T.sponge).state := rfl
    show some ((spSqueeze T.sponge).1, { T with sponge := (spSqueeze T.sponge).2 }) = _
    rw [e1, e2, hc]
  · exact J₁.transcript hpre J₂.heap ((DFrame.of_memFrame fr₂).mono fun a ha ↦
      Or.inl (by addr_omega [ha, hb1])) (tr₁ T (TranscriptAt.same hpre h m₁ hT))

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
