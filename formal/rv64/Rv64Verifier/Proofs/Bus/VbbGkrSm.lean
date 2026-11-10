import Rv64Verifier.Proofs.Bus.VbbGkrMle

/-!
# `verify_bus_balance`: an iteration's `samples`

`samples(2 - (layer & 1))` into `S - 720` (`step` kept in `s7`), `values` cleared, to the first
`multilinear_eval`'s entry. From there to `concat`, `MB`: `y` at `S - 720`, `vs` pushed into
`values` at `P`.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- From `samples` to `concat`: `y` at `S - 720`, `vs` pushed into `values` at `P`, `x`'s pointer
`xp`, the third child at `S - 1112` and `s9`. -/
structure MB (s u w : MachineState) (k : Start) (cnt : E) (P : Word) (n : ℕ) (x y c2 : List E)
    (xp : Word) (vs : List E) : Prop where
  ctx : Ctx s w k cnt P
  hu : heapNext s ≤ heapNext u
  hP : P.toNat + 72 ≤ heapNext u
  x20 : w.getReg .x20 = s.getReg .x12
  x24 : w.getReg .x24 = 1
  x23 : (w.getReg .x23).toNat = stepOf n
  layers : (w.getMem (s.getReg .x2 - 1128)).toNat = n
  valuesPtr : w.getMem (s.getReg .x2 - 1280) = P
  len : w.getMem (s.getReg .x2 - 160) = BitVec.ofNat 64 vs.length
  pushed : eListAt w P vs.length = vs
  vlen : vs.length ≤ 3
  xv : NewVecR u w (w.getMem (s.getReg .x2 - 1120)) xp (w.getMem (s.getReg .x2 - 1144)) x
  yv : NewVecE u w (s.getReg .x2 - BitVec.ofNat 64 720) y
  ylen : y.length = stepOf n
  y19 : w.getReg .x19 = vecPtr w (s.getReg .x2 - BitVec.ofNat 64 720)
  y22 : w.getReg .x22 = vecLen w (s.getReg .x2 - BitVec.ofNat 64 720)
  pal : P.toNat % 8 = 0
  ch2 : HeapVec u w (w.getMem (s.getReg .x2 - 1112)) (w.getReg .x25) c2
  l2 : c2.length = 2 ^ stepOf n
  step : StepR s u w fun a ↦ Scratch s a ∨ Within a P 72

theorem two_sub_toNat {x : Word} {n : Nat} (h : x.toNat = n % 2) :
    (2 - x).toNat = stepOf n := by
  rw [BitVec.toNat_sub, h]
  have : (2 : Word).toNat = 2 := rfl
  rw [this]
  unfold stepOf
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h0 <;> simp only [h0] <;> decide

/-- `samples` and `values` cleared, from `0x80006a14` to the first `multilinear_eval`'s entry. -/
theorem samplesStep (hS : SamplesSpec) {bev : MachineState → Word → List E → Option E}
    {s u w₀ : MachineState} {k : Start} {cnt : E} {P : Word} {n : ℕ} {x c0 c1 c2 : List E}
    {F : List E → TM BusResultRust} (hpre : BusBalancePre s)
    (h : AtSm s u w₀ k cnt P n x c0 c1 c2) (hpc : w₀.pc = 0x80006a14)
    (hP : P.toNat + 72 ≤ heapNext u) (hal : P.toNat % 8 = 0) (h20 : u.getReg .x20 = s.getReg .x12)
    (h24 : u.getReg .x24 = 1)
    (htr : Tracks (prog bev s) (s.getReg .x12) s w₀ (TM.samples (stepOf n) >>= F)) :
    ∃ w, Reaches Image.code w₀ w ∧ (Dead Image.code w ∨ ∃ y, w.pc = 0x8000d28c ∧
      MB s u w k cnt P n x y c2 (w₀.getReg .x8) [] ∧
      w.getReg .x1 = 0x80006a58 ∧ w.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608 ∧
      w.getReg .x8 = w₀.getReg .x8 ∧
      w.getReg .x13 = vecPtr w (s.getReg .x2 - BitVec.ofNat 64 720) ∧
      w.getReg .x14 = vecLen w (s.getReg .x2 - BitVec.ofNat 64 720) ∧
      w.getReg .x19 = w.getReg .x13 ∧ w.getReg .x22 = w.getReg .x14 ∧
      HeapVec u w (w.getReg .x11) (w.getReg .x12) c0 ∧
      HeapVec u w (w.getReg .x26) (w.getReg .x21) c1 ∧
      c0.length = 2 ^ stepOf n ∧ c1.length = 2 ^ stepOf n ∧
      Tracks (prog bev s) (s.getReg .x12) s w (F y)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have C₀ := h.ctx
  have sp₀ := C₀.inv.sp
  have hu := h.hu
  obtain ⟨w₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006a14_spec hpc trivial
  have k₁ := b80006a14_keeps h₁
  have m₁ := b80006a14_mem_same h₁
  have I₁ := C₀.inv.same m₁ (k₁ .x2 (by decide))
  have sp₁ := I₁.sp
  obtain ⟨v₁, hrv, ⟨hpcv, hp, stT, J, hval₁⟩ | hd⟩ := samplesCall hS hpre I₁ hr₁ (b80006a14_pc h₁)
    (k := 720) (by rw [b80006a14_x10 h₁, sp₀]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b80006a14_x11 h₁, h.regs .x20 (by decide), h20]) (by omega) (by omega) (by omega)
  swap
  · exact ⟨v₁, hrv, Or.inl hd⟩
  have st₁ := stT.toR
  have hstep : (w₁.getReg .x12).toNat = stepOf n := by
    rw [b80006a14_x12 h₁]; exact two_sub_toNat h.x22
  -- `y`
  set y := vecEs v₁ (s.getReg .x2 - BitVec.ofNat 64 720) with hy
  have hok (T : TState) (hT : TranscriptAt w₁ (s.getReg .x12) T) : ∃ T',
      (TM.samples (stepOf n)).run T = some (y, T') ∧
      NewVecE w₁ v₁ (s.getReg .x2 - BitVec.ofNat 64 720) y ∧ TranscriptAt v₁ (s.getReg .x12) T' := by
    obtain ⟨xs, T', e, hv, hT'⟩ := hval₁ T hT
    rw [hstep] at e
    have : xs = y := by rw [hy, hv.elems]
    subst this
    exact ⟨T', e, hv, hT'⟩
  obtain ⟨T₀, e₀, yv₁, -⟩ := hok _ (canonT_at w₁ (s.getReg .x12))
  have ylen : y.length = stepOf n := Returns.samples (stepOf n) _ _ _ e₀
  -- `values` cleared
  have hpc₁ : v₁.pc = 0x80006a30 := by rw [hpcv, returnAddress_eq, b80006a14_x1 h₁]; decide
  have spv := J.sp
  obtain ⟨w₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006a30_spec hpc₁ (by
    rv_eval [spv]
    and_intros <;> valid_access hval [hb1])
  have k₂ := b80006a30_keeps h₂
  have fr₂ := b80006a30_frame h₂ (by rw [spv]; addr_omega [hb1])
  rw [spv, show s.getReg .x2 - 1344 + 1184 = s.getReg .x2 - 160 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at fr₂
  have st₂ : StepR s v₁ w₂ (Within · (s.getReg .x2 - 160) 8) :=
    StepR.ofMemFrame J.heap fr₂ (fun _ h ↦ h) (by addr_omega [hb1]) (k₂ .x2 (by decide))
  have m160 := b80006a30_m_x2_1184 h₂
  rw [spv, show s.getReg .x2 - 1344 + 1184 = s.getReg .x2 - 160 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at m160
  -- the frames
  let A : Word → Prop := fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 720) 24 ∨
    Within a (s.getReg .x2 - 160) 8
  have fA : FrameW s A := fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb1]
  have sA (a : Word) (ha : A a) : Scratch s a := by
    rcases ha with ha | ha
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1]))))))
  have all : StepR s w₀ w₂ A :=
    (((StepR.same m₁ C₀.inv.heap (k₁ .x2 (by decide))).join (st₁.weaken fun a ha ↦ Or.inl ha)).join
      (st₂.weaken fun a ha ↦ Or.inr ha))
  have C₂ := C₀.step hpre (all.weaken sA)
  have wd (j : Nat) (hj : j = 1128 ∨ j = 1280 ∨ j = 1120 ∨ j = 1144 ∨ j = 1112) :
      w₂.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = w₀.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    all.word hpre (fun y hy hs ↦ by rcases hs with hs | hs <;> addr_omega [hy, hs, hb1, hj])
      (Or.inl (by addr_omega [hb1, hj]))
  have rg (r : Reg) (hr : r ∈ ([.x8, .x18, .x20, .x21, .x23, .x24, .x25, .x26, .x27] : List Reg)) :
      w₂.getReg r = w₁.getReg r := by
    rw [k₂ r (mem_of_mem hr _), hp r (mem_of_mem hr _)]
  have rg₀ (r : Reg) (hr : r ∈ ([.x8, .x18, .x20, .x21, .x24, .x25, .x26, .x27] : List Reg)) :
      w₂.getReg r = w₀.getReg r := by
    rw [rg r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have hn₁ : heapNext w₁ = heapNext w₀ := by simp only [heapNext, m₁]
  have yv₂ : NewVecE u w₂ (s.getReg .x2 - BitVec.ofNat 64 720) y :=
    (yv₁.widen (by have := h.step.mono; rw [hn₁]; exact this)).keepP hpre hu hP st₂
      (fun a ha ↦ Or.inl (by addr_omega [ha, hb1])) (by omega) (by omega)
      (fun y hy hs ↦ by addr_omega [hy, hs, hb1])
  have e712 : s.getReg .x2 - 1344 + 632 = s.getReg .x2 - BitVec.ofNat 64 720 + 8 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have e704 : s.getReg .x2 - 1344 + 640 = s.getReg .x2 - BitVec.ofNat 64 720 + 16 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have yp : v₁.getMem (s.getReg .x2 - BitVec.ofNat 64 720 + 8) =
      w₂.getMem (s.getReg .x2 - BitVec.ofNat 64 720 + 8) :=
    (st₂.word hpre (fun y hy hs ↦ by addr_omega [hy, hs, hb1]) (Or.inl (by addr_omega [hb1]))).symm
  have yl : v₁.getMem (s.getReg .x2 - BitVec.ofNat 64 720 + 16) =
      w₂.getMem (s.getReg .x2 - BitVec.ofNat 64 720 + 16) :=
    (st₂.word hpre (fun y hy hs ↦ by addr_omega [hy, hs, hb1]) (Or.inl (by addr_omega [hb1]))).symm
  have hx13 : w₂.getReg .x13 = vecPtr w₂ (s.getReg .x2 - BitVec.ofNat 64 720) := by
    rw [b80006a30_x13 h₂, spv, e712, yp]; rfl
  have hx14 : w₂.getReg .x14 = vecLen w₂ (s.getReg .x2 - BitVec.ofNat 64 720) := by
    rw [b80006a30_x14 h₂, spv, e704, yl]; rfl
  refine ⟨w₂, hrv.trans hr₂, Or.inr ⟨y, b80006a30_pc h₂, {
    ctx := C₂
    hu := hu
    hP := hP
    x20 := by rw [rg₀ .x20 (by decide), h.regs .x20 (by decide), h20]
    x24 := by rw [rg₀ .x24 (by decide), h.regs .x24 (by decide), h24]
    x23 := by rw [rg .x23 (by decide), b80006a14_x23 h₁]; exact two_sub_toNat h.x22
    layers := by
      rw [show s.getReg .x2 - 1128 = s.getReg .x2 - BitVec.ofNat 64 1128 from rfl, wd 1128 (by omega)]
      exact h.layers
    valuesPtr := by
      rw [show s.getReg .x2 - 1280 = s.getReg .x2 - BitVec.ofNat 64 1280 from rfl, wd 1280 (by omega)]
      exact h.valuesPtr
    len := by rw [m160]; rfl
    pushed := rfl
    vlen := Nat.zero_le _
    xv := by
      rw [show s.getReg .x2 - 1120 = s.getReg .x2 - BitVec.ofNat 64 1120 from rfl,
        show s.getReg .x2 - 1144 = s.getReg .x2 - BitVec.ofNat 64 1144 from rfl,
        wd 1120 (by omega), wd 1144 (by omega)]
      exact h.xv.keepU hpre hu all fA
    yv := yv₂
    ylen := ylen
    y19 := (b80006a30_x19 h₂).trans ((b80006a30_x13 h₂).symm.trans hx13)
    y22 := (b80006a30_x22 h₂).trans ((b80006a30_x14 h₂).symm.trans hx14)
    pal := hal
    ch2 := by
      rw [show s.getReg .x2 - 1112 = s.getReg .x2 - BitVec.ofNat 64 1112 from rfl,
        wd 1112 (by omega), rg₀ .x25 (by decide)]
      exact h.ch2.keepU hpre hu all fA
    l2 := h.lens.2.2
    step := (h.step.join (all.weaken sA)).weaken fun a ha ↦ Or.inl ha },
    b80006a30_x1 h₂, ?_, rg₀ .x8 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, h.lens.1, h.lens.2.1, ?_⟩⟩
  · rw [b80006a30_x10 h₂, spv]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  · exact hx13
  · exact hx14
  · rw [b80006a30_x19 h₂, b80006a30_x13 h₂]
  · rw [b80006a30_x22 h₂, b80006a30_x14 h₂]
  · rw [b80006a30_x11 h₂, b80006a30_x12 h₂, hp .x27 (by decide), hp .x18 (by decide),
      k₁ .x27 (by decide), k₁ .x18 (by decide)]
    exact h.ch0.keepU hpre hu all fA
  · rw [rg₀ .x26 (by decide), rg₀ .x21 (by decide)]; exact h.ch1.keepU hpre hu all fA
  · refine htr.bind fun T hT ↦ ?_
    obtain ⟨T', e, -, hT'⟩ := hok T (TranscriptAt.same hpre C₀.inv m₁ hT)
    exact ⟨T', e, J.transcript hpre st₂.heap ((DFrame.of_memFrame fr₂).mono fun a ha ↦
      Or.inl (by addr_omega [ha, hb1])) hT'⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
