import Rv64Verifier.Proofs.Bus.VbbTail1

/-!
# `verify_bus_balance` past the GKR loop: `memory = next_scalars(3)`

From `0x80006ba0`: `next_scalars(3)` into `S - 608` (an `Err` written through `s2` at
`0x80006c18`), its `Vec` copied to `S - 864` and the point's capacity kept at `S - 1320`, to the
next `next_scalar`'s entry (`memoryStep`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A call of `Transcript::next_scalars`, its `Result<Vec<E>>` at `S - k`. -/
theorem nextScalarsCall (hNS : NextScalarsSpec) {s u₀ u : MachineState} (hpre : BusBalancePre s)
    (h : Inv s u) (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x80004818) {k : Nat}
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 k) (h11 : u.getReg .x11 = s.getReg .x12)
    (hk1 : 128 ≤ k) (hk2 : k ≤ 1344) (hk8 : k % 8 = 0) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      StepT s u v (s.getReg .x2 - BitVec.ofNat 64 k) 24 ∧ Inv s v ∧
      ∀ T, TranscriptAt u (s.getReg .x12) T →
        match (TM.nextScalars (u.getReg .x12).toNat).run T with
        | some (xs, T') => vecCap v (s.getReg .x2 - BitVec.ofNat 64 k) ≠ errNiche ∧
            NewVecE u v (s.getReg .x2 - BitVec.ofNat 64 k) xs ∧ TranscriptAt v (s.getReg .x12) T'
        | none => vecCap v (s.getReg .x2 - BitVec.ofNat 64 k) = errNiche) ∨
      Dead Image.code v) := by
  have pre : NextScalarsPre u := tpre hpre h (n := 24) (m := nextScalarsStack) (by omega) hk2 hk8
    (by decide) (by decide) h10 h11
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hNS.call hr hpc pre
  · have st := TFrame.stepT hpre h (by decide) h10 h11 post.frame post.heap post.mono (hp.reg .x2)
    refine ⟨v, hrv, Or.inl ⟨hpcv, hp, st,
      h.afterT hpre (inFrame hpre (by omega) hk2) st, fun T hT ↦ ?_⟩⟩
    have hv := post.value T (h11 ▸ hT)
    rw [h10, h11] at hv
    exact hv
  · exact ⟨v, hrv, Or.inr hd⟩

/-- `next_scalars`' result: `Err` exactly when the mirror fails, otherwise one `Vec` for every
transcript. -/
theorem scalarsRun {u v : MachineState} {a p : Word} {n : Nat}
    (val : ∀ T, TranscriptAt u p T →
      match (TM.nextScalars n).run T with
      | some (xs, T') => vecCap v a ≠ errNiche ∧ NewVecE u v a xs ∧ TranscriptAt v p T'
      | none => vecCap v a = errNiche) :
    (vecCap v a = errNiche → ∀ T, TranscriptAt u p T → (TM.nextScalars n).run T = none) ∧
    (vecCap v a ≠ errNiche → ∃ xs, NewVecE u v a xs ∧ ∀ T, TranscriptAt u p T →
      ∃ T', (TM.nextScalars n).run T = some (xs, T') ∧ TranscriptAt v p T') := by
  constructor
  · intro hc T hT
    have h1 := val T hT
    revert h1
    rcases (TM.nextScalars n).run T with _ | ⟨xs, T'⟩
    · exact fun _ ↦ rfl
    · exact fun h1 ↦ absurd hc h1.1
  · intro hc
    have h0 := val (canonT u p) (canonT_at _ _)
    revert h0
    rcases (TM.nextScalars n).run (canonT u p) with _ | ⟨xs, T₀⟩
    · exact fun h0 ↦ absurd h0 hc
    · intro h0
      refine ⟨xs, h0.2.1, fun T hT ↦ ?_⟩
      have h1 := val T hT
      revert h1
      rcases (TM.nextScalars n).run T with _ | ⟨ys, T'⟩
      · exact fun h1 ↦ absurd h1 hc
      · intro h1
        exact ⟨T', by rw [show ys = xs from h1.2.1.elems.symm.trans h0.2.1.elems], h1.2.2⟩

/-- A `Vec<E>` header copied. -/
theorem _root_.Rv64Verifier.Transcript.NewVecE.copy {s w : MachineState} {a b : Word}
    {xs : List E} (h : NewVecE s w a xs) (e0 : w.getMem b = w.getMem a)
    (e8 : w.getMem (b + 8) = w.getMem (a + 8)) (e16 : w.getMem (b + 16) = w.getMem (a + 16)) :
    NewVecE s w b xs := by
  obtain ⟨⟨raw, len⟩, buf, el⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [RawVecOk, vecCap, vecPtr, vecLen, vecEs, e0, e8, e16] at * <;> assumption

/-- After `next_scalars(3)`, at the next `next_scalar`'s entry. -/
structure MemoryV (s w y : MachineState) (xs : List E) : Prop where
  inv : Inv s y
  regs : ∀ r ∈ ([.x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg),
    y.getReg r = w.getReg r
  x1 : y.getReg .x1 = 0x80006be8
  x10 : y.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608
  x11 : y.getReg .x11 = s.getReg .x12
  ptCap : y.getMem (s.getReg .x2 - 1320) = w.getReg .x22
  memory : NewVecE s y (s.getReg .x2 - 864) xs
  x8 : y.getReg .x8 = vecPtr y (s.getReg .x2 - 864)
  x9 : y.getReg .x9 = vecLen y (s.getReg .x2 - 864)
  step : StepR s w y fun a ↦ Within a (s.getReg .x2 - 608) 24 ∨ Within a (s.getReg .x2 - 864) 24 ∨
    Within a (s.getReg .x2 - 1320) 8

theorem memoryStep (hNS : NextScalarsSpec) {bev : MachineState → Word → List E → Option E}
    {s w : MachineState} {K : List E → TM BusResultRust} (hpre : BusBalancePre s) (h : Inv s w)
    (hpc : w.pc = 0x80006ba0) (hx18 : w.getReg .x18 = s.getReg .x10)
    (hx20 : w.getReg .x20 = s.getReg .x12)
    (htr : Tracks (prog bev s) (s.getReg .x12) s w (TM.nextScalars 3 >>= K)) :
    ∃ y, Reaches Image.code w y ∧ (Done bev s y ∨ Dead Image.code y ∨
      (y.pc = 0x8000c720 ∧ ∃ xs, MemoryV s w y xs ∧
        Tracks (prog bev s) (s.getReg .x12) s y (K xs))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  obtain ⟨u, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006ba0_spec hpc trivial
  have k₁ := b80006ba0_keeps h₁
  have m₁ := b80006ba0_mem_same h₁
  have I₁ := h.same m₁ (k₁ .x2 (by decide))
  have sp := h.sp
  have e736 : s.getReg .x2 - 1344 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  obtain ⟨v, hrv, ⟨hpcv, hp, st, J, val⟩ | hd⟩ :=
    nextScalarsCall hNS hpre I₁ hr₁ (b80006ba0_pc h₁) (k := 608)
      (by rw [b80006ba0_x10 h₁, sp, e736]) ((b80006ba0_x11 h₁).trans hx20)
      (by omega) (by omega) (by omega)
  swap
  · exact ⟨v, hrv, Or.inr (Or.inl hd)⟩
  rw [b80006ba0_x12 h₁] at val
  obtain ⟨herr, hok⟩ := scalarsRun val
  have sp' := J.sp
  have hpc' : v.pc = 0x80006bb4 := by rw [hpcv, returnAddress_eq, b80006ba0_x1 h₁]; decide
  obtain ⟨u₁, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006bb4_spec hpc' (by
    rv_eval [sp']
    and_intros <;> valid_access hval [hb1])
  have k₂ := b80006bb4_keeps h₂
  have m₂ := b80006bb4_mem_same h₂
  have I₂ := J.same m₂ (k₂ .x2 (by decide))
  have x18₂ : u₁.getReg .x18 = s.getReg .x10 := by
    rw [k₂ .x18 (by decide), hp .x18 (by decide), k₁ .x18 (by decide), hx18]
  by_cases hc : vecCap v (s.getReg .x2 - BitVec.ofNat 64 608) = errNiche
  · have pc₂ := b80006bb4_pc_taken h₂ (by rw [sp', e736]; exact hc)
    have ho := hpre.out
    obtain ⟨u₂, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80006c18_spec pc₂ (by
      rv_eval [x18₂]
      and_intros <;> exact Region.valid ho (by addr_omega [ho]) (by addr_omega [ho])
        (by addr_omega [ho]))
    obtain ⟨t, hrt, hdone⟩ := errDoneAt (bev := bev) hpre I₂ x18₂ (by omega)
      (b80006c18_frame h₃ (by rw [x18₂]; addr_omega [ho])) ((b80006c18_keeps h₃) .x2 (by decide))
      (b80006c18_pc h₃) (by rw [b80006c18_m_x18_0 h₃, b80006bb4_x11 h₂])
      (htr.fail fun T hT ↦ herr hc T (TranscriptAt.same hpre h m₁ hT))
    exact ⟨t, hrv.trans (hr₂.trans (hr₃.trans hrt)), Or.inl hdone⟩
  have pc₂ := b80006bb4_pc_not_taken h₂ (by rw [sp', e736]; exact hc)
  obtain ⟨xs, hxs, run⟩ := hok hc
  have sp₂ : u₁.getReg .x2 = s.getReg .x2 - 1344 := I₂.sp
  obtain ⟨y, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80006bc8_spec pc₂ (by
    rv_eval [sp₂]
    and_intros <;> valid_access hval [hb1])
  have k₃ := b80006bc8_keeps h₃
  have fr₃ : DFrame u₁ y fun a ↦ Within a (s.getReg .x2 - 864) 24 ∨
      Within a (s.getReg .x2 - 1320) 8 := fun a ha ↦
    h₃.frame a (by
      rv_eval [sp₂]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; addr_omega [hb1]))
  have st₃ : StepR s u₁ y fun a ↦ Within a (s.getReg .x2 - 864) 24 ∨
      Within a (s.getReg .x2 - 1320) 8 :=
    StepR.ofDFrame I₂.heap fr₃ (fun _ h ↦ h) (fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hb1]) (k₃ .x2 (by decide))
  have I₃ := I₂.afterR hpre (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb1]) st₃
  have st₂ : StepR s v u₁ (fun _ ↦ False) := StepR.same m₂ J.heap (k₂ .x2 (by decide))
  have hin : (s.getReg .x2 - 1344).toNat ≤ (s.getReg .x2 - BitVec.ofNat 64 608).toNat ∧
      (s.getReg .x2 - BitVec.ofNat 64 608).toNat + 24 ≤ (s.getReg .x2).toNat := by
    addr_omega [hb1]
  have hv₃ : NewVecE s y (s.getReg .x2 - BitVec.ofNat 64 608) xs :=
    ((hxs.widen I₁.mono).keepR hpre st₂ (fun _ h ↦ h.elim) hin fun _ _ h ↦ h).keepR hpre st₃
      (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb1]) hin
      fun y' hy h' ↦ by rcases h' with h' | h' <;> addr_omega [hy, h', hb1]
  have yk (j : Nat) (hj : j ≤ 16) : y.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + BitVec.ofNat 64 j) =
      v.getMem (s.getReg .x2 - BitVec.ofNat 64 608 + BitVec.ofNat 64 j) := by
    rw [fr₃ _ (fun i hi hw ↦ by rcases hw with hw | hw <;> addr_omega [hw, hi, hb1, hj]), m₂]
  have w480 := b80006bc8_m_x2_480 h₃
  have w488 := b80006bc8_m_x2_488 h₃
  have w496 := b80006bc8_m_x2_496 h₃
  have w24 := b80006bc8_m_x2_24 h₃
  rw [b80006bb4_x10 h₂, sp'] at w480
  rw [b80006bb4_x8 h₂, sp'] at w488
  rw [b80006bb4_x9 h₂, sp'] at w496
  rw [sp₂] at w480 w488 w496 w24
  have hmem : NewVecE s y (s.getReg .x2 - 864) xs := hv₃.copy
    (by
      rw [show s.getReg .x2 - 864 = s.getReg .x2 - 1344 + 480 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], w480, e736]
      simpa using (yk 0 (by omega)).symm)
    (by
      rw [show s.getReg .x2 - 864 + 8 = s.getReg .x2 - 1344 + 488 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], w488,
        show s.getReg .x2 - 1344 + 744 = s.getReg .x2 - BitVec.ofNat 64 608 + BitVec.ofNat 64 8 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
      exact (yk 8 (by omega)).symm)
    (by
      rw [show s.getReg .x2 - 864 + 16 = s.getReg .x2 - 1344 + 496 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], w496,
        show s.getReg .x2 - 1344 + 752 = s.getReg .x2 - BitVec.ofNat 64 608 + BitVec.ofNat 64 16 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
      exact (yk 16 (by omega)).symm)
  refine ⟨y, hrv.trans (hr₂.trans hr₃), Or.inr (Or.inr ⟨b80006bc8_pc h₃, xs, {
    inv := I₃
    regs := fun r hr ↦ by
      rw [k₃ r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), hp r (mem_of_mem hr _),
        k₁ r (mem_of_mem hr _)]
    x1 := b80006bc8_x1 h₃
    x10 := by rw [b80006bc8_x10 h₃, sp₂, e736]
    x11 := by
      rw [b80006bc8_x11 h₃, k₂ .x20 (by decide), hp .x20 (by decide), k₁ .x20 (by decide), hx20]
    ptCap := by
      rw [show s.getReg .x2 - 1320 = s.getReg .x2 - 1344 + 24 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], w24, k₂ .x22 (by decide),
        hp .x22 (by decide), k₁ .x22 (by decide)]
    memory := hmem
    x8 := by
      rw [vecPtr, show s.getReg .x2 - 864 + 8 = s.getReg .x2 - 1344 + 488 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], w488, k₃ .x8 (by decide), b80006bb4_x8 h₂,
        sp']
    x9 := by
      rw [vecLen, show s.getReg .x2 - 864 + 16 = s.getReg .x2 - 1344 + 496 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], w496, k₃ .x9 (by decide), b80006bb4_x9 h₂,
        sp']
    step := ((((StepR.same m₁ h.heap (k₁ .x2 (by decide))).trans st.toR).trans st₂).trans
      st₃).weaken fun a ha ↦ by
        rcases ha with ((ha | ha) | ha) | ha | ha
        · exact False.elim ha
        · exact Or.inl ha
        · exact False.elim ha
        · exact Or.inr (Or.inl ha)
        · exact Or.inr (Or.inr ha) }, ?_⟩)⟩
  refine (htr.bind fun T hT ↦ run T (TranscriptAt.same hpre h m₁ hT)).keep fun T hT ↦ ?_
  exact I₂.transcript hpre I₃.heap (fr₃.mono fun a ha ↦
    Or.inl (by rcases ha with ha | ha <;> addr_omega [ha, hb1])) (TranscriptAt.same hpre J m₂ hT)

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
