import Rv64Verifier.Proofs.Bus.VbbInit

/-!
# `verify_bus_balance`: the spine

The function's contract from three stages: the start (`start`, proved), the GKR loop
(`0x80006614` to `0x80006b60`, `GkrStage`) and the rest (`0x80006b60` to the return, `TailStage`),
the last two stated here, still to prove. With depth zero the loop is skipped (`depthZero`).

At `0x80006b60` (`AfterGkr`) the loop's state is in place: `point` in `s6` (capacity), `s11`
(pointer), `s5` (length), the tree values in `values` at `S - 176`, `count`'s limbs in `a1`, `a2`,
`a3`, and the code runs `tail`, the rest of the mirror.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A `Vec<E>` held in registers (capacity, pointer, length), its buffer allocated since `s`. -/
structure NewVecR (s u : MachineState) (cap ptr len : Word) (xs : List E) : Prop where
  le : len.toNat ≤ cap.toNat
  buf : NewBuf s u ptr (cap.toNat * 24) 8
  elems : eListAt u ptr len.toNat = xs

/-- After the GKR loop, at `0x80006b60`. -/
structure AfterGkr (bev : MachineState → Word → List E → Option E) (s u : MachineState)
    (k : Start) (cnt : E) (state : GkrState) : Prop where
  inv : Inv s u
  kept : Kept s u k
  x18 : u.getReg .x18 = s.getReg .x10
  x20 : u.getReg .x20 = s.getReg .x12
  x24 : u.getReg .x24 = vecPtr s (s.getReg .x11 + 24)
  x19 : u.getReg .x19 = vecPtr u (s.getReg .x2 - 176)
  x11 : u.getReg .x11 = k.count0
  x12 : u.getReg .x12 = k.count1
  cntEq : cnt = eOf3 k.count0 k.count1 (u.getReg .x13)
  point : NewVecR s u (u.getReg .x22) (u.getReg .x27) (u.getReg .x21) state.point
  values : NewVecE s u (s.getReg .x2 - 176) state.values
  tracks : Tracks (prog bev s) (s.getReg .x12) s u (tail bev s k cnt state)

/-- The GKR loop with a positive depth, to `0x80006b60`, or out. -/
def GkrStage (bev : MachineState → Word → List E → Option E) : Prop :=
  ∀ s u k sh cnt, BusBalancePre s → AfterStart bev s u k sh cnt → u.pc = 0x80006614 →
    ∃ v, Reaches Image.code u v ∧ (Done bev s v ∨ Dead Image.code v ∨
      ∃ state, v.pc = 0x80006b60 ∧ AfterGkr bev s v k cnt state)

/-- From `0x80006b60` to the return. -/
def TailStage (bev : MachineState → Word → List E → Option E) : Prop :=
  ∀ s u k cnt state, BusBalancePre s → AfterGkr bev s u k cnt state → u.pc = 0x80006b60 →
    ∃ t, Reaches Image.code u t ∧ (Done bev s t ∨ Dead Image.code t)

/-- Depth zero: `point` empty, the state the loop starts from. -/
theorem depthZero {bev : MachineState → Word → List E → Option E} {s u : MachineState}
    {k : Start} {sh cnt : E} (hpre : BusBalancePre s) (h : AfterStart bev s u k sh cnt)
    (hpc : u.pc = 0x80006b54) :
    ∃ v, Reaches Image.code u v ∧ v.pc = 0x80006b60 ∧
      AfterGkr bev s v k cnt ⟨[sh, sh, cnt], []⟩ := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hd : pushDepth s = 0 := by
    rcases h.branch with ⟨-, h0⟩ | ⟨h1, -⟩
    · exact h0
    · rw [hpc] at h1; exact absurd h1 (by decide)
  obtain ⟨v, hr, h₁⟩ := Sym.BlockSpec.reaches b80006b54_spec hpc trivial
  have k₁ := b80006b54_keeps h₁
  have m₁ := b80006b54_mem_same h₁
  have sp := k₁ .x2 (by decide)
  have st : ∀ {A : Word → Prop}, StepR s u v A := StepR.same m₁ h.inv.heap sp
  refine ⟨v, hr, b80006b54_pc h₁, {
    inv := h.inv.same m₁ sp
    kept := h.kept.step hpre st
    x18 := (k₁ .x18 (by decide)).trans h.x18
    x20 := (k₁ .x20 (by decide)).trans h.x20
    x24 := (k₁ .x24 (by decide)).trans h.x24
    x19 := by
      rw [k₁ .x19 (by decide), h.x19]
      exact (m₁ _).symm
    x11 := (k₁ .x11 (by decide)).trans h.x11
    x12 := (k₁ .x12 (by decide)).trans h.x12
    cntEq := by rw [k₁ .x13 (by decide)]; exact h.cntEq
    point := by
      rw [b80006b54_x22 h₁, b80006b54_x27 h₁, b80006b54_x21 h₁]
      exact ⟨Nat.le_refl _, ⟨by decide, Or.inl rfl⟩, rfl⟩
    values := h.values.keepR hpre (st (A := fun _ ↦ False)) (fun _ h ↦ False.elim h)
      (by addr_omega [hb1]) fun _ _ h ↦ h
    tracks := by
      have := h.tracks
      rw [hd, gkrLoopM_zero, pure_bind] at this
      exact this.keep fun T hT ↦ TranscriptAt.same hpre h.inv m₁ hT }⟩

/-- **`verify_bus_balance`'s contract**, from the GKR loop's and the rest's stages and the
callees' contracts. -/
theorem verify_bus_balance_spec (hBL : BusLayoutSpec) (hS : SamplesSpec)
    (hEK : Vbb.EqKernelSpec) (hD : DuplexSpec) (hN : NextScalarSpec) (hA : AllocSpec)
    {bev : MachineState → Word → List E → Option E} (hG : GkrStage bev) (hT : TailStage bev) :
    BusBalanceSpec bev := by
  intro s hpc hpre
  obtain ⟨u, hr, hdone | hd | ⟨k, sh, cnt, h⟩⟩ := start (bev := bev) hBL hS hEK hD hN hA hpc hpre
  · exact ⟨u, hr, Or.inl hdone⟩
  · exact ⟨u, hr, Or.inr hd⟩
  have tail_ {v : MachineState} (hrv : Reaches Image.code s v) {state : GkrState}
      (hv : v.pc = 0x80006b60) (hg : AfterGkr bev s v k cnt state) :
      ∃ t, Reaches Image.code s t ∧ ((t.pc = returnAddress s ∧ Preserves s t ∧
        BusBalancePost bev s t) ∨ Dead Image.code t) := by
    obtain ⟨t, hrt, hdone | hd⟩ := hT s v k cnt state hpre hg hv
    · exact ⟨t, hrv.trans hrt, Or.inl hdone⟩
    · exact ⟨t, hrv.trans hrt, Or.inr hd⟩
  rcases h.branch with ⟨hpc₀, -⟩ | ⟨hpc₁, -⟩
  · obtain ⟨v, hrv, hv, hg⟩ := depthZero hpre h hpc₀
    exact tail_ (hr.trans hrv) hv hg
  · obtain ⟨v, hrv, hdone | hd | ⟨state, hv, hg⟩⟩ := hG s u k sh cnt hpre h hpc₁
    · exact ⟨v, hr.trans hrv, Or.inl hdone⟩
    · exact ⟨v, hr.trans hrv, Or.inr hd⟩
    · exact tail_ (hr.trans hrv) hv hg

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
