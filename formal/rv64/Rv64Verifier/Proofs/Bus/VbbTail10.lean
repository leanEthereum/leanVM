import Rv64Verifier.Proofs.Bus.VbbTail9

/-!
# `verify_bus_balance` past the GKR loop: `memory[0]`'s claim's point

From `0x80006ca0` (`Scalars`) to `0x80006d2c` (`ptsA`): the frame keeps the point's length,
`values`' buffer and two limbs (an empty `memory` traps), `memory[0]` goes to `S - 248` and
`bytecode_final`'s last limb to `S - 1128`, then `copy1`.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A doubleword of the frame apart from a step's `A` keeps its value. -/
theorem StepS.slot {s v w : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (st : StepS s v w A) {x : Word} (hx : ∀ y, Within y x 8 → ¬ A y)
    (hin : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2).toNat) :
    w.getMem x = v.getMem x :=
  st.toR.word hpre hx (Or.inl hin)

/-- An `E` of the frame apart from a step's `A` keeps its value. -/
theorem StepS.eSlot {s v w : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (st : StepS s v w A) {x : Word} (hx : ∀ y, Within y x 24 → ¬ A y)
    (hin : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧ x.toNat + 24 ≤ (s.getReg .x2).toNat) :
    eAt w x = eAt v x := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  refine eAt_congr (st.slot hpre (fun y hy ↦ hx y (by addr_omega [hy, hin, hb2]))
      ⟨hin.1, by omega⟩) (st.slot hpre (fun y hy ↦ hx y (by addr_omega [hy, hin, hb2]))
      (by addr_omega [hin, hb2])) (st.slot hpre (fun y hy ↦ hx y (by addr_omega [hy, hin, hb2]))
      (by addr_omega [hin, hb2]))

/-- What the steps from `0x80006ca0` to `0x80006d2c` write in the frame. -/
def PtsAW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1280) 8 ∨ Within a (s.getReg .x2 - 1144) 8 ∨
    Within a (s.getReg .x2 - 1128) 24 ∨ Within a (s.getReg .x2 - 248) 24 ∨
    Within a (s.getReg .x2 - 608) 24

/-- At `0x80006d2c`, past `memory[0]` and the first copy. -/
structure PtsA (s q w : MachineState) (state : GkrState) : Prop where
  inv : Inv s w
  step : StepS s q w (PtsAW s)
  regs : ∀ r ∈ ([.x19, .x20, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg),
    w.getReg r = q.getReg r
  x9 : w.getReg .x9 = logMem s
  x18 : w.getReg .x18 = logMem s * 16 + logMem s * 8
  c0 : NewVecR s w (w.getReg .x8) (w.getReg .x21) (logMem s) (state.point.take (logMem s).toNat)
  m0 : eAt w (s.getReg .x2 - 248) = eAt q (q.getReg .x8)
  valuesPtr : w.getMem (s.getReg .x2 - 1280) = q.getReg .x19
  pointLen : w.getMem (s.getReg .x2 - 1144) = q.getReg .x21
  bf2 : w.getMem (s.getReg .x2 - 1128) = q.getMem (s.getReg .x2 - 584)
  bf1 : w.getMem (s.getReg .x2 - 1120) = q.getReg .x11
  mf2 : w.getMem (s.getReg .x2 - 1112) = q.getReg .x23
  len : q.getReg .x9 ≠ 0

theorem ptsA (hT : TryAllocZeroedSpec) (hM : MemcpySpec 0x800126e4)
    {bev : MachineState → Word → List E → Option E} {s q : MachineState} {k : Start}
    {state : GkrState} {mem : List E} {mf bf : E} (hpre : BusBalancePre s)
    (Sc : Scalars bev s q k state mem mf bf) (hpc : q.pc = 0x80006ca0) :
    ∃ w, Reaches Image.code q w ∧ (Dead Image.code w ∨ (w.pc = 0x80006d2c ∧ PtsA s q w state)) := by
  obtain ⟨hb1, hb2, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := Sc.inv.sp
  obtain ⟨u₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006ca0_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80006ca0_keeps h₁
  by_cases hz : q.getReg .x9 = 0
  · obtain ⟨u₂, hr₂, h₂⟩ :=
      Sym.BlockSpec.reaches b80006cb4_spec (b80006ca0_pc_not_taken h₁ hz) trivial
    exact ⟨u₂, hr₁.trans hr₂, Or.inl (dead_of_fetch (by
      rw [b80006cb4_pc h₂]; exact Option.isNone_iff_eq_none.mp (by decide +kernel)))⟩
  have pc₁ := b80006ca0_pc_taken h₁ hz
  have fr₁ : DFrame q u₁ fun a ↦ Within a (s.getReg .x2 - 1280) 8 ∨
      Within a (s.getReg .x2 - 1144) 8 ∨ Within a (s.getReg .x2 - 1128) 24 := fun a ha ↦
    h₁.frame a (by
      rv_eval [sp]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; addr_omega [hb1]))
  have st₁ : StepS s q u₁ fun a ↦ Within a (s.getReg .x2 - 1280) 8 ∨
      Within a (s.getReg .x2 - 1144) 8 ∨ Within a (s.getReg .x2 - 1128) 24 :=
    StepS.ofDFrame Sc.inv.heap fr₁ (fun _ h ↦ h) (fun i hi hw ↦ by
      rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb1]) (k₁ .x2 (by decide))
  have I₁ := Sc.inv.afterR hpre (fun a ha ↦ by
    rcases ha with ha | ha | ha <;> addr_omega [ha, hb1]) st₁.toR
  have sp₁ : u₁.getReg .x2 = s.getReg .x2 - 1344 := I₁.sp
  have hpos : 0 < (q.getReg .x9).toNat := by
    rcases Nat.eq_zero_or_pos (q.getReg .x9).toNat with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq h0) hz
    · exact h0
  have hlo := hpre.heap.lo
  have hhi := Sc.inv.heap.hi
  obtain ⟨i1, i2, i3⟩ : heapNext s ≤ (q.getReg .x8).toNat ∧
      (q.getReg .x8).toNat + 24 * (q.getReg .x9).toNat ≤ heapNext q ∧
      (q.getReg .x8).toNat % 8 = 0 := by
    rw [Sc.x8, Sc.x9]
    rw [Sc.x9] at hpos
    rcases NewVecE.inHeap hpre Sc.memory with h0 | h0
    · omega
    · exact h0
  simp only [heapNext, heapEnd, heapStart] at hlo hhi i1 i2
  have hvm : ValidMemRange (q.getReg .x8) 3 :=
    heapRange i3 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have x8₁ : u₁.getReg .x8 = q.getReg .x8 := k₁ .x8 (by decide)
  have mx (j : Nat) (hj : j ≤ 16) : u₁.getMem (q.getReg .x8 + BitVec.ofNat 64 j) =
      q.getMem (q.getReg .x8 + BitVec.ofNat 64 j) :=
    fr₁ _ fun i hi hw ↦ by
      rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb1, i1, i2, hpos, hhi, hj]
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80006cb8_spec pc₁ (by
    rv_eval [sp₁, x8₁]
    and_intros
    all_goals first
      | valid_access hval [hb1]
      | valid_access hvm [i1, i2, i3, hpos, hhi]
      | addr_omega [hb1, i1, i2, hpos, hhi])
  have k₂ := b80006cb8_keeps h₂
  have fr₂ : DFrame u₁ u₂ fun a ↦ Within a (s.getReg .x2 - 248) 24 ∨
      Within a (s.getReg .x2 - 1128) 8 := fun a ha ↦
    h₂.frame a (by
      rv_eval [sp₁, x8₁]
      and_intros <;> intro he <;> exact ha 0 (by decide) (by
        rw [add_ofNat_zero, he]; addr_omega [hb1]))
  have st₂ : StepS s u₁ u₂ fun a ↦ Within a (s.getReg .x2 - 248) 24 ∨
      Within a (s.getReg .x2 - 1128) 8 :=
    StepS.ofDFrame I₁.heap fr₂ (fun _ h ↦ h) (fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hw, hi, hb1]) (k₂ .x2 (by decide))
  have I₂ := I₁.afterR hpre (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb1])
    st₂.toR
  have lm₁ : u₁.getMem (s.getReg .x2 - 1344 + 208) = logMem s := by
    rw [show s.getReg .x2 - 1344 + 208 = s.getReg .x2 - 1136 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1],
      st₁.slot hpre (fun y hy h' ↦ by rcases h' with h' | h' | h' <;> addr_omega [hy, h', hb1])
        (by constructor <;> addr_omega [hb1])]
    exact Sc.kept.lm
  have x9₂ : u₂.getReg .x9 = logMem s := by rw [b80006cb8_x9 h₂, sp₁, lm₁]
  have x11₂ : u₂.getReg .x11 = logMem s := by rw [b80006cb8_x11 h₂, sp₁, lm₁]
  have x10₂ : u₂.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 608 := by
    rw [b80006cb8_x10 h₂, sp₁]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have x27₂ : u₂.getReg .x27 = q.getReg .x27 := by rw [k₂ .x27 (by decide), k₁ .x27 (by decide)]
  have st₁₂ := st₁.trans st₂
  have hp₂ := Sc.point.keepR hpre st₁₂.toR (fun a ha ↦ by
    rcases ha with (ha | ha | ha) | ha | ha <;> addr_omega [ha, hb1])
  have hlen : state.point.length = (q.getReg .x21).toNat := by
    rw [← Sc.point.elems, eListAt_length]
  obtain ⟨w, hrw, hd | ⟨hpcw, Iw, stw, rgw, x18w, c0⟩⟩ := copy1 hT hM hpre I₂ (b80006cb8_pc h₂)
    (b80006cb8_x1 h₂) x10₂ (b80006cb8_x13 h₂) (b80006cb8_x14 h₂) x9₂ x11₂ x27₂ hp₂
    (by rw [← hlen]; exact Sc.lm)
  · exact ⟨w, hr₁.trans (hr₂.trans hrw), Or.inl hd⟩
  have kw (x : Word) (hx : ∀ y, Within y x 8 → ¬ (Within y (s.getReg .x2 - 248) 24 ∨
      Within y (s.getReg .x2 - 1128) 8 ∨ Within y (s.getReg .x2 - 608) 24))
      (hin : (s.getReg .x2 - 1344).toNat ≤ x.toNat ∧ x.toNat + 8 ≤ (s.getReg .x2).toNat) :
      w.getMem x = u₁.getMem x := by
    rw [stw.slot hpre (fun y hy h' ↦ hx y hy (Or.inr (Or.inr h'))) hin,
      st₂.slot hpre (fun y hy h' ↦ hx y hy (by
        rcases h' with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h'))) hin]
  have q64 := b80006ca0_m_x2_64 h₁
  have q200 := b80006ca0_m_x2_200 h₁
  have q224 := b80006ca0_m_x2_224 h₁
  have q232 := b80006ca0_m_x2_232 h₁
  rw [sp] at q64 q200 q224 q232
  have b216 := b80006cb8_m_x2_216 h₂
  have a0 := b80006cb8_m_x2_1096 h₂
  have a1 := b80006cb8_m_x2_1104 h₂
  have a2 := b80006cb8_m_x2_1112 h₂
  rw [sp₁, x8₁] at a0 a1 a2
  rw [sp₁] at b216
  have m0₂ : eAt u₂ (s.getReg .x2 - 248) = eAt q (q.getReg .x8) := by
    refine eAt_congr ?_ ?_ ?_
    · rw [show s.getReg .x2 - 248 = s.getReg .x2 - 1344 + 1096 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], a0]
      simpa using mx 0 (by omega)
    · rw [show s.getReg .x2 - 248 + 8 = s.getReg .x2 - 1344 + 1104 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], a1]
      exact mx 8 (by omega)
    · rw [show s.getReg .x2 - 248 + 16 = s.getReg .x2 - 1344 + 1112 by
        apply BitVec.eq_of_toNat_eq; addr_omega [hb1], a2]
      exact mx 16 (by omega)
  refine ⟨w, hr₁.trans (hr₂.trans hrw), Or.inr ⟨hpcw, {
    inv := Iw
    step := (st₁₂.trans stw).weaken fun a ha ↦ by
      rcases ha with ((ha | ha | ha) | ha | ha) | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ha)))
    regs := fun r hr ↦ by
      rw [rgw r (mem_of_mem hr _), k₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
    x9 := by rw [rgw .x9 (by decide), x9₂]
    x18 := x18w
    c0 := c0
    m0 := by
      rw [stw.eSlot hpre (fun y hy h' ↦ by addr_omega [hy, h', hb1])
        (by constructor <;> addr_omega [hb1])]
      exact m0₂
    valuesPtr := by
      rw [kw _ (fun y hy h' ↦ by rcases h' with h' | h' | h' <;> addr_omega [hy, h', hb1])
        (by constructor <;> addr_omega [hb1]), show s.getReg .x2 - 1280 =
          s.getReg .x2 - 1344 + 64 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1], q64]
    pointLen := by
      rw [kw _ (fun y hy h' ↦ by rcases h' with h' | h' | h' <;> addr_omega [hy, h', hb1])
        (by constructor <;> addr_omega [hb1]), show s.getReg .x2 - 1144 =
          s.getReg .x2 - 1344 + 200 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1], q200]
    bf2 := by
      rw [stw.slot hpre (fun y hy h' ↦ by addr_omega [hy, h', hb1])
        (by constructor <;> addr_omega [hb1]), show s.getReg .x2 - 1128 =
          s.getReg .x2 - 1344 + 216 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1], b216,
        show s.getReg .x2 - 1344 + 760 = s.getReg .x2 - 584 by
          apply BitVec.eq_of_toNat_eq; addr_omega [hb1]]
      exact st₁.slot hpre (fun y hy h' ↦ by rcases h' with h' | h' | h' <;> addr_omega [hy, h', hb1])
        (by constructor <;> addr_omega [hb1])
    bf1 := by
      rw [kw _ (fun y hy h' ↦ by rcases h' with h' | h' | h' <;> addr_omega [hy, h', hb1])
        (by constructor <;> addr_omega [hb1]), show s.getReg .x2 - 1120 =
          s.getReg .x2 - 1344 + 224 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1], q224]
    mf2 := by
      rw [kw _ (fun y hy h' ↦ by rcases h' with h' | h' | h' <;> addr_omega [hy, h', hb1])
        (by constructor <;> addr_omega [hb1]), show s.getReg .x2 - 1112 =
          s.getReg .x2 - 1344 + 232 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1], q232]
    len := hz }⟩⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
