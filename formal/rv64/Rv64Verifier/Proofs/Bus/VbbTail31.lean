import Rv64Verifier.Proofs.Bus.VbbTail30

/-!
# `verify_bus_balance`'s side loop: one iteration's frame

An iteration from the side loop's head `h` writes the frame's slots `SlotW` (`LoopW` but the heap)
and the heap allocated from `z` on (`SideW`); `Cur` is that, with `Inv`. A callee's step that keeps
to `SideW` keeps `Cur` (`Cur.next`); what `SlotW` misses, and the heap below `z`'s `NEXT`, keep
their values (`Cur.slot`, `Cur.low`). `mulCallC` is `mul` on three of the frame's slots.
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Contracts

/-- The frame's slots the side loop writes: `LoopW` but the heap. -/
def SlotW (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 1304) 24 ∨ Within a (s.getReg .x2 - 1272) 16 ∨
    Within a (s.getReg .x2 - 1248) 8 ∨ Within a (s.getReg .x2 - 1216) 72 ∨
    Within a (s.getReg .x2 - 1136) 32 ∨ Within a (s.getReg .x2 - 632) 24 ∨
    Within a (s.getReg .x2 - 320) 216

/-- What an iteration writes up to `u`: the slots, and the heap from `z`'s `NEXT` to `u`'s. -/
def SideW (s z u : MachineState) (a : Word) : Prop :=
  SlotW s a ∨ (heapNext z ≤ a.toNat ∧ a.toNat < heapNext u)

/-- Within an iteration from `h`. -/
structure Cur (s z h u : MachineState) : Prop where
  inv : Inv s u
  step : StepS s h u (SideW s z u)

theorem SlotW.frame {s : MachineState} (hpre : BusBalancePre s) {a : Word} (ha : SlotW s a) :
    (s.getReg .x2 - 1344).toNat ≤ a.toNat ∧ a.toNat < (s.getReg .x2 - 104).toNat := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  simp only [SlotW] at ha
  rcases ha with ha | ha | ha | ha | ha | ha | ha <;> constructor <;> addr_omega [ha, hb1]

theorem SideW.w {s z u v : MachineState} (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z)
    (hv : HeapOk v) (huv : heapNext u ≤ heapNext v) {a : Word} (ha : SideW s z u a) :
    W s v a ∧ ¬ Within a (s.getReg .x2 - 104) 104 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hh := hv.hi
  rcases ha with ha | ⟨h1, h2⟩
  · have := SlotW.frame hpre ha
    exact ⟨Or.inr (Or.inr (Or.inl (by rw [stackLo_eq, stack_eq]; addr_omega [this, hb1]))),
      by addr_omega [this, hb1]⟩
  · simp only [heapNext, heapEnd] at hh huv hsz h1 h2
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp only [heapNext]; omega,
      by simp only [heapNext]; omega⟩))), by addr_omega [h1, h2, hh, huv, hb1]⟩

theorem SideW.mono {s z u v : MachineState} (h : heapNext u ≤ heapNext v) {a : Word}
    (ha : SideW s z u a) : SideW s z v a :=
  ha.imp_right fun ⟨h1, h2⟩ ↦ ⟨h1, by omega⟩

theorem Cur.start {s z h : MachineState} (I : Inv s h) : Cur s z h h :=
  ⟨I, StepS.same (fun _ ↦ rfl) I.heap rfl⟩

/-- A step that writes within `SideW` keeps `Cur`. -/
theorem Cur.next {s z h u v : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (hsz : heapNext s ≤ heapNext z) (C : Cur s z h u) (st : StepS s u v A)
    (hA : ∀ a, A a → SideW s z v a) : Cur s z h v := by
  refine ⟨C.inv.step hpre st.frame (fun a ha ↦ ?_) st.heap st.mono st.sp,
    (C.step.trans st).weaken fun a ha ↦ ?_⟩
  · rcases ha with ha | ha | ha | ha
    · exact SideW.w hpre hsz st.heap (le_refl _) (hA a ha)
    · exact Loc.w hpre C.inv st.heap (Or.inl (by
        obtain ⟨hb1, -, -, -⟩ := bounds hpre; addr_omega [ha, hb1]))
    · exact Loc.w hpre C.inv st.heap (Or.inr (Or.inl ha))
    · exact Loc.w hpre C.inv st.heap (Or.inr (Or.inr ha))
  · rcases ha with ha | ha
    · exact SideW.mono st.mono ha
    · exact hA a ha

/-- A frame slot that `SlotW` misses keeps its doubleword. -/
theorem Cur.slot {s z h u : MachineState} (hpre : BusBalancePre s) (C : Cur s z h u) {j : Nat}
    (hj : 8 ≤ j) (hj2 : j ≤ 1344) (hx : ∀ y, Within y (s.getReg .x2 - BitVec.ofNat 64 j) 8 →
      ¬ SlotW s y) :
    u.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = h.getMem (s.getReg .x2 - BitVec.ofNat 64 j) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hh := C.inv.heap.hi
  refine C.step.slot' hpre hj hj2 fun y hy hy' ↦ ?_
  rcases hy' with hy' | ⟨h1, h2⟩
  · exact hx y hy hy'
  · simp only [heapNext, heapEnd] at hh h2
    addr_omega [hy, h2, hh, hb1, hj, hj2]

/-- The heap below `z`'s `NEXT` keeps its doublewords. -/
theorem Cur.low {s z h u : MachineState} (hpre : BusBalancePre s) (C : Cur s z h u)
    (Ih : Inv s h) (hzh : heapNext z ≤ heapNext h) {x : Word} (h1 : heapStart ≤ x.toNat)
    (h2 : x.toNat + 8 ≤ heapNext z) : u.getMem x = h.getMem x :=
  C.step.heapWord hpre hzh Ih.heap (fun a ha hh ↦ by
    rcases ha with ha | ⟨b1, -⟩
    · have hf := SlotW.frame hpre ha
      obtain ⟨hb1, -, -, -⟩ := bounds hpre
      simp only [heapStart] at hh
      have hi := Ih.heap.hi
      simp only [heapNext, heapEnd] at hi hzh hh
      addr_omega [hf, hh, hb1, hi, hzh]
    · omega) h1 h2

/-- `mul` on the frame's slots `S - o` (the result, in `S - [320, 104)`), `S - a`, `S - b`. -/
theorem mulCallC (hMul : MulSpec) {s z h u₀ u : MachineState} (hpre : BusBalancePre s)
    (hsz : heapNext s ≤ heapNext z) (C : Cur s z h u) (hr : Reaches Image.code u₀ u)
    (hpc : u.pc = 0x80008c48) {o a b : Nat}
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 o)
    (h11 : u.getReg .x11 = s.getReg .x2 - BitVec.ofNat 64 a)
    (h12 : u.getReg .x12 = s.getReg .x2 - BitVec.ofNat 64 b)
    (ho : 128 ≤ o ∧ o ≤ 320 ∧ o % 8 = 0) (ha : 128 ≤ a ∧ a ≤ 1344 ∧ a % 8 = 0)
    (hb : 128 ≤ b ∧ b ≤ 1344 ∧ b % 8 = 0) (hoa : o + 24 ≤ a ∨ a + 24 ≤ o)
    (hob : o + 24 ≤ b ∨ b + 24 ≤ o) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Cur s z h v ∧
      DFrame u v (fun x ↦ Within x (s.getReg .x2 - BitVec.ofNat 64 o) 24 ∨
        Within x (s.getReg .x2 - BitVec.ofNat 64 2368) 1024) ∧ heapNext v = heapNext u ∧
      eAt v (s.getReg .x2 - BitVec.ofNat 64 o) =
        eAt u (s.getReg .x2 - BitVec.ofNat 64 a) * eAt u (s.getReg .x2 - BitVec.ofNat 64 b)) ∨
      Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hrs := hpre.stack.rodata
  rw [stackLo_eq] at hrs
  have hrb : rodataBase.toNat = 2684354560 := rfl
  have h := C.inv
  have hsl : stackLo u mulStack = s.getReg .x2 - BitVec.ofNat 64 2368 := by
    simp only [stackLo, mulStack, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have rs : RtStack u mulStack :=
    hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
  have pre : MulPre u := {
    out := by rw [h10]; valid_sub hval [hb1, ho]
    lhs := by rw [h11]; valid_sub hval [hb1, ha]
    rhs := by rw [h12]; valid_sub hval [hb1, hb]
    stack := rs.toStackOk
    outLhs := by rw [h10, h11]; addr_omega [hb1, ho, ha, hoa]
    outRhs := by rw [h10, h12]; addr_omega [hb1, ho, hb, hob]
    outStack := by rw [h10, hsl]; addr_omega [hb1, ho]
    lhsStack := by rw [h11, hsl]; addr_omega [hb1, ha]
    rhsStack := by rw [h12, hsl]; addr_omega [hb1, hb]
    rodata := h.rodata hpre
    stackRodata := by rw [hsl]; simp only [rodataSize] at hrs ⊢; addr_omega [hrs, hrb, hb1] }
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hMul.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have fr : DFrame u v fun x ↦ Within x (s.getReg .x2 - BitVec.ofNat 64 o) 24 ∨
      Within x (s.getReg .x2 - BitVec.ofNat 64 2368) 1024 :=
    (DFrame.of_two fun x h1 h2 ↦ post.frame x h1 h2).mono fun x hx ↦ by
      rw [h10, hsl] at hx; exact hx
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hx, hw, hi, hb1, ho])
  have st : StepS s u v fun x ↦ Within x (s.getReg .x2 - BitVec.ofNat 64 o) 24 :=
    ⟨fr.mono fun x hx ↦ by
      rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inl (by addr_omega [hx, hb1])), ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩,
      hn.ge, hp.reg .x2⟩
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, C.next hpre hsz st fun x hx ↦ Or.inl ?_, fr, hn, ?_⟩⟩
  · simp only [SlotW]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [hx, hb1, ho]))))))
  · have := post.value
    rw [h10, h11, h12] at this
    exact this

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
