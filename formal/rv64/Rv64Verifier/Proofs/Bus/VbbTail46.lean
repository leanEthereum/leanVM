import Rv64Verifier.Proofs.Bus.VbbTail45

/-!
# `verify_bus_balance`'s side loop: `add_scaled` into the block's form

`Form::add_scaled` on the block's form at `S - 296`, its buffer allocated from `t₀`'s `NEXT` on, of
a read-only form's terms and the weight at `S - 248` (`addScaledF`); read-only terms keep their
values (`termsOf_ro`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript

/-- Read-only terms keep their values. -/
theorem termsOf_ro {s u : MachineState} (I : Inv s u) {p : Word} {m : Nat}
    (hr : RO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) p (48 * m)) :
    Layout.termsOf u p m = Layout.termsOf s p m := by
  have hb := hr.bound
  have hm := I.miss hr
  simp only [Layout.termsOf]
  refine List.map_congr_left fun q hq ↦ ?_
  have hq' := List.mem_range.mp hq
  exact (Layout.termOf_frame (toLayoutFrame I.frame) (fun x hx ↦ hm x (by addr_omega [hx, hq', hb]))
    (by addr_omega [hq', hb])).1

/-- `add_scaled(S - 296, a1, a2, S - 248)`: the block's form, its buffer from `t₀`'s `NEXT` on,
plus the read-only terms at `a1` times the weight. -/
theorem addScaledF (hAS : Layout.AddScaledSpec) {s z h t₀ u : MachineState}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (hzt : heapNext z ≤ heapNext t₀)
    (htu : heapNext t₀ ≤ heapNext u) (C : Cur s z h u) (hpc : u.pc = 0x800119cc) (h10 : u.getReg .x10 = s.getReg .x2 - 296)
    (h13 : u.getReg .x13 = s.getReg .x2 - 248) (ok : Layout.FormOk u (s.getReg .x2 - 296))
    (fb : ∀ x, Layout.formBuf u (s.getReg .x2 - 296) x → heapNext t₀ ≤ x.toNat ∧ x.toNat < heapNext u)
    (hro : RO s busBalanceStack [(s.getReg .x10, 120)] (s.getReg .x12) (u.getReg .x11)
      (48 * (u.getReg .x12).toNat))
    (tags : ∀ q < (u.getReg .x12).toNat,
      (s.getMem (u.getReg .x11 + BitVec.ofNat 64 (48 * q))).toNat ≤ 2) :
    ∃ v, Reaches Image.code u v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Cur s z h v ∧
      DFrame u v (fun a ↦ Within a (s.getReg .x2 - 296) 24 ∨ Within a (s.getReg .x2 - 4544) 3200 ∨
        Within a nextAddr 8 ∨ (heapNext t₀ ≤ a.toNat ∧ a.toNat < heapNext v)) ∧
      heapNext u ≤ heapNext v ∧ Layout.FormOk v (s.getReg .x2 - 296) ∧
      (∀ x, Layout.formBuf v (s.getReg .x2 - 296) x → heapNext t₀ ≤ x.toNat ∧ x.toNat < heapNext v) ∧
      Layout.formOf v (s.getReg .x2 - 296) = (Layout.formOf u (s.getReg .x2 - 296)).addScaled
        ⟨Layout.termsOf s (u.getReg .x11) (u.getReg .x12).toNat⟩ (eAt u (s.getReg .x2 - 248))) ∨
      Dead Image.code v) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hrs := hpre.stack.rodata
  rw [stackLo_eq] at hab hnx hrs
  have hrb : rodataBase.toNat = 2684354560 := rfl
  have I := C.inv
  have hE := I.heap.hi
  have hmu := I.mono
  have hsl : stackLo u Layout.addScaledStack = s.getReg .x2 - BitVec.ofNat 64 2512 := by
    simp only [stackLo, Layout.addScaledStack, Contracts.mulStack, I.sp]
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have hfree := hro.free
  have hst := hro.stack
  have hbd := hro.bound
  rw [stackLo_eq, stack_eq] at hst
  have hsu : heapNext s ≤ heapNext u := I.mono
  have hsz' := hsz
  simp only [Outside, heapNext, heapEnd] at hfree hE hsu htu hzt hsz'
  have pre : Layout.AddScaledPre u := {
    heap := I.heap
    stack := hpre.stack.sub 1344 I.sp (by decide) (by decide) (by decide) (by decide) (by decide)
    self := by rw [h10]; valid_sub hval [hb1]
    ok := by rw [h10]; exact ok
    other := Bus.RO.range (n := 6 * (u.getReg .x12).toNat)
      (by rw [show 8 * (6 * (u.getReg .x12).toNat) = 48 * (u.getReg .x12).toNat by omega]; exact hro)
    otherTags := fun q hq ↦ by
      simp only [Layout.MonoOk]
      rw [I.word hro (by addr_omega [hq, hbd]) (by addr_omega [hq, hbd])]
      exact tags q hq
    weight := by rw [h13]; valid_sub hval [hb1]
    rodata := I.rodata hpre
    selfFree := by rw [h10]; simp only [Outside, heapNext, heapEnd]; addr_omega [hb1, hE, hnx]
    otherFree := by
      simp only [Outside, heapNext, heapEnd]
      exact ⟨hfree.1.imp (fun h ↦ by omega) id, hfree.2⟩
    weightFree := by rw [h13]; simp only [Outside, heapNext, heapEnd]; addr_omega [hb1, hE, hnx]
    selfStack := by rw [h10, hsl]; addr_omega [hb1]
    otherStack := by rw [hsl]; addr_omega [hst, hb1, hbd]
    weightStack := by rw [h13, hsl]; addr_omega [hb1]
    selfOther := by rw [h10]; addr_omega [hst, hb1, hbd]
    selfWeight := by rw [h10, h13]; addr_omega [hb1]
    selfRodata := by rw [h10]; simp only [rodataSize] at hrs ⊢; addr_omega [hrs, hrb, hb1]
    buf := fun x hx ↦ by
      rw [h10] at hx
      have hx' := fb x hx
      simp only [heapNext] at hx'
      rw [h10, h13]
      rintro (hw | hw | hw)
      · addr_omega [hw, hx', hb1, hE]
      · rcases hfree.1 with hf | hf
        · simp only [Within] at hw; omega
        · simp only [Within] at hw; omega
      · addr_omega [hw, hx', hb1, hE] }
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hAS.call (Reaches.refl u) hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have hvm := post.mono
  have hvE := post.heap.hi
  have frL : DFrame u v fun a ↦ Within a (s.getReg .x2 - 296) 24 ∨
      Layout.formBuf u (s.getReg .x2 - 296) a ∨ Within a (s.getReg .x2 - BitVec.ofNat 64 2512) 1168 ∨
        Within a nextAddr 8 ∨ Fresh u v a := by
    have := layoutFrame hrv post.frame; rw [h10, hsl] at this; exact this
  have fr : DFrame u v fun a ↦ Within a (s.getReg .x2 - 296) 24 ∨
      Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨
        (heapNext t₀ ≤ a.toNat ∧ a.toNat < heapNext v) := frL.mono fun a ha ↦ by
    rcases ha with ha | ha | ha | ha | ⟨a1, a2⟩
    · exact Or.inl ha
    · have := fb a ha
      exact Or.inr (Or.inr (Or.inr ⟨this.1, by omega⟩))
    · exact Or.inr (Or.inl (by addr_omega [ha, hb1]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr ⟨by simp only [heapNext] at a1 ⊢; omega, a2⟩))
  have st : StepS s u v fun a ↦ Within a (s.getReg .x2 - 296) 24 ∨
      (heapNext t₀ ≤ a.toNat ∧ a.toNat < heapNext v) :=
    ⟨fr.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (Or.inl ha)
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inl (Or.inr ha), post.heap, hvm, hp.reg .x2⟩
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, C.next hpre hsz st fun a ha ↦ ?_, fr, hvm, ?_, fun x hx ↦ ?_,
    ?_⟩⟩
  · rcases ha with ha | ⟨a1, a2⟩
    · exact Or.inl (by
        simp only [SlotW]
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by addr_omega [ha, hb1])))))))
    · exact Or.inr ⟨by simp only [heapNext] at a1 ⊢; omega, a2⟩
  · have := post.ok; rw [h10] at this; exact this
  · have hb := post.buf x (by rw [h10]; exact hx)
    rw [h10] at hb
    rcases hb with hb | ⟨b1, b2⟩
    · have := fb x hb; exact ⟨this.1, by omega⟩
    · exact ⟨by simp only [heapNext] at b1 ⊢; omega, b2⟩
  · have := post.value
    rw [h10, h13, termsOf_ro I hro] at this
    exact this

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
