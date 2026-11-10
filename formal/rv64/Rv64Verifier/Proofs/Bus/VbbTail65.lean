import Rv64Verifier.Proofs.Bus.VbbTail64

/-!
# `verify_bus_balance`'s side loop: room for the side's total

`grow_one` on the totals' `Vec<E>` at `S - 632` (`growOneT`); from `0x80007bbc`'s successor, with
the totals full, through `0x80007bf4`, `grow_one` and `0x80007c14`, or with room, to `0x80007480`
with room for one more total (`Push`, `toPush`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `grow_one` on the totals. -/
theorem growOneT (hG : GrowOneFreshSpec 0x80011c78 24 8) {s z h u₀ u : MachineState}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (C : Cur s z h u)
    (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x80011c78)
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 632)
    (hraw : RawVecOk u (s.getReg .x2 - BitVec.ofNat 64 632) 24 8) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Cur s z h v ∧
      DFrame u v (fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 632) 16 ∨
        Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨ Fresh u v a) ∧
      heapNext u ≤ heapNext v ∧ (vecCap u (s.getReg .x2 - BitVec.ofNat 64 632)).toNat + 1 ≤
        (vecCap v (s.getReg .x2 - BitVec.ofNat 64 632)).toNat ∧
      bytesAt v (vecPtr v (s.getReg .x2 - BitVec.ofNat 64 632))
          ((vecCap u (s.getReg .x2 - BitVec.ofNat 64 632)).toNat * 24) =
        bytesAt u (vecPtr u (s.getReg .x2 - BitVec.ofNat 64 632))
          ((vecCap u (s.getReg .x2 - BitVec.ofNat 64 632)).toNat * 24) ∧
      RawVecOk v (s.getReg .x2 - BitVec.ofNat 64 632) 24 8 ∧
      NewBuf u v (vecPtr v (s.getReg .x2 - BitVec.ofNat 64 632))
        ((vecCap v (s.getReg .x2 - BitVec.ofNat 64 632)).toNat * 24) 8) ∨ Dead Image.code v) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have h := C.inv
  obtain ⟨o1, o2, o3⟩ := frameSlot (m := growOneStack) hpre h (n := 16) (k := 632) (by omega)
    (by omega) (by omega) (by decide)
  have pre : GrowOnePre 24 8 u := {
    heap := h.heap
    self := by
      rw [h10]; exact regionRange o1 (Nat.le_refl _) (by omega) (by addr_omega [hb1, hb3])
    raw := h10 ▸ hraw
    stack := hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
    selfFree := h10 ▸ o2
    selfStack := h10 ▸ o3 }
  obtain ⟨v, hrv, ⟨hpcv, hp, post, hfresh⟩ | hd⟩ := hG.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have hsl : stackLo u growOneStack = s.getReg .x2 - BitVec.ofNat 64 (1344 + 160) := by
    simp only [stackLo, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have fr : DFrame u v (fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 632) 16 ∨
      Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨ Fresh u v a) :=
    fun x hx' ↦ post.frame.getMem fun i hi hw ↦ hx' i hi (by
      rw [hsl, h10] at hw
      rcases hw with hw | hw | hw | hw
      · exact Or.inl hw
      · exact Or.inr (Or.inl (by addr_omega [hw, hb1]))
      · exact Or.inr (Or.inr (Or.inl hw))
      · exact Or.inr (Or.inr (Or.inr hw)))
  have st : StepS s u v (Within · (s.getReg .x2 - BitVec.ofNat 64 632) 16) :=
    ⟨fr, post.heap, post.mono, hp.reg .x2⟩
  have hcap := post.cap
  have hby := post.bytes
  have hraw' := post.raw
  rw [h10] at hcap hby hfresh hraw'
  exact ⟨v, hrv, Or.inl ⟨hpcv, hp, C.next hpre hsz st fun a ha ↦ Or.inl (by
    simp only [SlotW]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))))),
    fr, post.mono, hcap, hby, hraw', hfresh⟩⟩

/-- At `0x80007480` from `t` (past `0x80007bbc`), with room for one more total. -/
structure Push (s z h t q : MachineState) (tot : List E) : Prop where
  cur : Cur s z h q
  fr : DFrame t q fun a ↦ Within a (s.getReg .x2 - 632) 16 ∨ Within a (s.getReg .x2 - 1136) 32 ∨
    Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨ Fresh t q a
  regs : ∀ r ∈ ([.x2, .x8, .x15, .x16, .x17, .x18, .x19, .x21, .x22, .x23, .x24, .x25, .x26, .x27,
    .x28, .x30] : List Reg), q.getReg r = t.getReg r
  len : vecLen q (s.getReg .x2 - 632) = vecLen t (s.getReg .x2 - 632)
  mono : heapNext t ≤ heapNext q
  room : (vecLen t (s.getReg .x2 - 632)).toNat < (vecCap q (s.getReg .x2 - 632)).toNat
  totals : NewVecE z q (s.getReg .x2 - 632) tot
  buf : (vecPtr q (s.getReg .x2 - 632) = vecPtr t (s.getReg .x2 - 632) ∧
      vecCap q (s.getReg .x2 - 632) = vecCap t (s.getReg .x2 - 632)) ∨
    NewBuf t q (vecPtr q (s.getReg .x2 - 632)) ((vecCap q (s.getReg .x2 - 632)).toNat * 24) 8

set_option maxRecDepth 8192 in
/-- To `0x80007480` with room, through `grow_one` when the totals are full. -/
theorem toPush (hG : GrowOneFreshSpec 0x80011c78 24 8) {s z h t : MachineState} {tot : List E}
    (hpre : BusBalancePre s) (hsz : heapNext s ≤ heapNext z) (Ct : Cur s z h t)
    (hzt : heapNext z ≤ heapNext t) (TB : NewVecE z t (s.getReg .x2 - 632) tot)
    (hpc : (t.pc = 0x80007480 ∧ vecLen t (s.getReg .x2 - 632) ≠ vecCap t (s.getReg .x2 - 632)) ∨
      (t.pc = 0x80007bf4 ∧ vecLen t (s.getReg .x2 - 632) = vecCap t (s.getReg .x2 - 632))) :
    ∃ q, Reaches Image.code t q ∧ (Dead Image.code q ∨ (q.pc = 0x80007480 ∧ Push s z h t q tot)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hnx := hpre.stack.next
  rw [stackLo_eq] at hnx
  have sp : t.getReg .x2 = s.getReg .x2 - 1344 := Ct.inv.sp
  have hl := TB.vec.len
  rcases hpc with ⟨hpc, hne⟩ | ⟨hpc, heq⟩
  · refine ⟨t, Reaches.refl _, Or.inr ⟨hpc, Ct, DFrame.refl _ _, fun _ _ ↦ rfl, rfl, le_refl _, ?_, TB,
      Or.inl ⟨rfl, rfl⟩⟩⟩
    have : (vecLen t (s.getReg .x2 - 632)).toNat ≠ (vecCap t (s.getReg .x2 - 632)).toNat :=
      fun h' ↦ hne (BitVec.eq_of_toNat_eq h')
    omega
  -- `0x80007bf4`
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80007bf4_spec hpc (by
    rv_eval [sp]; and_intros <;> valid_access hval [hb1])
  have k₁ := b80007bf4_keeps h₁
  have f₁ : DFrame t v₁ (Within · (s.getReg .x2 - 1136) 32) := fun a ha ↦ h₁.frame a (by
    rv_eval [sp]
    and_intros <;> intro he <;> exact ha 0 (by decide) (by
      rw [add_ofNat_zero, he]; addr_omega [hb1]))
  have hn₁ : heapNext v₁ = heapNext t := by
    simp only [heapNext]; rw [f₁ nextAddr fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx]]
  have st₁ : StepS s t v₁ (Within · (s.getReg .x2 - 1136) 32) :=
    StepS.ofDFrame Ct.inv.heap f₁ (fun _ h ↦ h) (fun j hj hw ↦ by addr_omega [hw, hj, hb1, hnx])
      (k₁ .x2 (by decide))
  have C₁ : Cur s z h v₁ := Ct.next hpre hsz st₁ fun a ha ↦ Or.inl (by
    simp only [SlotW]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
  have w632 (k : Nat) (hk : k + 8 ≤ 24) :
      v₁.getMem (s.getReg .x2 - 632 + BitVec.ofNat 64 k) =
        t.getMem (s.getReg .x2 - 632 + BitVec.ofNat 64 k) :=
    f₁ _ fun q hq hw ↦ by addr_omega [hw, hq, hb1, hk]
  have e632 : s.getReg .x2 - 632 = s.getReg .x2 - BitVec.ofNat 64 632 := rfl
  have c₁ : vecCap v₁ (s.getReg .x2 - 632) = vecCap t (s.getReg .x2 - 632) := by
    have := w632 0 (by omega); simp only [add_ofNat_zero] at this; exact this
  have p₁ : vecPtr v₁ (s.getReg .x2 - 632) = vecPtr t (s.getReg .x2 - 632) := w632 8 (by omega)
  have l₁ : vecLen v₁ (s.getReg .x2 - 632) = vecLen t (s.getReg .x2 - 632) := w632 16 (by omega)
  have hraw₁ : RawVecOk v₁ (s.getReg .x2 - BitVec.ofNat 64 632) 24 8 := by
    have := TB.vec.raw
    simp only [RawVecOk] at this ⊢
    rw [← e632, c₁, p₁]
    exact ⟨this.1, this.2.imp_right fun h ↦ ⟨h.1, by rw [hn₁]; exact h.2⟩⟩
  -- `grow_one`
  obtain ⟨v₂, hr₂, ⟨hpc₂, hp₂, C₂, f₂, hm₂, hcap₂, hby₂, hraw₂, hnew₂⟩ | hd⟩ :=
    growOneT hG hpre hsz C₁ (Reaches.refl _) (b80007bf4_pc h₁)
      (by rw [b80007bf4_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]) hraw₁
  swap
  · exact ⟨v₂, hr₁.trans hr₂, Or.inl hd⟩
  rw [← e632] at hcap₂ hby₂ hraw₂ hnew₂
  have sp₂ : v₂.getReg .x2 = s.getReg .x2 - 1344 := C₂.inv.sp
  -- `0x80007c14`
  obtain ⟨q, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80007c14_spec (by
    rw [hpc₂, returnAddress_eq, b80007bf4_x1 h₁]; decide) (by
    rv_eval [sp₂]; and_intros <;> valid_access hval [hb1])
  have k₃ := b80007c14_keeps h₃
  have m₃ := b80007c14_mem_same h₃
  have Cq : Cur s z h q := C₂.next hpre hsz (A := fun _ ↦ False)
    (StepS.same m₃ C₂.inv.heap (k₃ .x2 (by decide))) fun _ h ↦ h.elim
  have f₂' : DFrame v₁ v₂ fun a ↦ Within a (s.getReg .x2 - 632) 16 ∨
      Within a (s.getReg .x2 - 4544) 3200 ∨ Within a nextAddr 8 ∨ Fresh t v₂ a :=
    f₂.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨a1, a2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr ⟨by rw [← hn₁]; exact a1, a2⟩))
  have hnq : heapNext q = heapNext v₂ := by simp only [heapNext, m₃]
  have frq : DFrame t q fun a ↦ Within a (s.getReg .x2 - 632) 16 ∨
      Within a (s.getReg .x2 - 1136) 32 ∨ Within a (s.getReg .x2 - 4544) 3200 ∨
      Within a nextAddr 8 ∨ Fresh t q a :=
    ((f₁.mono fun a ha ↦ Or.inr (Or.inl ha)).trans f₂' fun a ha ↦ by
      rcases ha with ha | ha | ha | ⟨a1, a2⟩
      · exact Or.inl ha
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, by rw [hnq]; exact a2⟩)))).trans
      (DFrame.of_same m₃ _) fun _ h ↦ h
  -- the saved registers
  have a216 : v₂.getReg .x2 + 216 = s.getReg .x2 - 1128 := by
    rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a224 : v₂.getReg .x2 + 224 = s.getReg .x2 - 1120 := by
    rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have a232 : v₂.getReg .x2 + 232 = s.getReg .x2 - 1112 := by
    rw [sp₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have kept (j : Nat) (h1 : 1112 ≤ j) (h2 : j ≤ 1128) :
      v₂.getMem (s.getReg .x2 - BitVec.ofNat 64 j) = v₁.getMem (s.getReg .x2 - BitVec.ofNat 64 j) :=
    f₂ _ fun q hq hw ↦ by
      have hE := C₂.inv.heap.hi
      rcases hw with hw | hw | hw | ⟨-, a2⟩
      · addr_omega [hw, hq, hb1, h1, h2]
      · addr_omega [hw, hq, hb1, h1, h2]
      · addr_omega [hw, hq, hb1, h1, h2, hnx]
      · simp only [heapNext, heapEnd] at a2 hE; addr_omega [a2, hq, hb1, h1, h2, hE]
  have s216 := b80007bf4_m_x2_216 h₁
  have s224 := b80007bf4_m_x2_224 h₁
  have s232 := b80007bf4_m_x2_232 h₁
  have t216 : t.getReg .x2 + 216 = s.getReg .x2 - 1128 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have t224 : t.getReg .x2 + 224 = s.getReg .x2 - 1120 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  have t232 : t.getReg .x2 + 232 = s.getReg .x2 - 1112 := by
    rw [sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  rw [t216] at s216
  rw [t224] at s224
  rw [t232] at s232
  have pres (r : Reg) (hr : r ∈ ([.x2, .x8, .x18, .x19, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
      List Reg)) : q.getReg r = t.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hp₂.reg r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  -- the totals
  have q632 (k : Nat) (hk : k + 8 ≤ 24) :
      q.getMem (s.getReg .x2 - 632 + BitVec.ofNat 64 k) =
        v₂.getMem (s.getReg .x2 - 632 + BitVec.ofNat 64 k) := m₃ _
  have lq : vecLen q (s.getReg .x2 - 632) = vecLen t (s.getReg .x2 - 632) := by
    refine (q632 16 (by omega)).trans (Eq.trans ?_ l₁)
    exact f₂ _ fun q hq hw ↦ by
      have hE := C₂.inv.heap.hi
      rcases hw with hw | hw | hw | ⟨-, a2⟩
      · addr_omega [hw, hq, hb1]
      · addr_omega [hw, hq, hb1]
      · addr_omega [hw, hq, hb1, hnx]
      · simp only [heapNext, heapEnd] at a2 hE; addr_omega [a2, hq, hb1, hE]
  have pq : vecPtr q (s.getReg .x2 - 632) = vecPtr v₂ (s.getReg .x2 - 632) := q632 8 (by omega)
  have cq : vecCap q (s.getReg .x2 - 632) = vecCap v₂ (s.getReg .x2 - 632) := by
    have := q632 0 (by omega); simp only [add_ofNat_zero] at this; exact this
  rw [c₁] at hcap₂ hby₂
  rw [p₁] at hby₂
  have hb₂ := hnew₂
  simp only [NewBuf] at hb₂
  have hzq : heapNext z ≤ heapNext v₁ := by rw [hn₁]; exact hzt
  have tb := TB.buf
  simp only [NewBuf] at tb
  have htE := Ct.inv.heap.hi
  have hlenE : (vecLen t (s.getReg .x2 - 632)).toNat = (vecCap t (s.getReg .x2 - 632)).toNat := by
    rw [heq]
  refine ⟨q, hr₁.trans (hr₂.trans hr₃), Or.inr ⟨b80007c14_pc h₃, Cq, frq, ?_, lq,
    by rw [hnq, ← hn₁]; exact hm₂, ?_, ⟨⟨?_, ?_⟩, ?_, ?_⟩, Or.inr ?_⟩⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> try exact pres _ (by decide)
    · rw [b80007c14_x15 h₃, a232]; exact (kept 1112 (by omega) (by omega)).trans s232
    · rw [b80007c14_x16 h₃, hp₂.reg .x9, b80007bf4_x9 h₁]
    · rw [b80007c14_x17 h₃, hp₂.reg .x20, b80007bf4_x20 h₁]
    · rw [b80007c14_x28 h₃, a224]; exact (kept 1120 (by omega) (by omega)).trans s224
    · rw [b80007c14_x30 h₃, a216]; exact (kept 1128 (by omega) (by omega)).trans s216
  · rw [cq]; omega
  · have := hraw₂
    simp only [RawVecOk, Buf] at this ⊢
    rw [pq, cq, hnq]; exact this
  · rw [lq, cq]; omega
  · rw [pq, cq]
    simp only [NewBuf, hnq]
    exact ⟨hb₂.1, hb₂.2.imp_right fun h ↦ ⟨le_trans hzq h.1, h.2⟩⟩
  · simp only [vecEs]
    rw [pq, lq, (DFrame.of_same m₃ fun _ ↦ False).eListAt fun _ _ h ↦ h, hlenE]
    rw [eListAt_eq_of_bytesAt (n := (vecCap t (s.getReg .x2 - 632)).toNat)
      (by rw [Nat.mul_comm]; exact hby₂) hb₂.1 tb.1]
    rw [f₁.eListAt fun q hq hw ↦ by
      rcases tb.2 with h0 | ⟨b1, b2⟩
      · omega
      · simp only [heapNext, heapEnd] at b2 htE; addr_omega [hw, hq, b1, b2, htE, hb1]]
    have he := TB.elems
    simp only [vecEs] at he
    rw [← hlenE]; exact he
  · rw [pq, cq]
    simp only [NewBuf, hnq, ← hn₁]
    exact hb₂

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
