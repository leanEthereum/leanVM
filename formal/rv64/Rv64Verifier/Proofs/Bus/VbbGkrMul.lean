import Rv64Verifier.Proofs.Bus.VbbGkrNs

/-!
# `verify_bus_balance`: an iteration's products

Each child's product folded into the accumulator at `S - 720`, one `mul` per element, `self`
copied to `S - 248` first (`MulAt`, one body per loop, `mulLoop`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `mul(S - 720, S - 248, q)`, `q` an element in the heap. -/
theorem mulCallV (hMul : MulSpec) {s u₀ u : MachineState} (hpre : BusBalancePre s) (h : Inv s u)
    (hr : Reaches Image.code u₀ u) (hpc : u.pc = 0x80008c48)
    (h10 : u.getReg .x10 = s.getReg .x2 - BitVec.ofNat 64 720)
    (h11 : u.getReg .x11 = s.getReg .x2 - BitVec.ofNat 64 248) {q : Word} (h12 : u.getReg .x12 = q)
    (hq8 : q.toNat % 8 = 0) (hq1 : heapStart ≤ q.toNat) (hq2 : q.toNat + 24 ≤ heapEnd) :
    ∃ v, Reaches Image.code u₀ v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧
      StepR s u v (Within · (s.getReg .x2 - BitVec.ofNat 64 720) 24) ∧
      eAt v (s.getReg .x2 - BitVec.ofNat 64 720) =
        eAt u (s.getReg .x2 - BitVec.ofNat 64 248) * eAt u q ∧
      ∀ T, TranscriptAt u (s.getReg .x12) T → TranscriptAt v (s.getReg .x12) T) ∨
      Dead Image.code v) := by
  obtain ⟨hb1, hb2, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have hrs := hpre.stack.rodata
  have ha := hpre.stack.above
  rw [stackLo_eq] at hrs ha
  have hrb : rodataBase.toNat = 2684354560 := rfl
  have hsl : stackLo u mulStack = s.getReg .x2 - BitVec.ofNat 64 2368 := by
    simp only [stackLo, mulStack, h.sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1]
  simp only [heapStart, heapEnd] at hq1 hq2 ha
  have rs : RtStack u mulStack :=
    hpre.stack.sub 1344 h.sp (by decide) (by decide) (by decide) (by decide) (by decide)
  have hqv : ValidMemRange q 3 :=
    heapRange hq8 (by simp only [heapStart]; omega) (by simp only [heapEnd]; omega)
  have pre : MulPre u := {
    out := by rw [h10]; valid_sub hval [hb1]
    lhs := by rw [h11]; valid_sub hval [hb1]
    rhs := by rw [h12]; exact hqv
    stack := rs.toStackOk
    outLhs := by rw [h10, h11]; addr_omega [hb1]
    outRhs := by rw [h10, h12]; addr_omega [hb1, hq2, ha]
    outStack := by rw [h10, hsl]; addr_omega [hb1]
    lhsStack := by rw [h11, hsl]; addr_omega [hb1]
    rhsStack := by rw [h12, hsl]; addr_omega [hb1, hq2, ha]
    rodata := h.rodata hpre
    stackRodata := by rw [hsl]; simp only [rodataSize] at hrs ⊢; addr_omega [hrs, hrb, hb1] }
  obtain ⟨v, hrv, ⟨hpcv, hp, post⟩ | hd⟩ := hMul.call hr hpc pre
  swap
  · exact ⟨v, hrv, Or.inr hd⟩
  have fr : DFrame u v fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 720) 24 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 2368) 1024 :=
    (DFrame.of_two fun a h1 h2 ↦ post.frame a h1 h2).mono fun a ha ↦ by
      rw [h10, hsl] at ha; exact ha
  have hx := hpre.stack.next
  rw [stackLo_eq] at hx
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]
    exact congrArg BitVec.toNat (fr nextAddr fun i hi hw ↦ by
      rcases hw with hw | hw <;> addr_omega [hx, hw, hi, hb1])
  refine ⟨v, hrv, Or.inl ⟨hpcv, hp, ⟨fr.mono fun x hx ↦ ?_, ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩,
    hn.ge, hp.reg .x2⟩, ?_, fun T hT ↦ h.transcript hpre ⟨hn ▸ h.heap.lo, hn ▸ h.heap.hi⟩
      (fr.mono fun x hx ↦ Or.inl (by rcases hx with hx | hx <;> addr_omega [hx, hb1])) hT⟩⟩
  · rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [hx, hb1])))
  · have := post.value
    rw [h10, h11, h12] at this
    exact this

theorem foldl_take_succ (l : List E) (i : Nat) (hi : i < l.length) :
    (l.take (i + 1)).foldl (· * ·) 1 = (l.take i).foldl (· * ·) 1 * l.getD i 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.foldl_append,
    List.getD_eq_getElem _ _ hi]
  rfl

/-- A product loop's head after `i` of the `len` elements at `p`: the accumulator at `S - 720`. -/
structure MulAt (s v w : MachineState) (k : Start) (cnt : E) (P p : Word) (len : Nat)
    (l : List E) (i : Nat) : Prop where
  ctx : Ctx s w k cnt P
  x19 : w.getReg .x19 = p + BitVec.ofNat 64 (24 * i)
  x9 : w.getReg .x9 = p + BitVec.ofNat 64 (24 * len)
  regs : ∀ r ∈ ([.x8, .x18, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg),
    w.getReg r = v.getReg r
  acc : eAt w (s.getReg .x2 - BitVec.ofNat 64 720) = (l.take i).foldl (· * ·) 1
  step : StepR s v w fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 720) 24 ∨
    Within a (s.getReg .x2 - BitVec.ofNat 64 248) 32
  tr : ∀ T, TranscriptAt v (s.getReg .x12) T → TranscriptAt w (s.getReg .x12) T

theorem mulLoop {Q : Nat → MachineState → Prop} {head exit : Word} {len : Nat}
    (body : ∀ i w, i < len → Q i w → w.pc = head → ∃ w', Reaches Image.code w w' ∧
      (Dead Image.code w' ∨ (Q (i + 1) w' ∧ w'.pc = if i + 1 = len then exit else head))) :
    ∀ m i w, i + m = len → i < len → Q i w → w.pc = head →
      ∃ w', Reaches Image.code w w' ∧ (Dead Image.code w' ∨ (Q len w' ∧ w'.pc = exit)) := by
  intro m
  induction m with
  | zero => intro i w h1 h2; omega
  | succ m ih =>
    intro i w h1 h2 h hpc
    obtain ⟨w₁, hr₁, hd | ⟨h₁, hpc₁⟩⟩ := body i w h2 h hpc
    · exact ⟨w₁, hr₁, Or.inl hd⟩
    by_cases he : i + 1 = len
    · simp only [he, ↓reduceIte] at hpc₁
      rw [he] at h₁
      exact ⟨w₁, hr₁, Or.inr ⟨h₁, hpc₁⟩⟩
    · simp only [he, ↓reduceIte] at hpc₁
      obtain ⟨w₂, hr₂, h₂⟩ := ih (i + 1) w₁ (by omega) (by omega) h₁ hpc₁
      exact ⟨w₂, hr₁.trans hr₂, h₂⟩

/-- An `E` in a buffer allocated since the entry keeps its value across a step writing the
frame. -/
theorem StepR.eAtHeap {s v w : MachineState} {A : Word → Prop} (hpre : BusBalancePre s)
    (st : StepR s v w A) (hA : FrameW s A) {q : Word} (h1 : heapNext s ≤ q.toNat)
    (h2 : q.toNat + 24 ≤ heapNext v) : eAt w q = eAt v q := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hh := st.heap.hi
  have hm := st.mono
  have ha := hpre.stack.above
  rw [stackLo_eq] at ha
  simp only [heapNext, heapEnd] at h1 h2 hh hm ha
  have wd (j : Nat) (hj : j + 8 ≤ 24) :
      w.getMem (q + BitVec.ofNat 64 j) = v.getMem (q + BitVec.ofNat 64 j) :=
    st.word hpre (fun y hy hy' ↦ by have := hA y hy'; addr_omega [hy, this, hb1, h2, hh, hm, ha, hj])
      (Or.inr ⟨by simp only [heapNext]; addr_omega [h1, h2, hj, hh, hm],
        by simp only [heapNext]; addr_omega [h1, h2, hj, hh, hm]⟩)
  exact eAt_congr (by simpa using wd 0 (by omega)) (wd 8 (by omega)) (wd 16 (by omega))

/-- An iteration of the product loop at `0x80006870`. -/
theorem mulBody80006870 (hMul : MulSpec) {s v w : MachineState} {k : Start} {cnt : E} {P p : Word}
    {len : Nat} {l : List E} {i : Nat} (hpre : BusBalancePre s) (hl : eListAt v p len = l)
    (hp8 : p.toNat % 8 = 0) (hp1 : heapNext s ≤ p.toNat) (hp2 : p.toNat + 24 * len ≤ heapNext v)
    (h : MulAt s v w k cnt P p len l i) (hi : i < len) (hpc : w.pc = 0x80006870) :
    ∃ w', Reaches Image.code w w' ∧ (Dead Image.code w' ∨ (MulAt s v w' k cnt P p len l (i + 1) ∧
      w'.pc = if i + 1 = len then 0x800068a8 else 0x80006870)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have C := h.ctx
  have sp := C.inv.sp
  obtain ⟨w₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006870_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80006870_keeps h₁
  have fr₁ := b80006870_frame h₁ (by rw [sp]; addr_omega [hb1])
  rw [sp, show s.getReg .x2 - 1344 + 1096 = s.getReg .x2 - BitVec.ofNat 64 248 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at fr₁
  have st₁ : StepR s w w₁ (Within · (s.getReg .x2 - BitVec.ofNat 64 248) 32) :=
    StepR.ofMemFrame C.inv.heap fr₁ (fun _ h ↦ h) (by addr_omega [hb1]) (k₁ .x2 (by decide))
  have I₁ := C.inv.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₁
  have l0 := b80006870_m_x2_1096 h₁
  have l1 := b80006870_m_x2_1104 h₁
  have l2 := b80006870_m_x2_1112 h₁
  rw [sp, show s.getReg .x2 - 1344 + 1096 = s.getReg .x2 - BitVec.ofNat 64 248 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 624 =
      s.getReg .x2 - BitVec.ofNat 64 720 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l0
  rw [sp, show s.getReg .x2 - 1344 + 1104 = s.getReg .x2 - BitVec.ofNat 64 248 + 8 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 632 =
      s.getReg .x2 - BitVec.ofNat 64 720 + 8 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l1
  rw [sp, show s.getReg .x2 - 1344 + 1112 = s.getReg .x2 - BitVec.ofNat 64 248 + 16 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 640 =
      s.getReg .x2 - BitVec.ofNat 64 720 + 16 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l2
  have hcopy : eAt w₁ (s.getReg .x2 - BitVec.ofNat 64 248) =
      eAt w (s.getReg .x2 - BitVec.ofNat 64 720) := eAt_congr l0 l1 l2
  -- the element
  have hm := h.step.mono
  have hh := C.inv.heap.hi
  have hlo := hpre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hp1 hp2 hm hh hlo
  have hq : (p + BitVec.ofNat 64 (24 * i)).toNat = p.toNat + 24 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 24 * i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hel : eAt w₁ (p + BitVec.ofNat 64 (24 * i)) = l.getD i 0 := by
    rw [(h.step.join (st₁.weaken fun a ha ↦ Or.inr ha)).eAtHeap hpre
      (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb1])
      (by simp only [heapNext]; omega) (by simp only [heapNext]; omega),
      ← hl, List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact hi)]
    simp [eListAt]
  have x19₀ := h.x19
  obtain ⟨w₂, hr₂, ⟨hpc₂, hp₂, st₂, hv₂, tr₂⟩ | hd⟩ := mulCallV hMul hpre I₁ hr₁ (b80006870_pc h₁)
    (by rw [b80006870_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b80006870_x11 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b80006870_x12 h₁, x19₀]) (by rw [hq]; omega) (by simp only [heapStart]; omega)
    (by simp only [heapEnd]; omega)
  swap
  · exact ⟨w₂, hr₂, Or.inl hd⟩
  have I₂ := I₁.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₂
  obtain ⟨w₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800068a0_spec
    (by rw [hpc₂, returnAddress_eq, b80006870_x1 h₁]; decide) trivial
  have k₃ := b800068a0_keeps h₃
  have m₃ := b800068a0_mem_same h₃
  have rg (r : Reg) (hr : r ∈ ([.x8, .x9, .x18, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
      List Reg)) : w₃.getReg r = w.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hp₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have x19₂ : w₂.getReg .x19 = p + BitVec.ofNat 64 (24 * i) := by
    rw [hp₂ .x19 (by decide), k₁ .x19 (by decide), x19₀]
  have x9₂ : w₂.getReg .x9 = p + BitVec.ofNat 64 (24 * len) := by
    rw [hp₂ .x9 (by decide), k₁ .x9 (by decide), h.x9]
  have stw : StepR s w w₃ fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 720) 24 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 248) 32 :=
    (st₁.weaken fun a ha ↦ Or.inr ha).join ((st₂.weaken fun a ha ↦ Or.inl ha).join
      (StepR.same m₃ I₂.heap (k₃ .x2 (by decide))))
  refine ⟨w₃, hr₂.trans hr₃, Or.inr ⟨{
    ctx := C.step hpre (stw.weaken fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))))))
    x19 := by rw [b800068a0_x19 h₃, x19₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hq, hp2, hi]
    x9 := by rw [k₃ .x9 (by decide), x9₂]
    regs := fun r hr ↦ by rw [rg r (mem_of_mem hr _)]; exact h.regs r hr
    acc := by
      rw [eAt_congr (m₃ _) (m₃ _) (m₃ _), hv₂, hcopy, hel, h.acc,
        foldl_take_succ l i (by rw [← hl, eListAt_length]; exact hi)]
    step := h.step.join stw
    tr := fun T hT ↦ TranscriptAt.same hpre I₂ m₃ (tr₂ T (C.inv.transcript hpre I₁.heap
      ((DFrame.of_memFrame fr₁).mono fun a ha ↦ Or.inl (by addr_omega [ha, hb1])) (h.tr T hT))) }, ?_⟩⟩
  by_cases he : i + 1 = len
  · simp only [he, ↓reduceIte]
    exact b800068a0_pc_not_taken h₃ (by
      rw [x19₂, x9₂, ← he]; apply BitVec.eq_of_toNat_eq; addr_omega [hq, hp2, hi])
  · simp only [he, ↓reduceIte]
    exact b800068a0_pc_taken h₃ (by
      rw [x19₂, x9₂]
      intro hc
      have := congrArg BitVec.toNat hc
      apply he
      addr_omega [this, hq, hp2, hi])

/-- An iteration of the product loop at `0x800068e4`. -/
theorem mulBody800068e4 (hMul : MulSpec) {s v w : MachineState} {k : Start} {cnt : E} {P p : Word}
    {len : Nat} {l : List E} {i : Nat} (hpre : BusBalancePre s) (hl : eListAt v p len = l)
    (hp8 : p.toNat % 8 = 0) (hp1 : heapNext s ≤ p.toNat) (hp2 : p.toNat + 24 * len ≤ heapNext v)
    (h : MulAt s v w k cnt P p len l i) (hi : i < len) (hpc : w.pc = 0x800068e4) :
    ∃ w', Reaches Image.code w w' ∧ (Dead Image.code w' ∨ (MulAt s v w' k cnt P p len l (i + 1) ∧
      w'.pc = if i + 1 = len then 0x8000691c else 0x800068e4)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have C := h.ctx
  have sp := C.inv.sp
  obtain ⟨w₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800068e4_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b800068e4_keeps h₁
  have fr₁ := b800068e4_frame h₁ (by rw [sp]; addr_omega [hb1])
  rw [sp, show s.getReg .x2 - 1344 + 1096 = s.getReg .x2 - BitVec.ofNat 64 248 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at fr₁
  have st₁ : StepR s w w₁ (Within · (s.getReg .x2 - BitVec.ofNat 64 248) 32) :=
    StepR.ofMemFrame C.inv.heap fr₁ (fun _ h ↦ h) (by addr_omega [hb1]) (k₁ .x2 (by decide))
  have I₁ := C.inv.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₁
  have l0 := b800068e4_m_x2_1096 h₁
  have l1 := b800068e4_m_x2_1104 h₁
  have l2 := b800068e4_m_x2_1112 h₁
  rw [sp, show s.getReg .x2 - 1344 + 1096 = s.getReg .x2 - BitVec.ofNat 64 248 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 624 =
      s.getReg .x2 - BitVec.ofNat 64 720 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l0
  rw [sp, show s.getReg .x2 - 1344 + 1104 = s.getReg .x2 - BitVec.ofNat 64 248 + 8 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 632 =
      s.getReg .x2 - BitVec.ofNat 64 720 + 8 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l1
  rw [sp, show s.getReg .x2 - 1344 + 1112 = s.getReg .x2 - BitVec.ofNat 64 248 + 16 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 640 =
      s.getReg .x2 - BitVec.ofNat 64 720 + 16 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l2
  have hcopy : eAt w₁ (s.getReg .x2 - BitVec.ofNat 64 248) =
      eAt w (s.getReg .x2 - BitVec.ofNat 64 720) := eAt_congr l0 l1 l2
  -- the element
  have hm := h.step.mono
  have hh := C.inv.heap.hi
  have hlo := hpre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hp1 hp2 hm hh hlo
  have hq : (p + BitVec.ofNat 64 (24 * i)).toNat = p.toNat + 24 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 24 * i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hel : eAt w₁ (p + BitVec.ofNat 64 (24 * i)) = l.getD i 0 := by
    rw [(h.step.join (st₁.weaken fun a ha ↦ Or.inr ha)).eAtHeap hpre
      (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb1])
      (by simp only [heapNext]; omega) (by simp only [heapNext]; omega),
      ← hl, List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact hi)]
    simp [eListAt]
  have x19₀ := h.x19
  obtain ⟨w₂, hr₂, ⟨hpc₂, hp₂, st₂, hv₂, tr₂⟩ | hd⟩ := mulCallV hMul hpre I₁ hr₁ (b800068e4_pc h₁)
    (by rw [b800068e4_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b800068e4_x11 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b800068e4_x12 h₁, x19₀]) (by rw [hq]; omega) (by simp only [heapStart]; omega)
    (by simp only [heapEnd]; omega)
  swap
  · exact ⟨w₂, hr₂, Or.inl hd⟩
  have I₂ := I₁.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₂
  obtain ⟨w₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80006914_spec
    (by rw [hpc₂, returnAddress_eq, b800068e4_x1 h₁]; decide) trivial
  have k₃ := b80006914_keeps h₃
  have m₃ := b80006914_mem_same h₃
  have rg (r : Reg) (hr : r ∈ ([.x8, .x9, .x18, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
      List Reg)) : w₃.getReg r = w.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hp₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have x19₂ : w₂.getReg .x19 = p + BitVec.ofNat 64 (24 * i) := by
    rw [hp₂ .x19 (by decide), k₁ .x19 (by decide), x19₀]
  have x9₂ : w₂.getReg .x9 = p + BitVec.ofNat 64 (24 * len) := by
    rw [hp₂ .x9 (by decide), k₁ .x9 (by decide), h.x9]
  have stw : StepR s w w₃ fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 720) 24 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 248) 32 :=
    (st₁.weaken fun a ha ↦ Or.inr ha).join ((st₂.weaken fun a ha ↦ Or.inl ha).join
      (StepR.same m₃ I₂.heap (k₃ .x2 (by decide))))
  refine ⟨w₃, hr₂.trans hr₃, Or.inr ⟨{
    ctx := C.step hpre (stw.weaken fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))))))
    x19 := by rw [b80006914_x19 h₃, x19₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hq, hp2, hi]
    x9 := by rw [k₃ .x9 (by decide), x9₂]
    regs := fun r hr ↦ by rw [rg r (mem_of_mem hr _)]; exact h.regs r hr
    acc := by
      rw [eAt_congr (m₃ _) (m₃ _) (m₃ _), hv₂, hcopy, hel, h.acc,
        foldl_take_succ l i (by rw [← hl, eListAt_length]; exact hi)]
    step := h.step.join stw
    tr := fun T hT ↦ TranscriptAt.same hpre I₂ m₃ (tr₂ T (C.inv.transcript hpre I₁.heap
      ((DFrame.of_memFrame fr₁).mono fun a ha ↦ Or.inl (by addr_omega [ha, hb1])) (h.tr T hT))) }, ?_⟩⟩
  by_cases he : i + 1 = len
  · simp only [he, ↓reduceIte]
    exact b80006914_pc_not_taken h₃ (by
      rw [x19₂, x9₂, ← he]; apply BitVec.eq_of_toNat_eq; addr_omega [hq, hp2, hi])
  · simp only [he, ↓reduceIte]
    exact b80006914_pc_taken h₃ (by
      rw [x19₂, x9₂]
      intro hc
      have := congrArg BitVec.toNat hc
      apply he
      addr_omega [this, hq, hp2, hi])

/-- An iteration of the product loop at `0x80006968`. -/
theorem mulBody80006968 (hMul : MulSpec) {s v w : MachineState} {k : Start} {cnt : E} {P p : Word}
    {len : Nat} {l : List E} {i : Nat} (hpre : BusBalancePre s) (hl : eListAt v p len = l)
    (hp8 : p.toNat % 8 = 0) (hp1 : heapNext s ≤ p.toNat) (hp2 : p.toNat + 24 * len ≤ heapNext v)
    (h : MulAt s v w k cnt P p len l i) (hi : i < len) (hpc : w.pc = 0x80006968) :
    ∃ w', Reaches Image.code w w' ∧ (Dead Image.code w' ∨ (MulAt s v w' k cnt P p len l (i + 1) ∧
      w'.pc = if i + 1 = len then 0x800069a0 else 0x80006968)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have C := h.ctx
  have sp := C.inv.sp
  obtain ⟨w₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006968_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b80006968_keeps h₁
  have fr₁ := b80006968_frame h₁ (by rw [sp]; addr_omega [hb1])
  rw [sp, show s.getReg .x2 - 1344 + 1096 = s.getReg .x2 - BitVec.ofNat 64 248 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at fr₁
  have st₁ : StepR s w w₁ (Within · (s.getReg .x2 - BitVec.ofNat 64 248) 32) :=
    StepR.ofMemFrame C.inv.heap fr₁ (fun _ h ↦ h) (by addr_omega [hb1]) (k₁ .x2 (by decide))
  have I₁ := C.inv.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₁
  have l0 := b80006968_m_x2_1096 h₁
  have l1 := b80006968_m_x2_1104 h₁
  have l2 := b80006968_m_x2_1112 h₁
  rw [sp, show s.getReg .x2 - 1344 + 1096 = s.getReg .x2 - BitVec.ofNat 64 248 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 624 =
      s.getReg .x2 - BitVec.ofNat 64 720 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l0
  rw [sp, show s.getReg .x2 - 1344 + 1104 = s.getReg .x2 - BitVec.ofNat 64 248 + 8 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 632 =
      s.getReg .x2 - BitVec.ofNat 64 720 + 8 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l1
  rw [sp, show s.getReg .x2 - 1344 + 1112 = s.getReg .x2 - BitVec.ofNat 64 248 + 16 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 640 =
      s.getReg .x2 - BitVec.ofNat 64 720 + 16 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l2
  have hcopy : eAt w₁ (s.getReg .x2 - BitVec.ofNat 64 248) =
      eAt w (s.getReg .x2 - BitVec.ofNat 64 720) := eAt_congr l0 l1 l2
  -- the element
  have hm := h.step.mono
  have hh := C.inv.heap.hi
  have hlo := hpre.heap.lo
  simp only [heapNext, heapEnd, heapStart] at hp1 hp2 hm hh hlo
  have hq : (p + BitVec.ofNat 64 (24 * i)).toNat = p.toNat + 24 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 24 * i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have hel : eAt w₁ (p + BitVec.ofNat 64 (24 * i)) = l.getD i 0 := by
    rw [(h.step.join (st₁.weaken fun a ha ↦ Or.inr ha)).eAtHeap hpre
      (fun a ha ↦ by rcases ha with ha | ha <;> addr_omega [ha, hb1])
      (by simp only [heapNext]; omega) (by simp only [heapNext]; omega),
      ← hl, List.getD_eq_getElem _ _ (by rw [eListAt_length]; exact hi)]
    simp [eListAt]
  have x19₀ := h.x19
  obtain ⟨w₂, hr₂, ⟨hpc₂, hp₂, st₂, hv₂, tr₂⟩ | hd⟩ := mulCallV hMul hpre I₁ hr₁ (b80006968_pc h₁)
    (by rw [b80006968_x10 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b80006968_x11 h₁, sp]; apply BitVec.eq_of_toNat_eq; addr_omega [hb1])
    (by rw [b80006968_x12 h₁, x19₀]) (by rw [hq]; omega) (by simp only [heapStart]; omega)
    (by simp only [heapEnd]; omega)
  swap
  · exact ⟨w₂, hr₂, Or.inl hd⟩
  have I₂ := I₁.afterR hpre (fun a ha ↦ by addr_omega [ha, hb1]) st₂
  obtain ⟨w₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80006998_spec
    (by rw [hpc₂, returnAddress_eq, b80006968_x1 h₁]; decide) trivial
  have k₃ := b80006998_keeps h₃
  have m₃ := b80006998_mem_same h₃
  have rg (r : Reg) (hr : r ∈ ([.x8, .x9, .x18, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] :
      List Reg)) : w₃.getReg r = w.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hp₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have x19₂ : w₂.getReg .x19 = p + BitVec.ofNat 64 (24 * i) := by
    rw [hp₂ .x19 (by decide), k₁ .x19 (by decide), x19₀]
  have x9₂ : w₂.getReg .x9 = p + BitVec.ofNat 64 (24 * len) := by
    rw [hp₂ .x9 (by decide), k₁ .x9 (by decide), h.x9]
  have stw : StepR s w w₃ fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 720) 24 ∨
      Within a (s.getReg .x2 - BitVec.ofNat 64 248) 32 :=
    (st₁.weaken fun a ha ↦ Or.inr ha).join ((st₂.weaken fun a ha ↦ Or.inl ha).join
      (StepR.same m₃ I₂.heap (k₃ .x2 (by decide))))
  refine ⟨w₃, hr₂.trans hr₃, Or.inr ⟨{
    ctx := C.step hpre (stw.weaken fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1]))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb1])))))))
    x19 := by rw [b80006998_x19 h₃, x19₂]; apply BitVec.eq_of_toNat_eq; addr_omega [hq, hp2, hi]
    x9 := by rw [k₃ .x9 (by decide), x9₂]
    regs := fun r hr ↦ by rw [rg r (mem_of_mem hr _)]; exact h.regs r hr
    acc := by
      rw [eAt_congr (m₃ _) (m₃ _) (m₃ _), hv₂, hcopy, hel, h.acc,
        foldl_take_succ l i (by rw [← hl, eListAt_length]; exact hi)]
    step := h.step.join stw
    tr := fun T hT ↦ TranscriptAt.same hpre I₂ m₃ (tr₂ T (C.inv.transcript hpre I₁.heap
      ((DFrame.of_memFrame fr₁).mono fun a ha ↦ Or.inl (by addr_omega [ha, hb1])) (h.tr T hT))) }, ?_⟩⟩
  by_cases he : i + 1 = len
  · simp only [he, ↓reduceIte]
    exact b80006998_pc_not_taken h₃ (by
      rw [x19₂, x9₂, ← he]; apply BitVec.eq_of_toNat_eq; addr_omega [hq, hp2, hi])
  · simp only [he, ↓reduceIte]
    exact b80006998_pc_taken h₃ (by
      rw [x19₂, x9₂]
      intro hc
      have := congrArg BitVec.toNat hc
      apply he
      addr_omega [this, hq, hp2, hi])

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
