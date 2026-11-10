import Rv64Verifier.Proofs.Bus.VbbGkrMul

/-!
# `verify_bus_balance`: an iteration's claim check

In checked mode, each child's product (`loop*`, `MulDone`), saved at `S - 608`, `S - 584`,
`S - 560`; copied to `S - 248` by `memcpy`, `poly_eval` at the combiner into `S - 608`, compared
with the sumcheck's claim limb by limb (a mismatch to `0x800070f8`, `Err`).
-/

namespace Rv64Verifier.Proofs.Bus.VerifyBusBalance
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Runtime
  Rv64Verifier.Model Rv64Verifier.Bus Rv64Verifier.Transcript Rv64Verifier.Blocks.F26
  Rv64Verifier.Contracts
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- A product loop's exit: the accumulator holds the child's product. -/
structure MulDone (s z w : MachineState) (k : Start) (cnt : E) (P : Word) (l : List E) : Prop where
  ctx : Ctx s w k cnt P
  regs : ∀ r ∈ ([.x8, .x18, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg),
    w.getReg r = z.getReg r
  acc : eAt w (s.getReg .x2 - BitVec.ofNat 64 720) = l.foldl (· * ·) 1
  step : StepR s z w fun a ↦ Within a (s.getReg .x2 - BitVec.ofNat 64 720) 24 ∨
    Within a (s.getReg .x2 - BitVec.ofNat 64 248) 32
  tr : ∀ T, TranscriptAt z (s.getReg .x12) T → TranscriptAt w (s.getReg .x12) T

/-- The product loop entered at `0x8000685c` over a non-empty child, to `0x800068a8`. -/
theorem loop8000685c (hMul : MulSpec) {s z : MachineState} {k : Start} {cnt : E} {P p lw : Word}
    {l : List E} (hpre : BusBalancePre s) (C : Ctx s z k cnt P) (hpc : z.pc = 0x8000685c)
    (hp : z.getReg .x27 = p) (hlw : z.getReg .x18 = lw) (hv : HeapVec s z p lw l) (hne : lw ≠ 0)
    (hacc : eAt z (s.getReg .x2 - BitVec.ofNat 64 720) = 1) :
    ∃ w, Reaches Image.code z w ∧ (Dead Image.code w ∨ (w.pc = 0x800068a8 ∧ MulDone s z w k cnt P l)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := C.inv.sp
  obtain ⟨c, V⟩ := hv
  have hle := V.le
  have hb := V.buf
  have hel := V.elems
  have hlen : 0 < lw.toNat := Nat.pos_of_ne_zero fun h0 ↦ hne (BitVec.eq_of_toNat_eq h0)
  simp only [NewBuf] at hb
  obtain ⟨hp8, hp1, hp2⟩ : p.toNat % 8 = 0 ∧ heapNext s ≤ p.toNat ∧
      p.toNat + 24 * lw.toNat ≤ heapNext z := by
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · omega
    · exact ⟨hb.1, b1, by omega⟩
  have hh := C.inv.heap.hi
  simp only [heapNext, heapEnd] at hh hp2
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000685c_spec hpc trivial
  have k₁ := b8000685c_keeps h₁
  have m₁ := b8000685c_mem_same h₁
  have C₁ := C.step hpre (StepR.same m₁ C.inv.heap (k₁ .x2 (by decide)))
  have hn₁ : heapNext z₁ = heapNext z := by simp only [heapNext, m₁]
  have M0 : MulAt s z₁ z₁ k cnt P p lw.toNat l 0 := {
    ctx := C₁
    x19 := by rw [b8000685c_x19 h₁, hp]; simp
    x9 := by
      rw [b8000685c_x9 h₁, hp, hlw]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
      have : (16 : Word).toNat = 16 := rfl
      have : (8 : Word).toNat = 8 := rfl
      simp only [*]
      omega
    regs := fun _ _ ↦ rfl
    acc := by rw [eAt_congr (m₁ _) (m₁ _) (m₁ _), hacc]; rfl
    step := StepR.same (fun _ ↦ rfl) C₁.inv.heap rfl
    tr := fun _ h ↦ h }
  have hl₁ : eListAt z₁ p lw.toNat = l := by
    rw [← hel]; exact eListAt_congr fun i _ ↦ eAt_congr (m₁ _) (m₁ _) (m₁ _)
  obtain ⟨w, hrw, hd | ⟨hw, hpcw⟩⟩ :=
    mulLoop (Q := fun i w ↦ MulAt s z₁ w k cnt P p lw.toNat l i) (head := 0x80006870) (exit := 0x800068a8)
      (fun i w hi h hpc ↦ mulBody80006870 hMul hpre hl₁ hp8 hp1
        (by rw [hn₁]; simp only [heapNext]; omega) h hi hpc)
      lw.toNat 0 z₁ (by omega) hlen M0 (b8000685c_pc h₁)
  · exact ⟨w, hr₁.trans hrw, Or.inl hd⟩
  refine ⟨w, hr₁.trans hrw, Or.inr ⟨hpcw, {
    ctx := hw.ctx
    regs := fun r hr ↦ by rw [hw.regs r hr, k₁ r (mem_of_mem hr _)]
    acc := by rw [hw.acc, List.take_of_length_le (by rw [← hel, eListAt_length])]
    step := (StepR.same m₁ C.inv.heap (k₁ .x2 (by decide))).join hw.step
    tr := fun T hT ↦ hw.tr T (TranscriptAt.same hpre C.inv m₁ hT) }⟩⟩

/-- The product loop entered at `0x800068d0` over a non-empty child, to `0x8000691c`. -/
theorem loop800068d0 (hMul : MulSpec) {s z : MachineState} {k : Start} {cnt : E} {P p lw : Word}
    {l : List E} (hpre : BusBalancePre s) (C : Ctx s z k cnt P) (hpc : z.pc = 0x800068d0)
    (hp : z.getReg .x26 = p) (hlw : z.getReg .x21 = lw) (hv : HeapVec s z p lw l) (hne : lw ≠ 0)
    (hacc : eAt z (s.getReg .x2 - BitVec.ofNat 64 720) = 1) :
    ∃ w, Reaches Image.code z w ∧ (Dead Image.code w ∨ (w.pc = 0x8000691c ∧ MulDone s z w k cnt P l)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := C.inv.sp
  obtain ⟨c, V⟩ := hv
  have hle := V.le
  have hb := V.buf
  have hel := V.elems
  have hlen : 0 < lw.toNat := Nat.pos_of_ne_zero fun h0 ↦ hne (BitVec.eq_of_toNat_eq h0)
  simp only [NewBuf] at hb
  obtain ⟨hp8, hp1, hp2⟩ : p.toNat % 8 = 0 ∧ heapNext s ≤ p.toNat ∧
      p.toNat + 24 * lw.toNat ≤ heapNext z := by
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · omega
    · exact ⟨hb.1, b1, by omega⟩
  have hh := C.inv.heap.hi
  simp only [heapNext, heapEnd] at hh hp2
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800068d0_spec hpc trivial
  have k₁ := b800068d0_keeps h₁
  have m₁ := b800068d0_mem_same h₁
  have C₁ := C.step hpre (StepR.same m₁ C.inv.heap (k₁ .x2 (by decide)))
  have hn₁ : heapNext z₁ = heapNext z := by simp only [heapNext, m₁]
  have M0 : MulAt s z₁ z₁ k cnt P p lw.toNat l 0 := {
    ctx := C₁
    x19 := by rw [b800068d0_x19 h₁, hp]; simp
    x9 := by
      rw [b800068d0_x9 h₁, hp, hlw]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
      have : (16 : Word).toNat = 16 := rfl
      have : (8 : Word).toNat = 8 := rfl
      simp only [*]
      omega
    regs := fun _ _ ↦ rfl
    acc := by rw [eAt_congr (m₁ _) (m₁ _) (m₁ _), hacc]; rfl
    step := StepR.same (fun _ ↦ rfl) C₁.inv.heap rfl
    tr := fun _ h ↦ h }
  have hl₁ : eListAt z₁ p lw.toNat = l := by
    rw [← hel]; exact eListAt_congr fun i _ ↦ eAt_congr (m₁ _) (m₁ _) (m₁ _)
  obtain ⟨w, hrw, hd | ⟨hw, hpcw⟩⟩ :=
    mulLoop (Q := fun i w ↦ MulAt s z₁ w k cnt P p lw.toNat l i) (head := 0x800068e4) (exit := 0x8000691c)
      (fun i w hi h hpc ↦ mulBody800068e4 hMul hpre hl₁ hp8 hp1
        (by rw [hn₁]; simp only [heapNext]; omega) h hi hpc)
      lw.toNat 0 z₁ (by omega) hlen M0 (b800068d0_pc h₁)
  · exact ⟨w, hr₁.trans hrw, Or.inl hd⟩
  refine ⟨w, hr₁.trans hrw, Or.inr ⟨hpcw, {
    ctx := hw.ctx
    regs := fun r hr ↦ by rw [hw.regs r hr, k₁ r (mem_of_mem hr _)]
    acc := by rw [hw.acc, List.take_of_length_le (by rw [← hel, eListAt_length])]
    step := (StepR.same m₁ C.inv.heap (k₁ .x2 (by decide))).join hw.step
    tr := fun T hT ↦ hw.tr T (TranscriptAt.same hpre C.inv m₁ hT) }⟩⟩

/-- The product loop entered at `0x80006954` over a non-empty child, to `0x800069a0`. -/
theorem loop80006954 (hMul : MulSpec) {s z : MachineState} {k : Start} {cnt : E} {P p lw : Word}
    {l : List E} (hpre : BusBalancePre s) (C : Ctx s z k cnt P) (hpc : z.pc = 0x80006954)
    (hp : z.getMem (z.getReg .x2 + 232) = p) (hlw : z.getReg .x25 = lw) (hv : HeapVec s z p lw l) (hne : lw ≠ 0)
    (hacc : eAt z (s.getReg .x2 - BitVec.ofNat 64 720) = 1) :
    ∃ w, Reaches Image.code z w ∧ (Dead Image.code w ∨ (w.pc = 0x800069a0 ∧ MulDone s z w k cnt P l)) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := C.inv.sp
  obtain ⟨c, V⟩ := hv
  have hle := V.le
  have hb := V.buf
  have hel := V.elems
  have hlen : 0 < lw.toNat := Nat.pos_of_ne_zero fun h0 ↦ hne (BitVec.eq_of_toNat_eq h0)
  simp only [NewBuf] at hb
  obtain ⟨hp8, hp1, hp2⟩ : p.toNat % 8 = 0 ∧ heapNext s ≤ p.toNat ∧
      p.toNat + 24 * lw.toNat ≤ heapNext z := by
    rcases hb.2 with h0 | ⟨b1, b2⟩
    · omega
    · exact ⟨hb.1, b1, by omega⟩
  have hh := C.inv.heap.hi
  simp only [heapNext, heapEnd] at hh hp2
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80006954_spec hpc (by
    rv_eval [sp]
    valid_access hval [hb1])
  have k₁ := b80006954_keeps h₁
  have m₁ := b80006954_mem_same h₁
  have C₁ := C.step hpre (StepR.same m₁ C.inv.heap (k₁ .x2 (by decide)))
  have hn₁ : heapNext z₁ = heapNext z := by simp only [heapNext, m₁]
  have M0 : MulAt s z₁ z₁ k cnt P p lw.toNat l 0 := {
    ctx := C₁
    x19 := by rw [b80006954_x19 h₁, hp]; simp
    x9 := by
      rw [b80006954_x9 h₁, hp, hlw]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
      have : (16 : Word).toNat = 16 := rfl
      have : (8 : Word).toNat = 8 := rfl
      simp only [*]
      omega
    regs := fun _ _ ↦ rfl
    acc := by rw [eAt_congr (m₁ _) (m₁ _) (m₁ _), hacc]; rfl
    step := StepR.same (fun _ ↦ rfl) C₁.inv.heap rfl
    tr := fun _ h ↦ h }
  have hl₁ : eListAt z₁ p lw.toNat = l := by
    rw [← hel]; exact eListAt_congr fun i _ ↦ eAt_congr (m₁ _) (m₁ _) (m₁ _)
  obtain ⟨w, hrw, hd | ⟨hw, hpcw⟩⟩ :=
    mulLoop (Q := fun i w ↦ MulAt s z₁ w k cnt P p lw.toNat l i) (head := 0x80006968) (exit := 0x800069a0)
      (fun i w hi h hpc ↦ mulBody80006968 hMul hpre hl₁ hp8 hp1
        (by rw [hn₁]; simp only [heapNext]; omega) h hi hpc)
      lw.toNat 0 z₁ (by omega) hlen M0 (b80006954_pc h₁)
  · exact ⟨w, hr₁.trans hrw, Or.inl hd⟩
  refine ⟨w, hr₁.trans hrw, Or.inr ⟨hpcw, {
    ctx := hw.ctx
    regs := fun r hr ↦ by rw [hw.regs r hr, k₁ r (mem_of_mem hr _)]
    acc := by rw [hw.acc, List.take_of_length_le (by rw [← hel, eListAt_length])]
    step := (StepR.same m₁ C.inv.heap (k₁ .x2 (by decide))).join hw.step
    tr := fun T hT ↦ hw.tr T (TranscriptAt.same hpre C.inv m₁ hT) }⟩⟩

/-- What a product phase writes: the accumulator, the previous product's slot `S - j`, `S - 248`. -/
def PhA (s : MachineState) (j : Nat) (a : Word) : Prop :=
  Within a (s.getReg .x2 - BitVec.ofNat 64 720) 24 ∨ Within a (s.getReg .x2 - BitVec.ofNat 64 j) 24 ∨
    Within a (s.getReg .x2 - BitVec.ofNat 64 248) 32

theorem PhA.scratch {s : MachineState} (hpre : BusBalancePre s) {j : Nat} (hj : 200 ≤ j ∧ j ≤ 840)
    {a : Word} (h : PhA s j a) : Scratch s a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  rcases h with h | h | h <;>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by addr_omega [h, hb1, hj]))))))

theorem PhA.frameW {s : MachineState} (hpre : BusBalancePre s) {j : Nat} (hj : 200 ≤ j ∧ j ≤ 840) :
    FrameW s (PhA s j) := fun _ h ↦ Scratch.frameW hpre _ (h.scratch hpre hj)

/-- A product phase from its first block to the loop's exit. -/
structure Phase (s z y : MachineState) (k : Start) (cnt : E) (P : Word) (j : Nat) (l : List E) :
    Prop where
  ctx : Ctx s y k cnt P
  regs : ∀ r ∈ ([.x8, .x18, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27] : List Reg),
    y.getReg r = z.getReg r
  acc : eAt y (s.getReg .x2 - BitVec.ofNat 64 720) = l.foldl (· * ·) 1
  step : StepR s z y (PhA s j)
  tr : ∀ T, TranscriptAt z (s.getReg .x12) T → TranscriptAt y (s.getReg .x12) T

/-- The block at `0x8000684c` and the product loop after it, to `0x800068a8`. -/
theorem phase8000684c (hMul : MulSpec) {s z : MachineState} {k : Start} {cnt : E} {P p lw : Word}
    {l : List E} (hpre : BusBalancePre s) (C : Ctx s z k cnt P) (hpc : z.pc = 0x8000684c)
    (h24 : z.getReg .x24 = 1) (hp : z.getReg .x27 = p) (hlw : z.getReg .x18 = lw)
    (hv : HeapVec s z p lw l) :
    ∃ y, Reaches Image.code z y ∧ (Dead Image.code y ∨ (y.pc = 0x800068a8 ∧
      Phase s z y k cnt P 720 l )) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := C.inv.sp
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000684c_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b8000684c_keeps h₁
  have fr : DFrame z z₁ (PhA s 720) := fun a ha ↦ h₁.frame a (by
    rv_eval [sp]
    and_intros <;> intro he <;> exact ha 0 (by decide) (by
      rw [add_ofNat_zero, he]; simp only [PhA]; addr_omega [hb1]))
  have st₁ : StepR s z z₁ (PhA s 720) := StepR.ofDFrame C.inv.heap fr (fun _ h ↦ h)
    (fun i hi hw ↦ by simp only [PhA] at hw; rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb1])
    (k₁ .x2 (by decide))
  have C₁ := C.step hpre (st₁.weaken fun a ha ↦ PhA.scratch hpre (by omega) ha)
  have l0 := b8000684c_m_x2_624 h₁
  have l1 := b8000684c_m_x2_632 h₁
  have l2 := b8000684c_m_x2_640 h₁
  rw [sp, show s.getReg .x2 - 1344 + 624 = s.getReg .x2 - BitVec.ofNat 64 720 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l0
  rw [sp, show s.getReg .x2 - 1344 + 632 = s.getReg .x2 - BitVec.ofNat 64 720 + 8 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l1
  rw [sp, show s.getReg .x2 - 1344 + 640 = s.getReg .x2 - BitVec.ofNat 64 720 + 16 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l2
  have acc₁ : eAt z₁ (s.getReg .x2 - BitVec.ofNat 64 720) = 1 :=
    eAt_eq_of_limbs (by rw [l0, l1, l2, h24, limbs_one])
  have tr₁ (T : TState) (hT : TranscriptAt z (s.getReg .x12) T) :
      TranscriptAt z₁ (s.getReg .x12) T :=
    C.inv.transcript hpre st₁.heap (fr.mono fun a ha ↦ Or.inl (by
      simp only [PhA] at ha; rcases ha with ha | ha | ha <;> addr_omega [ha, hb1])) hT
  obtain ⟨c, V⟩ := hv
  by_cases hz : lw = 0
  · have hl : l = [] := by rw [← V.elems, hz]; rfl
    subst hl
    refine ⟨z₁, hr₁, Or.inr ⟨b8000684c_pc_taken h₁ (by rw [hlw, hz]), {
      ctx := C₁
      regs := fun r hr ↦ k₁ r (mem_of_mem hr _)
      acc := acc₁
      step := st₁
      tr := tr₁ }⟩⟩
  have hpc₁ := b8000684c_pc_not_taken h₁ (by rw [hlw]; exact hz)
  obtain ⟨y, hry, hd | ⟨hpcy, M⟩⟩ := loop8000685c hMul hpre C₁ hpc₁ (p := p) (lw := lw) (by rw [k₁ .x27 (by decide), hp])
    (by rw [k₁ .x18 (by decide), hlw]) (HeapVec.keepG hpre st₁ (PhA.frameW hpre (by omega))
      ⟨c, V⟩) hz acc₁
  · exact ⟨y, hr₁.trans hry, Or.inl hd⟩
  refine ⟨y, hr₁.trans hry, Or.inr ⟨hpcy, {
    ctx := M.ctx
    regs := fun r hr ↦ by rw [M.regs r hr, k₁ r (mem_of_mem hr _)]
    acc := M.acc
    step := st₁.join (M.step.weaken fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inr ha))
    tr := fun T hT ↦ M.tr T (tr₁ T hT) }⟩⟩

/-- The block at `0x800068a8` and the product loop after it, to `0x8000691c`. -/
theorem phase800068a8 (hMul : MulSpec) {s z : MachineState} {k : Start} {cnt : E} {P p lw : Word}
    {l : List E} (hpre : BusBalancePre s) (C : Ctx s z k cnt P) (hpc : z.pc = 0x800068a8)
    (h24 : z.getReg .x24 = 1) (hp : z.getReg .x26 = p) (hlw : z.getReg .x21 = lw)
    (hv : HeapVec s z p lw l) :
    ∃ y, Reaches Image.code z y ∧ (Dead Image.code y ∨ (y.pc = 0x8000691c ∧
      Phase s z y k cnt P 608 l  ∧
      eAt y (s.getReg .x2 - BitVec.ofNat 64 608) = eAt z (s.getReg .x2 - BitVec.ofNat 64 720))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := C.inv.sp
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800068a8_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b800068a8_keeps h₁
  have fr : DFrame z z₁ (PhA s 608) := fun a ha ↦ h₁.frame a (by
    rv_eval [sp]
    and_intros <;> intro he <;> exact ha 0 (by decide) (by
      rw [add_ofNat_zero, he]; simp only [PhA]; addr_omega [hb1]))
  have st₁ : StepR s z z₁ (PhA s 608) := StepR.ofDFrame C.inv.heap fr (fun _ h ↦ h)
    (fun i hi hw ↦ by simp only [PhA] at hw; rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb1])
    (k₁ .x2 (by decide))
  have C₁ := C.step hpre (st₁.weaken fun a ha ↦ PhA.scratch hpre (by omega) ha)
  have l0 := b800068a8_m_x2_624 h₁
  have l1 := b800068a8_m_x2_632 h₁
  have l2 := b800068a8_m_x2_640 h₁
  rw [sp, show s.getReg .x2 - 1344 + 624 = s.getReg .x2 - BitVec.ofNat 64 720 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l0
  rw [sp, show s.getReg .x2 - 1344 + 632 = s.getReg .x2 - BitVec.ofNat 64 720 + 8 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l1
  rw [sp, show s.getReg .x2 - 1344 + 640 = s.getReg .x2 - BitVec.ofNat 64 720 + 16 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l2
  have acc₁ : eAt z₁ (s.getReg .x2 - BitVec.ofNat 64 720) = 1 :=
    eAt_eq_of_limbs (by rw [l0, l1, l2, h24, limbs_one])
  have v0 := b800068a8_m_x2_736 h₁
  have v1 := b800068a8_m_x2_744 h₁
  have v2 := b800068a8_m_x2_752 h₁
  rw [sp, show s.getReg .x2 - 1344 + 736 = s.getReg .x2 - BitVec.ofNat 64 608 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 624 =
      s.getReg .x2 - BitVec.ofNat 64 720 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at v0
  rw [sp, show s.getReg .x2 - 1344 + 744 = s.getReg .x2 - BitVec.ofNat 64 608 + 8 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 632 =
      s.getReg .x2 - BitVec.ofNat 64 720 + 8 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at v1
  rw [sp, show s.getReg .x2 - 1344 + 752 = s.getReg .x2 - BitVec.ofNat 64 608 + 16 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 640 =
      s.getReg .x2 - BitVec.ofNat 64 720 + 16 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at v2
  have save₁ : eAt z₁ (s.getReg .x2 - BitVec.ofNat 64 608) =
      eAt z (s.getReg .x2 - BitVec.ofNat 64 720) := eAt_congr v0 v1 v2
  have tr₁ (T : TState) (hT : TranscriptAt z (s.getReg .x12) T) :
      TranscriptAt z₁ (s.getReg .x12) T :=
    C.inv.transcript hpre st₁.heap (fr.mono fun a ha ↦ Or.inl (by
      simp only [PhA] at ha; rcases ha with ha | ha | ha <;> addr_omega [ha, hb1])) hT
  obtain ⟨c, V⟩ := hv
  by_cases hz : lw = 0
  · have hl : l = [] := by rw [← V.elems, hz]; rfl
    subst hl
    refine ⟨z₁, hr₁, Or.inr ⟨b800068a8_pc_taken h₁ (by rw [hlw, hz]), {
      ctx := C₁
      regs := fun r hr ↦ k₁ r (mem_of_mem hr _)
      acc := acc₁
      step := st₁
      tr := tr₁ }, save₁⟩⟩
  have hpc₁ := b800068a8_pc_not_taken h₁ (by rw [hlw]; exact hz)
  obtain ⟨y, hry, hd | ⟨hpcy, M⟩⟩ := loop800068d0 hMul hpre C₁ hpc₁ (p := p) (lw := lw) (by rw [k₁ .x26 (by decide), hp])
    (by rw [k₁ .x21 (by decide), hlw]) (HeapVec.keepG hpre st₁ (PhA.frameW hpre (by omega))
      ⟨c, V⟩) hz acc₁
  · exact ⟨y, hr₁.trans hry, Or.inl hd⟩
  refine ⟨y, hr₁.trans hry, Or.inr ⟨hpcy, {
    ctx := M.ctx
    regs := fun r hr ↦ by rw [M.regs r hr, k₁ r (mem_of_mem hr _)]
    acc := M.acc
    step := st₁.join (M.step.weaken fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inr ha))
    tr := fun T hT ↦ M.tr T (tr₁ T hT) }, by
      rw [M.step.eAtFrame hpre (by omega) (by omega) fun y hy hs ↦ by
        rcases hs with hs | hs <;> addr_omega [hy, hs, hb1]]
      exact save₁⟩⟩

/-- The block at `0x8000691c` and the product loop after it, to `0x800069a0`. -/
theorem phase8000691c (hMul : MulSpec) {s z : MachineState} {k : Start} {cnt : E} {P p lw : Word}
    {l : List E} (hpre : BusBalancePre s) (C : Ctx s z k cnt P) (hpc : z.pc = 0x8000691c)
    (h24 : z.getReg .x24 = 1) (hp : z.getMem (z.getReg .x2 + 232) = p) (hlw : z.getReg .x25 = lw)
    (hv : HeapVec s z p lw l) :
    ∃ y, Reaches Image.code z y ∧ (Dead Image.code y ∨ (y.pc = 0x800069a0 ∧
      Phase s z y k cnt P 584 l  ∧
      eAt y (s.getReg .x2 - BitVec.ofNat 64 584) = eAt z (s.getReg .x2 - BitVec.ofNat 64 720))) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 4544) 568 := hpre.stack.valid
  have sp := C.inv.sp
  obtain ⟨z₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000691c_spec hpc (by
    rv_eval [sp]
    and_intros <;> valid_access hval [hb1])
  have k₁ := b8000691c_keeps h₁
  have fr : DFrame z z₁ (PhA s 584) := fun a ha ↦ h₁.frame a (by
    rv_eval [sp]
    and_intros <;> intro he <;> exact ha 0 (by decide) (by
      rw [add_ofNat_zero, he]; simp only [PhA]; addr_omega [hb1]))
  have st₁ : StepR s z z₁ (PhA s 584) := StepR.ofDFrame C.inv.heap fr (fun _ h ↦ h)
    (fun i hi hw ↦ by simp only [PhA] at hw; rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb1])
    (k₁ .x2 (by decide))
  have C₁ := C.step hpre (st₁.weaken fun a ha ↦ PhA.scratch hpre (by omega) ha)
  have l0 := b8000691c_m_x2_624 h₁
  have l1 := b8000691c_m_x2_632 h₁
  have l2 := b8000691c_m_x2_640 h₁
  rw [sp, show s.getReg .x2 - 1344 + 624 = s.getReg .x2 - BitVec.ofNat 64 720 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l0
  rw [sp, show s.getReg .x2 - 1344 + 632 = s.getReg .x2 - BitVec.ofNat 64 720 + 8 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l1
  rw [sp, show s.getReg .x2 - 1344 + 640 = s.getReg .x2 - BitVec.ofNat 64 720 + 16 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at l2
  have acc₁ : eAt z₁ (s.getReg .x2 - BitVec.ofNat 64 720) = 1 :=
    eAt_eq_of_limbs (by rw [l0, l1, l2, h24, limbs_one])
  have v0 := b8000691c_m_x2_760 h₁
  have v1 := b8000691c_m_x2_768 h₁
  have v2 := b8000691c_m_x2_776 h₁
  rw [sp, show s.getReg .x2 - 1344 + 760 = s.getReg .x2 - BitVec.ofNat 64 584 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 624 =
      s.getReg .x2 - BitVec.ofNat 64 720 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at v0
  rw [sp, show s.getReg .x2 - 1344 + 768 = s.getReg .x2 - BitVec.ofNat 64 584 + 8 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 632 =
      s.getReg .x2 - BitVec.ofNat 64 720 + 8 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at v1
  rw [sp, show s.getReg .x2 - 1344 + 776 = s.getReg .x2 - BitVec.ofNat 64 584 + 16 by
    apply BitVec.eq_of_toNat_eq; addr_omega [hb1], show s.getReg .x2 - 1344 + 640 =
      s.getReg .x2 - BitVec.ofNat 64 720 + 16 by apply BitVec.eq_of_toNat_eq; addr_omega [hb1]] at v2
  have save₁ : eAt z₁ (s.getReg .x2 - BitVec.ofNat 64 584) =
      eAt z (s.getReg .x2 - BitVec.ofNat 64 720) := eAt_congr v0 v1 v2
  have tr₁ (T : TState) (hT : TranscriptAt z (s.getReg .x12) T) :
      TranscriptAt z₁ (s.getReg .x12) T :=
    C.inv.transcript hpre st₁.heap (fr.mono fun a ha ↦ Or.inl (by
      simp only [PhA] at ha; rcases ha with ha | ha | ha <;> addr_omega [ha, hb1])) hT
  obtain ⟨c, V⟩ := hv
  by_cases hz : lw = 0
  · have hl : l = [] := by rw [← V.elems, hz]; rfl
    subst hl
    refine ⟨z₁, hr₁, Or.inr ⟨b8000691c_pc_taken h₁ (by rw [hlw, hz]), {
      ctx := C₁
      regs := fun r hr ↦ k₁ r (mem_of_mem hr _)
      acc := acc₁
      step := st₁
      tr := tr₁ }, save₁⟩⟩
  have hpc₁ := b8000691c_pc_not_taken h₁ (by rw [hlw]; exact hz)
  obtain ⟨y, hry, hd | ⟨hpcy, M⟩⟩ := loop80006954 hMul hpre C₁ hpc₁ (p := p) (lw := lw) (by rw [k₁ .x2 (by decide), ← hp]; exact fr _ fun i hi hw ↦ by simp only [PhA] at hw; rcases hw with hw | hw | hw <;> addr_omega [hw, hi, hb1, sp])
    (by rw [k₁ .x25 (by decide), hlw]) (HeapVec.keepG hpre st₁ (PhA.frameW hpre (by omega))
      ⟨c, V⟩) hz acc₁
  · exact ⟨y, hr₁.trans hry, Or.inl hd⟩
  refine ⟨y, hr₁.trans hry, Or.inr ⟨hpcy, {
    ctx := M.ctx
    regs := fun r hr ↦ by rw [M.regs r hr, k₁ r (mem_of_mem hr _)]
    acc := M.acc
    step := st₁.join (M.step.weaken fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (Or.inr ha))
    tr := fun T hT ↦ M.tr T (tr₁ T hT) }, by
      rw [M.step.eAtFrame hpre (by omega) (by omega) fun y hy hs ↦ by
        rcases hs with hs | hs <;> addr_omega [hy, hs, hb1]]
      exact save₁⟩⟩

end Rv64Verifier.Proofs.Bus.VerifyBusBalance
