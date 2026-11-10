import Rv64Verifier.Proofs.Transcript.RoundPolySome

/-!
# `sumcheck_round_poly`'s `Some` path: the buffer and the tail's sum

`0x8000c398`: 24 bytes from the allocator (`s1`), the claim's limbs into `s7`, `s8`, `s2`, the
tail's sum (the loop at `0x8000c408`) into `a3`, `a2`, `a0` (`AtMul`, at `0x8000c428`).
-/

namespace Rv64Verifier.Transcript.RoundPoly
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F44
  Rv64Verifier.Contracts LeanVM.Protocol.Verifier
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

attribute [local rv_addr] vecPtr vecLen vecCap

theorem b8000c3d0_x15' {s t : MachineState} (h : b8000c3d0.Holds s t)
    (hb : (s.getReg .x21).toNat + 16 + 24 * (s.getReg .x20).toNat < 2 ^ 64) :
    t.getReg .x15 = s.getReg .x21 + 16 + BitVec.ofNat 64 (24 * (s.getReg .x20).toNat) :=
  h.reg_eq .x15 rfl (by rv_eval []; exact end_ptr16 _ _ hb)

/-- At `0x8000c428`: the buffer `s1` (24 bytes, after `NEXT` at the tail's return), the claim's
limbs, the tail's sum in `a3`, `a2`, `a0`, `a1` = `&eq_factor.value`. -/
structure AtMul (s w : MachineState) : Prop where
  fr : Fr s w
  x18 : w.getReg .x18 = s.getMem (s.getReg .x13 + 16)
  x23 : w.getReg .x23 = s.getMem (s.getReg .x13)
  x24 : w.getReg .x24 = s.getMem (s.getReg .x13 + 8)
  x11 : w.getReg .x11 = s.getReg .x14 + 8
  x13 : w.getReg .x13 = (Model.limbs (sumE (eListAt w (w.getReg .x21) (w.getReg .x20).toNat))).1
  x12 : w.getReg .x12 = (Model.limbs (sumE (eListAt w (w.getReg .x21) (w.getReg .x20).toNat))).2.1
  x10 : w.getReg .x10 = (Model.limbs (sumE (eListAt w (w.getReg .x21) (w.getReg .x20).toNat))).2.2
  bAl : (w.getReg .x9).toNat % 8 = 0
  bNext : heapNext w = (w.getReg .x9).toNat + 24
  room : (w.getReg .x20).toNat ≤ (w.getReg .x22).toNat
  buf : (w.getReg .x21).toNat % 8 = 0 ∧ ((w.getReg .x22).toNat * 24 = 0 ∨
    heapNext s ≤ (w.getReg .x21).toNat ∧
      (w.getReg .x21).toNat + (w.getReg .x22).toNat * 24 ≤ (w.getReg .x9).toNat)
  bLo : heapNext s ≤ (w.getReg .x9).toNat
  value : ∀ T, TranscriptAt s (s.getReg .x11) T → ∃ T',
    (TM.nextScalars ((s.getReg .x12).toNat - 1)).run T =
      some (eListAt w (w.getReg .x21) (w.getReg .x20).toNat, T') ∧
      TranscriptAt w (s.getReg .x11) T'

/-- What the sum keeps. -/
def sumKept : List Reg :=
  [.x1, .x2, .x8, .x9, .x11, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

set_option maxHeartbeats 2000000 in
theorem someSum (hA : AllocSpec) {s v : MachineState} (hpre : RoundPolyPre s)
    (hpc : v.pc = 0x8000c398) (h : TailS s v) :
    ∃ w, Reaches Image.code v w ∧ ((w.pc = 0x8000c428 ∧ AtMul s w) ∨ Done s w) := by
  have hb := bounds hpre
  have hS : 80 ≤ (s.getReg .x2).toNat := by addr_omega [hb]
  have hst := hpre.stack
  have hcl := hpre.claim
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000c398_spec hpc trivial
  have k₁ := b8000c398_keeps h₁
  have hm₁ := b8000c398_mem_same h₁
  have F₁ : Fr s v₁ := h.fr.same hS (fun r hr ↦ k₁ r (mem_of_mem hr _)) hm₁
  obtain ⟨v₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hd⟩ :=
    hA.call hr₁ (b8000c398_pc h₁) ⟨F₁.heap, by rw [b8000c398_x10 h₁]; decide⟩
  swap
  · exact ⟨v₂, hr₂, Or.inr (Or.inr hd)⟩
  have hB0 : heapNext v₁ ≤ (v₂.getReg .x10).toNat := hpost₂.above
  have hBn : heapNext v₂ = (v₂.getReg .x10).toNat + 24 := by
    rw [hpost₂.next, b8000c398_x11 h₁]; rfl
  have hBa : (v₂.getReg .x10).toNat % 8 = 0 := by
    have := hpost₂.aligned; rw [b8000c398_x10 h₁] at this; exact this
  have hBh : (v₂.getReg .x10).toNat + 24 ≤ heapEnd := hBn ▸ hpost₂.heap.hi
  have hlo := F₁.heap.lo
  have hmono := F₁.mono
  have hne : v₂.getReg .x10 ≠ 0 := fun h0 ↦ by
    rw [h0] at hB0; simp only [heapStart] at hlo; simp at hB0; omega
  have D₂ : DFrame v₁ v₂ (Within · nextAddr 8) :=
    fun a ha ↦ hpost₂.mem a fun he ↦ ha 0 (by decide) (by rw [add_ofNat_zero, he]; addr_omega [])
  have F₂ : Fr s v₂ := {
    saved := F₁.saved.step hS (hpres₂.reg .x2) (fun r hr ↦ hpres₂ r (by
        simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide))
      fun y h1 h2 ↦ D₂ y fun i hi hw ↦ by addr_omega [hw, hi, h1, h2, hb, hst.next]
    x8 := (hpres₂.reg .x8).trans F₁.x8
    heap := hpost₂.heap
    mono := by omega
    frame := (F₁.frame.mono fun a h ↦ V.mono (by omega) h).trans D₂ fun a hw ↦
      Or.inr (Or.inr (Or.inl hw)) }
  obtain ⟨v₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b8000c3a8_spec
    (by rw [hpc₂, returnAddress_eq, b8000c398_x1 h₁]; decide) trivial
  have hm₃ := b8000c3a8_mem_same h₃
  have k₃ := b8000c3a8_keeps h₃
  have F₃ : Fr s v₃ := F₂.same hS (fun r hr ↦ k₃ r (mem_of_mem hr _)) hm₃
  have x18₃ : v₃.getReg .x18 = s.getReg .x13 := by
    rw [k₃ .x18 (by decide), hpres₂.reg .x18, k₁ .x18 (by decide), h.x18]
  have c0 : v₃.getMem (s.getReg .x13) = s.getMem (s.getReg .x13) := by
    have := F₃.claim hpre (k := 0) (by decide)
    simp only [Nat.mul_zero, add_ofNat_zero] at this
    exact this
  have c8 : v₃.getMem (s.getReg .x13 + 8) = s.getMem (s.getReg .x13 + 8) :=
    F₃.claim hpre (k := 1) (by decide)
  have c16 : v₃.getMem (s.getReg .x13 + 16) = s.getMem (s.getReg .x13 + 16) :=
    F₃.claim hpre (k := 2) (by decide)
  obtain ⟨v₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b8000c3ac_spec
    (b8000c3a8_pc_not_taken h₃ hne) (by
      rv_eval [x18₃]
      and_intros <;> (refine Region.valid hcl ?_ ?_ ?_ <;> addr_omega [hcl]))
  have k₄ := b8000c3ac_keeps h₄
  have hm₄ := b8000c3ac_mem_same h₄
  have F₄ : Fr s v₄ := F₃.same hS (fun r hr ↦ k₄ r (mem_of_mem hr _)) hm₄
  -- registers through the allocator
  have kr3 (r : Reg) (hr : r ∈ [Reg.x19, .x20, .x21, .x22]) : v₃.getReg r = v.getReg r := by
    rw [k₃ r (mem_of_mem hr _), hpres₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
  have kr (r : Reg) (hr : r ∈ [Reg.x19, .x20, .x21, .x22]) : v₄.getReg r = v.getReg r := by
    rw [k₄ r (mem_of_mem hr _), kr3 r hr]
  have hm (a : Word) (ha : a ≠ nextAddr) : v₄.getMem a = v.getMem a := by
    rw [hm₄, hm₃, hpost₂.mem a ha, hm₁]
  have x9₄ : v₄.getReg .x9 = v₂.getReg .x10 := by rw [b8000c3ac_x9 h₄, k₃ .x10 (by decide)]
  have nx₄ : heapNext v₄ = heapNext v₂ := by simp only [heapNext, hm₄, hm₃]
  have hroom := h.room
  have hbuf := h.buf
  simp only [NewBuf] at hbuf
  have hhiv := h.fr.heap.hi
  have nx₁ : heapNext v₁ = heapNext v := by simp only [heapNext, hm₁]
  -- the tail's elements are not `NEXT`
  have D : DFrame v v₄ (Within · nextAddr 8) := fun a ha ↦
    hm a fun he ↦ ha 0 (by decide) (by rw [add_ofNat_zero, he]; addr_omega [])
  have tailM : eListAt v₄ (v.getReg .x21) (v.getReg .x20).toNat =
      eListAt v (v.getReg .x21) (v.getReg .x20).toNat :=
    D.eListAt fun i hi hw ↦ by
      rcases hbuf.2 with h0 | h0
      · omega
      · addr_omega [hw, hi, h0, hroom, hhiv]
  -- the sum
  obtain ⟨w, hr₅, pc₅, kw, mw, s13, s12, s10⟩ : ∃ w, Reaches Image.code v₄ w ∧
      w.pc = 0x8000c428 ∧ (∀ r ∈ sumKept, w.getReg r = v₄.getReg r) ∧
      (∀ a, w.getMem a = v₄.getMem a) ∧
      w.getReg .x13 = (Model.limbs (sumE (eListAt v₄ (v.getReg .x21) (v.getReg .x20).toNat))).1 ∧
      w.getReg .x12 = (Model.limbs (sumE (eListAt v₄ (v.getReg .x21) (v.getReg .x20).toNat))).2.1 ∧
      w.getReg .x10 =
        (Model.limbs (sumE (eListAt v₄ (v.getReg .x21) (v.getReg .x20).toNat))).2.2 := by
    by_cases h0 : v.getReg .x20 = 0
    · have e0 : (v.getReg .x20).toNat = 0 := by rw [h0]; rfl
      have hz : Model.limbs (sumE (eListAt v₄ (v.getReg .x21) (v.getReg .x20).toNat)) =
          (0, 0, 0) := by
        rw [e0]; exact limbs_zero
      refine ⟨v₄, Reaches.refl _, b8000c3ac_pc_taken h₄ (by rw [kr3 .x20 (by simp)]; exact h0),
        fun _ _ ↦ rfl, fun _ ↦ rfl, ?_, ?_, ?_⟩
      · rw [hz, b8000c3ac_x13 h₄]
      · rw [hz, b8000c3ac_x12 h₄]
      · rw [hz, b8000c3ac_x10 h₄]
    · have hl : 0 < (v.getReg .x20).toNat := by
        rcases Nat.eq_zero_or_pos (v.getReg .x20).toNat with he | he
        · exact absurd (BitVec.eq_of_toNat_eq he) h0
        · exact he
      have h0' := hbuf.2.resolve_left (by omega)
      obtain ⟨v₅, hr₆, h₆⟩ := Sym.BlockSpec.reaches b8000c3d0_spec
        (b8000c3ac_pc_not_taken h₄ (by rw [kr3 .x20 (by simp)]; exact h0)) trivial
      have k₆ := b8000c3d0_keeps h₆
      have hm₆ := b8000c3d0_mem_same h₆
      have x14₆ : v₅.getReg .x14 = v.getReg .x21 + 16 := by
        rw [b8000c3d0_x14 h₆, kr .x21 (by simp)]
      have x15₆ : v₅.getReg .x15 = v.getReg .x21 + 16 +
          BitVec.ofNat 64 (24 * (v.getReg .x20).toNat) := by
        rw [b8000c3d0_x15' h₆ (by
            rw [kr .x21 (by simp), kr .x20 (by simp)]
            addr_omega [h0', hroom, hhiv]), kr .x21 (by simp), kr .x20 (by simp)]
      obtain ⟨w, hr₇, pc₇, A⟩ := sumLoop1 (b8000c3d0_pc h₆) hl hbuf.1 (by have := hpre.heap.lo; omega)
        (by addr_omega [h0', hroom, hhiv]) x14₆ x15₆
        (by rw [k₆ .x10 (by decide), b8000c3ac_x10 h₄])
        (by rw [k₆ .x12 (by decide), b8000c3ac_x12 h₄])
        (by rw [k₆ .x13 (by decide), b8000c3ac_x13 h₄])
      have el : eListAt v₅ (v.getReg .x21) (v.getReg .x20).toNat =
          eListAt v₄ (v.getReg .x21) (v.getReg .x20).toNat :=
        (DFrame.of_same hm₆ fun _ ↦ False).eListAt fun _ _ h ↦ h
      exact ⟨w, hr₆.trans hr₇, pc₇, fun r hr ↦ (A.kept r (mem_of_mem hr _)).trans (k₆ r (mem_of_mem hr _)),
        fun a ↦ (A.mem a).trans (hm₆ a), A.x13.trans (by rw [el]), A.x12.trans (by rw [el]),
        A.x10.trans (by rw [el])⟩
  have krw (r : Reg) (hr : r ∈ sumKept) : w.getReg r = v₄.getReg r := kw r hr
  have Fw : Fr s w := F₄.same hS (fun r hr ↦ kw r (mem_of_mem hr _)) mw
  have elw : eListAt w (w.getReg .x21) (w.getReg .x20).toNat =
      eListAt v (v.getReg .x21) (v.getReg .x20).toNat := by
    rw [krw .x21 (by decide), krw .x20 (by decide), kr .x21 (by simp), kr .x20 (by simp),
      (DFrame.of_same mw fun _ ↦ False).eListAt fun _ _ h ↦ h, tailM]
  have nxw : heapNext w = heapNext v₂ := by
    have : heapNext w = heapNext v₄ := by simp only [heapNext, mw]
    exact this.trans nx₄
  have x9w : w.getReg .x9 = v₂.getReg .x10 := (krw .x9 (by decide)).trans x9₄
  refine ⟨w, hr₂.trans (hr₃.trans (hr₄.trans hr₅)), Or.inl ⟨pc₅, {
    fr := Fw
    x18 := by rw [krw .x18 (by decide), b8000c3ac_x18 h₄, x18₃, c16]
    x23 := by rw [krw .x23 (by decide), b8000c3ac_x23 h₄, x18₃, c0]
    x24 := by rw [krw .x24 (by decide), b8000c3ac_x24 h₄, x18₃, c8]
    x11 := by rw [krw .x11 (by decide), b8000c3ac_x11 h₄, kr3 .x19 (by simp), h.x19]
    x13 := by rw [elw, s13, tailM]
    x12 := by rw [elw, s12, tailM]
    x10 := by rw [elw, s10, tailM]
    bAl := by rw [x9w]; exact hBa
    bNext := by rw [nxw, hBn, x9w]
    room := by rw [krw .x20 (by decide), krw .x22 (by decide), kr .x20 (by simp),
      kr .x22 (by simp)]; exact hroom
    buf := by
      rw [krw .x21 (by decide), krw .x22 (by decide), kr .x21 (by simp), kr .x22 (by simp), x9w]
      refine ⟨hbuf.1, ?_⟩
      rcases hbuf.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨h0.1, by omega⟩
    bLo := by rw [x9w]; omega
    value := fun T hT ↦ by
      obtain ⟨T', h1, h2⟩ := h.value T hT
      refine ⟨T', by rw [elw]; exact h1, Fr.transcriptAt hpre h.fr Fw.heap.hi
        ((D.trans (DFrame.of_same mw _) fun _ h ↦ h).mono fun a h ↦ Or.inr (Or.inl h)) h2⟩ }⟩⟩

end Rv64Verifier.Transcript.RoundPoly
