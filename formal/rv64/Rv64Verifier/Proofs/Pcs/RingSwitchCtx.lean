import Rv64Verifier.Proofs.Pcs.RingSwitchSetup

/-!
# `ring_switch`: from `samples` to the coefficient loop

`alloc(8, 1536)` for the coefficients' buffer `C`, `reserve(64)` on its `Vec` (at once), the
challenges' count read back, the loop's registers (`setup2`). At the loop's head `Ctx` holds what
the loops read and never write.
-/

namespace Rv64Verifier.Proofs.Pcs.RingSwitch
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.FieldContracts
  Rv64Verifier.Model.Pcs Rv64Verifier.Blocks.F36
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- `TranscriptOk` across a frame that misses `p`'s first word and the `Proof`. -/
theorem transcriptOk_frame {s t : MachineState} {W : Word → Prop} (hf : DFrame s t W) {p : Word}
    (hok : TranscriptOk s p) (hp : ∀ i < 8, ¬ W (p + BitVec.ofNat 64 i))
    (hq : ∀ i < 48, ¬ W (proofAt s p + BitVec.ofNat 64 i)) :
    TranscriptOk t p ∧ proofAt t p = proofAt s p ∧ streamPtr t p = streamPtr s p ∧
      streamLen t p = streamLen s p := by
  obtain ⟨h1, h2, h3⟩ := hf.stream hp hq
  refine ⟨⟨hok.self, by rw [h1]; exact hok.proof, by rw [h2, h3]; exact hok.stream, ?_⟩, h1, h2, h3⟩
  simp only [ProofApart, h1, h2, h3]; exact hok.apart

/-- What the loops read and never write, at the coefficient loop's first head `B1`: the
challenges `ch` at `chP`, the coefficients' buffer `C`, the frame's words. -/
structure Ctx (s B1 : MachineState) (C chP : Word) (ch : List E) : Prop where
  sp : B1.getReg .x2 = s.getReg .x2 - 464
  heap : HeapOk B1
  mono : heapNext s ≤ heapNext B1
  frame : DFrame s B1 fun a ↦ W0 s a ∨ Fresh s B1 a
  slots : ∀ p ∈ slots, B1.getMem (s.getReg .x2 - BitVec.ofNat 64 p.1) = s.getReg p.2
  out : B1.getMem (s.getReg .x2 - 456) = s.getReg .x10
  sP : B1.getMem (s.getReg .x2 - 448) = s.getReg .x12
  sLen : B1.getMem (s.getReg .x2 - 432) = s.getReg .x13
  chPm : B1.getMem (s.getReg .x2 - 424) = chP
  six : B1.getMem (s.getReg .x2 - 416) = 6
  cap : B1.getMem (s.getReg .x2 - 336) = 64
  cbuf : B1.getMem (s.getReg .x2 - 328) = C
  chLen : ch.length = 6
  chs : eListAt B1 chP 6 = ch
  chA : chP.toNat % 8 = 0
  chLo : heapNext s ≤ chP.toNat
  chC : chP.toNat + 144 ≤ C.toNat
  cA : C.toNat % 8 = 0
  cHi : C.toNat + 1536 = heapNext B1
  tok : TranscriptOk B1 (s.getReg .x14)
  value : ∀ T, TranscriptAt s (s.getReg .x14) T → ∃ T',
    (Model.TM.samples 6).run T = some (ch, T') ∧ TranscriptAt B1 (s.getReg .x14) T'

/-- Registers fixed through the coefficient loop. -/
structure CRegs (s u : MachineState) (C : Word) : Prop where
  x9 : u.getReg .x9 = C
  x18 : u.getReg .x18 = 1
  x19 : u.getReg .x19 = 32
  x20 : u.getReg .x20 = s.getReg .x2 - 192
  x23 : u.getReg .x23 = s.getReg .x11
  x24 : u.getReg .x24 = 64
  x27 : u.getReg .x27 = 6

/-- What the coefficient loop writes besides the stack below `sp`: its scratch `F + 152 ..
F + 360` and the buffer `C`. -/
def w1 (s : MachineState) (C : Word) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 312) 208 ∨ Within a C 1536

/-- At `0x8000986c`, before coefficient `k`. -/
structure CHead (s B1 u : MachineState) (C : Word) (ch : List E) (nx : Word) (k : Nat) : Prop
    extends CRegs s u C where
  ph : Ph B1 u (w1 s C) nx
  pc : u.pc = 0x8000986c
  lt : k < 64
  x22 : u.getReg .x22 = BitVec.ofNat 64 k
  x26 : u.getReg .x26 = BitVec.ofNat 64 k
  buf : ∀ l < k, eAt u (C + BitVec.ofNat 64 (24 * l)) = cacc ch l 6

theorem setup2 (hA : AllocSpec) {s B : MachineState} (hpre : RingSwitchPre s) (hB : AtB s B) :
    ∃ u, Reaches Image.code B u ∧ (Dead Image.code u ∨ ∃ C, Ctx s u C (vecPtr B (s.getReg .x2 - 408))
      (vecEs B (s.getReg .x2 - 408)) ∧ CHead s u u C (vecEs B (s.getReg .x2 - 408))
        (u.getMem nextAddr) 0) := by
  have hb := bounds hpre
  have hst := hpre.stack
  have hspB := hB.sp
  have hB0 := hB.heap
  -- `alloc(8, 1536)`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800097b4_spec hB.pc trivial
  have k₁ := b800097b4_keeps h₁
  have hm₁ := b800097b4_mem_same h₁
  have hn₁ : heapNext t₁ = heapNext B := by simp only [heapNext, hm₁]
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ := hA.call hr₁ (b800097b4_pc h₁)
    ⟨⟨hn₁ ▸ hB0.lo, hn₁ ▸ hB0.hi⟩, by rw [b800097b4_x10 h₁]; decide⟩
  swap
  · exact ⟨t₂, hr₂, Or.inl hdead⟩
  have hC₁ := hpost₂.above
  have hC₂ := hpost₂.next
  have hC₃ := hpost₂.aligned
  rw [b800097b4_x10 h₁] at hC₃
  rw [hn₁] at hC₁
  rw [b800097b4_x11 h₁] at hC₂
  have hC₃' : (t₂.getReg .x10).toNat % 8 = 0 := by simpa using hC₃
  have hlo := hB0.lo
  simp only [heapStart] at hlo
  -- `C ≠ 0`
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800097c4_spec
    (by rw [hpc₂, returnAddress_eq, b800097b4_x1 h₁]; decide) trivial
  have hC0 : t₂.getReg .x10 ≠ 0 := by
    intro h0; rw [h0] at hC₁; simp at hC₁; omega
  have k₃ := b800097c4_keeps h₃
  have hm₃ := b800097c4_mem_same h₃
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 464 := by
    rw [k₃ .x2 (by decide), hpres₂.reg .x2, k₁ .x2 (by decide), hspB]
  -- the `Vec` at `F + 128`, `reserve(64)`
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800097c8_spec (b800097c4_pc_not_taken h₃ hC0) (by
    rv_eval [hsp₃]
    and_intros <;> valid_access hst.valid [hb])
  have k₄ := b800097c8_keeps h₄
  have hm₄ := b800097c8_frame h₄ (by rw [hsp₃]; addr_omega [hb])
  rw [hsp₃] at hm₄
  rv_eval [] at hm₄
  have hsp₄ : t₄.getReg .x2 = s.getReg .x2 - 464 := by rw [k₄ .x2 (by decide), hsp₃]
  have hx10₄ : t₄.getReg .x10 = s.getReg .x2 - 336 := by rw [b800097c8_x10 h₄, hsp₃]; rv_eval []
  have e144 := b800097c8_m_x2_144 h₄
  have e136 := b800097c8_m_x2_136 h₄
  have e128 := b800097c8_m_x2_128 h₄
  have e32 := b800097c8_m_x2_32 h₄
  have e8 := b800097c8_m_x2_8 h₄
  rw [hsp₃] at e144 e136 e128 e32 e8
  rv_eval [] at e144 e136 e128 e32 e8
  obtain ⟨t₅, hr₅, hpc₅, hpres₅, -, hm₅⟩ := MultilinearWords.reserve_fast (b800097c8_pc h₄)
    (by rw [hx10₄]; valid_sub hst.valid [hb])
    (by rw [hx10₄, b800097c8_x11 h₄]; rv_eval [e144, e128]; decide)
  -- the challenges' count, `min(len, 6) = 6`
  have hsp₅ : t₅.getReg .x2 = s.getReg .x2 - 464 := (hpres₅.reg .x2).trans hsp₄
  have hx8₅ : t₅.getReg .x8 = 6 := by
    rw [hpres₅.reg .x8, k₄ .x8 (by decide), k₃ .x8 (by decide), hpres₂.reg .x8,
      k₁ .x8 (by decide), hB.x8]
  -- memory at `t₅` outside `NEXT` and `F + 8 .. F + 152` is `B`'s
  have keep₅ (a : Word) (h1 : a ≠ s.getReg .x2 - 320) (h2 : a ≠ s.getReg .x2 - 328)
      (h3 : a ≠ s.getReg .x2 - 336) (h4 : a ≠ s.getReg .x2 - 432) (h5 : a ≠ s.getReg .x2 - 456)
      (h6 : a ≠ nextAddr) : t₅.getMem a = B.getMem a := by
    rw [hm₅, h₄.frame a (by rv_eval [hsp₃]; exact ⟨h1, h2, h3, h4, h5⟩), hm₃, hpost₂.mem a h6, hm₁]
  have hlen₅ : t₅.getMem (s.getReg .x2 - 392) = 6 := by
    rw [keep₅ _ (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
      (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])]
    have := hB.len; simp only [vecLen] at this; rv_eval [] at this; exact this
  have hpc₅' : t₅.pc = 0x800097f4 := by rw [hpc₅, returnAddress_eq, b800097c8_x1 h₄]; decide
  obtain ⟨t₆, hr₆, h₆⟩ := Sym.BlockSpec.reaches b800097f4_spec hpc₅' (by
    rv_eval [hsp₅]
    and_intros <;> valid_access hst.valid [hb])
  have hm₆ := b800097f4_frame h₆ (by rw [hsp₅]; addr_omega [hb])
  rw [hsp₅] at hm₆
  rv_eval [] at hm₆
  have k₆ := b800097f4_keeps h₆
  have hpc₆ := b800097f4_pc_not_taken h₆ (by rw [hsp₅, hx8₅]; rv_eval [hlen₅]; decide)
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80009804_spec hpc₆ trivial
  have k₇ := b80009804_keeps h₇
  have hm₇ := b80009804_mem_same h₇
  have hsp₇ : t₇.getReg .x2 = s.getReg .x2 - 464 := by
    rw [k₇ .x2 (by decide), k₆ .x2 (by decide), hsp₅]
  obtain ⟨u, hr₈, h₈⟩ := Sym.BlockSpec.reaches b80009808_spec (b80009804_pc h₇) (by
    rv_eval [hsp₇]
    and_intros <;> valid_access hst.valid [hb])
  have hm₈ := b80009808_frame h₈ (by rw [hsp₇]; addr_omega [hb])
  rw [hsp₇] at hm₈
  rv_eval [] at hm₈
  have k₈ := b80009808_keeps h₈
  have hspu : u.getReg .x2 = s.getReg .x2 - 464 := by rw [k₈ .x2 (by decide), hsp₇]
  -- `u`'s memory from `t₅`'s
  have keep₈ (a : Word) (h1 : ¬ Within a (s.getReg .x2 - 424) 16) : u.getMem a = t₅.getMem a := by
    rw [hm₈ a (by addr_omega [h1, hb]), hm₇, hm₆ a (by addr_omega [h1, hb])]
  have hnu : u.getMem nextAddr = t₂.getMem nextAddr := by
    rw [keep₈ _ (by addr_omega [hb]), hm₅, hm₄ _ (by addr_omega [hb]), hm₃]
  have hheapu : heapNext u = (t₂.getReg .x10).toNat + 1536 := by
    simp only [heapNext, hnu]; exact hC₂
  have hn₂u : heapNext u = heapNext t₂ := by simp only [heapNext, hnu]
  have hHu : HeapOk u := ⟨hn₂u ▸ hpost₂.heap.lo, hn₂u ▸ hpost₂.heap.hi⟩
  -- the frame from `B`
  have hfB : DFrame B u fun a ↦ Within a (s.getReg .x2 - 464) 464 ∨ Within a nextAddr 8 := by
    intro a ha
    have h0 := ha 0 (by decide)
    rw [add_ofNat_zero] at h0
    rw [keep₈ a (fun h ↦ h0 (Or.inl (by addr_omega [h, hb]))),
      keep₅ a (fun h ↦ h0 (Or.inl (by rw [h]; addr_omega [hb])))
        (fun h ↦ h0 (Or.inl (by rw [h]; addr_omega [hb])))
        (fun h ↦ h0 (Or.inl (by rw [h]; addr_omega [hb])))
        (fun h ↦ h0 (Or.inl (by rw [h]; addr_omega [hb])))
        (fun h ↦ h0 (Or.inl (by rw [h]; addr_omega [hb])))
        (fun h ↦ h0 (Or.inr (by rw [h]; addr_omega [])))]
  have hBu : heapNext B ≤ heapNext u := by rw [hheapu]; omega
  -- registers
  have hx2₇ : t₇.getReg .x2 = s.getReg .x2 - 464 := hsp₇
  have r7 (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26])
      : t₇.getReg r = t₅.getReg r := by
    rw [k₇ r (mem_of_mem hr _), k₆ r (mem_of_mem hr _)]
  have r4 (r : Reg) (hr : r ∈ [Reg.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27])
      : t₄.getReg r = B.getReg r := by
    rw [k₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _), hpres₂.reg r (mem_of_mem hr _),
      k₁ r (mem_of_mem hr _)]
  -- the words written
  have hkHi (a : Word) (h1 : (s.getReg .x2).toNat - 312 ≤ a.toNat) (h2 : a.toNat < (s.getReg .x2).toNat) :
      u.getMem a = B.getMem a := by
    rw [keep₈ a (by addr_omega [h1, h2, hb]), keep₅ a (by addr_omega [h1, h2, hb])
      (by addr_omega [h1, h2, hb]) (by addr_omega [h1, h2, hb]) (by addr_omega [h1, h2, hb])
      (by addr_omega [h1, h2, hb]) (by addr_omega [h1, h2, hb])]
  have hw5 (a : Word) (ha : ¬ Within a (s.getReg .x2 - 424) 16) : u.getMem a = t₄.getMem a := by
    rw [keep₈ a ha, hm₅]
  -- the challenges
  have hvl := hB.vec.len
  have hbuf := hB.buf
  have hlen := hB.len
  simp only [NewBuf] at hbuf
  rw [hlen] at hvl
  have h6 : (6 : Word).toNat = 6 := rfl
  rw [h6] at hvl
  have hchB : heapNext s ≤ (vecPtr B (s.getReg .x2 - 408)).toNat ∧
      (vecPtr B (s.getReg .x2 - 408)).toNat + 144 ≤ heapNext B := by omega
  have hok := hpre.self.ok
  have hTi := hpre.self
  have hP := Region.bounds hok.self
  have hQ := Region.bounds hok.proof
  simp only [transcriptSize] at hP
  have hTS := hTi.stack
  have hPS := hTi.proofStack
  have hfree := hTi.free
  have hpfree := hTi.proofFree
  have hsfree := hTi.streamFree
  simp only [Outside] at hfree hpfree hsfree
  have hmB := hB.mono
  obtain ⟨hokB, hprB, hspB', hslB⟩ := transcriptOk_frame hB.frame hok
    (fun i hi hX ↦ by
      rcases hX with (hX | hX | hX) | hX
      · addr_omega [hX, hi, hP]
      · addr_omega [hX, hi, hP, hTS, hb]
      · addr_omega [hX, hi, hP, hfree.2]
      · simp only [Fresh] at hX; addr_omega [hX, hi, hP, hfree.1, hmB, hB0.hi])
    (fun i hi hX ↦ by
      rcases hX with (hX | hX | hX) | hX
      · addr_omega [hX, hi, hQ, hok.apart.1]
      · addr_omega [hX, hi, hQ, hPS.1, hb]
      · addr_omega [hX, hi, hQ, hpfree.2]
      · simp only [Fresh] at hX; addr_omega [hX, hi, hQ, hpfree.1, hmB, hB0.hi])
  have hmissU (x : Word) (hx : x.toNat < (s.getReg .x2).toNat - 1584 ∨ (s.getReg .x2).toNat ≤ x.toNat)
      (hn : ¬ Within x nextAddr 8) : ¬ (Within x (s.getReg .x2 - 464) 464 ∨ Within x nextAddr 8) := by
    rintro (h | h)
    · addr_omega [h, hx, hb]
    · exact hn h
  have hQB := hQ
  rw [← hprB] at hQB
  refine ⟨u, hr₂.trans (hr₃.trans (hr₄.trans (hr₅.trans (hr₆.trans (hr₇.trans hr₈))))),
    Or.inr ⟨t₂.getReg .x10, {
      sp := hspu
      heap := hHu
      mono := Nat.le_trans hmB hBu
      frame := ?_
      slots := fun p hp ↦ by
        have hb8 : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 ≤ 104 := by decide
        obtain ⟨h8, h104⟩ := hb8 p hp
        rw [hkHi _ (by addr_omega [h8, h104, hb]) (by addr_omega [h8, h104, hb])]
        exact hB.slots p hp
      out := by
        rw [hw5 _ (by addr_omega [hb]), e8, ← k₄ .x19 (by decide), r4 .x19 (by decide), hB.x19]
      sP := by
        rw [keep₈ _ (by addr_omega [hb]), keep₅ _ (by addr_omega [hb]) (by addr_omega [hb])
          (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])]
        exact hB.sP
      sLen := by rw [hw5 _ (by addr_omega [hb]), e32, ← k₄ .x9 (by decide), r4 .x9 (by decide), hB.x9]
      chPm := by
        have := b80009808_m_x2_40 h₈
        rw [hx2₇] at this; rv_eval [] at this
        rw [this, hm₇, hm₆ _ (by addr_omega [hb]), keep₅ _ (by addr_omega [hb]) (by addr_omega [hb])
          (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])]
        simp only [vecPtr]; rv_eval []
      six := by
        have := b800097f4_m_x2_48 h₆
        rw [hsp₅] at this; rv_eval [] at this
        rw [hm₈ _ (by addr_omega [hb]), hm₇, this, hlen₅]
      cap := by rw [hw5 _ (by addr_omega [hb]), e128]
      cbuf := by rw [hw5 _ (by addr_omega [hb]), e136, k₃ .x10 (by decide)]
      chLen := by rw [vecEs, eListAt_length, hlen]; rfl
      chs := by
        rw [vecEs, hlen, h6]
        exact hfB.eList (fun x hx ↦ hmissU x (by addr_omega [hx, hchB, hBu, hHu.hi, hb])
          (by addr_omega [hx, hchB, hBu, hHu.hi])) (Or.inr (by addr_omega [hchB, hBu, hHu.hi]))
      chA := hbuf.1
      chLo := hchB.1
      chC := by omega
      cA := hC₃'
      cHi := hheapu.symm
      tok := ?_
      value := ?_ }, {
      x9 := by
        rw [b80009808_x9 h₈, hx2₇]; rv_eval []
        rw [hm₇, hm₆ _ (by addr_omega [hb]), hm₅, e136, k₃ .x10 (by decide)]
      x18 := b80009808_x18 h₈
      x19 := b80009808_x19 h₈
      x20 := by rw [b80009808_x20 h₈, hx2₇]; rv_eval []
      x23 := by rw [k₈ .x23 (by decide), r7 .x23 (by decide), hpres₅.reg .x23, r4 .x23 (by decide), hB.x23]
      x24 := by rw [k₈ .x24 (by decide), r7 .x24 (by decide), hpres₅.reg .x24, b800097c8_x24 h₄]
      x27 := by rw [k₈ .x27 (by decide), b80009804_x27 h₇]
      ph := Ph.refl hHu _
      pc := b80009808_pc h₈
      lt := by decide
      x22 := by
        rw [b80009808_x22 h₈, hx2₇]; rv_eval []
        rw [hm₇, hm₆ _ (by addr_omega [hb]), hm₅, e144]
      x26 := b80009808_x26 h₈
      buf := fun l hl ↦ absurd hl (Nat.not_lt_zero l) }⟩⟩
  · refine (hB.frame.mono fun a ha ↦ ?_).trans hfB fun a ha ↦ ?_
    · rcases ha with ha | ha
      · exact Or.inl ha
      · simp only [Fresh] at ha ⊢; exact Or.inr ⟨ha.1, by omega⟩
    · rcases ha with ha | ha
      · exact Or.inl (Or.inr (Or.inl (by addr_omega [ha, hb])))
      · exact Or.inl (Or.inr (Or.inr ha))
  · refine (transcriptOk_frame hfB hokB (fun i hi ↦ hmissU _ (by addr_omega [hi, hP, hTS, hb])
      (by addr_omega [hi, hP, hfree.2])) (fun i hi ↦ hmissU _ (by addr_omega [hi, hQB, hPS.1, hprB, hb])
      (by rw [hprB]; addr_omega [hi, hQ, hpfree.2]))).1
  · intro T hT
    obtain ⟨T', hrun, hT'⟩ := hB.value T hT
    refine ⟨T', hrun, transcriptAt_frame hfB hT' hokB
      (fun x hx ↦ hmissU x (by addr_omega [hx, hP, hTS, hb]) (by addr_omega [hx, hP, hfree.2]))
      (fun x hx ↦ hmissU x (by rw [hprB] at hx; addr_omega [hx, hQ, hPS.1, hb])
        (by rw [hprB] at hx; addr_omega [hx, hQ, hpfree.2]))
      (fun x hx ↦ hmissU x (by rw [hspB', hslB] at hx; addr_omega [hx, hPS.2, hb])
        (by rw [hspB', hslB] at hx; addr_omega [hx, hsfree.2]))⟩

end Rv64Verifier.Proofs.Pcs.RingSwitch
