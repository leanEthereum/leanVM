import Rv64Verifier.Proofs.Main.Common

/-!
# `main`'s prologue and the table's length

`0x800002cc` saves the caller's registers in the 576-byte frame and aborts on an empty input;
`0x80000308` reads the table's length `n`, the first word, and aborts unless `n` words follow
(`iv_entry`, to `IvA` at `0x80000318`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.End
  Rv64Verifier.Blocks.F3

/-- At `0x80000318`: `s3` is the first word, the table's length, and that many words follow; `a0`
is the number of words after the first. -/
structure IvA (s : MachineState) (words : List Word) (u : MachineState) : Prop where
  inv : MInv s words u
  pc : u.pc = 0x80000318
  len : (words.getD 0 0).toNat + 1 ≤ words.length
  x19 : u.getReg .x19 = words.getD 0 0
  x10 : u.getReg .x10 = BitVec.ofNat 64 (words.length - 1)
  x11 : u.getReg .x11 = 0x10000000

theorem MInv.same {s u v : MachineState} {words : List Word} (h : MInv s words u)
    (hm : ∀ a, v.getMem a = u.getMem a) (hsp : v.getReg .x2 = msp) : MInv s words v :=
  h.frame (W := fun _ ↦ False) (ByteFrame.of_same hm _) hsp
    ⟨by simp only [heapNext, hm]; exact h.heap.lo, by simp only [heapNext, hm]; exact h.heap.hi⟩
    fun _ h ↦ h.elim

theorem next_init : ((0xa0000f30 : Word), (0x20000000 : Word)) ∈ Image.dataWords := by
  decide +kernel

/-- After the prologue: `MInv`. -/
theorem prologue_inv {s t : MachineState} {words : List Word} (hpre : MainPre words s)
    (hfit : words.length ≤ inputWords) (h : b800002cc.Holds s t) : MInv s words t := by
  have hsp := hpre.1
  have hst : stackTop.toNat = 0xbffffff0 := rfl
  have hfr : MemFrame s t (s.getReg .x2 - 104) 104 :=
    b800002cc_frame h (by rw [hsp]; decide)
  have hun := h.unaligned (by rv_eval [hsp, stackTop])
  have hbf : ByteFrame s t (Within · (s.getReg .x2 - 104) 104) :=
    ByteFrame.of_memFrame hfr (by rw [hsp]; decide) (by decide) hun
  have hnx : s.getMem nextAddr = 0x20000000 := hpre.2.2.2.1 _ next_init
  have hnx' : t.getMem nextAddr = 0x20000000 := by
    rw [hfr nextAddr (by rw [hsp]; addr_omega [hst])]; exact hnx
  have hheap : HeapOk t := ⟨by simp only [heapNext, hnx']; decide,
    by simp only [heapNext, hnx']; decide⟩
  have hib : inputBase.toNat = 0x10000000 := rfl
  refine ⟨hfit, ?_, ?_, ?_, hheap, ?_⟩
  · rw [b800002cc_x2 h, hsp]; decide
  · intro p hp
    simp only [mainSlots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show msp + BitVec.ofNat 64 472 = s.getReg .x2 - 104 by rw [hsp]; decide]
      exact b800002cc_m_x2_n104 h
    · rw [show msp + BitVec.ofNat 64 480 = s.getReg .x2 - 96 by rw [hsp]; decide]
      exact b800002cc_m_x2_n96 h
    · rw [show msp + BitVec.ofNat 64 488 = s.getReg .x2 - 88 by rw [hsp]; decide]
      exact b800002cc_m_x2_n88 h
    · rw [show msp + BitVec.ofNat 64 496 = s.getReg .x2 - 80 by rw [hsp]; decide]
      exact b800002cc_m_x2_n80 h
    · rw [show msp + BitVec.ofNat 64 504 = s.getReg .x2 - 72 by rw [hsp]; decide]
      exact b800002cc_m_x2_n72 h
    · rw [show msp + BitVec.ofNat 64 512 = s.getReg .x2 - 64 by rw [hsp]; decide]
      exact b800002cc_m_x2_n64 h
    · rw [show msp + BitVec.ofNat 64 520 = s.getReg .x2 - 56 by rw [hsp]; decide]
      exact b800002cc_m_x2_n56 h
    · rw [show msp + BitVec.ofNat 64 528 = s.getReg .x2 - 48 by rw [hsp]; decide]
      exact b800002cc_m_x2_n48 h
    · rw [show msp + BitVec.ofNat 64 536 = s.getReg .x2 - 40 by rw [hsp]; decide]
      exact b800002cc_m_x2_n40 h
    · rw [show msp + BitVec.ofNat 64 544 = s.getReg .x2 - 32 by rw [hsp]; decide]
      exact b800002cc_m_x2_n32 h
    · rw [show msp + BitVec.ofNat 64 552 = s.getReg .x2 - 24 by rw [hsp]; decide]
      exact b800002cc_m_x2_n24 h
    · rw [show msp + BitVec.ofNat 64 560 = s.getReg .x2 - 16 by rw [hsp]; decide]
      exact b800002cc_m_x2_n16 h
    · rw [show msp + BitVec.ofNat 64 568 = s.getReg .x2 - 8 by rw [hsp]; decide]
      exact b800002cc_m_x2_n8 h
  · intro i hi
    rw [← hpre.2.2.2.2 i hi]
    refine hbf.getMem fun j hj hw ↦ ?_
    rw [hsp] at hw
    simp only [inputWords] at hfit
    addr_omega [hw, hi, hj, hfit, hib, hst]
  · intro p hp
    have hw' := within_of_mem_rodataWords hp
    have h8 : p.1.toNat % 8 = 0 := by
      simpa using List.all_eq_true.mp rodataWords_aligned' p hp
    rw [hbf.getMem fun i hi hw ↦ by rw [hsp] at hw; addr_omega [hw, hw', h8, hi, hst]]
    exact hpre.rodataOk p hp

/-- **The prologue and the length check.** -/
theorem iv_entry {s : MachineState} {words : List Word} (hpc : s.pc = mainEntry)
    (hpre : MainPre words s) (hfit : words.length ≤ inputWords) :
    ∃ v, Reaches Image.code s v ∧ (IvA s words v ∨ Dead Image.code v) := by
  have hsp := hpre.1
  have h10 := hpre.2.2.1
  obtain ⟨t₀, hr₀, h₀⟩ := Sym.BlockSpec.reaches b800002cc_spec hpc
    (by rv_eval [hsp, stackTop]; decide)
  have hinv := prologue_inv hpre hfit h₀
  have e10 : t₀.getReg .x10 = BitVec.ofNat 64 words.length := by
    rw [b800002cc_keeps h₀ .x10 (by decide), h10]
  simp only [inputWords] at hfit
  by_cases hz : words.length = 0
  · obtain ⟨v, hv, hd⟩ := abort (u := t₀) (by
      rw [b800002cc_pc_taken h₀ (by rw [h10, hz]; rfl)]; decide)
    exact ⟨v, hr₀.trans hv, Or.inr hd⟩
  have hpc₀ : t₀.pc = 0x80000308 := b800002cc_pc_not_taken h₀ (by
    rw [h10]; intro he
    have := congrArg BitVec.toNat he
    simp at this
    omega)
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80000308_spec hpc₀ trivial
  have hw0 : t₀.getMem 0x10000000 = words.getD 0 0 := by
    have := hinv.input 0 (by omega)
    simp only [Nat.mul_zero] at this
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact this
  have hsub : (t₀.getReg .x10 - 1).toNat = words.length - 1 := by
    rw [e10, AddrOmega.sub_le _ _ (by simp; omega)]
    simp
    omega
  by_cases hlt : (t₀.getReg .x10 - 1).toNat < (t₀.getMem (0x10000000)).toNat
  · obtain ⟨v, hv, hd⟩ := abort (u := t₁) (by rw [b80000308_pc_taken h₁ hlt]; decide)
    exact ⟨v, hr₀.trans (hr₁.trans hv), Or.inr hd⟩
  rw [hsub, hw0] at hlt
  refine ⟨t₁, hr₀.trans hr₁, Or.inl ⟨hinv.same (b80000308_mem_same h₁) ?_,
    b80000308_pc_not_taken h₁ (by rw [hsub, hw0]; omega), by omega, ?_, ?_, ?_⟩⟩
  · rw [b80000308_keeps h₁ .x2 (by decide)]; exact hinv.sp
  · rw [b80000308_x19 h₁, hw0]
  · rw [b80000308_x10 h₁, e10]
    apply BitVec.eq_of_toNat_eq
    rw [AddrOmega.sub_le _ _ (by simp; omega)]
    simp
    omega
  · exact b80000308_x11 h₁

end Rv64Verifier.Proofs.Main
