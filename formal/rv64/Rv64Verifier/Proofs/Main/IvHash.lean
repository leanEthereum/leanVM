import Rv64Verifier.Proofs.Main.IvTag
import Rv64Verifier.Proofs.Hash.All
import Rv64Verifier.Proofs.Transcript.Keccak

/-!
# The table's bytes, then the IV

`0x800003d4` copies the table's `8 n` bytes from the input after `TAG` (`memcpy`; skipped for an
empty table), `0x800003ec` sets the length `8 n + 9` (`iv_copy`, to `IvC`); `0x800003f4` hashes
the buffer into `msp + 320` (`keccak_hash`) (`iv_hash`, to `AfterIv`). `iv_stage` is `IvStage`.
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.End
  Rv64Verifier.Blocks.F3

/-- `MInv` across a step that changes only the doublewords at addresses in `W`. -/
theorem MInv.frameD {s u v : MachineState} {words : List Word} {W : Word → Prop}
    (h : MInv s words u) (hW : ∀ a, ¬ W a → v.getMem a = u.getMem a) (hsp : v.getReg .x2 = msp)
    (hheap : HeapOk v) (hk : ∀ a, W a → ¬ Kept words a) : MInv s words v where
  fits := h.fits
  sp := hsp
  slots := by
    intro p hp
    rw [← h.slots p hp]
    have hb : 472 ≤ p.1 ∧ p.1 + 8 ≤ 576 := by
      revert hp; simp only [mainSlots, List.mem_cons, List.not_mem_nil, or_false]
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
        decide
    obtain ⟨h1, h2⟩ := hb
    exact hW _ fun hw ↦ hk _ hw (Or.inl (by addr_omega [h1, h2]))
  input := by
    intro i hi
    rw [← h.input i hi]
    have hf := h.fits
    have hib : inputBase.toNat = 0x10000000 := rfl
    exact hW _ fun hw ↦ hk _ hw (Or.inr (Or.inl (by addr_omega [hi, hf, hib])))
  heap := hheap
  rodata := by
    intro p hp
    have hw' := within_of_mem_rodataWords hp
    rw [hW _ fun hw ↦ hk _ hw (Or.inr (Or.inr hw'))]
    exact h.rodata p hp

/-- The table's bytes, from the input. -/
theorem input_bytes {s u : MachineState} {words : List Word} (h : MInv s words u)
    (hn : (words.getD 0 0).toNat + 1 ≤ words.length) :
    bytesAt u 0x10000008 (8 * (words.getD 0 0).toNat) = (tbl words).flatMap Model.toLeBytes := by
  have hf := h.fits
  simp only [inputWords] at hf
  rw [bytesAt_dwords u (by decide) _ (by have : (0x10000008 : Word).toNat = 0x10000008 := rfl; omega)]
  congr 1
  apply List.ext_getElem (by
    simp only [tbl, List.length_map, List.length_range, List.length_take, List.length_drop]; omega)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_range]
  simp only [tbl, List.getElem_take, List.getElem_drop]
  have e : (0x10000008 : Word) + BitVec.ofNat 64 (8 * i) = inputBase + BitVec.ofNat 64 (8 * (1 + i)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, inputBase_eq]
    have : (0x10000008 : Word).toNat = 0x10000008 := rfl
    have : (0x10000000 : Word).toNat = 0x10000000 := rfl
    omega
  rw [e, h.input (1 + i) (by omega)]

/-- At `0x800003f4`: the buffer at `s1` holds `TAG` and the table's bytes, `a2` their number. -/
structure IvC (s : MachineState) (words : List Word) (u : MachineState) : Prop where
  inv : MInv s words u
  pc : u.pc = 0x800003f4
  len : (words.getD 0 0).toNat + 1 ≤ words.length
  x19 : u.getReg .x19 = words.getD 0 0
  ptr : u.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * ((words.getD 0 0).toNat + 1))
  rest : (u.getMem (msp + 96)).toNat = words.length - ((words.getD 0 0).toNat + 1)
  buf : heapStart ≤ (u.getReg .x9).toNat ∧
    (u.getReg .x9).toNat + (8 * (words.getD 0 0).toNat + 9) ≤ heapNext u
  x12 : u.getReg .x12 = BitVec.ofNat 64 (8 * (words.getD 0 0).toNat + 9)
  bytes : bytesAt u (u.getReg .x9) (9 + 8 * (words.getD 0 0).toNat) =
    Model.tagRust ++ (tbl words).flatMap Model.toLeBytes

/-- **The table's bytes, to `IvC`.** -/
theorem iv_copy {s u : MachineState} {words : List Word} (h : IvT s words u) :
    ∃ v, Reaches Image.code u v ∧ (IvC s words v ∨ Dead Image.code v) := by
  have hsp := h.inv.sp
  have hfit := h.inv.fits
  simp only [inputWords] at hfit
  have hlen := h.len
  have hbuf := h.buf
  have hhi := h.inv.heap.hi
  simp only [heapStart, heapEnd] at hbuf hhi
  by_cases hz : words.getD 0 0 = 0
  · have hpc := h.pc
    simp only [hz, ↓reduceIte] at hpc
    have hn : (words.getD 0 0).toNat = 0 := by rw [hz]; rfl
    refine ⟨u, Reaches.refl u, Or.inl ⟨h.inv, hpc, hlen, h.x19, h.ptr, h.rest, h.buf, ?_, ?_⟩⟩
    · rw [h.x12, hn]; rfl
    · have ht : tbl words = [] := by simp only [tbl, hn, List.take_zero]
      rw [hn, ht]
      exact h.tag.trans (List.append_nil _).symm
  have hpc := h.pc
  simp only [hz, ↓reduceIte] at hpc
  set n := (words.getD 0 0).toNat with hn
  set p := u.getReg .x9 with hp
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800003d4_spec hpc trivial
  have k₁ := b800003d4_keeps h₁
  have m₁ := b800003d4_mem_same h₁
  have hsp₁ : t₁.getReg .x2 = msp := by rw [k₁ .x2 (by decide), hsp]
  have e10 : t₁.getReg .x10 = p + 9 := by rw [b800003d4_x10 h₁, h.x12]
  have e11 : t₁.getReg .x11 = 0x10000008 := b800003d4_x11 h₁
  have e12 : t₁.getReg .x12 = BitVec.ofNat 64 (8 * n) := by rw [b800003d4_x12 h₁, h.x8]
  have t12 : (t₁.getReg .x12).toNat = 8 * n := by
    rw [e12, BitVec.toNat_ofNat]; omega
  have tp9 : (p + 9).toNat = p.toNat + 9 := by
    rw [BitVec.toNat_add]; have : (9 : Word).toNat = 9 := rfl; omega
  obtain ⟨t₂, hr₂, hout⟩ := Runtime.memcpy t₁ (b800003d4_pc h₁) {
    dst := by rw [e10, t12]; simp only [Runtime.Mapped, tp9]; omega
    src := by rw [e11, t12]; simp only [Runtime.Mapped]; have : (0x10000008 : Word).toNat = 0x10000008 := rfl; omega
    apart := by
      rw [e10, e11, t12]; simp only [Apart, tp9]
      have : (0x10000008 : Word).toNat = 0x10000008 := rfl; omega
    stack := stackOk_msp hsp₁ (by decide) (by decide)
    dstStack := by rw [e10, t12]; simp only [stackLo, hsp₁]; addr_omega [tp9, hbuf, hhi]
    srcStack := by rw [e11, t12]; simp only [stackLo, hsp₁]; addr_omega [hfit, hlen] }
  rcases hout with ⟨hpc₂, hpres₂, hpost₂⟩ | hd
  swap
  · exact ⟨t₂, hr₁.trans hr₂, Or.inr hd⟩
  have hsp₂ : t₂.getReg .x2 = msp := (hpres₂.reg .x2).trans hsp₁
  have hpc₂' : t₂.pc = 0x800003ec := by rw [hpc₂, returnAddress, b800003d4_x1 h₁]; decide
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800003ec_spec hpc₂' trivial
  have k₃ := b800003ec_keeps h₃
  have m₃ := b800003ec_mem_same h₃
  have hsp₃ : t₃.getReg .x2 = msp := by rw [k₃ .x2 (by decide), hsp₂]
  have hW : ∀ a, (Within a (t₁.getReg .x10) (t₁.getReg .x12).toNat ∨
      Within a (stackLo t₁ memcpyStack) memcpyStack) →
      (heapStart ≤ a.toNat ∧ a.toNat < heapNext u) ∨ Within a (stackLo t₁ 16) 16 := by
    intro a ha
    rcases ha with ha | ha
    · rw [e10, t12] at ha
      left; simp only [heapStart]; constructor <;> addr_omega [ha, tp9, hbuf]
    · right; exact ha
  have hW' : ∀ a, (Within a (t₁.getReg .x10) (t₁.getReg .x12).toNat ∨
      Within a (stackLo t₁ memcpyStack) memcpyStack) → ¬ Kept words a := by
    intro a ha
    rcases hW a ha with ha | ha
    · exact not_kept_heap h.inv.fits ⟨ha.1, lt_of_lt_of_le ha.2 h.inv.heap.hi⟩
    · exact not_kept_stack h.inv.fits hsp₁ (by decide) ha
  have keep : ∀ a : Word, (∀ i < 8, ¬ ((heapStart ≤ (a + BitVec.ofNat 64 i).toNat ∧
      (a + BitVec.ofNat 64 i).toNat < heapNext u) ∨ Within (a + BitVec.ofNat 64 i) (stackLo t₁ 16) 16)) →
      t₃.getMem a = u.getMem a := by
    intro a ha
    rw [m₃, hpost₂.frame.getMem fun i hi hw ↦ ha i hi (hW _ hw), m₁]
  have hnx : t₃.getMem nextAddr = u.getMem nextAddr :=
    keep _ fun i hi hw ↦ by
      simp only [stackLo, hsp₁, heapStart] at hw; rcases hw with hw | hw <;> addr_omega [hw, hi, hhi]
  have hheap : HeapOk t₃ := ⟨by simp only [heapNext, hnx]; exact h.inv.heap.lo,
    by simp only [heapNext, hnx]; exact h.inv.heap.hi⟩
  have hinv : MInv s words t₃ := by
    have h₂ := (h.inv.same m₁ hsp₁).frame hpost₂.frame hsp₂
      ⟨by simp only [heapNext]; rw [← m₃, hnx]; exact h.inv.heap.lo,
        by simp only [heapNext]; rw [← m₃, hnx]; exact h.inv.heap.hi⟩ hW'
    exact h₂.same m₃ hsp₃
  have e9 : t₃.getReg .x9 = p := by rw [k₃ .x9 (by decide), hpres₂.reg .x9, k₁ .x9 (by decide)]
  refine ⟨t₃, hr₁.trans (hr₂.trans hr₃), Or.inl ⟨hinv, b800003ec_pc h₃, hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [k₃ .x19 (by decide), hpres₂.reg .x19, k₁ .x19 (by decide), h.x19]
  · rw [keep _ fun i hi hw ↦ by
      simp only [stackLo, hsp₁, heapStart] at hw; rcases hw with hw | hw <;> addr_omega [hw, hi, hhi]]
    exact h.ptr
  · rw [keep _ fun i hi hw ↦ by
      simp only [stackLo, hsp₁, heapStart] at hw; rcases hw with hw | hw <;> addr_omega [hw, hi, hhi]]
    exact h.rest
  · rw [e9, heapNext, hnx]; exact h.buf
  · rw [b800003ec_x12 h₃, hpres₂.reg .x18, hpres₂.reg .x8, k₁ .x18 (by decide), k₁ .x8 (by decide),
      h.x18, h.x8]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : (9 : Word).toNat = 9 := rfl
    have : (0 : Word).toNat = 0 := rfl
    omega
  · have b1 : bytesAt t₂ p 9 = Model.tagRust := by
      rw [hpost₂.frame.bytesAt fun i hi hw ↦ by
        rcases hw with hw | hw
        · rw [e10, t12] at hw; addr_omega [hw, hi, tp9, hbuf]
        · simp only [stackLo, hsp₁] at hw; addr_omega [hw, hi, hbuf, hhi], bytesAt_same m₁]
      exact h.tag
    have b2 : bytesAt t₂ (p + 9) (8 * n) = (tbl words).flatMap Model.toLeBytes := by
      have := hpost₂.bytes
      rw [e10, t12, e11] at this
      rw [this, bytesAt_same m₁]
      exact input_bytes h.inv hlen
    rw [e9, bytesAt_same m₃, bytesAt_add, b1]
    exact congrArg _ b2

end Rv64Verifier.Proofs.Main
