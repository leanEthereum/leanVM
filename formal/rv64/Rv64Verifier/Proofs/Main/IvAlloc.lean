import Rv64Verifier.Proofs.Main.IvEntry
import Rv64Verifier.Proofs.Runtime.All

/-!
# The IV's preimage buffer

`0x80000318` saves the input slice past the table (`msp + 88`, `msp + 96`) and calls
`try_allocate_in` for `Vec::<u8>::with_capacity(8 n + 9)` (`TryAllocZeroedSpec`); `0x80000350`
traps on its error; `0x80000358` moves the `Vec` into place at `msp + 104` and calls `reserve`,
which returns at once with room enough (`ReserveFastSpec`) (`iv_alloc`, to `IvB` at
`0x8000037c`).
-/

namespace Rv64Verifier.Proofs.Main
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Proofs.End
  Rv64Verifier.Blocks.F3

/-- At `0x8000037c`: an empty `Vec<u8>` at `msp + 104` with room for `8 n + 9` bytes. -/
structure IvB (s : MachineState) (words : List Word) (u : MachineState) : Prop where
  inv : MInv s words u
  pc : u.pc = 0x8000037c
  len : (words.getD 0 0).toNat + 1 ≤ words.length
  x19 : u.getReg .x19 = words.getD 0 0
  x8 : u.getReg .x8 = BitVec.ofNat 64 (8 * (words.getD 0 0).toNat)
  x9 : u.getReg .x9 = BitVec.ofNat 64 (8 * (words.getD 0 0).toNat + 9)
  ptr : u.getMem (msp + 88) = inputBase + BitVec.ofNat 64 (8 * ((words.getD 0 0).toNat + 1))
  rest : (u.getMem (msp + 96)).toNat = words.length - ((words.getD 0 0).toNat + 1)
  vlen : u.getMem (msp + 120) = 0
  buf : heapStart ≤ (u.getMem (msp + 112)).toNat ∧
    (u.getMem (msp + 112)).toNat + (8 * (words.getD 0 0).toNat + 9) ≤ heapNext u

theorem mul8 (w : Word) : w * 8 = BitVec.ofNat 64 (8 * w.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl]
  omega

theorem ptr_word (w : Word) :
    w * 8 + 0x10000000 + 8 = inputBase + BitVec.ofNat 64 (8 * (w.toNat + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    inputBase_eq]
  have h8 : (8 : Word).toNat = 8 := rfl
  have h1 : (0x10000000 : Word).toNat = 0x10000000 := rfl
  rw [h8, h1]
  omega

theorem rest_word {len : Nat} {w : Word} (h1 : w.toNat + 1 ≤ len) (h2 : len ≤ 2 ^ 25) :
    (BitVec.ofNat 64 (len - 1) - w).toNat = len - (w.toNat + 1) := by
  rw [AddrOmega.sub_le _ _ (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
  omega

/-- `try_allocate_in`'s call from `0x80000318`. -/
theorem iv_try_alloc {s u : MachineState} {words : List Word} (h : IvA s words u) :
    ∃ v, Reaches Image.code u v ∧
      ((∃ t, b80000318.Holds u t ∧ v.pc = 0x80000350 ∧ Preserves t v ∧
        TryAllocPost .x13 .x14 t v) ∨ Dead Image.code v) := by
  have hsp := h.inv.sp
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80000318_spec h.pc
    (by rv_eval [hsp, msp]; decide)
  have hsp₁ : t₁.getReg .x2 = msp := by rw [b80000318_keeps h₁ .x2 (by decide), hsp]
  have hfr := b80000318_frame h₁ (by rw [hsp]; decide)
  have hheap : HeapOk t₁ := by
    have e : t₁.getMem nextAddr = u.getMem nextAddr := hfr _ (by rw [hsp]; addr_omega [])
    exact ⟨by simp only [heapNext, e]; exact h.inv.heap.lo,
      by simp only [heapNext, e]; exact h.inv.heap.hi⟩
  have e10 : t₁.getReg .x10 = msp + 104 := by rw [b80000318_x10 h₁, hsp]
  obtain ⟨v, hv, hout⟩ := tryAllocZeroed t₁ (b80000318_pc h₁) {
    heap := hheap
    out := by rw [e10]; exact validRange_of (by decide) (by decide) (by decide)
    align := by rw [b80000318_x13 h₁]; decide
    size := by rw [b80000318_x14 h₁]; decide
    stack := rtStack_msp hsp₁ (by decide) (by decide)
    outFree := by rw [e10]; addr_omega []
    outStack := by rw [e10]; simp only [stackLo, hsp₁]; addr_omega [] }
  refine ⟨v, hr₁.trans hv, ?_⟩
  rcases hout with ⟨hpc, hpres, hpost, -⟩ | hd
  · exact Or.inl ⟨t₁, h₁, by rw [hpc, returnAddress, b80000318_x1 h₁]; decide, hpres, hpost⟩
  · exact Or.inr hd

/-- **The buffer, to `IvB`.** -/
theorem iv_alloc {s u : MachineState} {words : List Word} (h : IvA s words u) :
    ∃ v, Reaches Image.code u v ∧ (IvB s words v ∨ Dead Image.code v) := by
  have hsp := h.inv.sp
  have hfit := h.inv.fits
  simp only [inputWords] at hfit
  have hlen := h.len
  set n := (words.getD 0 0).toNat with hn
  obtain ⟨v, hv, ⟨t₁, h₁, hpc₂, hpres, hpost⟩ | hd⟩ := iv_try_alloc h
  swap
  · exact ⟨v, hv, Or.inr hd⟩
  have hsp₁ : t₁.getReg .x2 = msp := by rw [b80000318_keeps h₁ .x2 (by decide), hsp]
  have hsp₂ : v.getReg .x2 = msp := (hpres.reg .x2).trans hsp₁
  have e10 : t₁.getReg .x10 = msp + 104 := by rw [b80000318_x10 h₁, hsp]
  have e11 : t₁.getReg .x11 = BitVec.ofNat 64 (8 * n + 9) := by
    rw [b80000318_x11 h₁, h.x19, mul8 _]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : (9 : Word).toNat = 9 := rfl
    omega
  have hfr₁ := b80000318_frame h₁ (by rw [hsp]; decide)
  have hheap₁ := hpost.heap
  have hlo₁ : heapStart ≤ heapNext t₁ := by
    have e : t₁.getMem nextAddr = u.getMem nextAddr := hfr₁ _ (by rw [hsp]; addr_omega [])
    simp only [heapNext, e]; exact h.inv.heap.lo
  -- `MInv` after the call
  have hun₁ := h₁.unaligned (by rv_eval [hsp, msp])
  have hinv₁ : MInv s words t₁ := h.inv.frame
    (ByteFrame.of_memFrame hfr₁ (by rw [hsp]; decide) (by decide) hun₁) hsp₁
    ⟨by
      have e : t₁.getMem nextAddr = u.getMem nextAddr := hfr₁ _ (by rw [hsp]; addr_omega [])
      simp only [heapNext, e]; exact h.inv.heap.lo, by
      have e : t₁.getMem nextAddr = u.getMem nextAddr := hfr₁ _ (by rw [hsp]; addr_omega [])
      simp only [heapNext, e]; exact h.inv.heap.hi⟩
    fun a ha hk ↦ by rw [hsp] at ha; simp only [Kept, inputBase_eq] at hk
                     rcases hk with hk | hk | hk <;> addr_omega [ha, hk, hfit]
  have hinv₂ : MInv s words v := hinv₁.frame hpost.frame hsp₂ hheap₁ fun a ha ↦ by
    rcases ha with ha | ha | ha | ha
    · rw [e10] at ha
      intro hk; simp only [Kept, inputBase_eq] at hk
      rcases hk with hk | hk | hk <;> addr_omega [ha, hk, hfit]
    · exact not_kept_stack (by simpa only [inputWords] using hfit) hsp₁ (by decide) ha
    · exact not_kept_next (by simpa only [inputWords] using hfit) ha
    · exact not_kept_heap (by simpa only [inputWords] using hfit)
        ⟨le_trans hlo₁ ha.1, lt_of_lt_of_le ha.2 hheap₁.hi⟩
  -- the slice, kept by the call
  have keep₂ : ∀ k : Nat, k + 8 ≤ 104 → v.getMem (msp + BitVec.ofNat 64 k) =
      t₁.getMem (msp + BitVec.ofNat 64 k) := by
    intro k hk
    refine hpost.frame.getMem fun i hi hw ↦ ?_
    rcases hw with hw | hw | hw | hw
    · rw [e10] at hw; addr_omega [hw, hk, hi]
    · simp only [stackLo, hsp₁] at hw; addr_omega [hw, hk, hi]
    · addr_omega [hw, hk, hi]
    · have := hheap₁.hi; addr_omega [hw, hk, hi, this]
  -- the tag
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80000350_spec hpc₂ (by rv_eval [hsp₂, msp]; decide)
  by_cases htag : v.getMem (v.getReg .x2 + 104) ≠ 0
  · obtain ⟨w, hw, hd⟩ := abort (u := t₃) (by rw [b80000350_pc_taken h₃ htag]; decide)
    exact ⟨w, hv.trans (hr₃.trans hw), Or.inr hd⟩
  rw [not_not] at htag
  have hpc₃ := b80000350_pc_not_taken h₃ htag
  rw [hsp₂, ← e10] at htag
  obtain ⟨hcap, hbuf⟩ := hpost.ok htag
  have hm₃ := b80000350_mem_same h₃
  have k₃ := b80000350_keeps h₃
  have hsp₃ : t₃.getReg .x2 = msp := by rw [k₃ .x2 (by decide), hsp₂]
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b80000358_spec hpc₃ (by rv_eval [hsp₃, msp]; decide)
  have k₄ := b80000358_keeps h₄
  have hsp₄ : t₄.getReg .x2 = msp := by rw [k₄ .x2 (by decide), hsp₃]
  have hfr₄ := b80000358_frame h₄ (by rw [hsp₃]; decide)
  have hun₄ := h₄.unaligned (by rv_eval [hsp₃, msp])
  have e9 : words.getD 0 0 * 8 + 9 = BitVec.ofNat 64 (8 * n + 9) := by
    rw [mul8]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have : (9 : Word).toNat = 9 := rfl
    omega
  have x9₄ : t₄.getReg .x9 = BitVec.ofNat 64 (8 * n + 9) := by
    rw [k₄ .x9 (by decide), k₃ .x9 (by decide), hpres.reg .x9, b80000318_x9 h₁, h.x19, e9]
  have hcap₄ : t₄.getMem (msp + 104) = BitVec.ofNat 64 (8 * n + 9) := by
    have := b80000358_m_x2_104 h₄
    rw [hsp₃] at this
    rw [this, hm₃, show (msp + 112 : Word) = t₁.getReg .x10 + 8 by rw [e10]; rfl, hcap, e11]
  have hlen₄ : t₄.getMem (msp + 120) = 0 := by
    have := b80000358_m_x2_120 h₄; rwa [hsp₃] at this
  have hptr₄ : t₄.getMem (msp + 112) = v.getMem (t₁.getReg .x10 + 16) := by
    have := b80000358_m_x2_112 h₄
    rw [hsp₃] at this
    rw [this, hm₃, e10]; rfl
  obtain ⟨t₅, hr₅, hout₅⟩ := reserveFast_8000c898 t₄ (b80000358_pc h₄)
    ⟨by rw [b80000358_x10 h₄, hsp₃]; exact validRange_of (by decide) (by decide) (by decide), by
      rw [b80000358_x10 h₄, hsp₃, b80000358_x11 h₄, k₃ .x9 (by decide), hpres.reg .x9,
        b80000318_x9 h₁, h.x19, e9]
      simp only [vecLen, vecCap]
      rw [show (msp + 104 + 16 : Word) = msp + 120 from rfl, hlen₄, hcap₄]
      simp⟩
  rcases hout₅ with ⟨hpc₅, hpres₅, -, hm₅⟩ | hd
  swap
  · exact ⟨t₅, hv.trans (hr₃.trans (hr₄.trans hr₅)), Or.inr hd⟩
  have hsp₅ : t₅.getReg .x2 = msp := (hpres₅.reg .x2).trans hsp₄
  have hnx₄ : t₄.getMem nextAddr = v.getMem nextAddr := by
    rw [hfr₄ _ (by rw [hsp₃]; addr_omega []), hm₃]
  have hinv₅ : MInv s words t₅ := by
    have hinv₃ := hinv₂.same hm₃ hsp₃
    have hinv₄ := hinv₃.frame (ByteFrame.of_memFrame hfr₄ (by rw [hsp₃]; decide) (by decide) hun₄)
      hsp₄ ⟨by simp only [heapNext, hnx₄]; exact hheap₁.lo,
        by simp only [heapNext, hnx₄]; exact hheap₁.hi⟩
      fun a ha hk ↦ by
        rw [hsp₃] at ha; simp only [Kept, inputBase_eq] at hk
        rcases hk with hk | hk | hk <;> addr_omega [ha, hk, hfit]
    exact hinv₄.same hm₅ hsp₅
  have keep : ∀ k : Nat, k + 8 ≤ 104 → t₅.getMem (msp + BitVec.ofNat 64 k) =
      t₁.getMem (msp + BitVec.ofNat 64 k) := by
    intro k hk
    rw [hm₅, hfr₄ _ (by rw [hsp₃]; addr_omega [hk]), hm₃, keep₂ k hk]
  have m88 := b80000318_m_x2_88 h₁
  have m96 := b80000318_m_x2_96 h₁
  rw [hsp] at m88 m96
  refine ⟨t₅, hv.trans (hr₃.trans (hr₄.trans hr₅)), Or.inl ⟨hinv₅, ?_, hlen, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩⟩
  · rw [hpc₅, returnAddress, b80000358_x1 h₄]; decide
  · rw [hpres₅.reg .x19, k₄ .x19 (by decide), k₃ .x19 (by decide), hpres.reg .x19,
      b80000318_keeps h₁ .x19 (by decide), h.x19]
  · rw [hpres₅.reg .x8, k₄ .x8 (by decide), k₃ .x8 (by decide), hpres.reg .x8, b80000318_x8 h₁,
      h.x19, mul8]
  · rw [hpres₅.reg .x9, x9₄]
  · have k88 : t₅.getMem (msp + 88) = t₁.getMem (msp + 88) := keep 88 (by decide)
    rw [k88, m88, h.x19, h.x11]
    exact ptr_word _
  · have k96 : t₅.getMem (msp + 96) = t₁.getMem (msp + 96) := keep 96 (by decide)
    rw [k96, m96, h.x19, h.x10]
    exact rest_word hlen hfit
  · rw [hm₅]; exact hlen₄
  · rw [hm₅, hptr₄]
    have hsz : (t₁.getReg .x11).toNat * (t₁.getReg .x14).toNat = 8 * n + 9 := by
      rw [e11, b80000318_x14 h₁]; simp; omega
    rw [hsz] at hbuf
    obtain ⟨-, hb | hb⟩ := hbuf
    · omega
    · have hnx₅ : heapNext t₅ = heapNext v := by simp only [heapNext, hm₅, hnx₄]
      rw [hnx₅]
      exact ⟨le_trans hlo₁ hb.1, hb.2⟩

end Rv64Verifier.Proofs.Main
