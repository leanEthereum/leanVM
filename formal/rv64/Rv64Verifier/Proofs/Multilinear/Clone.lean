import Rv64Verifier.Proofs.Multilinear.Contracts
import Rv64Verifier.Proofs.Runtime.Inv
import Rv64Verifier.Blocks.F31

/-!
# `<Vec<E> as Clone>::clone`

A slice to a new `Vec<E>` (`<[E]>::to_vec`), compiled at `0x8000897c` (`Blocks/F31.lean`):
`0x8000897c` saves `ra`, `s0`..`s2` in a 64-byte frame (`s0` = the length, `s1` = the result,
`s2` = the source) and calls `try_allocate_in(sp + 8, len, 0, 8, 24)`; `0x800089b8` traps on
`Err`; `0x800089c0` writes the capacity, the pointer and a zero length, and returns for an empty
slice; `0x800089d8` calls `memcpy(ptr, src, 24 len)`, `0x800089f0` sets the length;
`0x800089f4` restores and returns.
-/

namespace Rv64Verifier.Proofs.Multilinear.Clone
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.MultilinearContracts Rv64Verifier.Blocks.F31
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

def slots : List (Nat × Reg) := [(8, .x1), (16, .x8), (24, .x9), (32, .x18)]

def kept : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- What the function writes besides its saved registers: the result, and the stack below them. -/
@[rv_addr] def W (s : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x10) 24 ∨ Within a (stackLo s cloneStack) 80

abbrev Inv (s u : MachineState) (nx : Word) : Prop := FnInv s u 64 slots kept (W s) nx

theorem bounds {s : MachineState} (h : ClonePre s) :
    0x78000070 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 24 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := ValidMemRange.bounds h.out (by decide)
  simp only [cloneStack, tryAllocStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

theorem stack64 {s : MachineState} (h : ClonePre s) : RtStack s 64 := by
  have hb := bounds h
  have hst := h.stack
  have hn := hst.next
  have hro := hst.rodata
  refine ⟨⟨?_, hst.aligned⟩, by addr_omega [hb], by addr_omega [hb, hn], by addr_omega [hb, hro]⟩
  exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])

theorem Inv.step {s u v : MachineState} {nx nx' : Word} {X : Word → Prop}
    (hpre : ClonePre s) (h : Inv s u nx) (hX : ByteFrame u v X)
    (hXsub : ∀ a, X a → W s a ∨ Within a nextAddr 8 ∨ (heapNext s ≤ a.toNat ∧ a.toNat < nx'.toNat))
    (hnx : v.getMem nextAddr = nx') (hle : nx.toNat ≤ nx'.toNat) (hend : nx'.toNat ≤ heapEnd)
    (hr : ∀ r ∈ Reg.x2 :: kept, v.getReg r = u.getReg r) :
    Inv s v nx' := by
  have hb := bounds hpre
  have hs := hpre.outStack
  exact FnInv.step (m := 32) h (stack64 hpre) (by decide) (by decide) (by decide)
    (fun a ha ha' ↦ by simp only [W] at ha; addr_omega [ha, ha', hs, hb]) hX hXsub hnx hle hend
    (hr _ (by decide)) fun r hr' ↦ hr r (List.mem_cons_of_mem _ hr')

/-- A block that writes nothing. -/
theorem Inv.same {s u v : MachineState} {nx : Word} (hpre : ClonePre s) (h : Inv s u nx)
    (hm : ∀ a, v.getMem a = u.getMem a) {l : List Reg} (hk : ∀ r ∈ l, v.getReg r = u.getReg r)
    (hl : ∀ r ∈ Reg.x2 :: kept, r ∈ l := by decide) : Inv s v nx :=
  h.step hpre (ByteFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim) ((hm _).trans h.next)
    (Nat.le_refl _) h.fits fun r hr ↦ hk r (hl r hr)

theorem Inv.saved {s u : MachineState} {nx : Word} (h : Inv s u nx) :
    u.getReg .x2 = s.getReg .x2 - 64 ∧ u.getMem (s.getReg .x2 - 8) = s.getReg .x1 ∧
      u.getMem (s.getReg .x2 - 16) = s.getReg .x8 ∧ u.getMem (s.getReg .x2 - 24) = s.getReg .x9 ∧
      u.getMem (s.getReg .x2 - 32) = s.getReg .x18 := by
  have hsp := h.sp
  have sl := h.slots
  simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true] at sl
  rv_eval [] at hsp sl
  exact ⟨hsp, sl⟩

/-- The epilogue: restore and return. -/
theorem exit {s u : MachineState} {nx : Word} (hpre : ClonePre s) (hpc : u.pc = 0x800089f4)
    (h : Inv s u nx) :
    ∃ t, Reaches Image.code u t ∧ t.pc = returnAddress s ∧ Preserves s t ∧
      ∀ a, t.getMem a = u.getMem a := by
  have hb := bounds hpre
  obtain ⟨hsp, sl1, sl2, sl3, sl4⟩ := h.saved
  obtain ⟨t, hr, ht⟩ := Sym.BlockSpec.reaches b800089f4_spec hpc (by
    rv_eval [hsp]
    and_intros <;> valid_access hpre.stack.valid [hb])
  have k := b800089f4_keeps ht
  have pc := b800089f4_pc ht
  have x2 := b800089f4_x2 ht
  have x8 := b800089f4_x8 ht
  have x9 := b800089f4_x9 ht
  have x18 := b800089f4_x18 ht
  rv_eval [hsp, sl1, sl2, sl3, sl4] at pc x2 x8 x9 x18
  refine ⟨t, hr, pc.trans (returnAddress_eq s).symm,
    preserves_of x2 x8 x9 x18 ((k _ (by decide)).trans (h.kept _ (by decide))) fun r hr' ↦ ?_,
    b800089f4_mem_same ht⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (k _ (by decide)).trans (h.kept _ (by decide))

/-- **`clone` meets its contract**, given `try_allocate_in`'s and `memcpy`'s. -/
theorem clone_spec (hT : TryAllocZeroedSpec) (hC : MemcpySpec 0x800126e4) : CloneSpec := by
  intro s hpc hpre
  have hb := bounds hpre
  have hst := hpre.stack
  have hab := hst.above
  have hnx8 := hst.next
  have hro := hst.rodata
  have hheap := hpre.heap
  have hos := hpre.outStack
  have hof := hpre.outFree
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b8000897c_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hst.valid [hb])
  have k₁ := b8000897c_keeps h₁
  have inv₁ : Inv s t₁ (s.getMem nextAddr) := FnInv.init hheap (stack64 hpre)
    (by rw [b8000897c_x2 h₁]; rfl)
    (by
      simp only [slots, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
        and_true]
      rv_eval []
      exact ⟨b8000897c_m_x2_n8 h₁, b8000897c_m_x2_n16 h₁, b8000897c_m_x2_n24 h₁,
        b8000897c_m_x2_n32 h₁⟩)
    (fun r hr ↦ k₁ r (mem_of_mem hr _))
    ((b8000897c_frame h₁ (by addr_omega [hb])).mono fun a ha ↦ by addr_omega [ha, hb])
    (h₁.unaligned (by rv_eval []; and_intros <;> addr_omega [hb])) (by decide)
  have hsp₁ : t₁.getReg .x2 = s.getReg .x2 - 64 := b8000897c_x2 h₁
  have hx10₁ : t₁.getReg .x10 = s.getReg .x2 - 56 := b8000897c_x10 h₁
  have hn₁ : heapNext t₁ = heapNext s := by simp only [heapNext, inv₁.next]
  have hsl : stackLo t₁ tryAllocStack = stackLo s cloneStack := by
    simp only [stackLo, tryAllocStack, cloneStack, hsp₁]
    rw [Sym.sub_sub_lit]; rfl
  have hpre₁ : TryAllocPre .x13 .x14 t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hheap.hi⟩
    out := by rw [hx10₁]; valid_sub hst.valid [hb]
    align := by rw [b8000897c_x13 h₁]; decide
    size := by rw [b8000897c_x14 h₁]; decide
    stack := ⟨⟨by rw [hsl]; valid_sub hst.valid [hb], by rw [hsp₁]; addr_omega [hb]⟩,
      by rw [hsl]; exact hab, by rw [hsl]; addr_omega [hnx8, hb],
      by rw [hsl]; addr_omega [hro, hb]⟩
    outFree := by
      rw [hx10₁]
      simp only [Outside]
      exact ⟨Or.inr (by addr_omega [hab, hb]), by addr_omega [hnx8, hb]⟩
    outStack := by rw [hx10₁, hsl]; addr_omega [hb] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂, -⟩ | hdead⟩ := hT.call hr₁ (b8000897c_pc h₁) hpre₁
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  have hfr₂ := hpost₂.frame
  rw [hx10₁, hsl] at hfr₂
  have inv₂ : Inv s t₂ (t₂.getMem nextAddr) := inv₁.step hpre hfr₂ (fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inl (Or.inr (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl ha)
      · simp only [Fresh, hn₁] at ha
        exact Or.inr (Or.inr ha))
    rfl (by rw [← heapNext, ← heapNext, ← hn₁]; exact hpost₂.mono) hpost₂.heap.hi
    fun r hr ↦ hpres₂ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 64 := (hpres₂.reg .x2).trans hsp₁
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800089b8_spec
    (by rw [hpc₂, returnAddress_eq, b8000897c_x1 h₁]; decide) (by
      rv_eval [hsp₂]
      valid_access hst.valid [hb])
  have htag : t₂.getMem (s.getReg .x2 - 56) = 0 ∨ t₂.getMem (s.getReg .x2 - 56) ≠ 0 :=
    eq_or_ne _ _
  rcases htag with htag | htag
  swap
  · refine ⟨t₃, hr₂.trans hr₃, Or.inr (dead_of_fetch ?_)⟩
    rw [b800089b8_pc_taken h₃ (by rv_eval [hsp₂]; exact htag)]
    exact Option.isNone_iff_eq_none.mp (by decide +kernel)
  have k₃ := b800089b8_keeps h₃
  have inv₃ := inv₂.same hpre (b800089b8_mem_same h₃) k₃
  obtain ⟨hcap, hbuf⟩ := hpost₂.ok (by rw [hx10₁]; exact htag)
  rw [hx10₁, b8000897c_x11 h₁] at hcap hbuf
  rw [b8000897c_x14 h₁, b8000897c_x13 h₁] at hbuf
  rv_eval [] at hcap hbuf
  -- the `Vec`'s fields
  have hx9₃ : t₃.getReg .x9 = s.getReg .x10 := by
    rw [k₃ .x9 (by decide), hpres₂.reg .x9, b8000897c_x9 h₁]
  have hx8₃ : t₃.getReg .x8 = s.getReg .x12 := by
    rw [k₃ .x8 (by decide), hpres₂.reg .x8, b8000897c_x8 h₁]
  have hsp₃ : t₃.getReg .x2 = s.getReg .x2 - 64 := (k₃ .x2 (by decide)).trans hsp₂
  have hpc₃ : t₃.pc = 0x800089c0 := b800089b8_pc_not_taken h₃ (by rv_eval [hsp₂]; exact htag)
  have hm₃ := b800089b8_mem_same h₃
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800089c0_spec hpc₃ (by
    rv_eval [hsp₃, hx9₃]
    and_intros <;> first | valid_access hst.valid [hb] | valid_access hpre.out [hb])
  have k₄ := b800089c0_keeps h₄
  have hm₄ := b800089c0_frame h₄ (by rw [hx9₃]; addr_omega [hb])
  rw [hx9₃] at hm₄
  have c₀ := b800089c0_m_x9_0 h₄
  have c₁ := b800089c0_m_x9_8 h₄
  have c₂ := b800089c0_m_x9_16 h₄
  rv_eval [hsp₃, hx9₃, hm₃] at c₀ c₁ c₂
  rw [hcap] at c₀
  have hof' := hof
  simp only [Outside] at hof'
  have inv₄ := inv₃.step hpre (ByteFrame.of_memFrame hm₄ (by addr_omega [hb]) (by decide)
    (h₄.unaligned (by rv_eval [hx9₃]; and_intros <;> addr_omega [hb])))
    (fun a ha ↦ Or.inl (Or.inl ha)) ((hm₄ _ (by addr_omega [hof'.2, hb])).trans inv₃.next)
    (Nat.le_refl _) inv₃.fits fun r hr ↦ k₄ r (mem_of_mem hr _)
  -- the buffer
  obtain ⟨P, hP⟩ : ∃ P, P = t₂.getMem (s.getReg .x2 - 40) := ⟨_, rfl⟩
  rw [← hP] at hbuf c₁
  have hn₂ : heapNext t₂ = (t₂.getMem nextAddr).toNat := rfl
  have hfit₂ := hpost₂.heap.hi
  have hmono₂ := hpost₂.mono
  have hlo := hheap.lo
  -- the end: from `0x800089f4` with the length at `out + 16`
  have fin (u : MachineState) (hu : Reaches Image.code s u) (hpcu : u.pc = 0x800089f4)
      (hinv : Inv s u (t₂.getMem nextAddr))
      (hc : u.getMem (s.getReg .x10) = s.getReg .x12) (hp : u.getMem (s.getReg .x10 + 8) = P)
      (hl : u.getMem (s.getReg .x10 + 16) = s.getReg .x12)
      (hel : eListAt u P (s.getReg .x12).toNat = eListAt s (s.getReg .x11) (s.getReg .x12).toNat) :
      ∃ t, Reaches Image.code s t ∧
        ((t.pc = returnAddress s ∧ Preserves s t ∧ ClonePost s t) ∨ Dead Image.code t) := by
    obtain ⟨t, hr, hpct, hpres, hmt⟩ := exit hpre hpcu hinv
    have hnt : heapNext t = heapNext t₂ := by simp only [heapNext, hmt, hinv.next]
    have hbf := hinv.frame (ByteFrame.of_same hmt fun _ ↦ False) (fun _ h ↦ h.elim)
      ((hmt _).trans hinv.next)
    refine ⟨t, hu.trans hr, Or.inl ⟨hpct, hpres, {
      heap := ⟨by omega, by omega⟩
      mono := by omega
      vec := ⟨?_, ?_⟩
      len := by simp only [vecLen, hmt, hl]
      elems := by simp only [vecEs, vecPtr, vecLen, hmt, hp, hl]; rw [← hel]; simp only [eListAt, eAt, hmt]
      fresh := ?_
      frame := hbf.mono fun a ha ↦ ?_ }⟩⟩
    · simp only [RawVecOk, Buf, vecPtr, vecCap, hmt, hp, hc]
      simp only [NewBuf] at hbuf
      refine ⟨hbuf.1, ?_⟩
      rcases hbuf.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨by omega, by rw [hnt]; omega⟩
    · simp only [vecLen, vecCap, hmt, hl, hc, le_refl]
    · simp only [NewBuf, vecPtr, hmt, hp] at hbuf ⊢
      refine ⟨hbuf.1, ?_⟩
      rcases hbuf.2 with h0 | h0
      · exact Or.inl (by rw [Nat.mul_comm]; exact h0)
      · exact Or.inr ⟨by omega, by rw [hnt]; omega⟩
    · rcases ha with ha | ha | ha | ha
      · rcases ha with ha | ha
        · exact Or.inl ha
        · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
      · exact Or.inr (Or.inr (Or.inl ha))
      · exact Or.inr (Or.inr (Or.inr (by simp only [Fresh, hnt] at ha ⊢; exact ha)))
  have hx8₄ : t₄.getReg .x8 = s.getReg .x12 := (k₄ .x8 (by decide)).trans hx8₃
  by_cases h0 : s.getReg .x12 = 0
  · have hz : (s.getReg .x12).toNat = 0 := by rw [h0]; rfl
    exact fin t₄ (hr₂.trans (hr₃.trans hr₄)) (b800089c0_pc_taken h₄ (by rw [hx8₃]; exact h0))
      inv₄ c₀ c₁ (by rw [c₂, h0]) (by rw [hz]; rfl)
  -- copy
  have hS := hpre.src
  have hSf := hpre.srcFree
  have hSs := hpre.srcStack
  have hSo := hpre.srcOut
  simp only [Outside] at hSf
  have hlen : 0 < (s.getReg .x12).toNat := by
    rcases Nat.eq_zero_or_pos (s.getReg .x12).toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq h) h0
    · exact h
  have hbuf' := hbuf
  simp only [NewBuf, hn₁] at hbuf'
  have hPr : heapNext s ≤ P.toNat ∧ P.toNat + (s.getReg .x12).toNat * 24 ≤ heapNext t₂ := by
    rcases hbuf'.2 with h | h
    · omega
    · exact h
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b800089d8_spec
    (b800089c0_pc_not_taken h₄ (by rw [hx8₃]; exact h0)) trivial
  have k₅ := b800089d8_keeps h₅
  have inv₅ := inv₄.same hpre (b800089d8_mem_same h₅) k₅
  have hsp₅ : t₅.getReg .x2 = s.getReg .x2 - 64 := by
    rw [k₅ .x2 (by decide), k₄ .x2 (by decide), hsp₃]
  have hd₅ : t₅.getReg .x10 = P := by
    rw [k₅ .x10 (by decide), b800089c0_x10 h₄, hsp₃, hm₃]
    rv_eval [hP]
  have hs₅ : t₅.getReg .x11 = s.getReg .x11 := by
    rw [b800089d8_x11 h₅, k₄ .x18 (by decide), k₃ .x18 (by decide), hpres₂.reg .x18,
      b8000897c_x18 h₁]
  have hn₅ : (t₅.getReg .x12).toNat = 24 * (s.getReg .x12).toNat := by
    rw [b800089d8_x12 h₅, k₄ .x8 (by decide), hx8₃]
    simp only [Mapped] at hS
    addr_omega [hS]
  have hpre₅ : MemcpyPre t₅ := {
    dst := by rw [hd₅, hn₅]; addr_omega [hPr, hfit₂, hlo]
    src := by rw [hs₅, hn₅]; exact hS
    apart := by rw [hd₅, hs₅, hn₅]; addr_omega [hPr, hfit₂, hSf.1]
    stack := ⟨by
        refine ValidMemRange.sub hst.valid ?_ ?_ ?_ <;> simp only [stackLo] <;> rw [hsp₅] <;>
          addr_omega [hb],
      by rw [hsp₅]; addr_omega [hb]⟩
    dstStack := by rw [hd₅, hn₅]; simp only [stackLo]; rw [hsp₅]; addr_omega [hPr, hfit₂, hb, hab]
    srcStack := by rw [hs₅, hn₅]; simp only [stackLo]; rw [hsp₅]; addr_omega [hSs, hb] }
  obtain ⟨t₆, hr₆, ⟨hpc₆, hpres₆, hcpy⟩ | hdead⟩ := hC.call hr₅ (b800089d8_pc h₅) hpre₅
  swap
  · exact ⟨t₆, hr₂.trans (hr₃.trans (hr₄.trans hr₆)), Or.inr hdead⟩
  have hfr₆ := hcpy.frame
  rw [hd₅, hn₅] at hfr₆
  simp only [stackLo, hsp₅] at hfr₆
  have inv₆ := inv₅.step hpre hfr₆ (fun a ha ↦ by
      rcases ha with ha | ha
      · exact Or.inr (Or.inr (by simp only [Within] at ha; omega))
      · exact Or.inl (Or.inr (by addr_omega [ha, hb])))
    ((hfr₆.getMem fun i hi ha ↦ by
        rcases ha with ha | ha
        · addr_omega [ha, hi, hPr, hfit₂]
        · addr_omega [ha, hi, hb, hnx8]).trans inv₅.next)
    (Nat.le_refl _) inv₅.fits fun r hr ↦ hpres₆ r (by unfold calleeSaved; exact mem_of_mem hr _)
  have hby := hcpy.bytes
  rw [hd₅, hs₅, hn₅] at hby
  -- the length
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b800089f0_spec
    (by rw [hpc₆, returnAddress_eq, b800089d8_x1 h₅]; decide) (by
      rv_eval [hpres₆.reg .x9, k₅ .x9 (by decide), k₄ .x9 (by decide), hx9₃]
      valid_access hpre.out [hb])
  have hx9₆ : t₆.getReg .x9 = s.getReg .x10 := by
    rw [hpres₆.reg .x9, k₅ .x9 (by decide), k₄ .x9 (by decide), hx9₃]
  have hm₇ := b800089f0_frame h₇ (by rw [hx9₆]; addr_omega [hb])
  rw [hx9₆] at hm₇
  have l₇ := b800089f0_m_x9_16 h₇
  rw [hx9₆, hpres₆.reg .x8, k₅ .x8 (by decide), hx8₄] at l₇
  have inv₇ := inv₆.step hpre (ByteFrame.of_memFrame hm₇ (by addr_omega [hb]) (by decide)
    (h₇.unaligned (by rv_eval [hx9₆]; addr_omega [hb])))
    (fun a ha ↦ Or.inl (Or.inl (by addr_omega [ha, hb])))
    ((hm₇ _ (by addr_omega [hof'.2, hb])).trans inv₆.next) (Nat.le_refl _) inv₆.fits
    fun r hr ↦ b800089f0_keeps h₇ r (mem_of_mem hr _)
  have hfit₅ := inv₅.fits
  have keep (a : Word) (h₁ : ¬ Within a (s.getReg .x10 + 16) 8)
      (h₂ : ∀ i < 8, ¬ (Within (a + BitVec.ofNat 64 i) P (24 * (s.getReg .x12).toNat) ∨
        Within (a + BitVec.ofNat 64 i) (s.getReg .x2 - 64 - BitVec.ofNat 64 memcpyStack)
          memcpyStack)) : t₇.getMem a = t₄.getMem a := by
    rw [hm₇ a h₁, hfr₆.getMem h₂, b800089d8_mem_same h₅]
  refine fin t₇ (hr₂.trans (hr₃.trans (hr₄.trans (hr₆.trans hr₇)))) (b800089f0_pc h₇) inv₇
    ?_ ?_ l₇ ?_
  · rw [keep _ (by addr_omega [hb]) fun i hi hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hw, hi, hof'.1, hPr, hfit₂, hb]
      · addr_omega [hw, hi, hos, hb]]
    exact c₀
  · rw [keep _ (by addr_omega [hb]) fun i hi hw ↦ by
      rcases hw with hw | hw
      · addr_omega [hw, hi, hof'.1, hPr, hfit₂, hb]
      · addr_omega [hw, hi, hos, hb]]
    exact c₁
  · have hPa : P.toNat % 8 = 0 := hbuf'.1
    refine eListAt_eq_of_bytesAt ?_ hPa hpre.srcAlign
    rw [(ByteFrame.of_memFrame hm₇ (by addr_omega [hb]) (by decide)
      (h₇.unaligned (by rv_eval [hx9₆]; addr_omega [hb]))).bytesAt fun i hi hw ↦ by
        addr_omega [hw, hi, hof'.1, hPr, hfit₂, hb], hby]
    refine inv₅.mem.bytesAt fun i hi hw ↦ ?_
    simp only [W] at hw
    rcases hw with (hw | hw) | hw | hw | hw
    · addr_omega [hw, hi, hSo, hS]
    · addr_omega [hw, hi, hSs, hb, hS]
    · addr_omega [hw, hi, hSs, hb, hS]
    · addr_omega [hw, hi, hSf.2, hS]
    · addr_omega [hw, hi, hSf.1, hfit₅, hS]

end Rv64Verifier.Proofs.Multilinear.Clone
