import Rv64Verifier.Proofs.Layout.Contracts
import Rv64Verifier.Blocks.F14

/-!
# `Form::term`, at `0x800050a8`

```rust
fn term(monomial: Monomial, coefficient: E) -> Self {
    Self { terms: vec![(monomial, coefficient)] }
}
```

compiled (`Blocks/F14.lean`): `0x800050a8` saves `ra`, `s0`..`s2` in an 80-byte frame and calls
`alloc(8, 48)`; `0x800050d8` traps on a null pointer (never: `alloc` halts instead); `0x800050dc`
copies the monomial and the coefficient into the buffer, writes the `Vec` (capacity 1, the buffer,
length 1) to `a0`, restores and returns.
-/

namespace Rv64Verifier.Layout.Term
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.Blocks.F14
  Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- **`Form::term` meets its contract**, given `alloc`'s. -/
theorem term_spec (hA : AllocSpec) : TermSpec := by
  intro s hpc hpre
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hob := ValidMemRange.bounds hpre.out (by decide)
  have hmb := ValidMemRange.bounds hpre.mono (by decide)
  have hcb := ValidMemRange.bounds hpre.coeff (by decide)
  have hof := hpre.outFree
  have hos := hpre.outStack
  have hms := hpre.monoStack
  have hcs := hpre.coeffStack
  have hmn := hpre.monoNext
  have hcn := hpre.coeffNext
  have hheap := hpre.heap
  simp only [termStack] at hsb hab hnx hos hms hcs
  -- the prologue, and the call
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800050a8_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hsb])
  have k₁ := b800050a8_keeps h₁
  have hf₁ : ByteFrame s t₁ (Within · (stackLo s 80) 80) :=
    h₁.byteFrame (by
      rv_eval []
      and_intros <;> first | (intro i hi; addr_omega [hsb, hi]) | addr_omega [hsb])
  have hn₁ : t₁.getMem nextAddr = s.getMem nextAddr :=
    hf₁.getMem_of (fun x hx h ↦ by addr_omega [hx, h, hnx, hsb]) (by decide)
  have hheap₁ : HeapOk t₁ := ⟨by simp only [heapNext, hn₁]; exact hheap.lo,
    by simp only [heapNext, hn₁]; exact hheap.hi⟩
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost⟩ | hdead⟩ :=
    hA.call hr₁ (b800050a8_pc h₁) ⟨hheap₁, by rw [b800050a8_x10 h₁]; decide⟩
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  obtain ⟨p, hp⟩ : ∃ p, p = t₂.getReg .x10 := ⟨_, rfl⟩
  have hpal : p.toNat % 8 = 0 := by rw [hp]; simpa [b800050a8_x10 h₁] using hpost.aligned
  have hpabove : heapNext t₁ ≤ p.toNat := hp ▸ hpost.above
  have hpnext : heapNext t₂ = p.toNat + 48 := by
    rw [hpost.next, ← hp, b800050a8_x11 h₁]; rfl
  have hhi₂ := hpost.heap.hi
  have hlo₁ := hheap₁.lo
  have hof' : (s.getReg .x10).toNat + 24 ≤ p.toNat ∨ 0x78000000 ≤ (s.getReg .x10).toNat := by
    have := hof.1
    simp only [heapNext, heapEnd, hn₁] at this hpabove
    omega
  simp only [heapNext, heapStart, heapEnd] at hpabove hpnext hhi₂ hlo₁
  have hp0 : t₂.getReg .x10 ≠ 0 := by
    rw [← hp]; intro h0; rw [h0] at hpabove; simp at hpabove; omega
  -- the null check, and the writes
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800050d8_spec
    (by rw [hpc₂, returnAddress_eq, b800050a8_x1 h₁]; decide) trivial
  have k₃ := b800050d8_keeps h₃
  have hx2 : t₃.getReg .x2 = s.getReg .x2 - 80 := by
    rw [k₃ .x2 (by decide), hpres₂.reg .x2, b800050a8_x2 h₁]
  have hx8 : t₃.getReg .x8 = s.getReg .x10 := by
    rw [k₃ .x8 (by decide), hpres₂.reg .x8, b800050a8_x8 h₁]
  have hx9 : t₃.getReg .x9 = s.getReg .x12 := by
    rw [k₃ .x9 (by decide), hpres₂.reg .x9, b800050a8_x9 h₁]
  have hx18 : t₃.getReg .x18 = s.getReg .x11 := by
    rw [k₃ .x18 (by decide), hpres₂.reg .x18, b800050a8_x18 h₁]
  have hx10 : t₃.getReg .x10 = p := by rw [k₃ .x10 (by decide), hp]
  have hbuf : ValidMemRange p 6 := validMemRange_of hpal (Or.inl ⟨by omega, by omega⟩)
  obtain ⟨t₄, hr₄, h₄⟩ := Sym.BlockSpec.reaches b800050dc_spec
    (b800050d8_pc_not_taken h₃ hp0) (by
      rv_eval [hx2, hx8, hx9, hx18, hx10]
      and_intros <;> first
        | valid_access hpre.stack.valid [hsb]
        | valid_access hpre.out [hob]
        | valid_access hpre.mono [hmb]
        | valid_access hpre.coeff [hcb]
        | valid_access hbuf [hpal, hpnext, hhi₂]
        | addr_omega [hsb, hab, hos, hof', hpabove, hpnext, hhi₂, hob, hpal])
  -- memory between the entry and the writes: the stack and `NEXT`
  have hf₃ : ByteFrame s t₃ fun a ↦ Within a (stackLo s 80) 80 ∨ Within a nextAddr 8 :=
    byteFrame_same (b800050d8_mem_same h₃) (hf₁.union hpost.byteFrame)
  have hrd (a : Word) (ha : Apart a 8 (stackLo s 80) 80) (hn : Apart a 8 nextAddr 8)
      (hw : a.toNat + 8 ≤ 2 ^ 64) : t₃.getMem a = s.getMem a :=
    hf₃.getMem_of (fun x hx h ↦ by rcases h with h | h <;> addr_omega [hx, h, ha, hn, hw]) hw
  have m₀ := hrd (s.getReg .x11) (by addr_omega [hms, hmb]) (by addr_omega [hmn]) (by addr_omega [hmb])
  have m₈ := hrd (s.getReg .x11 + 8) (by addr_omega [hms, hmb]) (by addr_omega [hmn, hmb])
    (by addr_omega [hmb])
  have m₁₆ := hrd (s.getReg .x11 + 16) (by addr_omega [hms, hmb]) (by addr_omega [hmn, hmb])
    (by addr_omega [hmb])
  have c₀ := hrd (s.getReg .x12) (by addr_omega [hcs, hcb]) (by addr_omega [hcn]) (by addr_omega [hcb])
  have c₈ := hrd (s.getReg .x12 + 8) (by addr_omega [hcs, hcb]) (by addr_omega [hcn, hcb])
    (by addr_omega [hcb])
  have c₁₆ := hrd (s.getReg .x12 + 16) (by addr_omega [hcs, hcb]) (by addr_omega [hcn, hcb])
    (by addr_omega [hcb])
  have hf₄ : ByteFrame t₃ t₄ fun a ↦ Within a (s.getReg .x10) 24 ∨ Within a p 48 :=
    h₄.byteFrame (by
      rv_eval [hx8, hx10]
      and_intros <;> first
        | (intro i hi; exact Or.inl (by addr_omega [hob, hi]))
        | (intro i hi; exact Or.inr (by addr_omega [hpal, hpnext, hhi₂, hi]))
        | addr_omega [hob, hpal, hpnext, hhi₂])
  have hn₄ : t₄.getMem nextAddr = t₃.getMem nextAddr :=
    hf₄.getMem_of (fun x hx h ↦ by rcases h with h | h <;> addr_omega [hx, h, hof, hpnext, hhi₂])
      (by decide)
  have hn₃ : t₃.getMem nextAddr = t₂.getMem nextAddr := b800050d8_mem_same h₃ _
  have hnext₄ : heapNext t₄ = p.toNat + 48 := by
    simp only [heapNext, hn₄, hn₃]; exact hpnext
  have hnext₁ : heapNext s = heapNext t₁ := by simp only [heapNext, hn₁]
  -- what the writes leave
  have w₀ := b800050dc_m_x10_0 h₄
  have w₈ := b800050dc_m_x10_8 h₄
  have w₁₆ := b800050dc_m_x10_16 h₄
  have w₂₄ := b800050dc_m_x10_24 h₄
  have w₃₂ := b800050dc_m_x10_32 h₄
  have w₄₀ := b800050dc_m_x10_40 h₄
  have o₀ := b800050dc_m_x8_0 h₄
  have o₈ := b800050dc_m_x8_8 h₄
  have o₁₆ := b800050dc_m_x8_16 h₄
  rw [hx10, hx18, m₀] at w₀
  rw [hx10, hx18, m₈] at w₈
  rw [hx10, hx18, m₁₆] at w₁₆
  rw [hx10, hx9, c₀] at w₂₄
  rw [hx10, hx9, c₈] at w₃₂
  rw [hx10, hx9, c₁₆] at w₄₀
  rw [hx8, hx10] at o₈
  rw [hx8] at o₀ o₁₆
  have hptr : vecPtr t₄ (s.getReg .x10) = p := o₈
  have hcap : vecCap t₄ (s.getReg .x10) = 1 := o₀
  have hlen : vecLen t₄ (s.getReg .x10) = 1 := o₁₆
  have hval : formOf t₄ (s.getReg .x10) =
      .term (monoOf s (s.getReg .x11)) (eAt s (s.getReg .x12)) := by
    have h1 : termsOf t₄ p 1 = [termOf t₄ p] := by simp [termsOf]
    rw [formOf, hptr, hlen, show (1 : Word).toNat = 1 from rfl, h1, termOf,
      monoOf_congr w₀ w₈ w₁₆, eAt_congr w₂₄ (by rw [BitVec.add_assoc]; exact w₃₂)
        (by rw [BitVec.add_assoc]; exact w₄₀)]
    rfl
  -- the epilogue
  have hpc₄ := b800050dc_pc h₄
  have r₁ := b800050dc_x1 h₄
  have r₂ := b800050dc_x2 h₄
  have r₈ := b800050dc_x8 h₄
  have r₉ := b800050dc_x9 h₄
  have r₁₈ := b800050dc_x18 h₄
  have k₄ := b800050dc_keeps h₄
  have hs (a : Word) (ha₁ : (s.getReg .x2).toNat - 32 ≤ a.toNat) (ha₂ : a.toNat < (s.getReg .x2).toNat)
      (ha₃ : a.toNat % 8 = 0) : t₃.getMem a = t₁.getMem a :=
    ((b800050d8_mem_same h₃ a).trans (hpost.mem a (by addr_omega [ha₁, ha₂, hsb, hnx]))).trans rfl
  have sv₁ := b800050a8_m_x2_n8 h₁
  have sv₈ := b800050a8_m_x2_n16 h₁
  have sv₉ := b800050a8_m_x2_n24 h₁
  have sv₁₈ := b800050a8_m_x2_n32 h₁
  rw [hx2] at hpc₄ r₁ r₂ r₈ r₉ r₁₈
  rv_eval [] at hpc₄ r₁ r₂ r₈ r₉ r₁₈
  rw [hs _ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb]), sv₁] at hpc₄ r₁
  rw [hs _ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb]), sv₈] at r₈
  rw [hs _ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb]), sv₉] at r₉
  rw [hs _ (by addr_omega [hsb]) (by addr_omega [hsb]) (by addr_omega [hsb]), sv₁₈] at r₁₈
  refine ⟨t₄, hr₂.trans (hr₃.trans hr₄), Or.inl ⟨hpc₄.trans (returnAddress_eq s).symm,
    preserves_of r₂ r₈ r₉ r₁₈ ((k₄ .x19 (by decide)).trans ?_) fun r hr ↦ ?_, ⟨⟨⟨?_, ?_⟩, ?_, ⟨⟨?_, ?_⟩, ?_⟩,
      ?_, ?_⟩, hval⟩⟩⟩
  · rw [k₃ .x19 (by decide), hpres₂.reg .x19, k₁ .x19 (by decide)]
  · rw [k₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _), hpres₂ r (mem_of_mem hr _),
      k₁ r (mem_of_mem hr _)]
  · rw [hnext₄]; simp only [heapStart]; omega
  · rw [hnext₄]; simp only [heapEnd]; omega
  · rw [hnext₁, hnext₄]; simp only [heapNext]; omega
  · simp only [RawVecOk, Buf, hptr, hcap, hnext₄]
    exact ⟨hpal, Or.inr ⟨by simp only [heapStart]; omega, by simp⟩⟩
  · rw [hcap, hlen]
  · intro i hi
    rw [hlen] at hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    simp only [MonoOk, hptr, Nat.mul_zero, BitVec.add_zero, w₀]
    exact hpre.monoOk
  · simp only [NewBuf, hptr, hcap, hnext₄, hnext₁]
    exact ⟨hpal, Or.inr ⟨hpabove, by simp⟩⟩
  · refine (hf₃.union hf₄).dframe.mono fun a h ↦ ?_
    rcases h with (h | h) | (h | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
    · refine Or.inr (Or.inr (Or.inr ?_))
      simp only [Fresh, hnext₁, hnext₄]
      addr_omega [h, hpabove]

end Rv64Verifier.Layout.Term
