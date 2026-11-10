import Rv64Verifier.Proofs.Layout.Keep
import Rv64Verifier.Blocks.F21

/-!
# `Flushes::state_derived`, at `0x80005e38`

```rust
fn state_derived(&mut self, pc: usize, fp: usize, npc: Form, nfp: Form) {
    self.pair(
        vec![constant(SEP_STATE), npc, nfp],
        vec![constant(SEP_STATE), col(pc, 0), col(fp, 0)],
    );
}
```

compiled for `pc = 0`, `fp = 1` (`Blocks/F21.lean`), `sp'` the entry's `sp - 112`: `0x80005e38`
saves `ra`, `s0`..`s3` and calls `alloc(8, 72)`, `0x80005e6c` traps on null; `0x80005e70` calls
`term(B, One, ONE)` on the buffer `B`; `0x80005e8c` moves `npc` and `nfp` into `B + 24` and `B + 48`,
writes the `Vec` `(3, B, 3)` at `sp'` and calls `alloc(8, 72)` again (`B'`); `0x80005ee0` calls
`term(B', One, ONE)`, `0x80005efc` `col(sp' + 24, 0, 0)` and `0x80005f10` `col(sp' + 48, 1, 0)`;
`0x80005f24` moves those two into `B' + 24` and `B' + 48`, writes `(3, B', 3)` at `sp' + 48` and
calls `pair(self, sp', sp' + 48)`; `0x80005f74` restores and returns.

The phases: the first `Vec` (`pushPhase`), the second's head (`headPhase`), the two `col`s
(`colsPhase`), the second `Vec` (`toPair`); what they keep is `Carry`.
-/

namespace Rv64Verifier.Layout.StateDerived
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F21 Rv64Verifier.Model.LayoutMirror

/-- What every phase keeps, from the entry `s` to `u`: the registers and slots the epilogue restores,
`self`, `.rodata`, and the first `Vec` (at `sp'`) once built, whose buffers are allocated below `P`
or are `npc`'s and `nfp`'s. -/
structure Carry (s u : MachineState) (P : Nat) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 112
  x8 : u.getReg .x8 = s.getReg .x10
  x18 : u.getReg .x18 = 3
  regs : ∀ r ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27], u.getReg r = s.getReg r
  ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : u.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : u.getMem (s.getReg .x2 - 40) = s.getReg .x19
  heap : HeapOk u
  lo : heapNext s ≤ P
  hi : P ≤ heapNext u
  rodata : RodataOk u
  frame : DFrame s u (Scratch s u (stackLo s 1312) 1312)
  keep : flushesOf u (s.getReg .x10) = flushesOf s (s.getReg .x10) ∧ FlushesOk u (s.getReg .x10) ∧
    flushesDeep u (s.getReg .x10) = flushesDeep s (s.getReg .x10) ∧
    flushesBuf u (s.getReg .x10) = flushesBuf s (s.getReg .x10)
  push : FormVecOk u (s.getReg .x2 - 112)
  pushVal : formVecOf u (s.getReg .x2 - 112) =
    [constantRust sepStateRust, formOf s (s.getReg .x11), formOf s (s.getReg .x12)]
  pushDeep : ∀ x, formVecDeep u (s.getReg .x2 - 112) x → (heapNext s ≤ x.toNat ∧ x.toNat < P) ∨
    formBuf s (s.getReg .x11) x ∨ formBuf s (s.getReg .x12) x

/-- A step that writes only the callees' stack, the frame's locals at `sp' + 24`, `NEXT` and the heap
from `P` on keeps `Carry`. -/
theorem Carry.step {s u v : MachineState} {P : Nat} (hpre : StateDerivedPre s) (c : Carry s u P)
    {W : Word → Prop} (hf : DFrame u v W)
    (hW : ∀ x, W x → Within x (s.getReg .x2 - 1312) 1200 ∨ Within x (s.getReg .x2 - 88) 48 ∨
      Within x nextAddr 8 ∨ (P ≤ x.toNat ∧ x.toNat < heapNext v))
    (hheap : HeapOk v) (hmono : heapNext u ≤ heapNext v) (hx2 : v.getReg .x2 = u.getReg .x2)
    (hx8 : v.getReg .x8 = u.getReg .x8) (hx18 : v.getReg .x18 = u.getReg .x18)
    (hregs : ∀ r ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27], v.getReg r = u.getReg r) :
    Carry s v P := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hro := hpre.stack.rodata
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  simp only [stateDerivedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hro hss
  have hhv := hheap.hi
  have hlo := c.lo
  have hhi := c.hi
  have hslot (a : Word) (ha₁ : (s.getReg .x2).toNat - 40 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : v.getMem a = u.getMem a :=
    hf.getMem_of (fun x hx hw ↦ by
      rcases hW x hw with h | h | h | h <;> addr_omega [hx, h, hsb, hab, hnx, hhv, ha₁, ha₂])
      (by addr_omega [hsb, ha₂])
  have hbelow : ∀ x, x.toNat < P → ¬ W x := fun x hx hw ↦ by
    rcases hW x hw with h | h | h | h <;> addr_omega [hx, h, hsb, hab, hnx, hhv, hhi, hmono]
  have hk := flushesOf_frame hf c.keep.2.1
    (fun x hx hw ↦ by
      rcases hW x hw with h | h | h | h <;> addr_omega [hx, h, hss, hsb, hsf, hlo, hhv])
    (fun x hx ↦ hbelow x (by
      rw [c.keep.2.2.1] at hx; have := (hpre.ok.deep_below hx).2; omega))
    (by have := ValidMemRange.bounds hpre.self (by decide); addr_omega [this]) c.heap hmono
  have hp := formVecOf_frame' hf c.push
    (fun x hx hw ↦ by
      rcases hW x hw with h | h | h | h <;> addr_omega [hx, h, hsb, hab, hnx, hhv, hhi, hmono])
    (fun x hx ↦ hbelow x (by
      rcases c.pushDeep x hx with h | h | h
      · exact h.2
      · have := (hpre.npcOk.buf_below h).2; omega
      · have := (hpre.nfpOk.buf_below h).2; omega)) (by addr_omega [hsb]) c.heap hmono
  exact {
    x2 := hx2.trans c.x2
    x8 := hx8.trans c.x8
    x18 := hx18.trans c.x18
    regs := fun r hr ↦ (hregs r hr).trans (c.regs r hr)
    ra := (hslot (s.getReg .x2 - 8) (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.ra
    s0 := (hslot (s.getReg .x2 - 16) (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s0
    s1 := (hslot (s.getReg .x2 - 24) (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s1
    s2 := (hslot (s.getReg .x2 - 32) (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s2
    s3 := (hslot (s.getReg .x2 - 40) (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s3
    heap := hheap
    lo := hlo
    hi := by omega
    rodata := RodataOk.dframe c.rodata hf fun x hw h ↦ by
      rcases hW x hw with h' | h' | h' | h' <;> addr_omega [h, h', hsb, hro, hhv, hhi, hmono]
    frame := (c.frame.union hf).mono fun x hx ↦ by
      simp only [Scratch, Fresh] at hx ⊢
      rcases hx with (h | h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h.1, by omega⟩)
      · rcases hW x h with h | h | h | h
        · exact Or.inl (by addr_omega [h, hsb])
        · exact Or.inl (by addr_omega [h, hsb])
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨by omega, h.2⟩)
    keep := ⟨hk.1.trans c.keep.1, hk.2.1, hk.2.2.1.trans c.keep.2.2.1, hk.2.2.2.trans c.keep.2.2.2⟩
    push := hp.2.1
    pushVal := hp.1.trans c.pushVal
    pushDeep := fun x hx ↦ c.pushDeep x (by rwa [hp.2.2] at hx) }

/-- At the second `alloc(8, 72)`: the first `Vec` built. -/
structure Pushed (s t : MachineState) : Prop extends Carry s t (heapNext t) where
  pc : t.pc = 0x80000284
  x1 : t.getReg .x1 = 0x80005edc
  x10 : t.getReg .x10 = 8
  x11 : t.getReg .x11 = 72

/-- After `term(B, One, ONE)`. -/
structure Termed (s t : MachineState) (B : Word) : Prop where
  pc : t.pc = 0x80005e8c
  x2 : t.getReg .x2 = s.getReg .x2 - 112
  x8 : t.getReg .x8 = s.getReg .x10
  x9 : t.getReg .x9 = B
  x18 : t.getReg .x18 = s.getReg .x12
  x19 : t.getReg .x19 = s.getReg .x11
  regs : ∀ r ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27], t.getReg r = s.getReg r
  ra : t.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : t.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : t.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : t.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : t.getMem (s.getReg .x2 - 40) = s.getReg .x19
  al : B.toNat % 8 = 0
  lo : heapNext s ≤ B.toNat
  hi : B.toNat + 72 ≤ heapNext t
  heap : HeapOk t
  frame : DFrame s t (Scratch s t (stackLo s 1312) 1312)
  ok : FormOk t B
  val : formOf t B = constantRust sepStateRust
  buf : ∀ x, formBuf t B x → B.toNat + 72 ≤ x.toNat ∧ x.toNat < heapNext t

/-- `alloc(8, 72)` and `term(B, One, ONE)`. -/
theorem termPhase (hA : AllocSpec) (hT : TermSpec) {s : MachineState} (hpc : s.pc = 0x80005e38)
    (hpre : StateDerivedPre s) :
    ∃ t B, Reaches Image.code s t ∧ (Termed s t B ∨ Dead Image.code t) := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hro := hpre.stack.rodata
  have hns := hpre.npcStack
  have hfs := hpre.nfpStack
  have hnf := hpre.npcFree
  have hff := hpre.nfpFree
  have hnb := ValidMemRange.bounds hpre.npc (by decide)
  have hfb := ValidMemRange.bounds hpre.nfp (by decide)
  have hheap := hpre.heap
  have hlo₀ := hheap.lo
  have hhi₀ := hheap.hi
  simp only [stateDerivedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hro hns hfs
  -- the frame, and `alloc(8, 72)`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005e38_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hsb])
  have k₁ := b80005e38_keeps h₁
  have hm₁ := b80005e38_frame h₁ (by addr_omega [hsb])
  have x2₁ := b80005e38_x2 h₁
  have hn₁ : heapNext t₁ = heapNext s := by
    simp only [heapNext]; rw [hm₁ _ (by addr_omega [hnx, hsb])]
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost₂⟩ | hdead⟩ :=
    hA.call hr₁ (b80005e38_pc h₁) ⟨⟨hn₁ ▸ hlo₀, hn₁ ▸ hhi₀⟩, by rw [b80005e38_x10 h₁]; decide⟩
  swap
  · exact ⟨t₂, 0, hr₂, Or.inr hdead⟩
  obtain ⟨B, hB⟩ : ∃ B, t₂.getReg .x10 = B := ⟨_, rfl⟩
  have hBal : B.toNat % 8 = 0 := by rw [← hB]; simpa [b80005e38_x10 h₁] using hpost₂.aligned
  have hBlo : heapNext s ≤ B.toNat := by rw [← hB, ← hn₁]; exact hpost₂.above
  have hBn : heapNext t₂ = B.toNat + 72 := by rw [hpost₂.next, hB, b80005e38_x11 h₁]; rfl
  have hh₂ := hpost₂.heap.hi
  simp only [heapStart, heapEnd] at hlo₀ hhi₀ hh₂
  have hB0 : t₂.getReg .x10 ≠ 0 := by
    rw [hB]; rintro rfl; simp at hBlo; omega
  -- the null check, and `term(B, One, ONE)`
  obtain ⟨t₂', hr₂', h₂'⟩ := Sym.BlockSpec.reaches b80005e6c_spec
    (by rw [hpc₂, returnAddress_eq, b80005e38_x1 h₁]; decide) trivial
  have k₂' := b80005e6c_keeps h₂'
  have x2₂' : t₂'.getReg .x2 = s.getReg .x2 - 112 := by
    rw [k₂' .x2 (by decide), hpres₂.reg .x2, x2₁]
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005e70_spec
    (b80005e6c_pc_not_taken h₂' hB0) (by
      rv_eval [x2₂']
      valid_access hpre.stack.valid [hsb])
  have k₃ := b80005e70_keeps h₃
  have hm₃ := b80005e70_frame h₃ (by addr_omega [hsb, x2₂'])
  rw [x2₂'] at hm₃
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 112 := (k₃ .x2 (by decide)).trans x2₂'
  have x10₃ : t₃.getReg .x10 = B := by rw [k₃ .x10 (by decide), k₂' .x10 (by decide), hB]
  have x11₃ : t₃.getReg .x11 = s.getReg .x2 - 64 := by rw [b80005e70_x11 h₃, x2₂']; rv_eval []
  have x12₃ := b80005e70_x12 h₃
  have tag₃ : t₃.getMem (s.getReg .x2 - 64) = 0 := by
    have := b80005e70_m_x2_48 h₃; rw [x2₂'] at this; rv_eval [] at this; exact this
  have hn₃ : heapNext t₃ = B.toNat + 72 := by
    simp only [heapNext]; rw [hm₃ _ (by addr_omega [hnx, hsb]), b80005e6c_mem_same h₂']; exact hBn
  have hf₃ : DFrame t₁ t₃ (Scratch t₁ t₃ (stackLo s 1312) 1272) :=
    ((hpost₂.byteFrame.dframe.union (DFrame.of_same (b80005e6c_mem_same h₂') fun _ ↦ False)).union
      hm₃.dframe).mono fun x hx ↦ by
        rcases hx with (hx | hx) | hx
        · exact Or.inr (Or.inl hx)
        · exact hx.elim
        · exact Or.inl (by addr_omega [hx, hsb])
  have hrod₃ : RodataOk t₃ := RodataOk.dframe hpre.rodata (hm₁.dframe.union hf₃) fun x hw h ↦ by
    simp only [Scratch, Fresh] at hw
    rcases hw with hw | hw | hw | hw <;> addr_omega [h, hw, hsb, hro, hh₂, hn₃, hBn]
  have hBv : ValidMemRange B 9 := validMemRange_of hBal (Or.inl ⟨by omega, by omega⟩)
  have hterm : TermPre t₃ := {
    heap := ⟨by rw [hn₃]; simp only [heapStart]; omega, by rw [hn₃]; simp only [heapEnd]; omega⟩
    stack := hpre.stack.inner (k := 112) x2₃ (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [x10₃]; exact ValidMemRange.sub hBv (by omega) (by omega) (by omega)
    mono := by rw [x11₃]; valid_sub hpre.stack.valid [hsb]
    coeff := by rw [x12₃]; exact validMemRange_of (by decide) (Or.inr ⟨by decide, by decide⟩)
    monoOk := by rw [x11₃]; simp only [MonoOk, tag₃]; decide
    outFree := by rw [x10₃]; addr_omega [hn₃, hh₂, hBn]
    monoNext := by rw [x11₃]; addr_omega [hsb, hnx]
    coeffNext := by rw [x12₃]; addr_omega []
    outStack := by rw [x10₃]; addr_omega [hsb, x2₃, hab, hh₂, hBn]
    monoStack := by rw [x11₃]; addr_omega [hsb, x2₃]
    coeffStack := by rw [x12₃]; addr_omega [hsb, x2₃, hro] }
  obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hnew₄, hval₄⟩ | hdead⟩ := hT.call hr₃ (b80005e70_pc h₃) hterm
  swap
  · exact ⟨t₄, 0, hr₂.trans (hr₂'.trans hr₄), Or.inr hdead⟩
  rw [x10₃, x11₃, x12₃] at hval₄
  rw [x10₃] at hnew₄
  have hv₄ : formOf t₄ B = constantRust sepStateRust := by
    rw [hval₄, eAt_one hrod₃, monoOf, tag₃]
    rfl
  have x2₄ : t₄.getReg .x2 = s.getReg .x2 - 112 := (hpres₄.reg .x2).trans x2₃
  have x9₄ : t₄.getReg .x9 = B := by
    rw [hpres₄.reg .x9, b80005e70_x9 h₃, k₂' .x10 (by decide), hB]
  have x18₄ : t₄.getReg .x18 = s.getReg .x12 := by
    rw [hpres₄.reg .x18, k₃ .x18 (by decide), k₂' .x18 (by decide), hpres₂.reg .x18,
      b80005e38_x18 h₁]
  have x19₄ : t₄.getReg .x19 = s.getReg .x11 := by
    rw [hpres₄.reg .x19, k₃ .x19 (by decide), k₂' .x19 (by decide), hpres₂.reg .x19,
      b80005e38_x19 h₁]
  have hn₄ := hnew₄.mono
  have hh₄ := hnew₄.heap.hi
  have hf₄ : DFrame t₁ t₄ (Scratch t₁ t₄ (stackLo s 1312) 1272) :=
    (hf₃.union hnew₄.frame).mono fun x hx ↦ by
      simp only [Scratch, Fresh] at hx ⊢
      rcases hx with (hx | hx | hx) | hx | hx | hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr ⟨hx.1, by omega⟩)
      · exact Or.inr (Or.inr (by addr_omega [hx, hn₁, hBlo, hBn, hn₄, hn₃]))
      · exact Or.inl (by addr_omega [hx, hsb, x2₃])
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr ⟨by omega, hx.2⟩)
  have hb0 : ∀ x, formBuf t₄ B x → B.toNat + 72 ≤ x.toNat ∧ x.toNat < heapNext t₄ := by
    intro x hx
    have hb := hnew₄.fresh
    simp only [NewBuf, formBuf, Within] at hb hx
    omega
  have hslot (a : Word) (ha₁ : (s.getReg .x2).toNat - 40 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : t₄.getMem a = t₁.getMem a := by
    refine hf₄.getMem_of (fun x hx hw ↦ ?_) (by addr_omega [hsb, ha₂])
    simp only [Scratch, Fresh] at hw
    rcases hw with hw | hw | hw <;> addr_omega [hx, hw, hsb, hnx, hab, hh₄, ha₁, ha₂]
  refine ⟨t₄, B, hr₂.trans (hr₂'.trans hr₄), Or.inl {
    pc := by rw [hpc₄, returnAddress_eq, b80005e70_x1 h₃]; decide
    x2 := x2₄
    x8 := by
      rw [hpres₄.reg .x8, k₃ .x8 (by decide), k₂' .x8 (by decide), hpres₂.reg .x8,
        b80005e38_x8 h₁]
    x9 := x9₄
    x18 := x18₄
    x19 := x19₄
    regs := fun r hr ↦ by
      rw [hpres₄ r (mem_of_mem hr _), k₃ r (mem_of_mem hr _), k₂' r (mem_of_mem hr _),
        hpres₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
    ra := by rw [hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])]; exact b80005e38_m_x2_n8 h₁
    s0 := by rw [hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])]; exact b80005e38_m_x2_n16 h₁
    s1 := by rw [hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])]; exact b80005e38_m_x2_n24 h₁
    s2 := by rw [hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])]; exact b80005e38_m_x2_n32 h₁
    s3 := by rw [hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])]; exact b80005e38_m_x2_n40 h₁
    al := hBal
    lo := hBlo
    hi := by omega
    heap := hnew₄.heap
    frame := (hm₁.dframe.union hf₄).mono fun x hx ↦ by
      simp only [Scratch, Fresh] at hx ⊢
      rcases hx with hx | hx | hx | hx
      · exact Or.inl (by addr_omega [hx, hsb])
      · exact Or.inl (by addr_omega [hx, hsb])
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr ⟨by omega, hx.2⟩)
    ok := hnew₄.ok
    val := hv₄
    buf := hb0 }⟩

/-- The first `Vec`: the moves and the header. -/
theorem pushPhase (hA : AllocSpec) (hT : TermSpec) {s : MachineState} (hpc : s.pc = 0x80005e38)
    (hpre : StateDerivedPre s) : ∃ t, Reaches Image.code s t ∧ (Pushed s t ∨ Dead Image.code t) := by
  obtain ⟨t₄, B, hr₄, T | hdead⟩ := termPhase hA hT hpc hpre
  swap
  · exact ⟨t₄, hr₄, Or.inr hdead⟩
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hro := hpre.stack.rodata
  have hns := hpre.npcStack
  have hfs := hpre.nfpStack
  have hnf := hpre.npcFree
  have hff := hpre.nfpFree
  have hnb := ValidMemRange.bounds hpre.npc (by decide)
  have hfb := ValidMemRange.bounds hpre.nfp (by decide)
  have hheap := hpre.heap
  have hlo₀ := hheap.lo
  have hhi₀ := hheap.hi
  simp only [stateDerivedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hro hns hfs
  have x2₄ := T.x2
  have x9₄ := T.x9
  have x18₄ := T.x18
  have x19₄ := T.x19
  have hBal := T.al
  have hBlo := T.lo
  have hBhi := T.hi
  have hh₄ := T.heap.hi
  simp only [heapStart, heapEnd] at hlo₀ hhi₀ hh₄
  have hBv : ValidMemRange B 9 := validMemRange_of hBal (Or.inl ⟨by omega, by omega⟩)
  -- the moves, and the `Vec` header
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80005e8c_spec
    T.pc (by
      rv_eval [x2₄, x9₄, x18₄, x19₄]
      and_intros
      all_goals (try valid_access hpre.stack.valid [hsb])
      all_goals (try valid_access hBv [hBal, hBhi, hh₄])
      all_goals (try valid_access hpre.npc [hnb])
      all_goals (try valid_access hpre.nfp [hfb])
      all_goals addr_omega [hsb, hab, hBal, hBhi, hh₄, hBlo, hnb, hfb, hnf, hff, hns, hfs])
  have k₅ := b80005e8c_keeps h₅
  have hw₅ : ByteFrame t₄ t₅ fun x ↦ Within x (s.getReg .x2 - 112) 24 ∨ Within x (B + 24) 48 :=
    h₅.byteFrame (by
      rv_eval [x2₄, x9₄]
      and_intros <;> first
        | (intro i hi; exact Or.inl (by addr_omega [hsb, hi]))
        | (intro i hi; exact Or.inr (by addr_omega [hBal, hBhi, hh₄, hi]))
        | addr_omega [hsb, hBal, hBhi, hh₄])
  have hn₅ : heapNext t₅ = heapNext t₄ := by
    have := hw₅.getMem_of (a := nextAddr) (fun x hx h ↦ by
      rcases h with h | h <;> addr_omega [hx, h, hsb, hnx, hBhi, hh₄]) (by decide)
    simp only [heapNext, this]
  have hmono₅ : heapNext s ≤ heapNext t₅ := by omega
  have hh₅ : heapNext t₅ ≤ heapEnd := by rw [hn₅]; exact hh₄
  have hf₅ : DFrame s t₅ (Scratch s t₅ (stackLo s 1312) 1312) :=
    (T.frame.union hw₅.dframe).mono fun x hx ↦ by
      simp only [Scratch, Fresh] at hx ⊢
      rcases hx with (hx | hx | hx) | hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr ⟨hx.1, by omega⟩)
      · exact Or.inl (by addr_omega [hx, hsb])
      · exact Or.inr (Or.inr (by addr_omega [hx, hBlo, hBhi, hn₅]))
  -- `npc`'s and `nfp`'s headers, read at `t₄`, are the entry's
  have hkeepS (a : Word) (ha : Apart a 8 (stackLo s 1312) 1312)
      (hfree : a.toNat + 8 ≤ heapNext s ∨ heapEnd ≤ a.toNat) (hna : Apart a 8 nextAddr 8)
      (hw : a.toNat + 8 ≤ 2 ^ 64) : t₄.getMem a = s.getMem a := by
    refine T.frame.getMem_of (fun x hx hw' ↦ ?_) hw
    simp only [Scratch, Fresh] at hw'
    rcases hw' with h | h | h <;> addr_omega [hx, h, ha, hfree, hna, hsb, hh₄, hw]
  have n24 := b80005e8c_m_x9_24 h₅
  have n32 := b80005e8c_m_x9_32 h₅
  have n40 := b80005e8c_m_x9_40 h₅
  have f48 := b80005e8c_m_x9_48 h₅
  have f56 := b80005e8c_m_x9_56 h₅
  have f64 := b80005e8c_m_x9_64 h₅
  rw [x9₄, x19₄] at n24 n32 n40
  rw [x9₄, x18₄] at f48 f56 f64
  have hnf1 := hnf.1
  have hff1 := hff.1
  rw [hkeepS _ (by addr_omega [hns, hnb]) (by addr_omega [hnf1, hnb]) (by addr_omega [hnf.2, hnb])
    (by addr_omega [hnb])] at n24
  rw [hkeepS _ (by addr_omega [hns, hnb]) (by addr_omega [hnf1, hnb]) (by addr_omega [hnf.2, hnb])
    (by addr_omega [hnb])] at n32
  rw [hkeepS _ (by addr_omega [hns, hnb]) (by addr_omega [hnf1, hnb]) (by addr_omega [hnf.2, hnb])
    (by addr_omega [hnb])] at n40
  rw [hkeepS _ (by addr_omega [hfs, hfb]) (by addr_omega [hff1, hfb]) (by addr_omega [hff.2, hfb])
    (by addr_omega [hfb])] at f48
  rw [hkeepS _ (by addr_omega [hfs, hfb]) (by addr_omega [hff1, hfb]) (by addr_omega [hff.2, hfb])
    (by addr_omega [hfb])] at f56
  rw [hkeepS _ (by addr_omega [hfs, hfb]) (by addr_omega [hff1, hfb]) (by addr_omega [hff.2, hfb])
    (by addr_omega [hfb])] at f64
  -- the three forms
  have hb0 := T.buf
  have he0 := formOf_frame hw₅.dframe T.ok
    (fun x hx h ↦ by rcases h with h | h <;> addr_omega [hx, h, hsb, hab, hBhi, hh₄])
    (fun x hx h ↦ by
      have := hb0 x hx
      rcases h with h | h <;> addr_omega [this, h, hsb, hab, hh₄])
    (by addr_omega [hBhi, hh₄]) T.heap (by omega)
  have hbuf0 := formBuf_frame hw₅.dframe (e := B)
    (fun x hx h ↦ by rcases h with h | h <;> addr_omega [hx, h, hsb, hab, hBhi, hh₄])
    (by addr_omega [hBhi, hh₄])
  have hnot (x : Word) (hx : x.toNat < heapNext s) : ¬ Scratch s t₅ (stackLo s 1312) 1312 x :=
    not_scratch hab hhi₀ hx
  have he1 := formOf_move hf₅ hpre.npcOk (e := B + 24) n24
    (by rw [show B + 24 + 8 = B + 32 by rv_eval []]; exact n32)
    (by rw [show B + 24 + 16 = B + 40 by rv_eval []]; exact n40)
    (fun x hx ↦ hnot x (hpre.npcOk.buf_below hx).2) hheap hmono₅
  have he2 := formOf_move hf₅ hpre.nfpOk (e := B + 48) f48
    (by rw [show B + 48 + 8 = B + 56 by rv_eval []]; exact f56)
    (by rw [show B + 48 + 16 = B + 64 by rv_eval []]; exact f64)
    (fun x hx ↦ hnot x (hpre.nfpOk.buf_below hx).2) hheap hmono₅
  have hm0 : t₅.getMem (s.getReg .x2 - 112) = 3 := by
    have := b80005e8c_m_x2_0 h₅; rwa [x2₄] at this
  have hm8 : t₅.getMem (s.getReg .x2 - 112 + 8) = B := by
    have := b80005e8c_m_x2_8 h₅; rwa [x2₄, x9₄] at this
  have hm16 : t₅.getMem (s.getReg .x2 - 112 + 16) = 3 := by
    have := b80005e8c_m_x2_16 h₅; rwa [x2₄] at this
  have hv := formVec3 hm0 hm8 hm16 hBal (by simp only [heapStart]; omega) (by omega) he0.2 he1.2.1
    he2.2.1 (fun x hx hw ↦ by
      rcases hx with hx | hx | hx
      · rw [hbuf0] at hx; have := hb0 x hx; addr_omega [this, hw]
      · rw [he1.2.2] at hx; have := (hpre.npcOk.buf_below hx).2; addr_omega [this, hw, hBlo]
      · rw [he2.2.2] at hx; have := (hpre.nfpOk.buf_below hx).2; addr_omega [this, hw, hBlo])
  have hslot (a : Word) (ha₁ : (s.getReg .x2).toNat - 40 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : t₅.getMem a = t₄.getMem a :=
    hw₅.getMem_of (fun x hx h ↦ by
      rcases h with h | h <;> addr_omega [hx, h, hsb, hab, hBhi, hh₄, ha₁, ha₂])
      (by addr_omega [hsb, ha₂])
  have hkeep := flushesOf_keep hf₅ hpre.ok hheap hmono₅ hh₅ hab hpre.selfFree
    (by have := hpre.selfStack; simp only [stateDerivedStack, colStack, powStack,
      Contracts.mulStack, Nat.reduceAdd] at this; exact this)
    (by have := ValidMemRange.bounds hpre.self (by decide); addr_omega [this])
  refine ⟨t₅, hr₄.trans hr₅, Or.inl {
    x2 := (k₅ .x2 (by decide)).trans x2₄
    x8 := (k₅ .x8 (by decide)).trans T.x8
    x18 := b80005e8c_x18 h₅
    regs := fun r hr ↦ (k₅ r (mem_of_mem hr _)).trans (T.regs r hr)
    ra := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans T.ra
    s0 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans T.s0
    s1 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans T.s1
    s2 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans T.s2
    s3 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans T.s3
    heap := ⟨by simp only [heapStart]; omega, hh₅⟩
    lo := hmono₅
    hi := Nat.le_refl _
    rodata := RodataOk.dframe hpre.rodata hf₅ fun x hx ↦ not_rodata_of_scratch hro hh₅ hx
    frame := hf₅
    keep := hkeep
    push := hv.1
    pushVal := by rw [hv.2.1, he0.1, T.val, he1.1, he2.1]
    pushDeep := fun x hx ↦ by
      rcases hv.2.2 x hx with h | h | h | h
      · exact Or.inl (by addr_omega [h, hBlo, hBhi, hn₅])
      · rw [hbuf0] at h; have := hb0 x h; exact Or.inl (by omega)
      · rw [he1.2.2] at h; exact Or.inr (Or.inl h)
      · rw [he2.2.2] at h; exact Or.inr (Or.inr h)
    pc := b80005e8c_pc h₅
    x1 := b80005e8c_x1 h₅
    x10 := b80005e8c_x10 h₅
    x11 := b80005e8c_x11 h₅ }⟩

/-- At the first `col`: the second `Vec`'s buffer `B` allocated, its first form built. -/
structure Headed (s t : MachineState) (P : Nat) (B : Word) : Prop extends Carry s t P where
  pc : t.pc = 0x80005efc
  x9 : t.getReg .x9 = B
  al : B.toNat % 8 = 0
  blo : P ≤ B.toNat
  bhi : B.toNat + 72 ≤ heapNext t
  ok : FormOk t B
  val : formOf t B = constantRust sepStateRust
  buf : ∀ x, formBuf t B x → B.toNat + 72 ≤ x.toNat ∧ x.toNat < heapNext t

theorem preservesRegs {s t : MachineState} (h : Preserves s t) :
    ∀ r ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27], t.getReg r = s.getReg r :=
  fun r hr ↦ h r (mem_of_mem hr _)

/-- `alloc(8, 72)` and `term(B, One, ONE)` again. -/
theorem headPhase (hA : AllocSpec) (hT : TermSpec) {s u : MachineState} (hpre : StateDerivedPre s)
    (c : Pushed s u) :
    ∃ t B, Reaches Image.code u t ∧ (Headed s t (heapNext u) B ∨ Dead Image.code t) := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hro := hpre.stack.rodata
  simp only [stateDerivedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hro
  have hlo₀ := c.heap.lo
  have hhi₀ := c.heap.hi
  simp only [heapStart, heapEnd] at hlo₀ hhi₀
  obtain ⟨u₁, hr₁, ⟨hpc₁, hpres₁, hpost₁⟩ | hdead⟩ :=
    hA.call (Reaches.refl u) c.pc ⟨c.heap, by rw [c.x10]; decide⟩
  swap
  · exact ⟨u₁, 0, hr₁, Or.inr hdead⟩
  obtain ⟨B, hB⟩ : ∃ B, u₁.getReg .x10 = B := ⟨_, rfl⟩
  have hBal : B.toNat % 8 = 0 := by rw [← hB]; simpa [c.x10] using hpost₁.aligned
  have hBlo : heapNext u ≤ B.toNat := by rw [← hB]; exact hpost₁.above
  have hBn : heapNext u₁ = B.toNat + 72 := by rw [hpost₁.next, hB, c.x11]; rfl
  have hh₁ := hpost₁.heap.hi
  simp only [heapEnd] at hh₁
  have hB0 : u₁.getReg .x10 ≠ 0 := by
    rw [hB]; rintro rfl; simp at hBlo; omega
  have c₁ := c.step hpre hpost₁.byteFrame.dframe (fun x hx ↦ Or.inr (Or.inr (Or.inl hx)))
    hpost₁.heap (by omega) (hpres₁.reg .x2) (hpres₁.reg .x8) (hpres₁.reg .x18) (preservesRegs hpres₁)
  -- the null check, and `term(B, One, ONE)`
  obtain ⟨u₂, hr₂, h₂⟩ := Sym.BlockSpec.reaches b80005edc_spec
    (by rw [hpc₁, returnAddress_eq, c.x1]; decide) trivial
  have k₂ := b80005edc_keeps h₂
  have hm₂ := b80005edc_mem_same h₂
  have hn₂ : heapNext u₂ = heapNext u₁ := by simp only [heapNext, hm₂]
  have c₂ := c₁.step hpre (DFrame.of_same hm₂ fun _ ↦ False) (fun _ h ↦ h.elim)
    ⟨hn₂ ▸ hpost₁.heap.lo, hn₂ ▸ hpost₁.heap.hi⟩ hn₂.ge (k₂ .x2 (by decide)) (k₂ .x8 (by decide))
    (k₂ .x18 (by decide)) fun r hr ↦ k₂ r (mem_of_mem hr _)
  obtain ⟨u₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005ee0_spec
    (b80005edc_pc_not_taken h₂ hB0) (by
      rv_eval [c₂.x2]
      valid_access hpre.stack.valid [hsb])
  have k₃ := b80005ee0_keeps h₃
  have hm₃ := b80005ee0_frame h₃ (by addr_omega [hsb, c₂.x2])
  rw [c₂.x2] at hm₃
  have hn₃ : heapNext u₃ = B.toNat + 72 := by
    simp only [heapNext]; rw [hm₃ _ (by addr_omega [hnx, hsb])]; rw [← hBn, ← hn₂]; rfl
  have c₃ := c₂.step hpre hm₃.dframe (fun x hx ↦ Or.inr (Or.inl (by addr_omega [hx, hsb])))
    ⟨by rw [hn₃]; simp only [heapStart]; omega, by rw [hn₃]; simp only [heapEnd]; omega⟩
    (by rw [hn₃, hn₂, hBn]) (k₃ .x2 (by decide)) (k₃ .x8 (by decide))
    (k₃ .x18 (by decide)) fun r hr ↦ k₃ r (mem_of_mem hr _)
  have x10₃ : u₃.getReg .x10 = B := by rw [k₃ .x10 (by decide), k₂ .x10 (by decide), hB]
  have x11₃ : u₃.getReg .x11 = s.getReg .x2 - 64 := by rw [b80005ee0_x11 h₃, c₂.x2]; rv_eval []
  have x12₃ := b80005ee0_x12 h₃
  have tag₃ : u₃.getMem (s.getReg .x2 - 64) = 0 := by
    have := b80005ee0_m_x2_48 h₃; rw [c₂.x2] at this; rv_eval [] at this; exact this
  have hBv : ValidMemRange B 9 := validMemRange_of hBal (Or.inl ⟨by omega, by omega⟩)
  have hterm : TermPre u₃ := {
    heap := c₃.heap
    stack := hpre.stack.inner (k := 112) c₃.x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [x10₃]; exact ValidMemRange.sub hBv (by omega) (by omega) (by omega)
    mono := by rw [x11₃]; valid_sub hpre.stack.valid [hsb]
    coeff := by rw [x12₃]; exact validMemRange_of (by decide) (Or.inr ⟨by decide, by decide⟩)
    monoOk := by rw [x11₃]; simp only [MonoOk, tag₃]; decide
    outFree := by rw [x10₃]; addr_omega [hn₃, hh₁, hBn]
    monoNext := by rw [x11₃]; addr_omega [hsb, hnx]
    coeffNext := by rw [x12₃]; addr_omega []
    outStack := by rw [x10₃]; addr_omega [hsb, c₃.x2, hab, hh₁, hBn]
    monoStack := by rw [x11₃]; addr_omega [hsb, c₃.x2]
    coeffStack := by rw [x12₃]; addr_omega [hsb, c₃.x2, hro] }
  obtain ⟨u₄, hr₄, ⟨hpc₄, hpres₄, hnew₄, hval₄⟩ | hdead⟩ := hT.call hr₃ (b80005ee0_pc h₃) hterm
  swap
  · exact ⟨u₄, 0, hr₁.trans (hr₂.trans hr₄), Or.inr hdead⟩
  rw [x10₃, x11₃, x12₃] at hval₄
  rw [x10₃] at hnew₄
  have hn₄ := hnew₄.mono
  have c₄ := c₃.step hpre hnew₄.frame (fun x hx ↦ by
      simp only [Fresh] at hx
      rcases hx with hx | hx | hx | hx
      · exact Or.inr (Or.inr (Or.inr (by addr_omega [hx, hBlo, hn₃, hn₄])))
      · exact Or.inl (by addr_omega [hx, hsb, c₃.x2])
      · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, hx.2⟩)))
    hnew₄.heap hn₄ (hpres₄.reg .x2) (hpres₄.reg .x8) (hpres₄.reg .x18) (preservesRegs hpres₄)
  refine ⟨u₄, B, hr₁.trans (hr₂.trans hr₄), Or.inl {
    toCarry := c₄
    pc := by rw [hpc₄, returnAddress_eq, b80005ee0_x1 h₃]; decide
    x9 := by rw [hpres₄.reg .x9, b80005ee0_x9 h₃, k₂ .x10 (by decide), hB]
    al := hBal
    blo := hBlo
    bhi := by omega
    ok := hnew₄.ok
    val := by rw [hval₄, eAt_one c₃.rodata, monoOf, tag₃]; rfl
    buf := fun x hx ↦ by
      have hb := hnew₄.fresh
      simp only [NewBuf, formBuf, Within] at hb hx
      omega }⟩

/-- At the moves into `B`: the two `col`s built at `sp' + 24` and `sp' + 48`, their buffers allocated
from `Q` on. -/
structure Cols (s t : MachineState) (P Q : Nat) (B : Word) : Prop extends Carry s t P where
  pc : t.pc = 0x80005f24
  x9 : t.getReg .x9 = B
  al : B.toNat % 8 = 0
  blo : P ≤ B.toNat
  bq : B.toNat + 72 ≤ Q
  qhi : Q ≤ heapNext t
  ok : FormOk t B
  val : formOf t B = constantRust sepStateRust
  buf : ∀ x, formBuf t B x → B.toNat + 72 ≤ x.toNat ∧ x.toNat < Q
  ok1 : FormOk t (s.getReg .x2 - 88)
  val1 : formOf t (s.getReg .x2 - 88) = colRust 0 0
  buf1 : ∀ x, formBuf t (s.getReg .x2 - 88) x → Q ≤ x.toNat ∧ x.toNat < heapNext t
  ok2 : FormOk t (s.getReg .x2 - 64)
  val2 : formOf t (s.getReg .x2 - 64) = colRust 1 0
  buf2 : ∀ x, formBuf t (s.getReg .x2 - 64) x → Q ≤ x.toNat ∧ x.toNat < heapNext t

/-- `col(sp' + 24, 0, 0)` and `col(sp' + 48, 1, 0)`. -/
theorem colsPhase (hC : ColSpec) {s v : MachineState} {P : Nat} {B : Word}
    (hpre : StateDerivedPre s) (c : Headed s v P B) :
    ∃ t, Reaches Image.code v t ∧ (Cols s t P (heapNext v) B ∨ Dead Image.code t) := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  simp only [stateDerivedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx
  have hhv := c.heap.hi
  have hbhi := c.bhi
  have hblo := c.blo
  have hplo := c.lo
  have hphi := c.hi
  simp only [heapEnd] at hhv
  obtain ⟨v₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b80005efc_spec c.pc trivial
  have k₁ := b80005efc_keeps h₁
  have hm₁ := b80005efc_mem_same h₁
  have hn₁ : heapNext v₁ = heapNext v := by simp only [heapNext, hm₁]
  have c₁ := c.step hpre (DFrame.of_same hm₁ fun _ ↦ False) (fun _ h ↦ h.elim)
    ⟨hn₁ ▸ c.heap.lo, hn₁ ▸ c.heap.hi⟩ hn₁.ge (k₁ .x2 (by decide)) (k₁ .x8 (by decide))
    (k₁ .x18 (by decide)) fun r hr ↦ k₁ r (mem_of_mem hr _)
  have x10₁ : v₁.getReg .x10 = s.getReg .x2 - 88 := by rw [b80005efc_x10 h₁, c.x2]; rv_eval []
  have hcol₁ : ColPre v₁ := {
    heap := c₁.heap
    stack := hpre.stack.inner (k := 112) c₁.x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [x10₁]; valid_sub hpre.stack.valid [hsb]
    outFree := by rw [x10₁]; addr_omega [hsb, hab, hnx]
    outStack := by rw [x10₁]; addr_omega [hsb, c₁.x2]
    rodata := c₁.rodata }
  obtain ⟨v₂, hr₂, ⟨hpc₂, hpres₂, hnew₂, hval₂⟩ | hdead⟩ := hC.call hr₁ (b80005efc_pc h₁) hcol₁
  swap
  · exact ⟨v₂, hr₂, Or.inr hdead⟩
  rw [x10₁, b80005efc_x11 h₁, b80005efc_x12 h₁] at hval₂
  rw [x10₁] at hnew₂
  have hn₂ := hnew₂.mono
  have hh₂ := hnew₂.heap.hi
  simp only [heapEnd] at hh₂
  have hW₂ : ∀ x, (Within x (s.getReg .x2 - 88) 24 ∨ Within x (stackLo v₁ colStack) colStack ∨
      Within x nextAddr 8 ∨ Fresh v₁ v₂ x) → Within x (s.getReg .x2 - 1312) 1200 ∨
      Within x (s.getReg .x2 - 88) 48 ∨ Within x nextAddr 8 ∨ (P ≤ x.toNat ∧ x.toNat < heapNext v₂) :=
    fun x hx ↦ by
      simp only [Fresh] at hx
      rcases hx with hx | hx | hx | hx
      · exact Or.inr (Or.inl (by addr_omega [hx, hsb]))
      · exact Or.inl (by addr_omega [hx, hsb, c₁.x2])
      · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, hx.2⟩))
  have c₂ := c₁.step hpre hnew₂.frame hW₂ hnew₂.heap hn₂ (hpres₂.reg .x2) (hpres₂.reg .x8)
    (hpres₂.reg .x18) (preservesRegs hpres₂)
  have hf₂ : DFrame v v₂ fun x ↦ Within x (s.getReg .x2 - 88) 24 ∨
      Within x (stackLo v₁ colStack) colStack ∨ Within x nextAddr 8 ∨ Fresh v₁ v₂ x :=
    ((DFrame.of_same hm₁ fun _ ↦ False).union hnew₂.frame).mono fun x hx ↦ hx.elim False.elim id
  have hB₂ := formOf_frame hf₂ c.ok (fun x hx hw ↦ by
      simp only [Fresh] at hw
      rcases hw with h | h | h | h <;> addr_omega [hx, h, hsb, hab, hnx, hbhi, hhv, hn₁, c₁.x2])
    (fun x hx hw ↦ by
      have := c.buf x hx
      simp only [Fresh] at hw
      rcases hw with h | h | h | h <;> addr_omega [this, h, hsb, hab, hnx, hhv, hn₁, c₁.x2])
    (by addr_omega [hbhi, hhv]) c.heap (by omega)
  have hbB₂ := formBuf_frame hf₂ (e := B) (fun x hx hw ↦ by
      simp only [Fresh] at hw
      rcases hw with h | h | h | h <;> addr_omega [hx, h, hsb, hab, hnx, hbhi, hhv, hn₁, c₁.x2])
    (by addr_omega [hbhi, hhv])
  have hb₂ : ∀ x, formBuf v₂ (s.getReg .x2 - 88) x → heapNext v ≤ x.toNat ∧ x.toNat < heapNext v₂ := by
    intro x hx
    have hb := hnew₂.fresh
    simp only [NewBuf, formBuf, Within] at hb hx
    omega
  -- `col(sp' + 48, 1, 0)`
  obtain ⟨v₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b80005f10_spec
    (by rw [hpc₂, returnAddress_eq, b80005efc_x1 h₁]; decide) trivial
  have k₃ := b80005f10_keeps h₃
  have hm₃ := b80005f10_mem_same h₃
  have hn₃ : heapNext v₃ = heapNext v₂ := by simp only [heapNext, hm₃]
  have c₃ := c₂.step hpre (DFrame.of_same hm₃ fun _ ↦ False) (fun _ h ↦ h.elim)
    ⟨hn₃ ▸ c₂.heap.lo, hn₃ ▸ c₂.heap.hi⟩ hn₃.ge (k₃ .x2 (by decide)) (k₃ .x8 (by decide))
    (k₃ .x18 (by decide)) fun r hr ↦ k₃ r (mem_of_mem hr _)
  have x10₃ : v₃.getReg .x10 = s.getReg .x2 - 64 := by
    rw [b80005f10_x10 h₃, (hpres₂.reg .x2).trans c₁.x2]; rv_eval []
  have hcol₃ : ColPre v₃ := {
    heap := c₃.heap
    stack := hpre.stack.inner (k := 112) c₃.x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [x10₃]; valid_sub hpre.stack.valid [hsb]
    outFree := by rw [x10₃]; addr_omega [hsb, hab, hnx]
    outStack := by rw [x10₃]; addr_omega [hsb, c₃.x2]
    rodata := c₃.rodata }
  obtain ⟨v₄, hr₄, ⟨hpc₄, hpres₄, hnew₄, hval₄⟩ | hdead⟩ := hC.call hr₃ (b80005f10_pc h₃) hcol₃
  swap
  · exact ⟨v₄, hr₂.trans hr₄, Or.inr hdead⟩
  rw [x10₃, b80005f10_x11 h₃, b80005f10_x12 h₃] at hval₄
  rw [x10₃] at hnew₄
  have hn₄ := hnew₄.mono
  have hh₄ := hnew₄.heap.hi
  simp only [heapEnd] at hh₄
  have c₄ := c₃.step hpre hnew₄.frame (fun x hx ↦ by
      simp only [Fresh] at hx
      rcases hx with hx | hx | hx | hx
      · exact Or.inr (Or.inl (by addr_omega [hx, hsb]))
      · exact Or.inl (by addr_omega [hx, hsb, c₃.x2])
      · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega, hx.2⟩)))
    hnew₄.heap hn₄ (hpres₄.reg .x2) (hpres₄.reg .x8) (hpres₄.reg .x18) (preservesRegs hpres₄)
  have hf₄ : DFrame v₂ v₄ fun x ↦ Within x (s.getReg .x2 - 64) 24 ∨
      Within x (stackLo v₃ colStack) colStack ∨ Within x nextAddr 8 ∨ Fresh v₃ v₄ x :=
    ((DFrame.of_same hm₃ fun _ ↦ False).union hnew₄.frame).mono fun x hx ↦ hx.elim False.elim id
  have hB₄ := formOf_frame hf₄ hB₂.2 (fun x hx hw ↦ by
      simp only [Fresh] at hw
      rcases hw with h | h | h | h <;> addr_omega [hx, h, hsb, hab, hnx, hbhi, hhv, hn₁, hn₂, hn₃, c₃.x2])
    (fun x hx hw ↦ by
      rw [hbB₂] at hx
      have := c.buf x hx
      simp only [Fresh] at hw
      rcases hw with h | h | h | h <;> addr_omega [this, h, hsb, hab, hnx, hhv, hn₁, hn₂, hn₃, c₃.x2])
    (by addr_omega [hbhi, hhv]) hnew₂.heap (by omega)
  have hbB₄ := formBuf_frame hf₄ (e := B) (fun x hx hw ↦ by
      simp only [Fresh] at hw
      rcases hw with h | h | h | h <;> addr_omega [hx, h, hsb, hab, hnx, hbhi, hhv, hn₁, hn₂, hn₃, c₃.x2])
    (by addr_omega [hbhi, hhv])
  have h1₄ := formOf_frame hf₄ hnew₂.ok (fun x hx hw ↦ by
      simp only [Fresh] at hw
      rcases hw with h | h | h | h <;> addr_omega [hx, h, hsb, hab, hnx, hh₂, hh₄, hn₃, c₃.x2])
    (fun x hx hw ↦ by
      have := hb₂ x hx
      simp only [Fresh] at hw
      rcases hw with h | h | h | h <;> addr_omega [this, h, hsb, hab, hnx, hh₂, hn₃, c₃.x2])
    (by addr_omega [hsb]) hnew₂.heap (by omega)
  have hb1₄ := formBuf_frame hf₄ (e := s.getReg .x2 - 88) (fun x hx hw ↦ by
      simp only [Fresh] at hw
      rcases hw with h | h | h | h <;> addr_omega [hx, h, hsb, hab, hnx, hh₂, hh₄, hn₃, c₃.x2])
    (by addr_omega [hsb])
  refine ⟨v₄, hr₂.trans hr₄, Or.inl {
    toCarry := c₄
    pc := by rw [hpc₄, returnAddress_eq, b80005f10_x1 h₃]; decide
    x9 := by
      rw [hpres₄.reg .x9, k₃ .x9 (by decide), hpres₂.reg .x9, k₁ .x9 (by decide), c.x9]
    al := c.al
    blo := hblo
    bq := hbhi
    qhi := by omega
    ok := hB₄.2
    val := by rw [hB₄.1, hB₂.1, c.val]
    buf := fun x hx ↦ by rw [hbB₄, hbB₂] at hx; exact c.buf x hx
    ok1 := h1₄.2
    val1 := by rw [h1₄.1, hval₂]; rfl
    buf1 := fun x hx ↦ by rw [hb1₄] at hx; have := hb₂ x hx; omega
    ok2 := hnew₄.ok
    val2 := by rw [hval₄]; rfl
    buf2 := fun x hx ↦ by
      have hb := hnew₄.fresh
      simp only [NewBuf, formBuf, Within] at hb hx
      omega }⟩

/-- At the call to `pair`: both `Vec`s built. -/
structure AtPair (s t : MachineState) (P : Nat) : Prop extends Carry s t P where
  pc : t.pc = 0x80011b98
  x1 : t.getReg .x1 = 0x80005f74
  x10 : t.getReg .x10 = s.getReg .x10
  x11 : t.getReg .x11 = s.getReg .x2 - 112
  x12 : t.getReg .x12 = s.getReg .x2 - 64
  pre : PairPre t
  pullVal : formVecOf t (s.getReg .x2 - 64) =
    [constantRust sepStateRust, colRust 0 0, colRust 1 0]
  pullDeep : ∀ y, formVecDeep t (s.getReg .x2 - 64) y → P ≤ y.toNat ∧ y.toNat < heapNext t

/-- The moves into `B`, the second header, and `pair`'s precondition. -/
theorem toPair {s w : MachineState} {P Q : Nat} {B : Word} (hpre : StateDerivedPre s)
    (c : Cols s w P Q B) : ∃ t, Reaches Image.code w t ∧ AtPair s t P := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hselfb := ValidMemRange.bounds hpre.self (by decide)
  simp only [stateDerivedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hss
  have hhw := c.heap.hi
  have hbq := c.bq
  have hqhi := c.qhi
  have hblo := c.blo
  have hplo := c.lo
  have hBal := c.al
  simp only [heapEnd] at hhw
  have hs₀ := hpre.heap.lo
  simp only [heapStart] at hs₀
  have hBv : ValidMemRange B 9 := validMemRange_of hBal (Or.inl ⟨by omega, by omega⟩)
  obtain ⟨x, hrx, h⟩ := Sym.BlockSpec.reaches b80005f24_spec c.pc (by
    rv_eval [c.x2, c.x9]
    and_intros
    all_goals (try valid_access hpre.stack.valid [hsb])
    all_goals (try valid_access hBv [hBal, hbq, hqhi, hhw])
    all_goals addr_omega [hsb, hab, hBal, hbq, hqhi, hhw])
  have kx := b80005f24_keeps h
  have hw : ByteFrame w x fun y ↦ Within y (s.getReg .x2 - 64) 24 ∨ Within y (B + 24) 48 :=
    h.byteFrame (by
      rv_eval [c.x2, c.x9]
      and_intros <;> first
        | (intro i hi; exact Or.inl (by addr_omega [hsb, hi]))
        | (intro i hi; exact Or.inr (by addr_omega [hBal, hbq, hqhi, hhw, hi]))
        | addr_omega [hsb, hBal, hbq, hqhi, hhw])
  have hnx' : heapNext x = heapNext w := by
    have := hw.getMem_of (a := nextAddr) (fun y hy h ↦ by
      rcases h with h | h <;> addr_omega [hy, h, hsb, hnx, hbq, hqhi, hhw]) (by decide)
    simp only [heapNext, this]
  have cx := c.step hpre hw.dframe (fun y hy ↦ by
      rcases hy with hy | hy
      · exact Or.inr (Or.inl (by addr_omega [hy, hsb]))
      · exact Or.inr (Or.inr (Or.inr (by addr_omega [hy, hblo, hbq, hqhi, hnx']))))
    ⟨hnx' ▸ c.heap.lo, hnx' ▸ c.heap.hi⟩ hnx'.ge (kx .x2 (by decide)) (kx .x8 (by decide))
    (kx .x18 (by decide)) fun r hr ↦ kx r (mem_of_mem hr _)
  have hwd := hw.dframe
  -- the three forms of the second `Vec`
  have he0 := formOf_frame hwd c.ok
    (fun y hy h ↦ by rcases h with h | h <;> addr_omega [hy, h, hsb, hab, hbq, hqhi, hhw])
    (fun y hy h ↦ by
      have := c.buf y hy
      rcases h with h | h <;> addr_omega [this, h, hsb, hab, hqhi, hhw])
    (by addr_omega [hbq, hqhi, hhw]) c.heap (by omega)
  have hbuf0 := formBuf_frame hwd (e := B)
    (fun y hy h ↦ by rcases h with h | h <;> addr_omega [hy, h, hsb, hab, hbq, hqhi, hhw])
    (by addr_omega [hbq, hqhi, hhw])
  have m24 := b80005f24_m_x9_24 h
  have m32 := b80005f24_m_x9_32 h
  have m40 := b80005f24_m_x9_40 h
  have m48 := b80005f24_m_x9_48 h
  have m56 := b80005f24_m_x9_56 h
  have m64 := b80005f24_m_x9_64 h
  rw [c.x9, c.x2] at m24 m32 m40 m48 m56 m64
  rv_eval [] at m24 m32 m40 m48 m56 m64
  have hnot (y : Word) (h1 : Q ≤ y.toNat) (h2 : y.toNat < heapNext w) :
      ¬ (Within y (s.getReg .x2 - 64) 24 ∨ Within y (B + 24) 48) := by
    rintro (h | h) <;> addr_omega [h, h1, h2, hsb, hab, hbq, hhw]
  have he1 := formOf_move hwd c.ok1 (e := B + 24) m24
    (by rw [show B + 24 + 8 = B + 32 by rv_eval [],
      show s.getReg .x2 - 88 + 8 = s.getReg .x2 - 80 by rv_eval []]; exact m32)
    (by rw [show B + 24 + 16 = B + 40 by rv_eval [],
      show s.getReg .x2 - 88 + 16 = s.getReg .x2 - 72 by rv_eval []]; exact m40)
    (fun y hy ↦ hnot y (c.buf1 y hy).1 (c.buf1 y hy).2) c.heap (by omega)
  have he2 := formOf_move hwd c.ok2 (e := B + 48) m48
    (by rw [show B + 48 + 8 = B + 56 by rv_eval [],
      show s.getReg .x2 - 64 + 8 = s.getReg .x2 - 56 by rv_eval []]; exact m56)
    (by rw [show B + 48 + 16 = B + 64 by rv_eval [],
      show s.getReg .x2 - 64 + 16 = s.getReg .x2 - 48 by rv_eval []]; exact m64)
    (fun y hy ↦ hnot y (c.buf2 y hy).1 (c.buf2 y hy).2) c.heap (by omega)
  have hm0 : x.getMem (s.getReg .x2 - 64) = 3 := by
    have := b80005f24_m_x2_48 h; rw [c.x2, c.x18] at this; rv_eval [] at this; exact this
  have hm8 : x.getMem (s.getReg .x2 - 64 + 8) = B := by
    have := b80005f24_m_x2_56 h; rw [c.x2, c.x9] at this
    rw [show s.getReg .x2 - 64 + 8 = s.getReg .x2 - 112 + 56 by rv_eval []]; exact this
  have hm16 : x.getMem (s.getReg .x2 - 64 + 16) = 3 := by
    have := b80005f24_m_x2_64 h; rw [c.x2, c.x18] at this
    rw [show s.getReg .x2 - 64 + 16 = s.getReg .x2 - 112 + 64 by rv_eval []]; exact this
  have hv := formVec3 hm0 hm8 hm16 hBal (by simp only [heapStart]; omega)
    (by omega) he0.2 he1.2.1 he2.2.1 (fun y hy hw' ↦ by
      rcases hy with hy | hy | hy
      · rw [hbuf0] at hy; have := c.buf y hy; addr_omega [this, hw']
      · rw [he1.2.2] at hy; have := c.buf1 y hy; addr_omega [this, hw', hbq]
      · rw [he2.2.2] at hy; have := c.buf2 y hy; addr_omega [this, hw', hbq])
  have hbb : ∀ y, flushesBuf x (s.getReg .x10) y → y.toNat < heapNext s := fun y hy ↦ by
    rw [cx.keep.2.2.2] at hy; exact (hpre.ok.buf_below hy).2
  have hfresh : ∀ y, heapNext s ≤ y.toNat → y.toNat < heapNext x →
      ¬ (Within y (s.getReg .x10) 48 ∨ flushesBuf x (s.getReg .x10) y) := by
    intro y h1 h2 hy
    rcases hy with hy | hy
    · addr_omega [hy, h1, h2, hsf, hhw, hnx']
    · have := hbb y hy; omega
  have hpull : ∀ y, formVecDeep x (s.getReg .x2 - 64) y → P ≤ y.toNat ∧ y.toNat < heapNext x := by
    intro y hy
    rcases hv.2.2 y hy with h | h | h | h
    · simp only [Within] at h; omega
    · rw [hbuf0] at h; have := c.buf y h; omega
    · rw [he1.2.2] at h; have := c.buf1 y h; omega
    · rw [he2.2.2] at h; have := c.buf2 y h; omega
  have x2x := cx.x2
  have hx10 : x.getReg .x10 = s.getReg .x10 := by rw [b80005f24_x10 h, c.x8]
  have hx11 : x.getReg .x11 = s.getReg .x2 - 112 := by rw [b80005f24_x11 h, c.x2]
  have hx12 : x.getReg .x12 = s.getReg .x2 - 64 := by rw [b80005f24_x12 h, c.x2]; rv_eval []
  refine ⟨x, hrx, {
    toCarry := cx
    pc := b80005f24_pc h
    x1 := b80005f24_x1 h
    x10 := hx10
    x11 := hx11
    x12 := hx12
    pre := ?_
    pullVal := by rw [hv.2.1, he0.1, c.val, he1.1, c.val1, he2.1, c.val2]
    pullDeep := hpull }⟩
  exact {
    heap := cx.heap
    stack := hpre.stack.inner (k := 112) x2x (by decide) (by decide) (by decide) (by decide)
      (by decide)
    self := by rw [hx10]; exact hpre.self
    ok := by rw [hx10]; exact cx.keep.2.1
    push := by rw [hx11]; valid_sub hpre.stack.valid [hsb]
    pull := by rw [hx12]; valid_sub hpre.stack.valid [hsb]
    pushOk := by rw [hx11]; exact cx.push
    pullOk := by rw [hx12]; exact hv.1
    selfFree := by rw [hx10]; have := cx.hi; addr_omega [hsf, hplo, this]
    pushFree := by rw [hx11]; addr_omega [hsb, hab, hnx]
    pullFree := by rw [hx12]; addr_omega [hsb, hab, hnx]
    selfStack := by rw [hx10]; addr_omega [hss, hsb, x2x]
    pushStack := by rw [hx11]; addr_omega [hsb, x2x]
    pullStack := by rw [hx12]; addr_omega [hsb, x2x]
    apart := fun y hy hw' ↦ by
      rw [hx11, hx12] at hy
      rw [hx10] at hw'
      rcases hy with hy | hy | hy | hy
      · rcases hw' with h | h
        · addr_omega [hy, h, hss, hsb]
        · have h1 := hbb y h; have h2 := hpre.heap.hi; addr_omega [hy, h1, h2, hsb, hab]
      · rcases cx.pushDeep y hy with h | h | h
        · exact hfresh y h.1 (by have := cx.hi; omega) hw'
        · exact hpre.apart y (Or.inr (Or.inl h)) (by rwa [cx.keep.2.2.2] at hw')
        · exact hpre.apart y (Or.inr (Or.inr (Or.inr h))) (by rwa [cx.keep.2.2.2] at hw')
      · rcases hw' with h | h
        · addr_omega [hy, h, hss, hsb]
        · have h1 := hbb y h; have h2 := hpre.heap.hi; addr_omega [hy, h1, h2, hsb, hab]
      · exact hfresh y (by have := (hpull y hy).1; omega) (hpull y hy).2 hw' }

/-- What `pair` and the epilogue leave, from the call at `x` to `z`. -/
theorem finish {s x y z : MachineState} {P : Nat} (hpre : StateDerivedPre s) (X : AtPair s x P)
    (Y : PairPost x y) (hz : ∀ a, z.getMem a = y.getMem a) :
    GrowFlushes s z (s.getReg .x10) stateDerivedStack
        (fun q ↦ formBuf s (s.getReg .x11) q ∨ formBuf s (s.getReg .x12) q) ∧
      flushesOf z (s.getReg .x10) = (flushesOf s (s.getReg .x10)).stateDerived 0 1
        (formOf s (s.getReg .x11)) (formOf s (s.getReg .x12)) := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hselfb := ValidMemRange.bounds hpre.self (by decide)
  simp only [stateDerivedStack, colStack, powStack, Contracts.mulStack, Nat.reduceAdd] at hsb
  have hval := Y.value
  have hdeep := Y.deep
  have hfr := Y.frame
  rw [X.x10, X.x11, X.x12] at hval hdeep
  rw [X.x10, X.keep.2.2.2] at hfr
  have Yok := Y.ok
  rw [X.x10] at Yok
  have hn : heapNext z = heapNext y := by simp only [heapNext, hz]
  have hfin := flushesOf_frame (DFrame.of_same hz fun _ ↦ False) Yok (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) (by addr_omega [hselfb]) Y.heap hn.ge
  have hm := Y.mono
  have hlo := X.lo
  have hhi := X.hi
  refine ⟨{
    heap := ⟨hn ▸ Y.heap.lo, hn ▸ Y.heap.hi⟩
    mono := by omega
    ok := hfin.2.1
    deep := fun q hq ↦ by
      rw [hfin.2.2.1] at hq
      rcases hdeep q hq with h | h | h | h
      · rw [X.keep.2.2.1] at h; exact Or.inl h
      · rcases X.pushDeep q h with h | h | h
        · simp only [Fresh]; exact Or.inr (Or.inr ⟨h.1, by omega⟩)
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inl (Or.inr h))
      · have := X.pullDeep q h
        simp only [Fresh]; exact Or.inr (Or.inr ⟨by omega, by omega⟩)
      · simp only [Fresh] at h ⊢; exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    frame := ((X.frame.union hfr).union (DFrame.of_same hz fun _ ↦ False)).mono fun q hq ↦ by
      simp only [Scratch] at hq
      rcases hq with ((hq | hq | hq) | hq | hq | hq | hq | hq) | hq
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [hq, hsb])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
      · simp only [Fresh] at hq ⊢; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hq.1, by omega⟩)))
      · exact Or.inl hq
      · exact Or.inr (Or.inl hq)
      · exact Or.inr (Or.inr (Or.inl (by addr_omega [hq, hsb, X.x2])))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hq)))
      · simp only [Fresh] at hq ⊢; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
      · exact hq.elim }, ?_⟩
  rw [hfin.1, hval, X.keep.1, X.pushVal, X.pullVal]
  rfl

/-- **`Flushes::state_derived` meets its contract**, given `alloc`'s, `Form::term`'s, `col`'s and
`Flushes::pair`'s. -/
theorem state_derived_spec (hA : AllocSpec) (hT : TermSpec) (hC : ColSpec) (hP : PairSpec) :
    StateDerivedSpec := by
  intro s hpc hpre
  obtain ⟨u, hru, U | hdead⟩ := pushPhase hA hT hpc hpre
  swap
  · exact ⟨u, hru, Or.inr hdead⟩
  obtain ⟨v, B, hrv, V | hdead⟩ := headPhase hA hT hpre U
  swap
  · exact ⟨v, hru.trans hrv, Or.inr hdead⟩
  obtain ⟨w, hrw, W | hdead⟩ := colsPhase hC hpre V
  swap
  · exact ⟨w, hru.trans (hrv.trans hrw), Or.inr hdead⟩
  obtain ⟨x, hrx, X⟩ := toPair hpre W
  obtain ⟨y, hry, ⟨hpcy, hpresy, Y⟩ | hdead⟩ := hP.call hrx X.pc X.pre
  swap
  · exact ⟨y, hru.trans (hrv.trans (hrw.trans hry)), Or.inr hdead⟩
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hss := hpre.selfStack
  simp only [stateDerivedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hss
  have x2y : y.getReg .x2 = s.getReg .x2 - 112 := (hpresy.reg .x2).trans X.x2
  obtain ⟨z, hrz, hz⟩ := Sym.BlockSpec.reaches b80005f74_spec
    (by rw [hpcy, returnAddress_eq, X.x1]; decide) (by
      rv_eval [x2y]
      and_intros <;> valid_access hpre.stack.valid [hsb])
  have hfr := Y.frame
  rw [X.x10, X.keep.2.2.2] at hfr
  have hhy := Y.heap.hi
  have hsave (a : Word) (ha₁ : (s.getReg .x2).toNat - 40 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : y.getMem a = x.getMem a := by
    refine hfr.getMem_of (fun q hq hw ↦ ?_) (by addr_omega [hsb, ha₂])
    rcases hw with hw | hw | hw | hw | hw
    · addr_omega [hq, hw, hss, hsb, ha₁, ha₂]
    · have h1 := (hpre.ok.buf_below hw).2
      have h2 := hpre.heap.hi
      addr_omega [hq, h1, h2, hsb, hab, ha₁, ha₂]
    · addr_omega [hq, hw, hsb, X.x2, ha₁, ha₂]
    · addr_omega [hq, hw, hnx, hsb, ha₁, ha₂]
    · simp only [Fresh] at hw; addr_omega [hq, hw, hhy, hab, hsb, ha₁, ha₂]
  have pcz := b80005f74_pc hz
  have r₁ := b80005f74_x1 hz
  have r₂ := b80005f74_x2 hz
  have r₈ := b80005f74_x8 hz
  have r₉ := b80005f74_x9 hz
  have r₁₈ := b80005f74_x18 hz
  have r₁₉ := b80005f74_x19 hz
  have kz := b80005f74_keeps hz
  rw [x2y] at pcz r₁ r₂ r₈ r₉ r₁₈ r₁₉
  rv_eval [] at pcz r₁ r₂ r₈ r₉ r₁₈ r₁₉
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), X.ra] at pcz r₁
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), X.s0] at r₈
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), X.s1] at r₉
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), X.s2] at r₁₈
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), X.s3] at r₁₉
  refine ⟨z, hru.trans (hrv.trans (hrw.trans (hry.trans hrz))), Or.inl ⟨
    pcz.trans (returnAddress_eq s).symm, preserves_of r₂ r₈ r₉ r₁₈ r₁₉ fun r hr ↦ ?_,
    finish hpre X Y (b80005f74_mem_same hz)⟩⟩
  rw [kz r (mem_of_mem hr _), hpresy r (mem_of_mem hr _), X.regs r hr]

end Rv64Verifier.Layout.StateDerived
