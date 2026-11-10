import Rv64Verifier.Proofs.Layout.Keep
import Rv64Verifier.Proofs.Layout.ContractsFlushes
import Rv64Verifier.Blocks.F16

/-!
# `Flushes::memory`, at `0x800051b0`

```rust
fn memory(&mut self, address: Form, count: usize, values: &[Form; 3]) {
    self.counted(&[constant(SEP_MEM), address], col(count, 1), count, values);
}
```

compiled (`Blocks/F16.lean`), `sp'` the entry's `sp - 112`: `0x800051b0` saves `ra`, `s0`..`s3`
and calls `term(sp', One, GEN)`; `0x800051f4` moves the address to `sp' + 24` and calls
`col(sp' + 48, count, 1)`; `0x80005220` calls `counted(self, sp', sp' + 48, count, values, 3)`;
`0x80005240` restores and returns.
-/

namespace Rv64Verifier.Layout.Memory
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F16 Rv64Verifier.Model.LayoutMirror

/-- The state at the call to `counted`. -/
structure AtCall (s t : MachineState) : Prop where
  pc : t.pc = 0x8000525c
  ra : t.getReg .x1 = 0x80005240
  x2 : t.getReg .x2 = s.getReg .x2 - 112
  x10 : t.getReg .x10 = s.getReg .x10
  x11 : t.getReg .x11 = s.getReg .x2 - 112
  x12 : t.getReg .x12 = s.getReg .x2 - 64
  x13 : t.getReg .x13 = s.getReg .x12
  x14 : t.getReg .x14 = s.getReg .x13
  x15 : t.getReg .x15 = 3
  regs : ∀ r ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27], t.getReg r = s.getReg r
  s0 : t.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s1 : t.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s2 : t.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s3 : t.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s4 : t.getMem (s.getReg .x2 - 40) = s.getReg .x19
  pre : CountedPre t
  frame : DFrame s t (Scratch s t (stackLo s 1504) 1504)
  mono : heapNext s ≤ heapNext t
  keep : flushesOf t (s.getReg .x10) = flushesOf s (s.getReg .x10) ∧
    flushesDeep t (s.getReg .x10) = flushesDeep s (s.getReg .x10) ∧
    flushesBuf t (s.getReg .x10) = flushesBuf s (s.getReg .x10)
  pre2 : formsAt t (s.getReg .x2 - 112) 2 = [constantRust sepMemRust, formOf s (s.getReg .x11)]
  counter : formOf t (s.getReg .x2 - 64) = colRust (s.getReg .x12).toNat 1
  values : formsAt t (s.getReg .x13) 3 = formsAt s (s.getReg .x13) 3

/-- At the call to `col`: `term`'s form at `sp'`, the address's header at `sp' + 24`. -/
structure Head (s t : MachineState) : Prop where
  pc : t.pc = 0x80004b34
  ra : t.getReg .x1 = 0x80005220
  x2 : t.getReg .x2 = s.getReg .x2 - 112
  x8 : t.getReg .x8 = s.getReg .x13
  x9 : t.getReg .x9 = s.getReg .x12
  x10 : t.getReg .x10 = s.getReg .x2 - 64
  x11 : t.getReg .x11 = s.getReg .x12
  x12 : t.getReg .x12 = 1
  x19 : t.getReg .x19 = s.getReg .x10
  regs : ∀ r ∈ [Reg.x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27], t.getReg r = s.getReg r
  s0 : t.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s1 : t.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s2 : t.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s3 : t.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s4 : t.getMem (s.getReg .x2 - 40) = s.getReg .x19
  heap : HeapOk t
  mono : heapNext s ≤ heapNext t
  frame : DFrame s t (Scratch s t (stackLo s 1504) 1504)
  rodata : RodataOk t
  tOk : FormOk t (s.getReg .x2 - 112)
  tVal : formOf t (s.getReg .x2 - 112) = constantRust sepMemRust
  tBuf : ∀ x, formBuf t (s.getReg .x2 - 112) x → heapNext s ≤ x.toNat ∧ x.toNat < heapNext t
  aOk : FormOk t (s.getReg .x2 - 88)
  aVal : formOf t (s.getReg .x2 - 88) = formOf s (s.getReg .x11)
  aBuf : formBuf t (s.getReg .x2 - 88) = formBuf s (s.getReg .x11)

/-- `term(sp', One, GEN)` and the address's move. -/
theorem head (hT : TermSpec) {s : MachineState} (hpc : s.pc = 0x800051b0)
    (hpre : MemoryPre s) : ∃ t, Reaches Image.code s t ∧ (Head s t ∨ Dead Image.code t) := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hro := hpre.stack.rodata
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have has := hpre.addressStack
  have haf := hpre.addressFree
  have hab' := ValidMemRange.bounds hpre.address (by decide)
  have hvs := hpre.valuesStack
  have hvf := hpre.valuesFree
  have hvb := ValidMemRange.bounds hpre.values (by decide)
  have hheap := hpre.heap
  have hhs := hheap.hi
  simp only [memoryStack, countedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hro hss has hvs
  -- the frame, and `term(sp', One, GEN)`
  obtain ⟨t₁, hr₁, h₁⟩ := Sym.BlockSpec.reaches b800051b0_spec hpc (by
    rv_eval []
    and_intros <;> valid_access hpre.stack.valid [hsb])
  have k₁ := b800051b0_keeps h₁
  have hm₁ := b800051b0_frame h₁ (by addr_omega [hsb])
  have x2₁ := b800051b0_x2 h₁
  have hn₁ : heapNext t₁ = heapNext s := by
    simp only [heapNext]; rw [hm₁ _ (by addr_omega [hnx, hsb])]
  have tag₁ : t₁.getMem (s.getReg .x2 - 64) = 0 := b800051b0_m_x2_n64 h₁
  have hrod₁ : RodataOk t₁ := hpre.rodata.frame hm₁ (by addr_omega [hsb, hro])
  have hterm : TermPre t₁ := {
    heap := ⟨hn₁ ▸ hheap.lo, hn₁ ▸ hhs⟩
    stack := hpre.stack.inner (k := 112) x2₁ (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [b800051b0_x10 h₁]; valid_sub hpre.stack.valid [hsb]
    mono := by rw [b800051b0_x11 h₁]; valid_sub hpre.stack.valid [hsb]
    coeff := by
      rw [b800051b0_x12 h₁]; exact validMemRange_of (by decide) (Or.inr ⟨by decide, by decide⟩)
    monoOk := by rw [b800051b0_x11 h₁]; simp only [MonoOk, tag₁]; decide
    outFree := by rw [b800051b0_x10 h₁]; addr_omega [hsb, hab, hnx]
    monoNext := by rw [b800051b0_x11 h₁]; addr_omega [hsb, hnx]
    coeffNext := by rw [b800051b0_x12 h₁]; addr_omega []
    outStack := by rw [b800051b0_x10 h₁]; addr_omega [hsb, x2₁]
    monoStack := by rw [b800051b0_x11 h₁]; addr_omega [hsb, x2₁]
    coeffStack := by rw [b800051b0_x12 h₁]; addr_omega [hsb, x2₁, hro] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hnew₂, hval₂⟩ | hdead⟩ := hT.call hr₁ (b800051b0_pc h₁) hterm
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  rw [b800051b0_x10 h₁, b800051b0_x11 h₁, b800051b0_x12 h₁] at hval₂
  rw [b800051b0_x10 h₁] at hnew₂
  have hv₂ : formOf t₂ (s.getReg .x2 - 112) = constantRust sepMemRust := by
    rw [hval₂, eAt_gen hrod₁, monoOf, tag₁]; rfl
  have x2₂ : t₂.getReg .x2 = s.getReg .x2 - 112 := (hpres₂.reg .x2).trans x2₁
  have x18₂ : t₂.getReg .x18 = s.getReg .x11 := by
    rw [hpres₂.reg .x18, b800051b0_x18 h₁]
  have hn₂ := hnew₂.mono
  have hh₂ := hnew₂.heap.hi
  have hf₂ : DFrame t₁ t₂ (Scratch t₁ t₂ (stackLo s 1504) 1464) :=
    hnew₂.frame.mono fun x hx ↦ by
      rcases hx with hx | hx | hx | hx
      · exact Or.inl (by addr_omega [hx, hsb])
      · exact Or.inl (by addr_omega [hx, hsb, x2₁])
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
  -- the address's header, read at `t₂`, is the entry's
  have hkeepA (a : Word) (ha₁ : (s.getReg .x11).toNat ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x11).toNat + 24) : t₂.getMem a = s.getMem a := by
    rw [hf₂.getMem_of (fun x hx hw ↦ ?_) (by addr_omega [hab', ha₂]),
      hm₁ a (by addr_omega [has, hsb, hab', ha₁, ha₂])]
    simp only [Scratch, Fresh] at hw
    have hf1 := haf.1
    rcases hw with hw | hw | hw <;> addr_omega [hx, hw, has, hf1, haf.2, hsb, hn₁, hh₂, ha₁, ha₂,
      hab']
  -- the move
  obtain ⟨t₃, hr₃, h₃⟩ := Sym.BlockSpec.reaches b800051f4_spec
    (by rw [hpc₂, returnAddress_eq, b800051b0_x1 h₁]; decide) (by
      rv_eval [x2₂, x18₂]
      and_intros
      all_goals (try valid_access hpre.stack.valid [hsb])
      all_goals valid_access hpre.address [hab'])
  have k₃ := b800051f4_keeps h₃
  have hm₃ := b800051f4_frame h₃ (by addr_omega [hsb, x2₂])
  rw [x2₂] at hm₃
  have hn₃ : heapNext t₃ = heapNext t₂ := by
    simp only [heapNext]; rw [hm₃ _ (by addr_omega [hnx, hsb])]
  have x2₃ : t₃.getReg .x2 = s.getReg .x2 - 112 := (k₃ .x2 (by decide)).trans x2₂
  have hf₁₃ : DFrame s t₃ (Scratch s t₃ (stackLo s 1504) 1504) :=
    ((hm₁.dframe.union hf₂).union hm₃.dframe).mono fun x hx ↦ by
      simp only [Scratch, Fresh] at hx ⊢
      rcases hx with (hx | hx | hx | hx) | hx
      · exact Or.inl (by addr_omega [hx, hsb])
      · exact Or.inl (by addr_omega [hx, hsb])
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
      · exact Or.inl (by addr_omega [hx, hsb])
  have hA₃ := formOf_move hf₁₃ hpre.addressOk (e := s.getReg .x2 - 88)
    (by have := b800051f4_m_x2_24 h₃; rw [x2₂, x18₂] at this; rv_eval [] at this
        rw [this, hkeepA _ (by addr_omega [hab']) (by addr_omega [hab'])])
    (by have := b800051f4_m_x2_32 h₃; rw [x2₂, x18₂] at this; rv_eval [] at this
        rw [show s.getReg .x2 - 88 + 8 = s.getReg .x2 - 80 by rv_eval [], this,
          hkeepA _ (by addr_omega [hab']) (by addr_omega [hab'])])
    (by have := b800051f4_m_x2_40 h₃; rw [x2₂, x18₂] at this; rv_eval [] at this
        rw [show s.getReg .x2 - 88 + 16 = s.getReg .x2 - 72 by rv_eval [], this,
          hkeepA _ (by addr_omega [hab']) (by addr_omega [hab'])])
    (fun x hx ↦ not_scratch hab hhs (hpre.addressOk.buf_below hx).2) hheap (by omega)
  have hT₃ := formOf_frame hm₃.dframe hnew₂.ok (fun x hx hw ↦ by addr_omega [hx, hw, hsb])
    (fun x hx hw ↦ by
      have := (hnew₂.ok.buf_below hx).2
      addr_omega [this, hw, hsb, hab, hh₂]) (by addr_omega [hsb]) hnew₂.heap hn₃.ge
  have hTb := formBuf_frame hm₃.dframe (e := s.getReg .x2 - 112)
    (fun x hx hw ↦ by addr_omega [hx, hw, hsb]) (by addr_omega [hsb])
  have hslot (a : Word) (ha₁ : (s.getReg .x2).toNat - 40 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : t₃.getMem a = t₁.getMem a := by
    rw [hm₃ a (by addr_omega [hsb, ha₁, ha₂]), hf₂.getMem_of (fun x hx hw ↦ ?_)
      (by addr_omega [hsb, ha₂])]
    simp only [Scratch, Fresh] at hw
    rcases hw with hw | hw | hw <;> addr_omega [hx, hw, hsb, hnx, hab, hh₂, ha₁, ha₂]
  refine ⟨t₃, hr₂.trans hr₃, Or.inl {
    pc := b800051f4_pc h₃
    ra := b800051f4_x1 h₃
    x2 := x2₃
    x8 := by rw [k₃ .x8 (by decide), hpres₂.reg .x8, b800051b0_x8 h₁]
    x9 := by rw [k₃ .x9 (by decide), hpres₂.reg .x9, b800051b0_x9 h₁]
    x10 := by rw [b800051f4_x10 h₃, x2₂]; rv_eval []
    x11 := by rw [b800051f4_x11 h₃, hpres₂.reg .x9, b800051b0_x9 h₁]
    x12 := b800051f4_x12 h₃
    x19 := by rw [k₃ .x19 (by decide), hpres₂.reg .x19, b800051b0_x19 h₁]
    regs := fun r hr ↦ by
      rw [k₃ r (mem_of_mem hr _), hpres₂ r (mem_of_mem hr _), k₁ r (mem_of_mem hr _)]
    s0 := by rw [hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])]; exact b800051b0_m_x2_n8 h₁
    s1 := by rw [hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])]; exact b800051b0_m_x2_n16 h₁
    s2 := by rw [hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])]; exact b800051b0_m_x2_n24 h₁
    s3 := by rw [hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])]; exact b800051b0_m_x2_n32 h₁
    s4 := by rw [hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])]; exact b800051b0_m_x2_n40 h₁
    heap := ⟨hn₃ ▸ hnew₂.heap.lo, hn₃ ▸ hh₂⟩
    mono := by omega
    frame := hf₁₃
    rodata := RodataOk.dframe hpre.rodata hf₁₃ fun x hx ↦
      not_rodata_of_scratch hro (by rw [hn₃]; exact hh₂) hx
    tOk := hT₃.2
    tVal := hT₃.1.trans hv₂
    tBuf := fun x hx ↦ by
      rw [hTb] at hx
      have hb := hnew₂.fresh
      simp only [NewBuf, formBuf, Within] at hb hx
      omega
    aOk := hA₃.2.1
    aVal := hA₃.1
    aBuf := hA₃.2.2 }⟩

/-- `col(sp' + 48, count, 1)`, and `counted`'s precondition. -/
theorem toCall (hT : TermSpec) (hC : ColSpec) {s : MachineState} (hpc : s.pc = 0x800051b0)
    (hpre : MemoryPre s) : ∃ t, Reaches Image.code s t ∧ (AtCall s t ∨ Dead Image.code t) := by
  obtain ⟨t₃, hr₃, H | hdead⟩ := head hT hpc hpre
  swap
  · exact ⟨t₃, hr₃, Or.inr hdead⟩
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hro := hpre.stack.rodata
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hvs := hpre.valuesStack
  have hvf := hpre.valuesFree
  have hvb := ValidMemRange.bounds hpre.values (by decide)
  have hheap := hpre.heap
  have hhs := hheap.hi
  simp only [memoryStack, countedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hro hss hvs
  have x2₃ := H.x2
  have x10₃ := H.x10
  have hh₃ := H.heap.hi
  have hm₃ := H.mono
  have hcol : ColPre t₃ := {
    heap := H.heap
    stack := hpre.stack.inner (k := 112) x2₃ (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [x10₃]; valid_sub hpre.stack.valid [hsb]
    outFree := by rw [x10₃]; addr_omega [hsb, hab, hnx]
    outStack := by rw [x10₃]; addr_omega [hsb, x2₃]
    rodata := H.rodata }
  obtain ⟨t₄, hr₄, ⟨hpc₄, hpres₄, hnew₄, hval₄⟩ | hdead⟩ := hC.call hr₃ H.pc hcol
  swap
  · exact ⟨t₄, hr₄, Or.inr hdead⟩
  rw [x10₃, H.x11, H.x12] at hval₄
  rw [x10₃] at hnew₄
  have hn₄ := hnew₄.mono
  have hh₄ := hnew₄.heap.hi
  obtain ⟨t₅, hr₅, h₅⟩ := Sym.BlockSpec.reaches b80005220_spec
    (by rw [hpc₄, returnAddress_eq, H.ra]; decide) trivial
  have k₅ := b80005220_keeps h₅
  have hm₅ := b80005220_mem_same h₅
  have hcnt := hnew₄.same hm₅ (by addr_omega [hsb])
  have hn₅ : heapNext t₅ = heapNext t₄ := by simp only [heapNext, hm₅]
  have x2₅ : t₅.getReg .x2 = s.getReg .x2 - 112 := by
    rw [k₅ .x2 (by decide), hpres₄.reg .x2, x2₃]
  have hf₃₅ : DFrame t₃ t₅ (Scratch t₃ t₅ (stackLo s 1504) 1464) :=
    hcnt.1.frame.mono fun x hx ↦ by
      rcases hx with hx | hx | hx | hx
      · exact Or.inl (by addr_omega [hx, hsb])
      · exact Or.inl (by addr_omega [hx, hsb, x2₃])
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)
  have hf₅ : DFrame s t₅ (Scratch s t₅ (stackLo s 1504) 1504) :=
    H.frame.scratch_trans (hf₃₅.mono fun x hx ↦ by
      simp only [Scratch] at hx ⊢
      rcases hx with hx | hx | hx
      · exact Or.inl (by addr_omega [hx, hsb])
      · exact Or.inr (Or.inl hx)
      · exact Or.inr (Or.inr hx)) (by omega) (by omega)
  have hmono₅ : heapNext s ≤ heapNext t₅ := by omega
  have hh₅ : heapNext t₅ ≤ heapEnd := by omega
  have hslot (a : Word) (ha₁ : (s.getReg .x2).toNat - 40 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : t₅.getMem a = t₃.getMem a := by
    refine hf₃₅.getMem_of (fun x hx hw ↦ ?_) (by addr_omega [hsb, ha₂])
    simp only [Scratch, Fresh] at hw
    rcases hw with hw | hw | hw <;> addr_omega [hx, hw, hsb, hnx, hab, hh₅, ha₁, ha₂]
  -- the three forms at the call
  have hT₅ := formOf_frame hcnt.1.frame H.tOk
    (fun x hx hw ↦ by
      simp only [Fresh] at hw
      rcases hw with hw | hw | hw | hw <;> addr_omega [hx, hw, hsb, hab, hnx, x2₃, hh₅])
    (fun x hx hw ↦ by
      have := H.tBuf x hx
      simp only [Fresh] at hw
      rcases hw with hw | hw | hw | hw <;> addr_omega [this, hw, hsb, hab, hnx, x2₃, hh₃])
    (by addr_omega [hsb]) H.heap (by omega)
  have hA₅ := formOf_frame hcnt.1.frame H.aOk
    (fun x hx hw ↦ by
      simp only [Fresh] at hw
      rcases hw with hw | hw | hw | hw <;> addr_omega [hx, hw, hsb, hab, hnx, x2₃, hh₅])
    (fun x hx hw ↦ by
      rw [H.aBuf] at hx
      have := (hpre.addressOk.buf_below hx).2
      simp only [Fresh] at hw
      rcases hw with hw | hw | hw | hw <;> addr_omega [this, hw, hsb, hab, hnx, x2₃, hhs, hm₃])
    (by addr_omega [hsb]) H.heap (by omega)
  have hV := formsAt_keep hf₅ hpre.valuesOk hheap hmono₅ hh₅ hab hvf hvs (by addr_omega [hvb])
  have hkeep := flushesOf_keep hf₅ hpre.ok hheap hmono₅ hh₅ hab hsf hss
    (by have := ValidMemRange.bounds hpre.self (by decide); addr_omega [this])
  have e0 : s.getReg .x2 - 112 + BitVec.ofNat 64 (24 * 0) = s.getReg .x2 - 112 := by
    addr_omega [hsb]
  have e1 : s.getReg .x2 - 112 + BitVec.ofNat 64 (24 * 1) = s.getReg .x2 - 88 := by
    addr_omega [hsb]
  have x10₅ : t₅.getReg .x10 = s.getReg .x10 := by
    rw [b80005220_x10 h₅, hpres₄.reg .x19, H.x19]
  have x11₅ : t₅.getReg .x11 = s.getReg .x2 - 112 := by rw [b80005220_x11 h₅, hpres₄.reg .x2, x2₃]
  have x12₅ : t₅.getReg .x12 = s.getReg .x2 - 64 := by
    rw [b80005220_x12 h₅, hpres₄.reg .x2, x2₃]; rv_eval []
  have x13₅ : t₅.getReg .x13 = s.getReg .x12 := by rw [b80005220_x13 h₅, hpres₄.reg .x9, H.x9]
  have x14₅ : t₅.getReg .x14 = s.getReg .x13 := by rw [b80005220_x14 h₅, hpres₄.reg .x8, H.x8]
  have x15₅ := b80005220_x15 h₅
  have hcp : CountedPre t₅ := {
    heap := hcnt.1.heap
    stack := hpre.stack.inner (k := 112) x2₅ (by decide) (by decide) (by decide) (by decide)
      (by decide)
    self := by rw [x10₅]; exact hpre.self
    ok := by rw [x10₅]; exact hkeep.2.1
    selfFree := by rw [x10₅]; addr_omega [hsf, hmono₅]
    selfStack := by rw [x10₅]; addr_omega [hss, hsb, x2₅]
    rodata := RodataOk.dframe hpre.rodata hf₅ fun x hx ↦ not_rodata_of_scratch hro hh₅ hx
    pre := by rw [x11₅]; valid_sub hpre.stack.valid [hsb]
    preOk := by
      rw [x11₅]
      intro i hi
      match i, hi with
      | 0, _ => rw [e0]; exact hT₅.2
      | 1, _ => rw [e1]; exact hA₅.2
    preFree := by rw [x11₅]; addr_omega [hsb, hab, hnx]
    preStack := by rw [x11₅]; addr_omega [hsb, x2₅]
    counter := by rw [x12₅]; valid_sub hpre.stack.valid [hsb]
    counterOk := by rw [x12₅]; exact hcnt.1.ok
    counterFree := by rw [x12₅]; addr_omega [hsb, hab, hnx]
    counterStack := by rw [x12₅]; addr_omega [hsb, x2₅]
    suf := by rw [x14₅, x15₅]; exact hpre.values
    sufOk := by rw [x14₅, x15₅]; exact hV.2.1
    sufFree := by rw [x14₅, x15₅]; addr_omega [hvf, hmono₅]
    sufStack := by rw [x14₅, x15₅]; addr_omega [hvs, hsb, x2₅, hvb] }
  refine ⟨t₅, hr₄.trans hr₅, Or.inl {
    pc := b80005220_pc h₅
    ra := b80005220_x1 h₅
    x2 := x2₅
    x10 := x10₅
    x11 := x11₅
    x12 := x12₅
    x13 := x13₅
    x14 := x14₅
    x15 := x15₅
    regs := fun r hr ↦ by
      rw [k₅ r (mem_of_mem hr _), hpres₄ r (mem_of_mem hr _), H.regs r hr]
    s0 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans H.s0
    s1 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans H.s1
    s2 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans H.s2
    s3 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans H.s3
    s4 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans H.s4
    pre := hcp
    frame := hf₅
    mono := hmono₅
    keep := ⟨hkeep.1, hkeep.2.2.1, hkeep.2.2.2⟩
    pre2 := by
      show [formOf t₅ (s.getReg .x2 - 112 + BitVec.ofNat 64 (24 * 0)),
        formOf t₅ (s.getReg .x2 - 112 + BitVec.ofNat 64 (24 * 1))] = _
      rw [e0, e1, hT₅.1, H.tVal, hA₅.1, H.aVal]
    counter := by rw [hcnt.2, hval₄]; rfl
    values := hV.1 }⟩

/-- **`Flushes::memory` meets its contract**, given `Form::term`'s, `col`'s and `counted`'s. -/
theorem memory_spec (hT : TermSpec) (hC : ColSpec) (hK : CountedSpec) : MemorySpec := by
  intro s hpc hpre
  obtain ⟨t₅, hr₅, A | hdead⟩ := toCall hT hC hpc hpre
  swap
  · exact ⟨t₅, hr₅, Or.inr hdead⟩
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hss := hpre.selfStack
  have hselfb := ValidMemRange.bounds hpre.self (by decide)
  simp only [memoryStack, countedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hss
  have hh₅ := A.pre.heap.hi
  have hm₅ := A.mono
  have hbb : ∀ x, flushesBuf s (s.getReg .x10) x → x.toNat < heapNext s := fun x h ↦
    (hpre.ok.buf_below h).2
  obtain ⟨t₆, hr₆, ⟨hpc₆, hpres₆, hgrow₆, hval₆⟩ | hdead⟩ := hK.call hr₅ A.pc A.pre
  swap
  · exact ⟨t₆, hr₆, Or.inr hdead⟩
  rw [A.x10, A.x11, A.x12, A.x13, A.x14, A.x15] at hval₆
  rw [A.x10] at hgrow₆
  have x2₆ : t₆.getReg .x2 = s.getReg .x2 - 112 := (hpres₆.reg .x2).trans A.x2
  obtain ⟨t₇, hr₇, h₇⟩ := Sym.BlockSpec.reaches b80005240_spec
    (by rw [hpc₆, returnAddress_eq, A.ra]; decide) (by
      rv_eval [x2₆]
      and_intros <;> valid_access hpre.stack.valid [hsb])
  have hm₇ := b80005240_mem_same h₇
  have hn₆ := hgrow₆.mono
  have hh₆ := hgrow₆.heap.hi
  have hg₆ := hgrow₆.frame
  rw [A.keep.2.2] at hg₆
  have hsave (a : Word) (ha₁ : (s.getReg .x2).toNat - 40 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : t₆.getMem a = t₅.getMem a := by
    refine hg₆.getMem_of (fun x hx hw ↦ ?_) (by addr_omega [hsb, ha₂])
    rcases hw with hw | hw | hw | hw | hw
    · addr_omega [hx, hw, hss, hsb, ha₁, ha₂]
    · have h1 := hbb x hw; have h2 := hpre.heap.hi; addr_omega [hx, h1, h2, hsb, hab, ha₁, ha₂]
    · addr_omega [hx, hw, hsb, A.x2, ha₁, ha₂]
    · addr_omega [hx, hw, hnx, hsb, ha₁, ha₂]
    · simp only [Fresh] at hw; addr_omega [hx, hw, hh₆, hab, hsb, ha₁, ha₂]
  have pc₇ := b80005240_pc h₇
  have r₁ := b80005240_x1 h₇
  have r₂ := b80005240_x2 h₇
  have r₈ := b80005240_x8 h₇
  have r₉ := b80005240_x9 h₇
  have r₁₈ := b80005240_x18 h₇
  have r₁₉ := b80005240_x19 h₇
  have k₇ := b80005240_keeps h₇
  rw [x2₆] at pc₇ r₁ r₂ r₈ r₉ r₁₈ r₁₉
  rv_eval [] at pc₇ r₁ r₂ r₈ r₉ r₁₈ r₁₉
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), A.s0] at pc₇ r₁
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), A.s1] at r₈
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), A.s2] at r₉
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), A.s3] at r₁₈
  rw [hsave _ (by addr_omega [hsb]) (by addr_omega [hsb]), A.s4] at r₁₉
  have hn₇ : heapNext t₇ = heapNext t₆ := by simp only [heapNext, hm₇]
  have hfin := flushesOf_frame (DFrame.of_same hm₇ fun _ ↦ False) hgrow₆.ok (fun _ _ h ↦ h)
    (fun _ _ h ↦ h) (by addr_omega [hselfb]) hgrow₆.heap hn₇.ge
  refine ⟨t₇, hr₆.trans hr₇, Or.inl ⟨pc₇.trans (returnAddress_eq s).symm,
    preserves_of r₂ r₈ r₉ r₁₈ r₁₉ fun r hr ↦ ?_, ?_, ?_⟩⟩
  · rw [k₇ r (mem_of_mem hr _), hpres₆ r (mem_of_mem hr _), A.regs r hr]
  · exact {
      heap := ⟨hn₇ ▸ hgrow₆.heap.lo, hn₇ ▸ hh₆⟩
      mono := by omega
      ok := hfin.2.1
      deep := fun x hx ↦ by
        rw [hfin.2.2.1] at hx
        rcases hgrow₆.deep x hx with h | h | h
        · rw [A.keep.2.1] at h; exact Or.inl h
        · exact h.elim
        · simp only [Fresh] at h ⊢
          exact Or.inr (Or.inr ⟨by omega, by omega⟩)
      frame := ((A.frame.union hg₆).union (DFrame.of_same hm₇ fun _ ↦ False)).mono fun x hx ↦ by
        simp only [Scratch] at hx
        rcases hx with ((hx | hx | hx) | hx | hx | hx | hx | hx) | hx
        · exact Or.inr (Or.inr (Or.inl (by addr_omega [hx, hsb])))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
        · simp only [Fresh] at hx ⊢; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hx.1, by omega⟩)))
        · exact Or.inl hx
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr (Or.inl (by addr_omega [hx, hsb, A.x2])))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
        · simp only [Fresh] at hx ⊢
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
        · exact hx.elim }
  · rw [hfin.1, hval₆, A.keep.1, A.pre2, A.counter, show (3 : Word).toNat = 3 from rfl,
      A.values]
    rfl

end Rv64Verifier.Layout.Memory
