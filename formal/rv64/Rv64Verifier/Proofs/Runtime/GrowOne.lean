import Rv64Verifier.Proofs.Runtime.Inv
import Rv64Verifier.Proofs.Runtime.Grow

/-!
# `RawVec<T>::grow_one`, eight copies

```rust
if let Err(err) = self.inner.grow_amortized(self.cap, 1, T::LAYOUT) { handle_error(err) }
```

Every copy is the same fourteen words but for the element's alignment and size (`addi a3`,
`addi a4`) and the call's offset: at `e`, a 16-byte frame saving `ra`, `a1 = cap`, `a2 = 1`,
`a3 = align`, `a4 = size`, the call to `grow_amortized`; at `e + 32`, `a0 ≠ -1` goes to the trap at
`e + 52`; at `e + 40`, restore and return. One expectation per block, parametrized by `e` and the
constants (`callA`, `checkB`, `retC`), is checked against each copy by the kernel (`spec_of`), and
one proof (`grow_one_of`) covers them all.
-/

namespace Rv64Verifier.Runtime.GrowOne
open RiscvZkvm.Rv64 Rv64Verifier.Sym
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `e`: the frame, the arguments, the call. -/
def callA (e al sz : Word) : Expect where
  steps := 8
  pc := .c 0x8000c184
  regs := [(.x1, .c (e + 32)), (.x2, .bin .add (.reg .x2) (.c 0xfffffffffffffff0)),
    (.x10, .reg .x10), (.x11, .ld (.reg .x10)), (.x12, .c 1), (.x13, .c al), (.x14, .c sz)] ++
    saved.map fun r ↦ (r, .reg r)
  mem := [(⟨some (.reg .x2), 0xfffffffffffffff8⟩, .reg .x1)]
  writes := [⟨some (.reg .x2), 0xfffffffffffffff8⟩]
  obl := [.ne ⟨some (.reg .x10), 0⟩ ⟨some (.reg .x2), 0xfffffffffffffff8⟩,
    .valid ⟨some (.reg .x10), 0⟩ 8, .valid ⟨some (.reg .x2), 0xfffffffffffffff8⟩ 8]

/-- At `e + 32`: the trap unless `grow_amortized` returned `-1`. -/
def checkB (e : Word) : Expect where
  steps := 2
  pc := .ite .ne (.reg .x10) (.c 0xffffffffffffffff) (.c (e + 52)) (.c (e + 40))
  regs := (.x2, .reg .x2) :: saved.map fun r ↦ (r, .reg r)
  mem := []
  writes := []
  obl := []

/-- At `e + 40`: restore, return. -/
def retC : Expect where
  steps := 3
  pc := .bin .and (.ld (.bin .add (.reg .x2) (.c 8))) (.c 0xfffffffffffffffe)
  regs := [(.x1, .ld (.bin .add (.reg .x2) (.c 8))), (.x2, .bin .add (.reg .x2) (.c 16))] ++
    saved.map fun r ↦ (r, .reg r)
  mem := []
  writes := []
  obl := [.valid ⟨some (.reg .x2), 8⟩ 8]

theorem _root_.Rv64Verifier.Runtime.GrowOnePre.bounds {size align : Nat} {s : MachineState}
    (h : GrowOnePre size align s) :
    0x780000a0 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (s.getReg .x10).toNat % 8 = 0 ∧
      (s.getReg .x10).toNat + 16 ≤ 0xc0000008 := by
  have := h.stack.bounds (by decide) (by decide)
  have ha := h.stack.above
  have ho := ValidMemRange.bounds h.self (by decide)
  simp only [growOneStack, stackLo, heapEnd] at this ha
  rw [this.2.2.2] at ha
  omega

/-- **Every copy of `grow_one` meets its contract**, its new buffer a new one, given
`grow_amortized`'s, from its three blocks. -/
theorem grow_one_of (hG : GrowSpec) {e : Word} {size align : Nat}
    (hal : 0 < align ∧ align ≤ 2 ^ 32) (hsz : 0 < size ∧ size < 2 ^ 32)
    (hA : Spec e (callA e (BitVec.ofNat 64 align) (BitVec.ofNat 64 size)))
    (hB : Spec (e + 32) (checkB e)) (hC : Spec (e + 40) retC)
    (hret : (e + 32) &&& 0xfffffffffffffffe = e + 32)
    (htrap : Image.code.fetch (e + 52) = none) : GrowOneFreshSpec e size align := by
  intro s hpc hpre
  have hb := hpre.bounds
  have hst := hpre.stack
  have hss := hpre.selfStack
  have hsf := hpre.selfFree
  have hnx8 := hst.next
  have hab := hst.above
  have hraw := hpre.raw
  simp only [RawVecOk, Buf, vecPtr, vecCap] at hraw
  obtain ⟨t₁, hr₁, h₁⟩ := hA.reaches hpc (by
    rv_eval []
    and_intros
    · addr_omega [hb, hss]
    · valid_access hpre.self [hb]
    · valid_access hst.valid [hb])
  have x1 := h₁.reg .x1 rfl
  have x2 := h₁.reg .x2 rfl
  have x10 := h₁.reg .x10 rfl
  have x11 := h₁.reg .x11 rfl
  have x12 := h₁.reg .x12 rfl
  have x13 := h₁.reg .x13 rfl
  have x14 := h₁.reg .x14 rfl
  have pc₁ := h₁.pc
  have m₁ := h₁.memAt 0 (by exact Nat.zero_lt_one)
  rv_eval [] at x1 x2 x10 x11 x12 x13 x14 pc₁ m₁
  have hm₁ (a : Word) (ha : a ≠ s.getReg .x2 - 8) : t₁.getMem a = s.getMem a :=
    h₁.frame a (by rv_eval []; exact ha)
  have hn₁ : t₁.getMem nextAddr = s.getMem nextAddr := hm₁ _ (by addr_omega [hb, hnx8])
  have hheap₁ : HeapOk t₁ := ⟨by simp only [heapNext, hn₁]; exact hpre.heap.lo,
    by simp only [heapNext, hn₁]; exact hpre.heap.hi⟩
  have hsl : stackLo t₁ growStack = stackLo s growOneStack := by
    simp only [stackLo, growStack, growOneStack, x2]
    rw [Sym.sub_sub_lit]; rfl
  have hself : t₁.getMem (s.getReg .x10) = s.getMem (s.getReg .x10) := hm₁ _ (by addr_omega [hb, hss])
  have hself8 : t₁.getMem (s.getReg .x10 + 8) = s.getMem (s.getReg .x10 + 8) :=
    hm₁ _ (by addr_omega [hb, hss])
  have hv₁ : ValidMemRange (stackLo t₁ growStack) (growStack / 8) := by
    rw [hsl]
    exact ValidMemRange.sub hst.valid (by addr_omega [hb]) (by addr_omega [hb]) (by addr_omega [hb])
  have hro := hst.rodata
  have hpre₁ : GrowPre t₁ := {
    heap := hheap₁
    self := by rw [x10]; exact hpre.self
    align := by rw [x13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hal
    size := by rw [x14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hsz.1
    raw := by
      rw [x10, x13, x14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      simp only [RawVecOk, Buf, vecPtr, vecCap, hself, hself8, heapNext, hn₁]
      exact hraw
    stack := ⟨⟨hv₁, by rw [x2]; addr_omega [hb]⟩, by rw [hsl]; exact hab,
      by rw [hsl]; addr_omega [hnx8, hb], by rw [hsl]; addr_omega [hro, hb]⟩
    selfFree := by
      rw [x10]
      simp only [Outside, heapNext, hn₁] at hsf ⊢
      exact ⟨hsf.1, by addr_omega [hsf.2]⟩
    selfStack := by rw [x10, hsl]; addr_omega [hss] }
  obtain ⟨t₂, hr₂, ⟨hpc₂, hpres₂, hpost⟩ | hdead⟩ := hG.call hr₁ pc₁ hpre₁
  swap
  · exact ⟨t₂, hr₂, Or.inr hdead⟩
  have hpc₂' : t₂.pc = e + 32 := by rw [hpc₂, returnAddress_eq, x1]; exact hret
  obtain ⟨t₃, hr₃, h₃⟩ := hB.reaches hpc₂' trivial
  have pc₃ := h₃.pc
  have hm₃ (a : Word) : t₃.getMem a = t₂.getMem a := h₃.frame a (by simp [checkB])
  have k₃ (r : Reg) (hr : r ∈ Reg.x2 :: saved) : t₃.getReg r = t₂.getReg r := by
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact h₃.reg _ rfl
  rv_eval [] at pc₃
  rcases eq_ite_cases pc₃ with ⟨hne, pc₃⟩ | ⟨hok, pc₃⟩
  · exact ⟨t₃, hr₂.trans hr₃, Or.inr (dead_of_fetch (by rw [pc₃]; exact htrap))⟩
  have hok' : t₂.getReg .x10 = 0xffffffffffffffff := by simpa using hok
  have hsp₂ : t₂.getReg .x2 = s.getReg .x2 - 16 := by rw [hpres₂.reg .x2, x2]
  obtain ⟨t₄, hr₄, h₄⟩ := hC.reaches pc₃ (by
    rv_eval [k₃ .x2 (by decide), hsp₂]
    valid_access hst.valid [hb])
  have pc₄ := h₄.pc
  have x1₄ := h₄.reg .x1 rfl
  have x2₄ := h₄.reg .x2 rfl
  rv_eval [k₃ .x2 (by decide), hsp₂, hm₃] at pc₄ x1₄ x2₄
  have hm₄ (a : Word) : t₄.getMem a = t₃.getMem a := h₄.frame a (by simp [retC])
  have hfr := hpost.frame
  rw [x10, hsl] at hfr
  have hheap₂ := hpost.heap
  have hra : t₂.getMem (s.getReg .x2 - 8) = s.getReg .x1 := by
    rw [hfr.getMem fun i hi ha ↦ ?_, m₁]
    have := hheap₂.hi
    simp only [Fresh, heapNext] at ha this
    rcases ha with ha | ha | ha | ha
    · addr_omega [ha, hi, hss, hb]
    · addr_omega [ha, hi, hb]
    · addr_omega [ha, hi, hb, hnx8]
    · addr_omega [ha.2, hi, hb, hab, this]
  rw [hra] at pc₄
  have hsz' : (BitVec.ofNat 64 size).toNat = size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hal' : (BitVec.ofNat 64 align).toNat = align := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmt (a : Word) : t₄.getMem a = t₂.getMem a := (hm₄ a).trans (hm₃ a)
  have hn₄ : heapNext t₄ = heapNext t₂ := by simp only [heapNext, hmt]
  have hn₁' : heapNext t₁ = heapNext s := by simp only [heapNext, hn₁]
  refine ⟨t₄, hr₂.trans (hr₃.trans hr₄), Or.inl ⟨pc₄.trans (returnAddress_eq s).symm, ?_,
    ⟨⟨hn₄ ▸ hheap₂.lo, hn₄ ▸ hheap₂.hi⟩, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩⟩
  · have kA := h₁.keeps (rs := saved) rfl
    have kC := h₄.keeps (rs := saved) rfl
    intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · exact x2₄
    · have hr' : r ∈ saved := by simp only [saved, List.mem_cons, List.not_mem_nil, or_false]; exact hr
      rw [kC r hr', k₃ r (List.mem_cons_of_mem _ hr'), hpres₂ r (mem_of_mem hr' _), kA r hr']
  · rw [hn₄, ← hn₁']; exact hpost.mono
  · obtain ⟨hcap, -, -⟩ := hpost.ok hok'
    rw [x11, x12, x10] at hcap
    simp only [vecCap, hmt]
    exact hcap
  · obtain ⟨-, hraw', -⟩ := hpost.ok hok'
    rw [x10, x13, x14, hsz', hal'] at hraw'
    simp only [RawVecOk, Buf, vecCap, vecPtr, hmt, hn₄] at hraw' ⊢
    exact hraw'
  · obtain ⟨-, -, hby⟩ := hpost.ok hok'
    rw [x10, x14, hsz'] at hby
    simp only [vecCap, vecPtr, hmt, hself, hself8] at hby ⊢
    rw [(ByteFrame.of_same hmt fun _ ↦ False).bytesAt fun _ _ h ↦ h, hby]
    rcases hraw.2 with h0 | h0
    · simp only [h0]; rfl
    · exact bytesAt_of_below (lo := s.getReg .x2 - 8) (N := 8)
        (fun a ha ↦ hm₁ a fun h' ↦ ha (by rw [h']; addr_omega [hb]))
        (by have := hpre.heap.hi; addr_omega [h0, this, hab, hb])
  · have bf₁ := ByteFrame.of_single (s := s) (t := t₁) (by addr_omega [hb]) hm₁
    refine ((bf₁.mono (w' := fun a ↦ Within a (s.getReg .x10) 16 ∨
      Within a (stackLo s growOneStack) growOneStack ∨ Within a nextAddr 8 ∨ Fresh s t₄ a)
      fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb]))).trans hfr fun a ha ↦ ?_).trans
      (ByteFrame.of_same hmt _) fun _ h ↦ h
    rcases ha with ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inl (by addr_omega [ha, hb]))
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (by simp only [Fresh, hn₁', hn₄] at ha ⊢; exact ha)))
  · have hf := hpost.fresh hok'
    rw [x10, x13, x14, hsz', hal'] at hf
    simp only [NewBuf, vecCap, vecPtr, hmt, hn₄, hn₁'] at hf ⊢
    exact hf

/-! ## The copies -/

theorem trap {e : Word} (h : (Image.code.fetch e).isNone = true) : Image.code.fetch e = none :=
  Option.isNone_iff_eq_none.mp h

/-- `RawVec<ColumnClaim>::grow_one`. -/
theorem grow_one_8000c0a4 (hG : GrowSpec) : GrowOneFreshSpec 0x8000c0a4 56 8 :=
  grow_one_of hG (by decide) (by decide)
    (spec_of 12329 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 12337 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 12339 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (by decide) (trap (by decide +kernel))

/-- `RawVec<(Vec<E>, GluedWeight)>::grow_one`. -/
theorem grow_one_8000c7d0 (hG : GrowSpec) : GrowOneFreshSpec 0x8000c7d0 80 8 :=
  grow_one_of hG (by decide) (by decide)
    (spec_of 12788 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 12796 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 12798 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (by decide) (trap (by decide +kernel))

/-- `RawVec<K>::grow_one`. -/
theorem grow_one_8000d7bc (hG : GrowSpec) : GrowOneFreshSpec 0x8000d7bc 8 8 :=
  grow_one_of hG (by decide) (by decide)
    (spec_of 13807 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 13815 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 13817 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (by decide) (trap (by decide +kernel))

/-- `RawVec<GluedClaim>::grow_one`. -/
theorem grow_one_8000db78 (hG : GrowSpec) : GrowOneFreshSpec 0x8000db78 88 8 :=
  grow_one_of hG (by decide) (by decide)
    (spec_of 14046 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 14054 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 14056 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (by decide) (trap (by decide +kernel))

/-- `RawVec<(Vec<E>, Vec<E>)>::grow_one`. -/
theorem grow_one_80010a94 (hG : GrowSpec) : GrowOneFreshSpec 0x80010a94 48 8 :=
  grow_one_of hG (by decide) (by decide)
    (spec_of 17061 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 17069 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 17071 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (by decide) (trap (by decide +kernel))

/-- `RawVec<Vec<Form>>::grow_one`. -/
theorem grow_one_80011c78 (hG : GrowSpec) : GrowOneFreshSpec 0x80011c78 24 8 :=
  grow_one_of hG (by decide) (by decide)
    (spec_of 18206 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 18214 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 18216 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (by decide) (trap (by decide +kernel))

/-- `RawVec<u16>::grow_one`. -/
theorem grow_one_80011f88 (hG : GrowSpec) : GrowOneFreshSpec 0x80011f88 2 2 :=
  grow_one_of hG (by decide) (by decide)
    (spec_of 18402 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 18410 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 18412 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (by decide) (trap (by decide +kernel))

/-- `RawVec<(u64, usize)>::grow_one`. -/
theorem grow_one_80011fc0 (hG : GrowSpec) : GrowOneFreshSpec 0x80011fc0 16 8 :=
  grow_one_of hG (by decide) (by decide)
    (spec_of 18416 8 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 18424 2 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (spec_of 18426 3 (by decide +kernel) (by decide +kernel) (by decide) (by decide))
    (by decide) (trap (by decide +kernel))

end Rv64Verifier.Runtime.GrowOne
