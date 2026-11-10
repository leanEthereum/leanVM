import Rv64Verifier.Proofs.Layout.Keep
import Rv64Verifier.Proofs.Layout.ContractsBuild
import Rv64Verifier.Blocks.F20

/-!
# `Flushes::memory_cols`, at `0x80005c64`: what its phases keep

```rust
fn memory_cols(&mut self, address: Form, count: usize, columns: &[usize]) {
    let values = core::array::from_fn(|limb| columns.get(limb).map_or(constant(ZERO), |&column| col(column, 0)));
    self.memory(address, count, &values);
}
```

compiled (`Blocks/F20.lean`), `sp'` the entry's `sp - 240`: each limb calls `term(sp' + 168, One,
ZERO)` (the default is built eagerly), then `col(sp' + 144, columns[limb], 0)` while there are
columns, and moves the limb's form into `sp' + 72 + 24 limb`; `0x80005dd4` `memcpy`s the three into
`sp'` and `0x80005e00` calls `memory(self, address, count, sp')`.

Every phase keeps `Inv`: the registers and slots the epilogue restores, `.rodata`, and a frame of
scratch writes. A form built on the way is `Built`: sound, its buffer allocated since the entry.
-/

namespace Rv64Verifier.Layout.MemoryCols
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Model.LayoutMirror

/-- `ZERO` in `.rodata`, at `0xa0000068`. -/
theorem eAt_zero {s : MachineState} (h : RodataOk s) : eAt s 0xa0000068 = 0 := by
  have h0 : s.getMem 0xa0000068 = 0 := h.word
  have h1 : s.getMem (0xa0000068 + 8) = 0 := h.word
  have h2 : s.getMem (0xa0000068 + 16) = 0 := h.word
  exact eAt_eq_of_limbs (by rw [h0, h1, h2]; decide +kernel)

/-- The stack's bounds. -/
theorem facts {s : MachineState} (hpre : MemoryColsPre s) :
    (0x20 + 1744 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (stackLo s 1744).toNat = (s.getReg .x2).toNat - 1744) ∧
    heapEnd ≤ (stackLo s 1744).toNat ∧ Apart (stackLo s 1744) 1744 nextAddr 8 ∧
    Apart (stackLo s 1744) 1744 rodataStart rodataSize := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hro := hpre.stack.rodata
  simp only [memoryColsStack, memoryStack, countedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hro
  exact ⟨hsb, hab, hnx, hro⟩

/-- The stack lies above `.rodata`'s start: its second doubleword is valid and above the heap. -/
theorem stack_high {s : MachineState} (hpre : MemoryColsPre s) :
    0xa0000000 ≤ (stackLo s 1744).toNat := by
  obtain ⟨hsb, hab, -, -⟩ := facts hpre
  have hv := hpre.stack.valid 1 (by
    simp only [memoryColsStack, memoryStack, countedStack, colStack, powStack, Contracts.mulStack,
      Nat.reduceAdd]; decide)
  simp only [memoryColsStack, memoryStack, countedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hv
  have h := (Sym.validAccess_eight _).mp (validAccess_of_dword hv)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h
  simp only [heapEnd] at hab
  omega

/-- What every phase keeps, from the entry `s` to `u`. -/
structure Inv (s u : MachineState) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 240
  x8 : u.getReg .x8 = s.getReg .x12
  x9 : u.getReg .x9 = s.getReg .x11
  x18 : u.getReg .x18 = s.getReg .x10
  x19 : u.getReg .x19 = s.getReg .x13
  x20 : u.getReg .x20 = s.getReg .x14
  regs : ∀ r ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x26, .x27], u.getReg r = s.getReg r
  ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : u.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : u.getMem (s.getReg .x2 - 40) = s.getReg .x19
  s4 : u.getMem (s.getReg .x2 - 48) = s.getReg .x20
  heap : HeapOk u
  mono : heapNext s ≤ heapNext u
  rodata : RodataOk u
  frame : DFrame s u (Scratch s u (stackLo s 1744) 1744)

/-- A form built since the entry `s`, at `e` in `u`: sound, its buffer allocated since. -/
structure Built (s u : MachineState) (e : Word) (f : FormRust) : Prop where
  ok : FormOk u e
  val : formOf u e = f
  buf : ∀ x, formBuf u e x → heapNext s ≤ x.toNat ∧ x.toNat < heapNext u

/-- A step that writes only the stack below the saved registers, `NEXT` and the heap it allocates
keeps `Inv`. -/
theorem Inv.step {s u v : MachineState} (hpre : MemoryColsPre s) (c : Inv s u) {W : Word → Prop}
    (hf : DFrame u v W)
    (hW : ∀ x, W x → Within x (stackLo s 1744) 1696 ∨ Within x nextAddr 8 ∨ Fresh u v x)
    (hheap : HeapOk v) (hmono : heapNext u ≤ heapNext v) (hp : Preserves u v) : Inv s v := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hhv := hheap.hi
  have cm := c.mono
  have hslot (a : Word) (ha₁ : (s.getReg .x2).toNat - 48 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : v.getMem a = u.getMem a :=
    hf.getMem_of (fun x hx hw ↦ by
      rcases hW x hw with h | h | h
      · addr_omega [hx, h, hsb, ha₁, ha₂]
      · addr_omega [hx, h, hsb, hnx, ha₁, ha₂]
      · simp only [Fresh] at h; addr_omega [hx, h, hsb, hab, hhv, ha₁, ha₂])
      (by addr_omega [hsb, ha₂])
  exact {
    x2 := (hp.reg .x2).trans c.x2
    x8 := (hp.reg .x8).trans c.x8
    x9 := (hp.reg .x9).trans c.x9
    x18 := (hp.reg .x18).trans c.x18
    x19 := (hp.reg .x19).trans c.x19
    x20 := (hp.reg .x20).trans c.x20
    regs := fun r hr ↦ (hp r (mem_of_mem hr _)).trans (c.regs r hr)
    ra := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.ra
    s0 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s0
    s1 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s1
    s2 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s2
    s3 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s3
    s4 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s4
    heap := hheap
    mono := by omega
    rodata := RodataOk.dframe c.rodata hf fun x hw h ↦ by
      rcases hW x hw with h' | h' | h'
      · addr_omega [h, h', hsb, hro]
      · addr_omega [h, h']
      · simp only [Fresh] at h'; addr_omega [h, h', hhv]
    frame := (c.frame.union hf).mono fun x hx ↦ by
      simp only [Scratch, Fresh] at hx ⊢
      rcases hx with (h | h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h.1, by omega⟩)
      · rcases hW x h with h | h | h
        · exact Or.inl (by addr_omega [h, hsb])
        · exact Or.inr (Or.inl h)
        · simp only [Fresh] at h; exact Or.inr (Or.inr ⟨by omega, h.2⟩) }

/-- A form built is kept by a step whose writes miss its header and lie in the stack, `NEXT` or the
heap allocated since. -/
theorem Built.step {s u v : MachineState} {e : Word} {f : FormRust} (b : Built s u e f)
    {W : Word → Prop} (hf : DFrame u v W) (hheap : HeapOk u) (hmono : heapNext u ≤ heapNext v)
    (hW : ∀ x, W x → heapEnd ≤ x.toNat ∨ heapNext u ≤ x.toNat)
    (he : ∀ x, Within x e 24 → ¬ W x) (hew : e.toNat + 24 ≤ 2 ^ 64) : Built s v e f := by
  have hhi := hheap.hi
  have hk := formOf_frame hf b.ok he (fun x hx hw ↦ by
    have := b.buf x hx
    rcases hW x hw with h | h <;> omega) hew hheap hmono
  refine ⟨hk.2, hk.1.trans b.val, fun x hx ↦ ?_⟩
  rw [formBuf_frame hf he hew] at hx
  have := b.buf x hx
  omega

/-- A form built, its header copied from `e'` to `e`. -/
theorem Built.move {s u v : MachineState} {e e' : Word} {f : FormRust} (b : Built s u e' f)
    {W : Word → Prop} (hf : DFrame u v W) (hheap : HeapOk u) (hmono : heapNext u ≤ heapNext v)
    (hW : ∀ x, W x → heapEnd ≤ x.toNat ∨ heapNext u ≤ x.toNat)
    (h0 : v.getMem e = u.getMem e') (h8 : v.getMem (e + 8) = u.getMem (e' + 8))
    (h16 : v.getMem (e + 16) = u.getMem (e' + 16)) : Built s v e f := by
  have hhi := hheap.hi
  have hk := formOf_move hf b.ok h0 h8 h16 (fun x hx hw ↦ by
    have := b.buf x hx
    rcases hW x hw with h | h <;> omega) hheap hmono
  refine ⟨hk.2.1, hk.1.trans b.val, fun x hx ↦ ?_⟩
  rw [hk.2.2] at hx
  have := b.buf x hx
  omega

/-- What a call keeps: the forms built in the frame's locals, apart from its output `o`. -/
def Keeps (s u v : MachineState) (o : Word) : Prop :=
  ∀ e f, Built s u e f → (s.getReg .x2).toNat - 240 ≤ e.toNat →
    e.toNat + 24 ≤ (s.getReg .x2).toNat - 48 → Apart e 24 o 24 → Built s v e f

/-- A call building a form at `o` in the frame's locals, its stack below `sp'`. -/
theorem callFrame {s u v : MachineState} (hpre : MemoryColsPre s) (c : Inv s u) {o : Word}
    {n : Nat}
    (hf : DFrame u v fun a ↦ Within a o 24 ∨ Within a (stackLo u n) n ∨ Within a nextAddr 8 ∨
      Fresh u v a)
    (ho₁ : (s.getReg .x2).toNat - 240 ≤ o.toNat) (ho₂ : o.toNat + 24 ≤ (s.getReg .x2).toNat - 48)
    (hst : ∀ a, Within a (stackLo u n) n →
      (s.getReg .x2).toNat - 1744 ≤ a.toNat ∧ a.toNat < (s.getReg .x2).toNat - 240)
    (hheap : HeapOk v) (hmono : heapNext u ≤ heapNext v) (hp : Preserves u v) :
    Inv s v ∧ Keeps s u v o := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hhv := hheap.hi
  have hhu := c.heap.hi
  refine ⟨c.step hpre hf (fun x hx ↦ ?_) hheap hmono hp, fun e f b he₁ he₂ hap ↦ ?_⟩
  · rcases hx with h | h | h | h
    · exact Or.inl (by addr_omega [h, hsb, ho₁, ho₂])
    · have := hst x h; exact Or.inl (by addr_omega [this, hsb])
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · refine b.step hf c.heap hmono (fun x hx ↦ ?_) (fun x hx hw ↦ ?_) (by addr_omega [he₂, hsb])
    · rcases hx with h | h | h | h
      · exact Or.inl (by addr_omega [h, hsb, hab, ho₁, ho₂])
      · have := hst x h; exact Or.inl (by addr_omega [this, hsb, hab])
      · exact Or.inl (by addr_omega [h])
      · exact Or.inr h.1
    · rcases hw with h | h | h | h
      · addr_omega [hx, h, hap]
      · have := hst x h; addr_omega [hx, this, he₁]
      · addr_omega [hx, h, hsb, hnx, he₁, he₂]
      · simp only [Fresh] at h; addr_omega [hx, h, hsb, hab, hhv, he₁, he₂]

/-- A block writing `k` bytes from `lo` in the frame's locals. -/
theorem Inv.block {s u v : MachineState} (hpre : MemoryColsPre s) (c : Inv s u) {lo : Word}
    {k : Nat} (hm : MemFrame u v lo k) (hlo : (s.getReg .x2).toNat - 240 ≤ lo.toNat)
    (hk : lo.toNat + k ≤ (s.getReg .x2).toNat - 48) (hp : Preserves u v) : Inv s v := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]; rw [hm _ (by addr_omega [hnx, hsb, hlo, hk])]
  exact c.step hpre hm.dframe (fun x hx ↦ Or.inl (by addr_omega [hx, hsb, hlo, hk]))
    ⟨hn ▸ c.heap.lo, hn ▸ c.heap.hi⟩ hn.ge hp

theorem Built.block {s u v : MachineState} {e : Word} {f : FormRust} (hpre : MemoryColsPre s)
    (b : Built s u e f) (c : Inv s u) {lo : Word} {k : Nat} (hm : MemFrame u v lo k)
    (hlo : (s.getReg .x2).toNat - 240 ≤ lo.toNat) (hk : lo.toNat + k ≤ (s.getReg .x2).toNat - 48)
    (he : Apart e 24 lo k) (hew : e.toNat + 24 ≤ 2 ^ 64) : Built s v e f := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]; rw [hm _ (by addr_omega [hnx, hsb, hlo, hk])]
  exact b.step hm.dframe c.heap hn.ge (fun x hx ↦ Or.inl (by addr_omega [hx, hsb, hab, hlo, hk]))
    (fun x hx hw ↦ by addr_omega [hx, hw, he]) hew

/-- A block's copy of a form's header from `e'` to `e`, both in the frame's locals. -/
theorem Built.blockMove {s u v : MachineState} {e e' : Word} {f : FormRust}
    (hpre : MemoryColsPre s) (b : Built s u e' f) (c : Inv s u) {lo : Word} {k : Nat}
    (hm : MemFrame u v lo k) (hlo : (s.getReg .x2).toNat - 240 ≤ lo.toNat)
    (hk : lo.toNat + k ≤ (s.getReg .x2).toNat - 48)
    (h0 : v.getMem e = u.getMem e') (h8 : v.getMem (e + 8) = u.getMem (e' + 8))
    (h16 : v.getMem (e + 16) = u.getMem (e' + 16)) : Built s v e f := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]; rw [hm _ (by addr_omega [hnx, hsb, hlo, hk])]
  exact b.move hm.dframe c.heap hn.ge (fun x hx ↦ Or.inl (by addr_omega [hx, hsb, hab, hlo, hk]))
    h0 h8 h16

/-- A block writing nothing. -/
theorem Inv.same {s u v : MachineState} (hpre : MemoryColsPre s) (c : Inv s u)
    (hm : ∀ a, v.getMem a = u.getMem a) (hp : Preserves u v) : Inv s v := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact c.step hpre (DFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim)
    ⟨hn ▸ c.heap.lo, hn ▸ c.heap.hi⟩ hn.ge hp

theorem Built.same {s u v : MachineState} {e : Word} {f : FormRust} (b : Built s u e f)
    (hheap : HeapOk u) (hm : ∀ a, v.getMem a = u.getMem a) (hew : e.toNat + 24 ≤ 2 ^ 64) :
    Built s v e f := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact b.step (DFrame.of_same hm fun _ ↦ False) hheap hn.ge (fun _ h ↦ h.elim) (fun _ _ h ↦ h) hew

/-! ## The calls -/

/-- `term(sp' + 168, One, ZERO)`, the monomial's tag at `sp'`. -/
theorem termCall (hT : TermSpec) {s u0 u : MachineState} (hpre : MemoryColsPre s) (c : Inv s u)
    (hr : Reaches Image.code u0 u) (hpc : u.pc = 0x800050a8)
    (h10 : u.getReg .x10 = s.getReg .x2 - 72) (h11 : u.getReg .x11 = s.getReg .x2 - 240)
    (h12 : u.getReg .x12 = 0xa0000068) (htag : u.getMem (s.getReg .x2 - 240) = 0) :
    ∃ v, Reaches Image.code u0 v ∧ ((v.pc = returnAddress u ∧ Inv s v ∧
      Built s v (s.getReg .x2 - 72) (constantRust 0) ∧ Keeps s u v (s.getReg .x2 - 72)) ∨
      Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hterm : TermPre u := {
    heap := c.heap
    stack := hpre.stack.inner (k := 240) x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [h10]; valid_sub hpre.stack.valid [hsb]
    mono := by rw [h11]; valid_sub hpre.stack.valid [hsb]
    coeff := by rw [h12]; exact validMemRange_of (by decide) (Or.inr ⟨by decide, by decide⟩)
    monoOk := by rw [h11]; simp only [MonoOk, htag]; decide
    outFree := by rw [h10]; addr_omega [hsb, hab, hnx]
    monoNext := by rw [h11]; addr_omega [hsb, hnx]
    coeffNext := by rw [h12]; addr_omega []
    outStack := by rw [h10]; addr_omega [hsb, x2]
    monoStack := by rw [h11]; addr_omega [hsb, x2]
    coeffStack := by rw [h12]; addr_omega [hsb, x2, hro] }
  obtain ⟨v, hrv, ⟨hpcv, hpres, hnew, hval⟩ | hdead⟩ := hT.call hr hpc hterm
  swap
  · exact ⟨v, hrv, Or.inr hdead⟩
  rw [h10] at hnew hval
  rw [h11, h12] at hval
  obtain ⟨cv, kv⟩ := callFrame hpre c hnew.frame (by addr_omega [hsb]) (by addr_omega [hsb])
    (fun a h ↦ by addr_omega [h, hsb, x2]) hnew.heap hnew.mono hpres
  have cm := c.mono
  refine ⟨v, hrv, Or.inl ⟨hpcv, cv, ⟨hnew.ok, ?_, fun x hx ↦ ?_⟩, kv⟩⟩
  · rw [hval, monoOf, htag, eAt_zero c.rodata]; rfl
  · have hb := hnew.fresh
    simp only [NewBuf, formBuf, Within] at hb hx
    omega

/-- `col(sp' + 144, a1, 0)`. -/
theorem colCall (hC : ColSpec) {s u0 u : MachineState} (hpre : MemoryColsPre s) (c : Inv s u)
    (hr : Reaches Image.code u0 u) (hpc : u.pc = 0x80004b34)
    (h10 : u.getReg .x10 = s.getReg .x2 - 96) (h12 : u.getReg .x12 = 0) :
    ∃ v, Reaches Image.code u0 v ∧ ((v.pc = returnAddress u ∧ Inv s v ∧
      Built s v (s.getReg .x2 - 96) (colRust (u.getReg .x11).toNat 0) ∧
      Keeps s u v (s.getReg .x2 - 96)) ∨ Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hcol : ColPre u := {
    heap := c.heap
    stack := hpre.stack.inner (k := 240) x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [h10]; valid_sub hpre.stack.valid [hsb]
    outFree := by rw [h10]; addr_omega [hsb, hab, hnx]
    outStack := by rw [h10]; addr_omega [hsb, x2]
    rodata := c.rodata }
  obtain ⟨v, hrv, ⟨hpcv, hpres, hnew, hval⟩ | hdead⟩ := hC.call hr hpc hcol
  swap
  · exact ⟨v, hrv, Or.inr hdead⟩
  rw [h10] at hnew hval
  rw [h12] at hval
  obtain ⟨cv, kv⟩ := callFrame hpre c hnew.frame (by addr_omega [hsb]) (by addr_omega [hsb])
    (fun a h ↦ by addr_omega [h, hsb, x2]) hnew.heap hnew.mono hpres
  have cm := c.mono
  refine ⟨v, hrv, Or.inl ⟨hpcv, cv, ⟨hnew.ok, hval, fun x hx ↦ ?_⟩, kv⟩⟩
  have hb := hnew.fresh
  simp only [NewBuf, formBuf, Within] at hb hx
  omega

/-- The columns are kept: they miss every scratch write. -/
theorem Inv.column {s u : MachineState} (hpre : MemoryColsPre s) (c : Inv s u) {i : Nat}
    (hi : i < (s.getReg .x14).toNat) :
    u.getMem (s.getReg .x13 + BitVec.ofNat 64 (8 * i)) =
      s.getMem (s.getReg .x13 + BitVec.ofNat 64 (8 * i)) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hcf := hpre.columnsFree
  have hcs := hpre.columnsStack
  have hcb := ValidMemRange.bounds hpre.columns (by omega)
  simp only [memoryColsStack, memoryStack, countedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hcs
  have hhu := c.heap.hi
  have hcf1 := hcf.1
  have hcf2 := hcf.2
  exact c.frame.getMem_of (fun x hx hw ↦ by
    simp only [Scratch, Fresh] at hw
    rcases hw with hw | hw | hw <;> addr_omega [hx, hw, hcf1, hcf2, hcs, hcb, hi, hhu])
    (by addr_omega [hcb, hi])

/-- A block writing `ZERO`'s monomial tag at `sp'`, then `term(sp' + 168, One, ZERO)`. -/
theorem zeroTerm (hT : TermSpec) {s u0 t t₁ : MachineState} (hpre : MemoryColsPre s)
    (c : Inv s t) (hr : Reaches Image.code u0 t₁) (hm : MemFrame t t₁ (t.getReg .x2) 8)
    (hp : Preserves t t₁) (hpc : t₁.pc = 0x800050a8)
    (h10 : t₁.getReg .x10 = t.getReg .x2 + 168) (h11 : t₁.getReg .x11 = t.getReg .x2)
    (h12 : t₁.getReg .x12 = 0xa0000068) (htag : t₁.getMem (t.getReg .x2) = 0) :
    ∃ v, Reaches Image.code u0 v ∧ ((v.pc = returnAddress t₁ ∧ Inv s v ∧
      Built s v (s.getReg .x2 - 72) (constantRust 0) ∧
      ∀ e f, Built s t e f → (s.getReg .x2).toNat - 232 ≤ e.toNat →
        e.toNat + 24 ≤ (s.getReg .x2).toNat - 48 → Apart e 24 (s.getReg .x2 - 72) 24 →
        Built s v e f) ∨ Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  rw [c.x2] at hm h10 h11 htag
  have c₁ := c.block hpre hm (by addr_omega [hsb]) (by addr_omega [hsb]) hp
  obtain ⟨v, hrv, ⟨hpcv, cv, bv, kv⟩ | hd⟩ := termCall hT hpre c₁ hr hpc
    (by rw [h10]; rv_eval []) h11 h12 htag
  · exact ⟨v, hrv, Or.inl ⟨hpcv, cv, bv, fun e f b he₁ he₂ hap ↦
      kv e f (b.block hpre c hm (by addr_omega [hsb]) (by addr_omega [hsb])
        (by addr_omega [hsb, he₁]) (by addr_omega [hsb, he₂])) (by omega) he₂ hap⟩⟩
  · exact ⟨v, hrv, Or.inr hd⟩

/-- A block writing nothing, then `col(sp' + 144, a1, 0)`. -/
theorem colBlock (hC : ColSpec) {s u0 t t₁ : MachineState} (hpre : MemoryColsPre s)
    (c : Inv s t) (hr : Reaches Image.code u0 t₁) (hm : ∀ a, t₁.getMem a = t.getMem a)
    (hp : Preserves t t₁) (hpc : t₁.pc = 0x80004b34)
    (h10 : t₁.getReg .x10 = t.getReg .x2 + 144) (h12 : t₁.getReg .x12 = 0) :
    ∃ v, Reaches Image.code u0 v ∧ ((v.pc = returnAddress t₁ ∧ Inv s v ∧
      Built s v (s.getReg .x2 - 96) (colRust (t₁.getReg .x11).toNat 0) ∧
      ∀ e f, Built s t e f → (s.getReg .x2).toNat - 240 ≤ e.toNat →
        e.toNat + 24 ≤ (s.getReg .x2).toNat - 48 → Apart e 24 (s.getReg .x2 - 96) 24 →
        Built s v e f) ∨ Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  rw [c.x2] at h10
  have c₁ := c.same hpre hm hp
  obtain ⟨v, hrv, ⟨hpcv, cv, bv, kv⟩ | hd⟩ := colCall hC hpre c₁ hr hpc (by rw [h10]; rv_eval []) h12
  · exact ⟨v, hrv, Or.inl ⟨hpcv, cv, bv, fun e f b he₁ he₂ hap ↦
      kv e f (b.same c.heap hm (by addr_omega [hsb, he₂])) he₁ he₂ hap⟩⟩
  · exact ⟨v, hrv, Or.inr hd⟩

end Rv64Verifier.Layout.MemoryCols
