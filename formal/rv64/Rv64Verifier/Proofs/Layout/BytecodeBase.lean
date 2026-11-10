import Rv64Verifier.Proofs.Layout.MemoryColsBase
import Rv64Verifier.Blocks.F11

/-!
# `Flushes::bytecode`, at `0x80004b94`: what its phases keep

```rust
fn bytecode(&mut self, pc: usize, count: usize, opcode: usize, operands: Vec<Form>) {
    let suffix = [vec![constant(gpow(opcode as u64))], operands].concat();
    self.counted(&[constant(SEP_BYTECODE), col(pc, 0)], col(count, 1), count, &suffix);
}
```

compiled for `pc = 0` (`Blocks/F11.lean`), `sp'` the entry's `sp - 144`: `0x80004b94` saves `ra`,
`s0`..`s4` and calls `alloc(8, 24)` (`B`), `0x80004bd0` traps on null; `0x80004bd4` writes `GEN` at
`sp'` and calls `pow(sp' + 72, sp', opcode)`; `0x80004bfc` calls `term(B, One, sp' + 72)`;
`0x80004c14` calls `try_allocate_in(sp', len + 1, 0, 8, 24)`, `0x80004c38` traps on an error;
`0x80004c40` makes the `Vec` at `sp' + 48` and calls `spec_extend` with `B..B + 24`, `0x80004c68`
with the operands; `0x80004c88` calls `term(sp', One, SEP_BYTECODE)`, `0x80004ca4`
`col(sp' + 24, 0, 0)`, `0x80004cb8` `col(sp' + 72, count, 1)`; `0x80004ccc` calls
`counted(self, sp', sp' + 72, count, suffix)`; `0x80004cec` restores and returns.

Every phase keeps `Inv`; a form built is `MemoryCols.Built`, the suffix's `Vec` `VBuilt`.
-/

namespace Rv64Verifier.Layout.Bytecode
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.MemoryCols (Built)

/-- The stack's bounds. -/
theorem facts {s : MachineState} (hpre : BytecodePre s) :
    (0x20 + 1536 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (stackLo s 1536).toNat = (s.getReg .x2).toNat - 1536) ∧
    heapEnd ≤ (stackLo s 1536).toNat ∧ Apart (stackLo s 1536) 1536 nextAddr 8 ∧
    Apart (stackLo s 1536) 1536 rodataStart rodataSize := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hro := hpre.stack.rodata
  simp only [bytecodeStack, countedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hsb hab hnx hro
  exact ⟨hsb, hab, hnx, hro⟩

/-- The registers `Inv` tracks are kept. -/
def KeepRegs (u v : MachineState) : Prop :=
  ∀ r ∈ [Reg.x2, .x8, .x9, .x21, .x22, .x23, .x24, .x25, .x26, .x27], v.getReg r = u.getReg r

theorem keepRegs_of {u v : MachineState} (h : Preserves u v) : KeepRegs u v :=
  fun r hr ↦ h r (mem_of_mem hr _)

/-- What every phase keeps, from the entry `s` to `u`. -/
structure Inv (s u : MachineState) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 144
  x8 : u.getReg .x8 = s.getReg .x11
  x9 : u.getReg .x9 = s.getReg .x10
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
  frame : DFrame s u (Scratch s u (stackLo s 1536) 1536)

/-- A step that writes only the stack below the saved registers, `NEXT` and the heap allocated since
the entry keeps `Inv`. -/
theorem Inv.step {s u v : MachineState} (hpre : BytecodePre s) (c : Inv s u) {W : Word → Prop}
    (hf : DFrame u v W)
    (hW : ∀ x, W x → Within x (stackLo s 1536) 1488 ∨ Within x nextAddr 8 ∨
      (heapNext s ≤ x.toNat ∧ x.toNat < heapNext v))
    (hheap : HeapOk v) (hmono : heapNext u ≤ heapNext v) (hp : KeepRegs u v) : Inv s v := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hhv := hheap.hi
  have cm := c.mono
  have hslot (a : Word) (ha₁ : (s.getReg .x2).toNat - 48 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : v.getMem a = u.getMem a :=
    hf.getMem_of (fun x hx hw ↦ by
      rcases hW x hw with h | h | h
      · addr_omega [hx, h, hsb, ha₁, ha₂]
      · addr_omega [hx, h, hsb, hnx, ha₁, ha₂]
      · addr_omega [hx, h, hsb, hab, hhv, ha₁, ha₂])
      (by addr_omega [hsb, ha₂])
  exact {
    x2 := (hp .x2 (by decide)).trans c.x2
    x8 := (hp .x8 (by decide)).trans c.x8
    x9 := (hp .x9 (by decide)).trans c.x9
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
      · addr_omega [h, h', hhv]
    frame := (c.frame.union hf).mono fun x hx ↦ by
      simp only [Scratch, Fresh] at hx ⊢
      rcases hx with (h | h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h.1, by omega⟩)
      · rcases hW x h with h | h | h
        · exact Or.inl (by addr_omega [h, hsb])
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h) }

/-- A `Vec<Form>` built since the entry `s`, at `e` in `u`. -/
structure VBuilt (s u : MachineState) (e : Word) (l : List FormRust) : Prop where
  ok : FormVecOk u e
  val : formVecOf u e = l
  deep : ∀ x, formVecDeep u e x → heapNext s ≤ x.toNat ∧ x.toNat < heapNext u

theorem VBuilt.step {s u v : MachineState} {e : Word} {l : List FormRust} (b : VBuilt s u e l)
    {W : Word → Prop} (hf : DFrame u v W) (hheap : HeapOk u) (hmono : heapNext u ≤ heapNext v)
    (hW : ∀ x, W x → heapEnd ≤ x.toNat ∨ heapNext u ≤ x.toNat)
    (he : ∀ x, Within x e 24 → ¬ W x) (hew : e.toNat + 24 ≤ 2 ^ 64) : VBuilt s v e l := by
  have hhi := hheap.hi
  have hk := formVecOf_frame' hf b.ok he (fun x hx hw ↦ by
    have := b.deep x hx
    rcases hW x hw with h | h <;> omega) hew hheap hmono
  refine ⟨hk.2.1, hk.1.trans b.val, fun x hx ↦ ?_⟩
  rw [hk.2.2] at hx
  have := b.deep x hx
  omega

/-- What a call keeps: the forms and the `Vec` built in the frame's locals, apart from `o`. -/
def Keeps (s u v : MachineState) (o : Word) : Prop :=
  (∀ e f, Built s u e f → (s.getReg .x2).toNat - 144 ≤ e.toNat →
    e.toNat + 24 ≤ (s.getReg .x2).toNat - 48 → Apart e 24 o 24 → Built s v e f) ∧
  (∀ e l, VBuilt s u e l → (s.getReg .x2).toNat - 144 ≤ e.toNat →
    e.toNat + 24 ≤ (s.getReg .x2).toNat - 48 → Apart e 24 o 24 → VBuilt s v e l)

/-- A call building a form at `o` in the frame's locals, its stack below `sp'`. -/
theorem callFrame {s u v : MachineState} (hpre : BytecodePre s) (c : Inv s u) {o : Word}
    {n : Nat}
    (hf : DFrame u v fun a ↦ Within a o 24 ∨ Within a (stackLo u n) n ∨ Within a nextAddr 8 ∨
      Fresh u v a)
    (ho₁ : (s.getReg .x2).toNat - 144 ≤ o.toNat) (ho₂ : o.toNat + 24 ≤ (s.getReg .x2).toNat - 48)
    (hst : ∀ a, Within a (stackLo u n) n →
      (s.getReg .x2).toNat - 1536 ≤ a.toNat ∧ a.toNat < (s.getReg .x2).toNat - 144)
    (hheap : HeapOk v) (hmono : heapNext u ≤ heapNext v) (hp : Preserves u v) :
    Inv s v ∧ Keeps s u v o := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hhv := hheap.hi
  have hhu := c.heap.hi
  have cm := c.mono
  have hW : ∀ x, (Within x o 24 ∨ Within x (stackLo u n) n ∨ Within x nextAddr 8 ∨
      Fresh u v x) → heapEnd ≤ x.toNat ∨ heapNext u ≤ x.toNat := fun x hx ↦ by
    rcases hx with h | h | h | h
    · exact Or.inl (by addr_omega [h, hsb, hab, ho₁, ho₂])
    · have := hst x h; exact Or.inl (by addr_omega [this, hsb, hab])
    · exact Or.inl (by addr_omega [h])
    · exact Or.inr h.1
  have hne (e : Word) (he₁ : (s.getReg .x2).toNat - 144 ≤ e.toNat)
      (he₂ : e.toNat + 24 ≤ (s.getReg .x2).toNat - 48) (hap : Apart e 24 o 24) :
      ∀ x, Within x e 24 → ¬ (Within x o 24 ∨ Within x (stackLo u n) n ∨ Within x nextAddr 8 ∨
        Fresh u v x) := fun x hx hw ↦ by
    rcases hw with h | h | h | h
    · addr_omega [hx, h, hap]
    · have := hst x h; addr_omega [hx, this, he₁]
    · addr_omega [hx, h, hsb, hnx, he₁, he₂]
    · simp only [Fresh] at h; addr_omega [hx, h, hsb, hab, hhv, he₁, he₂]
  refine ⟨c.step hpre hf (fun x hx ↦ ?_) hheap hmono (keepRegs_of hp), fun e f b he₁ he₂ hap ↦
    b.step hf c.heap hmono hW (hne e he₁ he₂ hap) (by addr_omega [he₂, hsb]),
    fun e l b he₁ he₂ hap ↦ b.step hf c.heap hmono hW (hne e he₁ he₂ hap) (by addr_omega [he₂, hsb])⟩
  rcases hx with h | h | h | h
  · exact Or.inl (by addr_omega [h, hsb, ho₁, ho₂])
  · have := hst x h; exact Or.inl (by addr_omega [this, hsb])
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨by simp only [Fresh] at h; omega, h.2⟩)

/-- A block writing `k` bytes from `lo` in the frame's locals. -/
theorem Inv.block {s u v : MachineState} (hpre : BytecodePre s) (c : Inv s u) {lo : Word}
    {k : Nat} (hm : MemFrame u v lo k) (hlo : (s.getReg .x2).toNat - 144 ≤ lo.toNat)
    (hk : lo.toNat + k ≤ (s.getReg .x2).toNat - 48) (hp : KeepRegs u v) :
    Inv s v ∧ (∀ e f, Built s u e f → Apart e 24 lo k → e.toNat + 24 ≤ 2 ^ 64 → Built s v e f) ∧
      (∀ e l, VBuilt s u e l → Apart e 24 lo k → e.toNat + 24 ≤ 2 ^ 64 → VBuilt s v e l) ∧
      heapNext v = heapNext u := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]; rw [hm _ (by addr_omega [hnx, hsb, hlo, hk])]
  have hW : ∀ x, Within x lo k → heapEnd ≤ x.toNat ∨ heapNext u ≤ x.toNat :=
    fun x hx ↦ Or.inl (by addr_omega [hx, hsb, hab, hlo, hk])
  refine ⟨c.step hpre hm.dframe (fun x hx ↦ Or.inl (by addr_omega [hx, hsb, hlo, hk]))
    ⟨hn ▸ c.heap.lo, hn ▸ c.heap.hi⟩ hn.ge hp, fun e f b hap hw ↦ b.step hm.dframe c.heap hn.ge hW
      (fun x hx h ↦ by addr_omega [hx, h, hap]) hw,
    fun e l b hap hw ↦ b.step hm.dframe c.heap hn.ge hW
      (fun x hx h ↦ by addr_omega [hx, h, hap]) hw, hn⟩

/-- A block writing nothing. -/
theorem Inv.same {s u v : MachineState} (hpre : BytecodePre s) (c : Inv s u)
    (hm : ∀ a, v.getMem a = u.getMem a) (hp : KeepRegs u v) :
    Inv s v ∧ (∀ e f, Built s u e f → e.toNat + 24 ≤ 2 ^ 64 → Built s v e f) ∧
      (∀ e l, VBuilt s u e l → e.toNat + 24 ≤ 2 ^ 64 → VBuilt s v e l) := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact ⟨c.step hpre (DFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim)
    ⟨hn ▸ c.heap.lo, hn ▸ c.heap.hi⟩ hn.ge hp,
    fun e f b hw ↦ b.step (DFrame.of_same hm fun _ ↦ False) c.heap hn.ge (fun _ h ↦ h.elim)
      (fun _ _ h ↦ h) hw,
    fun e l b hw ↦ b.step (DFrame.of_same hm fun _ ↦ False) c.heap hn.ge (fun _ h ↦ h.elim)
      (fun _ _ h ↦ h) hw⟩

/-! ## The calls -/

/-- `term(o, One, c)`, the monomial's tag at `m`, both in the frame's locals. -/
theorem termCall (hT : TermSpec) {s u0 u : MachineState} (hpre : BytecodePre s) (c : Inv s u)
    (hr : Reaches Image.code u0 u) (hpc : u.pc = 0x800050a8) {o m q : Word}
    (h10 : u.getReg .x10 = o) (h11 : u.getReg .x11 = m) (h12 : u.getReg .x12 = q)
    (htag : u.getMem m = 0)
    (ho₁ : (s.getReg .x2).toNat - 144 ≤ o.toNat) (ho₂ : o.toNat + 24 ≤ (s.getReg .x2).toNat - 48)
    (hm₁ : (s.getReg .x2).toNat - 144 ≤ m.toNat) (hm₂ : m.toNat + 24 ≤ (s.getReg .x2).toNat - 48)
    (ho₈ : o.toNat % 8 = 0) (hm₈ : m.toNat % 8 = 0) (hq : ValidMemRange q 3) (hqn : Apart q 24 nextAddr 8)
    (hqs : Apart q 24 (s.getReg .x2 - 224) 80) :
    ∃ v, Reaches Image.code u0 v ∧ ((v.pc = returnAddress u ∧ Inv s v ∧
      Built s v o (.term .one (eAt u q)) ∧ Keeps s u v o) ∨ Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hterm : TermPre u := {
    heap := c.heap
    stack := hpre.stack.inner (k := 144) x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [h10]; valid_sub hpre.stack.valid [hsb, ho₁, ho₂, ho₈]
    mono := by rw [h11]; valid_sub hpre.stack.valid [hsb, hm₁, hm₂, hm₈]
    coeff := by rw [h12]; exact hq
    monoOk := by rw [h11]; simp only [MonoOk, htag]; decide
    outFree := by rw [h10]; addr_omega [hsb, hab, hnx, ho₁, ho₂]
    monoNext := by rw [h11]; addr_omega [hsb, hnx, hm₁, hm₂]
    coeffNext := by rw [h12]; exact hqn
    outStack := by rw [h10]; addr_omega [hsb, x2, ho₁, ho₂]
    monoStack := by rw [h11]; addr_omega [hsb, x2, hm₁, hm₂]
    coeffStack := by rw [h12]; addr_omega [hsb, x2, hqs] }
  obtain ⟨v, hrv, ⟨hpcv, hpres, hnew, hval⟩ | hdead⟩ := hT.call hr hpc hterm
  swap
  · exact ⟨v, hrv, Or.inr hdead⟩
  rw [h10] at hnew hval
  rw [h11, h12] at hval
  obtain ⟨cv, kv⟩ := callFrame hpre c hnew.frame ho₁ ho₂ (fun a h ↦ by addr_omega [h, hsb, x2])
    hnew.heap hnew.mono hpres
  have cm := c.mono
  refine ⟨v, hrv, Or.inl ⟨hpcv, cv, ⟨hnew.ok, ?_, fun x hx ↦ ?_⟩, kv⟩⟩
  · rw [hval, monoOf, htag]; rfl
  · have hb := hnew.fresh
    simp only [NewBuf, formBuf, Within] at hb hx
    omega

/-- `col(o, a1, a2)`, `o` in the frame's locals. -/
theorem colCall (hC : ColSpec) {s u0 u : MachineState} (hpre : BytecodePre s) (c : Inv s u)
    (hr : Reaches Image.code u0 u) (hpc : u.pc = 0x80004b34) {o : Word}
    (h10 : u.getReg .x10 = o) (ho₁ : (s.getReg .x2).toNat - 144 ≤ o.toNat)
    (ho₂ : o.toNat + 24 ≤ (s.getReg .x2).toNat - 48) (ho₈ : o.toNat % 8 = 0) :
    ∃ v, Reaches Image.code u0 v ∧ ((v.pc = returnAddress u ∧ Inv s v ∧
      Built s v o (colRust (u.getReg .x11).toNat (u.getReg .x12).toNat) ∧ Keeps s u v o) ∨
      Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hcol : ColPre u := {
    heap := c.heap
    stack := hpre.stack.inner (k := 144) x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [h10]; valid_sub hpre.stack.valid [hsb, ho₁, ho₂, ho₈]
    outFree := by rw [h10]; addr_omega [hsb, hab, hnx, ho₁, ho₂]
    outStack := by rw [h10]; addr_omega [hsb, x2, ho₁, ho₂]
    rodata := c.rodata }
  obtain ⟨v, hrv, ⟨hpcv, hpres, hnew, hval⟩ | hdead⟩ := hC.call hr hpc hcol
  swap
  · exact ⟨v, hrv, Or.inr hdead⟩
  rw [h10] at hnew hval
  obtain ⟨cv, kv⟩ := callFrame hpre c hnew.frame ho₁ ho₂ (fun a h ↦ by addr_omega [h, hsb, x2])
    hnew.heap hnew.mono hpres
  have cm := c.mono
  refine ⟨v, hrv, Or.inl ⟨hpcv, cv, ⟨hnew.ok, hval, fun x hx ↦ ?_⟩, kv⟩⟩
  have hb := hnew.fresh
  simp only [NewBuf, formBuf, Within] at hb hx
  omega

theorem trap : Image.code.fetch 0x80004d0c = none :=
  Option.isNone_iff_eq_none.mp (by decide +kernel)

theorem shl24 (x : Word) : (x <<< 4) + (x <<< 3) = BitVec.ofNat 64 (24 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega

/-- The operands' header is kept: it misses every scratch write. -/
theorem Inv.ops {s u : MachineState} (hpre : BytecodePre s) (c : Inv s u) {k : Nat}
    (hk : k + 8 ≤ 24) :
    u.getMem (s.getReg .x13 + BitVec.ofNat 64 k) = s.getMem (s.getReg .x13 + BitVec.ofNat 64 k) := by
  have hof := hpre.opsFree
  have hos := hpre.opsStack
  have hob := ValidMemRange.bounds hpre.ops (by decide)
  simp only [bytecodeStack, countedStack, colStack, powStack, Contracts.mulStack,
    Nat.reduceAdd] at hos
  have hhu := c.heap.hi
  have hof1 := hof.1
  have hof2 := hof.2
  exact c.frame.getMem_of (fun x hx hw ↦ by
    simp only [Scratch, Fresh] at hw
    rcases hw with hw | hw | hw <;> addr_omega [hx, hw, hof1, hof2, hos, hob, hk, hhu])
    (by addr_omega [hob, hk])

/-- `spec_extend(sp' + 48, p, p + 24 n)`: the `Vec` built at `sp' + 48` grows by the `n` forms
from `p`, which miss its buffer. -/
theorem extendCall (hS : SpecExtendSpec) {s u0 u : MachineState} (hpre : BytecodePre s)
    (c : Inv s u) (hr : Reaches Image.code u0 u) (hpc : u.pc = 0x80011db8) {l : List FormRust}
    (vb : VBuilt s u (s.getReg .x2 - 96) l) {p : Word} {n : Nat}
    (h10 : u.getReg .x10 = s.getReg .x2 - 96) (h11 : u.getReg .x11 = p)
    (h12 : u.getReg .x12 = p + BitVec.ofNat 64 (24 * n)) (hsrc : ValidMemRange p (3 * n))
    (hok : FormsOk u p n) (hfree : Outside u p (24 * n))
    (hstk : Apart p (24 * n) (stackLo s 1536) 1536)
    (hsep : ∀ x, (Within x p (24 * n) ∨ formsDeep u p n x) →
      ¬ formVecBuf u (s.getReg .x2 - 96) x)
    (hpl : p.toNat + 24 * n < 2 ^ 64) :
    ∃ v, Reaches Image.code u0 v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Inv s v ∧
      VBuilt s v (s.getReg .x2 - 96) (l ++ formsAt u p n)) ∨ Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hhi := c.heap.hi
  have cm := c.mono
  have hd : (u.getReg .x12).toNat - (u.getReg .x11).toNat = 24 * n := by
    rw [h11, h12]; addr_omega [hpl]
  have hcnt : ((u.getReg .x12).toNat - (u.getReg .x11).toNat) / 24 = n := by rw [hd]; omega
  have hse : SpecExtendPre u := {
    heap := c.heap
    stack := hpre.stack.inner (k := 144) x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    self := by rw [h10]; valid_sub hpre.stack.valid [hsb]
    ok := by rw [h10]; exact vb.ok
    bounds := by rw [h11, h12]; addr_omega [hpl]
    whole := by rw [hd]; omega
    src := by rw [hd, h11, show 24 * n / 8 = 3 * n by omega]; exact hsrc
    srcOk := by rw [hcnt, h11]; exact hok
    selfFree := by rw [h10]; addr_omega [hsb, hab, hnx]
    srcFree := by rw [hd, h11]; exact hfree
    selfStack := by rw [h10]; addr_omega [hsb, x2]
    srcStack := by rw [hd, h11]; addr_omega [hstk, hsb, x2]
    apart := by
      rw [hcnt, hd, h11, h10]
      intro x hx h
      rcases h with h | h
      · rcases hx with hx | ⟨i, hi, hx⟩
        · addr_omega [hx, h, hstk, hsb]
        · have := ((hok i hi).buf_below hx).2; addr_omega [this, h, hsb, hab, hhi]
      · exact hsep x hx h
    header := by
      rw [h10]
      intro x hx hd'
      have := (vb.deep x hd').2
      addr_omega [hx, this, hhi, hsb, hab] }
  obtain ⟨v, hrv, ⟨hpcv, hpres, hpost⟩ | hdead⟩ := hS.call hr hpc hse
  swap
  · exact ⟨v, hrv, Or.inr hdead⟩
  have hval := hpost.value
  have hok' := hpost.ok
  have hdeep := hpost.deep
  have hfr := hpost.frame
  rw [h10] at hval hok' hdeep hfr
  rw [hcnt, h11, vb.val] at hval
  have hm' := hpost.mono
  refine ⟨v, hrv, Or.inl ⟨hpcv, hpres, c.step hpre hfr (fun x h ↦ ?_) hpost.heap hm' (keepRegs_of hpres),
    hok', hval, fun x hx ↦ ?_⟩⟩
  · rcases h with h | h | h | h | h
    · exact Or.inl (by addr_omega [h, hsb])
    · exact Or.inr (Or.inr ⟨(vb.deep x (Or.inl h)).1, by have := (vb.deep x (Or.inl h)).2; omega⟩)
    · exact Or.inl (by addr_omega [h, hsb, x2])
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨by simp only [Fresh] at h; omega, h.2⟩)
  · rcases hdeep x hx with h | h
    · have := vb.deep x h; omega
    · simp only [Fresh] at h; omega

end Rv64Verifier.Layout.Bytecode
