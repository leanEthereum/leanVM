import Rv64Verifier.Proofs.Layout.ContractsArith
import Rv64Verifier.Proofs.Layout.LimbSite
import Rv64Verifier.Blocks.F19

/-!
# `flushes_arith`, at `0x8000547c`: what its phases keep

```rust
fn flushes_arith(opcode: usize, multiply: bool) -> Flushes {
    let mut flushes = Flushes::default();
    flushes.state_step(pc, fp);
    let operands = vec![col(o_a, 0), col(o_b, 0), col(o_c, 0), constant(ZERO), constant(ZERO)];
    flushes.bytecode(pc, cnt_bc, opcode, operands);
    flushes.memory_cols(prod(fp, o_a, 0), cnt_a, &va);
    flushes.memory_cols(prod(fp, o_b, 0), cnt_b, &vb);
    let result = if multiply { /* TOWER_LANES' sums of products */ } else { /* col + col */ };
    flushes.memory(prod(fp, o_c, 0), cnt_c, &result);
    flushes
}
```

compiled (`Blocks/F19.lean`), `sp'` the entry's `sp - 480`, the saved registers in its top 64
bytes. The `Flushes` is built at `sp' + 8` and copied to `a0` on return. Every phase keeps `Inv`;
a form built is `Held` with its buffer's bounds, the `Flushes` `FHeld`.
-/

namespace Rv64Verifier.Layout.Arith
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.Limb (Held)

/-- The stack's bounds. -/
theorem facts {s : MachineState} (hpre : FlushesArithPre s) :
    (0x20 + 2224 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (stackLo s 2224).toNat = (s.getReg .x2).toNat - 2224) ∧
    heapEnd ≤ (stackLo s 2224).toNat ∧ Apart (stackLo s 2224) 2224 nextAddr 8 ∧
    Apart (stackLo s 2224) 2224 rodataStart rodataSize := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hro := hpre.stack.rodata
  simp only [flushesArithStack, memoryColsStack, memoryStack, countedStack, colStack, powStack,
    Contracts.mulStack, Nat.reduceAdd] at hsb hab hnx hro
  exact ⟨hsb, hab, hnx, hro⟩

theorem stackValid {s : MachineState} (hpre : FlushesArithPre s) :
    ValidMemRange (stackLo s 2224) 278 := by
  simpa only [flushesArithStack, memoryColsStack, memoryStack, countedStack, colStack, powStack,
    Contracts.mulStack, Nat.reduceAdd] using hpre.stack.valid

/-- The stack lies above `.rodata`'s start. -/
theorem stack_high {s : MachineState} (hpre : FlushesArithPre s) :
    0xa0000000 ≤ (stackLo s 2224).toNat := by
  obtain ⟨hsb, hab, -, -⟩ := facts hpre
  have h := (Sym.validAccess_eight _).mp (validAccess_of_dword (stackValid hpre 1 (by decide)))
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h
  simp only [heapEnd] at hab
  omega

/-- What every phase keeps, from the entry `s` to `u`. -/
structure Inv (s u : MachineState) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 480
  x8 : u.getReg .x8 = s.getReg .x10
  regs : ∀ r ∈ [Reg.x23, .x24, .x25, .x26, .x27], u.getReg r = s.getReg r
  ra : u.getMem (s.getReg .x2 - 8) = s.getReg .x1
  s0 : u.getMem (s.getReg .x2 - 16) = s.getReg .x8
  s1 : u.getMem (s.getReg .x2 - 24) = s.getReg .x9
  s2 : u.getMem (s.getReg .x2 - 32) = s.getReg .x18
  s3 : u.getMem (s.getReg .x2 - 40) = s.getReg .x19
  s4 : u.getMem (s.getReg .x2 - 48) = s.getReg .x20
  s5 : u.getMem (s.getReg .x2 - 56) = s.getReg .x21
  s6 : u.getMem (s.getReg .x2 - 64) = s.getReg .x22
  heap : HeapOk u
  mono : heapNext s ≤ heapNext u
  rodata : RodataOk u
  frame : DFrame s u (Scratch s u (stackLo s 2224) 2224)

/-- The registers `Inv` tracks. -/
def KeepRegs (u v : MachineState) : Prop :=
  ∀ r ∈ [Reg.x2, .x8, .x23, .x24, .x25, .x26, .x27], v.getReg r = u.getReg r

theorem keepRegs_of {u v : MachineState} (h : Preserves u v) : KeepRegs u v :=
  fun r hr ↦ h r (mem_of_mem hr _)

/-- A step that writes only the stack below the saved registers, `NEXT` and the heap allocated
since the entry keeps `Inv`. -/
theorem Inv.step {s u v : MachineState} (hpre : FlushesArithPre s) (c : Inv s u) {W : Word → Prop}
    (hf : DFrame u v W)
    (hW : ∀ x, W x → Within x (stackLo s 2224) 2160 ∨ Within x nextAddr 8 ∨ Fresh s v x)
    (hheap : HeapOk v) (hmono : heapNext u ≤ heapNext v) (hr : KeepRegs u v) : Inv s v := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hhv := hheap.hi
  have cm := c.mono
  have hslot (a : Word) (ha₁ : (s.getReg .x2).toNat - 64 ≤ a.toNat)
      (ha₂ : a.toNat + 8 ≤ (s.getReg .x2).toNat) : v.getMem a = u.getMem a :=
    hf.getMem_of (fun x hx hw ↦ by
      rcases hW x hw with h | h | h
      · addr_omega [hx, h, hsb, ha₁, ha₂]
      · addr_omega [hx, h, hsb, hnx, ha₁, ha₂]
      · simp only [Fresh] at h; addr_omega [hx, h, hsb, hab, hhv, ha₁, ha₂])
      (by addr_omega [hsb, ha₂])
  exact {
    x2 := (hr .x2 (by decide)).trans c.x2
    x8 := (hr .x8 (by decide)).trans c.x8
    regs := fun r h ↦ (hr r (mem_of_mem h _)).trans (c.regs r h)
    ra := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.ra
    s0 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s0
    s1 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s1
    s2 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s2
    s3 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s3
    s4 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s4
    s5 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s5
    s6 := (hslot _ (by addr_omega [hsb]) (by addr_omega [hsb])).trans c.s6
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
        · exact Or.inr (Or.inr h) }

/-- A block writing `k` bytes from `lo` in the frame's locals. -/
theorem Inv.block {s u v : MachineState} (hpre : FlushesArithPre s) (c : Inv s u) {lo : Word}
    {k : Nat} (hm : MemFrame u v lo k) (hlo : (s.getReg .x2).toNat - 480 ≤ lo.toNat)
    (hk : lo.toNat + k ≤ (s.getReg .x2).toNat - 64) (hr : KeepRegs u v) :
    Inv s v ∧ heapNext v = heapNext u := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]; rw [hm _ (by addr_omega [hnx, hsb, hlo, hk])]
  exact ⟨c.step hpre hm.dframe (fun x hx ↦ Or.inl (by addr_omega [hx, hsb, hlo, hk]))
    ⟨hn ▸ c.heap.lo, hn ▸ c.heap.hi⟩ hn.ge hr, hn⟩

/-- A block writing nothing. -/
theorem Inv.same {s u v : MachineState} (hpre : FlushesArithPre s) (c : Inv s u)
    (hm : ∀ a, v.getMem a = u.getMem a) (hr : KeepRegs u v) : Inv s v := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact c.step hpre (DFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim)
    ⟨hn ▸ c.heap.lo, hn ▸ c.heap.hi⟩ hn.ge hr

/-! ## Values held -/

/-- A held form is kept by a step whose writes miss its header and its buffer's bounds. -/
theorem keepHeld {u v : MachineState} {e : Word} {f : FormRust} {l h : Nat} (b : Held u e f l h)
    {W : Word → Prop} (hf : DFrame u v W) (hheap : HeapOk u) (hmono : heapNext u ≤ heapNext v)
    (hW : ∀ x, W x → l ≤ x.toNat → h ≤ x.toNat) (he : ∀ x, Within x e 24 → ¬ W x)
    (hew : e.toNat + 24 ≤ 2 ^ 64) : Held v e f l h := by
  have hk := formOf_frame hf b.ok he (fun x hx hw ↦ by
    have := b.buf x hx
    have := hW x hw this.1
    omega) hew hheap hmono
  refine ⟨hk.2, hk.1.trans b.val, fun x hx ↦ ?_⟩
  rw [formBuf_frame hf he hew] at hx
  exact b.buf x hx

/-- A held form, its header copied from `e'` to `e`. -/
theorem moveHeld {u v : MachineState} {e e' : Word} {f : FormRust} {l h : Nat}
    (b : Held u e' f l h) {W : Word → Prop} (hf : DFrame u v W) (hheap : HeapOk u)
    (hmono : heapNext u ≤ heapNext v) (hW : ∀ x, W x → l ≤ x.toNat → h ≤ x.toNat)
    (h0 : v.getMem e = u.getMem e') (h8 : v.getMem (e + 8) = u.getMem (e' + 8))
    (h16 : v.getMem (e + 16) = u.getMem (e' + 16)) : Held v e f l h := by
  have hk := formOf_move hf b.ok h0 h8 h16 (fun x hx hw ↦ by
    have := b.buf x hx
    have := hW x hw this.1
    omega) hheap hmono
  refine ⟨hk.2.1, hk.1.trans b.val, fun x hx ↦ ?_⟩
  rw [hk.2.2] at hx
  exact b.buf x hx

/-- The `Flushes` at `sp' + 8`, everything it reaches allocated since the entry and below `hi`. -/
structure FHeld (s u : MachineState) (fl : FlushesRust) (hi : Nat) : Prop where
  ok : FlushesOk u (s.getReg .x2 - 472)
  val : flushesOf u (s.getReg .x2 - 472) = fl
  deep : ∀ x, flushesDeep u (s.getReg .x2 - 472) x → heapNext s ≤ x.toNat ∧ x.toNat < hi

theorem FHeld.keep {s u v : MachineState} {fl : FlushesRust} {hi : Nat} (b : FHeld s u fl hi)
    {W : Word → Prop} (hf : DFrame u v W) (hheap : HeapOk u) (hmono : heapNext u ≤ heapNext v)
    (hW : ∀ x, W x → heapNext s ≤ x.toNat → hi ≤ x.toNat)
    (he : ∀ x, Within x (s.getReg .x2 - 472) 48 → ¬ W x)
    (hew : (s.getReg .x2 - 472).toNat + 48 ≤ 2 ^ 64) : FHeld s v fl hi := by
  have hk := flushesOf_frame hf b.ok he (fun x hx hw ↦ by
    have := b.deep x hx
    have := hW x hw this.1
    omega) hew hheap hmono
  refine ⟨hk.2.1, hk.1.trans b.val, fun x hx ↦ ?_⟩
  rw [hk.2.2.1] at hx
  exact b.deep x hx

theorem FHeld.mono {s u : MachineState} {fl : FlushesRust} {hi hi' : Nat} (b : FHeld s u fl hi)
    (h : hi ≤ hi') : FHeld s u fl hi' :=
  ⟨b.ok, b.val, fun x hx ↦ ⟨(b.deep x hx).1, Nat.lt_of_lt_of_le (b.deep x hx).2 h⟩⟩

theorem heldMono {u : MachineState} {e : Word} {f : FormRust} {l h l' h' : Nat}
    (b : Held u e f l h) (hl : l' ≤ l) (hh : h ≤ h') : Held u e f l' h' :=
  ⟨b.ok, b.val, fun x hx ↦ ⟨Nat.le_trans hl (b.buf x hx).1, Nat.lt_of_lt_of_le (b.buf x hx).2 hh⟩⟩

/-- A header in the frame's locals, above the `Flushes`. -/
@[rv_addr] def Loc (s : MachineState) (e : Word) : Prop :=
  (s.getReg .x2).toNat - 424 ≤ e.toNat ∧ e.toNat + 24 ≤ (s.getReg .x2).toNat - 64

/-- A header in the locals, or allocated below `M`. -/
@[rv_addr] def Slot (s : MachineState) (M : Nat) (e : Word) : Prop :=
  Loc s e ∨ (heapStart ≤ e.toNat ∧ e.toNat + 24 ≤ M)

/-- What a step from `u` to `v` keeps: the forms held below `M` whose headers miss the `k` bytes
from `o`, and the `Flushes` held below `M`. -/
def Keeps (s u v : MachineState) (o : Word) (k M : Nat) : Prop :=
  (∀ e f l h, Held u e f l h → h ≤ M → Slot s M e → Apart e 24 o k → Held v e f l h) ∧
  (∀ fl hi, FHeld s u fl hi → hi ≤ M → FHeld s v fl hi)

/-- What a step keeps, from what it writes: `o`'s `k` bytes, in the stack or from `M` on, which
miss the `Flushes`; the stack below the locals; `NEXT`; and the heap from `M` on. -/
theorem keeps_of {s u v : MachineState} (hpre : FlushesArithPre s) (c : Inv s u)
    {W : Word → Prop} (hf : DFrame u v W) (hmono : heapNext u ≤ heapNext v)
    (hhv : heapNext v ≤ heapEnd) {o : Word} {k M : Nat} (hM : M ≤ heapNext u)
    (hW : ∀ x, W x → Within x o k ∨ Within x (stackLo s 2224) 1744 ∨ Within x nextAddr 8 ∨
      (M ≤ x.toNat ∧ x.toNat < heapNext v))
    (hoM : heapEnd ≤ o.toNat ∨ M ≤ o.toNat) (ho : Apart o k (s.getReg .x2 - 472) 48) :
    Keeps s u v o k M := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hhu := c.heap.hi
  refine ⟨fun e f l h b hh hs hap ↦ ?_, fun fl hi b hh ↦ ?_⟩
  · have hb (x : Word) (hx : formBuf u e x) : heapStart ≤ x.toNat ∧ x.toNat < h := by
      have := b.buf x hx
      have := formBuf_below b.ok hx
      omega
    refine keepHeld b hf c.heap hmono (fun x hw hl ↦ ?_) (fun x hx hw ↦ ?_) (by
      rcases hs with hs | hs <;> addr_omega [hs, hsb, hhu, hM])
    · rcases hW x hw with h' | h' | h' | h'
      · simp only [Within] at h'; simp only [heapEnd] at hoM hhu; omega
      · addr_omega [h', hsb, hab, hhu, hh, hM]
      · addr_omega [h', hhu, hh, hM]
      · omega
    · rcases hW x hw with h' | h' | h' | h'
      · addr_omega [hx, h', hap]
      · rcases hs with hs | hs <;> addr_omega [hx, h', hs, hsb, hab, hM, hhu]
      · rcases hs with hs | hs <;> addr_omega [hx, h', hs, hsb, hnx, hhu, hM]
      · rcases hs with hs | hs <;> addr_omega [hx, h', hs, hsb, hab, hhv]
  · refine b.keep hf c.heap hmono (fun x hw hl ↦ ?_) (fun x hx hw ↦ ?_) (by addr_omega [hsb])
    · rcases hW x hw with h' | h' | h' | h'
      · simp only [Within] at h'; simp only [heapEnd] at hoM hhu; omega
      · addr_omega [h', hsb, hab, hhu, hh, hM]
      · addr_omega [h', hhu, hh, hM]
      · omega
    · rcases hW x hw with h' | h' | h' | h'
      · addr_omega [hx, h', ho]
      · addr_omega [hx, h', hsb]
      · addr_omega [hx, h', hsb, hnx]
      · addr_omega [hx, h', hsb, hab, hhv]

end Rv64Verifier.Layout.Arith
