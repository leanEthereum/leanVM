import Rv64Verifier.Proofs.Layout.ContractsKeccak
import Rv64Verifier.Proofs.Layout.MemoryColsBase
import Rv64Verifier.Blocks.F13

/-!
# `flushes_keccak`'s `limb` closure, at `0x80004de4`: what its phases keep

```rust
fn layout_limb(even: Option<usize>, odd: Option<usize>, flag: usize, missing: Option<usize>) -> Form {
    let (a, b) = (even.or(missing), odd.or(missing));
    if a == b {
        return a.map_or(constant(ZERO), |a| col(a, 0));
    }
    Form::sum([a.map(|a| col(a, 0)), a.map(|a| prod(flag, a, 0)), b.map(|b| prod(flag, b, 0))]
        .into_iter().flatten())
}
```

compiled (`Blocks/F13.lean`), `sp'` the entry's `sp - 208`, the saved registers in its top 64 bytes.
Every phase keeps `Inv`; a form built in the locals is `Held` with its buffer's bounds.
-/

namespace Rv64Verifier.Layout.Limb
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Model.LayoutMirror

/-- The stack's bounds. -/
theorem facts {s : MachineState} (hpre : LimbPre s) :
    (0x20 + 1408 ≤ (s.getReg .x2).toNat ∧ (s.getReg .x2).toNat ≤ 0xc0000008 ∧
      (s.getReg .x2).toNat % 16 = 0 ∧ (stackLo s 1408).toNat = (s.getReg .x2).toNat - 1408) ∧
    heapEnd ≤ (stackLo s 1408).toNat ∧ Apart (stackLo s 1408) 1408 nextAddr 8 ∧
    Apart (stackLo s 1408) 1408 rodataStart rodataSize := by
  have hsb := hpre.stack.bounds (by decide) (by decide)
  have hab := hpre.stack.above
  have hnx := hpre.stack.next
  have hro := hpre.stack.rodata
  simp only [limbStack, colStack, powStack, Contracts.mulStack, Nat.reduceAdd] at hsb hab hnx hro
  exact ⟨hsb, hab, hnx, hro⟩

/-- What every phase keeps, from the entry `s` to `u`. -/
structure Inv (s u : MachineState) : Prop where
  x2 : u.getReg .x2 = s.getReg .x2 - 208
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
  frame : DFrame s u (Scratch s u (stackLo s 1408) 1408)

/-- A step that writes only the stack below the saved registers, `NEXT` and the heap it allocates
keeps `Inv`; `x8` and the registers above `x22` are callee-saved. -/
theorem Inv.step {s u v : MachineState} (hpre : LimbPre s) (c : Inv s u) {W : Word → Prop}
    (hf : DFrame u v W)
    (hW : ∀ x, W x → Within x (stackLo s 1408) 1344 ∨ Within x nextAddr 8 ∨ Fresh s v x)
    (hheap : HeapOk v) (hmono : heapNext u ≤ heapNext v)
    (hr : ∀ r ∈ [Reg.x2, .x8, .x23, .x24, .x25, .x26, .x27], v.getReg r = u.getReg r) :
    Inv s v := by
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
theorem Inv.block {s u v : MachineState} (hpre : LimbPre s) (c : Inv s u) {lo : Word}
    {k : Nat} (hm : MemFrame u v lo k) (hlo : (s.getReg .x2).toNat - 208 ≤ lo.toNat)
    (hk : lo.toNat + k ≤ (s.getReg .x2).toNat - 64)
    (hr : ∀ r ∈ [Reg.x2, .x8, .x23, .x24, .x25, .x26, .x27], v.getReg r = u.getReg r) :
    Inv s v := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]; rw [hm _ (by addr_omega [hnx, hsb, hlo, hk])]
  exact c.step hpre hm.dframe (fun x hx ↦ Or.inl (by addr_omega [hx, hsb, hlo, hk]))
    ⟨hn ▸ c.heap.lo, hn ▸ c.heap.hi⟩ hn.ge hr

/-- A block writing nothing. -/
theorem Inv.same {s u v : MachineState} (hpre : LimbPre s) (c : Inv s u)
    (hm : ∀ a, v.getMem a = u.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x8, .x23, .x24, .x25, .x26, .x27], v.getReg r = u.getReg r) :
    Inv s v := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact c.step hpre (DFrame.of_same hm fun _ ↦ False) (fun _ h ↦ h.elim)
    ⟨hn ▸ c.heap.lo, hn ▸ c.heap.hi⟩ hn.ge hr

/-- A form at `e`, its buffer allocated in `[lo, hi)`. -/
structure Held (u : MachineState) (e : Word) (f : FormRust) (lo hi : Nat) : Prop where
  ok : FormOk u e
  val : formOf u e = f
  buf : ∀ x, formBuf u e x → lo ≤ x.toNat ∧ x.toNat < hi

/-- A form held is kept by a step whose writes miss its header and lie in the stack, `NEXT` or
from `hi` on. -/
theorem Held.step {u v : MachineState} {e : Word} {f : FormRust} {lo hi : Nat}
    (b : Held u e f lo hi) {W : Word → Prop} (hf : DFrame u v W) (hheap : HeapOk u)
    (hmono : heapNext u ≤ heapNext v)
    (hW : ∀ x, W x → heapEnd ≤ x.toNat ∨ hi ≤ x.toNat)
    (he : ∀ x, Within x e 24 → ¬ W x) (hew : e.toNat + 24 ≤ 2 ^ 64) : Held v e f lo hi := by
  have hk := formOf_frame hf b.ok he (fun x hx hw ↦ by
    have := b.buf x hx
    have := (b.ok.buf_below hx).2
    have := hheap.hi
    rcases hW x hw with h | h <;> omega) hew hheap hmono
  refine ⟨hk.2, hk.1.trans b.val, fun x hx ↦ ?_⟩
  rw [formBuf_frame hf he hew] at hx
  exact b.buf x hx

/-- A form held, its header copied from `e'` to `e`. -/
theorem Held.move {u v : MachineState} {e e' : Word} {f : FormRust} {lo hi : Nat}
    (b : Held u e' f lo hi) {W : Word → Prop} (hf : DFrame u v W) (hheap : HeapOk u)
    (hmono : heapNext u ≤ heapNext v) (hW : ∀ x, W x → heapEnd ≤ x.toNat ∨ hi ≤ x.toNat)
    (h0 : v.getMem e = u.getMem e') (h8 : v.getMem (e + 8) = u.getMem (e' + 8))
    (h16 : v.getMem (e + 16) = u.getMem (e' + 16)) : Held v e f lo hi := by
  have hk := formOf_move hf b.ok h0 h8 h16 (fun x hx hw ↦ by
    have := b.buf x hx
    have := (b.ok.buf_below hx).2
    have := hheap.hi
    rcases hW x hw with h | h <;> omega) hheap hmono
  refine ⟨hk.2.1, hk.1.trans b.val, fun x hx ↦ ?_⟩
  rw [hk.2.2] at hx
  exact b.buf x hx

theorem Held.same {u v : MachineState} {e : Word} {f : FormRust} {lo hi : Nat}
    (b : Held u e f lo hi) (hheap : HeapOk u) (hm : ∀ a, v.getMem a = u.getMem a)
    (hew : e.toNat + 24 ≤ 2 ^ 64) : Held v e f lo hi := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact b.step (DFrame.of_same hm fun _ ↦ False) hheap hn.ge (fun _ h ↦ h.elim) (fun _ _ h ↦ h) hew

/-- A block writing `k` bytes from `lo` in the frame's locals keeps a form held whose header it
misses, its buffer below `NEXT`. -/
theorem Held.block {s u v : MachineState} {e : Word} {f : FormRust} {l h : Nat}
    (hpre : LimbPre s) (b : Held u e f l h) (c : Inv s u) {lo : Word} {k : Nat}
    (hm : MemFrame u v lo k) (hlo : (s.getReg .x2).toNat - 208 ≤ lo.toNat)
    (hk : lo.toNat + k ≤ (s.getReg .x2).toNat - 64) (he : Apart e 24 lo k)
    (hew : e.toNat + 24 ≤ 2 ^ 64) : Held v e f l h := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]; rw [hm _ (by addr_omega [hnx, hsb, hlo, hk])]
  exact b.step hm.dframe c.heap hn.ge (fun x hx ↦ Or.inl (by addr_omega [hx, hsb, hab, hlo, hk]))
    (fun x hx hw ↦ by addr_omega [hx, hw, he]) hew

/-- A block's copy of a form's header from `e'` to `e`, both in the frame's locals. -/
theorem Held.blockMove {s u v : MachineState} {e e' : Word} {f : FormRust} {l h : Nat}
    (hpre : LimbPre s) (b : Held u e' f l h) (c : Inv s u) {lo : Word} {k : Nat}
    (hm : MemFrame u v lo k) (hlo : (s.getReg .x2).toNat - 208 ≤ lo.toNat)
    (hk : lo.toNat + k ≤ (s.getReg .x2).toNat - 64)
    (h0 : v.getMem e = u.getMem e') (h8 : v.getMem (e + 8) = u.getMem (e' + 8))
    (h16 : v.getMem (e + 16) = u.getMem (e' + 16)) : Held v e f l h := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]; rw [hm _ (by addr_omega [hnx, hsb, hlo, hk])]
  exact b.move hm.dframe c.heap hn.ge (fun x hx ↦ Or.inl (by addr_omega [hx, hsb, hab, hlo, hk]))
    h0 h8 h16

/-- A call building a form at `o` in the frame's locals, its stack below `sp'`: `Inv`, and every
form held in the locals apart from `o`, its buffer below `NEXT`. -/
theorem callFrame {s u v : MachineState} (hpre : LimbPre s) (c : Inv s u) {o : Word} {n : Nat}
    (hf : DFrame u v fun a ↦ Within a o 24 ∨ Within a (stackLo u n) n ∨ Within a nextAddr 8 ∨
      Fresh u v a)
    (ho₁ : (s.getReg .x2).toNat - 208 ≤ o.toNat) (ho₂ : o.toNat + 24 ≤ (s.getReg .x2).toNat - 64)
    (hst : ∀ a, Within a (stackLo u n) n →
      (s.getReg .x2).toNat - 1408 ≤ a.toNat ∧ a.toNat < (s.getReg .x2).toNat - 208)
    (hheap : HeapOk v) (hmono : heapNext u ≤ heapNext v) (hp : Preserves u v) :
    Inv s v ∧ ∀ e f l h, Held u e f l h → h ≤ heapNext u →
      (s.getReg .x2).toNat - 208 ≤ e.toNat → e.toNat + 24 ≤ (s.getReg .x2).toNat - 64 →
      Apart e 24 o 24 → Held v e f l h := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have hhv := hheap.hi
  have hhu := c.heap.hi
  refine ⟨c.step hpre hf (fun x hx ↦ ?_) hheap hmono fun r hr ↦ hp r (mem_of_mem hr _),
    fun e f l h b hh he₁ he₂ hap ↦ ?_⟩
  · rcases hx with h | h | h | h
    · exact Or.inl (by addr_omega [h, hsb, ho₁, ho₂])
    · have := hst x h; exact Or.inl (by addr_omega [this, hsb])
    · exact Or.inr (Or.inl h)
    · have := c.mono; simp only [Fresh] at h ⊢; exact Or.inr (Or.inr ⟨by omega, h.2⟩)
  · refine b.step hf c.heap hmono (fun x hx ↦ ?_) (fun x hx hw ↦ ?_) (by addr_omega [he₂, hsb])
    · rcases hx with h' | h' | h' | h'
      · exact Or.inl (by addr_omega [h', hsb, hab, ho₁, ho₂])
      · have := hst x h'; exact Or.inl (by addr_omega [this, hsb, hab])
      · exact Or.inl (by addr_omega [h'])
      · exact Or.inr (by simp only [Fresh] at h'; omega)
    · rcases hw with h' | h' | h' | h'
      · addr_omega [hx, h', hap]
      · have := hst x h'; addr_omega [hx, this, he₁]
      · addr_omega [hx, h', hsb, hnx, he₁, he₂]
      · simp only [Fresh] at h'; addr_omega [hx, h', hsb, hab, hhv, he₁, he₂]

end Rv64Verifier.Layout.Limb
