import Rv64Verifier.Proofs.Layout.LimbSite

/-!
# `flushes_keccak`'s `limb` closure: the sum

From `0x80004f28`, the summands `col(a)` at `sp' + 72`, `prod(flag, a)` at `sp' + 48` and
`prod(flag, b)` at `sp' + 24`, each present unless its capacity register (`s5`, `s4`, `s1`) is `-1`
(`Slot`), are added in turn into the sum (`Mid` between the sites), which `0x80005028` writes to
`a0`.
-/

namespace Rv64Verifier.Layout.Limb
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Blocks.F13 Rv64Verifier.Model.LayoutMirror

/-- A summand: absent, its register `-1`, or a form at `e` built before `H`, its register its
capacity, so not `-1`. -/
def Slot (s w : MachineState) (H : Nat) (r : Reg) (e : Word) : Option FormRust → Prop
  | none => w.getReg r = 0xffffffffffffffff
  | some g => g.terms ≠ [] ∧ Held w e g (heapNext s) H ∧ w.getReg r ≠ 0xffffffffffffffff

theorem Held.weaken {u : MachineState} {e : Word} {f : FormRust} {lo hi lo' hi' : Nat}
    (b : Held u e f lo hi) (hl : lo' ≤ lo) (hh : hi ≤ hi') : Held u e f lo' hi' :=
  ⟨b.ok, b.val, fun x hx ↦ by have := b.buf x hx; omega⟩

/-- A form's capacity is not `-1`. -/
theorem cap_ne {u : MachineState} (hheap : HeapOk u) {e : Word} (hok : FormOk u e) :
    u.getMem e ≠ 0xffffffffffffffff := by
  have hraw := hok.vec.raw
  have hhi := hheap.hi
  simp only [RawVecOk, Buf, vecCap] at hraw
  intro h
  rw [h] at hraw
  simp only [heapEnd] at hhi
  rcases hraw.2 with h0 | h0
  · simp at h0
  · have : (0xffffffffffffffff : Word).toNat = 2 ^ 64 - 1 := rfl
    omega

theorem sum_snoc (l : List FormRust) (g : FormRust) :
    FormRust.sum (l ++ [g]) = (FormRust.sum l).add g := by
  simp only [FormRust.sum, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Between the sites, from the start `w` of the sum: the sum `f`, `s2 = sp' + 128`, `s3 = -1`,
`s1`, `s4` and the forms held in the locals below the sum kept. -/
structure Mid (s w z : MachineState) (f : FormRust) : Prop extends Inv s z where
  x18 : z.getReg .x18 = s.getReg .x2 - 80
  x19 : z.getReg .x19 = 0xffffffffffffffff
  x9 : z.getReg .x9 = w.getReg .x9
  x20 : z.getReg .x20 = w.getReg .x20
  acc : Acc s z (heapNext w) f
  hz : heapNext w ≤ heapNext z
  keep : ∀ e g l, Held w e g l (heapNext w) → (s.getReg .x2).toNat - 208 ≤ e.toNat →
    e.toNat + 24 ≤ (s.getReg .x2).toNat - 112 → Held z e g l (heapNext w)

/-- A block writing nothing keeps `Mid`. -/
theorem Mid.same {s w z v : MachineState} {f : FormRust} (hpre : LimbPre s) (m : Mid s w z f)
    (hm : ∀ a, v.getMem a = z.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x8, .x9, .x10, .x13, .x14, .x18, .x19, .x20, .x23, .x24, .x25, .x26, .x27],
      v.getReg r = z.getReg r) : Mid s w v f := by
  obtain ⟨hsb, -⟩ := facts hpre
  have hn : heapNext v = heapNext z := by simp only [heapNext, hm]
  have hzh := m.hz
  exact {
    toInv := m.toInv.same hpre hm fun r h ↦ hr r (mem_of_mem h _)
    x18 := (hr .x18 (by decide)).trans m.x18
    x19 := (hr .x19 (by decide)).trans m.x19
    x9 := (hr .x9 (by decide)).trans m.x9
    x20 := (hr .x20 (by decide)).trans m.x20
    acc := by
      rcases m.acc with ⟨b, a13, a14, a10⟩ | ⟨hf, a13, a14, a10⟩
      · refine Or.inl ⟨hn ▸ b.same m.heap hm (by addr_omega [hsb]), ?_, ?_, ?_⟩
        · rw [hr .x13 (by decide), a13, hm]
        · rw [hr .x14 (by decide), a14, hm]
        · rw [hr .x10 (by decide), a10, hm]
      · exact Or.inr ⟨hf, by rw [hr .x13 (by decide), a13], by rw [hr .x14 (by decide), a14],
          by rw [hr .x10 (by decide), a10]⟩
    hz := by omega
    keep := fun e g l b he₁ he₂ ↦ (m.keep e g l b he₁ he₂).same m.heap hm (by addr_omega [hsb, he₂]) }

/-- After a site, at its reload: the words at `sp' + 96` into `(a3, a4, a0)`. -/
theorem Mid.reload {s w z v : MachineState} {f : FormRust} (hpre : LimbPre s) (c : Inv s z)
    (x18 : z.getReg .x18 = s.getReg .x2 - 80) (x19 : z.getReg .x19 = 0xffffffffffffffff)
    (x9 : z.getReg .x9 = w.getReg .x9) (x20 : z.getReg .x20 = w.getReg .x20)
    (b : Held z (s.getReg .x2 - 112) f (heapNext w) (heapNext z))
    (keep : ∀ e g l, Held w e g l (heapNext w) → (s.getReg .x2).toNat - 208 ≤ e.toNat →
      e.toNat + 24 ≤ (s.getReg .x2).toNat - 112 → Held z e g l (heapNext w))
    (hz : heapNext w ≤ heapNext z) (hm : ∀ a, v.getMem a = z.getMem a)
    (hr : ∀ r ∈ [Reg.x2, .x8, .x9, .x18, .x19, .x20, .x23, .x24, .x25, .x26, .x27],
      v.getReg r = z.getReg r)
    (h10 : v.getReg .x10 = z.getMem (z.getReg .x2 + 112))
    (h13 : v.getReg .x13 = z.getMem (z.getReg .x2 + 96))
    (h14 : v.getReg .x14 = z.getMem (z.getReg .x2 + 104)) : Mid s w v f := by
  obtain ⟨hsb, -⟩ := facts hpre
  have hn : heapNext v = heapNext z := by simp only [heapNext, hm]
  have x2 := c.x2
  exact {
    toInv := c.same hpre hm fun r h ↦ hr r (mem_of_mem h _)
    x18 := (hr .x18 (by decide)).trans x18
    x19 := (hr .x19 (by decide)).trans x19
    x9 := (hr .x9 (by decide)).trans x9
    x20 := (hr .x20 (by decide)).trans x20
    acc := Or.inl ⟨hn ▸ b.same c.heap hm (by addr_omega [hsb]),
      by rw [h13, hm, x2]; congr 1; addr_omega [hsb], by rw [h14, hm, x2]; congr 1; addr_omega [hsb],
      by rw [h10, hm, x2]; congr 1; addr_omega [hsb]⟩
    hz := by omega
    keep := fun e g l b he₁ he₂ ↦ (keep e g l b he₁ he₂).same c.heap hm (by addr_omega [hsb, he₂]) }

end Rv64Verifier.Layout.Limb
