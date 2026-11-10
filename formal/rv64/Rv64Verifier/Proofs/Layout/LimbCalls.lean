import Rv64Verifier.Proofs.Layout.LimbBase

/-!
# `flushes_keccak`'s `limb` closure: its calls

`term`, `col` and `prod` build a form in the frame's locals; `add_scaled` adds one into the sum at
`sp' + 96` (its buffer allocated after every summand's).
-/

namespace Rv64Verifier.Layout.Limb
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Model.LayoutMirror

/-- `col`'s and `prod`'s arguments, the form at `o` in the frame's locals. -/
theorem colPre {s u : MachineState} (hpre : LimbPre s) (c : Inv s u) {o : Word}
    (h10 : u.getReg .x10 = o) (ho₁ : (s.getReg .x2).toNat - 208 ≤ o.toNat)
    (ho₂ : o.toNat + 24 ≤ (s.getReg .x2).toNat - 64) (h8 : o.toNat % 8 = 0) : ColPre u := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  exact {
    heap := c.heap
    stack := hpre.stack.inner (k := 208) x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [h10]; valid_sub hpre.stack.valid [hsb, ho₁, ho₂, h8]
    outFree := by rw [h10]; addr_omega [hsb, hab, hnx, ho₁, ho₂]
    outStack := by rw [h10]; addr_omega [hsb, x2, ho₁, ho₂]
    rodata := c.rodata }

/-- After a call that builds a new form at `o` in the frame's locals, with a stack of `n` bytes
below `sp'`. -/
theorem afterNew {s u v : MachineState} (hpre : LimbPre s) (c : Inv s u) {o : Word} {n : Nat}
    (ho₁ : (s.getReg .x2).toNat - 208 ≤ o.toNat) (ho₂ : o.toNat + 24 ≤ (s.getReg .x2).toNat - 64)
    (hn : n ≤ 1200) (hpres : Preserves u v) (hnew : NewForm u v o n) :
    Inv s v ∧ Held v o (formOf v o) (heapNext u) (heapNext v) ∧
      ∀ e f l h, Held u e f l h → h ≤ heapNext u →
        (s.getReg .x2).toNat - 208 ≤ e.toNat → e.toNat + 24 ≤ (s.getReg .x2).toNat - 64 →
        Apart e 24 o 24 → Held v e f l h := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  obtain ⟨cv, kv⟩ := callFrame hpre c hnew.frame ho₁ ho₂
    (fun a h ↦ by simp only [stackLo] at h; rw [x2] at h; addr_omega [h, hsb, hn]) hnew.heap
    hnew.mono hpres
  refine ⟨cv, ⟨hnew.ok, rfl, fun x hx ↦ ?_⟩, kv⟩
  have hb := hnew.fresh
  simp only [NewBuf, formBuf, Within] at hb hx
  omega

/-- `term(sp', One, ZERO)`, the monomial's tag at `sp' + 96`. -/
theorem termCall (hT : TermSpec) {s u0 u : MachineState} (hpre : LimbPre s) (c : Inv s u)
    (hr : Reaches Image.code u0 u) (hpc : u.pc = 0x800050a8)
    (h10 : u.getReg .x10 = s.getReg .x2 - 208) (h11 : u.getReg .x11 = s.getReg .x2 - 112)
    (h12 : u.getReg .x12 = 0xa0000068) (htag : u.getMem (s.getReg .x2 - 112) = 0) :
    ∃ v, Reaches Image.code u0 v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Inv s v ∧
      Held v (s.getReg .x2 - 208) (constantRust 0) (heapNext u) (heapNext v)) ∨
      Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hterm : TermPre u := {
    heap := c.heap
    stack := hpre.stack.inner (k := 208) x2 (by decide) (by decide) (by decide) (by decide)
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
  obtain ⟨cv, bv, -⟩ := afterNew hpre c (by addr_omega [hsb]) (by addr_omega [hsb])
    (by simp only [termStack]; decide) hpres hnew
  refine ⟨v, hrv, Or.inl ⟨hpcv, hpres, cv, bv.ok, ?_, bv.buf⟩⟩
  rw [hval, monoOf, htag, MemoryCols.eAt_zero c.rodata]; rfl

/-- `ONE` is valid and apart from everything the frame holds. -/
theorem one_valid : ValidMemRange (0xa00000b0 : Word) 3 :=
  validMemRange_of (by decide) (Or.inr ⟨by decide, by decide⟩)

/-- A buffer in the heap is valid. -/
theorem buf_valid {u : MachineState} (hheap : HeapOk u) {e : Word} (hok : FormOk u e) :
    ValidMemRange (vecPtr u e) (6 * (vecLen u e).toNat) ∧
      (6 * (vecLen u e).toNat = 0 ∨ heapStart ≤ (vecPtr u e).toNat ∧
        (vecPtr u e).toNat + 48 * (vecLen u e).toNat ≤ heapNext u) := by
  have hraw := hok.vec.raw
  have hlen := hok.vec.len
  have hhi := hheap.hi
  simp only [RawVecOk, Buf] at hraw
  rcases hraw.2 with h0 | h0
  · have : (vecLen u e).toNat = 0 := by rw [Nat.mul_eq_zero] at h0; omega
    rw [this]
    exact ⟨fun i hi ↦ absurd hi (by omega), Or.inl rfl⟩
  · refine ⟨validMemRange_of hraw.1 (Or.inl ?_), Or.inr ⟨h0.1, by omega⟩⟩
    simp only [heapStart, heapEnd] at h0 hhi
    omega

/-- `add_scaled(sp' + 96, other, ONE)`: the summand at `e`, held below `H`, into the sum, held
from `H` on. -/
theorem addCall (hA : AddScaledSpec) {s u0 u : MachineState} (hpre : LimbPre s) (c : Inv s u)
    (hr : Reaches Image.code u0 u) (hpc : u.pc = 0x800119cc) {e : Word} {f g : FormRust} {H : Nat}
    (h10 : u.getReg .x10 = s.getReg .x2 - 112) (h11 : u.getReg .x11 = vecPtr u e)
    (h12 : u.getReg .x12 = vecLen u e) (h13 : u.getReg .x13 = 0xa00000b0)
    (ba : Held u (s.getReg .x2 - 112) f H (heapNext u)) (bo : Held u e g (heapNext s) H)
    (hH : heapNext s ≤ H) (hHu : H ≤ heapNext u)
    (hg : g.terms ≠ []) :
    ∃ v, Reaches Image.code u0 v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Inv s v ∧
      heapNext u ≤ heapNext v ∧ Held v (s.getReg .x2 - 112) (f.add g) H (heapNext v) ∧
      ∀ e' f' l, Held u e' f' l H → (s.getReg .x2).toNat - 208 ≤ e'.toNat →
        e'.toNat + 24 ≤ (s.getReg .x2).toNat - 64 → Apart e' 24 (s.getReg .x2 - 112) 24 →
        Held v e' f' l H) ∨ Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hhu := c.heap.hi
  have hm := c.mono
  obtain ⟨hov, hob⟩ := buf_valid c.heap bo.ok
  have hlen : (vecLen u e).toNat ≠ 0 := fun h0 ↦ hg (by rw [← bo.val, formOf, termsOf, h0]; rfl)
  replace hob : heapStart ≤ (vecPtr u e).toNat ∧
      (vecPtr u e).toNat + 48 * (vecLen u e).toNat ≤ heapNext u := hob.resolve_left (by omega)
  have hsl : stackLo u addScaledStack = s.getReg .x2 - 1376 := by
    simp only [stackLo, x2, addScaledStack, Contracts.mulStack]; addr_omega [hsb]
  have hbo (x : Word) (hx : Within x (vecPtr u e) (48 * (vecLen u e).toNat)) :
      x.toNat < H := by
    have hl := bo.ok.vec.len
    have := bo.buf x (by simp only [formBuf, Within] at hx ⊢; omega)
    exact this.2
  have hadd : AddScaledPre u := {
    heap := c.heap
    stack := hpre.stack.inner (k := 208) x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    self := by rw [h10]; valid_sub hpre.stack.valid [hsb]
    ok := by rw [h10]; exact ba.ok
    other := by rw [h11, h12]; exact hov
    otherTags := by rw [h11, h12]; exact bo.ok.tags
    weight := by rw [h13]; exact one_valid
    rodata := c.rodata
    selfFree := by rw [h10]; addr_omega [hsb, hab, hnx]
    otherFree := by
      rw [h11, h12]
      exact ⟨Or.inl hob.2, by addr_omega [hob, hhu]⟩
    weightFree := by rw [h13]; addr_omega []
    selfStack := by rw [h10, hsl]; addr_omega [hsb]
    otherStack := by rw [h11, h12, hsl]; addr_omega [hob, hhu, hab, hsb]
    weightStack := by rw [h13, hsl]; addr_omega [hsb, hro]
    selfOther := by rw [h10, h11, h12]; addr_omega [hob, hhu, hab, hsb]
    selfWeight := by rw [h10, h13]; addr_omega [hsb, hro]
    selfRodata := by rw [h10]; addr_omega [hsb, hro]
    buf := fun x hx ↦ by
      rw [h10] at hx
      have hb := ba.buf x hx
      rw [h10, h11, h12, h13]
      rintro (h | h | h)
      · simp only [heapEnd] at hab; addr_omega [h, hb, hsb, hab, hhu]
      · have := hbo x h; omega
      · addr_omega [h, hb, hhu] }
  obtain ⟨v, hrv, ⟨hpcv, hpres, hpost⟩ | hdead⟩ := hA.call hr hpc hadd
  swap
  · exact ⟨v, hrv, Or.inr hdead⟩
  have hf := hpost.frame
  rw [h10, hsl] at hf
  have hhv := hpost.heap.hi
  have hmv := hpost.mono
  -- the writes: the sum's header and buffer, `add_scaled`'s stack, `NEXT`, the new heap
  have hW (x : Word) (hx : Within x (s.getReg .x2 - 112) 24 ∨
      formBuf u (s.getReg .x2 - 112) x ∨ Within x (s.getReg .x2 - 1376) addScaledStack ∨
      Within x nextAddr 8 ∨ Fresh u v x) :
      Within x (stackLo s 1408) 1344 ∨ Within x nextAddr 8 ∨ Fresh s v x := by
    simp only [addScaledStack, Contracts.mulStack] at hx
    rcases hx with h | h | h | h | h
    · exact Or.inl (by addr_omega [h, hsb])
    · have := ba.buf x h; exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inl (by addr_omega [h, hsb])
    · exact Or.inr (Or.inl h)
    · simp only [Fresh] at h; exact Or.inr (Or.inr ⟨by omega, h.2⟩)
  have cv := c.step hpre hf hW hpost.heap hmv fun r hr ↦ hpres r (mem_of_mem hr _)
  refine ⟨v, hrv, Or.inl ⟨hpcv, hpres, cv, hmv, ⟨?_, ?_, fun x hx ↦ ?_⟩, ?_⟩⟩
  · simpa only [h10] using hpost.ok
  · have hv := hpost.value
    rw [h10, h11, h12, h13, ba.val, eAt_one c.rodata] at hv
    rw [hv, FormRust.add]
    congr 1
    rw [← bo.val]; rfl
  · rcases hpost.buf x (by simpa only [h10] using hx) with h | h
    · rw [h10] at h; have := ba.buf x h; exact ⟨this.1, by omega⟩
    · simp only [Fresh] at h; exact ⟨by omega, h.2⟩
  · intro e' f' l b hb₁ hb₂ hap
    refine b.step hf c.heap hmv (fun x hx ↦ ?_) (fun x hx hw ↦ ?_) (by addr_omega [hb₂, hsb])
    · simp only [addScaledStack, Contracts.mulStack] at hx
      rcases hx with h | h | h | h | h
      · exact Or.inl (by addr_omega [h, hsb, hab])
      · exact Or.inr (ba.buf x h).1
      · exact Or.inl (by addr_omega [h, hsb, hab])
      · exact Or.inl (by addr_omega [h])
      · simp only [Fresh] at h; exact Or.inr (by omega)
    · simp only [addScaledStack, Contracts.mulStack] at hw
      rcases hw with h | h | h | h | h
      · addr_omega [hx, h, hap]
      · have := ba.buf x h; simp only [heapEnd] at hab; addr_omega [hx, this, hb₁, hsb, hab, hhu]
      · addr_omega [hx, h, hb₁, hsb]
      · addr_omega [hx, h, hb₁, hb₂, hsb, hnx]
      · simp only [Fresh, heapEnd] at h hab; addr_omega [hx, h, hb₁, hsb, hab, hhv]

end Rv64Verifier.Layout.Limb
