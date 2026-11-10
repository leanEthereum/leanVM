import Rv64Verifier.Proofs.Layout.ArithBase

/-!
# `flushes_arith`: its calls

`col`, `prod` and `term` build a form in the frame's locals or in the operands' buffer;
`add_scaled` adds a form into a sum whose buffer lies below the summand's; `state_step`,
`bytecode`, `memory_cols` and `memory` grow the `Flushes` at `sp' + 8`.
-/

namespace Rv64Verifier.Layout.Arith
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Runtime Rv64Verifier.FieldContracts
  Rv64Verifier.Model.LayoutMirror
open Rv64Verifier.Layout.Limb (Held)

/-- Where a call's output goes: the locals, or a buffer allocated since the entry. -/
@[rv_addr] def Out (s u : MachineState) (o : Word) : Prop :=
  Loc s o ∨ (heapNext s ≤ o.toNat ∧ o.toNat + 24 ≤ heapNext u)

/-- `col`'s and `prod`'s arguments. -/
theorem colPre {s u : MachineState} (hpre : FlushesArithPre s) (c : Inv s u) {o : Word}
    (h10 : u.getReg .x10 = o) (ho : Out s u o) (h8 : o.toNat % 8 = 0) : ColPre u := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hhu := c.heap.hi
  have hlo := hpre.heap.lo
  have cm := c.mono
  exact {
    heap := c.heap
    stack := hpre.stack.inner (k := 480) x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by
      rw [h10]
      rcases ho with ho | ho
      · valid_sub (stackValid hpre) [hsb, ho, h8]
      · exact validMemRange_of h8 (Or.inl (by simp only [heapStart, heapEnd] at hlo hhu; omega))
    outFree := by rw [h10]; rcases ho with ho | ho <;> addr_omega [hsb, hab, hnx, ho, hhu]
    outStack := by rw [h10]; rcases ho with ho | ho <;> addr_omega [hsb, x2, ho, hab, hhu]
    rodata := c.rodata }

/-- After a call that builds a new form at `o` with `n` bytes of stack below `sp'`. -/
theorem afterNew {s u v : MachineState} (hpre : FlushesArithPre s) (c : Inv s u) {o : Word}
    {n M : Nat} (ho : Out s u o) (hM : M ≤ heapNext u) (hoM : heapEnd ≤ o.toNat ∨ M ≤ o.toNat)
    (hn : n ≤ 1744) (hpres : Preserves u v) (hnew : NewForm u v o n) :
    Inv s v ∧ heapNext u ≤ heapNext v ∧ Held v o (formOf v o) (heapNext u) (heapNext v) ∧
      Keeps s u v o 24 M := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hhv := hnew.heap.hi
  have hhu := c.heap.hi
  have hmv := hnew.mono
  have cm := c.mono
  have hst (x : Word) (h : Within x (stackLo u n) n) : Within x (stackLo s 2224) 1744 := by
    simp only [stackLo] at h; rw [x2] at h; addr_omega [h, hsb, hn]
  refine ⟨c.step hpre hnew.frame (fun x hx ↦ ?_) hnew.heap hmv (keepRegs_of hpres), hmv,
    ⟨hnew.ok, rfl, fun x hx ↦ ?_⟩,
    keeps_of hpre c hnew.frame hmv hhv hM (fun x hx ↦ ?_) hoM (by
      rcases ho with ho | ho <;> addr_omega [ho, hsb, hab, hhv, hhu])⟩
  · rcases hx with h | h | h | h
    · rcases ho with ho | ho
      · exact Or.inl (by addr_omega [h, hsb, ho])
      · exact Or.inr (Or.inr ⟨by addr_omega [h, ho], by addr_omega [h, ho, hmv]⟩)
    · exact Or.inl (by have := hst x h; addr_omega [this, hsb])
    · exact Or.inr (Or.inl h)
    · simp only [Fresh] at h ⊢; exact Or.inr (Or.inr ⟨by omega, h.2⟩)
  · have hb := hnew.fresh
    simp only [NewBuf, formBuf, Within] at hb hx
    omega
  · rcases hx with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (hst x h))
    · exact Or.inr (Or.inr (Or.inl h))
    · simp only [Fresh] at h; exact Or.inr (Or.inr (Or.inr ⟨by omega, h.2⟩))

/-- What a call building a form at `o` gives. -/
def NewPost (s u v : MachineState) (o : Word) (f : FormRust) (M : Nat) : Prop :=
  v.pc = returnAddress u ∧ Preserves u v ∧ Inv s v ∧ heapNext u ≤ heapNext v ∧
    Held v o f (heapNext u) (heapNext v) ∧ Keeps s u v o 24 M

/-- `col(o, a1, a2)`. -/
theorem colCall (hC : ColSpec) {s u0 u : MachineState} (hpre : FlushesArithPre s) (c : Inv s u)
    (hr : Reaches Image.code u0 u) (hpc : u.pc = 0x80004b34) {o : Word} {M : Nat}
    (h10 : u.getReg .x10 = o) (ho : Out s u o) (h8 : o.toNat % 8 = 0) (hM : M ≤ heapNext u)
    (hoM : heapEnd ≤ o.toNat ∨ M ≤ o.toNat) :
    ∃ v, Reaches Image.code u0 v ∧ (NewPost s u v o
      (colRust (u.getReg .x11).toNat (u.getReg .x12).toNat) M ∨ Dead Image.code v) := by
  obtain ⟨v, hrv, ⟨hpcv, hpres, hnew, hval⟩ | hdead⟩ := hC.call hr hpc (colPre hpre c h10 ho h8)
  swap
  · exact ⟨v, hrv, Or.inr hdead⟩
  rw [h10] at hnew hval
  obtain ⟨cv, mv, bv, kv⟩ := afterNew hpre c ho hM hoM (by simp only [colStack, powStack]; decide)
    hpres hnew
  exact ⟨v, hrv, Or.inl ⟨hpcv, hpres, cv, mv, hval ▸ bv, kv⟩⟩

/-- `prod(o, a1, a2, a3)`. -/
theorem prodCall (hP : ProdSpec) {s u0 u : MachineState} (hpre : FlushesArithPre s) (c : Inv s u)
    (hr : Reaches Image.code u0 u) (hpc : u.pc = 0x80005138) {o : Word} {M : Nat}
    (h10 : u.getReg .x10 = o) (ho : Out s u o) (h8 : o.toNat % 8 = 0) (hM : M ≤ heapNext u)
    (hoM : heapEnd ≤ o.toNat ∨ M ≤ o.toNat) :
    ∃ v, Reaches Image.code u0 v ∧ (NewPost s u v o
      (prodRust (u.getReg .x11).toNat (u.getReg .x12).toNat (u.getReg .x13).toNat) M ∨
      Dead Image.code v) := by
  obtain ⟨v, hrv, ⟨hpcv, hpres, hnew, hval⟩ | hdead⟩ := hP.call hr hpc (colPre hpre c h10 ho h8)
  swap
  · exact ⟨v, hrv, Or.inr hdead⟩
  rw [h10] at hnew hval
  obtain ⟨cv, mv, bv, kv⟩ := afterNew hpre c ho hM hoM (by simp only [colStack, powStack]; decide)
    hpres hnew
  exact ⟨v, hrv, Or.inl ⟨hpcv, hpres, cv, mv, hval ▸ bv, kv⟩⟩

/-- `term(o, One, ZERO)`, the monomial's tag at `sp' + 80`. -/
theorem termCall (hT : TermSpec) {s u0 u : MachineState} (hpre : FlushesArithPre s) (c : Inv s u)
    (hr : Reaches Image.code u0 u) (hpc : u.pc = 0x800050a8) {o : Word}
    (h10 : u.getReg .x10 = o) (ho : Loc s o) (h8 : o.toNat % 8 = 0)
    (h11 : u.getReg .x11 = s.getReg .x2 - 400) (h12 : u.getReg .x12 = 0xa0000068)
    (htag : u.getMem (s.getReg .x2 - 400) = 0) :
    ∃ v, Reaches Image.code u0 v ∧ (NewPost s u v o (constantRust 0) (heapNext u) ∨
      Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hterm : TermPre u := {
    heap := c.heap
    stack := hpre.stack.inner (k := 480) x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    out := by rw [h10]; valid_sub (stackValid hpre) [hsb, ho, h8]
    mono := by rw [h11]; valid_sub (stackValid hpre) [hsb]
    coeff := by rw [h12]; exact validMemRange_of (by decide) (Or.inr ⟨by decide, by decide⟩)
    monoOk := by rw [h11]; simp only [MonoOk, htag]; decide
    outFree := by rw [h10]; addr_omega [hsb, hab, hnx, ho]
    monoNext := by rw [h11]; addr_omega [hsb, hnx]
    coeffNext := by rw [h12]; addr_omega []
    outStack := by rw [h10]; addr_omega [hsb, x2, ho]
    monoStack := by rw [h11]; addr_omega [hsb, x2]
    coeffStack := by rw [h12]; addr_omega [hsb, x2, hro] }
  obtain ⟨v, hrv, ⟨hpcv, hpres, hnew, hval⟩ | hdead⟩ := hT.call hr hpc hterm
  swap
  · exact ⟨v, hrv, Or.inr hdead⟩
  rw [h10] at hnew hval
  rw [h11, h12] at hval
  obtain ⟨cv, mv, bv, kv⟩ := afterNew hpre c (Or.inl ho) (Nat.le_refl _)
    (Or.inl (by addr_omega [ho, hsb, hab])) (by simp only [termStack]; decide) hpres hnew
  refine ⟨v, hrv, Or.inl ⟨hpcv, hpres, cv, mv, ?_, kv⟩⟩
  rw [hval, monoOf, htag, MemoryCols.eAt_zero c.rodata] at bv
  exact bv

/-- `add_scaled(o, other, ONE)`: the summand at `e`, held from `H` on, into the sum at `o`, held
in `[L, H)`. -/
theorem addCall (hA : AddScaledSpec) {s u0 u : MachineState} (hpre : FlushesArithPre s)
    (c : Inv s u) (hr : Reaches Image.code u0 u) (hpc : u.pc = 0x800119cc) {o e : Word}
    {f g : FormRust} {L H : Nat} (h10 : u.getReg .x10 = o) (h11 : u.getReg .x11 = vecPtr u e)
    (h12 : u.getReg .x12 = vecLen u e) (h13 : u.getReg .x13 = 0xa00000b0) (ho : Loc s o)
    (h8 : o.toNat % 8 = 0) (ba : Held u o f L H) (bo : Held u e g H (heapNext u))
    (hL : heapNext s ≤ L) (hLH : L ≤ H) (hH : H ≤ heapNext u) (hg : g.terms ≠ []) :
    ∃ v, Reaches Image.code u0 v ∧ ((v.pc = returnAddress u ∧ Preserves u v ∧ Inv s v ∧
      heapNext u ≤ heapNext v ∧ Held v o (f.add g) L (heapNext v) ∧ Keeps s u v o 24 L) ∨
      Dead Image.code v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hhu := c.heap.hi
  have hm := c.mono
  obtain ⟨hov, hob⟩ := Limb.buf_valid c.heap bo.ok
  have hlen : (vecLen u e).toNat ≠ 0 := fun h0 ↦ hg (by rw [← bo.val, formOf, termsOf, h0]; rfl)
  replace hob : heapStart ≤ (vecPtr u e).toNat ∧
      (vecPtr u e).toNat + 48 * (vecLen u e).toNat ≤ heapNext u := hob.resolve_left (by omega)
  have hsl : stackLo u addScaledStack = s.getReg .x2 - 1648 := by
    simp only [stackLo, x2, addScaledStack, Contracts.mulStack]; addr_omega [hsb]
  have hbo (x : Word) (hx : Within x (vecPtr u e) (48 * (vecLen u e).toNat)) : H ≤ x.toNat := by
    have hl := bo.ok.vec.len
    exact (bo.buf x (by simp only [formBuf, Within] at hx ⊢; omega)).1
  have hba (x : Word) (hx : formBuf u o x) : L ≤ x.toNat ∧ x.toNat < H := ba.buf x hx
  have hadd : AddScaledPre u := {
    heap := c.heap
    stack := hpre.stack.inner (k := 480) x2 (by decide) (by decide) (by decide) (by decide)
      (by decide)
    self := by rw [h10]; valid_sub (stackValid hpre) [hsb, ho, h8]
    ok := by rw [h10]; exact ba.ok
    other := by rw [h11, h12]; exact hov
    otherTags := by rw [h11, h12]; exact bo.ok.tags
    weight := by rw [h13]; exact Limb.one_valid
    rodata := c.rodata
    selfFree := by rw [h10]; addr_omega [hsb, hab, hnx, ho]
    otherFree := by
      rw [h11, h12]
      exact ⟨Or.inl hob.2, by addr_omega [hob, hhu]⟩
    weightFree := by rw [h13]; addr_omega []
    selfStack := by rw [h10, hsl]; addr_omega [hsb, ho]
    otherStack := by rw [h11, h12, hsl]; addr_omega [hob, hhu, hab, hsb]
    weightStack := by rw [h13, hsl]; addr_omega [hsb, hro]
    selfOther := by rw [h10, h11, h12]; addr_omega [hob, hhu, hab, hsb, ho]
    selfWeight := by rw [h10, h13]; addr_omega [hsb, hro, ho]
    selfRodata := by rw [h10]; addr_omega [hsb, hro, ho]
    buf := fun x hx ↦ by
      rw [h10] at hx
      have hb := hba x hx
      rw [h10, h11, h12, h13]
      rintro (h | h | h)
      · simp only [heapEnd] at hab; addr_omega [h, hb, hsb, hab, hhu, hH, ho]
      · have := hbo x h; omega
      · addr_omega [h, hb, hhu, hH] }
  obtain ⟨v, hrv, ⟨hpcv, hpres, hpost⟩ | hdead⟩ := hA.call hr hpc hadd
  swap
  · exact ⟨v, hrv, Or.inr hdead⟩
  have hf := hpost.frame
  rw [h10, hsl] at hf
  have hhv := hpost.heap.hi
  have hmv := hpost.mono
  have cv := c.step hpre hf (fun x hx ↦ by
    simp only [addScaledStack, Contracts.mulStack] at hx
    rcases hx with h | h | h | h | h
    · exact Or.inl (by addr_omega [h, hsb, ho])
    · have := hba x h; exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inl (by addr_omega [h, hsb])
    · exact Or.inr (Or.inl h)
    · simp only [Fresh] at h; exact Or.inr (Or.inr ⟨by omega, h.2⟩)) hpost.heap hmv
    (keepRegs_of hpres)
  refine ⟨v, hrv, Or.inl ⟨hpcv, hpres, cv, hmv, ⟨?_, ?_, fun x hx ↦ ?_⟩,
    keeps_of hpre c hf hmv hhv (by omega) (fun x hx ↦ ?_) (Or.inl (by addr_omega [ho, hsb, hab]))
      (by addr_omega [ho, hsb])⟩⟩
  · simpa only [h10] using hpost.ok
  · have hv := hpost.value
    rw [h10, h11, h12, h13, ba.val, eAt_one c.rodata] at hv
    rw [hv, FormRust.add]
    congr 1
    rw [← bo.val]; rfl
  · rcases hpost.buf x (by simpa only [h10] using hx) with h | h
    · rw [h10] at h; have := hba x h; exact ⟨this.1, by omega⟩
    · simp only [Fresh] at h; exact ⟨by omega, h.2⟩
  · simp only [addScaledStack, Contracts.mulStack] at hx
    rcases hx with h | h | h | h | h
    · exact Or.inl h
    · have := hba x h; exact Or.inr (Or.inr (Or.inr ⟨this.1, by omega⟩))
    · exact Or.inr (Or.inl (by addr_omega [h, hsb]))
    · exact Or.inr (Or.inr (Or.inl h))
    · simp only [Fresh] at h; exact Or.inr (Or.inr (Or.inr ⟨by omega, h.2⟩))

/-! ## Growing the `Flushes` -/

/-- A callee's `FlushesPre` on the `Flushes` at `sp' + 8`, with `n` bytes of stack. -/
theorem flushesPre {s u : MachineState} (hpre : FlushesArithPre s) (c : Inv s u) {fl : FlushesRust}
    {hi : Nat} (b : FHeld s u fl hi) (h10 : u.getReg .x10 = s.getReg .x2 - 472) {n : Nat}
    (hn : 480 + n ≤ flushesArithStack) (hn8 : n % 8 = 0) (hn0 : 8 ≤ n) : FlushesPre n u := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hn' : n ≤ 1744 := by simp only [flushesArithStack, memoryColsStack, memoryStack,
    countedStack, colStack, powStack, Contracts.mulStack] at hn; omega
  exact {
    heap := c.heap
    stack := hpre.stack.inner (k := 480) x2 hn (by decide) hn8 (by decide) (by decide)
    self := by rw [h10]; valid_sub (stackValid hpre) [hsb]
    ok := by rw [h10]; exact b.ok
    selfFree := by rw [h10]; addr_omega [hsb, hab, hnx]
    selfStack := by rw [h10]; simp only [stackLo]; rw [x2]; addr_omega [hsb, hn']
    rodata := c.rodata }

/-- After a call growing the `Flushes`, with `n` bytes of stack. -/
theorem afterGrow {s u v : MachineState} (hpre : FlushesArithPre s) (c : Inv s u)
    {fl : FlushesRust} {hi : Nat} (b : FHeld s u fl hi) (hhi : hi ≤ heapNext u) {n : Nat}
    (hn : n ≤ 1744) (hpres : Preserves u v)
    (hg : GrowFlushes u v (s.getReg .x2 - 472) n fun _ ↦ False) :
    Inv s v ∧ FHeld s v (flushesOf v (s.getReg .x2 - 472)) (heapNext v) := by
  obtain ⟨hsb, hab, hnx, hro⟩ := facts hpre
  have x2 := c.x2
  have hmv := hg.mono
  have cm := c.mono
  refine ⟨c.step hpre hg.frame (fun x hx ↦ ?_) hg.heap hmv (keepRegs_of hpres),
    ⟨hg.ok, rfl, fun x hx ↦ ?_⟩⟩
  · rcases hx with h | h | h | h | h
    · exact Or.inl (by addr_omega [h, hsb])
    · have := b.deep x (h.imp Or.inl Or.inl)
      exact Or.inr (Or.inr ⟨this.1, by omega⟩)
    · exact Or.inl (by simp only [stackLo] at h; rw [x2] at h; addr_omega [h, hsb, hn])
    · exact Or.inr (Or.inl h)
    · simp only [Fresh] at h ⊢; exact Or.inr (Or.inr ⟨by omega, h.2⟩)
  · rcases hg.deep x hx with h | h | h
    · have := b.deep x h; exact ⟨this.1, by omega⟩
    · exact h.elim
    · simp only [Fresh] at h; exact ⟨by omega, h.2⟩

end Rv64Verifier.Layout.Arith
