import Rv64Verifier.Proofs.Walk.R6M

/-!
# `walk`: the layout calls a cell's `memory_if` makes

`prod` and `col` into a scratch slot, `Form::add_scaled` on a slot's form, each keeping the loop's
state (`KM`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FormOk formOf formBuf flushesDeep OptAt)

/-- `prod(a1, a2, a3)` into the scratch slot `o`. -/
theorem prodCall (hP : Rv64Verifier.Layout.ProdSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ : Nat} {F : LayoutMirror.FlushesRust}
    {o : Word} (hpre : WalkPre s) (h : KM OI s u A k R Q B σ F)
    (hpc : u.pc = 0x80005138) (x10 : u.getReg .x10 = o) (ho : InScr s o) (ho' : InSlot s o 24) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      KM OI s t A k R Q B σ F ∧
      flushesDeep t (s.getReg .x2 - 1488) = flushesDeep u (s.getReg .x2 - 1488) ∧
      Rv64Verifier.Layout.NewForm u t o Rv64Verifier.Layout.colStack ∧
      formOf t o = LayoutMirror.prodRust (u.getReg .x11).toNat (u.getReg .x12).toNat
        (u.getReg .x13).toNat) ∨ Dead Image.code t) := by
  have hn : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  have I := h.m.inv
  have sO := slotW (n := 3) hpre I (o := o) (by simpa [InSlot] using ho') hn
  have pre : Rv64Verifier.Layout.ColPre u := {
    heap := I.heap
    stack := stk_sub hpre I hn (by decide)
    out := by rw [x10]; exact sO.1
    outFree := by rw [x10]; exact sO.2.1
    outStack := by rw [x10]; exact sO.2.2
    rodata := I.rodata hpre }
  obtain ⟨t, hr, ⟨hpct, hp, nf, fv⟩ | hdd⟩ := hP u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hdd⟩
  rw [x10] at nf fv
  have K := KM.call hpre h nf.frame ho hn nf.heap nf.mono (hp .x2 (by decide))
  exact ⟨t, hr, Or.inl ⟨hpct, hp, K.1, K.2, nf, fv⟩⟩

/-- `col(a1, a2)` into the scratch slot `o`. -/
theorem colCall (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ : Nat} {F : LayoutMirror.FlushesRust}
    {o : Word} (hpre : WalkPre s) (h : KM OI s u A k R Q B σ F)
    (hpc : u.pc = 0x80004b34) (x10 : u.getReg .x10 = o) (ho : InScr s o) (ho' : InSlot s o 24) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      KM OI s t A k R Q B σ F ∧
      flushesDeep t (s.getReg .x2 - 1488) = flushesDeep u (s.getReg .x2 - 1488) ∧
      Rv64Verifier.Layout.NewForm u t o Rv64Verifier.Layout.colStack ∧
      formOf t o = LayoutMirror.colRust (u.getReg .x11).toNat (u.getReg .x12).toNat) ∨
      Dead Image.code t) := by
  have hn : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  have I := h.m.inv
  have sO := slotW (n := 3) hpre I (o := o) (by simpa [InSlot] using ho') hn
  have pre : Rv64Verifier.Layout.ColPre u := {
    heap := I.heap
    stack := stk_sub hpre I hn (by decide)
    out := by rw [x10]; exact sO.1
    outFree := by rw [x10]; exact sO.2.1
    outStack := by rw [x10]; exact sO.2.2
    rodata := I.rodata hpre }
  obtain ⟨t, hr, ⟨hpct, hp, nf, fv⟩ | hdd⟩ := hC u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hdd⟩
  rw [x10] at nf fv
  have K := KM.call hpre h nf.frame ho hn nf.heap nf.mono (hp .x2 (by decide))
  exact ⟨t, hr, Or.inl ⟨hpct, hp, K.1, K.2, nf, fv⟩⟩

/-- A callee writing a slot `o`, heap from `L` on, its stack, `NEXT` and fresh heap keeps a form
in another slot whose buffer lies below `L`. -/
theorem SF.call' {s u t : MachineState} {o o' : Word} {n L : Nat} {f : LayoutMirror.FormRust}
    {lo hi : Nat} (hpre : WalkPre s) (h : Inv s u) (hf : SF u o' f lo hi)
    (fr : Rv64Verifier.Layout.DFrame u t fun a ↦ Within a o 24 ∨
      (L ≤ a.toNat ∧ a.toNat < heapNext u) ∨ Within a (stackLo u n) n ∨ Within a nextAddr 8 ∨
      Fresh u t a) (hn : n ≤ 8736)
    (ho : InSlot s o 24) (ho' : InSlot s o' 24)
    (hoo : o.toNat + 24 ≤ o'.toNat ∨ o'.toNat + 24 ≤ o.toNat) (hhi : hi ≤ L)
    (hL : L ≤ heapNext u) (hv : HeapOk t) (mono : heapNext u ≤ heapNext t) : SF t o' f lo hi := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨o1, o2, -⟩ := ho
  obtain ⟨p1, p2, -⟩ := ho'
  have hu := h.heap.hi
  have ht := hv.hi
  simp only [heapEnd, heapNext] at hu ht
  refine hf.frame fr (fun x hx hw ↦ ?_) (fun x hx1 hx2 hw ↦ ?_) (by addr_omega [p2, hb1]) h.heap mono
  · simp only [Within] at hx
    rcases hw with hw | hw | hw | hw | hw
    · simp only [Within] at hw; omega
    · simp only [heapNext] at hw; addr_omega [hx, hw, hb1, p1, p2, hu]
    · rw [stackLo_callee h] at hw; simp only [Within] at hw; addr_omega [hx, hw, hb1, hn, p1, p2]
    · simp only [Within] at hw; addr_omega [hx, hw, hb1, p1, p2]
    · simp only [Fresh, heapNext] at hw; addr_omega [hx, hw, hb1, p1, p2, hu, ht]
  · have hh : hi ≤ heapNext u := le_trans hhi hL
    simp only [heapNext] at hh
    rcases hw with hw | hw | hw | hw | hw
    · simp only [Within] at hw; addr_omega [hw, hb1, o1, o2, hx2, hh, hu]
    · omega
    · rw [stackLo_callee h] at hw; simp only [Within] at hw; addr_omega [hw, hb1, hn, hx2, hh, hu]
    · simp only [Within] at hw; addr_omega [hw, hx2, hh, hu]
    · simp only [Fresh, heapNext] at hw; omega

/-- `self.add_scaled(other, ONE)`: `self` the form at the scratch slot `o`, `other` the
one-term form at the slot `q`, allocated after `self`'s buffer. -/
theorem ascCall (hA : Rv64Verifier.Layout.AddScaledSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {σ : Nat} {F : LayoutMirror.FlushesRust}
    {o q : Word} {f g : LayoutMirror.FormRust} {lo hi lo' hi' : Nat} (hpre : WalkPre s)
    (h : KM OI s u A k R Q B σ F) (hpc : u.pc = 0x800119cc) (x10 : u.getReg .x10 = o)
    (ho : InScr s o) (ho' : InSlot s o 24) (hq : InSlot s q 24) (hf : SF u o f lo hi)
    (hg : SF u q g lo' hi') (hlen : (vecLen u q).toNat = 1) (hhi : hi ≤ lo') (hlohi : lo ≤ hi)
    (hlo : ∀ x, flushesDeep u (s.getReg .x2 - 1488) x → x.toNat < lo) (hB : B ≤ lo)
    (x11 : u.getReg .x11 = vecPtr u q) (x12 : u.getReg .x12 = vecLen u q)
    (x13 : u.getReg .x13 = 0xa00000b0) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      KM OI s t A k R Q B σ F ∧
      flushesDeep t (s.getReg .x2 - 1488) = flushesDeep u (s.getReg .x2 - 1488) ∧
      SF t o (f.add g) lo (heapNext t) ∧ HeapOk t ∧ heapNext u ≤ heapNext t ∧
      Rv64Verifier.Layout.DFrame u t (fun a ↦ Within a o 24 ∨
        (lo ≤ a.toNat ∧ a.toNat < heapNext u) ∨
        Within a (stackLo u Rv64Verifier.Layout.addScaledStack) Rv64Verifier.Layout.addScaledStack ∨
        Within a nextAddr 8 ∨ Fresh u t a)) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hn : Rv64Verifier.Layout.addScaledStack ≤ 8736 := by decide
  have I := h.m.inv
  have hu := I.heap.hi
  have hu' := I.heap.lo
  simp only [heapEnd, heapStart, heapNext] at hu hu'
  have sO := slotW (n := 3) hpre I (o := o) (by simpa [InSlot] using ho') hn
  obtain ⟨o1, o2, o3⟩ := ho'
  obtain ⟨q1, q2, q3⟩ := hq
  have qraw := hg.ok.vec.raw
  have qlen := hg.ok.vec.len
  simp only [RawVecOk, Buf] at qraw
  rw [hlen] at qlen
  have qbuf : heapStart ≤ (vecPtr u q).toNat ∧ (vecPtr u q).toNat + 48 ≤ heapNext u := by
    rcases qraw.2 with h0 | h0
    · rw [Nat.mul_eq_zero] at h0; omega
    · constructor
      · exact h0.1
      · have := h0.2; nlinarith
  have q0 : formBuf u q (vecPtr u q) := by
    simp only [formBuf, Within]; omega
  have qlo := (hg.buf _ q0).1
  have fbuf (x : Word) (hx : formBuf u o x) : lo ≤ x.toNat ∧ x.toNat < hi := hf.buf x hx
  simp only [heapStart, heapNext] at qbuf
  have hiN : hi ≤ (u.getMem nextAddr).toNat := by omega
  have hab := hpre.stack.above
  rw [stackLo_eq] at hab
  simp only [heapEnd] at hab
  have pre : Rv64Verifier.Layout.AddScaledPre u := {
    heap := I.heap
    stack := stk_sub hpre I hn (by decide)
    self := by rw [x10]; exact sO.1
    ok := by rw [x10]; exact hf.ok
    other := by
      rw [x11, x12, hlen]
      exact Rv64Verifier.Layout.validMemRange_of qraw.1 (Or.inl ⟨by omega, by omega⟩)
    otherTags := by rw [x11, x12]; exact hg.ok.tags
    weight := by rw [x13]; exact Rv64Verifier.Layout.validMemRange_of (by decide) (Or.inr ⟨by decide, by decide⟩)
    rodata := I.rodata hpre
    selfFree := by rw [x10]; exact sO.2.1
    otherFree := by rw [x11, x12, hlen]; exact ⟨Or.inl (by simp only [heapNext]; omega), by addr_omega [qbuf, hu]⟩
    weightFree := by rw [x13]; exact ⟨Or.inr (by decide), by addr_omega []⟩
    selfStack := by rw [x10]; exact sO.2.2
    otherStack := by rw [x11, x12, hlen, stackLo_callee I]; addr_omega [qbuf, hb1, hab, hu]
    weightStack := by rw [x13, stackLo_callee I]; addr_omega [hb1]
    selfOther := by rw [x10, x11, x12, hlen]; addr_omega [qbuf, hb1, o1, hu]
    selfWeight := by rw [x10, x13]; addr_omega [hb1, o1, o2]
    selfRodata := by rw [x10]; addr_omega [hb1, o1, o2]
    buf := fun x hx hw ↦ by
      rw [x10] at hx
      have := fbuf x hx
      rw [x10, x11, x12, hlen, x13] at hw
      rcases hw with hw | hw | hw
      · simp only [Within] at hw; addr_omega [hw, this, hb1, o1, hiN, hu]
      · simp only [Within] at hw; omega
      · simp only [Within] at hw; addr_omega [hw, this, hb1, hiN, hu] }
  obtain ⟨t, hr, ⟨hpct, hp, post⟩ | hdd⟩ := hA u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hdd⟩
  have fr := post.frame
  rw [x10] at fr
  have fr' : Rv64Verifier.Layout.DFrame u t (fun a ↦ Within a o 24 ∨
      (lo ≤ a.toNat ∧ a.toNat < heapNext u) ∨
      Within a (stackLo u Rv64Verifier.Layout.addScaledStack) Rv64Verifier.Layout.addScaledStack ∨
      Within a nextAddr 8 ∨ Fresh u t a) := fr.mono fun a ha ↦ by
    rcases ha with ha | ha | ha | ha | ha
    · exact Or.inl ha
    · have := fbuf a ha; exact Or.inr (Or.inl ⟨this.1, by simp only [heapNext] at *; omega⟩)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ha)))
  have hB' := h.m.bufQ.2.2.2
  have ht := post.heap.hi
  simp only [heapEnd, heapNext] at ht
  have K := h.step hpre fr' (fun a ha ↦ ?_) (fun a ha ↦ ?_) (fun a ha hd ↦ ?_) post.heap post.mono
    (hp .x2 (by decide))
  · refine ⟨t, hr, Or.inl ⟨hpct, hp, K.1, K.2, ⟨?_, ?_, fun x hx ↦ ?_⟩, post.heap, post.mono, fr'⟩⟩
    · rw [← x10]; exact post.ok
    · rw [← x10, post.value, x10, hf.val, x11, x12, x13, Rv64Verifier.Layout.eAt_one (I.rodata hpre),
        ← hg.val]
      rfl
    · rw [← x10] at hx
      rcases post.buf x hx with hx | hx
      · rw [x10] at hx; have := fbuf x hx; have := post.mono; simp only [heapNext] at *; omega
      · simp only [Fresh] at hx; have := post.mono; simp only [heapNext] at *; omega
  · rcases ha with ha | ha | ha | ha | ha
    · have hs := ho a ha
      exact Or.inl (by simp only [Scr, Within] at hs ⊢; rcases hs with c | c | c | c <;> addr_omega [c, hb1])
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by have := post.mono; omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (stackLo_w6 hpre I hn ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ha.2⟩))))
  · rcases ha with ha | ha | ha | ha | ha
    · exact Or.inl (ho a ha)
    · right; simp only [Within]; simp only [heapNext] at ha; addr_omega [ha, hb1, hu]
    · right; rw [stackLo_callee I] at ha; simp only [Within] at ha ⊢; addr_omega [ha, hb1, hn]
    · right; simp only [Within] at ha ⊢; addr_omega [ha, hb1]
    · right; simp only [Fresh, heapNext] at ha; simp only [Within]; addr_omega [ha, hb1, ht]
  · have hdb := (h.fl.ok.deep_below hd).2
    have hl := hlo a hd
    simp only [heapNext] at hdb
    rcases ha with ha | ha | ha | ha | ha
    · have hs := ho a ha
      simp only [Scr, Within] at hs; rcases hs with c | c | c | c <;> addr_omega [c, hb1, hdb, hu]
    · omega
    · rw [stackLo_callee I] at ha; simp only [Within] at ha; addr_omega [ha, hb1, hn, hdb, hu]
    · simp only [Within] at ha; addr_omega [ha, hdb, hu]
    · simp only [Fresh, heapNext] at ha; omega

end Rv64Verifier.Proofs.Walk
