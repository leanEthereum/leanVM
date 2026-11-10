import Rv64Verifier.Proofs.Walk.Dr2
import Rv64Verifier.Proofs.Walk.AtJump

/-!
# `walk`: `tables()`, the tools JUMP needs (R8)

`add_scaled` with `other`'s buffer on either side of `self`'s (`ascM8d`); the tables after DEREF's
apart from a frame slot (`l5_off`); JUMP's empty `Flushes` kept (`JE`); a function moving forms into
the `Flushes` under construction keeps `M8` (`M8.growM`); `prod` and `col` into a frame slot with
their frame (`prodF`, `colF`); a form kept across a callee (`SF.cwx`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

/-- A slot apart from the five finished tables. -/
theorem l5_off {s : MachineState} (hpre : WalkPre s) {M n : Nat}
    (h : M ≤ 1416 ∧ (512 + n ≤ M ∨ M ≤ 440)) : ∀ e ∈ L5 s, ∀ a,
      Within a (s.getReg .x2 - BitVec.ofNat 64 M) n → ¬ Within a e.1 72 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro e he a ha hw
  simp only [L5, L4, L3, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases h with ⟨h1, h2 | h2⟩ <;>
    rcases he with rfl | rfl | rfl | rfl | rfl <;> simp only [Within] at ha hw <;>
    addr_omega [ha, hw, hb1, h1, h2]

/-- JUMP's empty `Flushes` at `sp + 1728`. -/
structure JE (s u : MachineState) : Prop where
  ok : FlushesOk u (s.getReg .x2 - 928)
  val : flushesOf u (s.getReg .x2 - 928) = {}
  nd : ∀ x, ¬ flushesDeep u (s.getReg .x2 - 928) x

theorem JE.frame {s u v : MachineState} {w : Word → Prop} (hpre : WalkPre s) (h : JE s u)
    (fr : Rv64Verifier.Layout.DFrame u v w) (hh : ∀ x, Within x (s.getReg .x2 - 928) 48 → ¬ w x)
    (hheap : HeapOk u) (mono : heapNext u ≤ heapNext v) : JE s v := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have G := Rv64Verifier.Layout.flushesOf_frame fr h.ok hh (fun x hx ↦ absurd hx (h.nd x))
    (by addr_omega [hb1]) hheap mono
  exact ⟨G.2.1, by rw [G.1]; exact h.val, fun x hx ↦ h.nd x (by rw [← G.2.2.1]; exact hx)⟩

theorem JE.of_empty {s u : MachineState} (h : EmptyAt u (s.getReg .x2 - 928)) : JE s u := by
  obtain ⟨f0, f8, f16, f24, f32, f40⟩ := h
  obtain ⟨fok, fval, fnd⟩ := flushesOk_empty f0 f8 f16 f24 f32 f40
  exact ⟨fok, fval, fnd⟩

/-- A function growing the `Flushes` at the frame slot `o`, moving into it forms whose buffers lie
from `lo` on. -/
theorem M8.growM {OI : MachineState → Word → List (List Opening) → Prop} {s u t : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o : Word} {F : LayoutMirror.FlushesRust} {lo n : Nat}
    {m : Word → Prop} (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L) (fb : FB u o F lo)
    (hlo : W ≤ lo) (hlo' : lo ≤ heapNext u) (ho : InSlot s o 48)
    (hL : ∀ e ∈ L, ∀ a, Within a o 48 → ¬ Within a e.1 72)
    (g : Rv64Verifier.Layout.GrowFlushes u t o n m) (hm : ∀ x, m x → lo ≤ x.toNat) (hn : n ≤ 8736)
    (sp : t.getReg .x2 = u.getReg .x2) : M8 OI s t A k R Q B Bb W L ∧ FB t o (flushesOf t o) lo := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨o1, o2, o3⟩ := ho
  have hh := g.heap.hi
  have hu := h.m.inv.heap.hi
  have hW := h.bb.2.2.2
  have hBW : B ≤ W := by have := h.bb; omega
  simp only [heapEnd] at hh hu
  have hbuf : ∀ x, Rv64Verifier.Layout.flushesBuf u o x → lo ≤ x.toNat ∧ x.toNat < heapNext u :=
    fun x hx ↦ ⟨fb.deep x (hx.imp Or.inl Or.inl), (fb.ok.buf_below hx).2⟩
  refine ⟨h.step hpre g.frame (fun a ha ↦ ?_) (fun a ha ↦ ?_) g.heap g.mono sp, g.ok, rfl, fun x hx ↦ ?_⟩
  · rcases ha with ha | ha | ha | ha | ha
    · exact Or.inl (by simp only [Within] at ha ⊢; addr_omega [ha, o1, o2, hb1])
    · have := hbuf a ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by have := g.mono; omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (stackLo_w6 hpre h.m.inv hn ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ha.2⟩))))
  · simp only [M8W]
    have slotOf : ∀ e ∈ L, ∀ x : Word, x.toNat < (s.getReg .x2 - 2080).toNat → ¬ Within x e.1 72 :=
      fun e he x hx hw ↦ by
        obtain ⟨e1, -, -⟩ := (h.tabs e he).1; simp only [Within] at hw; omega
    rcases ha with ha | ha | ha | ha | ha
    · refine ⟨?_, ?_, ?_, ?_, fun e he ↦ hL e he a ha⟩ <;> simp only [Within] at ha ⊢ <;>
        addr_omega [ha, o1, o2, hb1, hW, hu]
    · have := hbuf a ha
      refine ⟨by omega, ?_, ?_, ?_, fun e he ↦ slotOf e he a (by addr_omega [this, hb1, hu])⟩ <;>
        simp only [Within] <;> addr_omega [this, hb1, hu]
    · rw [stackLo_callee h.m.inv] at ha
      refine ⟨?_, ?_, ?_, ?_, fun e he ↦ ?_⟩ <;> simp only [Within] at ha ⊢
      all_goals first
        | addr_omega [ha, hb1, hn, hW, hu]
        | (obtain ⟨e1, -, -⟩ := (h.tabs e he).1; intro hw; addr_omega [ha, hb1, hn, e1, hw])
    · refine ⟨?_, ?_, ?_, ?_, fun e he ↦ slotOf e he a (by simp only [Within, nextAddr] at ha; addr_omega [ha, hb1])⟩ <;>
        simp only [Within, nextAddr] at ha ⊢ <;> addr_omega [ha, hb1, hW, hu]
    · simp only [Fresh] at ha
      refine ⟨by omega, ?_, ?_, ?_, fun e he ↦ slotOf e he a (by addr_omega [ha, hb1, hh])⟩ <;>
        simp only [Within] <;> addr_omega [ha, hb1, hh]
  · rcases g.deep x hx with hd | hd | hd
    · exact fb.deep x hd
    · exact hm x hd
    · simp only [Fresh] at hd; omega

set_option maxRecDepth 8192 in
/-- `ascM8`, `other`'s buffer apart from `self`'s either way. -/
theorem ascM8d (hA : Rv64Verifier.Layout.AddScaledSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o q : Word} {f g : LayoutMirror.FormRust}
    {lo hi lo' hi' : Nat} (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L)
    (hpc : u.pc = 0x800119cc) (x10 : u.getReg .x10 = o) (ho : InSlot s o 24)
    (hL : ∀ e ∈ L, ∀ a, Within a o 24 → ¬ Within a e.1 72) (hf : SF u o f lo hi)
    (hg : SF u q g lo' hi') (hlen : (vecLen u q).toNat = 1) (hdis : hi' ≤ lo ∨ hi ≤ lo')
    (hhiN : hi ≤ heapNext u) (hloN : lo ≤ heapNext u) (hWl : W ≤ lo)
    (x11 : u.getReg .x11 = vecPtr u q) (x12 : u.getReg .x12 = vecLen u q)
    (x13 : u.getReg .x13 = 0xa00000b0) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      M8 OI s t A k R Q B Bb W L ∧ SF t o (f.add g) lo (heapNext t) ∧ heapNext u ≤ heapNext t ∧
      Rv64Verifier.Layout.DFrame u t (fun a ↦ CW u t o Rv64Verifier.Layout.addScaledStack a ∨
        (lo ≤ a.toNat ∧ a.toNat < hi))) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hn : Rv64Verifier.Layout.addScaledStack ≤ 8736 := by decide
  have I := h.m.inv
  have hu := I.heap.hi
  have hu' := I.heap.lo
  simp only [heapEnd, heapStart, heapNext] at hu hu' hhiN hloN
  have hS := slotOk hpre h ho hL
  have sO := slotW (n := 3) hpre I (o := o) (by simpa [InSlot] using ho) hn
  obtain ⟨o1, o2, o3⟩ := ho
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
  simp only [heapStart, heapNext] at qbuf
  have q47 : (vecPtr u q).toNat + 48 ≤ hi' := by
    have hx : formBuf u q (vecPtr u q + 47) := by
      simp only [formBuf, Within]; addr_omega [qbuf, qlen, hu]
    have := (hg.buf _ hx).2
    addr_omega [this, qbuf, hu]
  have q0 : lo' ≤ (vecPtr u q).toNat := by
    have hx : formBuf u q (vecPtr u q) := by
      simp only [formBuf, Within]; addr_omega [qbuf, qlen, hu]
    exact (hg.buf _ hx).1
  have fbuf (x : Word) (hx : formBuf u o x) : lo ≤ x.toNat ∧ x.toNat < hi := hf.buf x hx
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
      · simp only [Within] at hw; addr_omega [hw, this, hb1, o1, hhiN, hu]
      · simp only [Within] at hw; rcases hdis with hd | hd <;> omega
      · simp only [Within] at hw; addr_omega [hw, this, hb1, hhiN, hu] }
  obtain ⟨t, hr, ⟨hpct, hp, post⟩ | hdd⟩ := hA u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hdd⟩
  have fr := post.frame
  rw [x10] at fr
  have fr' : Rv64Verifier.Layout.DFrame u t (fun a ↦ CW u t o Rv64Verifier.Layout.addScaledStack a ∨
      (lo ≤ a.toNat ∧ a.toNat < hi)) := fr.mono fun a ha ↦ by
    rcases ha with ha | ha | ha | ha | ha
    · exact Or.inl (Or.inl ha)
    · exact Or.inr (fbuf a ha)
    · exact Or.inl (Or.inr (Or.inl ha))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr ha)))
  have hb := h.bb
  have hW := h.bb.2.2.2
  have hBu := h.m.bufQ.2.2.2
  have hBW : B ≤ W := by omega
  simp only [heapNext] at hW hBu
  have ht := post.heap.hi
  have mo := post.mono
  simp only [heapEnd, heapNext] at ht mo
  have M := h.step hpre fr' (fun a ha ↦ ?_) (fun a ha ↦ ?_) post.heap post.mono (hp.reg .x2)
  · refine ⟨t, hr, Or.inl ⟨hpct, hp, M, ⟨?_, ?_, fun x hx ↦ ?_⟩, post.mono, fr'⟩⟩
    · rw [← x10]; exact post.ok
    · rw [← x10, post.value, x10, hf.val, x11, x12, x13, Rv64Verifier.Layout.eAt_one (I.rodata hpre),
        ← hg.val]
      rfl
    · rw [← x10] at hx
      rcases post.buf x hx with hx | hx
      · rw [x10] at hx; have := fbuf x hx; simp only [heapNext]; omega
      · simp only [Fresh, heapNext] at hx ⊢; omega
  · rcases ha with (ha | ha | ha | ha) | ha
    · exact (hS a ha).1.mono post.mono
    · exact Or.inr (Or.inr (Or.inr (Or.inl (stackLo_w6 hpre I hn ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · simp only [Fresh, heapNext] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by simp only [heapNext]; omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by simp only [heapNext]; omega⟩))))
  · rcases ha with (ha | ha | ha | ha) | ha
    · exact (hS a ha).2
    · simp only [M8W]
      rw [stackLo_callee I] at ha
      refine ⟨?_, ?_, ?_, ?_, fun e he hw ↦ ?_⟩ <;> simp only [Within] at ha ⊢
      all_goals first
        | addr_omega [ha, hb1, hn, hu, hW]
        | (obtain ⟨e1, e2, -⟩ := (h.tabs e he).1; simp only [Within] at hw; addr_omega [ha, hb1, hn, e1, hw])
    · simp only [M8W]
      refine ⟨?_, ?_, ?_, ?_, fun e he hw ↦ ?_⟩ <;> simp only [Within] at ha ⊢
      all_goals first
        | addr_omega [ha, hb1, hu, hW]
        | (obtain ⟨e1, e2, -⟩ := (h.tabs e he).1; simp only [Within] at hw; addr_omega [ha, hb1, e1, hw])
    · simp only [M8W]
      simp only [Fresh, heapNext] at ha
      refine ⟨by omega, ?_, ?_, ?_, fun e he hw ↦ ?_⟩
      all_goals first
        | addr_omega [ha, hb1, ht, hW]
        | (obtain ⟨e1, e2, -⟩ := (h.tabs e he).1; simp only [Within] at hw; addr_omega [ha, hb1, e1, hw, ht])
    · simp only [M8W]
      refine ⟨by omega, ?_, ?_, ?_, fun e he hw ↦ ?_⟩
      all_goals first
        | (simp only [Within]; addr_omega [ha, hb1, hhiN, hu])
        | (obtain ⟨e1, e2, -⟩ := (h.tabs e he).1; simp only [Within] at hw; addr_omega [ha, hb1, e1, hw, hhiN, hu])


/-- A frame slot misses what a callee writing another slot, its stack, `NEXT`, fresh heap and a
heap range writes. -/
theorem slot_not_cwx {s u t : MachineState} (hpre : WalkPre s) (I : Inv s u) {o₁ o : Word}
    {n₁ n lo' hi' : Nat} (h1 : InSlot s o₁ n₁) (hn : n ≤ 8736)
    (hoo : ∀ x, Within x o₁ n₁ → ¬ Within x o 24) (hv : HeapOk t) (hhi' : hi' ≤ heapNext t) :
    ∀ x, Within x o₁ n₁ → ¬ (CW u t o n x ∨ (lo' ≤ x.toNat ∧ x.toNat < hi')) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨e1, e2, -⟩ := h1
  have ht := hv.hi
  simp only [heapEnd, heapNext] at ht hhi'
  intro x hx hw
  rcases hw with (hw | hw | hw | hw) | hw
  · exact hoo x hx hw
  · rw [stackLo_callee I] at hw; simp only [Within] at hx hw; addr_omega [hx, hw, hb1, hn, e1, e2]
  · simp only [Within] at hx hw; addr_omega [hx, hw, hb1, e1, e2]
  · simp only [Fresh, heapNext] at hw; simp only [Within] at hx; addr_omega [hx, hw, hb1, e1, e2, ht]
  · simp only [Within] at hx; addr_omega [hx, hw, hb1, e1, e2, ht, hhi']

/-- A form in a frame slot kept across a callee writing another slot, its stack, `NEXT`, fresh heap
and a heap range apart from its buffer. -/
theorem SF.cwx {s u t : MachineState} {o o' : Word} {n lo hi lo' hi' : Nat}
    {f : LayoutMirror.FormRust} (hpre : WalkPre s) (I : Inv s u) (hf : SF u o f lo hi)
    (ho : InSlot s o 24) (hhi : hi ≤ heapNext u)
    (fr : Rv64Verifier.Layout.DFrame u t fun a ↦ CW u t o' n a ∨ (lo' ≤ a.toNat ∧ a.toNat < hi'))
    (hn : n ≤ 8736) (ho' : InSlot s o' 24) (hoo : ∀ x, Within x o 24 → ¬ Within x o' 24)
    (hA : hi ≤ lo' ∨ hi' ≤ lo) (hhi' : hi' ≤ heapNext t) (hv : HeapOk t)
    (mono : heapNext u ≤ heapNext t) : SF t o f lo hi := by
  have H : SFh s u lo hi [(o, f)] := ⟨fun e he ↦ by
    simp only [List.mem_singleton] at he; subst he; exact hf, fun e he ↦ by
    simp only [List.mem_singleton] at he; subst he; exact ho⟩
  exact (H.frame' hpre I fr hn ho' (fun e he ↦ by
    simp only [List.mem_singleton] at he; subst he; exact hoo) hA hhi hhi' hv mono).sf _
    (List.mem_singleton_self _)

set_option maxRecDepth 8192 in
/-- `prod(a1, a2, a3)` into a frame slot, with the call's frame. -/
theorem prodF (hP : Rv64Verifier.Layout.ProdSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o : Word} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W L) (ho : InSlot s o 24)
    (hL : ∀ e ∈ L, ∀ a, Within a o 24 → ¬ Within a e.1 72) (hpc : u.pc = 0x80005138)
    (x10 : u.getReg .x10 = o) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      M8 OI s t A k R Q B Bb W L ∧
      SF t o (LayoutMirror.prodRust (u.getReg .x11).toNat (u.getReg .x12).toNat (u.getReg .x13).toNat)
        (heapNext u) (heapNext t) ∧
      Rv64Verifier.Layout.DFrame u t (CW u t o Rv64Verifier.Layout.colStack) ∧ HeapOk t ∧
      heapNext u ≤ heapNext t) ∨ Dead Image.code t) := by
  have hn : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  have I := h.m.inv
  obtain ⟨v1, v2, v3⟩ := slotPre hpre I ho hn
  have pre : Rv64Verifier.Layout.ColPre u := {
    heap := I.heap
    stack := stk_sub hpre I hn (by decide)
    out := by rw [x10]; exact v1
    outFree := by rw [x10]; exact v2
    outStack := by rw [x10]; exact v3
    rodata := I.rodata hpre }
  obtain ⟨t, hr, ⟨hpct, hp, nf, fv⟩ | hd⟩ := hP u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  rw [x10] at nf fv
  obtain ⟨o1, o2, -⟩ := ho
  exact ⟨t, hr, Or.inl ⟨hpct, hp, h.call hpre nf.frame ⟨o1, o2⟩ hL hn nf.heap nf.mono (hp.reg .x2),
    SF.ofNew nf fv, nf.frame, nf.heap, nf.mono⟩⟩

set_option maxRecDepth 8192 in
/-- `col(a1, a2)` into a frame slot, with the call's frame. -/
theorem colF (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o : Word} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W L) (ho : InSlot s o 24)
    (hL : ∀ e ∈ L, ∀ a, Within a o 24 → ¬ Within a e.1 72) (hpc : u.pc = 0x80004b34)
    (x10 : u.getReg .x10 = o) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      M8 OI s t A k R Q B Bb W L ∧
      SF t o (LayoutMirror.colRust (u.getReg .x11).toNat (u.getReg .x12).toNat)
        (heapNext u) (heapNext t) ∧
      Rv64Verifier.Layout.DFrame u t (CW u t o Rv64Verifier.Layout.colStack) ∧ HeapOk t ∧
      heapNext u ≤ heapNext t) ∨ Dead Image.code t) := by
  have hn : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  have I := h.m.inv
  obtain ⟨v1, v2, v3⟩ := slotPre hpre I ho hn
  have pre : Rv64Verifier.Layout.ColPre u := {
    heap := I.heap
    stack := stk_sub hpre I hn (by decide)
    out := by rw [x10]; exact v1
    outFree := by rw [x10]; exact v2
    outStack := by rw [x10]; exact v3
    rodata := I.rodata hpre }
  obtain ⟨t, hr, ⟨hpct, hp, nf, fv⟩ | hd⟩ := hC u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  rw [x10] at nf fv
  obtain ⟨o1, o2, -⟩ := ho
  exact ⟨t, hr, Or.inl ⟨hpct, hp, h.call hpre nf.frame ⟨o1, o2⟩ hL hn nf.heap nf.mono (hp.reg .x2),
    SF.ofNew nf fv, nf.frame, nf.heap, nf.mono⟩⟩

/-- The registers JUMP keeps. -/
structure JR (s u : MachineState) : Prop where
  x19 : u.getReg .x19 = 1
  x21 : u.getReg .x21 = 6
  x22 : u.getReg .x22 = 2
  x23 : u.getReg .x23 = s.getReg .x2 - 512
  x27 : u.getReg .x27 = 6

theorem JR.keeps {s u t : MachineState} {l : List Reg} (h : JR s u)
    (hk : ∀ r ∈ l, t.getReg r = u.getReg r)
    (hl : ∀ r ∈ ([.x19, .x21, .x22, .x23, .x27] : List Reg), r ∈ l := by decide) : JR s t :=
  ⟨by rw [hk .x19 (hl _ (by decide))]; exact h.x19, by rw [hk .x21 (hl _ (by decide))]; exact h.x21,
    by rw [hk .x22 (hl _ (by decide))]; exact h.x22, by rw [hk .x23 (hl _ (by decide))]; exact h.x23,
    by rw [hk .x27 (hl _ (by decide))]; exact h.x27⟩

theorem JR.pres {s u t : MachineState} (h : JR s u) (hp : Preserves u t) : JR s t :=
  h.keeps hp

end Rv64Verifier.Proofs.Walk
