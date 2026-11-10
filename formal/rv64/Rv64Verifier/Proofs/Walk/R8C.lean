import Rv64Verifier.Proofs.Walk.R8B

/-!
# `walk`: `tables()`, SET's head (R8)

A function growing the `Flushes` under construction keeps `M8` (`M8.grow`). From `mulStage`'s end:
`state_step` on the empty `Flushes` at `sp + 1728`, `alloc(8, 120)` for SET's five operands, to
the first `col` call (`setHead`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep)

/-- A function growing the `Flushes` under construction at the frame slot `o`. -/
theorem M8.grow {OI : MachineState → Word → List (List Opening) → Prop} {s u t : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o : Word} {F : LayoutMirror.FlushesRust} {lo n : Nat}
    (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L) (fb : FB u o F lo) (hlo : W ≤ lo)
    (hlo' : lo ≤ heapNext u) (ho : InSlot s o 48) (hL : ∀ e ∈ L, ∀ a, Within a o 48 → ¬ Within a e.1 72)
    (g : Rv64Verifier.Layout.GrowFlushes u t o n (fun _ ↦ False)) (hn : n ≤ 8736)
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
    · exact hd.elim
    · simp only [Fresh] at hd; omega

/-- SET's operands buffer `P`: 120 bytes, fresh past the `Flushes` under construction. -/
structure OpsBuf (u : MachineState) (o P : Word) : Prop where
  al : P.toNat % 8 = 0
  next : P.toNat + 120 ≤ heapNext u
  deep : ∀ x, flushesDeep u o x → x.toNat < P.toNat

set_option maxRecDepth 8192 in
/-- SET's head: `state_step` on the empty `Flushes` at `sp + 1728`, `alloc(8, 120)`, to `col(2, 0)`
into the buffer. -/
theorem setHead (hSS : Rv64Verifier.Layout.StateStepSpec) (hAS : AllocSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L)
    (hL : ∀ e ∈ L, ∀ a, Within a (s.getReg .x2 - 928) 48 → ¬ Within a e.1 72) (r : R8 u)
    (he : EmptyAt u (s.getReg .x2 - 928)) (x10 : u.getReg .x10 = s.getReg .x2 - 928)
    (x1 : u.getReg .x1 = 0x80002100) (hpc : u.pc = 0x80004a90) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80004b34 ∧ ∃ P, M8 OI s t A k R Q B Bb W L ∧
      FB t (s.getReg .x2 - 928) (({} : LayoutMirror.FlushesRust).stateStep 0 1) (heapNext u) ∧
      OpsBuf t (s.getReg .x2 - 928) P ∧ R8 t ∧ t.getReg .x10 = P ∧ t.getReg .x25 = P ∧
      t.getReg .x11 = 2 ∧ t.getReg .x12 = 0 ∧ t.getReg .x27 = 6 ∧ t.getReg .x1 = 0x80002134) ∨
      Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  obtain ⟨f0, f8, f16, f24, f32, f40⟩ := he
  obtain ⟨fok, fval, fnd⟩ := flushesOk_empty f0 f8 f16 f24 f32 f40
  have hn : Rv64Verifier.Layout.stateStepStack ≤ 8736 := by decide
  have hslot : InSlot s (s.getReg .x2 - 928) (8 * 6) := by simp only [InSlot]; addr_omega [hb1, hb3]
  obtain ⟨v1, v2, v3⟩ := slotW hpre h.m.inv hslot hn
  have pre : Rv64Verifier.Layout.FlushesPre Rv64Verifier.Layout.stateStepStack u := {
    heap := h.m.inv.heap
    stack := stk_sub hpre h.m.inv hn (by decide)
    self := by rw [x10]; exact v1
    ok := by rw [x10]; exact fok
    selfFree := by rw [x10]; exact v2
    selfStack := by rw [x10]; exact v3
    rodata := h.m.inv.rodata hpre }
  obtain ⟨t₁, r₁, ⟨pc₁, hp₁, ⟨g, gv⟩⟩ | d⟩ := hSS u hpc pre
  swap
  · exact ⟨t₁, r₁, Or.inr d⟩
  rw [x10] at g gv
  rw [fval] at gv
  obtain ⟨M₁, F₁⟩ := h.grow hpre ⟨fok, fval, fun x hx ↦ absurd hx (fnd x)⟩ h.bb.2.2.2 (le_refl _)
    hslot hL g hn (hp₁.reg .x2)
  rw [gv] at F₁
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := M₁.m.inv.sp
  obtain ⟨u₂, r₂, g₂⟩ := Sym.BlockSpec.reaches b80002100_spec (by rw [pc₁, returnAddress_eq, x1]; decide) trivial
  have k₂ := b80002100_keeps g₂
  have m₂ := b80002100_mem_same g₂
  have hn₂ : heapNext u₂ = heapNext t₁ := by simp only [heapNext, m₂]
  have fr₂ := Rv64Verifier.Layout.DFrame.of_same m₂ (fun _ ↦ False)
  have M₂ := M₁.step hpre fr₂ (fun _ h ↦ h.elim) (fun _ h ↦ h.elim) ⟨hn₂ ▸ M₁.m.inv.heap.lo,
    hn₂ ▸ M₁.m.inv.heap.hi⟩ hn₂.ge (k₂ .x2 (by decide))
  have F₂ := F₁.frame fr₂ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) M₁.m.inv.heap hn₂.ge
  obtain ⟨t₃, r₃, ⟨pc₃, hp₃, post₃⟩ | d⟩ := hAS.call (Reaches.refl u₂) (b80002100_pc g₂)
    ⟨M₂.m.inv.heap, by rw [b80002100_x10 g₂]; decide⟩
  swap
  · exact ⟨t₃, r₁.trans (r₂.trans r₃), Or.inr d⟩
  have hal := post₃.aligned
  have hab := post₃.above
  have hnx := post₃.next
  rw [b80002100_x10 g₂] at hal
  rw [b80002100_x11 g₂] at hnx
  rw [show (8 : Word).toNat = 8 from rfl] at hal
  rw [show (120 : Word).toNat = 120 from rfl] at hnx
  set P := t₃.getReg .x10 with hP
  have fr₃ : Rv64Verifier.Layout.DFrame u₂ t₃ (Within · nextAddr 8) := fun a ha _ ↦
    post₃.mem a fun he ↦ ha a (by simp only [Within]; omega) (by rw [he]; simp only [Within]; omega)
  have hu₂ := M₂.m.inv.heap.hi
  have hW := M₂.bb.2.2.2
  simp only [heapEnd] at hu₂
  have mono₃ : heapNext u₂ ≤ heapNext t₃ := by rw [hnx]; omega
  have M₃ := M₂.step hpre fr₃ (fun x hx ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))
    (fun x hx ↦ by
      simp only [M8W]
      refine ⟨?_, ?_, ?_, ?_, fun e he hw ↦ ?_⟩
      all_goals first
        | (simp only [Within, nextAddr] at hx ⊢; addr_omega [hx, hb1, hW, hu₂])
        | (obtain ⟨e1, -, -⟩ := (M₂.tabs e he).1; simp only [Within, nextAddr] at hx hw; addr_omega [hx, hw, e1, hb1]))
    post₃.heap mono₃ (hp₃.reg .x2)
  have F₃ := F₂.1.frame fr₃ (fun x hx hw ↦ by simp only [Within, nextAddr] at hx hw; addr_omega [hx, hw, hb1])
    (fun x _ h2 hw ↦ by simp only [Within, nextAddr] at hw; addr_omega [hw, h2, hu₂]) (by addr_omega [hb1])
    M₂.m.inv.heap mono₃
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 2656 := M₃.m.inv.sp
  obtain ⟨u₄, r₄, g₄⟩ := Sym.BlockSpec.reaches b80002110_spec
    (by rw [pc₃, returnAddress_eq, b80002100_x1 g₂]; decide) (by
      rv_eval [sp₃]
      valid_access hval [hb1])
  have hP0 : P ≠ 0 := fun he ↦ by
    have := congrArg BitVec.toNat he; rw [show (0 : Word).toNat = 0 from rfl] at this
    have := M₂.m.inv.heap.lo; simp only [heapStart] at this; omega
  obtain ⟨u₅, r₅, g₅⟩ := Sym.BlockSpec.reaches b80002120_spec (b80002110_pc_taken g₄ hP0) trivial
  have m₄₅ (a : Word) : u₅.getMem a = t₃.getMem a := (b80002120_mem_same g₅ a).trans (b80002110_mem_same g₄ a)
  have sp₅ : u₅.getReg .x2 = t₃.getReg .x2 := (b80002120_keeps g₅ .x2 (by decide)).trans
    (b80002110_keeps g₄ .x2 (by decide))
  have hn₅ : heapNext u₅ = heapNext t₃ := by simp only [heapNext, m₄₅]
  have fr₅ := Rv64Verifier.Layout.DFrame.of_same m₄₅ (fun _ ↦ False)
  have M₅ := M₃.step hpre fr₅ (fun _ h ↦ h.elim) (fun _ h ↦ h.elim) ⟨hn₅ ▸ M₃.m.inv.heap.lo,
    hn₅ ▸ M₃.m.inv.heap.hi⟩ hn₅.ge sp₅
  have F₅ := F₃.1.frame fr₅ (fun _ _ h ↦ h) (fun _ _ _ h ↦ h) (by addr_omega [hb1]) M₃.m.inv.heap hn₅.ge
  have hd₅ : flushesDeep u₅ (s.getReg .x2 - 928) = flushesDeep t₁ (s.getReg .x2 - 928) := by
    rw [F₅.2, F₃.2, F₂.2]
  have k₄ := b80002110_keeps g₄
  have k₅ := b80002120_keeps g₅
  refine ⟨u₅, r₁.trans (r₂.trans (r₃.trans (r₄.trans r₅))), Or.inl ⟨b80002120_pc g₅, P, M₅, F₅.1,
    ⟨hal, by rw [hn₅, hnx], fun x hx ↦ by
      rw [hd₅] at hx; have := (F₁.ok.deep_below hx).2; rw [← hn₂] at this; omega⟩,
    ⟨?_, ?_⟩, ?_, by rw [b80002120_x25 g₅, k₄ .x10 (by decide)], b80002120_x11 g₅, b80002120_x12 g₅, ?_, b80002120_x1 g₅⟩⟩
  · rw [k₅ .x8 (by decide), k₄ .x8 (by decide), hp₃.reg .x8, k₂ .x8 (by decide), hp₁.reg .x8]; exact r.x8
  · rw [k₅ .x24 (by decide), k₄ .x24 (by decide), hp₃.reg .x24, k₂ .x24 (by decide), hp₁.reg .x24]; exact r.x24
  · rw [k₅ .x10 (by decide), k₄ .x10 (by decide)]
  · rw [k₅ .x27 (by decide), b80002110_x27 g₄, spAdd hpre sp₃ (N := 152) (M := 2504) (by decide),
      M₃.lens.2]; rfl

end Rv64Verifier.Proofs.Walk
