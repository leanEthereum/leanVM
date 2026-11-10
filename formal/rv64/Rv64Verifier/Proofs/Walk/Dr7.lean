import Rv64Verifier.Proofs.Walk.Dr6

/-!
# `walk`: `tables()`, DEREF's head (R8)

From `state_step`'s call on the empty `Flushes` at `sp + 2312`: `state_step`, `alloc(8, 120)` for
the operands, `col(2, 0)` straight into the buffer `P`, to `0x8000275c` (`derefHead1`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

set_option maxRecDepth 8192 in
/-- `state_step`, `alloc(8, 120)` and `col(2, 0)` into the operands' buffer `P`. -/
theorem derefHead1 (hSS : Rv64Verifier.Layout.StateStepSpec) (hAS : AllocSpec)
    (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W lo₂ : Nat} (hpre : WalkPre s)
    (h : DS OI s u A k R Q B Bb W (L4 s setT) (s.getReg .x2 - 344) {} (heapNext u) lo₂ (storeFs s))
    (hW : W ≤ heapNext u) (r : DRg s u 0xa00000b0) (x10 : u.getReg .x10 = s.getReg .x2 - 344)
    (x1 : u.getReg .x1 = 0x8000272c) (hpc : u.pc = 0x80004a90) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x8000275c ∧ ∃ P : Word, P.toNat % 8 = 0 ∧
      heapNext u ≤ P.toNat ∧
      DS OI s t A k R Q B Bb W (L4 s setT) (s.getReg .x2 - 344) (({} : LayoutMirror.FlushesRust).stateStep 0 1)
        (heapNext u) (P.toNat + 120) [(P, LayoutMirror.colRust 2 0)] ∧
      (∀ x, flushesDeep t (s.getReg .x2 - 344) x → x.toNat < P.toNat) ∧
      SFh s t lo₂ (heapNext u) (storeFs s) ∧ DRg s t P ∧ t.getReg .x22 = 2) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have I := h.m.m.inv
  have hSh : SFh s u lo₂ (heapNext u) (storeFs s) := h.sl.toH (by slots_tac [hb1, hb3])
  -- `state_step`
  have hn : Rv64Verifier.Layout.stateStepStack ≤ 8736 := by decide
  have hFo : InSlot s (s.getReg .x2 - 344) (8 * 6) := inSlot_off hpre (by decide)
  obtain ⟨v1, v2, v3⟩ := slotW hpre I hFo hn
  have pre : Rv64Verifier.Layout.FlushesPre Rv64Verifier.Layout.stateStepStack u := {
    heap := I.heap
    stack := stk_sub hpre I hn (by decide)
    self := by rw [x10]; exact v1
    ok := by rw [x10]; exact h.fb.ok
    selfFree := by rw [x10]; exact v2
    selfStack := by rw [x10]; exact v3
    rodata := I.rodata hpre }
  obtain ⟨t₁, q₁, ⟨pc₁, hp₁, ⟨g, gv⟩⟩ | d⟩ := hSS u hpc pre
  swap
  · exact ⟨t₁, q₁, Or.inr d⟩
  rw [x10] at g gv
  rw [h.fb.val] at gv
  obtain ⟨M₁, F₁⟩ := h.m.grow hpre h.fb hW (le_refl _) h.fo (l4_off hpre (by decide)) g hn (hp₁.reg .x2)
  rw [gv] at F₁
  have H₁ := hSh.grow hpre I g h.fb (le_refl _) h.fo (by forms_tac [hb1]) hn (le_refl _)
  have sp₁ : t₁.getReg .x2 = s.getReg .x2 - 2656 := M₁.m.inv.sp
  have R₁ := r.pres hp₁
  -- `alloc(8, 120)`
  obtain ⟨u₂, q₂, g₂⟩ := Sym.BlockSpec.reaches b8000272c_spec (by rw [pc₁, returnAddress_eq, x1]; decide)
    trivial
  have m₂ := b8000272c_mem_same g₂
  have hn₂ : heapNext u₂ = heapNext t₁ := by simp only [heapNext, m₂]
  have M₂ := M₁.same hpre m₂ (b8000272c_keeps g₂ .x2 (by decide))
  have F₂ := F₁.same hpre h.fo M₁.m.inv.heap m₂
  have H₂ := H₁.next hpre M₁.m.inv (Rv64Verifier.Layout.DFrame.of_same m₂ _) (le_trans (le_refl _) g.mono)
    hn₂.ge
  have R₂ := R₁.keeps (b8000272c_keeps g₂)
  obtain ⟨t₃, q₃, ⟨pc₃, hp₃, post₃⟩ | d⟩ := hAS.call (Reaches.refl u₂) (b8000272c_pc g₂)
    ⟨M₂.m.inv.heap, by rw [b8000272c_x10 g₂]; decide⟩
  swap
  · exact ⟨t₃, q₁.trans (q₂.trans q₃), Or.inr d⟩
  have hal := post₃.aligned
  have hab := post₃.above
  have hnx := post₃.next
  rw [b8000272c_x10 g₂] at hal
  rw [b8000272c_x11 g₂] at hnx
  rw [show (8 : Word).toNat = 8 from rfl] at hal
  rw [show (120 : Word).toNat = 120 from rfl] at hnx
  set P := t₃.getReg .x10 with hP
  have fr₃ : Rv64Verifier.Layout.DFrame u₂ t₃ (Within · nextAddr 8) := fun a ha _ ↦
    post₃.mem a fun he ↦ ha a (by simp only [Within]; omega) (by rw [he]; simp only [Within]; omega)
  have hu₂ := M₂.m.inv.heap.hi
  have hW₂ := M₂.bb.2.2.2
  simp only [heapEnd] at hu₂
  have mono₃ : heapNext u₂ ≤ heapNext t₃ := by rw [hnx]; omega
  have M₃ := M₂.step hpre fr₃ (fun x hx ↦ Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hx)))))
    (fun x hx ↦ by
      simp only [M8W]
      refine ⟨?_, ?_, ?_, ?_, fun e he hw ↦ ?_⟩
      all_goals first
        | (simp only [Within, nextAddr] at hx ⊢; addr_omega [hx, hb1, hW₂, hu₂])
        | (obtain ⟨e1, -, -⟩ := (M₂.tabs e he).1; simp only [Within, nextAddr] at hx hw; addr_omega [hx, hw, e1, hb1]))
    post₃.heap mono₃ (hp₃.reg .x2)
  have F₃ := F₂.frame fr₃ (fun x hx hw ↦ by simp only [Within, nextAddr] at hx hw; addr_omega [hx, hw, hb1])
    (fun x _ h2 hw ↦ by simp only [Within, nextAddr] at hw; addr_omega [hw, h2, hu₂]) (by addr_omega [hb1])
    M₂.m.inv.heap mono₃
  have H₃ := H₂.next hpre M₂.m.inv fr₃ (by rw [hn₂]; exact g.mono) mono₃
  have R₃ := R₂.pres hp₃
  have sp₃ : t₃.getReg .x2 = s.getReg .x2 - 2656 := M₃.m.inv.sp
  have hP0 : P ≠ 0 := fun he ↦ by
    have := congrArg BitVec.toNat he; rw [show (0 : Word).toNat = 0 from rfl] at this
    have := M₂.m.inv.heap.lo; simp only [heapStart] at this; omega
  obtain ⟨u₄, q₄, g₄⟩ := Sym.BlockSpec.reaches b8000273c_spec
    (by rw [pc₃, returnAddress_eq, b8000272c_x1 g₂]; decide) trivial
  obtain ⟨u₅, q₅, g₅⟩ := Sym.BlockSpec.reaches b80002744_spec (b8000273c_pc_taken g₄ hP0) trivial
  have m₄₅ (a : Word) : u₅.getMem a = t₃.getMem a :=
    (b80002744_mem_same g₅ a).trans (b8000273c_mem_same g₄ a)
  have sp₅ : u₅.getReg .x2 = t₃.getReg .x2 :=
    (b80002744_keeps g₅ .x2 (by decide)).trans (b8000273c_keeps g₄ .x2 (by decide))
  have hn₅ : heapNext u₅ = heapNext t₃ := by simp only [heapNext, m₄₅]
  have M₅ := M₃.same hpre m₄₅ sp₅
  have F₅ := F₃.1.same hpre h.fo M₃.m.inv.heap m₄₅
  have H₅ := H₃.next hpre M₃.m.inv (Rv64Verifier.Layout.DFrame.of_same m₄₅ _)
    (by rw [hn₂] at hab; exact le_trans (le_trans g.mono hab) (by omega)) hn₅.ge
  have x10₅ : u₅.getReg .x10 = P := by
    rw [b80002744_keeps g₅ .x10 (by decide), b8000273c_keeps g₄ .x10 (by decide)]
  have R₅ : DRg s u₅ P := ⟨by rw [b80002744_keeps g₅ .x18 (by decide), b8000273c_keeps g₄ .x18 (by decide)]; exact R₃.x18,
    by rw [b80002744_keeps g₅ .x23 (by decide), b8000273c_keeps g₄ .x23 (by decide)]; exact R₃.x23,
    by rw [b80002744_x24 g₅, b8000273c_keeps g₄ .x10 (by decide)],
    by rw [b80002744_keeps g₅ .x25 (by decide), b8000273c_keeps g₄ .x25 (by decide)]; exact R₃.x25,
    by rw [b80002744_keeps g₅ .x26 (by decide), b8000273c_keeps g₄ .x26 (by decide)]; exact R₃.x26,
    by rw [b80002744_keeps g₅ .x27 (by decide), b8000273c_keeps g₄ .x27 (by decide)]; exact R₃.x27⟩
  have hPlo : heapNext t₁ ≤ P.toNat := by rw [← hn₂]; exact hab
  have pnx : P.toNat + 120 ≤ heapNext u₅ := by rw [hn₅, hnx]
  have hu₅ := M₅.m.inv.heap.hi
  simp only [heapEnd] at hu₅
  have pdeep : ∀ x, flushesDeep u₅ (s.getReg .x2 - 344) x → x.toNat < P.toNat := fun x hx ↦ by
    have := (F₂.ok.deep_below (by rw [← F₃.2, ← deep_same m₄₅]; exact hx)).2
    rw [hn₂] at this; omega
  -- `col(2, 0)` into `P`
  have hnC : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  have hs := hpre.heap.lo
  simp only [heapStart] at hs
  have hq := M₅.m.bufQ
  have hb := M₅.bb
  have hPh : 0x20000000 ≤ P.toNat := by omega
  have preC : Rv64Verifier.Layout.ColPre u₅ := {
    heap := M₅.m.inv.heap
    stack := stk_sub hpre M₅.m.inv hnC (by decide)
    out := by rw [x10₅]; exact Rv64Verifier.Layout.validMemRange_of hal (Or.inl ⟨by omega, by omega⟩)
    outFree := by rw [x10₅]; exact ⟨Or.inl (by omega), by addr_omega [pnx, hu₅]⟩
    outStack := by rw [x10₅, stackLo_callee M₅.m.inv]; addr_omega [hb1, hnC, pnx, hu₅]
    rodata := M₅.m.inv.rodata hpre }
  obtain ⟨t₆, q₆, ⟨pc₆, hp₆, nf₆, fv₆⟩ | d⟩ := hC u₅ (b80002744_pc g₅) preC
  swap
  · exact ⟨t₆, q₁.trans (q₂.trans (q₃.trans (q₄.trans (q₅.trans q₆)))), Or.inr d⟩
  rw [x10₅] at nf₆ fv₆
  have K₆ := M₅.newForm hpre F₅ h.fo nf₆ hnC (fun a ha ↦ by
      simp only [Within] at ha
      refine ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))), ?_⟩
      simp only [M8W]
      refine ⟨by omega, ?_, ?_, ?_, fun e he hw ↦ ?_⟩
      · simp only [Within]; addr_omega [ha, hb1, pnx, hu₅]
      · simp only [Within]; addr_omega [ha, hb1, pnx, hu₅]
      · simp only [Within]; addr_omega [ha, hb1, pnx, hu₅]
      · obtain ⟨e1, -, -⟩ := (M₅.tabs e he).1
        simp only [Within] at hw; addr_omega [ha, hw, hb1, e1, pnx, hu₅])
    (fun a ha ↦ ⟨by simp only [Within] at ha ⊢; addr_omega [ha, hb1, pnx, hu₅],
      fun hd ↦ by have := pdeep a hd; simp only [Within] at ha; omega⟩) (hp₆.reg .x2)
  have H₆ := H₅.frame' (o := s.getReg .x2 - 344) (lo' := P.toNat) (hi' := P.toNat + 24) hpre M₅.m.inv
    (nf₆.frame.mono fun a ha ↦ by
      rcases ha with ha | ha | ha | ha
      · exact Or.inr (by simp only [Within] at ha; addr_omega [ha, pnx, hu₅])
      · exact Or.inl (Or.inr (Or.inl ha))
      · exact Or.inl (Or.inr (Or.inr (Or.inl ha)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr ha)))) hnC (inSlot_off hpre (by decide))
    (by forms_tac [hb1]) (Or.inl (le_trans (le_trans (le_refl _) g.mono) hPlo))
    (le_trans g.mono (by omega)) (le_trans (by omega) nf₆.mono) nf₆.heap nf₆.mono
  refine ⟨t₆, q₁.trans (q₂.trans (q₃.trans (q₄.trans (q₅.trans q₆)))), Or.inl ⟨?_, P, hal,
    le_trans g.mono hPlo, ⟨K₆.1, K₆.2.1, h.fo,
      (SFs.nil s t₆ _).cons (SF.ofNew nf₆ (by rw [fv₆, b80002744_x11 g₅, b80002744_x12 g₅]; rfl))
        (by omega) (le_refl _) (Or.inr (by have := nf₆.mono; omega)), by have := nf₆.mono; omega⟩,
    fun x hx ↦ pdeep x (by rw [← K₆.2.2]; exact hx), H₆, R₅.pres hp₆, ?_⟩⟩
  · rw [pc₆, returnAddress_eq, b80002744_x1 g₅]; decide
  · rw [hp₆.reg .x22, b80002744_x22 g₅]

end Rv64Verifier.Proofs.Walk
