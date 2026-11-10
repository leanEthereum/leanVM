import Rv64Verifier.Proofs.Walk.Dr5

/-!
# `walk`: `tables()`, forms kept across a table's calls (R8)

Forms with fixed buffer bounds (`SFh`) kept by a function growing the `Flushes` under construction
whose footprint lies past them (`SFh.grow`), by an allocation (`SFh.next`), and by `col` and `prod`
into a frame slot (`colE`, `prodE`: `colD` and `prodD` that also keep them).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

theorem SFh.grow {s u t : MachineState} {lo hi lo' n : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    {o : Word} {m : Word → Prop} {F : LayoutMirror.FlushesRust} (hpre : WalkPre s) (h : Inv s u)
    (hf : SFh s u lo hi Fs) (g : Rv64Verifier.Layout.GrowFlushes u t o n m) (fb : FB u o F lo')
    (hhi : hi ≤ lo') (ho : InSlot s o 48) (hoo : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x o 48)
    (hn : n ≤ 8736) (hhiN : hi ≤ heapNext u) : SFh s t lo hi Fs := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨o1, o2, -⟩ := ho
  have hu := h.heap.hi
  have ht := g.heap.hi
  have mono := g.mono
  simp only [heapEnd, heapNext] at hu ht mono hhiN
  have hbuf : ∀ x, Rv64Verifier.Layout.flushesBuf u o x → lo' ≤ x.toNat ∧ x.toNat < heapNext u :=
    fun x hx ↦ ⟨fb.deep x (hx.imp Or.inl Or.inl), (fb.ok.buf_below hx).2⟩
  refine ⟨fun e he ↦ ?_, hf.slot⟩
  obtain ⟨e1, e2, -⟩ := hf.slot e he
  refine (hf.sf e he).frame g.frame (fun x hx hw ↦ ?_) (fun x hx1 hx2 hw ↦ ?_) (by addr_omega [hb1, e2])
    h.heap (by simp only [heapNext]; omega)
  · simp only [Within] at hx
    rcases hw with hw | hw | hw | hw | hw
    · exact hoo e he x (by simp only [Within]; exact hx) hw
    · have := hbuf x hw; simp only [heapNext] at this; addr_omega [hx, this, hb1, e1, e2, hu]
    · rw [stackLo_callee h] at hw; simp only [Within] at hw; addr_omega [hx, hw, hb1, hn, e1, e2]
    · simp only [Within] at hw; addr_omega [hx, hw, hb1, e1, e2]
    · simp only [Fresh, heapNext] at hw; addr_omega [hx, hw, hb1, e1, e2, ht]
  · rcases hw with hw | hw | hw | hw | hw
    · simp only [Within] at hw; addr_omega [hw, hb1, o1, o2, hx2, hhiN, hu]
    · have := hbuf x hw; omega
    · rw [stackLo_callee h] at hw; simp only [Within] at hw; addr_omega [hw, hb1, hn, hx2, hhiN, hu]
    · simp only [Within] at hw; addr_omega [hw, hx2, hhiN, hu]
    · simp only [Fresh, heapNext] at hw; omega

theorem SFh.next {s u t : MachineState} {lo hi : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    (hpre : WalkPre s) (h : Inv s u) (hf : SFh s u lo hi Fs)
    (fr : Rv64Verifier.Layout.DFrame u t (Within · nextAddr 8)) (hhiN : hi ≤ heapNext u)
    (mono : heapNext u ≤ heapNext t) :
    SFh s t lo hi Fs := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hu := h.heap.hi
  simp only [heapEnd, heapNext] at hu hhiN
  refine ⟨fun e he ↦ ?_, hf.slot⟩
  obtain ⟨e1, e2, -⟩ := hf.slot e he
  refine (hf.sf e he).frame fr (fun x hx hw ↦ ?_) (fun x _ hx2 hw ↦ ?_) (by addr_omega [hb1, e2])
    h.heap mono
  · simp only [Within, nextAddr] at hx hw; addr_omega [hx, hw, hb1, e1, e2]
  · simp only [Within, nextAddr] at hw; addr_omega [hw, hx2, hhiN, hu]

set_option maxRecDepth 8192 in
/-- `col(a1, a2)` into a frame slot, keeping the forms `Hs` too. -/
theorem colE (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o o' : Word} {F : LayoutMirror.FlushesRust}
    {lo lo₂ lo₃ hi₃ : Nat} {Fs Hs : List (Word × LayoutMirror.FormRust)}
    (hpre : WalkPre s) (h : DS OI s u A k R Q B Bb W L o' F lo lo₂ Fs) (hH : SFh s u lo₃ hi₃ Hs)
    (hhi : hi₃ ≤ heapNext u) (ho : InSlot s o 24)
    (hL : ∀ e ∈ L, ∀ a, Within a o 24 → ¬ Within a e.1 72) (hoo : ∀ a, Within a o 24 → ¬ Within a o' 48)
    (hFs : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x o 24)
    (hHs : ∀ e ∈ Hs, ∀ x, Within x e.1 24 → ¬ Within x o 24)
    (hpc : u.pc = 0x80004b34) (x10 : u.getReg .x10 = o) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      DS OI s t A k R Q B Bb W L o' F lo lo₂
        ((o, LayoutMirror.colRust (u.getReg .x11).toNat (u.getReg .x12).toNat) :: Fs) ∧
      SFh s t lo₃ hi₃ Hs ∧ heapNext u ≤ heapNext t ∧ flushesDeep t o' = flushesDeep u o') ∨
      Dead Image.code t) := by
  have hn : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  have I := h.m.m.inv
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
  obtain ⟨M, Fb, mo, S, D⟩ := newSlot hpre h.m h.fb h.fo h.sl h.hlo₂ ho hL hoo hFs nf hn fv (hp.reg .x2)
  exact ⟨t, hr, Or.inl ⟨hpct, hp, ⟨M, Fb, h.fo, S, le_trans h.hlo₂ mo⟩,
    hH.frame' (lo' := 0) (hi' := 0) hpre I (nf.frame.mono fun _ ha ↦ Or.inl ha) hn ho hHs
      (Or.inr (Nat.zero_le _)) hhi (Nat.zero_le _) nf.heap mo, mo, D⟩⟩

set_option maxRecDepth 8192 in
/-- `prod(a1, a2, a3)` into a frame slot, keeping the forms `Hs` too. -/
theorem prodE (hP : Rv64Verifier.Layout.ProdSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o o' : Word} {F : LayoutMirror.FlushesRust}
    {lo lo₂ lo₃ hi₃ : Nat} {Fs Hs : List (Word × LayoutMirror.FormRust)}
    (hpre : WalkPre s) (h : DS OI s u A k R Q B Bb W L o' F lo lo₂ Fs) (hH : SFh s u lo₃ hi₃ Hs)
    (hhi : hi₃ ≤ heapNext u) (ho : InSlot s o 24)
    (hL : ∀ e ∈ L, ∀ a, Within a o 24 → ¬ Within a e.1 72) (hoo : ∀ a, Within a o 24 → ¬ Within a o' 48)
    (hFs : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x o 24)
    (hHs : ∀ e ∈ Hs, ∀ x, Within x e.1 24 → ¬ Within x o 24)
    (hpc : u.pc = 0x80005138) (x10 : u.getReg .x10 = o) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      DS OI s t A k R Q B Bb W L o' F lo lo₂
        ((o, LayoutMirror.prodRust (u.getReg .x11).toNat (u.getReg .x12).toNat
          (u.getReg .x13).toNat) :: Fs) ∧
      SFh s t lo₃ hi₃ Hs ∧ heapNext u ≤ heapNext t ∧ flushesDeep t o' = flushesDeep u o') ∨
      Dead Image.code t) := by
  have hn : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  have I := h.m.m.inv
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
  obtain ⟨M, Fb, mo, S, D⟩ := newSlot hpre h.m h.fb h.fo h.sl h.hlo₂ ho hL hoo hFs nf hn fv (hp.reg .x2)
  exact ⟨t, hr, Or.inl ⟨hpct, hp, ⟨M, Fb, h.fo, S, le_trans h.hlo₂ mo⟩,
    hH.frame' (lo' := 0) (hi' := 0) hpre I (nf.frame.mono fun _ ha ↦ Or.inl ha) hn ho hHs
      (Or.inr (Nat.zero_le _)) hhi (Nat.zero_le _) nf.heap mo, mo, D⟩⟩

end Rv64Verifier.Proofs.Walk
