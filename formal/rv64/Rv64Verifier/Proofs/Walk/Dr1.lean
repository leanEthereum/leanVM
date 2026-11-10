import Rv64Verifier.Proofs.Walk.Dr0

/-!
# `walk`: `tables()`, a table's forms under way (R8)

`DS`: `M8`, the `Flushes` under construction at a frame slot, the forms held. The calls `col`,
`prod`, `term` into a frame slot (`colD`, `prodD`, `termD`) and a block writing frame slots
(`DS.blk`) keep it. `SS`: a sum under way at a frame slot `acc`, its buffer from `H` on, its terms'
forms below `H`; started by a block writing the empty form (`SS.start`), kept by a block rewriting
`acc` (`SS.blk`), grown by `add_scaled` (`SS.asc`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

/-- A table under way: `M8`, the `Flushes` at the frame slot `o'`, the forms `Fs`. -/
structure DS (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B : Nat) (Bb : Word) (W : Nat)
    (L : List (Word × LayoutMirror.TableRust)) (o' : Word) (F : LayoutMirror.FlushesRust)
    (lo lo₂ : Nat) (Fs : List (Word × LayoutMirror.FormRust)) : Prop where
  m : M8 OI s u A k R Q B Bb W L
  fb : FB u o' F lo
  fo : InSlot s o' 48
  sl : SFs s u lo₂ Fs
  hlo₂ : lo₂ ≤ heapNext u

set_option maxRecDepth 8192 in
/-- `col(a1, a2)` into a frame slot. -/
theorem colD (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o o' : Word} {F : LayoutMirror.FlushesRust}
    {lo lo₂ : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    (hpre : WalkPre s) (h : DS OI s u A k R Q B Bb W L o' F lo lo₂ Fs) (ho : InSlot s o 24)
    (hL : ∀ e ∈ L, ∀ a, Within a o 24 → ¬ Within a e.1 72) (hoo : ∀ a, Within a o 24 → ¬ Within a o' 48)
    (hFs : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x o 24)
    (hpc : u.pc = 0x80004b34) (x10 : u.getReg .x10 = o) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      DS OI s t A k R Q B Bb W L o' F lo lo₂
        ((o, LayoutMirror.colRust (u.getReg .x11).toNat (u.getReg .x12).toNat) :: Fs) ∧
      Keep u t (heapNext u) ∧ heapNext u ≤ heapNext t ∧ flushesDeep t o' = flushesDeep u o') ∨
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
    Keep.cw hpre I nf.frame hn ho.1, mo, D⟩⟩

set_option maxRecDepth 8192 in
/-- `prod(a1, a2, a3)` into a frame slot. -/
theorem prodD (hP : Rv64Verifier.Layout.ProdSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o o' : Word} {F : LayoutMirror.FlushesRust}
    {lo lo₂ : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    (hpre : WalkPre s) (h : DS OI s u A k R Q B Bb W L o' F lo lo₂ Fs) (ho : InSlot s o 24)
    (hL : ∀ e ∈ L, ∀ a, Within a o 24 → ¬ Within a e.1 72) (hoo : ∀ a, Within a o 24 → ¬ Within a o' 48)
    (hFs : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x o 24)
    (hpc : u.pc = 0x80005138) (x10 : u.getReg .x10 = o) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      DS OI s t A k R Q B Bb W L o' F lo lo₂
        ((o, LayoutMirror.prodRust (u.getReg .x11).toNat (u.getReg .x12).toNat
          (u.getReg .x13).toNat) :: Fs) ∧
      Keep u t (heapNext u) ∧ heapNext u ≤ heapNext t ∧ flushesDeep t o' = flushesDeep u o') ∨
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
    Keep.cw hpre I nf.frame hn ho.1, mo, D⟩⟩

set_option maxRecDepth 8192 in
/-- `Form::term(One, ZERO)` into a frame slot, the monomial `One` at the slot `m`. -/
theorem termD (hT : Rv64Verifier.Layout.TermSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o o' m : Word} {F : LayoutMirror.FlushesRust}
    {lo lo₂ : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    (hpre : WalkPre s) (h : DS OI s u A k R Q B Bb W L o' F lo lo₂ Fs) (ho : InSlot s o 24)
    (hL : ∀ e ∈ L, ∀ a, Within a o 24 → ¬ Within a e.1 72) (hoo : ∀ a, Within a o 24 → ¬ Within a o' 48)
    (hFs : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x o 24)
    (hpc : u.pc = 0x800050a8) (x10 : u.getReg .x10 = o) (x11 : u.getReg .x11 = m) (hm : InSlot s m 24)
    (hm0 : u.getMem m = 0) (x12 : u.getReg .x12 = 0xa0000068) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      DS OI s t A k R Q B Bb W L o' F lo lo₂ ((o, LayoutMirror.constantRust 0) :: Fs) ∧
      Keep u t (heapNext u) ∧ heapNext u ≤ heapNext t ∧ flushesDeep t o' = flushesDeep u o') ∨
      Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hn : Rv64Verifier.Layout.termStack ≤ 8736 := by decide
  have I := h.m.m.inv
  obtain ⟨v1, v2, v3⟩ := slotPre hpre I ho hn
  obtain ⟨w1, -, w3⟩ := slotPre hpre I hm hn
  obtain ⟨m1, m2, -⟩ := hm
  have pre : Rv64Verifier.Layout.TermPre u := {
    heap := I.heap
    stack := stk_sub hpre I hn (by decide)
    out := by rw [x10]; exact v1
    mono := by rw [x11]; exact w1
    coeff := by rw [x12]; exact zero_vmr'
    monoOk := by rw [x11]; simp only [Rv64Verifier.Layout.MonoOk, hm0]; decide
    outFree := by rw [x10]; exact v2
    monoNext := by rw [x11]; addr_omega [hb1, m1, m2]
    coeffNext := by rw [x12]; addr_omega []
    outStack := by rw [x10]; exact v3
    monoStack := by rw [x11]; exact w3
    coeffStack := by rw [x12, stackLo_callee I]; addr_omega [hb1] }
  obtain ⟨t, hr, ⟨hpct, hp, nf, fv⟩ | hdd⟩ := hT u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hdd⟩
  rw [x10] at nf fv
  obtain ⟨M, Fb, mo, S, D⟩ := newSlot hpre h.m h.fb h.fo h.sl h.hlo₂ ho hL hoo hFs nf hn (by
    rw [fv, x11, x12, Rv64Verifier.Layout.monoOf, hm0, zeroE (I.rodata hpre)]) (hp.reg .x2)
  exact ⟨t, hr, Or.inl ⟨hpct, hp, ⟨M, Fb, h.fo, S, le_trans h.hlo₂ mo⟩,
    Keep.cw hpre I nf.frame hn ho.1, mo, D⟩⟩

/-- A block writing only the frame slot `o`, apart from the tables, the `Flushes` under
construction and the forms `Fs'` kept. -/
theorem DS.blk {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o o' : Word} {n : Nat} {F : LayoutMirror.FlushesRust}
    {lo lo₂ : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    (hpre : WalkPre s) (h : DS OI s u A k R Q B Bb W L o' F lo lo₂ Fs) (ho : InSlot s o n)
    (hL : ∀ e ∈ L, ∀ a, Within a o n → ¬ Within a e.1 72) (hoo : ∀ a, Within a o n → ¬ Within a o' 48)
    (Fs' : List (Word × LayoutMirror.FormRust)) (hs : ∀ e ∈ Fs', e ∈ Fs)
    (hFs : ∀ e ∈ Fs', ∀ x, Within x e.1 24 → ¬ Within x o n)
    (fr : Rv64Verifier.Layout.DFrame u v fun x ↦ Within x o n) (sp : v.getReg .x2 = u.getReg .x2) :
    DS OI s v A k R Q B Bb W L o' F lo lo₂ Fs' ∧ heapNext v = heapNext u ∧
      flushesDeep v o' = flushesDeep u o' ∧ Keep u v (heapNext u) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have I := h.m.m.inv
  have hu := I.heap.hi
  simp only [heapEnd] at hu
  obtain ⟨M, hn⟩ := h.m.slotStep hpre ho hL fr sp
  obtain ⟨o1, o2, -⟩ := ho
  obtain ⟨p1, p2, -⟩ := h.fo
  have heapApart : ∀ x : Word, x.toNat < heapNext u → ¬ Within x o n := fun x hx hw ↦ by
    simp only [Within] at hw; simp only [heapNext] at hx hu; addr_omega [hw, hx, hb1, o1, hu]
  have Fb := h.fb.frame fr (fun x hx hw ↦ hoo x hw hx) (fun x _ hx ↦ heapApart x hx)
    (by addr_omega [hb1, p2]) I.heap hn.ge
  refine ⟨⟨M, Fb.1, h.fo, ⟨fun e he ↦ ?_, fun e he ↦ ?_⟩, by rw [hn]; exact h.hlo₂⟩, hn, Fb.2,
    Keep.slot hpre hu fr ⟨o1, o2⟩⟩
  · have hl := h.sl.loc e (hs e he)
    have he' : e.1.toNat + 24 ≤ 2 ^ 64 := by
      rcases hl with ⟨e1, e2, -⟩ | hl
      · addr_omega [hb1, e2]
      · simp only [heapNext] at hl hu; omega
    rw [hn]
    exact (h.sl.sf e (hs e he)).frame fr (fun x hx hw ↦ hFs e he x hx hw)
      (fun x _ hx ↦ heapApart x hx) he' I.heap hn.ge
  · rw [hn]; exact h.sl.loc e (hs e he)

/-- A sum under way at the frame slot `acc` (with the scratch slot after it), its buffer from `H`
on; its terms' forms `Fs` below `H`. -/
structure SS (OI : MachineState → Word → List (List Opening) → Prop) (s u : MachineState)
    (A : List E) (k : Nat) (R Q : Word) (B : Nat) (Bb : Word) (W : Nat)
    (L : List (Word × LayoutMirror.TableRust)) (o' : Word) (F : LayoutMirror.FlushesRust)
    (lo lo₂ H : Nat) (Fs : List (Word × LayoutMirror.FormRust)) (acc : Word)
    (f : LayoutMirror.FormRust) : Prop where
  m : M8 OI s u A k R Q B Bb W L
  fb : FB u o' F lo
  fo : InSlot s o' 48
  fd : ∀ x, flushesDeep u o' x → x.toNat < H
  sh : SFh s u lo₂ H Fs
  sa : SF u acc f H (heapNext u)
  ha : InSlot s acc 48
  hL : ∀ e ∈ L, ∀ a, Within a acc 48 → ¬ Within a e.1 72
  hoo : ∀ a, Within a acc 48 → ¬ Within a o' 48
  hFs : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x acc 48
  hW : W ≤ H
  hH : H ≤ heapNext u

/-- A block writing `acc`'s 48 bytes, `acc`'s header rewritten unchanged. -/
theorem SS.blk {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o' : Word} {F : LayoutMirror.FlushesRust}
    {lo lo₂ H : Nat} {Fs : List (Word × LayoutMirror.FormRust)} {acc : Word} {f : LayoutMirror.FormRust}
    (hpre : WalkPre s) (h : SS OI s u A k R Q B Bb W L o' F lo lo₂ H Fs acc f)
    (fr : Rv64Verifier.Layout.DFrame u v fun x ↦ Within x acc 48)
    (m0 : v.getMem acc = u.getMem acc) (m8 : v.getMem (acc + 8) = u.getMem (acc + 8))
    (m16 : v.getMem (acc + 16) = u.getMem (acc + 16)) (sp : v.getReg .x2 = u.getReg .x2) :
    SS OI s v A k R Q B Bb W L o' F lo lo₂ H Fs acc f ∧ heapNext v = heapNext u ∧
      Keep u v (heapNext u) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have I := h.m.m.inv
  have hu := I.heap.hi
  simp only [heapEnd] at hu
  obtain ⟨M, hn⟩ := h.m.slotStep hpre h.ha h.hL fr sp
  obtain ⟨o1, o2, -⟩ := h.ha
  obtain ⟨p1, p2, -⟩ := h.fo
  have heapApart : ∀ x : Word, x.toNat < heapNext u → ¬ Within x acc 48 := fun x hx hw ↦ by
    simp only [Within] at hw; simp only [heapNext] at hx hu; addr_omega [hw, hx, hb1, o1, hu]
  have Fb := h.fb.frame' fr (fun x hx hw ↦ h.hoo x hw hx)
    (fun x hx ↦ heapApart x (h.fb.ok.deep_below hx).2) (by addr_omega [hb1, p2]) I.heap hn.ge
  have hHu := h.hH
  refine ⟨⟨M, Fb.1, h.fo, fun x hx ↦ h.fd x (by rw [← Fb.2]; exact hx),
    h.sh.slot' hpre fr h.ha h.hFs I.heap h.hH hn.ge,
    by rw [hn]; exact h.sa.move fr m0 m8 m16 (fun x _ hx ↦ heapApart x hx) I.heap hn.ge,
    h.ha, h.hL, h.hoo, h.hFs, h.hW, by rw [hn]; exact h.hH⟩, hn, Keep.slot hpre hu fr ⟨o1, o2⟩⟩

/-- A block writing the empty form at `acc` starts a sum over the forms `Fs`. -/
theorem SS.start {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o' : Word} {F : LayoutMirror.FlushesRust}
    {lo lo₂ : Nat} {Fs : List (Word × LayoutMirror.FormRust)} {acc : Word}
    (hpre : WalkPre s) (h : DS OI s u A k R Q B Bb W L o' F lo lo₂ Fs) (ha : InSlot s acc 48)
    (hL : ∀ e ∈ L, ∀ a, Within a acc 48 → ¬ Within a e.1 72)
    (hoo : ∀ a, Within a acc 48 → ¬ Within a o' 48)
    (hFs : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x acc 48) (hs : ∀ e ∈ Fs, InSlot s e.1 24)
    (fr : Rv64Verifier.Layout.DFrame u v fun x ↦ Within x acc 48)
    (m0 : v.getMem acc = 0) (m8 : v.getMem (acc + 8) = 8) (m16 : v.getMem (acc + 16) = 0)
    (sp : v.getReg .x2 = u.getReg .x2) :
    SS OI s v A k R Q B Bb W L o' F lo lo₂ (heapNext u) Fs acc {} ∧ heapNext v = heapNext u ∧
      Keep u v (heapNext u) := by
  obtain ⟨D, hn, hd, K⟩ := h.blk hpre ha hL hoo Fs (fun _ h ↦ h) hFs fr sp
  refine ⟨⟨D.m, D.fb, D.fo, fun x hx ↦ ?_, ?_, ?_, ha, hL, hoo, hFs, ?_, by rw [hn]⟩, hn, K⟩
  · rw [hd] at hx; exact (h.fb.ok.deep_below hx).2
  · have := D.sl.toH hs; rw [hn] at this; exact this
  · rw [hn]; exact SF.empty _ _ m0 m8 m16
  · have := h.m.bb.2.2.2; exact this

set_option maxRecDepth 8192 in
/-- `acc.add_scaled(other, ONE)`, `other` the one-term form at `q`, one of the sum's terms. -/
theorem SS.asc (hA : Rv64Verifier.Layout.AddScaledSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o' : Word} {F : LayoutMirror.FlushesRust}
    {lo lo₂ H : Nat} {Fs : List (Word × LayoutMirror.FormRust)} {acc q : Word}
    {f g : LayoutMirror.FormRust}
    (hpre : WalkPre s) (h : SS OI s v A k R Q B Bb W L o' F lo lo₂ H Fs acc f) (hq : (q, g) ∈ Fs)
    (hg : ∃ m c, g = LayoutMirror.FormRust.term m c) (hpc : v.pc = 0x800119cc) (x10 : v.getReg .x10 = acc)
    (x11 : v.getReg .x11 = vecPtr v q) (x12 : v.getReg .x12 = vecLen v q)
    (x13 : v.getReg .x13 = 0xa00000b0) :
    ∃ t, Reaches Image.code v t ∧ ((t.pc = returnAddress v ∧ Preserves v t ∧
      SS OI s t A k R Q B Bb W L o' F lo lo₂ H Fs acc (f.add g) ∧ Keep v t H ∧
      heapNext v ≤ heapNext t) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have I := h.m.m.inv
  have hu := I.heap.hi
  simp only [heapEnd] at hu
  obtain ⟨o1, o2, o3⟩ := h.ha
  obtain ⟨p1, p2, -⟩ := h.fo
  have hn : Rv64Verifier.Layout.addScaledStack ≤ 8736 := by decide
  have hHv := h.hH
  have hlen : (vecLen v q).toNat = 1 := by
    obtain ⟨m, c, rfl⟩ := hg
    exact len_term (h.sh.sf _ hq).val
  obtain ⟨t, hr, ⟨hpct, hp, M, sa, mo, fr⟩ | hd⟩ := ascM8 hA hpre h.m hpc x10
    ⟨o1, by omega, o3⟩ (fun e he a ha ↦ h.hL e he a (by simp only [Within] at ha ⊢; omega)) h.sa
    (h.sh.sf _ hq) hlen (le_refl _) (le_refl _) h.hH h.hW x11 x12 x13
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  have ht := M.m.inv.heap.hi
  simp only [heapEnd] at ht
  have hHt : H ≤ heapNext t := le_trans h.hH mo
  have notHeap : ∀ x, CW v t acc Rv64Verifier.Layout.addScaledStack x → heapStart ≤ x.toNat →
      x.toNat < heapNext v → False := fun x hx hs hx2 ↦ by
    simp only [heapNext] at hx2 hu
    rcases hx with hx | hx | hx | hx
    · simp only [Within] at hx; addr_omega [hx, hb1, o1, hx2, hu]
    · rw [stackLo_callee I] at hx; simp only [Within] at hx; addr_omega [hx, hb1, hn, hx2, hu]
    · simp only [Within, nextAddr] at hx; addr_omega [hx, hx2, hu]
    · simp only [Fresh, heapNext] at hx; omega
  have Fb := h.fb.frame' fr (fun x hx hw ↦ by
      rcases hw with hw | hw
      · rcases hw with hw | hw | hw | hw
        · exact h.hoo x (by simp only [Within] at hw ⊢; omega) hx
        · rw [stackLo_callee I] at hw; simp only [Within] at hx hw; addr_omega [hx, hw, hb1, hn, p1, p2]
        · simp only [Within, nextAddr] at hx hw; addr_omega [hx, hw, hb1, p1, p2]
        · simp only [Fresh, heapNext] at hw; simp only [Within] at hx
          simp only [heapNext] at ht; addr_omega [hx, hw, hb1, p1, p2, ht]
      · simp only [Within] at hx; simp only [heapNext] at hu hHv; addr_omega [hx, hw, hb1, p1, p2, hu, hHv])
    (fun x hx hw ↦ by
      have d1 := h.fd x hx
      have d2 := h.fb.ok.deep_below hx
      rcases hw with hw | hw
      · exact notHeap x hw d2.1 d2.2
      · omega) (by addr_omega [hb1, p2]) I.heap mo
  refine ⟨t, hr, Or.inl ⟨hpct, hp, ⟨M, Fb.1, h.fo, fun x hx ↦ h.fd x (by rw [← Fb.2]; exact hx),
    h.sh.frame' hpre I fr hn ⟨o1, by omega, o3⟩
      (fun e he x hx hw ↦ h.hFs e he x hx (by simp only [Within] at hw ⊢; omega))
      (Or.inl (le_refl _)) h.hH mo M.m.inv.heap mo,
    sa, ⟨o1, o2, o3⟩, h.hL, h.hoo, h.hFs, h.hW, hHt⟩, ?_, mo⟩⟩
  refine Keep.of fr fun x hx hs ↦ ?_
  rcases hx with hx | hx
  · by_contra hc
    exact notHeap x hx hs (by omega)
  · exact hx.1

end Rv64Verifier.Proofs.Walk
