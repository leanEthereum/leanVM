import Rv64Verifier.Proofs.Walk.R8C

/-!
# `walk`: `tables()`, the calls that build a form (R8)

A call that writes one form's 24 bytes, its stack, `NEXT` and fresh heap keeps `M8` and the
`Flushes` under construction (`M8.cw`), and the forms held in frame slots or in the heap (`SFs.cw`).
`colM8`, `prodM8` and `termM8` are `col`, `prod` and `term` into a frame slot.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

theorem W6.mono {s v v' : MachineState} {B : Nat} {a : Word} (h : W6 s B v a)
    (hm : heapNext v ≤ heapNext v') : W6 s B v' a := by
  rcases h with h | h | h | h | h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, by omega⟩))))

/-- A frame slot apart from the finished tables' is what `M8` lets a step write. -/
theorem slotOk {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L)
    {o : Word} {n : Nat} (ho : InSlot s o n) (hL : ∀ e ∈ L, ∀ a, Within a o n → ¬ Within a e.1 72) :
    ∀ a, Within a o n → W6 s B u a ∧ M8W s W L a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨o1, o2, -⟩ := ho
  have hu := h.m.inv.heap.hi
  have hW := h.bb.2.2.2
  simp only [heapEnd] at hu
  intro a ha
  refine ⟨Or.inl (by simp only [Within] at ha ⊢; addr_omega [ha, o1, o2, hb1]), ?_⟩
  simp only [M8W]
  refine ⟨?_, ?_, ?_, ?_, fun e he ↦ hL e he a ha⟩ <;> simp only [Within] at ha ⊢ <;>
    addr_omega [ha, o1, o2, hb1, hW, hu]

/-- A callee writing the 24 bytes at `o`, its stack, `NEXT` and fresh heap keeps `M8` and the
`Flushes` under construction at `o'`. -/
theorem M8.cw {OI : MachineState → Word → List (List Opening) → Prop} {s u t : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o o' : Word} {F : LayoutMirror.FlushesRust}
    {lo n : Nat} (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L) (fb : FB u o' F lo)
    (ho' : InSlot s o' 48) (fr : Rv64Verifier.Layout.DFrame u t (CW u t o n)) (hn : n ≤ 8736)
    (hW : ∀ a, Within a o 24 → W6 s B u a ∧ M8W s W L a)
    (hF : ∀ a, Within a o 24 → ¬ Within a o' 48 ∧ ¬ flushesDeep u o' a)
    (hv : HeapOk t) (mono : heapNext u ≤ heapNext t) (sp : t.getReg .x2 = u.getReg .x2) :
    M8 OI s t A k R Q B Bb W L ∧ FB t o' F lo ∧ flushesDeep t o' = flushesDeep u o' := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hh := hv.hi
  have hu := h.m.inv.heap.hi
  have hW' := h.bb.2.2.2
  have hBW : B ≤ W := by have := h.bb; omega
  simp only [heapEnd, heapNext] at hh hu hW'
  obtain ⟨p1, p2, -⟩ := ho'
  have M := h.step hpre fr (fun a ha ↦ ?_) (fun a ha ↦ ?_) hv mono sp
  · have G := Rv64Verifier.Layout.flushesOf_frame fr fb.ok (fun x hx hw ↦ ?_) (fun x hx hw ↦ ?_)
      (by addr_omega [hb1, p2]) h.m.inv.heap mono
    · exact ⟨M, ⟨G.2.1, by rw [G.1]; exact fb.val, fun x hx ↦ fb.deep x (by rw [← G.2.2.1]; exact hx)⟩, G.2.2.1⟩
    · rcases hw with hw | hw | hw | hw
      · exact (hF x hw).1 hx
      · rw [stackLo_callee h.m.inv] at hw; simp only [Within] at hx hw; addr_omega [hx, hw, hb1, hn, p1, p2]
      · simp only [Within] at hx hw; addr_omega [hx, hw, hb1, p1, p2]
      · simp only [Fresh, heapNext] at hw; simp only [Within] at hx; addr_omega [hx, hw, hb1, p1, p2, hh]
    · have hdb := (fb.ok.deep_below hx).2
      simp only [heapNext] at hdb
      rcases hw with hw | hw | hw | hw
      · exact (hF x hw).2 hx
      · rw [stackLo_callee h.m.inv] at hw; simp only [Within] at hw; addr_omega [hw, hb1, hn, hdb, hu]
      · simp only [Within] at hw; addr_omega [hw, hdb, hu]
      · simp only [Fresh, heapNext] at hw; omega
  · rcases ha with ha | ha | ha | ha
    · exact (hW a ha).1.mono mono
    · exact Or.inr (Or.inr (Or.inr (Or.inl (stackLo_w6 hpre h.m.inv hn ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp only [heapNext] at ha; omega, ha.2⟩))))
  · rcases ha with ha | ha | ha | ha
    · exact (hW a ha).2
    · simp only [M8W]
      rw [stackLo_callee h.m.inv] at ha
      refine ⟨?_, ?_, ?_, ?_, fun e he hw ↦ ?_⟩ <;> simp only [Within] at ha ⊢
      all_goals first
        | addr_omega [ha, hb1, hn, hW', hu]
        | (obtain ⟨o1, o2, -⟩ := (h.tabs e he).1; simp only [Within] at hw; addr_omega [ha, hb1, hn, o1, hw])
    · simp only [M8W]
      refine ⟨?_, ?_, ?_, ?_, fun e he hw ↦ ?_⟩ <;> simp only [Within] at ha ⊢
      all_goals first
        | addr_omega [ha, hb1, hW', hu]
        | (obtain ⟨o1, o2, -⟩ := (h.tabs e he).1; simp only [Within] at hw; addr_omega [ha, hb1, o1, hw])
    · simp only [M8W]
      simp only [Fresh, heapNext] at ha
      refine ⟨by omega, ?_, ?_, ?_, fun e he hw ↦ ?_⟩
      all_goals first
        | addr_omega [ha, hb1, hh]
        | (obtain ⟨o1, o2, -⟩ := (h.tabs e he).1; simp only [Within] at hw; addr_omega [ha, hb1, o1, hw, hh])

theorem SF.wid {u : MachineState} {e : Word} {f : LayoutMirror.FormRust} {lo hi lo' hi' : Nat}
    (h : SF u e f lo hi) (hl : lo' ≤ lo) (hh : hi ≤ hi') : SF u e f lo' hi' :=
  ⟨h.ok, h.val, fun x hx ↦ ⟨by have := (h.buf x hx).1; omega, by have := (h.buf x hx).2; omega⟩⟩

/-- The forms `Fs`, each in a frame slot or in the heap, their buffers in `[lo, heapNext u)`. -/
structure SFs (s u : MachineState) (lo : Nat) (Fs : List (Word × LayoutMirror.FormRust)) : Prop where
  sf : ∀ e ∈ Fs, SF u e.1 e.2 lo (heapNext u)
  loc : ∀ e ∈ Fs, InSlot s e.1 24 ∨ e.1.toNat + 24 ≤ heapNext u

/-- A callee writing a frame slot `o` apart from every form's header keeps the forms. -/
theorem SFs.cw {s u t : MachineState} {o : Word} {n lo : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    (hpre : WalkPre s) (h : Inv s u) (hf : SFs s u lo Fs)
    (fr : Rv64Verifier.Layout.DFrame u t (CW u t o n)) (hn : n ≤ 8736) (ho : InSlot s o 24)
    (hoo : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x o 24) (hv : HeapOk t)
    (mono : heapNext u ≤ heapNext t) : SFs s t lo Fs := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨o1, o2, -⟩ := ho
  have hu := h.heap.hi
  have ht := hv.hi
  simp only [heapEnd, heapNext] at hu ht mono
  refine ⟨fun e he ↦ ?_, fun e he ↦ (hf.loc e he).imp id fun h ↦ by simp only [heapNext] at h ⊢; omega⟩
  have hl := hf.loc e he
  simp only [heapNext] at hl
  have he' : e.1.toNat + 24 ≤ 2 ^ 64 := by
    rcases hl with ⟨e1, e2, -⟩ | hl
    · addr_omega [hb1, e2]
    · omega
  refine ((hf.sf e he).frame fr (fun x hx hw ↦ ?_) (fun x hx1 hx2 hw ↦ ?_) he' h.heap
    (by simp only [heapNext]; omega)).wid (le_refl _) (by simp only [heapNext]; omega)
  · simp only [Within] at hx
    rcases hw with hw | hw | hw | hw
    · exact hoo e he x (by simp only [Within]; exact hx) hw
    · rw [stackLo_callee h] at hw; simp only [Within] at hw
      rcases hl with ⟨e1, e2, -⟩ | hl <;> first
        | addr_omega [hx, hw, hb1, hn, e1, e2, hu] | addr_omega [hx, hw, hb1, hn, hl, hu]
    · simp only [Within] at hw; rcases hl with ⟨e1, e2, -⟩ | hl <;> first
        | addr_omega [hx, hw, hb1, e1, e2, hu] | addr_omega [hx, hw, hb1, hl, hu]
    · simp only [Fresh, heapNext] at hw
      rcases hl with ⟨e1, e2, -⟩ | hl <;> first
        | addr_omega [hx, hw, hb1, e1, e2, hu, ht] | addr_omega [hx, hw, hb1, hl, hu, ht]
  · simp only [heapNext] at hx2
    rcases hw with hw | hw | hw | hw
    · simp only [Within] at hw; addr_omega [hw, hb1, o1, o2, hx2, hu]
    · rw [stackLo_callee h] at hw; simp only [Within] at hw; addr_omega [hw, hb1, hn, hx2, hu]
    · simp only [Within] at hw; addr_omega [hw, hx2, hu]
    · simp only [Fresh, heapNext] at hw; omega

/-- A step that writes no memory keeps the forms. -/
theorem SFs.same {s u v : MachineState} {lo : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    (hpre : WalkPre s) (h : SFs s u lo Fs) (hm : ∀ a, v.getMem a = u.getMem a) (hheap : HeapOk u) :
    SFs s v lo Fs := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  have hu := hheap.hi
  simp only [heapEnd] at hu
  refine ⟨fun e he ↦ ?_, fun e he ↦ by rw [hn]; exact h.loc e he⟩
  rw [hn]
  refine (h.sf e he).frame (Rv64Verifier.Layout.DFrame.of_same hm (fun _ ↦ False)) (fun _ _ h ↦ h)
    (fun _ _ _ h ↦ h) ?_ hheap hn.ge
  rcases h.loc e he with ⟨e1, e2, -⟩ | hl
  · addr_omega [hb1, e2]
  · omega

theorem M8.same {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L)
    (hm : ∀ a, v.getMem a = u.getMem a) (sp : v.getReg .x2 = u.getReg .x2) :
    M8 OI s v A k R Q B Bb W L := by
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  exact h.step hpre (Rv64Verifier.Layout.DFrame.of_same hm (fun _ ↦ False)) (fun _ h ↦ h.elim)
    (fun _ h ↦ h.elim) ⟨hn ▸ h.m.inv.heap.lo, hn ▸ h.m.inv.heap.hi⟩ hn.ge sp

theorem FB.same {s u v : MachineState} {o : Word} {F : LayoutMirror.FlushesRust} {lo : Nat}
    (hpre : WalkPre s) (h : FB u o F lo) (ho : InSlot s o 48) (hheap : HeapOk u)
    (hm : ∀ a, v.getMem a = u.getMem a) : FB v o F lo := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hn : heapNext v = heapNext u := by simp only [heapNext, hm]
  obtain ⟨o1, o2, -⟩ := ho
  exact (h.frame (Rv64Verifier.Layout.DFrame.of_same hm (fun _ ↦ False)) (fun _ _ h ↦ h)
    (fun _ _ _ h ↦ h) (by addr_omega [hb1, o2]) hheap hn.ge).1

/-- A form built into the 24 bytes at `o` keeps `M8` and the `Flushes` under construction. -/
theorem M8.newForm {OI : MachineState → Word → List (List Opening) → Prop} {s u t : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o o' : Word} {F : LayoutMirror.FlushesRust}
    {lo n : Nat} (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L) (fb : FB u o' F lo)
    (ho' : InSlot s o' 48) (nf : Rv64Verifier.Layout.NewForm u t o n) (hn : n ≤ 8736)
    (hW : ∀ a, Within a o 24 → W6 s B u a ∧ M8W s W L a)
    (hF : ∀ a, Within a o 24 → ¬ Within a o' 48 ∧ ¬ flushesDeep u o' a)
    (sp : t.getReg .x2 = u.getReg .x2) :
    M8 OI s t A k R Q B Bb W L ∧ FB t o' F lo ∧ flushesDeep t o' = flushesDeep u o' :=
  h.cw hpre fb ho' nf.frame hn hW hF nf.heap nf.mono sp

/-- A slot apart from the `Flushes` under construction at a slot `o'`. -/
theorem slotF {s u : MachineState} {o o' : Word} {F : LayoutMirror.FlushesRust} {lo : Nat}
    (hpre : WalkPre s) (fb : FB u o' F lo) (hheap : HeapOk u) (ho : InSlot s o 24)
    (hoo : ∀ a, Within a o 24 → ¬ Within a o' 48) :
    ∀ a, Within a o 24 → ¬ Within a o' 48 ∧ ¬ flushesDeep u o' a := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨o1, o2, -⟩ := ho
  intro a ha
  refine ⟨hoo a ha, fun hd ↦ ?_⟩
  have h1 := (fb.ok.deep_below hd).2
  have hu := hheap.hi
  simp only [heapEnd, heapNext] at hu h1
  simp only [Within] at ha
  addr_omega [ha, o1, o2, hb1, h1, hu]

theorem SFs.nil (s u : MachineState) (lo : Nat) : SFs s u lo [] :=
  ⟨fun _ h ↦ absurd h List.not_mem_nil, fun _ h ↦ absurd h List.not_mem_nil⟩

theorem SFs.cons {s u : MachineState} {lo lo' hi : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    {o : Word} {f : LayoutMirror.FormRust} (h : SFs s u lo Fs) (hf : SF u o f lo' hi) (hl : lo ≤ lo')
    (hh : hi ≤ heapNext u) (ho : InSlot s o 24 ∨ o.toNat + 24 ≤ heapNext u) :
    SFs s u lo ((o, f) :: Fs) :=
  ⟨fun e he ↦ by
    rcases List.mem_cons.mp he with rfl | he
    · exact hf.wid hl hh
    · exact h.sf e he,
   fun e he ↦ by
    rcases List.mem_cons.mp he with rfl | he
    · exact ho
    · exact h.loc e he⟩

/-- A form built into a frame slot `o`: `M8`, the `Flushes` under construction and the forms held
are kept, and the new form joins them. -/
theorem newSlot {OI : MachineState → Word → List (List Opening) → Prop} {s u t : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o o' : Word} {F : LayoutMirror.FlushesRust}
    {lo lo₂ n : Nat} {Fs : List (Word × LayoutMirror.FormRust)} {f : LayoutMirror.FormRust}
    (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L) (fb : FB u o' F lo) (ho' : InSlot s o' 48)
    (hS : SFs s u lo₂ Fs) (hlo₂ : lo₂ ≤ heapNext u) (ho : InSlot s o 24)
    (hL : ∀ e ∈ L, ∀ a, Within a o 24 → ¬ Within a e.1 72) (hoo : ∀ a, Within a o 24 → ¬ Within a o' 48)
    (hFs : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x o 24)
    (nf : Rv64Verifier.Layout.NewForm u t o n) (hn : n ≤ 8736) (hv : formOf t o = f)
    (sp : t.getReg .x2 = u.getReg .x2) :
    M8 OI s t A k R Q B Bb W L ∧ FB t o' F lo ∧ heapNext u ≤ heapNext t ∧ SFs s t lo₂ ((o, f) :: Fs) ∧
      flushesDeep t o' = flushesDeep u o' := by
  have K := h.newForm hpre fb ho' nf hn (slotOk hpre h ho hL) (slotF hpre fb h.m.inv.heap ho hoo) sp
  exact ⟨K.1, K.2.1, nf.mono, (hS.cw hpre h.m.inv nf.frame hn ho hFs nf.heap nf.mono).cons
    (SF.ofNew nf hv) hlo₂ (le_refl _) (Or.inl ho), K.2.2⟩

/-- What a form's slot gives the callee's precondition. -/
theorem slotPre {s u : MachineState} (hpre : WalkPre s) (h : Inv s u) {o : Word} {m : Nat}
    (ho : InSlot s o 24) (hm : m ≤ 8736) :
    ValidMemRange o 3 ∧ Outside u o 24 ∧ Apart o 24 (stackLo u m) m :=
  slotW (n := 3) hpre h (by simpa [InSlot] using ho) hm

set_option maxRecDepth 8192 in
/-- `col(a1, a2)` into a frame slot. -/
theorem colSlot (hC : Rv64Verifier.Layout.ColSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o o' : Word} {F : LayoutMirror.FlushesRust}
    {lo lo₂ : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L) (fb : FB u o' F lo) (ho' : InSlot s o' 48)
    (hS : SFs s u lo₂ Fs) (hlo₂ : lo₂ ≤ heapNext u) (ho : InSlot s o 24)
    (hL : ∀ e ∈ L, ∀ a, Within a o 24 → ¬ Within a e.1 72) (hoo : ∀ a, Within a o 24 → ¬ Within a o' 48)
    (hFs : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x o 24)
    (hpc : u.pc = 0x80004b34) (x10 : u.getReg .x10 = o) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      M8 OI s t A k R Q B Bb W L ∧ FB t o' F lo ∧ heapNext u ≤ heapNext t ∧
      SFs s t lo₂ ((o, LayoutMirror.colRust (u.getReg .x11).toNat (u.getReg .x12).toNat) :: Fs) ∧
      flushesDeep t o' = flushesDeep u o') ∨
      Dead Image.code t) := by
  have hn : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  obtain ⟨v1, v2, v3⟩ := slotPre hpre h.m.inv ho hn
  have pre : Rv64Verifier.Layout.ColPre u := {
    heap := h.m.inv.heap
    stack := stk_sub hpre h.m.inv hn (by decide)
    out := by rw [x10]; exact v1
    outFree := by rw [x10]; exact v2
    outStack := by rw [x10]; exact v3
    rodata := h.m.inv.rodata hpre }
  obtain ⟨t, hr, ⟨hpct, hp, nf, fv⟩ | hd⟩ := hC u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  rw [x10] at nf fv
  exact ⟨t, hr, Or.inl ⟨hpct, hp, newSlot hpre h fb ho' hS hlo₂ ho hL hoo hFs nf hn fv (hp.reg .x2)⟩⟩

set_option maxRecDepth 8192 in
/-- `prod(a1, a2, a3)` into a frame slot. -/
theorem prodSlot (hP : Rv64Verifier.Layout.ProdSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o o' : Word} {F : LayoutMirror.FlushesRust}
    {lo lo₂ : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L) (fb : FB u o' F lo) (ho' : InSlot s o' 48)
    (hS : SFs s u lo₂ Fs) (hlo₂ : lo₂ ≤ heapNext u) (ho : InSlot s o 24)
    (hL : ∀ e ∈ L, ∀ a, Within a o 24 → ¬ Within a e.1 72) (hoo : ∀ a, Within a o 24 → ¬ Within a o' 48)
    (hFs : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x o 24)
    (hpc : u.pc = 0x80005138) (x10 : u.getReg .x10 = o) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      M8 OI s t A k R Q B Bb W L ∧ FB t o' F lo ∧ heapNext u ≤ heapNext t ∧
      SFs s t lo₂ ((o, LayoutMirror.prodRust (u.getReg .x11).toNat (u.getReg .x12).toNat
        (u.getReg .x13).toNat) :: Fs) ∧ flushesDeep t o' = flushesDeep u o') ∨ Dead Image.code t) := by
  have hn : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  obtain ⟨v1, v2, v3⟩ := slotPre hpre h.m.inv ho hn
  have pre : Rv64Verifier.Layout.ColPre u := {
    heap := h.m.inv.heap
    stack := stk_sub hpre h.m.inv hn (by decide)
    out := by rw [x10]; exact v1
    outFree := by rw [x10]; exact v2
    outStack := by rw [x10]; exact v3
    rodata := h.m.inv.rodata hpre }
  obtain ⟨t, hr, ⟨hpct, hp, nf, fv⟩ | hd⟩ := hP u hpc pre
  swap
  · exact ⟨t, hr, Or.inr hd⟩
  rw [x10] at nf fv
  exact ⟨t, hr, Or.inl ⟨hpct, hp, newSlot hpre h fb ho' hS hlo₂ ho hL hoo hFs nf hn fv (hp.reg .x2)⟩⟩

set_option maxRecDepth 8192 in
/-- `Form::term(One, ZERO)` into a frame slot, the monomial `One` at the slot `m`. -/
theorem termSlot (hT : Rv64Verifier.Layout.TermSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o o' m : Word} {F : LayoutMirror.FlushesRust}
    {lo lo₂ : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L) (fb : FB u o' F lo) (ho' : InSlot s o' 48)
    (hS : SFs s u lo₂ Fs) (hlo₂ : lo₂ ≤ heapNext u) (ho : InSlot s o 24)
    (hL : ∀ e ∈ L, ∀ a, Within a o 24 → ¬ Within a e.1 72) (hoo : ∀ a, Within a o 24 → ¬ Within a o' 48)
    (hFs : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x o 24)
    (hpc : u.pc = 0x800050a8) (x10 : u.getReg .x10 = o) (x11 : u.getReg .x11 = m) (hm : InSlot s m 24)
    (hm0 : u.getMem m = 0) (x12 : u.getReg .x12 = 0xa0000068) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      M8 OI s t A k R Q B Bb W L ∧ FB t o' F lo ∧ heapNext u ≤ heapNext t ∧
      SFs s t lo₂ ((o, LayoutMirror.constantRust 0) :: Fs) ∧ flushesDeep t o' = flushesDeep u o') ∨
      Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hn : Rv64Verifier.Layout.termStack ≤ 8736 := by decide
  have I := h.m.inv
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
  refine ⟨t, hr, Or.inl ⟨hpct, hp, newSlot hpre h fb ho' hS hlo₂ ho hL hoo hFs nf hn ?_ (hp.reg .x2)⟩⟩
  rw [fv, x11, x12, Rv64Verifier.Layout.monoOf, hm0, zeroE (I.rodata hpre)]
  rfl

/-- A block that writes only a frame slot `o` apart from the finished tables, the `Flushes` under
construction and the forms held keeps them all, and `NEXT`. -/
theorem slotWrite {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o o' : Word} {F : LayoutMirror.FlushesRust}
    {lo lo₂ : Nat} {Fs : List (Word × LayoutMirror.FormRust)}
    (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L) (fb : FB u o' F lo) (ho' : InSlot s o' 48)
    (hS : SFs s u lo₂ Fs) (ho : InSlot s o 24)
    (hL : ∀ e ∈ L, ∀ a, Within a o 24 → ¬ Within a e.1 72) (hoo : ∀ a, Within a o 24 → ¬ Within a o' 48)
    (hFs : ∀ e ∈ Fs, ∀ x, Within x e.1 24 → ¬ Within x o 24)
    (fr : Rv64Verifier.Layout.DFrame u v fun x ↦ Within x o 24) (sp : v.getReg .x2 = u.getReg .x2) :
    M8 OI s v A k R Q B Bb W L ∧ FB v o' F lo ∧ SFs s v lo₂ Fs ∧ heapNext v = heapNext u ∧
      flushesDeep v o' = flushesDeep u o' := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨o1, o2, o3⟩ := ho
  have hn : heapNext v = heapNext u := by
    simp only [heapNext]
    rw [fr nextAddr (fun x hx hw ↦ by simp only [Within] at hx hw; addr_omega [hx, hw, hb1, o1, o2])
      (by decide)]
  have hv : HeapOk v := ⟨hn ▸ h.m.inv.heap.lo, hn ▸ h.m.inv.heap.hi⟩
  have fr' : Rv64Verifier.Layout.DFrame u v (CW u v o 0) := fr.mono fun a ha ↦ Or.inl ha
  have K := h.cw hpre fb ho' fr' (by decide) (slotOk hpre h ⟨o1, o2, o3⟩ hL)
    (slotF hpre fb h.m.inv.heap ⟨o1, o2, o3⟩ hoo) hv hn.ge sp
  exact ⟨K.1, K.2.1, hS.cw hpre h.m.inv fr' (by decide) ⟨o1, o2, o3⟩ hFs hv hn.ge, hn, K.2.2⟩

/-- The finished XOR, MUL and KECCAK tables' slots. -/
abbrev L3 (s : MachineState) : List (Word × LayoutMirror.TableRust) :=
  [(s.getReg .x2 - 1704, kTable), (s.getReg .x2 - 1632, xorT), (s.getReg .x2 - 1560, mulT)]

theorem l3_apart {s : MachineState} (hpre : WalkPre s) {o : Word} {n : Nat}
    (ho : (s.getReg .x2 - 1488).toNat ≤ o.toNat) : ∀ e ∈ L3 s, ∀ a, Within a o n → ¬ Within a e.1 72 := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  intro e he a ha hw
  simp only [L3, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;> simp only [Within] at ha hw <;> addr_omega [ha, hw, hb1, ho]

theorem deep_same {u v : MachineState} {o : Word} (hm : ∀ a, v.getMem a = u.getMem a) :
    flushesDeep v o = flushesDeep u o := by
  funext x
  simp only [flushesDeep, Rv64Verifier.Layout.formVecsDeep, Rv64Verifier.Layout.formVecsBuf,
    Rv64Verifier.Layout.formVecDeep, Rv64Verifier.Layout.formVecBuf, Rv64Verifier.Layout.formsDeep,
    formBuf, vecCap, vecPtr, vecLen, hm]

end Rv64Verifier.Proofs.Walk
