import Rv64Verifier.Proofs.Walk.R7D
import Rv64Verifier.Proofs.Layout.ContractsArith

/-!
# `walk`: `tables()`, the state the five tables are built in (R8)

`M8` keeps the finished tables across a step that writes none of their 72-byte slots, nothing
they reach (all below `W`), nor the heights' lengths or the tables' buffer's slot (`M8.step`); a
table built from `W` on joins them (`M8.push`). A `Flushes` under construction sits in a frame
slot, all it reaches from `lo` on (`FB`). `arithCall` and `padCall` are the calls of
`flushes_arith` and of `vec![ZERO; n]`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep)

/-! ## A `Table` in memory -/

theorem TableAt.below {u : MachineState} {a : Word} {t : LayoutMirror.TableRust} (h : TableAt u a t)
    {x : Word} (hx : tableDeep u a x) : x.toNat < heapNext u := by
  rcases hx with hx | hx
  · have hr := h.padVec.raw
    simp only [RawVecOk, Buf] at hr
    simp only [Within] at hx
    rcases hr.2 with h0 | h0 <;> omega
  · exact (h.ok.deep_below hx).2

/-- A `Table` across a frame that writes neither its 72 bytes nor what it reaches. -/
theorem TableAt.frame {u v : MachineState} {a : Word} {t : LayoutMirror.TableRust} {w : Word → Prop}
    (h : TableAt u a t) (fr : Rv64Verifier.Layout.DFrame u v w) (hh : ∀ x, Within x a 72 → ¬ w x)
    (hd : ∀ x, tableDeep u a x → ¬ w x) (ha : a.toNat + 72 ≤ 2 ^ 64) (hheap : HeapOk u)
    (mono : heapNext u ≤ heapNext v) : TableAt v a t ∧ tableDeep v a = tableDeep u a := by
  have h0 := fr a (fun x hx ↦ hh x (by simp only [Within] at hx ⊢; addr_omega [hx, ha])) (by omega)
  have h8 := fr (a + 8) (fun x hx ↦ hh x (by simp only [Within] at hx ⊢; addr_omega [hx, ha]))
    (by addr_omega [ha])
  have h16 := fr (a + 16) (fun x hx ↦ hh x (by simp only [Within] at hx ⊢; addr_omega [hx, ha]))
    (by addr_omega [ha])
  have G := Rv64Verifier.Layout.flushesOf_frame fr h.ok
    (fun x hx ↦ hh x (by simp only [Within] at hx ⊢; addr_omega [hx, ha]))
    (fun x hx ↦ hd x (Or.inr hx)) (by addr_omega [ha]) hheap mono
  have hr := h.padVec.raw
  have hl := h.padVec.len
  simp only [RawVecOk, Buf, vecPtr, vecCap, vecLen] at hr hl
  have hes : vecEs v a = vecEs u a := by
    simp only [vecEs, vecPtr, vecLen, h8, h16]
    refine Bus.eListAt_congr fun i hi ↦ ?_
    have hin (c : Nat) (hc : c < 24) : tableDeep u a (u.getMem (a + 8) + BitVec.ofNat 64 (24 * i) +
        BitVec.ofNat 64 c) := by
      left; simp only [Within, vecPtr, vecCap]
      rcases hr.2 with h0' | h0' <;> addr_omega [hi, hl, hc, h0']
    have k (c : Nat) (hc : c ≤ 16) :
        v.getMem (u.getMem (a + 8) + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 c) =
          u.getMem (u.getMem (a + 8) + BitVec.ofNat 64 (24 * i) + BitVec.ofNat 64 c) :=
      fr _ (fun x hx hw ↦ by
        have := hd x
        simp only [Within] at hx
        refine this ?_ hw
        left; simp only [Within, vecPtr, vecCap]
        rcases hr.2 with h0' | h0' <;> addr_omega [hi, hl, hc, h0', hx]) (by
          rcases hr.2 with h0' | h0' <;> addr_omega [hi, hl, hc, h0'])
    apply eAt_congr
    · have := k 0 (by omega); rwa [add_ofNat_zero] at this
    · exact k 8 (by omega)
    · exact k 16 (by omega)
  have hdeep : tableDeep v a = tableDeep u a := by
    funext x; simp only [tableDeep, vecPtr, vecCap, h0, h8, G.2.2.1]
  exact ⟨⟨vecOk_move h0 h8 h16 mono h.padVec, by rw [hes]; exact h.pad, G.2.1, by rw [G.1]; exact h.flushes⟩,
    hdeep⟩

/-! ## `M8` across a step -/

/-- What a step past finished tables may not write. -/
@[rv_addr] def M8W (s : MachineState) (W : Nat) (L : List (Word × LayoutMirror.TableRust)) (a : Word) :
    Prop :=
  W ≤ a.toNat ∧ ¬ Within a (s.getReg .x2 - 2520) 8 ∧ ¬ Within a (s.getReg .x2 - 2504) 8 ∧
    ¬ Within a (s.getReg .x2 - 2456) 8 ∧ ∀ e ∈ L, ¬ Within a e.1 72

theorem M8.step {OI : MachineState → Word → List (List Opening) → Prop} {s u v : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {w : Word → Prop} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W L) (fr : Rv64Verifier.Layout.DFrame u v w)
    (hw : ∀ a, w a → W6 s B v a) (hk : ∀ a, w a → M8W s W L a) (hv : HeapOk v)
    (mono : heapNext u ≤ heapNext v) (sp : v.getReg .x2 = u.getReg .x2) : M8 OI s v A k R Q B Bb W L := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  exact {
    m := h.m.step hpre (fr.mono hw) hv mono sp
    lens := ⟨by rw [fr _ (fun x hx hwx ↦ (hk x hwx).2.1 hx) (by addr_omega [hb1])]; exact h.lens.1,
      by rw [fr _ (fun x hx hwx ↦ (hk x hwx).2.2.1 hx) (by addr_omega [hb1])]; exact h.lens.2⟩
    bb := ⟨h.bb.1, h.bb.2.1, h.bb.2.2.1, by have := h.bb.2.2.2; omega⟩
    slot := by rw [fr _ (fun x hx hwx ↦ (hk x hwx).2.2.2.1 hx) (by addr_omega [hb1])]; exact h.slot
    tabs := fun e he ↦ by
      obtain ⟨hs, ht, hd⟩ := h.tabs e he
      obtain ⟨o1, o2, o3⟩ := hs
      have T := ht.frame fr (fun x hx hwx ↦ (hk x hwx).2.2.2.2 e he hx)
        (fun x hx hwx ↦ by have := (hd x hx).2.1; have := (hk x hwx).1; omega)
        (by addr_omega [hb1, o2]) h.m.inv.heap mono
      exact ⟨⟨o1, o2, o3⟩, T.1, fun x hx ↦ hd x (by rw [← T.2]; exact hx)⟩ }

/-- A table built from `W` on joins the finished ones. -/
theorem M8.push {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o : Word} {t : LayoutMirror.TableRust}
    (h : M8 OI s u A k R Q B Bb W L) (ho : InSlot s o 72) (ht : TableAt u o t)
    (hd : ∀ x, tableDeep u o x → W ≤ x.toNat) : M8 OI s u A k R Q B Bb (heapNext u) (L ++ [(o, t)]) := by
  obtain ⟨b1, b2, b3, b4⟩ := h.bb
  refine ⟨h.m, h.lens, ⟨b1, b2, by omega, le_refl _⟩, h.slot, fun e he ↦ ?_⟩
  rcases List.mem_append.mp he with he | he
  · obtain ⟨hs, ht', hd'⟩ := h.tabs e he
    exact ⟨hs, ht', fun x hx ↦ by have := hd' x hx; exact ⟨this.1, by omega, this.2.2⟩⟩
  · simp only [List.mem_singleton] at he
    subst he
    exact ⟨ho, ht, fun x hx ↦ by
      have := hd x hx; have := ht.below hx
      simp only [Within]; omega⟩

/-! ## A `Flushes` under construction -/

/-- The `Flushes` at `o` holds `F`, all it reaches from `lo` on. -/
structure FB (u : MachineState) (o : Word) (F : LayoutMirror.FlushesRust) (lo : Nat) : Prop where
  ok : FlushesOk u o
  val : flushesOf u o = F
  deep : ∀ x, flushesDeep u o x → lo ≤ x.toNat

theorem FB.frame {u v : MachineState} {o : Word} {F : LayoutMirror.FlushesRust} {lo : Nat}
    {w : Word → Prop} (h : FB u o F lo) (fr : Rv64Verifier.Layout.DFrame u v w)
    (hh : ∀ x, Within x o 48 → ¬ w x) (hd : ∀ x, lo ≤ x.toNat → x.toNat < heapNext u → ¬ w x)
    (ho : o.toNat + 48 ≤ 2 ^ 64) (hheap : HeapOk u) (mono : heapNext u ≤ heapNext v) :
    FB v o F lo ∧ flushesDeep v o = flushesDeep u o := by
  have G := Rv64Verifier.Layout.flushesOf_frame fr h.ok hh
    (fun x hx ↦ hd x (h.deep x hx) (h.ok.deep_below hx).2) ho hheap mono
  exact ⟨⟨G.2.1, by rw [G.1]; exact h.val, fun x hx ↦ h.deep x (by rw [← G.2.2.1]; exact hx)⟩, G.2.2.1⟩

/-- A `Flushes` whose header was copied from `o'` to the frame slot `o`. -/
theorem FB.move {u v : MachineState} {o o' : Word} {F : LayoutMirror.FlushesRust} {lo : Nat}
    {w : Word → Prop} (h : FB u o' F lo) (fr : Rv64Verifier.Layout.DFrame u v w)
    (g0 : v.getMem o = u.getMem o') (g8 : v.getMem (o + 8) = u.getMem (o' + 8))
    (g16 : v.getMem (o + 16) = u.getMem (o' + 16)) (g24 : v.getMem (o + 24) = u.getMem (o' + 24))
    (g32 : v.getMem (o + 24 + 8) = u.getMem (o' + 24 + 8))
    (g40 : v.getMem (o + 24 + 16) = u.getMem (o' + 24 + 16))
    (hd : ∀ x, lo ≤ x.toNat → x.toNat < heapNext u → ¬ w x) (ho : 0x78000000 ≤ o.toNat)
    (hheap : HeapOk u) (mono : heapNext u ≤ heapNext v) : FB v o F lo := by
  have hu := hheap.hi
  simp only [heapEnd] at hu
  have G := Rv64Verifier.Layout.Arith.flushesOf_move fr h.ok g0 g8 g16 g24 g32 g40
    (fun x hx ↦ hd x (h.deep x hx) (h.ok.deep_below hx).2)
    (fun x hx hd' ↦ by have := (h.ok.deep_below hd').2; simp only [Within] at hx; omega) hheap mono
  exact ⟨G.2.1, by rw [G.1]; exact h.val, fun x hx ↦ h.deep x (by rw [← G.2.2]; exact hx)⟩

/-! ## The calls -/

/-- What a callee writing `n` bytes at the frame slot `o` writes, as `M8` sees it. -/
theorem M8.call {OI : MachineState → Word → List (List Opening) → Prop} {s u t : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o : Word} {n m : Nat} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W L)
    (fr : Rv64Verifier.Layout.DFrame u t fun a ↦ Within a o n ∨ Within a (stackLo u m) m ∨
      Within a nextAddr 8 ∨ Fresh u t a)
    (ho : (s.getReg .x2 - 2080).toNat ≤ o.toNat ∧ o.toNat + n ≤ (s.getReg .x2 - 104).toNat)
    (hL : ∀ e ∈ L, ∀ a, Within a o n → ¬ Within a e.1 72) (hm : m ≤ 8736)
    (hv : HeapOk t) (mono : heapNext u ≤ heapNext t) (sp : t.getReg .x2 = u.getReg .x2) :
    M8 OI s t A k R Q B Bb W L := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have hh := hv.hi
  have hu := h.m.inv.heap.hi
  have hW := h.bb.2.2.2
  have hBW : B ≤ W := by have := h.bb; omega
  simp only [heapEnd, heapNext] at hh hu hW
  refine h.step hpre fr (fun a ha ↦ ?_) (fun a ha ↦ ?_) hv mono sp
  · rcases ha with ha | ha | ha | ha
    · exact Or.inl (by simp only [Within] at ha ⊢; addr_omega [ha, ho, hb1])
    · exact Or.inr (Or.inr (Or.inr (Or.inl (stackLo_w6 hpre h.m.inv hm ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · simp only [Fresh] at ha
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp only [heapNext] at ha; omega, ha.2⟩))))
  · simp only [M8W]
    rcases ha with ha | ha | ha | ha
    · refine ⟨?_, ?_, ?_, ?_, fun e he ↦ hL e he a ha⟩ <;> simp only [Within] at ha ⊢ <;> addr_omega [ha, ho, hb1, hW, hu]
    · rw [stackLo_callee h.m.inv] at ha
      refine ⟨?_, ?_, ?_, ?_, fun e he hw ↦ ?_⟩ <;> simp only [Within] at ha ⊢
      all_goals first
        | addr_omega [ha, hb1, hm, hW, hu]
        | (obtain ⟨o1, o2, -⟩ := (h.tabs e he).1; simp only [Within] at hw; addr_omega [ha, hb1, hm, o1, hw])
    · refine ⟨?_, ?_, ?_, ?_, fun e he hw ↦ ?_⟩ <;> simp only [Within] at ha ⊢
      all_goals first
        | addr_omega [ha, hb1, hW, hu]
        | (obtain ⟨o1, o2, -⟩ := (h.tabs e he).1; simp only [Within] at hw; addr_omega [ha, hb1, o1, hw])
    · simp only [Fresh, heapNext] at ha
      refine ⟨by omega, ?_, ?_, ?_, fun e he hw ↦ ?_⟩
      all_goals first
        | addr_omega [ha, hb1, hh]
        | (obtain ⟨o1, o2, -⟩ := (h.tabs e he).1; simp only [Within] at hw; addr_omega [ha, hb1, o1, hw, hh])

set_option maxRecDepth 8192 in
/-- `flushes_arith(opcode, multiply)` into `sp + 1728`. -/
theorem arithCall (hFA : Rv64Verifier.Layout.FlushesArithSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} (hpre : WalkPre s)
    (h : M8 OI s u A k R Q B Bb W L) (hL : ∀ e ∈ L, ∀ a, Within a (s.getReg .x2 - 928) 48 → ¬ Within a e.1 72)
    (hpc : u.pc = 0x8000547c) (x10 : u.getReg .x10 = s.getReg .x2 - 928) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧ heapNext u ≤ heapNext t ∧
      M8 OI s t A k R Q B Bb W L ∧ FB t (s.getReg .x2 - 928) (LayoutMirror.flushesArithRust (u.getReg .x11).toNat (u.getReg .x12 != 0))
        (heapNext u)) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hn : Rv64Verifier.Layout.flushesArithStack ≤ 8736 := by decide
  obtain ⟨v1, v2, v3⟩ := slotW hpre h.m.inv (n := 6) (o := s.getReg .x2 - 928) (by
    simp only [InSlot]; addr_omega [hb1, hb3]) hn
  have pre : Rv64Verifier.Layout.FlushesArithPre u := {
    heap := h.m.inv.heap
    stack := stk_sub hpre h.m.inv hn (by decide)
    out := by rw [x10]; exact v1
    outFree := by rw [x10]; exact v2
    outStack := by rw [x10]; exact v3
    rodata := h.m.inv.rodata hpre }
  obtain ⟨t, r, ⟨hpc', hp, ⟨g, gv⟩⟩ | hd⟩ := hFA u hpc pre
  swap
  · exact ⟨t, r, Or.inr hd⟩
  rw [x10] at g gv
  refine ⟨t, r, Or.inl ⟨hpc', hp, g.mono, h.call hpre (o := s.getReg .x2 - 928) (n := 48)
    (m := Rv64Verifier.Layout.flushesArithStack) g.frame (by addr_omega [hb1]) hL hn g.heap g.mono (hp.reg .x2),
    g.ok, gv, fun x hx ↦ (g.fresh x hx).1⟩⟩

set_option maxRecDepth 8192 in
/-- `vec![ZERO; n]` into the frame slot `o`, past the `Flushes` under construction at `o'`. -/
theorem padCall (hFE : MultilinearContracts.FromElemSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {L : List (Word × LayoutMirror.TableRust)} {o o' : Word} {F : LayoutMirror.FlushesRust} {lo : Nat}
    (hpre : WalkPre s) (h : M8 OI s u A k R Q B Bb W L) (fb : FB u o' F lo)
    (ho' : InSlot s o' 48) (ho : InSlot s o 24) (hoo : ∀ a, Within a o 24 → ¬ Within a o' 48)
    (hL : ∀ e ∈ L, ∀ a, Within a o 24 → ¬ Within a e.1 72) (hpc : u.pc = 0x80005360)
    (x10 : u.getReg .x10 = o) (x11 : u.getReg .x11 = 0xa0000068) (hn0 : 0 < (u.getReg .x12).toNat) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧ heapNext u ≤ heapNext t ∧
      M8 OI s t A k R Q B Bb W L ∧ FB t o' F lo ∧ ∃ P, ZVec t o (u.getReg .x12).toNat P (heapNext u)) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  have pre := fromElemPre hpre h.m.inv (by rw [x10]; exact ho) x11
  obtain ⟨t, r, ⟨hpc', hp, post⟩ | hd⟩ := hFE.call (Reaches.refl u) hpc pre
  swap
  · exact ⟨t, r, Or.inr hd⟩
  have fr := post.frame.dframe
  have nb := post.fresh
  have hlen := post.len
  have hel := post.elems
  rw [x10] at fr nb hlen hel
  rw [x11, zeroE (h.m.inv.rodata hpre)] at hel
  have hh := post.heap.hi
  simp only [heapEnd] at hh
  simp only [NewBuf] at nb
  set P := vecPtr t o with hP
  obtain ⟨o1, o2, o3⟩ := ho
  obtain ⟨p1, p2, p3⟩ := ho'
  have hfb := fb.frame fr (fun x hx hw ↦ by
      rcases hw with hw | hw | hw | hw
      · exact hoo x hw hx
      · rw [stackLo_callee h.m.inv] at hw; simp only [Within] at hx hw
        simp only [MultilinearContracts.fromElemStack, tryAllocStack] at hw; addr_omega [hx, hw, hb1, p1]
      · simp only [Within] at hx hw; addr_omega [hx, hw, hb1, p1]
      · simp only [Fresh, heapNext] at hw hh; simp only [Within] at hx; addr_omega [hx, hw, hb1, p1, hh])
    (fun x h1 h2 hw ↦ by
      rcases hw with hw | hw | hw | hw
      · simp only [Within] at hw; addr_omega [hw, h2, o1, hb1, h.m.inv.heap.hi]
      · rw [stackLo_callee h.m.inv] at hw; simp only [Within] at hw; have := h.m.inv.heap.hi
        simp only [heapEnd] at this; simp only [MultilinearContracts.fromElemStack, tryAllocStack] at hw
        addr_omega [hw, h2, hb1, this]
      · simp only [Within, nextAddr] at hw; have := h.m.inv.heap.hi
        simp only [heapEnd] at this; addr_omega [hw, h2, this]
      · simp only [Fresh] at hw; omega)
    (by addr_omega [hb1, p2]) h.m.inv.heap post.mono
  refine ⟨t, r, Or.inl ⟨hpc', hp, post.mono, h.call hpre (o := o) (n := 24) (m := MultilinearContracts.fromElemStack)
    fr (by addr_omega [o1, o2]) hL (by decide) post.heap post.mono (hp.reg .x2), hfb.1, P, {
      vec := by rw [← x10]; exact post.vec
      ptr := rfl
      len := by rw [hlen]; simp
      zero := fun i hi ↦ ?_
      buf := ⟨nb.1, by omega, by omega⟩ }⟩⟩
  have := congrArg (fun l ↦ l.getD i 0) hel
  simp only [vecEs, hlen, eListAt] at this
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_map, List.getElem_range] at this
  rw [this, List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact hi), List.getElem_replicate]

end Rv64Verifier.Proofs.Walk
