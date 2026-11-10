import Rv64Verifier.Proofs.Walk.Jp4

/-!
# `walk`: `tables()`, JUMP's memory flushes (R8)

From `jumpBc`'s return: three times `prod(1, o, 0)` into `sp + 2432`, the column at `sp + 2504`,
`memory_cols(fp·o, cnt, &[column])` on the `Flushes` at `sp + 1728` (`jumpCols`, to `0x80002d30`).
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
  Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript Rv64Verifier.Blocks.F4
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)
open Rv64Verifier.Layout (FlushesOk flushesOf flushesDeep FormOk formOf formBuf)

theorem colsAt_one (u : MachineState) (p : Word) :
    Rv64Verifier.Layout.colsAt u p 1 = [(u.getMem p).toNat] := by
  show [(u.getMem (p + BitVec.ofNat 64 (8 * 0))).toNat] = _
  simp

/-- `FB` across a callee writing a frame slot, its stack, `NEXT` and fresh heap. -/
theorem FB.cw {s u t : MachineState} {o o' : Word} {n lo : Nat} {F : LayoutMirror.FlushesRust}
    (hpre : WalkPre s) (I : Inv s u) (h : FB u o F lo) (ho : InSlot s o 48)
    (fr : Rv64Verifier.Layout.DFrame u t (CW u t o' n)) (hn : n ≤ 8736) (ho' : InSlot s o' 24)
    (hoo : ∀ x, Within x o 48 → ¬ Within x o' 24) (hv : HeapOk t) (mono : heapNext u ≤ heapNext t) :
    FB t o F lo := by
  obtain ⟨hb1, -, -, -⟩ := bounds hpre
  obtain ⟨e1, e2, e3⟩ := ho
  obtain ⟨f1, -, -⟩ := ho'
  have hu := I.heap.hi
  simp only [heapEnd, heapNext] at hu
  refine (h.frame' fr (fun x hx hw ↦ slot_not_cwx (lo' := 0) (hi' := 0) hpre I ⟨e1, e2, e3⟩ hn hoo hv
    (Nat.zero_le _) x hx (Or.inl hw)) (fun x hx hw ↦ ?_) (by addr_omega [hb1, e2]) I.heap mono).1
  have hd := h.ok.deep_below hx
  simp only [heapStart, heapNext] at hd
  rcases hw with hw | hw | hw | hw
  · simp only [Within] at hw; addr_omega [hw, hb1, hd, hu, f1]
  · rw [stackLo_callee I] at hw; simp only [Within] at hw; addr_omega [hw, hb1, hn, hd, hu]
  · simp only [Within, nextAddr] at hw; addr_omega [hw, hd, hu]
  · simp only [Fresh, heapNext] at hw; omega

set_option maxRecDepth 8192 in
/-- `memory_cols(address, cnt, &[c])` on the `Flushes` at `sp + 1728`, the address at `sp + 2432`,
the column at `sp + 2504`. -/
theorem memColsJ (hK : Rv64Verifier.Layout.MemoryColsSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {F : LayoutMirror.FlushesRust} {a : LayoutMirror.FormRust} {lo hi : Nat} {c : Word}
    (hpre : WalkPre s) (M : M8 OI s u A k R Q B Bb W (L5 s)) (fb : FB u (s.getReg .x2 - 928) F W)
    (sa : SF u (s.getReg .x2 - 224) a lo hi) (x10 : u.getReg .x10 = s.getReg .x2 - 928)
    (x11 : u.getReg .x11 = s.getReg .x2 - 224) (x13 : u.getReg .x13 = s.getReg .x2 - 152)
    (x14 : u.getReg .x14 = 1) (hc : u.getMem (s.getReg .x2 - 152) = c) (hpc : u.pc = 0x80005c64) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = returnAddress u ∧ Preserves u t ∧
      M8 OI s t A k R Q B Bb W (L5 s) ∧
      FB t (s.getReg .x2 - 928) (F.memoryCols a (u.getReg .x12).toNat [c.toNat]) W ∧
      heapNext u ≤ heapNext t) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hnK : Rv64Verifier.Layout.memoryColsStack ≤ 8736 := by decide
  have hFo : InSlot s (s.getReg .x2 - 928) (8 * 6) := inSlot_off hpre (by decide)
  obtain ⟨v1, v2, v3⟩ := slotW hpre M.m.inv hFo hnK
  obtain ⟨w1, w2, w3⟩ := slotPre hpre M.m.inv (o := s.getReg .x2 - 224) (inSlot_off hpre (by decide)) hnK
  obtain ⟨z1, z2, z3⟩ := slotW hpre M.m.inv (n := 1) (o := s.getReg .x2 - 152) (inSlot_off hpre (by decide)) hnK
  have e1 : (1 : Word).toNat = 1 := rfl
  have pre : Rv64Verifier.Layout.MemoryColsPre u := {
    heap := M.m.inv.heap
    stack := stk_sub hpre M.m.inv hnK (by decide)
    self := by rw [x10]; exact v1
    ok := by rw [x10]; exact fb.ok
    selfFree := by rw [x10]; exact v2
    selfStack := by rw [x10]; exact v3
    rodata := M.m.inv.rodata hpre
    address := by rw [x11]; exact w1
    addressOk := by rw [x11]; exact sa.ok
    addressFree := by rw [x11]; exact w2
    addressStack := by rw [x11]; exact w3
    len := by rw [x14]; decide
    columns := by rw [x13, x14, e1]; exact z1
    columnsFree := by rw [x13, x14, e1]; exact z2
    columnsStack := by rw [x13, x14, e1]; exact z3 }
  obtain ⟨t, hr, ⟨hpct, hp, ⟨g, gv⟩⟩ | d⟩ := hK u hpc pre
  swap
  · exact ⟨t, hr, Or.inr d⟩
  rw [x10] at g gv
  rw [x11, x13, x14, fb.val, sa.val, e1, colsAt_one, hc] at gv
  obtain ⟨M', F'⟩ := M.grow hpre fb (le_refl _) M.bb.2.2.2 hFo (l5_off hpre (by decide)) g hnK (hp.reg .x2)
  rw [gv] at F'
  exact ⟨t, hr, Or.inl ⟨hpct, hp, M', F', g.mono⟩⟩

set_option maxRecDepth 8192 in
/-- The three memory flushes, to the `Flushes`' move at `0x80002d30`. -/
theorem jumpCols (hP : Rv64Verifier.Layout.ProdSpec) (hK : Rv64Verifier.Layout.MemoryColsSpec)
    {OI : MachineState → Word → List (List Opening) → Prop} {s u : MachineState}
    {A : List E} {k : Nat} {R Q : Word} {B : Nat} {Bb : Word} {W : Nat}
    {F : LayoutMirror.FlushesRust} (hpre : WalkPre s) (M : M8 OI s u A k R Q B Bb W (L5 s))
    (fb : FB u (s.getReg .x2 - 928) F W) (r : JR s u) (x20 : u.getReg .x20 = s.getReg .x2 - 512)
    (x8 : u.getReg .x8 = 5) (x24 : u.getReg .x24 = 0xa0000068) (hpc : u.pc = 0x80002c5c) :
    ∃ t, Reaches Image.code u t ∧ ((t.pc = 0x80002d30 ∧ M8 OI s t A k R Q B Bb W (L5 s) ∧
      FB t (s.getReg .x2 - 928)
        (((F.memoryCols (LayoutMirror.prodRust 1 2 0) 8 [5]).memoryCols (LayoutMirror.prodRust 1 3 0) 9
          [6]).memoryCols (LayoutMirror.prodRust 1 4 0) 10 [7]) W ∧
      JR s t ∧ t.getReg .x20 = s.getReg .x2 - 512 ∧ t.getReg .x8 = 5 ∧ t.getReg .x9 = 8 ∧
      t.getReg .x24 = 0xa0000068) ∨ Dead Image.code t) := by
  obtain ⟨hb1, -, hb3, -⟩ := bounds hpre
  have hval : ValidMemRange (s.getReg .x2 - 11392) 1424 := hpre.stack.valid
  have hFo : InSlot s (s.getReg .x2 - 928) 48 := inSlot_off hpre (by decide)
  have hn : Rv64Verifier.Layout.colStack ≤ 8736 := by decide
  -- `prod(1, 2, 0)`, the column 5, `memory_cols(.., 8, ..)`
  have sp0 : u.getReg .x2 = s.getReg .x2 - 2656 := M.m.inv.sp
  obtain ⟨a0, pa0, ga0⟩ := Sym.BlockSpec.reaches b80002c5c_spec hpc trivial
  have ma0 := b80002c5c_mem_same ga0
  have Ma0 := M.same hpre ma0 (b80002c5c_keeps ga0 .x2 (by decide))
  have Fa0 := fb.same hpre hFo M.m.inv.heap ma0
  obtain ⟨b0, pb0, ⟨pcb0, hpb0, Mb0, Sb0, frb0, hvb0, mob0⟩ | d⟩ := prodF hP (o := s.getReg .x2 - 224) hpre Ma0
    (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) (b80002c5c_pc ga0)
    (by rw [b80002c5c_x10 ga0]; exact spAdd hpre sp0 (by decide))
  swap
  · exact ⟨b0, (pa0.trans pb0), Or.inr d⟩
  rw [b80002c5c_x11 ga0, b80002c5c_x12 ga0, b80002c5c_x13 ga0] at Sb0
  have Fb0 := Fa0.cw hpre Ma0.m.inv hFo frb0 hn (inSlot_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide)) hvb0 mob0
  have spb0 : b0.getReg .x2 = s.getReg .x2 - 2656 := Mb0.m.inv.sp
  have y20b0 : b0.getReg .x20 = s.getReg .x2 - 512 := by
    rw [hpb0.reg .x20, b80002c5c_keeps ga0 .x20 (by decide)]; exact x20
  have x8b0 : b0.getReg .x8 = 5 := by
    rw [hpb0.reg .x8, b80002c5c_keeps ga0 .x8 (by decide)]; exact x8
  obtain ⟨c0, pc0', gc0⟩ := Sym.BlockSpec.reaches b80002c78_spec
    (by rw [pcb0, returnAddress_eq, b80002c5c_x1 ga0]; decide) (by
      rv_eval [spb0, y20b0]
      valid_access hval [hb1])
  have frc0 : Rv64Verifier.Layout.DFrame b0 c0 fun y ↦ Within y (s.getReg .x2 - 152) 8 := by
    have := MemFrame.dframe (b80002c78_frame gc0 (by rw [y20b0]; addr_omega [hb1]))
    rwa [y20b0, show s.getReg .x2 - 512 + 360 = s.getReg .x2 - 152 by rv_eval []] at this
  obtain ⟨Mc0, hnc0⟩ := Mb0.slotStep hpre (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) frc0
    (b80002c78_keeps gc0 .x2 (by decide))
  have hub0 := hvb0.hi
  simp only [heapEnd] at hub0
  have Fc0 := (Fb0.frame frc0 (apart_off hpre (by decide) (by decide) (by decide))
    (fun y _ hy hw ↦ by simp only [Within] at hw; simp only [heapNext] at hy hub0; addr_omega [hw, hy, hb1, hub0])
    (by addr_omega [hb1]) hvb0 hnc0.ge).1
  have Sc0 := Sb0.blk hpre (inSlot_off hpre (by decide)) (inSlot_off hpre (by decide)) (le_refl _) hvb0 frc0
    (apart_off hpre (by decide) (by decide) (by decide)) hnc0.ge
  have spc0 : b0.getReg .x2 = s.getReg .x2 - 2656 := spb0
  obtain ⟨d0, pd0, ⟨pcd0, hpd0, Md0, Fd0, mod0⟩ | d⟩ := memColsJ hK hpre Mc0 Fc0 Sc0
    (by rw [b80002c78_x10 gc0]; exact spAdd hpre spb0 (by decide))
    (by rw [b80002c78_x11 gc0]; exact spAdd hpre spb0 (by decide))
    (by rw [b80002c78_x13 gc0]; exact spAdd hpre spb0 (by decide)) (b80002c78_x14 gc0)
    (c := 5) (by have h' := b80002c78_m_x20_360 gc0; rv_eval [y20b0] at h' ⊢; rw [h']; exact x8b0) (b80002c78_pc gc0)
  swap
  · exact ⟨d0, (pa0.trans (pb0.trans (pc0'.trans pd0))), Or.inr d⟩
  rw [b80002c78_x12 gc0] at Fd0
  have Q0 := (pa0.trans (pb0.trans (pc0'.trans pd0)))
  have r0 := (((r.keeps (b80002c5c_keeps ga0)).pres hpb0).keeps (b80002c78_keeps gc0)).pres hpd0
  have y200 : d0.getReg .x20 = s.getReg .x2 - 512 := by
    rw [hpd0.reg .x20, b80002c78_keeps gc0 .x20 (by decide)]; exact y20b0
  have y80 : d0.getReg .x8 = 5 := by
    rw [hpd0.reg .x8, b80002c78_keeps gc0 .x8 (by decide), hpb0.reg .x8, b80002c5c_keeps ga0 .x8 (by decide)]
    exact x8
  have y240 : d0.getReg .x24 = 0xa0000068 := by
    rw [hpd0.reg .x24, b80002c78_keeps gc0 .x24 (by decide), hpb0.reg .x24, b80002c5c_keeps ga0 .x24 (by decide)]
    exact x24
  have y90 : d0.getReg .x9 = 8 := by rw [hpd0.reg .x9]; exact b80002c78_x9 gc0
  -- `prod(1, 3, 0)`, the column 6, `memory_cols(.., 9, ..)`
  have sp1 : d0.getReg .x2 = s.getReg .x2 - 2656 := Md0.m.inv.sp
  obtain ⟨a1, pa1, ga1⟩ := Sym.BlockSpec.reaches b80002ca4_spec (by rw [pcd0, returnAddress_eq, b80002c78_x1 gc0]; decide) trivial
  have ma1 := b80002ca4_mem_same ga1
  have Ma1 := Md0.same hpre ma1 (b80002ca4_keeps ga1 .x2 (by decide))
  have Fa1 := Fd0.same hpre hFo Md0.m.inv.heap ma1
  obtain ⟨b1, pb1, ⟨pcb1, hpb1, Mb1, Sb1, frb1, hvb1, mob1⟩ | d⟩ := prodF hP (o := s.getReg .x2 - 224) hpre Ma1
    (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) (b80002ca4_pc ga1)
    (by rw [b80002ca4_x10 ga1]; exact spAdd hpre sp1 (by decide))
  swap
  · exact ⟨b1, Q0.trans (pa1.trans pb1), Or.inr d⟩
  rw [b80002ca4_x11 ga1, b80002ca4_x12 ga1, b80002ca4_x13 ga1] at Sb1
  have Fb1 := Fa1.cw hpre Ma1.m.inv hFo frb1 hn (inSlot_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide)) hvb1 mob1
  have spb1 : b1.getReg .x2 = s.getReg .x2 - 2656 := Mb1.m.inv.sp
  have y20b1 : b1.getReg .x20 = s.getReg .x2 - 512 := by
    rw [hpb1.reg .x20, b80002ca4_keeps ga1 .x20 (by decide)]; exact y200
  have x21b1 : b1.getReg .x21 = 6 := by
    rw [hpb1.reg .x21, b80002ca4_keeps ga1 .x21 (by decide)]; exact r0.x21
  obtain ⟨c1, pc1', gc1⟩ := Sym.BlockSpec.reaches b80002cc0_spec
    (by rw [pcb1, returnAddress_eq, b80002ca4_x1 ga1]; decide) (by
      rv_eval [spb1, y20b1]
      valid_access hval [hb1])
  have frc1 : Rv64Verifier.Layout.DFrame b1 c1 fun y ↦ Within y (s.getReg .x2 - 152) 8 := by
    have := MemFrame.dframe (b80002cc0_frame gc1 (by rw [y20b1]; addr_omega [hb1]))
    rwa [y20b1, show s.getReg .x2 - 512 + 360 = s.getReg .x2 - 152 by rv_eval []] at this
  obtain ⟨Mc1, hnc1⟩ := Mb1.slotStep hpre (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) frc1
    (b80002cc0_keeps gc1 .x2 (by decide))
  have hub1 := hvb1.hi
  simp only [heapEnd] at hub1
  have Fc1 := (Fb1.frame frc1 (apart_off hpre (by decide) (by decide) (by decide))
    (fun y _ hy hw ↦ by simp only [Within] at hw; simp only [heapNext] at hy hub1; addr_omega [hw, hy, hb1, hub1])
    (by addr_omega [hb1]) hvb1 hnc1.ge).1
  have Sc1 := Sb1.blk hpre (inSlot_off hpre (by decide)) (inSlot_off hpre (by decide)) (le_refl _) hvb1 frc1
    (apart_off hpre (by decide) (by decide) (by decide)) hnc1.ge
  have spc1 : b1.getReg .x2 = s.getReg .x2 - 2656 := spb1
  obtain ⟨d1, pd1, ⟨pcd1, hpd1, Md1, Fd1, mod1⟩ | d⟩ := memColsJ hK hpre Mc1 Fc1 Sc1
    (by rw [b80002cc0_x10 gc1]; exact spAdd hpre spb1 (by decide))
    (by rw [b80002cc0_x11 gc1]; exact spAdd hpre spb1 (by decide))
    (by rw [b80002cc0_x13 gc1]; exact spAdd hpre spb1 (by decide)) (b80002cc0_x14 gc1)
    (c := 6) (by have h' := b80002cc0_m_x20_360 gc1; rv_eval [y20b1] at h' ⊢; rw [h']; exact x21b1) (b80002cc0_pc gc1)
  swap
  · exact ⟨d1, Q0.trans (pa1.trans (pb1.trans (pc1'.trans pd1))), Or.inr d⟩
  rw [b80002cc0_x12 gc1] at Fd1
  have Q1 := Q0.trans (pa1.trans (pb1.trans (pc1'.trans pd1)))
  have r1 := (((r0.keeps (b80002ca4_keeps ga1)).pres hpb1).keeps (b80002cc0_keeps gc1)).pres hpd1
  have y201 : d1.getReg .x20 = s.getReg .x2 - 512 := by
    rw [hpd1.reg .x20, b80002cc0_keeps gc1 .x20 (by decide)]; exact y20b1
  have y81 : d1.getReg .x8 = 5 := by
    rw [hpd1.reg .x8, b80002cc0_keeps gc1 .x8 (by decide), hpb1.reg .x8, b80002ca4_keeps ga1 .x8 (by decide)]
    exact y80
  have y241 : d1.getReg .x24 = 0xa0000068 := by
    rw [hpd1.reg .x24, b80002cc0_keeps gc1 .x24 (by decide), hpb1.reg .x24, b80002ca4_keeps ga1 .x24 (by decide)]
    exact y240
  have y91 : d1.getReg .x9 = 8 := by
    rw [hpd1.reg .x9, b80002cc0_keeps gc1 .x9 (by decide), hpb1.reg .x9, b80002ca4_keeps ga1 .x9 (by decide)]
    exact y90
  -- `prod(1, 4, 0)`, the column 7, `memory_cols(.., 10, ..)`
  have sp2 : d1.getReg .x2 = s.getReg .x2 - 2656 := Md1.m.inv.sp
  obtain ⟨a2, pa2, ga2⟩ := Sym.BlockSpec.reaches b80002ce8_spec (by rw [pcd1, returnAddress_eq, b80002cc0_x1 gc1]; decide) trivial
  have ma2 := b80002ce8_mem_same ga2
  have Ma2 := Md1.same hpre ma2 (b80002ce8_keeps ga2 .x2 (by decide))
  have Fa2 := Fd1.same hpre hFo Md1.m.inv.heap ma2
  obtain ⟨b2, pb2, ⟨pcb2, hpb2, Mb2, Sb2, frb2, hvb2, mob2⟩ | d⟩ := prodF hP (o := s.getReg .x2 - 224) hpre Ma2
    (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) (b80002ce8_pc ga2)
    (by rw [b80002ce8_x10 ga2]; exact spAdd hpre sp2 (by decide))
  swap
  · exact ⟨b2, Q1.trans (pa2.trans pb2), Or.inr d⟩
  rw [b80002ce8_x11 ga2, b80002ce8_x12 ga2, b80002ce8_x13 ga2] at Sb2
  have Fb2 := Fa2.cw hpre Ma2.m.inv hFo frb2 hn (inSlot_off hpre (by decide)) (apart_off hpre (by decide) (by decide) (by decide)) hvb2 mob2
  have spb2 : b2.getReg .x2 = s.getReg .x2 - 2656 := Mb2.m.inv.sp
  have y20b2 : b2.getReg .x20 = s.getReg .x2 - 512 := by
    rw [hpb2.reg .x20, b80002ce8_keeps ga2 .x20 (by decide)]; exact y201
  obtain ⟨c2, pc2', gc2⟩ := Sym.BlockSpec.reaches b80002d04_spec
    (by rw [pcb2, returnAddress_eq, b80002ce8_x1 ga2]; decide) (by
      rv_eval [spb2, y20b2]
      valid_access hval [hb1])
  have frc2 : Rv64Verifier.Layout.DFrame b2 c2 fun y ↦ Within y (s.getReg .x2 - 152) 8 := by
    have := MemFrame.dframe (b80002d04_frame gc2 (by rw [y20b2]; addr_omega [hb1]))
    rwa [y20b2, show s.getReg .x2 - 512 + 360 = s.getReg .x2 - 152 by rv_eval []] at this
  obtain ⟨Mc2, hnc2⟩ := Mb2.slotStep hpre (inSlot_off hpre (by decide)) (l5_off hpre (by decide)) frc2
    (b80002d04_keeps gc2 .x2 (by decide))
  have hub2 := hvb2.hi
  simp only [heapEnd] at hub2
  have Fc2 := (Fb2.frame frc2 (apart_off hpre (by decide) (by decide) (by decide))
    (fun y _ hy hw ↦ by simp only [Within] at hw; simp only [heapNext] at hy hub2; addr_omega [hw, hy, hb1, hub2])
    (by addr_omega [hb1]) hvb2 hnc2.ge).1
  have Sc2 := Sb2.blk hpre (inSlot_off hpre (by decide)) (inSlot_off hpre (by decide)) (le_refl _) hvb2 frc2
    (apart_off hpre (by decide) (by decide) (by decide)) hnc2.ge
  have spc2 : b2.getReg .x2 = s.getReg .x2 - 2656 := spb2
  obtain ⟨d2, pd2, ⟨pcd2, hpd2, Md2, Fd2, mod2⟩ | d⟩ := memColsJ hK hpre Mc2 Fc2 Sc2
    (by rw [b80002d04_x10 gc2]; exact spAdd hpre spb2 (by decide))
    (by rw [b80002d04_x11 gc2]; exact spAdd hpre spb2 (by decide))
    (by rw [b80002d04_x13 gc2]; exact spAdd hpre spb2 (by decide)) (b80002d04_x14 gc2)
    (c := 7) (by have h' := b80002d04_m_x20_360 gc2; rv_eval [y20b2] at h' ⊢; rw [h']) (b80002d04_pc gc2)
  swap
  · exact ⟨d2, Q1.trans (pa2.trans (pb2.trans (pc2'.trans pd2))), Or.inr d⟩
  rw [b80002d04_x12 gc2] at Fd2
  have Q2 := Q1.trans (pa2.trans (pb2.trans (pc2'.trans pd2)))
  have r2 := (((r1.keeps (b80002ce8_keeps ga2)).pres hpb2).keeps (b80002d04_keeps gc2)).pres hpd2
  have y202 : d2.getReg .x20 = s.getReg .x2 - 512 := by
    rw [hpd2.reg .x20, b80002d04_keeps gc2 .x20 (by decide)]; exact y20b2
  have y82 : d2.getReg .x8 = 5 := by
    rw [hpd2.reg .x8, b80002d04_keeps gc2 .x8 (by decide), hpb2.reg .x8, b80002ce8_keeps ga2 .x8 (by decide)]
    exact y81
  have y242 : d2.getReg .x24 = 0xa0000068 := by
    rw [hpd2.reg .x24, b80002d04_keeps gc2 .x24 (by decide), hpb2.reg .x24, b80002ce8_keeps ga2 .x24 (by decide)]
    exact y241
  have y92 : d2.getReg .x9 = 8 := by
    rw [hpd2.reg .x9, b80002d04_keeps gc2 .x9 (by decide), hpb2.reg .x9, b80002ce8_keeps ga2 .x9 (by decide)]
    exact y91
  exact ⟨d2, Q2, Or.inl ⟨by rw [pcd2, returnAddress_eq, b80002d04_x1 gc2]; decide, Md2, Fd2, r2, y202, y82,
    y92, y242⟩⟩

end Rv64Verifier.Proofs.Walk
