import Rv64Verifier.Proofs.Pcs.VsoLvGlueFront

/-!
# `verify_stacked_opening`'s glue: the glued claim staged, room made

From `0x8000b7b8` (`GMid`): the `GluedClaim` staged at `S - 384` (the weight, then the scalar at
`S - 328`), `grow_one` of `glued` if it is full (`0x8000b818`, `0x8000db78`), to `0x8000b67c`
(`GAt67`, `gstage`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- At `0x8000b67c`, claim `i` staged at `S - 384`, room for it in `glued`, from `u`. -/
structure GAt67 (s g : MachineState) (lam : E) (Wl : Model.Pcs.WhirLocals)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) (i : ℕ) (u w : MachineState) : Prop where
  pc : w.pc = 0x8000b67c
  sp : w.getReg .x2 = s.getReg .x2 - 1040
  regs : ∀ r ∈ ZK, w.getReg r = u.getReg r
  x8 : w.getReg .x8 = vecLen u (s.getReg .x2 - 664)
  inv : InvR s w (w.getMem nextAddr)
  heap : HeapOk w
  mono : heapNext u ≤ heapNext w
  fr : DFrame u w (GlueW s g w)
  gv : VecOk w (s.getReg .x2 - 664) 88 8
  glen : vecLen w (s.getReg .x2 - 664) = vecLen u (s.getReg .x2 - 664)
  room : (vecLen u (s.getReg .x2 - 664)).toNat < (vecCap w (s.getReg .x2 - 664)).toNat
  old : ∀ j < (vecLen u (s.getReg .x2 - 664)).toNat,
    WordsEq w (vecPtr w (s.getReg .x2 - 664) + BitVec.ofNat 64 (88 * j)) u
      (vecPtr u (s.getReg .x2 - 664) + BitVec.ofNat 64 (88 * j)) 11
  gbuf : (vecPtr w (s.getReg .x2 - 664) = vecPtr g (s.getReg .x2 - 664) ∧
      vecCap w (s.getReg .x2 - 664) = vecCap g (s.getReg .x2 - 664)) ∨
    NewBuf g w (vecPtr w (s.getReg .x2 - 664)) ((vecCap w (s.getReg .x2 - 664)).toNat * 88) 8
  stage : WordsEq w (s.getReg .x2 - 384) g (pAddr g s i + 24) 7
  scal : eAt w (s.getReg .x2 - 384 + 56) = (gacc lam Wl pend (i + 1)).2
  sc : eAt w (s.getReg .x2 - 408) = (gacc lam Wl pend (i + 1)).2
  quad : eListAt w (g.getMem (s.getReg .x2 - 896)) (g.getReg .x23).toNat =
    (gacc lam Wl pend (i + 1)).1.runningQuad

/-- `u`'s glued claims' buffer misses the quadratic's, all of it below `heapNext u`. -/
theorem GInv.gapart {s g : MachineState} {lam : E} {Wl : Model.Pcs.WhirLocals}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {i : ℕ} {u : MachineState}
    (hg : GlueIn s g lam Wl pend) (hu : GInv s g lam Wl pend i u) :
    Apart (g.getMem (s.getReg .x2 - 896)) (24 * (g.getReg .x23).toNat)
      (vecPtr u (s.getReg .x2 - 664)) ((vecCap u (s.getReg .x2 - 664)).toNat * 88) ∧
    (vecPtr u (s.getReg .x2 - 664)).toNat % 8 = 0 ∧
    ((vecCap u (s.getReg .x2 - 664)).toNat * 88 = 0 ∨
      (vecPtr u (s.getReg .x2 - 664)).toNat + (vecCap u (s.getReg .x2 - 664)).toNat * 88 ≤
        heapNext u) := by
  have hraw := hu.gv.raw
  simp only [RawVecOk, Buf] at hraw
  refine ⟨?_, hraw.1, ?_⟩
  · rcases hu.gbuf with ⟨e1, e2⟩ | h0
    · rw [e1, e2]; exact hg.apart
    · rcases hg.quad.2.2 with h1 | h1
      · simp only [Apart]; omega
      · simp only [NewBuf] at h0
        rcases h0.2 with h2 | h2
        · simp only [Apart]; omega
        · simp only [Apart]; omega
  · rcases hraw.2 with h0 | h0
    · exact Or.inl h0
    · exact Or.inr h0.2

/-- After `0x8000b7b8`, the claim staged, `glued` as at `u`. -/
structure GAt7 (s g : MachineState) (lam : E) (Wl : Model.Pcs.WhirLocals)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) (i : ℕ) (u w : MachineState) : Prop where
  sp : w.getReg .x2 = s.getReg .x2 - 1040
  regs : ∀ r ∈ ZK, w.getReg r = u.getReg r
  x8 : w.getReg .x8 = vecLen u (s.getReg .x2 - 664)
  inv : InvR s w (w.getMem nextAddr)
  nx : w.getMem nextAddr = u.getMem nextAddr
  fr : DFrame u w (GlueW s g w)
  ecap : vecCap w (s.getReg .x2 - 664) = vecCap u (s.getReg .x2 - 664)
  eptr : vecPtr w (s.getReg .x2 - 664) = vecPtr u (s.getReg .x2 - 664)
  elen : vecLen w (s.getReg .x2 - 664) = vecLen u (s.getReg .x2 - 664)
  old : ∀ j < (vecLen u (s.getReg .x2 - 664)).toNat,
    WordsEq w (vecPtr w (s.getReg .x2 - 664) + BitVec.ofNat 64 (88 * j)) u
      (vecPtr u (s.getReg .x2 - 664) + BitVec.ofNat 64 (88 * j)) 11
  stage : WordsEq w (s.getReg .x2 - 384) g (pAddr g s i + 24) 7
  scal : eAt w (s.getReg .x2 - 384 + 56) = (gacc lam Wl pend (i + 1)).2
  sc : eAt w (s.getReg .x2 - 408) = (gacc lam Wl pend (i + 1)).2
  quad : eListAt w (g.getMem (s.getReg .x2 - 896)) (g.getReg .x23).toNat =
    (gacc lam Wl pend (i + 1)).1.runningQuad
  pcA : vecLen u (s.getReg .x2 - 664) ≠ vecCap u (s.getReg .x2 - 664) → w.pc = 0x8000b67c
  pcB : vecLen u (s.getReg .x2 - 664) = vecCap u (s.getReg .x2 - 664) → w.pc = 0x8000b818

theorem gstage7 {s g : MachineState} {lam : E}
    {Wl : Model.Pcs.WhirLocals} {pend : List (List E × Model.Pcs.GluedWeightRust)} {i : ℕ}
    {u t : MachineState} (hpre : VsoPre s) (hg : GlueIn s g lam Wl pend)
    (hu : GInv s g lam Wl pend i u) (ht : GMid s g lam Wl pend i u t) :
    ∃ w, Reaches Image.code t w ∧ GAt7 s g lam Wl pend i u w := by
  have hb := bounds hpre
  have hst := hpre.stack
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hgh := hg.heap.hi
  have huh := hu.heap.hi
  simp only [heapEnd] at hgh huh
  have hmo := hu.mono
  obtain ⟨hap, hp8, hpb⟩ := hu.gapart hg
  have hQb := hg.quad.2.2
  -- `0x8000b7b8`
  obtain ⟨t7, r7, h7⟩ := Sym.BlockSpec.reaches b8000b7b8_spec ht.pc (by
    rv_eval [ht.sp]; and_intros <;> valid_access hst.valid [hb])
  have k7 := b8000b7b8_keeps h7
  have f7 : DFrame t t7 (Within · (s.getReg .x2 - 384) 80) := by
    have := DFrame.of_memFrame (b8000b7b8_frame h7 (by rw [ht.sp]; addr_omega [hb]))
    rwa [ht.sp, show s.getReg .x2 - 1040 + 656 = s.getReg .x2 - 384 by rv_eval []] at this
  have sp7 : t7.getReg .x2 = s.getReg .x2 - 1040 := by rw [k7 .x2 (by decide), ht.sp]
  have hnt : heapNext t = heapNext u := by simp only [heapNext, ht.nx]
  obtain ⟨nx7, inv7⟩ := invR_step hpre ht.inv ht.heap f7 (fun a ha ↦ Or.inl (by
    addr_omega [ha, hb])) (by rw [sp7, ht.sp])
  have hn7 : heapNext t7 = heapNext u := by simp only [heapNext, nx7, ht.nx]
  -- `u` to `t7`: the stack below `S - 304`, the quadratic
  have Z7 : DFrame u t7 fun a ↦ Within a (g.getMem (s.getReg .x2 - 896)) (24 * (g.getReg .x23).toNat) ∨
      Within a (s.getReg .x2 - 464) 160 ∨ Within a (s.getReg .x2 - 160) 24 ∨
      Within a (s.getReg .x2 - 2464) 1424 :=
    ht.fr.trans f7 fun a ha ↦ Or.inr (Or.inl (by addr_omega [ha, hb]))
  have hdr (c : ℕ) (hc : c = 664 ∨ c = 656 ∨ c = 648) :
      t7.getMem (s.getReg .x2 - BitVec.ofNat 64 c) = u.getMem (s.getReg .x2 - BitVec.ofNat 64 c) :=
    Z7 _ fun j hj hw ↦ by
      rcases hQb with h0 | h0
      · rcases hw with hw | hw | hw | hw <;> rcases hc with rfl | rfl | rfl <;>
          first | (simp only [Within] at hw; omega) | addr_omega [hw, hj, hb]
      · rcases hw with hw | hw | hw | hw <;> rcases hc with rfl | rfl | rfl <;>
          addr_omega [hw, hj, hb, h0, hgh]
  have ecap : vecCap t7 (s.getReg .x2 - 664) = vecCap u (s.getReg .x2 - 664) := hdr 664 (by decide)
  have eptr : vecPtr t7 (s.getReg .x2 - 664) = vecPtr u (s.getReg .x2 - 664) := by
    simp only [vecPtr]; rw [show s.getReg .x2 - 664 + 8 = s.getReg .x2 - BitVec.ofNat 64 656 by
      rv_eval []]; exact hdr 656 (by decide)
  have elen : vecLen t7 (s.getReg .x2 - 664) = vecLen u (s.getReg .x2 - 664) := by
    simp only [vecLen]; rw [show s.getReg .x2 - 664 + 16 = s.getReg .x2 - BitVec.ofNat 64 648 by
      rv_eval []]; exact hdr 648 (by decide)
  -- the glued claims' words, as `u` has them
  have hlc := hu.gv.len
  have old7 : ∀ j < (vecLen u (s.getReg .x2 - 664)).toNat,
      WordsEq t7 (vecPtr t7 (s.getReg .x2 - 664) + BitVec.ofNat 64 (88 * j)) u
        (vecPtr u (s.getReg .x2 - 664) + BitVec.ofNat 64 (88 * j)) 11 := fun j hj k hk ↦ by
    rw [eptr]
    refine Z7 _ fun x hx hw ↦ ?_
    rcases hpb with h0 | h0
    · omega
    rcases hw with hw | hw | hw | hw
    · simp only [Apart] at hap
      rcases hap with h1 | h1 | h1 | h1
      · simp only [Within] at hw; omega
      · omega
      · addr_omega [hw, hx, h1, h0, hj, hk, hlc, huh]
      · addr_omega [hw, hx, h1, h0, hj, hk, hlc, huh]
    · addr_omega [hw, hx, hb, h0, hj, hk, hlc, huh]
    · addr_omega [hw, hx, hb, h0, hj, hk, hlc, huh]
    · addr_omega [hw, hx, hb, h0, hj, hk, hlc, huh]
  -- the staged claim
  have stage7 : WordsEq t7 (s.getReg .x2 - 384) g (pAddr g s i + 24) 7 := by
    intro k hk
    interval_cases k
    · have e := b8000b7b8_m_x2_656 h7
      rw [ht.sp] at e
      rw [show s.getReg .x2 - 384 + BitVec.ofNat 64 (8 * 0) = s.getReg .x2 - 1040 + 656 by
        addr_omega [hb], e,
        show s.getReg .x2 - 1040 + 576 = s.getReg .x2 - 464 + BitVec.ofNat 64 (8 * 0) by
        addr_omega [hb]]
      exact ht.wt 0 (by decide)
    · have e := b8000b7b8_m_x2_664 h7
      rw [ht.sp] at e
      rw [show s.getReg .x2 - 384 + BitVec.ofNat 64 (8 * 1) = s.getReg .x2 - 1040 + 664 by
        addr_omega [hb], e,
        show s.getReg .x2 - 1040 + 584 = s.getReg .x2 - 464 + BitVec.ofNat 64 (8 * 1) by
        addr_omega [hb]]
      exact ht.wt 1 (by decide)
    · have e := b8000b7b8_m_x2_672 h7
      rw [ht.sp] at e
      rw [show s.getReg .x2 - 384 + BitVec.ofNat 64 (8 * 2) = s.getReg .x2 - 1040 + 672 by
        addr_omega [hb], e,
        show s.getReg .x2 - 1040 + 592 = s.getReg .x2 - 464 + BitVec.ofNat 64 (8 * 2) by
        addr_omega [hb]]
      exact ht.wt 2 (by decide)
    · have e := b8000b7b8_m_x2_680 h7
      rw [ht.sp] at e
      rw [show s.getReg .x2 - 384 + BitVec.ofNat 64 (8 * 3) = s.getReg .x2 - 1040 + 680 by
        addr_omega [hb], e,
        show s.getReg .x2 - 1040 + 600 = s.getReg .x2 - 464 + BitVec.ofNat 64 (8 * 3) by
        addr_omega [hb]]
      exact ht.wt 3 (by decide)
    · have e := b8000b7b8_m_x2_688 h7
      rw [ht.sp] at e
      rw [show s.getReg .x2 - 384 + BitVec.ofNat 64 (8 * 4) = s.getReg .x2 - 1040 + 688 by
        addr_omega [hb], e,
        show s.getReg .x2 - 1040 + 608 = s.getReg .x2 - 464 + BitVec.ofNat 64 (8 * 4) by
        addr_omega [hb]]
      exact ht.wt 4 (by decide)
    · have e := b8000b7b8_m_x2_696 h7
      rw [ht.sp] at e
      rw [show s.getReg .x2 - 384 + BitVec.ofNat 64 (8 * 5) = s.getReg .x2 - 1040 + 696 by
        addr_omega [hb], e,
        show s.getReg .x2 - 1040 + 616 = s.getReg .x2 - 464 + BitVec.ofNat 64 (8 * 5) by
        addr_omega [hb]]
      exact ht.wt 5 (by decide)
    · have e := b8000b7b8_m_x2_704 h7
      rw [ht.sp] at e
      rw [show s.getReg .x2 - 384 + BitVec.ofNat 64 (8 * 6) = s.getReg .x2 - 1040 + 704 by
        addr_omega [hb], e,
        show s.getReg .x2 - 1040 + 624 = s.getReg .x2 - 464 + BitVec.ofNat 64 (8 * 6) by
        addr_omega [hb]]
      exact ht.wt 6 (by decide)
  have scal7 : eAt t7 (s.getReg .x2 - 384 + 56) = (gacc lam Wl pend (i + 1)).2 := by
    rw [← ht.sc]
    apply eAt_congr
    · have e := b8000b7b8_m_x2_712 h7; rw [ht.sp] at e
      rw [show s.getReg .x2 - 384 + 56 = s.getReg .x2 - 1040 + 712 by rv_eval [], e,
        show s.getReg .x2 - 1040 + 632 = s.getReg .x2 - 408 by rv_eval []]
    · have e := b8000b7b8_m_x2_720 h7; rw [ht.sp] at e
      rw [show s.getReg .x2 - 384 + 56 + 8 = s.getReg .x2 - 1040 + 720 by rv_eval [], e,
        show s.getReg .x2 - 1040 + 640 = s.getReg .x2 - 408 + 8 by rv_eval []]
    · have e := b8000b7b8_m_x2_728 h7; rw [ht.sp] at e
      rw [show s.getReg .x2 - 384 + 56 + 16 = s.getReg .x2 - 1040 + 728 by rv_eval [], e,
        show s.getReg .x2 - 1040 + 648 = s.getReg .x2 - 408 + 16 by rv_eval []]
  have sc7 : eAt t7 (s.getReg .x2 - 408) = (gacc lam Wl pend (i + 1)).2 := by
    rw [← ht.sc]; exact f7.eAt fun j hj hw ↦ by addr_omega [hw, hj, hb]
  have quad7 : eListAt t7 (g.getMem (s.getReg .x2 - 896)) (g.getReg .x23).toNat =
      (gacc lam Wl pend (i + 1)).1.runningQuad := by
    rw [← ht.quad]
    refine f7.eListAt fun j hj hw ↦ ?_
    rcases hQb with h0 | h0
    · omega
    · addr_omega [hw, hj, hb, h0, hgh]
  have hfr7 : DFrame u t7 (GlueW s g t7) := Z7.mono fun a ha ↦ by
    rcases ha with ha | ha | ha | ha
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
  have x87 : t7.getReg .x8 = vecLen u (s.getReg .x2 - 664) := by
    rw [b8000b7b8_x8 h7, ht.sp, show s.getReg .x2 - 1040 + 392 = s.getReg .x2 - 664 + 16 by
      rv_eval [], ← f7 _ fun j hj hw ↦ by addr_omega [hw, hj, hb]]
    simp only [vecLen] at elen
    exact elen
  have h392 : t.getMem (t.getReg .x2 + 392) = vecLen u (s.getReg .x2 - 664) := by
    rw [ht.sp, show s.getReg .x2 - 1040 + 392 = s.getReg .x2 - 664 + 16 by rv_eval [],
      ← f7 _ fun j hj hw ↦ by addr_omega [hw, hj, hb]]
    simp only [vecLen] at elen
    exact elen
  have h376 : t.getMem (t.getReg .x2 + 376) = vecCap u (s.getReg .x2 - 664) := by
    rw [ht.sp, show s.getReg .x2 - 1040 + 376 = s.getReg .x2 - 664 by rv_eval [],
      ← f7 _ fun j hj hw ↦ by addr_omega [hw, hj, hb]]
    exact ecap
  exact ⟨t7, r7, {
    sp := sp7
    regs := fun r hr ↦ by
      rw [k7 r (by simp only [ZK] at hr; revert hr; decide +revert), ht.regs r hr]
    x8 := x87
    inv := inv7
    nx := nx7.trans ht.nx
    fr := hfr7
    ecap := ecap
    eptr := eptr
    elen := elen
    old := old7
    stage := stage7
    scal := scal7
    sc := sc7
    quad := quad7
    pcA := fun h ↦ b8000b7b8_pc_taken h7 (by rw [h392, h376]; exact h)
    pcB := fun h ↦ b8000b7b8_pc_not_taken h7 (by rw [h392, h376]; exact h) }⟩

end Rv64Verifier.Proofs.Pcs.Vso
