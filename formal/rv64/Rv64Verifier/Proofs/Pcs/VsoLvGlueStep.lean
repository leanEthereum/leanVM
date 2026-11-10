import Rv64Verifier.Proofs.Pcs.VsoLvGlueInner

/-!
# `verify_stacked_opening`'s glue: a pending claim, to its glued claim's assembly

`GInv` is the glue after `i` pending claims (at `0x8000b6b4` for the next one). From there
(`gfront`): the claim's weight copied to `S - 464`, `scalar *= lam`, the intro added to the
quadratic, to `0x8000b7b8` (`GMid`).
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

/-- After `i` pending claims glued, from `g`. -/
structure GInv (s g : MachineState) (lam : E) (Wl : Model.Pcs.WhirLocals)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) (i : ℕ) (u : MachineState) : Prop where
  sp : u.getReg .x2 = s.getReg .x2 - 1040
  regs : ∀ q ∈ [Reg.x9, .x23, .x25, .x26], u.getReg q = g.getReg q
  x20 : u.getReg .x20 = g.getMem (s.getReg .x2 - 672)
  x24 : u.getReg .x24 = vecPtr g (s.getReg .x2 - 616) + BitVec.ofNat 64 (80 * pend.length)
  x27 : u.getReg .x27 =
    g.getMem (s.getReg .x2 - 896) + BitVec.ofNat 64 (24 * (g.getReg .x23).toNat)
  inv : InvR s u (u.getMem nextAddr)
  heap : HeapOk u
  mono : heapNext g ≤ heapNext u
  fr : DFrame g u (GlueW s g u)
  sc : eAt u (s.getReg .x2 - 408) = (gacc lam Wl pend i).2
  quad : eListAt u (g.getMem (s.getReg .x2 - 896)) (g.getReg .x23).toNat =
    (gacc lam Wl pend i).1.runningQuad
  gv : VecOk u (s.getReg .x2 - 664) 88 8
  glen : (vecLen u (s.getReg .x2 - 664)).toNat = Wl.glued.length + i
  gl : gluedListAt u (vecPtr u (s.getReg .x2 - 664)) (vecLen u (s.getReg .x2 - 664)).toNat =
    (gacc lam Wl pend i).1.glued
  gbuf : (vecPtr u (s.getReg .x2 - 664) = vecPtr g (s.getReg .x2 - 664) ∧
      vecCap u (s.getReg .x2 - 664) = vecCap g (s.getReg .x2 - 664)) ∨
    NewBuf g u (vecPtr u (s.getReg .x2 - 664)) ((vecCap u (s.getReg .x2 - 664)).toNat * 88) 8
  bufs : ∀ j < (vecLen u (s.getReg .x2 - 664)).toNat, ∀ y, InBufs u (gAddr u s j) y →
    GlueReads s g y
  aligned : ∀ j < (vecLen u (s.getReg .x2 - 664)).toNat, WeightAligned u (gAddr u s j)

/-- At `0x8000b7b8`, claim `i`'s weight at `S - 464`, its scalar at `S - 408`, the quadratic
updated, from `u`. -/
structure GMid (s g : MachineState) (lam : E) (Wl : Model.Pcs.WhirLocals)
    (pend : List (List E × Model.Pcs.GluedWeightRust)) (i : ℕ) (u t : MachineState) : Prop where
  pc : t.pc = 0x8000b7b8
  sp : t.getReg .x2 = s.getReg .x2 - 1040
  regs : ∀ r ∈ ZK, t.getReg r = u.getReg r
  inv : InvR s t (t.getMem nextAddr)
  heap : HeapOk t
  nx : t.getMem nextAddr = u.getMem nextAddr
  fr : DFrame u t fun a ↦ Within a (g.getMem (s.getReg .x2 - 896)) (24 * (g.getReg .x23).toNat) ∨
    Within a (s.getReg .x2 - 464) 160 ∨ Within a (s.getReg .x2 - 160) 24 ∨
    Within a (s.getReg .x2 - 2464) 1424
  sc : eAt t (s.getReg .x2 - 408) = (gacc lam Wl pend (i + 1)).2
  quad : eListAt t (g.getMem (s.getReg .x2 - 896)) (g.getReg .x23).toNat =
    (gacc lam Wl pend (i + 1)).1.runningQuad
  wt : WordsEq t (s.getReg .x2 - 464) g (pAddr g s i + 24) 7

/-- What the glue reads misses what it writes, below `heapEnd`. -/
theorem GlueIn.rd {s g z : MachineState} {lam : E} {Wl : Model.Pcs.WhirLocals}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} (hpre : VsoPre s)
    (hg : GlueIn s g lam Wl pend) {y : Word} (hy : GlueReads s g y) :
    ¬ GlueW s g z y ∧ y.toNat < heapEnd := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  obtain ⟨h1, h2, h3, h4⟩ := hg.reads y hy
  have hgh := hg.heap.hi
  refine ⟨fun hw ↦ ?_, by omega⟩
  simp only [heapEnd] at hgh
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw
  · exact h3 hw
  · exact h4 hw
  · addr_omega [hw, hb, h2, hgh]
  · addr_omega [hw, hb, h2, hgh]
  · addr_omega [hw, hb, h2, hgh]
  · addr_omega [hw, hb, h2, hgh]
  · addr_omega [hw, hnx, hb, h2, hgh]
  · simp only [Fresh] at hw; omega

/-- Two ranges with no byte in common are apart. -/
theorem apart_of_forall {a b : Word} {n m : ℕ} (h : ∀ y : Word, Within y a n → ¬ Within y b m) :
    Apart a n b m := by
  simp only [Apart]
  by_cases hn : n = 0
  · exact Or.inl hn
  by_cases hm : m = 0
  · exact Or.inr (Or.inl hm)
  refine Or.inr (Or.inr (Classical.byContradiction fun hc ↦ ?_))
  simp only [not_or, not_le] at hc
  have ha := a.isLt
  have hb := b.isLt
  have := h (BitVec.ofNat 64 (max a.toNat b.toNat)) (by
    simp only [Within, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show max a.toNat b.toNat < 2 ^ 64 by
      omega)]; omega)
  exact this (by
    simp only [Within, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show max a.toNat b.toNat < 2 ^ 64 by
      omega)]; omega)

theorem GlueW.mono {s g z z' : MachineState} {a : Word} (h : heapNext z ≤ heapNext z')
    (ha : GlueW s g z a) : GlueW s g z' a := by
  rcases ha with ha | ha | ha | ha | ha | ha | ha | ha
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · exact Or.inr (Or.inr (Or.inl ha))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ha)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha))))))
  · simp only [Fresh] at ha
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨ha.1, by omega⟩))))))

/-- The pending claims, element `i`. -/
theorem pend_get {g s : MachineState} {pend : List (List E × Model.Pcs.GluedWeightRust)}
    (h : pendAt g (vecPtr g (s.getReg .x2 - 616)) (vecLen g (s.getReg .x2 - 616)).toNat = pend)
    {i : ℕ} (hi : i < pend.length) :
    pend[i] = (vecEs g (pAddr g s i), weightAt g (pAddr g s i + 24)) := by
  subst h
  simp [pendAt, pAddr]

theorem pend_len {g s : MachineState} {pend : List (List E × Model.Pcs.GluedWeightRust)}
    (h : pendAt g (vecPtr g (s.getReg .x2 - 616)) (vecLen g (s.getReg .x2 - 616)).toNat = pend) :
    (vecLen g (s.getReg .x2 - 616)).toNat = pend.length := by
  subst h; simp [pendAt]

/-- Where the glue writes: its stack slots, `NEXT`, or below `heapEnd`. -/
theorem GlueW.split {s g z : MachineState} {lam : E} {Wl : Model.Pcs.WhirLocals}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} (hg : GlueIn s g lam Wl pend)
    (hz : heapNext z ≤ heapEnd) {a : Word} (h : GlueW s g z a) :
    Within a (s.getReg .x2 - 664) 24 ∨ Within a (s.getReg .x2 - 464) 160 ∨
      Within a (s.getReg .x2 - 160) 24 ∨ Within a (s.getReg .x2 - 2464) 1424 ∨
      Within a nextAddr 8 ∨ a.toNat < heapEnd := by
  have hgh := hg.heap.hi
  rcases h with h | h | h | h | h | h | h | h
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    rcases hg.quad.2.2 with h0 | h0
    · simp only [Within] at h; omega
    · simp only [Within] at h; omega
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    have hraw := hg.glued.1.raw
    simp only [RawVecOk, Buf] at hraw
    rcases hraw.2 with h0 | h0
    · simp only [Within] at h; omega
    · simp only [Within] at h; omega
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · simp only [Fresh] at h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))

end Rv64Verifier.Proofs.Pcs.Vso
