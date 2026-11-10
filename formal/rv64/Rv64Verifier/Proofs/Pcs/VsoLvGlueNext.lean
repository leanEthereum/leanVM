import Rv64Verifier.Proofs.Pcs.VsoLvGluePush

/-!
# `verify_stacked_opening`'s glue: one pending claim glued

`gpushB`: after the push (`GEnd`), the invariant holds for `i + 1` claims; `gstep` is one
pending claim from `0x8000b6b4`.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts Rv64Verifier.Blocks.F38
  LeanVM.Protocol
open Rv64Verifier.Sym (reduceReg reducePc reduceMem reduceWrites reduceObl)

theorem gluedAt_congr {v u : MachineState} {a b : Word} (h : WordsEq v a u b 11)
    (hb : WBufs v u b) : gluedAt v a = gluedAt u b := by
  simp only [gluedAt]
  rw [weightAt_congr (h.ptrs (by omega)) hb, h.get 10 (by omega) 80 (by decide)]
  congr 1
  apply eAt_congr
  · exact h.get 7 (by omega) 56 (by decide)
  · rw [BitVec.add_assoc, BitVec.add_assoc]; exact h.get 8 (by omega) _ (by decide)
  · rw [BitVec.add_assoc, BitVec.add_assoc]; exact h.get 9 (by omega) _ (by decide)

/-- **After `i + 1` claims**: the invariant, from the push's end. -/
theorem gpushB {s g : MachineState} {lam : E} {Wl : Model.Pcs.WhirLocals}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {i : ℕ} {u w z : MachineState}
    (hpre : VsoPre s) (hg : GlueIn s g lam Wl pend) (hu : GInv s g lam Wl pend i u)
    (hi : i < pend.length) (hw : GAt67 s g lam Wl pend i u w) (hz : GEnd s u w z) :
    GInv s g lam Wl pend (i + 1) z := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  obtain ⟨hp8, hp0, hde, hd88, hdc⟩ := hw.dest
  have hps := hw.lo hg
  have hwh := hw.heap.hi
  simp only [heapEnd] at hwh
  have hgh := hg.heap.hi
  simp only [heapEnd] at hgh
  have hmo := hu.mono
  have hmw := hw.mono
  have hnz : heapNext z = heapNext w := by simp only [heapNext, hz.nx]
  have hroom := hw.room
  have hn := pend_len hg.pnd
  -- the slot lies in `glued`'s buffer at `g`, or in the heap allocated since
  have hdW : ∀ y, Within y (gDest s u w) 88 → GlueW s g z y := fun y hy ↦ by
    rcases hw.gbuf with ⟨e1, e2⟩ | h0
    · refine Or.inr (Or.inl ?_)
      rw [← e1, ← e2]; simp only [Within] at hy ⊢; omega
    · simp only [NewBuf] at h0
      rcases h0.2 with h1 | h1
      · omega
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))))
        simp only [Fresh, Within] at hy ⊢; omega
  have frz : DFrame w z (GlueW s g z) := hz.fr.mono fun a ha ↦ by
    rcases ha with ha | ha | ha
    · exact hdW a ha
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha, hb])))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ha)))))
  have fru : DFrame u z (GlueW s g z) :=
    (hw.fr.mono fun a ha ↦ GlueW.mono (by rw [hnz]) ha).trans frz fun _ h ↦ h
  have frg : DFrame g z (GlueW s g z) :=
    (hu.fr.mono fun a ha ↦ GlueW.mono (by rw [hnz]; omega) ha).trans fru fun _ h ↦ h
  -- `glued`'s header at `z`
  have hdr (o : ℕ) (ho : o = 0 ∨ o = 8) :
      z.getMem (s.getReg .x2 - 664 + BitVec.ofNat 64 o) =
        w.getMem (s.getReg .x2 - 664 + BitVec.ofNat 64 o) :=
    hz.fr _ fun j hj hx ↦ by
      rcases hx with hx | hx | hx <;> rcases ho with rfl | rfl <;>
        addr_omega [hx, hj, hb, hde, hd88, hdc, hwh]
  have ecap : vecCap z (s.getReg .x2 - 664) = vecCap w (s.getReg .x2 - 664) := by
    have := hdr 0 (Or.inl rfl); simpa [vecCap] using this
  have eptr : vecPtr z (s.getReg .x2 - 664) = vecPtr w (s.getReg .x2 - 664) := by
    have := hdr 8 (Or.inr rfl); simpa [vecPtr] using this
  have hlenz : (vecLen z (s.getReg .x2 - 664)).toNat = (vecLen u (s.getReg .x2 - 664)).toNat + 1 := by
    rw [hz.len, BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl]; omega
  have hlc := hu.gv.len
  -- the old claims' words and buffers
  have oldW : ∀ j < (vecLen u (s.getReg .x2 - 664)).toNat,
      WordsEq z (vecPtr z (s.getReg .x2 - 664) + BitVec.ofNat 64 (88 * j)) u
        (vecPtr u (s.getReg .x2 - 664) + BitVec.ofNat 64 (88 * j)) 11 := fun j hj k hk ↦ by
    rw [eptr, ← hw.old j hj k hk]
    exact hz.fr _ fun x hx hX ↦ by
      rcases hX with hX | hX | hX <;> addr_omega [hX, hx, hj, hk, hb, hde, hd88, hdc, hwh]
  have oldB : ∀ j < (vecLen u (s.getReg .x2 - 664)).toNat,
      WBufs z u (vecPtr u (s.getReg .x2 - 664) + BitVec.ofNat 64 (88 * j)) := fun j hj ↦
    WBufs.of_frame fru fun y hy ↦ hg.rd hpre (hu.bufs j hj y hy)
  -- the new claim's
  have newW : WordsEq z (gDest s u w) g (pAddr g s i + 24) 7 := fun k hk ↦ by
    rw [hz.words k (by omega)]; exact hw.stage k hk
  have hrd : ∀ y, InBufs g (pAddr g s i + 24) y → GlueReads s g y := fun y hy ↦
    Or.inr (Or.inl ⟨i, by rw [hn]; exact hi, Or.inr hy⟩)
  have newB : WBufs z g (pAddr g s i + 24) := WBufs.of_frame frg fun y hy ↦ hg.rd hpre (hrd y hy)
  have hnew : gluedAt z (gDest s u w) =
      ⟨(gacc lam Wl pend (i + 1)).2, Wl.folds.length, weightAt g (pAddr g s i + 24)⟩ := by
    simp only [gluedAt]
    rw [weightAt_congr (newW.ptrs (by omega)) newB, ← hw.scal]
    congr 1
    · apply eAt_congr
      · rw [show gDest s u w + 56 = gDest s u w + BitVec.ofNat 64 (8 * 7) from rfl,
          hz.words 7 (by omega)]; rfl
      · rw [BitVec.add_assoc, show gDest s u w + (56 + 8) = gDest s u w + BitVec.ofNat 64 (8 * 8) from rfl,
          hz.words 8 (by omega), BitVec.add_assoc]; rfl
      · rw [BitVec.add_assoc, show gDest s u w + (56 + 16) = gDest s u w + BitVec.ofNat 64 (8 * 9) from rfl,
          hz.words 9 (by omega), BitVec.add_assoc]; rfl
    · rw [hz.fold, hu.x20, hg.folds, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hg.flen]
  have hdest : gDest s u w = vecPtr z (s.getReg .x2 - 664) +
      BitVec.ofNat 64 (88 * (vecLen u (s.getReg .x2 - 664)).toNat) := by
    rw [eptr]; rfl
  have hgl : gluedListAt z (vecPtr z (s.getReg .x2 - 664)) (vecLen z (s.getReg .x2 - 664)).toNat =
      (gacc lam Wl pend (i + 1)).1.glued := by
    rw [hlenz, gacc_succ hi]
    show _ = (gacc lam Wl pend i).1.glued ++
      [⟨(gacc lam Wl pend i).2 * lam, (gacc lam Wl pend i).1.folds.length, pend[i].2⟩]
    rw [gacc_folds, pend_get hg.pnd hi, ← hu.gl]
    simp only [gluedListAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    congr 1
    · apply List.map_congr_left
      intro j hj
      simp only [List.mem_range] at hj
      exact gluedAt_congr (oldW j hj) (oldB j hj)
    · rw [← hdest, hnew, gacc_succ hi]
      rfl
  have hQb := hg.quad.2.2
  refine {
    sp := hz.sp
    regs := fun q hq ↦ by
      rw [hz.regs q (by revert hq; decide +revert)]; exact hu.regs q hq
    x20 := by rw [hz.regs .x20 (by decide)]; exact hu.x20
    x24 := by rw [hz.regs .x24 (by decide)]; exact hu.x24
    x27 := by rw [hz.regs .x27 (by decide)]; exact hu.x27
    inv := hz.inv
    heap := ⟨by rw [hnz]; exact hw.heap.lo, by rw [hnz]; exact hw.heap.hi⟩
    mono := by rw [hnz]; omega
    fr := frg
    sc := by
      rw [← hw.sc]
      exact hz.fr.eAt fun j hj hx ↦ by
        rcases hx with hx | hx | hx <;> addr_omega [hx, hj, hb, hde, hd88, hdc, hwh]
    quad := by
      rw [← hw.quad]
      refine hz.fr.eListAt fun j hj hx ↦ ?_
      rcases hQb with h0 | h0
      · omega
      rcases hx with hx | hx | hx
      · rcases hw.gbuf with ⟨e1, e2⟩ | h1
        · have hap := hg.apart
          rw [← e1, ← e2] at hap
          simp only [Apart] at hap
          rcases hap with h2 | h2 | h2 | h2
          · omega
          · omega
          · addr_omega [hx, hj, h2, hde, hd88, hdc, hwh]
          · addr_omega [hx, hj, h2, hde, hd88, hdc, hwh, h0]
        · simp only [NewBuf] at h1
          rcases h1.2 with h2 | h2
          · omega
          · addr_omega [hx, hj, h2, hde, hd88, hdc, hwh, h0]
      · addr_omega [hx, hj, hb, h0, hgh]
      · addr_omega [hx, hj, hb, h0, hgh]
    gv := by
      have hraw := hw.gv.raw
      simp only [RawVecOk, Buf] at hraw
      refine ⟨?_, by rw [hlenz, ecap]; omega⟩
      simp only [RawVecOk, Buf, ecap, eptr, hnz]
      exact hraw
    glen := by rw [hlenz, hu.glen]; omega
    gl := hgl
    gbuf := by
      rw [eptr, ecap]
      rcases hw.gbuf with h0 | h0
      · exact Or.inl h0
      · refine Or.inr ?_
        simp only [NewBuf] at h0 ⊢
        rw [hnz]; exact h0
    bufs := fun j hj y hy ↦ by
      rw [hlenz] at hj
      simp only [gAddr] at hy
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hu.bufs j hj y ((InBufs_congr ((oldW j hj).ptrs (by omega)) y).mp hy)
      · rw [← hdest] at hy
        exact hrd y ((InBufs_congr (newW.ptrs le_rfl) y).mp hy)
    aligned := fun j hj ↦ by
      rw [hlenz] at hj
      simp only [gAddr]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact (WeightAligned_congr ((oldW j hj).ptrs (by omega))).mpr (hu.aligned j hj)
      · rw [← hdest]
        exact (WeightAligned_congr (newW.ptrs le_rfl)).mpr (hg.paligned i (by rw [hn]; exact hi)) }

end Rv64Verifier.Proofs.Pcs.Vso
