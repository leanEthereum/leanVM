import Rv64Verifier.Proofs.Pcs.VsoTailFrontB
import Rv64Verifier.Proofs.Pcs.VsoTailCtx
import Rv64Verifier.Proofs.Pcs.VsoLvGlue

/-!
# `verify_stacked_opening`'s level tail: into the glue

From the rows' end (`AtR`) and the push (`Fronted`), the glue's entry `GlueIn`: the pending
claims the opening left and the intro message's `Queries` claim, the fold rounds' quadratic and
folds, `lam`, the head's glued claims.
-/

namespace Rv64Verifier.Proofs.Pcs.Vso
open RiscvZkvm.Rv64 LeanVM.Parameters Rv64Verifier.Contracts Rv64Verifier.Runtime
  Rv64Verifier.Transcript Rv64Verifier.Pcs Rv64Verifier.PcsContracts LeanVM.Protocol

/-- The heap allocated since the entry and before `r`, outside the pending claims' buffer, misses
what the push writes. -/
theorem notFrW {s r g : MachineState} {y : Word} (hpre : VsoPre s) (hr : HeapOk r)
    (h1 : heapNext s ≤ y.toNat) (h2 : y.toNat < heapNext r)
    (h3 : ¬ Within y (vecPtr r (s.getReg .x2 - 616))
      ((vecCap r (s.getReg .x2 - 616)).toNat * 80)) : ¬ FrW s r g y := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIf := hI.free
  simp only [Outside] at hIf
  have hhi := hr.hi
  simp only [heapEnd] at hhi
  intro hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  · addr_omega [hw, hb, h2, hhi]
  · addr_omega [hw, hb, h2, hhi]
  · addr_omega [hw, hb, h2, hhi]
  · addr_omega [hw, hb, h2, hhi]
  · addr_omega [hw, hb, h2, hhi]
  · addr_omega [hw, hb, h2, hhi]
  · addr_omega [hw, hb, h2, hhi]
  · rcases hIf.1 with h0 | h0
    · addr_omega [hw, hS, h0, h1]
    · addr_omega [hw, hS, h0, h2, hhi]
  · addr_omega [hw, h2, hhi]
  · exact h3 hw
  · simp only [Fresh] at hw; omega

/-- A `Vec<E>` at `a` in `g` with `b`'s header in `r`, its elements unchanged. -/
theorem vecEs_congr {r g : MachineState} {a b : Word} {X : Word → Prop} (hD : DFrame r g X)
    (h8 : g.getMem (a + 8) = r.getMem (b + 8)) (h16 : g.getMem (a + 16) = r.getMem (b + 16))
    (hbuf : ∀ i < 24 * (vecLen r b).toNat, ¬ X (vecPtr r b + BitVec.ofNat 64 i)) :
    vecEs g a = vecEs r b := by
  simp only [vecEs, vecPtr, vecLen, h8, h16]
  exact hD.eListAt hbuf

theorem addOfNat (P : Word) (a b : ℕ) :
    P + BitVec.ofNat 64 a + BitVec.ofNat 64 b = P + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem lenG {s : MachineState} {x : LCtx} {h t u w r g : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf qq res q : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (ha : AtR s x h t u w r ℓ Wl lf qq res pend d qs) (hf : Fronted s r g q) :
    (vecLen g (s.getReg .x2 - 616)).toNat = (vecLen r (s.getReg .x2 - 616)).toNat + 1 := by
  have hhr := ha.heap.hi
  have hraw := ha.pnd.vec.raw
  simp only [RawVecOk, Buf] at hraw
  have hlc := ha.pnd.vec.len
  rw [hf.len, BitVec.toNat_add]
  have : (vecLen r (s.getReg .x2 - 616)).toNat < 2 ^ 63 := by
    rcases hraw.2 with h0 | h0
    · omega
    · simp only [heapEnd] at hhr; omega
  simp only [show (1 : Word).toNat = 1 from rfl]; omega

/-- The pending claims at the glue's entry: the opening's, then the intro message's. -/
theorem pendG {s : MachineState} {x : LCtx} {h t u w r g : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf qq res q : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (ha : AtR s x h t u w r ℓ Wl lf qq res pend d qs) (hf : Fronted s r g q) :
    pendAt g (vecPtr g (s.getReg .x2 - 616)) (vecLen g (s.getReg .x2 - 616)).toNat =
      pend ++ [(q, Model.Pcs.GluedWeightRust.queries (mlOf s Wl lf) qs
        (Verifier.powers (eAt w (s.getReg .x2 - 384)) qs.length))] := by
  have hb := bounds hpre
  have hP := ha.pnd
  have hhr := ha.heap.hi
  have hsl := hpre.heap.lo
  have hst : heapNext s ≤ heapNext t := le_trans ha.head.facts.hs
    (le_trans ha.head.facts.hL ha.ht)
  have hraw := hP.vec.raw
  simp only [RawVecOk, Buf] at hraw
  have hlc := hP.vec.len
  obtain ⟨Pr, hPr⟩ : ∃ Pr, vecPtr r (s.getReg .x2 - 616) = Pr := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, (vecLen r (s.getReg .x2 - 616)).toNat = n := ⟨_, rfl⟩
  have hn1 : (vecLen g (s.getReg .x2 - 616)).toNat = n + 1 := by
    rw [hf.len, BitVec.toNat_add, hn]
    have : n < 2 ^ 63 := by
      rcases hraw.2 with h0 | h0
      · omega
      · simp only [heapEnd] at hhr; omega
    simp only [show (1 : Word).toNat = 1 from rfl]; omega
  have hpend := hP.elems
  rw [hPr, hn] at hpend
  rw [hn1, ← hpend, pendAt, pendAt, List.range_succ, List.map_append]
  have hfr := hf.fr
  have hpu := ha.pu
  have hold (o : ℕ) (ho : o % 8 = 0) (hoN : o + 8 ≤ 80 * n) :
      g.getMem (vecPtr g (s.getReg .x2 - 616) + BitVec.ofNat 64 o) =
        r.getMem (Pr + BitVec.ofNat 64 o) := by
    rw [← hPr]; exact hf.old o ho (by rw [hn]; exact hoN)
  -- a byte of the heap allocated since `t`, below `r`'s `NEXT`, outside the pending buffer
  have nW (y : Word) (h1 : heapNext t ≤ y.toNat) (h2 : y.toNat < heapNext r)
      (h3 : ¬ Within y (vecPtr r (s.getReg .x2 - 616))
        ((vecCap r (s.getReg .x2 - 616)).toNat * 80)) : ¬ FrW s r g y :=
    notFrW hpre ha.heap (by omega) h2 h3
  congr 1
  · -- the opening's claims
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range] at hi
    have hin : i < (vecLen r (s.getReg .x2 - 616)).toNat := by rw [hn]; exact hi
    have hI := hP.intro i hin
    have hO := hP.ood i hin
    rw [hPr] at hI hO
    have hIr := hI.raw
    simp only [RawVecOk, Buf] at hIr
    have hIl := hI.len
    have hOr := hO.2.raw
    simp only [RawVecOk, Buf] at hOr
    have hOl := hO.2.len
    refine Prod.ext ?_ ?_
    · have w8 := hold (80 * i + 8) (by omega) (by omega)
      have w16 := hold (80 * i + 16) (by omega) (by omega)
      rw [← addOfNat, ← addOfNat] at w8 w16
      refine vecEs_congr hfr w8 w16 fun k hk ↦ ?_
      rcases hIr.2 with h0 | h0
      · omega
      · have hy : Within (vecPtr r (Pr + BitVec.ofNat 64 (80 * i)) + BitVec.ofNat 64 k)
            (vecPtr r (Pr + BitVec.ofNat 64 (80 * i)))
            ((vecCap r (Pr + BitVec.ofNat 64 (80 * i))).toNat * 24) := by
          simp only [Within]; simp only [heapEnd] at hhr; addr_omega [h0, hk, hIl, hhr]
        have hPB : PBufs r (s.getReg .x2 - 616)
            (vecPtr r (Pr + BitVec.ofNat 64 (80 * i)) + BitVec.ofNat 64 k) :=
          Or.inr ⟨i, hin, Or.inl (by rw [hPr]; exact hy)⟩
        have hfr' := hP.fresh _ hPB
        exact nW _ hfr'.1 hfr'.2 (hP.self i hin _ (Or.inl (by rw [hPr]; exact hy)))
    · have e24 : g.getMem (vecPtr g (s.getReg .x2 - 616) + BitVec.ofNat 64 (80 * i) + 24) =
          r.getMem (Pr + BitVec.ofNat 64 (80 * i) + 24) := by
        rw [show (24 : Word) = BitVec.ofNat 64 24 from rfl, addOfNat, addOfNat,
          hold _ (by omega) (by omega)]
      simp only [weightAt]
      rw [e24, ite_eq_left_of_eq_true _ _ (eq_true hO.1), ite_eq_left_of_eq_true _ _ (eq_true hO.1)]
      congr 1
      refine vecEs_congr hfr ?_ ?_ fun k hk ↦ ?_
      · rw [show (24 : Word) = BitVec.ofNat 64 24 from rfl, show (8 : Word) = BitVec.ofNat 64 8 from rfl,
          addOfNat, addOfNat, addOfNat, addOfNat, addOfNat, addOfNat, hold _ (by omega) (by omega)]
      · rw [show (24 : Word) = BitVec.ofNat 64 24 from rfl, show (8 : Word) = BitVec.ofNat 64 8 from rfl,
          show (16 : Word) = BitVec.ofNat 64 16 from rfl,
          addOfNat, addOfNat, addOfNat, addOfNat, addOfNat, addOfNat, hold _ (by omega) (by omega)]
      · rcases hOr.2 with h0 | h0
        · omega
        · have hy : Within (vecPtr r (Pr + BitVec.ofNat 64 (80 * i) + 24 + 8) + BitVec.ofNat 64 k)
              (vecPtr r (Pr + BitVec.ofNat 64 (80 * i) + 24 + 8))
              (24 * (vecLen r (Pr + BitVec.ofNat 64 (80 * i) + 24 + 8)).toNat) := by
            simp only [Within]; simp only [heapEnd] at hhr; addr_omega [h0, hk, hOl, hhr]
          have hIB : InBufs r (vecPtr r (s.getReg .x2 - 616) + BitVec.ofNat 64 (80 * i) + 24)
              (vecPtr r (Pr + BitVec.ofNat 64 (80 * i) + 24 + 8) + BitVec.ofNat 64 k) := by
            rw [InBufs, hPr, ite_eq_left_of_eq_true _ _ (eq_true hO.1)]; exact hy
          have hfr' := hP.fresh _ (Or.inr ⟨i, hin, Or.inr hIB⟩)
          exact nW _ hfr'.1 hfr'.2 (hP.self i hin _ (Or.inr hIB))
  · -- the intro message's claim
    have hE : vecPtr g (s.getReg .x2 - 616) + BitVec.ofNat 64 (80 * n) =
        pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat := by rw [hn]; rfl
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
    rw [hE]
    have w24 := hf.w24
    have w32 := hf.w32
    have w40 := hf.w40
    have w56 := hf.w56
    have w64 := hf.w64
    have w72 := hf.w72
    have hfi := hf.intro.2.1
    generalize pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat = e at w24 w32 w40 w56 w64 w72 hfi ⊢
    have hqlen : qs.length < 2 ^ 32 := by
      rcases ha.qbuf.2.2 with h0 | h0
      · omega
      · simp only [heapEnd] at hhr; have := ha.wr; omega
    have h24 : g.getMem (e + 24) ≠
        0xffffffffffffffff := by
      rw [w24, ha.m1000]
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by rw [show (0xffffffffffffffff : Word).toNat = 2 ^ 64 - 1 from rfl]; omega)
    refine Prod.ext hfi ?_
    simp only [weightAt]
    rw [ite_eq_right_of_eq_false _ _ (eq_false h24)]
    obtain ⟨hqw, hq8, hqb⟩ := ha.qbuf
    have hpw := ha.pw
    obtain ⟨hpwv, hpwe, hpwl, hpwb⟩ := hpw
    have hml : (mlOf s Wl lf) < 2 ^ 64 := by
      have := (s.getReg .x12).isLt; simp only [mlOf]; omega
    congr 1
    · rw [show e + 24 + 48 =
          e + 72 by rw [BitVec.add_assoc]; rfl,
        w72, ha.m872, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hml]
    · simp only [vecWords, vecPtr, vecLen]
      rw [show e + 24 + 8 =
          e + 32 by rw [BitVec.add_assoc]; rfl,
        show e + 24 + 16 =
          e + 40 by rw [BitVec.add_assoc]; rfl,
        w32, w40, ha.x26, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine (DFrame.readWords' hfr (fun a hw hin ↦ ?_) ?_).trans hqw
      · rcases hqb with h0 | h0
        · simp only [Within] at hin; omega
        · have htu := ha.tu
          have hwr := ha.wr
          refine nW a (by addr_omega [hin, h0, htu]) (by addr_omega [hin, h0, hwr])
            (fun hin' ↦ ?_) hw
          have := hpu a (Or.inl hin')
          addr_omega [hin, h0, this]
      · rcases hqb with h0 | h0
        · omega
        · simp only [heapEnd] at hhr; have := ha.wr; omega
    · rw [show e + 24 + 24 =
          e + 48 by rw [BitVec.add_assoc]; rfl, ← hpwe]
      refine vecEs_congr hfr ?_ ?_ fun k hk ↦ ?_
      · rw [show e + 48 + 8 =
            e + 56 by rw [BitVec.add_assoc]; rfl,
          w56, show s.getReg .x2 - 488 + 8 = s.getReg .x2 - 480 by rv_eval []]
      · rw [show e + 48 + 16 =
            e + 64 by rw [BitVec.add_assoc]; rfl,
          w64, show s.getReg .x2 - 488 + 16 = s.getReg .x2 - 472 by rv_eval []]
      · have hl := hpwv.len
        rcases hpwb with h0 | h0
        · omega
        · simp only [heapEnd] at hhr
          have hwr := ha.wr
          have htu := ha.tu
          refine nW _ (by addr_omega [h0, hk, hl, hhr, htu])
            (by addr_omega [h0, hk, hl, hhr, hwr]) fun hin' ↦ ?_
          have := hpu _ (Or.inl hin')
          addr_omega [h0, hk, hl, hhr, this]

/-- **The head's glued claims kept**, through a frame that misses their header, their buffer and
their weights' buffers. -/
theorem gluedKeep {s : MachineState} {x : LCtx} {h v : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {X : Word → Prop} (hpre : VsoPre s) (hh : Head s x h ℓ Wl)
    (hD : DFrame h v X)
    (hhdr : ∀ y : Word, (s.getReg .x2 - 664).toNat ≤ y.toNat → y.toNat < (s.getReg .x2 - 640).toNat →
      ¬ X y)
    (hbuf : ∀ y : Word, x.L ≤ y.toNat → y.toNat < heapNext h →
      ¬ Within y (vecPtr h (s.getReg .x2 - 688)) ((vecCap h (s.getReg .x2 - 688)).toNat * 24) →
      ¬ X y) :
    vecCap v (s.getReg .x2 - 664) = vecCap h (s.getReg .x2 - 664) ∧
    vecPtr v (s.getReg .x2 - 664) = vecPtr h (s.getReg .x2 - 664) ∧
    vecLen v (s.getReg .x2 - 664) = vecLen h (s.getReg .x2 - 664) ∧
    gluedListAt v (vecPtr v (s.getReg .x2 - 664)) (vecLen v (s.getReg .x2 - 664)).toNat = Wl.glued ∧
    ∀ i < (vecLen h (s.getReg .x2 - 664)).toNat,
      (∀ y, InBufs v (gAddr v s i) y ↔ InBufs h (gAddr h s i) y) ∧
      (WeightAligned v (gAddr v s i) ↔ WeightAligned h (gAddr h s i)) := by
  have hb := bounds hpre
  have hhi := hh.heap.hi
  have hF := hh.facts
  obtain ⟨hgv, hgl, hglo⟩ := hh.glued
  have hraw := hgv.raw
  simp only [RawVecOk, Buf] at hraw
  have hlc := hgv.len
  have hap := hh.apart.1
  have hdr (o : ℕ) (ho : o + 8 ≤ 24) :
      v.getMem (s.getReg .x2 - 664 + BitVec.ofNat 64 o) =
        h.getMem (s.getReg .x2 - 664 + BitVec.ofNat 64 o) :=
    hD _ fun i hi hx ↦ hhdr _ (by addr_omega [hb, hi, ho]) (by addr_omega [hb, hi, ho]) hx
  have ec : vecCap v (s.getReg .x2 - 664) = vecCap h (s.getReg .x2 - 664) := by
    simpa only [vecCap, add_ofNat_zero] using hdr 0 (by decide)
  have ep : vecPtr v (s.getReg .x2 - 664) = vecPtr h (s.getReg .x2 - 664) := hdr 8 (by decide)
  have el : vecLen v (s.getReg .x2 - 664) = vecLen h (s.getReg .x2 - 664) := hdr 16 (by decide)
  -- the glued claims' buffer
  have hgb (y : Word) (hy : Within y (vecPtr h (s.getReg .x2 - 664))
      ((vecCap h (s.getReg .x2 - 664)).toNat * 88)) : ¬ X y := by
    rcases hraw.2 with h0 | h0
    · simp only [Within] at hy; omega
    · rcases hglo with h1 | h1
      · have : (vecCap h (s.getReg .x2 - 664)).toNat = 0 := by rw [h1]; rfl
        simp only [Within] at hy; omega
      · refine hbuf y (by simp only [Within] at hy; omega) (by simp only [Within] at hy; omega) ?_
        intro hw
        simp only [Apart, Within] at hap hy hw
        omega
  have hWE (i : ℕ) (hi : i < (vecLen h (s.getReg .x2 - 664)).toNat) :
      WordsEq v (gAddr v s i) h (gAddr h s i) 11 := fun k hk ↦ by
    simp only [gAddr, ep]
    refine hD _ fun j hj hx ↦ hgb _ ?_ hx
    rcases hraw.2 with h0 | h0
    · omega
    · simp only [heapEnd] at hhi; addr_omega [h0, hj, hk, hi, hlc, hhi]
  have hWB (i : ℕ) (hi : i < (vecLen h (s.getReg .x2 - 664)).toNat) : WBufs v h (gAddr h s i) :=
    WBufs.of_frame hD fun y hy ↦ by
      obtain ⟨h1, h2, h3, -, -⟩ := hh.frozen i hi y hy
      exact ⟨hbuf y h1 h2 h3, by omega⟩
  refine ⟨ec, ep, el, ?_, fun i hi ↦ ⟨fun y ↦ InBufs_congr ((hWE i hi).ptrs (by omega)) y, ?_⟩⟩
  swap
  · have hp := (hWE i hi).ptrs (by omega)
    unfold WeightAligned
    rw [hp.w0, hp.p0, hp.p8, hp.p24]
  rw [ep, el, ← hgl]
  simp only [gluedListAt]
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  have h1 := hWE i hi
  have h2 := hWB i hi
  simp only [gAddr, ep] at h1 h2
  exact gluedAt_congr h1 h2

/-- What the level wrote from its head to the glue's entry. -/
def ZH (s h g : MachineState) (a : Word) : Prop :=
  Within a (s.getReg .x2 - 2464) 1800 ∨ Within a (s.getReg .x2 - 640) 640 ∨
    Within a (s.getReg .x10 + 8) 352 ∨ Within a nextAddr 8 ∨
    (heapNext h ≤ a.toNat ∧ a.toNat < heapNext g) ∨
    Within a (vecPtr h (s.getReg .x2 - 688)) ((vecCap h (s.getReg .x2 - 688)).toNat * 24)

theorem frHG {s : MachineState} {x : LCtx} {h t u w r g : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf qq res q : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (ha : AtR s x h t u w r ℓ Wl lf qq res pend d qs) (hf : Fronted s r g q) :
    DFrame h g (ZH s h g) := by
  have hb := bounds hpre
  have hmo := hf.mono
  have hP := ha.pnd
  have hrt : heapNext h ≤ heapNext r := le_trans ha.ht (le_trans ha.tu (le_trans ha.uw ha.wr))
  refine (ha.gfr.mono fun a ha' ↦ ?_).trans (hf.fr.mono fun a ha' ↦ ?_) fun _ h ↦ h
  · rcases ha' with ha' | ha' | ha' | ha' | ha' | ha'
    · exact Or.inl ha'
    · exact Or.inr (Or.inl ha')
    · exact Or.inr (Or.inr (Or.inl ha'))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ha'.1, by omega⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ha'))))
  · rcases ha' with ha' | ha' | ha' | ha' | ha' | ha' | ha' | ha' | ha' | ha' | ha'
    · exact Or.inl (by addr_omega [ha', hb])
    · exact Or.inr (Or.inl (by addr_omega [ha', hb]))
    · exact Or.inr (Or.inl (by addr_omega [ha', hb]))
    · exact Or.inr (Or.inl (by addr_omega [ha', hb]))
    · exact Or.inr (Or.inl (by addr_omega [ha', hb]))
    · exact Or.inr (Or.inl (by addr_omega [ha', hb]))
    · exact Or.inl (by addr_omega [ha', hb])
    · exact Or.inr (Or.inr (Or.inl (by addr_omega [ha'])))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ha')))
    · have hfr := hP.fresh a (Or.inl ha')
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by have := ha.ht; omega, by omega⟩))))
    · simp only [Fresh] at ha'
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, ha'.2⟩))))

/-- The glued claims at the glue's entry, the head's. -/
theorem gluedG {s : MachineState} {x : LCtx} {h t u w r g : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf qq res q : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (ha : AtR s x h t u w r ℓ Wl lf qq res pend d qs) (hf : Fronted s r g q) :
    vecCap g (s.getReg .x2 - 664) = vecCap h (s.getReg .x2 - 664) ∧
    vecPtr g (s.getReg .x2 - 664) = vecPtr h (s.getReg .x2 - 664) ∧
    vecLen g (s.getReg .x2 - 664) = vecLen h (s.getReg .x2 - 664) ∧
    gluedListAt g (vecPtr g (s.getReg .x2 - 664)) (vecLen g (s.getReg .x2 - 664)).toNat = Wl.glued ∧
    ∀ i < (vecLen h (s.getReg .x2 - 664)).toNat,
      (∀ y, InBufs g (gAddr g s i) y ↔ InBufs h (gAddr h s i) y) ∧
      (WeightAligned g (gAddr g s i) ↔ WeightAligned h (gAddr h s i)) := by
  have hb := bounds hpre
  obtain ⟨hnx, -⟩ := sfacts hpre
  have hI := hpre.self
  have hS := Region.bounds hI.ok.self
  have hIs := hI.stack
  rw [stackLo_vso, vso_stack] at hIs
  have hIf := hI.free
  simp only [Outside] at hIf
  have hF := ha.head.facts
  refine gluedKeep hpre ha.head (frHG hpre ha hf) (fun y h1 h2 hx ↦ ?_) (fun y h1 h2 h3 hx ↦ ?_)
  · rcases hx with hx | hx | hx | hx | hx | hx
    · addr_omega [hx, h1, h2, hb]
    · addr_omega [hx, h1, h2, hb]
    · addr_omega [hx, h1, h2, hb, hS, hIs]
    · addr_omega [hx, h1, h2, hb, hnx]
    · have := hf.heap.hi; simp only [heapEnd] at this; addr_omega [hx.2, h1, h2, hb, this]
    · have := hF.F
      rcases this with h0 | h0
      · simp only [Within] at hx; omega
      · have := hF.hend; simp only [heapEnd] at this; addr_omega [hx, h0, h1, h2, hb, this]
  · have hhe := hF.hend
    simp only [heapEnd] at hhe
    rcases hx with hx | hx | hx | hx | hx | hx
    · addr_omega [hx, h2, hb, hhe]
    · addr_omega [hx, h2, hb, hhe]
    · rcases hIf.1 with h0 | h0
      · addr_omega [hx, hS, h0, h1, hF.hs]
      · addr_omega [hx, hS, h0, h2, hhe]
    · addr_omega [hx, h2, hhe]
    · omega
    · exact h3 hx

/-- Every byte the glue reads is new since the fold rounds' end, or a head's glued claim's. -/
theorem readsClass {s : MachineState} {x : LCtx} {h t u w r g : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf qq res q : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (ha : AtR s x h t u w r ℓ Wl lf qq res pend d qs) (hf : Fronted s r g q)
    (y : Word) (hy : GlueReads s g y) :
    (heapNext t ≤ y.toNat ∧ y.toNat < heapNext g) ∨
      ∃ i < (vecLen h (s.getReg .x2 - 664)).toNat, InBufs h (gAddr h s i) y := by
  have hb := bounds hpre
  have hP := ha.pnd
  have hhr := ha.heap.hi
  have hhg := hf.heap.hi
  have hmo := hf.mono
  have hrt : heapNext t ≤ heapNext r := le_trans ha.tu (le_trans ha.uw ha.wr)
  obtain ⟨hgv, hgs⟩ := hf.vec
  have hglc := hgv.len
  have hraw := hP.vec.raw
  simp only [RawVecOk, Buf] at hraw
  obtain ⟨Pr, hPr⟩ : ∃ Pr, vecPtr r (s.getReg .x2 - 616) = Pr := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, (vecLen r (s.getReg .x2 - 616)).toNat = n := ⟨_, rfl⟩
  have hn1 : (vecLen g (s.getReg .x2 - 616)).toNat = n + 1 := by
    rw [hf.len, BitVec.toNat_add, hn]
    have hlc := hP.vec.len
    have : n < 2 ^ 63 := by
      rcases hraw.2 with h0 | h0
      · omega
      · simp only [heapEnd] at hhr; omega
    simp only [show (1 : Word).toNat = 1 from rfl]; omega
  have hold (o : ℕ) (ho : o % 8 = 0) (hoN : o + 8 ≤ 80 * n) :
      g.getMem (vecPtr g (s.getReg .x2 - 616) + BitVec.ofNat 64 o) =
        r.getMem (Pr + BitVec.ofNat 64 o) := by
    rw [← hPr]; exact hf.old o ho (by rw [hn]; exact hoN)
  have newR (h1 : heapNext r ≤ y.toNat) (h2 : y.toNat < heapNext g) :
      (heapNext t ≤ y.toNat ∧ y.toNat < heapNext g) ∨
        ∃ i < (vecLen h (s.getReg .x2 - 664)).toNat, InBufs h (gAddr h s i) y :=
    Or.inl ⟨by omega, h2⟩
  have oldR (hpb : PBufs r (s.getReg .x2 - 616) y) :
      (heapNext t ≤ y.toNat ∧ y.toNat < heapNext g) ∨
        ∃ i < (vecLen h (s.getReg .x2 - 664)).toNat, InBufs h (gAddr h s i) y := by
    have := hP.fresh y hpb; exact Or.inl ⟨this.1, by omega⟩
  rcases hy with hy | ⟨i, hi, hy⟩ | ⟨i, hi, hy⟩
  · -- the pending claims' buffer
    rcases hf.pnew with ⟨e1, e2⟩ | hnew
    · refine oldR (Or.inl ?_)
      rw [e1] at hy
      have := hgv.len
      rw [e2] at this
      simp only [Within] at hy ⊢; omega
    · simp only [NewBuf] at hnew
      rcases hnew.2 with h0 | h0
      · simp only [Within] at hy; omega
      · exact newR (by simp only [Within] at hy; omega) (by simp only [Within] at hy; omega)
  · rw [hn1] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · -- an opening's claim, copied
      have hin : i < (vecLen r (s.getReg .x2 - 616)).toNat := by rw [hn]; exact hi
      have hWE : WordsEq g (pAddr g s i) r (Pr + BitVec.ofNat 64 (80 * i)) 10 := fun k hk ↦ by
        simp only [pAddr]
        rw [addOfNat, addOfNat, hold _ (by omega) (by omega)]
      have hWE24 : WordsEq g (pAddr g s i + 24) r (Pr + BitVec.ofNat 64 (80 * i) + 24) 7 :=
        fun k hk ↦ by
          have := hWE (k + 3) (by omega)
          rw [show (24 : Word) = BitVec.ofNat 64 24 from rfl, addOfNat, addOfNat]
          simp only [pAddr] at this ⊢
          rw [addOfNat, addOfNat] at this ⊢
          rw [show 80 * i + (24 + 8 * k) = 80 * i + 8 * (k + 3) by ring]
          exact this
      rcases hy with hy | hy
      · have e8 : vecPtr g (pAddr g s i) = vecPtr r (Pr + BitVec.ofNat 64 (80 * i)) :=
          hWE.get 1 (by omega) 8 (by decide)
        have e16 : vecLen g (pAddr g s i) = vecLen r (Pr + BitVec.ofNat 64 (80 * i)) :=
          hWE.get 2 (by omega) 16 (by decide)
        rw [e8, e16] at hy
        have hI := hP.intro i hin
        rw [hPr] at hI
        have hl := hI.len
        refine oldR (Or.inr ⟨i, hin, Or.inl ?_⟩)
        rw [hPr]; simp only [Within] at hy ⊢; omega
      · rw [InBufs_congr (hWE24.ptrs (by omega))] at hy
        exact oldR (Or.inr ⟨i, hin, Or.inr (by rw [hPr]; exact hy)⟩)
    · -- the intro message's claim
      rw [← hn] at hy
      rcases hy with hy | hy
      · obtain ⟨hiv, -, hinb⟩ := hf.intro
        have hl := hiv.len
        simp only [NewBuf] at hinb
        rcases hinb.2 with h0 | h0
        · simp only [Within] at hy; omega
        · exact newR (by simp only [Within] at hy; omega) (by simp only [Within] at hy; omega)
      · have hqlen : qs.length < 2 ^ 32 := by
          rcases ha.qbuf.2.2 with h0 | h0
          · omega
          · simp only [heapEnd] at hhr; have := ha.wr; omega
        have h24 : g.getMem (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat + 24) ≠
            0xffffffffffffffff := by
          rw [hf.w24, ha.m1000]
          intro he
          have := congrArg BitVec.toNat he
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          exact absurd this (by
            rw [show (0xffffffffffffffff : Word).toNat = 2 ^ 64 - 1 from rfl]; omega)
        rw [InBufs, ite_eq_right_of_eq_false _ _ (eq_false h24)] at hy
        have w32 := hf.w32
        have w40 := hf.w40
        have w56 := hf.w56
        have w64 := hf.w64
        generalize pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat = e at w32 w40 w56 w64 hy
        simp only [vecPtr, vecLen] at hy
        rw [show e + 24 + 8 = e + 32 by rw [BitVec.add_assoc]; rfl,
          show e + 24 + 16 = e + 40 by rw [BitVec.add_assoc]; rfl,
          show e + 24 + 24 + 8 = e + 56 by
              rw [BitVec.add_assoc, BitVec.add_assoc]; rfl,
          show e + 24 + 24 + 16 = e + 64 by
              rw [BitVec.add_assoc, BitVec.add_assoc]; rfl,
          w32, w40, w56, w64, ha.x26] at hy
        obtain ⟨-, -, hqb⟩ := ha.qbuf
        obtain ⟨hpwv, -, hpwl, hpwb⟩ := ha.pw
        have hwg : heapNext w ≤ heapNext g := le_trans ha.wr hmo
        rcases hy with hy | hy
        · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hy
          rcases hqb with h0 | h0
          · simp only [Within] at hy; omega
          · refine Or.inl ⟨?_, ?_⟩ <;> simp only [Within] at hy <;> have := ha.tu <;> omega
        · have hpl := hpwv.len
          rw [show s.getReg .x2 - 480 = s.getReg .x2 - 488 + 8 by rv_eval [],
            show s.getReg .x2 - 472 = s.getReg .x2 - 488 + 16 by rv_eval []] at hy
          rcases hpwb with h0 | h0
          · simp only [vecLen] at h0; simp only [Within] at hy; omega
          · refine Or.inl ⟨?_, ?_⟩ <;> simp only [Within, vecPtr, vecLen] at hy h0 hpl <;>
              have := ha.tu <;> omega
  · -- a head's glued claim
    obtain ⟨-, -, el, -, hib⟩ := gluedG hpre ha hf
    rw [el] at hi
    exact Or.inr ⟨i, hi, ((hib i hi).1 y).mp hy⟩

/-- **Into the glue**: `GlueIn` from the rows' end and the push. -/
theorem glueIn {s : MachineState} {x : LCtx} {h t u w r g : MachineState} {ℓ : ℕ}
    {Wl : Model.Pcs.WhirLocals} {lf qq res q : List E}
    {pend : List (List E × Model.Pcs.GluedWeightRust)} {d : Digest} {qs : List Word}
    (hpre : VsoPre s) (ha : AtR s x h t u w r ℓ Wl lf qq res pend d qs) (hf : Fronted s r g q) :
    GlueIn s g (eAt w (s.getReg .x2 - 384)) (Model.Pcs.foldSt Wl lf qq).1
      (pend ++ [(q, Model.Pcs.GluedWeightRust.queries (mlOf s Wl lf) qs
        (Verifier.powers (eAt w (s.getReg .x2 - 384)) qs.length))]) := by
  have hb := bounds hpre
  have hhr := ha.heap.hi
  have hhg := hf.heap.hi
  have hmo := hf.mono
  have hF := ha.head.facts
  have hsl := hpre.heap.lo
  have hP := ha.pnd
  have hrt : heapNext t ≤ heapNext r := le_trans ha.tu (le_trans ha.uw ha.wr)
  have hst : heapNext s ≤ heapNext t := le_trans hF.hs (le_trans hF.hL ha.ht)
  obtain ⟨hgv, hgs⟩ := hf.vec
  obtain ⟨ec, ep, el, hgl, -⟩ := gluedG hpre ha hf
  obtain ⟨hhv, -, hhlo⟩ := ha.head.glued
  have hhraw := hhv.raw
  simp only [RawVecOk, Buf] at hhraw
  have hfQ := ha.fo.Q
  obtain ⟨q896, q23, -, qel⟩ := ha.quad
  -- the head's quadratic
  have hhq := ha.head.quad
  have hhap := ha.head.apart
  have hfroz := ha.head.frozen
  -- reads at `g` from the slots `r` had
  have kg (y : Word) (hy : (s.getReg .x2 - 1040).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 904).toNat ∨ (s.getReg .x2 - 896).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 616).toNat ∨ (s.getReg .x2 - 592).toNat ≤ y.toNat ∧
      y.toNat + 8 ≤ (s.getReg .x2 - 512).toNat) : g.getMem y = r.getMem y :=
    hf.fr y fun i hi hw ↦ by
      have hI := hpre.self
      have hS := Region.bounds hI.ok.self
      have hIs := hI.stack
      rw [stackLo_vso, vso_stack] at hIs
      obtain ⟨hnx, -⟩ := sfacts hpre
      rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw <;>
        first
        | (rcases hy with hy | hy | hy <;> addr_omega [hw, hi, hy, hb])
        | (rcases hy with hy | hy | hy <;> addr_omega [hw, hi, hy, hb, hS, hIs])
        | (rcases hy with hy | hy | hy <;> addr_omega [hw, hi, hy, hb, hnx])
        | (have hraw := hP.vec.raw
           simp only [RawVecOk, Buf] at hraw
           rcases hraw.2 with h0 | h0
           · simp only [Within] at hw; omega
           · simp only [heapEnd] at hhr; rcases hy with hy | hy | hy <;> addr_omega [hw, hi, hy, hb, h0, hhr])
        | (simp only [Fresh] at hw; rcases hy with hy | hy | hy <;> addr_omega [hw.2, hi, hy, hb, hhg])
  have hlenF : (vecEs r (s.getReg .x2 - 688)).length = (Wl.folds ++ lf).length := by
    rw [ha.folds.2.1]
  have hQb : (t.getReg .x23).toNat = 0 ∨ heapNext s ≤ (t.getReg .x22).toNat ∧
      (t.getReg .x22).toNat + 24 * (t.getReg .x23).toNat ≤ heapNext t := by
    rcases hfQ.2.2 with ⟨e1, e2⟩ | h0 | h0
    · rw [e1, e2]
      rcases hhq.2.2 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨by have := hF.hs; omega, by have := ha.ht; omega⟩
    · exact Or.inl h0
    · exact Or.inr ⟨by have := hF.hs; have := hF.hL; omega, h0.2⟩
  refine {
    pc := hf.pc
    sp := hf.sp
    inv := hf.inv
    heap := hf.heap
    x18 := hf.x18
    x22 := hf.x22
    npos := by simp
    pnd := pendG hpre ha hf
    pbuf := by
      have hlg := lenG ha hf
      have hlc := hgv.len
      refine ⟨hgs.1, ?_⟩
      rcases hgs.2 with h0 | h0
      · omega
      · exact ⟨by omega, by omega⟩
    intro := fun i hi ↦ by
      rw [lenG ha hf] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · have hI : VecOk r (pAddr r s i) 24 8 := hP.intro i hi
        have hWE : WordsEq g (pAddr g s i) r (pAddr r s i) 3 := fun k hk ↦ by
          simp only [pAddr]
          rw [addOfNat, addOfNat]
          exact hf.old _ (by omega) (by omega)
        have e0 : vecCap g (pAddr g s i) = vecCap r (pAddr r s i) := hWE.zero (by omega)
        have e8 : vecPtr g (pAddr g s i) = vecPtr r (pAddr r s i) :=
          hWE.get 1 (by omega) 8 (by decide)
        have e16 : vecLen g (pAddr g s i) = vecLen r (pAddr r s i) :=
          hWE.get 2 (by omega) 16 (by decide)
        have hraw := hI.raw
        simp only [RawVecOk, Buf] at hraw ⊢
        refine ⟨?_, by rw [e0, e16]; exact hI.len⟩
        simp only [RawVecOk, Buf]
        rw [e0, e8]
        exact ⟨hraw.1, hraw.2.imp id fun h ↦ ⟨h.1, by have := hmo; simp only [heapNext] at *; omega⟩⟩
      · exact hf.intro.1
    quad := by
      rw [kg _ (Or.inr (Or.inl (by addr_omega [hb]))), q896, hf.regs .x23 (by decide), q23]
      refine ⟨?_, hfQ.2.1, ?_⟩
      · rw [← qel]
        refine hf.fr.eListAt fun i hi ↦ ?_
        rcases hQb with h0 | h0
        · omega
        · have hy : (t.getReg .x22 + BitVec.ofNat 64 i).toNat = (t.getReg .x22).toNat + i := by
            simp only [heapEnd] at hhr; addr_omega [h0, hi, hrt, hhr]
          refine notFrW hpre ha.heap (by omega) (by omega) fun hw ↦ ?_
          have := hP.fresh _ (Or.inl hw)
          omega
      · rcases hQb with h0 | h0
        · exact Or.inl h0
        · exact Or.inr ⟨h0.1, by omega⟩
    folds := by
      rw [kg _ (Or.inr (Or.inl (by addr_omega [hb])))]
      show r.getMem (s.getReg .x2 - 672) = BitVec.ofNat 64 (Wl.folds ++ lf).length
      rw [show s.getReg .x2 - 672 = s.getReg .x2 - 688 + 16 by rv_eval []]
      apply ofNat_toNat_eq
      rw [← hlenF]
      simp [vecEs, eListAt_length, vecLen]
    flen := by
      show (Wl.folds ++ lf).length < 2 ^ 64
      rw [← hlenF]; simp only [vecEs, eListAt_length]; exact BitVec.isLt _
    lam := by
      rw [kg _ (Or.inl (by addr_omega [hb])), kg _ (Or.inl (by addr_omega [hb])),
        kg _ (Or.inl (by addr_omega [hb]))]
      exact ha.lam
    one := hf.one
    glued := by
      refine ⟨⟨?_, by rw [el, ec]; exact hhv.len⟩, hgl, ?_⟩
      · simp only [RawVecOk, Buf]
        rw [ec, ep]
        exact ⟨hhraw.1, hhraw.2.imp id fun h ↦ ⟨h.1, by have := ha.ht; omega⟩⟩
      · rw [ec, ep]
        rcases hhlo with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (by have := hF.hs; omega)
    apart := by
      rw [kg _ (Or.inr (Or.inl (by addr_omega [hb]))), q896, hf.regs .x23 (by decide), q23, ec, ep]
      simp only [Apart]
      rcases hfQ.2.2 with ⟨e1, e2⟩ | h0 | h0
      · rw [e1, e2]; have := hhap.2.2; simp only [Apart] at this; omega
      · omega
      · rcases hhraw.2 with h1 | h1
        · omega
        · omega
    reads := fun y hy ↦ by
      have hsy : heapNext s ≤ heapNext t := hst
      rcases readsClass hpre ha hf y hy with ⟨h1, h2⟩ | ⟨i, hi, hib⟩
      · rw [kg _ (Or.inr (Or.inl (by addr_omega [hb]))), q896, hf.regs .x23 (by decide), q23, ep,
          ec]
        refine ⟨by omega, h2, fun hw ↦ ?_, fun hw ↦ ?_⟩
        · simp only [Within] at hw
          rcases hQb with h0 | h0 <;> omega
        · simp only [Within] at hw
          rcases hhraw.2 with h0 | h0
          · omega
          · have := ha.ht; omega
      · obtain ⟨f1, f2, f3, f4, f5⟩ := hfroz i hi y hib
        rw [kg _ (Or.inr (Or.inl (by addr_omega [hb]))), q896, hf.regs .x23 (by decide), q23, ep,
          ec]
        refine ⟨by have := hF.hs; omega, by have := ha.ht; omega, fun hw ↦ ?_, f4⟩
        rcases hfQ.2.2 with ⟨e1, e2⟩ | h0 | h0
        · rw [e1, e2] at hw; exact f5 hw
        · simp only [Within] at hw; omega
        · simp only [Within] at hw; omega
    galigned := fun i hi ↦ by
      obtain ⟨-, -, el', -, hib⟩ := gluedG hpre ha hf
      rw [el'] at hi
      exact ((hib i hi).2).mpr (ha.head.aligned i hi)
    paligned := fun i hi ↦ by
      rw [lenG ha hf] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · have hO := hP.ood i hi
        have hOr := hO.2.raw
        have hWE : WordsEq g (pAddr g s i + 24) r (pAddr r s i + 24) 3 := fun k hk ↦ by
          simp only [pAddr]
          rw [show (24 : Word) = BitVec.ofNat 64 24 from rfl, addOfNat, addOfNat, addOfNat, addOfNat]
          exact hf.old _ (by omega) (by omega)
        unfold WeightAligned
        have e0 : g.getMem (pAddr g s i + 24) = r.getMem (pAddr r s i + 24) := hWE.zero (by omega)
        have e16 : vecPtr g (pAddr g s i + 24 + 8) = vecPtr r (pAddr r s i + 24 + 8) := by
          show g.getMem (pAddr g s i + 24 + 8 + 8) = r.getMem (pAddr r s i + 24 + 8 + 8)
          rw [BitVec.add_assoc (pAddr g s i + 24), BitVec.add_assoc (pAddr r s i + 24)]
          exact hWE.get 2 (by omega) (8 + 8) (by decide)
        have hO1 : r.getMem (pAddr r s i + 24) = 0xffffffffffffffff := hO.1
        rw [e0, ite_eq_left_of_eq_true _ _ (eq_true hO1), e16]
        exact hOr.1
      · have h24 := hf.w24
        rw [ha.m1000] at h24
        have hqlen : qs.length < 2 ^ 32 := by
          rcases ha.qbuf.2.2 with h0 | h0
          · omega
          · simp only [heapEnd] at hhr; have := ha.wr; omega
        have hne : g.getMem (pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat + 24) ≠
            0xffffffffffffffff := by
          rw [h24]; intro he
          have := congrArg BitVec.toNat he
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
          exact absurd this (by rw [show (0xffffffffffffffff : Word).toNat = 2 ^ 64 - 1 from rfl]; omega)
        have w32 := hf.w32
        have w56 := hf.w56
        generalize pAddr g s (vecLen r (s.getReg .x2 - 616)).toNat = e at hne w32 w56 ⊢
        unfold WeightAligned
        rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]
        simp only [vecPtr]
        rw [show e + 24 + 8 = e + 32 by rw [BitVec.add_assoc]; rfl,
          show e + 24 + 24 + 8 = e + 56 by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl, w32, w56]
        refine ⟨ha.qbuf.2.1, ?_⟩
        have := ha.pw.1.raw.1
        simpa only [vecPtr, show s.getReg .x2 - 488 + 8 = s.getReg .x2 - 480 by rv_eval []] using this }

end Rv64Verifier.Proofs.Pcs.Vso
