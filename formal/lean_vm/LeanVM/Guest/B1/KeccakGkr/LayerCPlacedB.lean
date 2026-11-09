/-
  LeanVM.Guest.B1.KeccakGkr.LayerCPlacedB

  **`keccak_layer` is complete, placed, within a bound** (`CompleteAtFB`), for its two
  specializations: its frame, its buffers and its callees' words.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCPlaced
public import LeanVM.Guest.B1.KeccakGkr.FlatFB
public import LeanVM.Guest.Memory.LoopPre

/-!
# `keccak_layer`, complete and placed within a bound

`layer_completeAtFB` is `layer_completeAtF` with the size of the layer's run bounded before the
memory, by

  `layerWords fs first y KP KR = fs (layerName first) + (y + 171)
    + (fs (packLoopName first) + ⌊y/8⌋ * KP) + (fs (remLoopName first) + (y % 8) * KR)`:

the layer's frame; its buffers (`allocDyn` of `y` words for the pack challenges, then 128 for the
round records, 11 for the local point, 25 for the next claim's lanes and 7 for its flips); the
eight-round pack loop's call (`⌊y/8⌋` iterations of at most `KP` words each and its run's one
phantom frame `fs (packLoopName first)` when it is entered, that frame alone when it is skipped,
which is when `y < 8`); the remainder loop's likewise (`y % 8` iterations of at most `KR` words and
its frame, its frame alone when `8 ∣ y`).

The hypotheses on the callees are fs-generic: each loop's run's words, per iteration and its one
phantom frame (`TotalLeOn … LoopPre`, the form of `Count.wSKt_totalLeOn`). The proof is `layer_completeAtF`'s
with `completeAt_flatOutFB`, the pure callees placed within their bounds by
`completeAtDTB_of_relIn`, the honest valuation `layer_obl`.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Lift LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.Protocol.KeccakGkr

@[expose] public section

/-- **`keccak_layer`'s words**: its frame, its buffers (`y + 128 + 11 + 25 + 7`), the eight-round
pack loop's (its frame and `⌊y/8⌋` iterations of at most `KP` words) and the remainder loop's (its
frame and `y % 8` iterations of at most `KR` words). -/
def layerWords (fs : String → ℕ) (first y KP KR : ℕ) : ℕ :=
  fs (layerName first) + (y + 171) + (fs (packLoopName first) + y / 8 * KP) +
    (fs (remLoopName first) + y % 8 * KR)

theorem packLoopName_ne_rem (first : ℕ) : packLoopName first ≠ remLoopName first := by
  unfold packLoopName remLoopName; split <;> decide

/-- The callees' bounds: the pack loop's run (its iterations and its one phantom frame), the
remainder loop's. -/
def layerKidBd (fs : String → ℕ) (first y KP KR : ℕ) (k : Kid) : ℕ :=
  if k.f = packLoopName first then y / 8 * KP + fs (packLoopName first)
  else y % 8 * KR + fs (remLoopName first)

/-- The words of the layer's callees, an entered one's bound, a skipped one's frame. -/
theorem layerKids_bound (fs : String → ℕ) (D : LayerData) (first : ℕ)
    (CL : ClaimLay) (bcur bout b KP KR : ℕ) :
    kidsBound fs (layerKidBd fs first D.y KP KR) (layerKids D first CL bcur bout b) ≤
      fs (packLoopName first) + D.y / 8 * KP + (fs (remLoopName first) + D.y % 8 * KR) := by
  have hne := packLoopName_ne_rem first
  simp only [kidsBound, layerKids, layerKidBd, hne.symm, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, ↓reduceIte]
  split_ifs <;> omega

theorem lt_of_taken {m : ℕ} (h : decide (1 + gen ^ m ≠ 0) = true) : 0 < m := by
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0
    exact absurd (e_add_eq_zero_iff.mpr (pow_zero gen).symm) (by simpa using h)
  · exact h0

variable {fs : String → ℕ} {cert : String → V → ℕ}

set_option maxRecDepth 20000 in
/-- **`keccak_layer` is complete, placed, within `layerWords fs first D.y KP KR` words**, for
its two specializations: `layer_completeAtF` with the pack loop's run at most `KP` words per
iteration and its frame, the remainder loop's at most `KR` and its frame. -/
theorem layer_completeAtFB {first : ℕ} (hf : first < 2) (κ : ℕ) (D : LayerData)
    (CL : ClaimLay) (bcur bout : ℕ) {p0 p1 iota : E} {KP KR : ℕ}
    (hP : TotalLeOn coreProgram fs (packLoopName first) LoopPre
      fun a ↦ logG (a.getD 1 0) * KP + fs (packLoopName first))
    (hR : TotalLeOn coreProgram fs (remLoopName first) LoopPre
      fun a ↦ logG (a.getD 1 0) * KR + fs (remLoopName first))
    (hcl : D.cap.length = 5) (hcap : AllCanonical D.cap)
    (hw : first = 1 → (p0, p1) = Keccak.scalarCells D.w0 dsObserve)
    (hy1 : 1 ≤ D.y) (hy30 : D.y ≤ 30) (hpl : D.product.length = 47)
    (hpm : D.packMsgs.length = D.y) (hlm : D.localMsgs.length = 11)
    (hproj : projectedOf D.c D.product + iota * sumE D.c.mu = D.c.value)
    (hfin : LayerFinal D.c (D.s0 first) D.product D.packMsgs D.localMsgs D.t)
    (hCL : CL.Ok first D.c D.y) :
    CompleteAtFB fs cert κ (layerName first)
      (fun fp ↦ layerLin D first CL bcur bout (fp + fs (layerName first)))
      (D.cap ++ [p0, p1, ptr bcur, gen ^ D.y, gen ^ (D.y / 8), gen ^ (D.y % 8), ptr CL.bclaim,
        ptr bout, iota])
      (fun fp rets Lout ↦ rets = D.rets first (ptr bcur) ∧
        Lout = layerBufs D first (ptr bcur) (fp + fs (layerName first)))
      (layerWords fs first D.y KP KR) := by
  obtain ⟨fn, hfind, hbody, hparams⟩ := layer_fn hf
  obtain ⟨hflat, haddrs, -, -, -, -⟩ := layerPre_kernel hf
  have hlocL : (D.locPt first).length = 11 := by
    rw [LayerData.locPt, LayerData.loc, layerLocal, localRunF_length, hlm]
  have hne := packLoopName_ne_rem first
  refine CompleteAtFB.mono_bound ?_ (show fs (layerName first) + (layerSizes D).sum +
      (fs (packLoopName first) + D.y / 8 * KP + (fs (remLoopName first) + D.y % 8 * KR)) ≤
        layerWords fs first D.y KP KR by
    simp only [layerSizes, layerWords, List.sum_cons, List.sum_nil]; omega)
  refine completeAt_flatOutFB (fs := fs) (cert := cert) hfind (layer_loop hf) κ _ _
    (fun _ ↦ D.rets first (ptr bcur)) _ (hbody.trans (layerT_pre first)) hflat haddrs
    (layerPre_noLoadIte hf)
    (layerSizes D) (fun _ ↦ layerOwn D first (ptr bcur)) (fun _ ↦ ?_) (fun _ ↦ ⟨rfl, rfl⟩)
    (fun fp ↦ layerKids D first CL bcur bout (fp + fs (layerName first)))
    (layerKidBd fs first D.y KP KR)
    (fs (packLoopName first) + D.y / 8 * KP + (fs (remLoopName first) + D.y % 8 * KR)) ?_
    (fun fp ↦ layerKids_bound fs D first CL bcur bout _ KP KR) ?_ ?_ ?_
  · -- the buffers' words fit
    simp only [layerOwn, layerSizes, List.forall₂_cons, List.Forall₂.nil, and_true]
    refine ⟨by rw [LayerData.chs_length hpm], by rw [recWords_length], by rw [hlocL],
      by rw [lanesOut_length], by simp [flipsOf]⟩
  · -- the callees, placed within their bounds
    intro fp k hk ht
    simp only [layerKids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · have hne1 : 1 + gen ^ (D.y / 8) ≠ 0 := by simpa using ht
      have hm0 : 0 < D.y / 8 := lt_of_taken ht
      simp only [layerKidBd, ↓reduceIte]
      refine CompleteAtDTB.toCompleteAtB (completeAtDTB_of_relIn
        layerKidS_pure (packLoopName_mem first) (fun rd t rets' hn hv hb ↦ ?_)
        fun rd _ hm ↦ (layer_kids hf D CL bcur bout _ hy30 hpl hpm hlm hm).1 hne1)
      have h1 := hP rd t _ rets' hn (loopPre_gen hm0 (by omega) _) hv hb
      simp only [List.getD_cons_succ, List.getD_cons_zero] at h1
      rwa [gen_pow_eq_ofK, logG_spec (by omega)] at h1
    · have hne1 : 1 + gen ^ (D.y % 8) ≠ 0 := by simpa using ht
      have hm0 : 0 < D.y % 8 := lt_of_taken ht
      simp only [layerKidBd, hne.symm, ↓reduceIte]
      refine CompleteAtDTB.toCompleteAtB (completeAtDTB_of_relIn
        layerKidS_pure (remLoopName_mem first) (fun rd t rets' hn hv hb ↦ ?_)
        fun rd _ hm ↦ (layer_kids hf D CL bcur bout _ hy30 hpl hpm hlm hm).2 hne1)
      have h1 := hR rd t _ rets' hn (loopPre_gen hm0 (by omega) _) hv hb
      simp only [List.getD_cons_succ, List.getD_cons_zero] at h1
      rwa [gen_pow_eq_ofK, logG_spec (by omega)] at h1
  · intro fp k hk _ i hi
    rw [layerKids_lin k hk] at hi
    obtain ⟨q, hq, h1, h2⟩ := hi
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl ⟨q, hq, h1, h2⟩
    · exact Or.inr ⟨q, hq, h1, h2⟩
  · intro fp rd hB hLin k hk
    rw [layerKids_lin k hk]
    exact Main.memL_append.mpr ⟨hLin, hB⟩
  · -- the honest valuation
    intro fp outs hout rd _ hB hLin
    rw [hparams, hbody]
    exact layer_obl hf D CL bcur bout hcl hcap hw hy1 hy30 hpl hpm hlm hproj hfin hCL _ outs hout rd
      hB hLin

end
end LeanVM.Guest.B1.VerifySub
