/-
  LeanVM.Guest.B1.KeccakGkr.LayerCPlacedBE

  `keccak_layer` complete, placed, within a bound, by a tree exact at every node.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCPlacedB
public import LeanVM.Guest.B1.KeccakGkr.FlatE
public import LeanVM.Guest.B1.Exact.VkExact
public import LeanVM.Guest.Exact.FreeVk

/-!
# `keccak_layer`, exact

`layer_completeAtFBE`: `layer_completeAtFB` by a tree exact at every node (`completeAt_flatOutFBE`): the layer's paths
exact (`layer_pathExact`), `grind_check__L3` by `grind_check_completeDTBR`, the two loops exact for free.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Lift LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Main (MemL RegionL)
open LeanVM.Protocol.KeccakGkr

@[expose] public section

theorem packLoop_exactOk (first : ℕ) : ExactOk (packLoopName first) := by
  unfold packLoopName
  split
  · exact .free layer1_loop0_exactFree
  · exact .free layer0_loop0_exactFree

theorem remLoop_exactOk (first : ℕ) : ExactOk (remLoopName first) := by
  unfold remLoopName
  split
  · exact .free layer1_loop1_exactFree
  · exact .free layer0_loop1_exactFree

variable {fs : String → ℕ} {cert : String → V → ℕ}

set_option maxRecDepth 20000 in
/-- **`layer_completeAtFB` by a tree exact at every node.** -/
theorem layer_completeAtFBE {first : ℕ} (hf : first < 2) {κ : ℕ} (hκ : 11 ≤ κ) (D : LayerData)
    (CL : ClaimLay) (bcur bout tbE : ℕ) {p0 p1 iota st : E} {KP KR : ℕ}
    (hP : TotalLeOn coreProgram fs (packLoopName first) LoopPre
      fun a ↦ logG (a.getD 1 0) * KP + fs (packLoopName first))
    (hR : TotalLeOn coreProgram fs (remLoopName first) LoopPre
      fun a ↦ logG (a.getD 1 0) * KR + fs (remLoopName first))
    (hcl : D.cap.length = 5)
    (hw : first = 1 → (p0, p1) = Keccak.scalarCells D.w0 dsObserve)
    (hy1 : 1 ≤ D.y) (hy30 : D.y ≤ 30) (hpl : D.product.length = 47)
    (hpm : D.packMsgs.length = D.y) (hlm : D.localMsgs.length = 11)
    (hproj : projectedOf D.c D.product + iota * sumE D.c.mu = D.c.value)
    (hgrind : ((D.s0 first).absorbAll D.product dsObserve).GrindOk sGrindBits D.nonce)
    (hfin : LayerFinal D.c (D.s0 first) D.product D.nonce D.packMsgs D.localMsgs D.t)
    (hCL : CL.Ok first D.c D.y) :
    CompleteAtFBT fs cert κ (layerName first)
      (fun fp ↦ layerLin D first CL bcur bout tbE (fp + fs (layerName first)))
      (D.cap ++ [p0, p1, ptr bcur, gen ^ D.y, gen ^ (D.y / 8), gen ^ (D.y % 8), ptr CL.bclaim,
        ptr bout, iota, ptr tbE, st])
      (fun fp rets Lout ↦ rets = D.rets first (ptr bcur) ∧
        Lout = layerBufs D first (ptr bcur) (fp + fs (layerName first)))
      exT (layerWords fs first D.y KP KR) := by
  obtain ⟨fn, hfind, hbody, hparams⟩ := layer_fn hf
  obtain ⟨hflat, haddrs, -, -, -, -⟩ := layerPre_kernel hf
  have hlocL : (D.locPt first).length = 11 := by
    rw [LayerData.locPt, LayerData.loc, layerLocal, localRunF_length, hlm]
  have hne := packLoopName_ne_rem first
  obtain ⟨hg1, hg2⟩ := grind_ne_loops first
  refine CompleteAtFBT.mono_bound ?_ (show fs (layerName first) + (layerSizes D).sum +
      (fs (grindCheckName 3) + (fs (packLoopName first) + D.y / 8 * KP +
        (fs (remLoopName first) + D.y % 8 * KR))) ≤
        layerWords fs first D.y KP KR by
    simp only [layerSizes, layerWords, List.sum_cons, List.sum_nil]; omega)
  refine completeAt_flatOutFBE (fs := fs) (cert := cert) hfind (layer_loop hf) (layer_pathExact hf hbody) κ _ _
    (fun _ ↦ D.rets first (ptr bcur)) _ (hbody.trans (layerT_pre first)) hflat haddrs
    (layerPre_noLoadIte hf)
    (layerSizes D) (fun _ ↦ layerOwn D first (ptr bcur)) (fun _ ↦ ?_) (fun _ ↦ ⟨rfl, rfl⟩)
    (fun fp ↦ layerKids D first CL bcur bout tbE (fp + fs (layerName first)))
    (layerKidBd fs first D.y KP KR)
    (fs (grindCheckName 3) + (fs (packLoopName first) + D.y / 8 * KP +
      (fs (remLoopName first) + D.y % 8 * KR))) ?_
    (fun fp ↦ layerKids_bound fs D first CL bcur bout tbE _ KP KR) ?_ ?_ ?_
  · -- the buffers' words fit
    simp only [layerOwn, layerSizes, List.forall₂_cons, List.Forall₂.nil, and_true]
    refine ⟨by rw [LayerData.chs_length hpm], by rw [recWords_length], by rw [hlocL],
      by rw [lanesOut_length], by simp [flipsOf]⟩
  · -- the callees, placed within their bounds
    intro fp k hk ht
    simp only [layerKids, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    · simp only [layerKidBd, ↓reduceIte]
      exact (grind_check_completeDTBR (bits := 3) (by decide) hκ
        fun _ _ hm ↦ ⟨rfl, D.gw first, ptr tbE, rfl,
          winTabs_of_memL hm (List.mem_append_left _ tabs_mem), LayerData.gw_pow hgrind⟩).mono le_rfl
        fun _ _ h ↦ h.2
    · have hne1 : 1 + gen ^ (D.y / 8) ≠ 0 := by simpa using ht
      have hm0 : 0 < D.y / 8 := lt_of_taken ht
      simp only [layerKidBd, hg1.symm, ↓reduceIte]
      refine (CompleteAtDTB.toCompleteAtB (completeAtDTB_of_relIn
        layerKidS_pure (packLoopName_mem first) (fun rd t rets' hn hv hb ↦ ?_)
        fun rd _ hm ↦ (layer_kids hf D CL bcur bout tbE _ hy30 hpl hpm hlm hm).1 hne1)).toDTBE
        (packLoop_exactOk first)
      have h1 := hP rd t _ rets' hn (loopPre_gen hm0 (by omega) _) hv hb
      simp only [List.getD_cons_succ, List.getD_cons_zero] at h1
      rwa [gen_pow_eq_ofK, logG_spec (by omega)] at h1
    · have hne1 : 1 + gen ^ (D.y % 8) ≠ 0 := by simpa using ht
      have hm0 : 0 < D.y % 8 := lt_of_taken ht
      simp only [layerKidBd, hne.symm, hg2.symm, ↓reduceIte]
      refine (CompleteAtDTB.toCompleteAtB (completeAtDTB_of_relIn
        layerKidS_pure (remLoopName_mem first) (fun rd t rets' hn hv hb ↦ ?_)
        fun rd _ hm ↦ (layer_kids hf D CL bcur bout tbE _ hy30 hpl hpm hlm hm).2 hne1)).toDTBE
        (remLoop_exactOk first)
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
    intro fp outs hout rd hlow hB hLin
    rw [hparams, hbody]
    exact layer_obl hf hκ D CL bcur bout tbE hcl hw hy1 hy30 hpl hpm hlm hproj hgrind hfin hCL _
      outs hout rd hlow hB hLin

end
end LeanVM.Guest.B1.VerifySub
