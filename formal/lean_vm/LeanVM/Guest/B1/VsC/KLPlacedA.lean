/-
  LeanVM.Guest.B1.VsC.KLPlacedA

  `keccak_layer` placed: its oracle, the values every memory's valuation takes, its own words and
  what they give its caller.
-/

module

public import LeanVM.Guest.B1.VsC.KLSplit
public import LeanVM.Guest.B1.VsC.KLayerA
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»

/-!
# A layer, placed: the oracle and the own words

At cursor `cb` the layer's `HeapBuf`s are the pack point (`y` words at `cb`), the local point
(`11` at `cb + y`), the next claim's lanes (`25` at `cb + y + 11`) and flips (`7` at `cb + y + 36`).
`layerW`: the oracle, those bases, the two dispatches' honest returns `r1`, `r2` and the inlined
`grind_check`'s honest windows. `layer_static`: what every memory's valuation takes there (the
oracle's words, and the words computed from the parameters only). `layerWo`: the own words, the
honest challenges, local point, lanes and flips; `layer_out`: a memory holding them and the next
claim's record at `out` holds the next claim (`ClaimRec`).
-/

namespace LeanVM.Guest.B1.VerifySub.KL

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr

@[expose] public section

/-- The word the inlined `grind_check` reads: the nonce's permutation's output `1`. -/
noncomputable def LayerData.gw (D : LayerData) (first : ℕ) : E :=
  cellsOfState (((D.s0 first).absorbAll D.product dsObserve).nonceState D.nonce) false
    ⟨1, by omega⟩

/-- **The oracle**: the `HeapBuf`s' bases from `cb`, the dispatches' returns, the windows. -/
noncomputable def layerW (D : LayerData) (first : ℕ) (cur : E) (cb : ℕ) (i : ℕ) : E :=
  if i = preOff first + 782 then VsC.ptrAtV cb
  else if i = preOff first + 810 then VsC.ptrAtV (cb + D.y)
  else if i = tW first + 25 then VsC.ptrAtV (cb + D.y + 11)
  else if i = topV (tW first) + 3 then VsC.ptrAtV (cb + D.y + 36)
  else if preOff first + 785 ≤ i ∧ i < preOff first + 792 then
    (D.r1 first cur).getD (i - (preOff first + 785)) 0
  else if preOff first + 798 ≤ i ∧ i < preOff first + 805 then
    (D.r2 first cur).getD (i - (preOff first + 798)) 0
  else gcWin 3 (D.gw first) (i - (preOff first + 544))

theorem layer_nums {first : ℕ} (hf : first < 2) :
    preOff first ≤ 20 ∧ preOff first + 810 < tW first + 25 ∧ tW first + 25 < topV (tW first) + 3 := by
  interval_cases first <;> exact ⟨by decide, by decide +kernel, by decide +kernel⟩

section
variable {D : LayerData} {first : ℕ} {cur : E} {cb : ℕ}

theorem layerW_vals (hf : first < 2) :
    layerW D first cur cb (preOff first + 782) = VsC.ptrAtV cb ∧
      layerW D first cur cb (preOff first + 810) = VsC.ptrAtV (cb + D.y) ∧
      layerW D first cur cb (tW first + 25) = VsC.ptrAtV (cb + D.y + 11) ∧
      layerW D first cur cb (topV (tW first) + 3) = VsC.ptrAtV (cb + D.y + 36) ∧
      (∀ k < 7, layerW D first cur cb (preOff first + 785 + k) = (D.r1 first cur).getD k 0) ∧
      (∀ k < 7, layerW D first cur cb (preOff first + 798 + k) = (D.r2 first cur).getD k 0) ∧
      ∀ j ≤ gcW 3, layerW D first cur cb (preOff first + 544 + j) = gcWin 3 (D.gw first) j := by
  obtain ⟨h0, h1, h2⟩ := layer_nums hf
  have hW : gcW 3 = 5 := by decide
  refine ⟨by simp [layerW], by simp [layerW], ?_, ?_, fun k hk ↦ ?_, fun k hk ↦ ?_, fun j hj ↦ ?_⟩
  · simp only [layerW, show ¬ (tW first + 25 = preOff first + 782) by omega,
      show ¬ (tW first + 25 = preOff first + 810) by omega, ↓reduceIte]
  · simp only [layerW, show ¬ (topV (tW first) + 3 = preOff first + 782) by omega,
      show ¬ (topV (tW first) + 3 = preOff first + 810) by omega,
      show ¬ (topV (tW first) + 3 = tW first + 25) by omega, ↓reduceIte]
  · simp only [layerW, show ¬ (preOff first + 785 + k = preOff first + 782) by omega,
      show ¬ (preOff first + 785 + k = preOff first + 810) by omega,
      show ¬ (preOff first + 785 + k = tW first + 25) by omega,
      show ¬ (preOff first + 785 + k = topV (tW first) + 3) by omega,
      show preOff first + 785 ≤ preOff first + 785 + k ∧ preOff first + 785 + k < preOff first + 792 by omega,
      and_self, ↓reduceIte, Nat.add_sub_cancel_left]
  · simp only [layerW, show ¬ (preOff first + 798 + k = preOff first + 782) by omega,
      show ¬ (preOff first + 798 + k = preOff first + 810) by omega,
      show ¬ (preOff first + 798 + k = tW first + 25) by omega,
      show ¬ (preOff first + 798 + k = topV (tW first) + 3) by omega,
      show ¬ (preOff first + 785 ≤ preOff first + 798 + k ∧ preOff first + 798 + k < preOff first + 792) by omega,
      show preOff first + 798 ≤ preOff first + 798 + k ∧ preOff first + 798 + k < preOff first + 805 by omega,
      and_self, ↓reduceIte, Nat.add_sub_cancel_left]
  · simp only [layerW, show ¬ (preOff first + 544 + j = preOff first + 782) by omega,
      show ¬ (preOff first + 544 + j = preOff first + 810) by omega,
      show ¬ (preOff first + 544 + j = tW first + 25) by omega,
      show ¬ (preOff first + 544 + j = topV (tW first) + 3) by omega,
      show ¬ (preOff first + 785 ≤ preOff first + 544 + j ∧ preOff first + 544 + j < preOff first + 792) by omega,
      show ¬ (preOff first + 798 ≤ preOff first + 544 + j ∧ preOff first + 544 + j < preOff first + 805) by omega,
      ↓reduceIte, Nat.add_sub_cancel_left]

end

/-- The layer's arguments. -/
def layerArgs (D : LayerData) (p0 p1 cur claim out iota tb : E) : List E :=
  D.cap ++ [p0, p1, cur, gen ^ D.y, gen ^ (D.y / krStep), gen ^ (D.y % krStep), claim, out, iota, tb]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- **What every memory's valuation takes**: the oracle's words and those computed from the
parameters only. -/
theorem layer_static {first : ℕ} (hf : first < 2) {D : LayerData} (hcl : D.cap.length = 5)
    {p0 p1 cur claim out iota tb : E} {cb : ℕ} (rd : Reader) :
    let σ := layerσ rd (layerW D first cur cb) (layerArgs D p0 p1 cur claim out iota tb) first
    σ (.n (valf% «keccak_layer» "cursor@1")) = cur ∧ σ (.n (valf% «keccak_layer» "y_g")) = gen ^ D.y ∧
      σ (.n (valf% «keccak_layer» "step_g")) = gen ^ (D.y / krStep) ∧
      σ (.n (valf% «keccak_layer» "rem_g")) = gen ^ (D.y % krStep) ∧
      σ (.n (valf% «keccak_layer» "claim")) = claim ∧ σ (.n (valf% «keccak_layer» "out")) = out ∧
      σ (.n (valf% «keccak_layer» "tabs")) = tb ∧
      σ (.n (preOff first + 782)) = VsC.ptrAtV cb ∧ σ (.n (preOff first + 784)) = cur * gen ^ 48 ∧
      (∀ k < 7, σ (.n (preOff first + 785 + k)) = (D.r1 first cur).getD k 0) ∧
      σ (.n (preOff first + 797)) = VsC.ptrAtV cb * gen ^ D.n1 ∧
      (∀ k < 7, σ (.n (preOff first + 798 + k)) = (D.r2 first cur).getD k 0) ∧
      σ (.n (preOff first + 810)) = VsC.ptrAtV (cb + D.y) ∧
      σ (.n (tW first + 25)) = VsC.ptrAtV (cb + D.y + 11) ∧
      σ (.n (topV (tW first) + 3)) = VsC.ptrAtV (cb + D.y + 36) := by
  intro σ'
  have hl : (layerArgs D p0 p1 cur claim out iota tb).length = 15 := by simp [layerArgs, hcl]
  have hG := layer_good (rd := rd) (w := layerW D first cur cb) hf hl
  have hpar := fun i (hi : i < 15) ↦ layer_param (rd := rd) (w := layerW D first cur cb) hf hl hi
  generalize hσ' : layerσ rd (layerW D first cur cb) (layerArgs D p0 p1 cur claim out iota tb) first = σ
    at hG hpar
  have eσ : σ' = σ := hσ'
  rw [eσ]
  clear eσ hσ'
  obtain ⟨f0, f1, f2, f3, f4, hcapE⟩ := five_of_length' hcl
  simp only [layerArgs, hcapE] at hpar
  obtain ⟨w782, w810, w25, wF, w785, w798, -⟩ := layerW_vals (D := D) (cur := cur) (cb := cb) hf
  have hP : ∀ s ∈ packT (preOff first), GoodS rd (layerSt first) (layerW D first cur cb) σ s :=
    fun s hs ↦ hG s (by rw [layerT_sections]; simp [hs])
  have hm : ∀ s, s ∈ packT (preOff first) → GoodS rd (layerSt first) (layerW D first cur cb) σ s := hP
  set o := preOff first with ho
  have e782 : σ (.n (o + 782)) = layerW D first cur cb (o + 782) :=
    hm (.atom (.hint (.allocDyn (.n (o + 782)) (.n (valf% «keccak_layer» "y_g"))))) (by simp [packT])
  have e783 : σ (.n (o + 783)) = word 281474976710656 0 :=
    hm (.atom (.const (.n (o + 783)) (word 281474976710656 0))) (by simp [packT])
  have e784 := mul_good (d := o + 784) (x := valf% «keccak_layer» "cursor@1") (y := o + 783)
    (by omega) (by omega) (hm _ (by simp [packT]))
  have r1 : ∀ v ∈ (List.range 7).map (fun k ↦ V.n (o + 785 + k)), σ v = layerW D first cur cb v.idx :=
    hm (.dispatch (.n (valf% «keccak_layer» "step_g")) stepNames
      ((cap5 (o + 539)) ++ [.n (o + 784), .n (o + 780), .n (o + 781), .n (o + 782),
        .n (valf% «keccak_layer» "tabs")]) ((List.range 7).map fun k ↦ .n (o + 785 + k)))
      (by simp [packT])
  have e792 := mul_good (d := o + 792) (x := valf% «keccak_layer» "step_g")
    (y := valf% «keccak_layer» "step_g") (by omega) (by omega) (hm _ (by simp [packT]))
  have e793 := mul_good (d := o + 793) (x := o + 792) (y := o + 792) (by omega) (by omega)
    (hm _ (by simp [packT]))
  have e794 := mul_good (d := o + 794) (x := o + 793) (y := o + 793) (by omega) (by omega)
    (hm _ (by simp [packT]))
  have e795 := mul_good (d := o + 795) (x := o + 794) (y := o + 794) (by omega) (by omega)
    (hm _ (by simp [packT]))
  have e797 := mul_good (d := o + 797) (x := o + 782) (y := o + 795) (by omega) (by omega)
    (hm _ (by simp [packT]))
  have r2 : ∀ v ∈ (List.range 7).map (fun k ↦ V.n (o + 798 + k)), σ v = layerW D first cur cb v.idx :=
    hm (.dispatch (.n (valf% «keccak_layer» "rem_g")) remNames
      (((List.range 7).map fun k ↦ .n (o + 785 + k)) ++ [.n (o + 796), .n (o + 797),
        .n (valf% «keccak_layer» "tabs")]) ((List.range 7).map fun k ↦ .n (o + 798 + k)))
      (by simp [packT])
  have e810 : σ (.n (o + 810)) = layerW D first cur cb (o + 810) :=
    hm (.atom (.hint (.alloc (.n (o + 810)) 11))) (by simp [packT])
  have hT : ∀ s ∈ tailT (layOff first) (tW first) (tV first),
      GoodS rd (layerSt first) (layerW D first cur cb) σ s :=
    fun s hs ↦ hG s (by rw [layerT_sections]; simp [hs])
  have g27 : σ (.n (tW first + 25)) = layerW D first cur cb (tW first + 25) :=
    hT (.atom (.hint (.alloc (.n (tW first + 25)) 25))) (by
      rw [tailT_split]; simp [tailPre, tailA1, tailP2])
  have gfl : σ (.n (topV (tW first) + 3)) = layerW D first cur cb (topV (tW first) + 3) :=
    hT (.atom (.hint (.alloc (.n (topV (tW first) + 3)) 7))) (by
      rw [tailT_split]; simp [tailPre, tailA1, tailTop])
  have a7 : σ (.n 7) = cur := hpar 7 (by norm_num)
  have a9 : σ (.n 9) = gen ^ (D.y / krStep) := hpar 9 (by norm_num)
  have h16 : σ (.n (o + 795)) = gen ^ D.n1 := by
    rw [e795, e794, e793, e792, a9, LayerData.n1, krStep, pow_mul]; ring
  refine ⟨a7, hpar 8 (by norm_num), a9, hpar 10 (by norm_num), hpar 11 (by norm_num),
    hpar 12 (by norm_num), hpar 14 (by norm_num), by rw [e782, w782],
    by rw [e784, e783, a7, gen48], fun k hk ↦ ?_, by rw [e797, e782, w782, h16], fun k hk ↦ ?_,
    by rw [e810, w810], by rw [g27, w25], by rw [gfl, wF]⟩
  · rw [r1 _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)]; exact w785 k hk
  · rw [r2 _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)]; exact w798 k hk

/-! ## The own words -/

/-- The flips of the next claim. -/
def layerFl (D : LayerData) (first : ℕ) : List E :=
  flipsOf (laterWeights (lanesOut (D.locPt first) (D.beta first).1) (eqKernel ((D.locPt first).take 6)))

/-- **The layer's own words**: the pack challenges, the local point, the next claim's lanes and
flips. -/
noncomputable def layerWo (D : LayerData) (first cb : ℕ) : Words :=
  [(cb, D.chs first), (cb + D.y, D.locPt first), (cb + D.y + 11, lanesOut (D.locPt first) (D.beta first).1),
    (cb + D.y + 36, layerFl D first)]

theorem layerWo_lengths {D : LayerData} {first : ℕ} (hpm : D.packMsgs.length = D.y)
    (hlm : D.localMsgs.length = 11) :
    (D.chs first).length = D.y ∧ (D.locPt first).length = 11 ∧
      (lanesOut (D.locPt first) (D.beta first).1).length = 25 ∧ (layerFl D first).length = 7 := by
  refine ⟨LayerData.chs_length hpm, ?_, lanesOut_length _ _, by simp [layerFl, flipsOf]⟩
  rw [LayerData.locPt, LayerData.loc, layerLocal, localRunF_length, hlm]

/-- **What the own words give the caller**: a memory holding them and the next claim's record at
`out` holds the next claim. -/
theorem layer_out {D : LayerData} {first : ℕ} (hpm : D.packMsgs.length = D.y)
    (hlm : D.localMsgs.length = 11) {rd : Reader} {cb : ℕ} {out : E}
    (hW : HoldsWords rd (layerWo D first cb)) (ho : ReadsAt rd out (VsC.klOutW (D.next first) cb D.y)) :
    ClaimRec rd false out (D.next first) D.y := by
  obtain ⟨_, hlocL, _, _⟩ := layerWo_lengths (first := first) hpm hlm
  have w0 : ReadsAt rd (VsC.ptrAtV cb) (D.chs first) := hW (cb, D.chs first) (by simp [layerWo])
  have w1 : ReadsAt rd (VsC.ptrAtV (cb + D.y)) (D.locPt first) :=
    hW (cb + D.y, D.locPt first) (by simp [layerWo])
  have w2 : ReadsAt rd (VsC.ptrAtV (cb + D.y + 11)) (lanesOut (D.locPt first) (D.beta first).1) :=
    hW (cb + D.y + 11, lanesOut (D.locPt first) (D.beta first).1) (by simp [layerWo])
  have w3 : ReadsAt rd (VsC.ptrAtV (cb + D.y + 36)) (layerFl D first) :=
    hW (cb + D.y + 36, layerFl D first) (by simp [layerWo])
  have hoK : ∀ k < 6, LoadHolds rd out k ((VsC.klOutW (D.next first) cb D.y).getD k 0) :=
    fun k hk ↦ kk_readsAt_getD ho (by simp [VsC.klOutW]; omega)
  simp only [ClaimRec, Bool.false_eq_true, ↓reduceIte]
  refine ⟨by show (keccakInstanceWeights _).length = _; rw [keccakInstanceWeights_length]; rfl,
    by show (D.chs first).length = D.y; exact LayerData.chs_length hpm,
    by simpa [VsC.klOutW] using hoK 0 (by norm_num),
    by simpa [VsC.klOutW] using hoK 1 (by norm_num), fun i hi ↦ ?_,
    ⟨VsC.ptrAtV cb, by simpa [VsC.klOutW, VsC.ptrAtV] using hoK 2 (by norm_num), w0⟩,
    VsC.ptrAtV (cb + D.y + 11), lanesOut (D.locPt first) (D.beta first).1,
    by simpa [VsC.klOutW, VsC.ptrAtV] using hoK 3 (by norm_num), lanesOut_length _ _, w2,
    VsC.ptrAtV (cb + D.y), VsC.ptrAtV (cb + D.y + 36), D.locPt first,
    by simpa [VsC.klOutW, VsC.ptrAtV] using hoK 4 (by norm_num), hlocL, w1,
    by simpa [VsC.klOutW, VsC.ptrAtV] using hoK 5 (by norm_num), ?_, ?_⟩
  · have hi16 : i < 16 := hi
    have hlen : 6 + i < (VsC.klOutW (D.next first) cb D.y).length := by
      simp [VsC.klOutW, LayerData.next, layerClaim, keccakInstanceWeights_length]; omega
    have := kk_readsAt_getD ho hlen
    rw [VsC.klOutW, List.getD_append_right _ _ _ _ (by simp)] at this
    simpa using this
  · have hw : (D.next first).weights =
        laterWeights (lanesOut (D.locPt first) (D.beta first).1) (eqKernel ((D.locPt first).take 6)) := by
      simp only [LayerData.next, layerClaim, laterWeights]
      rw [← batch_factor _ hlocL]
      rfl
    rw [hw]; exact w3
  · simp only [LayerData.next, layerClaim, laterWeights]
    rw [← batch_factor _ hlocL]
    rfl

end
end LeanVM.Guest.B1.VerifySub.KL
