/-
  LeanVM.Guest.B1.VsC.KLBody

  `keccak_layer`'s body, completely, on Hotwire's template (the archive's `LayerCG`).
-/

module

public import LeanVM.Guest.B1.VsC.KLSpec
public import LeanVM.Guest.B1.VsC.KLPack
public import LeanVM.Guest.B1.VsC.KLHon
public import LeanVM.Guest.B1.KeccakGkr.LayerWeight0
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«keccak_layer__L»

/-!
# A layer's body, completely

`layer_body_complete`: for a layer's honest data `D` (the claim's projection and final checks
holding, the nonce passing the grind), on a memory holding the claim's record, the stream words
`D.xs` at the cursor, the next claim's record at `out` (`D.outW`, its pointers the oracle's
buffers), the local point, the next claim's lanes and flips in the buffers the oracle `w` places,
the window tables, with the inlined `grind_check`'s range checks passing and the oracle at its
windows the honest ones, and the two dispatches' returns the honest `r1`, `r2`: the honest
valuation satisfies the body under any call relation holding of the two dispatched calls, and
returns `D.rets`. The values the dispatches read are the honest ones (the capacity after `s`, the
product at `s`, the claim's point pointer).
-/

namespace LeanVM.Guest.B1.VerifySub.KL

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd LeanVM.Protocol.KeccakGkr

@[expose] public section

theorem kk_readsAt_getD {rd : Reader} {p : E} {xs : List E} (h : ReadsAt rd p xs) {k : ℕ}
    (hk : k < xs.length) : LoadHolds rd p k (xs.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

namespace LayerData

variable {D : LayerData} {first : ℕ} {rd : Reader}

/-- **The stream's parts**: the product and the nonce at the cursor, the position rounds'
messages and `t` after the pack rounds' messages. -/
theorem xs_split (hpl : D.product.length = 47) (hpm : D.packMsgs.length = D.y)
    (hlm : D.localMsgs.length = 11) {cur : E} (h : ReadsAt rd cur D.xs) :
    ReadsAt rd cur D.product ∧ LoadHolds rd cur 47 D.nonce ∧
      ReadsAt rd (cur * gen ^ (48 + 2 * D.y)) (D.localMsgs.flatMap fun m ↦ [m.1, m.2.1, m.2.2]) ∧
      ReadsAt rd (cur * gen ^ (48 + 2 * D.y + 33)) [D.t.1, D.t.2.1, D.t.2.2] := by
  simp only [xs, List.append_assoc] at h
  rw [readsAt_append, readsAt_append, readsAt_append, readsAt_append] at h
  obtain ⟨h1, h0, h2, h3, h4⟩ := h
  rw [hpl] at h0
  have hn := h0 0 (by simp)
  rw [loadHolds_mul_gen_pow, Nat.add_zero] at hn
  rw [List.length_singleton, length_flatMap_pairs, hpm, hpl, mul_assoc, ← pow_add,
    mul_assoc, ← pow_add] at h3
  rw [List.length_singleton, length_flatMap_pairs, flatMap_triples_length, hlm, hpm, hpl,
    mul_assoc, ← pow_add, mul_assoc, ← pow_add, mul_assoc, ← pow_add] at h4
  refine ⟨h1, by simpa using hn, by convert h3 using 2; ring_nf, by convert h4 using 2; ring_nf⟩

end LayerData

theorem five_of_length' {l : List E} (h : l.length = 5) :
    ∃ a b c d e, l = [a, b, c, d, e] := by
  match l, h with
  | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩

theorem outW_mu {D : LayerData} {first : ℕ} {pt lp lc sl : E} {i : ℕ} :
    (D.outW first pt lp lc sl).getD (6 + i) 0 =
      (keccakInstanceWeights (D.sv first)).getD i 0 := by
  simp only [LayerData.outW, LayerData.next, layerClaim, LayerData.sv]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem preOff_ok {first : ℕ} (hf : first < 2) : LayOff (preOff first) := by
  interval_cases first
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem layOff_okP {first : ℕ} (hf : first < 2) : LayOffP (layOff first) := by
  interval_cases first
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem layOff_eq (first : ℕ) : layOff first = preOff first + 1 := by unfold layOff preOff; rfl

/-- The cursor after the pack rounds. -/
theorem cur_pack {D : LayerData} {cur : E} :
    cur * gen ^ 48 * gen ^ (2 * D.n1) * gen ^ (2 * (D.y % krStep)) = cur * gen ^ (48 + 2 * D.y) := by
  rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
  congr 2
  unfold LayerData.n1 krStep
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **A layer's body, completely.** -/
theorem layer_body_complete {first : ℕ} (hf : first < 2) (D : LayerData) {C : CallRel}
    {rd : Reader} {w : ℕ → E} {p0 p1 cur claim out iota tb cpt : E} {cw : List E}
    (hcl : D.cap.length = 5)
    (hw : first = 1 → (p0, p1) = Keccak.scalarCells D.w0 dsObserve)
    (hy32 : D.y < 32) (hpl : D.product.length = 47)
    (hpm : D.packMsgs.length = D.y) (hlm : D.localMsgs.length = 11)
    (hproj : projectedOf D.c D.product + iota * sumE D.c.mu = D.c.value)
    (hgrind : ((D.s0 first).absorbAll D.product dsObserve).GrindOk sGrindBits D.nonce)
    (hfin : LayerFinal D.c (D.s0 first) D.product D.nonce D.packMsgs D.localMsgs D.t)
    (hcr : ClaimRec rd (first = 1) claim D.c D.y) (hcpt : LoadHolds rd claim 2 cpt)
    (hcw : ReadsAt rd claim cw) (hcwl : (if first = 1 then 4 else 5) ≤ cw.length)
    (hxs : ReadsAt rd cur D.xs)
    (hloc : ReadsAt rd (w (layOff first + 809)) (D.locPt first))
    (hlan : ReadsAt rd (w (tW first + 25)) (lanesOut (D.locPt first) (D.beta first).1))
    (hfl : ReadsAt rd (w (topV (tW first) + 3))
      (flipsOf (laterWeights (lanesOut (D.locPt first) (D.beta first).1)
        (eqKernel ((D.locPt first).take 6)))))
    (hout : ReadsAt rd out (D.outW first (w (preOff first + 782)) (w (tW first + 25))
      (w (layOff first + 809)) (w (topV (tW first) + 3))))
    (hrc : ∀ v ≤ 11, ∀ e < 2 ^ v, ∃ y t1 t2 : E, LoadHolds rd (gen ^ e) 0 t1 ∧
      wBound v = gen ^ e * y ∧ LoadHolds rd y 0 t2)
    (htb : WinTabs rd tb)
    (hwin : ∀ j ≤ gcW 3, w (preOff first + 544 + j) = gcWin 3 (cellsOfState
      (((D.s0 first).absorbAll D.product dsObserve).nonceState D.nonce) false ⟨1, by omega⟩) j)
    (hr1 : ∀ k < 7, w (preOff first + 785 + k) = (D.r1 first cur).getD k 0)
    (hr2 : ∀ k < 7, w (preOff first + 798 + k) = (D.r2 first cur).getD k 0)
    (hc1 : C (stepNames.getD (D.y / krStep) "") (D.capS first ++
          [cur * gen ^ 48, polyEval D.product (D.sv first), cpt, w (preOff first + 782), tb])
          ((List.range 7).map fun k ↦ w (preOff first + 785 + k)))
    (hc2 : C (remNames.getD (D.y % krStep) "") (((List.range 7).map fun k ↦ w (preOff first + 785 + k)) ++
          [cpt * gen ^ D.n1, w (preOff first + 782) * gen ^ D.n1, tb])
          ((List.range 7).map fun k ↦ w (preOff first + 798 + k))) :
    let σ := layerσ rd w (D.cap ++ [p0, p1, cur, gen ^ D.y, gen ^ (D.y / krStep),
      gen ^ (D.y % krStep), claim, out, iota, tb]) first
    ((cap5 (preOff first + 539)).map σ = D.capS first ∧
      σ (.n (preOff first + 780)) = polyEval D.product (D.sv first) ∧
      σ (.n (preOff first + 781)) = cpt ∧ σ (.n (preOff first + 796)) = cpt * gen ^ D.n1 ∧
      σ (.n (preOff first + 532)) = cellsOfState (((D.s0 first).absorbAll D.product
        dsObserve).nonceState D.nonce) false ⟨1, by omega⟩) ∧
    Stmt.HoldsList C rd σ (layerT first) False (fun r ↦ r = D.rets first cur) := by
  intro σ'
  obtain ⟨f0, f1, f2, f3, f4, hcapE⟩ := five_of_length' hcl
  have hl : (D.cap ++ [p0, p1, cur, gen ^ D.y, gen ^ (D.y / krStep), gen ^ (D.y % krStep), claim,
      out, iota, tb]).length = 15 := by simp [hcl]
  have hG := layer_good (rd := rd) (w := w) hf hl
  have hpar := fun i (hi : i < 15) ↦ layer_param (rd := rd) (w := w) hf hl hi
  have hσ := fun v ↦ layerσ_idx (rd := rd) (w := w) (first := first)
    (args := D.cap ++ [p0, p1, cur, gen ^ D.y, gen ^ (D.y / krStep), gen ^ (D.y % krStep),
    claim, out, iota, tb]) v
  generalize hσ' : layerσ rd w (D.cap ++ [p0, p1, cur, gen ^ D.y, gen ^ (D.y / krStep),
    gen ^ (D.y % krStep), claim, out, iota, tb]) first = σ at hG hpar hσ
  have eσ : σ' = σ := hσ'
  rw [eσ]
  clear eσ hσ'
  rw [hcapE] at hpar
  have a0 : σ (.n (valf% «keccak_layer» "fs0")) = f0 := hpar 0 (by norm_num)
  have a1 : σ (.n (valf% «keccak_layer» "fs1")) = f1 := hpar 1 (by norm_num)
  have a2 : σ (.n (valf% «keccak_layer» "fs2")) = f2 := hpar 2 (by norm_num)
  have a3 : σ (.n (valf% «keccak_layer» "fs3")) = f3 := hpar 3 (by norm_num)
  have a4 : σ (.n (valf% «keccak_layer» "fs4")) = f4 := hpar 4 (by norm_num)
  have a5 : σ (.n (valf% «keccak_layer» "p0")) = p0 := hpar 5 (by norm_num)
  have a6 : σ (.n (valf% «keccak_layer» "p1")) = p1 := hpar 6 (by norm_num)
  have a7 : σ (.n (valf% «keccak_layer» "cursor@1")) = cur := hpar 7 (by norm_num)
  have a9 : σ (.n (valf% «keccak_layer» "step_g")) = gen ^ (D.y / krStep) := hpar 9 (by norm_num)
  have a10 : σ (.n (valf% «keccak_layer» "rem_g")) = gen ^ (D.y % krStep) := hpar 10 (by norm_num)
  have a11 : σ (.n (valf% «keccak_layer» "claim")) = claim := hpar 11 (by norm_num)
  have a12 : σ (.n (valf% «keccak_layer» "out")) = out := hpar 12 (by norm_num)
  have a13 : σ (.n (valf% «keccak_layer» "iota")) = iota := hpar 13 (by norm_num)
  have a14 : σ (.n (valf% «keccak_layer» "tabs")) = tb := hpar 14 (by norm_num)
  clear hpar
  have ho := preOff_ok hf
  have hoP := layOff_okP hf
  have hlo := layOff_eq first
  rw [layerT_sections] at hG ⊢
  have hNS := layer_noStore hf
  have hS7 := not_mem_of_noStoreVia hNS (p := .n (valf% «keccak_layer» "cursor@1")) (by simp)
  have hS11 := not_mem_of_noStoreVia hNS (p := .n (valf% «keccak_layer» "claim")) (by simp)
  have hS78 := not_mem_of_noStoreVia hNS (p := .n (layOff first + 802)) (by simp)
  obtain ⟨hRe, hRw, hRt, hRtop, hRf, hRfl⟩ := layer_residOk hf
  -- the claim's record
  obtain ⟨hmuL, hptL, hval, hkap, hmus, ⟨pp, hpp, hppR⟩, lp, lanes, hlp, hlanesL, hlanesR, hwts⟩ :=
    hcr
  have hcw4 : 4 ≤ cw.length := le_trans (by split <;> omega) hcwl
  have elp : cw.getD 3 0 = lp := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact loadHolds_unique (hcw 3 (by omega)) hlp
  -- the stream
  obtain ⟨hxP, hxN, hxL, hxT⟩ := LayerData.xs_split hpl hpm hlm hxs
  -- the sections' equations
  have gA : ∀ s ∈ secA1 first ++ secA2 first, GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by rcases List.mem_append.mp hs with h | h <;> simp [h])
  have gR : ∀ s ∈ rmfeBlockT (preOff first), GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by simp [hs])
  have gH : ∀ s ∈ hornerS first, GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by simp [hs])
  have gP : ∀ s ∈ packT (preOff first), GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by simp [hs])
  have gLR : ∀ s ∈ localS (layOff first), GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by simp [hs])
  have gT : ∀ s ∈ tReadsT (layOff first), GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by simp [hs])
  have gE : ∀ s ∈ eqfS (layOff first), GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by simp [hs])
  have gW : ∀ s ∈ weightT first (layOff first), GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by simp [hs])
  have gTl : ∀ s ∈ tailT (layOff first) (tW first) (tV first),
      GoodS rd (layerSt first) w σ s := fun s hs ↦ hG s (by simp [hs])
  -- the product, the grind and `s`
  have hs0 : plainStart first [σ (.n (valf% «keccak_layer» "fs0")), σ (.n (valf% «keccak_layer» "fs1")),
      σ (.n (valf% «keccak_layer» "fs2")), σ (.n (valf% «keccak_layer» "fs3")),
      σ (.n (valf% «keccak_layer» "fs4"))] D.w0 = D.s0 first := by
    rw [a0, a1, a2, a3, a4, LayerData.s0, hcapE]
  obtain ⟨-, hprodE, h532, hsq, HA⟩ := layerA_complete (C := C) hf hσ gA
    (hS7 · ·) (hS11 · ·) (w0 := D.w0) (fun h1 ↦ by rw [a5, a6]; exact hw h1) (c := D.c) hmuL
    (by rw [a11]; exact hval) (by rw [a11]; exact hkap) (fun i hi ↦ by rw [a11]; exact hmus i hi)
    hpl (by rw [a7]; exact hxP) (by rw [a13]; exact hproj) (n := D.nonce) (by rw [a7]; exact hxN)
    (by rw [hs0]; exact hgrind) hrc (by rw [a14]; exact htb) (layerSt_noGrind hf)
    (by rw [hs0]; exact hwin)
  rw [hs0] at hsq h532
  have e531 : σ (.n (preOff first + 531)) = D.sv first := by rw [LayerData.sv, hsq]
  have ecapS : (cap5 (preOff first + 539)).map σ = D.capS first := by rw [LayerData.capS, hsq]
  have hsq' : layerSq (D.s0 first) D.product D.nonce = (D.sv first, ⟨D.capS first, []⟩) := by
    rw [LayerData.sv, LayerData.capS, hsq]
  -- the instance weights
  have HR : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (rmfeBlockT (preOff first)) next kret :=
    fun hn ↦ rmfe_complete (C := C) ho hσ gR
    (fun i hi ↦ by
      rw [a12, e531, ← outW_mu]
      exact kk_readsAt_getD hout (by simp [LayerData.outW, LayerData.next, layerClaim,
        keccakInstanceWeights_length]; omega))
    (by
      rw [a12, e531]
      have := kk_readsAt_getD hout (k := 1) (by simp [LayerData.outW])
      simpa [LayerData.outW, LayerData.next, layerClaim, LayerData.sv] using this) hn
  -- the product at `s`
  have HH : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (hornerS first) next kret :=
    fun hn ↦ horner_complete (C := C) hf hσ gH hn
  have e780 : σ (.n (preOff first + 780)) = polyEval D.product (D.sv first) := by
    obtain ⟨hl47, -⟩ := prodTab_facts first hf
    have := (hornerT_holds (cs := D.product) hpl (fun k hk ↦ by
      rw [← hprodE]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (show k < (prodTab first).length by omega), Option.map_some,
        Option.getD_some]) (HH (next := True) (kret := fun _ ↦ True) trivial)).1
    rwa [e531, show preOff first + 689 + 91 = preOff first + 780 by omega] at this
  -- the pack rounds
  have hj1 : D.y / krStep < 2 := by unfold krStep; omega
  have hj2 : D.y % krStep < 16 := by unfold krStep; omega
  obtain ⟨e781, e782, -, -, e796, -, e798, ecp, e810, HP⟩ := pack_complete (C := C) (by omega) gP
    (hS11 _ _) (by rw [a11]; exact hcpt) hj1 a9 hj2 a10
    (by rw [ecapS, a7, e780, a14]; exact hc1)
    (by rw [a14, show krStep * (D.y / krStep) = D.n1 from rfl]; exact hc2)
  have hn1 : krStep * (D.y / krStep) = D.n1 := rfl
  rw [hn1] at e796
  -- the state after the pack rounds
  have hpk := LayerData.pack_split hpm hsq'
  obtain ⟨hr2s, hr2l⟩ := LayerData.run2_state (D := D) (first := first)
  have ecur : σ (.n (layOff first + 802)) = cur * gen ^ (48 + 2 * D.y) := by
    rw [hlo, show preOff first + 1 + 802 = preOff first + 798 + 5 by omega, e798 5 (by norm_num),
      hr2 5 (by norm_num), LayerData.r2, List.getD_append_right _ _ _ _ (by rw [hr2l]),
      hr2l]
    exact cur_pack
  have evIn : σ (.n (layOff first + 803)) = (D.run2 first).1.1 := by
    rw [hlo, show preOff first + 1 + 803 = preOff first + 798 + 6 by omega, e798 6 (by norm_num),
      hr2 6 (by norm_num), LayerData.r2, List.getD_append_right _ _ _ _ (by simp [hr2l]), hr2l]
    rfl
  have ecapL : (cap5 (layOff first + 804)).map σ = (D.run2 first).2.cap := by
    obtain ⟨c0, c1, c2, c3, c4, hc⟩ := five_of_length' hr2l
    have hk : ∀ j < 5, σ (.n (layOff first + 804 + j)) = (D.run2 first).2.cap.getD j 0 := by
      intro j hj
      rw [hlo, show preOff first + 1 + 804 + j = preOff first + 805 + j by omega, ecp j hj,
        hr2 j (by omega), LayerData.r2, List.getD_append _ _ _ _ (by rw [hr2l]; exact hj)]
    have k0 := hk 0 (by norm_num)
    have k1 := hk 1 (by norm_num)
    have k2 := hk 2 (by norm_num)
    have k3 := hk 3 (by norm_num)
    have k4 := hk 4 (by norm_num)
    rw [hc] at k0 k1 k2 k3 k4 ⊢
    simp only [cap5, List.map_cons, List.map_nil, Nat.add_zero, List.getD_cons_zero,
      List.getD_cons_succ] at k0 k1 k2 k3 k4 ⊢
    rw [k0, k1, k2, k3, k4]
  have e809 : σ (.n (layOff first + 809)) = w (layOff first + 809) := by
    rw [hlo, show preOff first + 1 + 809 = preOff first + 810 by omega, e810]
  -- the position rounds
  have eLoc : localRunF D.localMsgs (σ (.n (layOff first + 803)))
      ⟨(cap5 (layOff first + 804)).map σ, []⟩ = D.loc first := by
    rw [evIn, ecapL, LayerData.loc, layerLocal,
      show layerPack D.c (D.s0 first) D.product D.nonce D.packMsgs = D.pack first from rfl, hpk]
    simp only
    rw [← hr2s]
  obtain ⟨hvR, hcR, HLR⟩ := localRounds_complete (C := C)
    (cur := .n (layOff first + 802)) (loc := .n (layOff first + 809))
    (vIn := .n (layOff first + 803)) (capV := cap5 (layOff first + 804))
    (a0 := layOff first + 810) (hS78 · ·) 11 D.localMsgs hlm (by norm_num) gLR
    (by rw [ecur]; exact hxL)
  rw [eLoc] at hvR hcR HLR
  -- `t`
  have hT : ∀ k < 3, LoadHolds rd (σ (.n (layOff first + 802))) (33 + k)
      ([D.t.1, D.t.2.1, D.t.2.2].getD k 0) := by
    intro k hk
    rw [ecur, ← loadHolds_mul_gen_pow, mul_assoc, ← pow_add]
    exact kk_readsAt_getD hxT (by simp; omega)
  obtain ⟨et0, et1, et2, HT⟩ := tReads_complete (C := C) gT (hS78 · ·)
    (by simpa using hT 0 (by norm_num)) (by simpa using hT 1 (by norm_num))
    (by simpa using hT 2 (by norm_num))
  -- the lane weights of the local point
  have hlocL : (D.locPt first).length = 11 := by
    rw [LayerData.locPt, LayerData.loc, layerLocal, localRunF_length, hlm]
  have hlocσ : ReadsAt rd (σ (.n (layOff first + 809))) (D.locPt first) := by
    rw [e809]; exact hloc
  have HE : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (eqfS (layOff first)) next kret :=
    fun hn ↦ eqf_complete hoP hσ gE (not_mem_of_noneIn hRe) hlocL hlocσ hn
  obtain ⟨⟨rs, hrsL, hrs, hent⟩, -⟩ := eqfT_holds (C := C) (rd := rd) (σ := σ)
    (pt := .n (layOff first + 809)) (off := 6) (n := 5) (count := 25) (b := layOff first + 1171)
    (by norm_num) (by norm_num) (by decide) (by decide)
    (HE (next := True) (kret := fun _ ↦ True) trivial)
  have hrs6 : rs = (D.locPt first).drop 6 := by
    apply List.ext_getElem (by simp [hrsL, hlocL])
    intro k h1 h2
    rw [List.getElem_drop]
    exact loadHolds_unique (hrs k h1) (hlocσ (6 + k) (by omega))
  have hfw : ∀ i < 25, σ (.n (laneW (layOff first) i)) = eqAt ((D.locPt first).drop 6) i := by
    intro i hi
    rw [← hrs6]
    exact hent i hi
  -- the weights
  obtain ⟨locC, hlc⟩ : ∃ locC : List E, first = 0 → locC.length = 11 ∧
      ReadsAt rd (cw.getD 4 0) locC := by
    rcases (by omega : first = 0 ∨ first = 1) with h0 | h1
    · subst h0
      simp only [show ¬ (0 = 1) by decide, decide_false, Bool.false_eq_true, ↓reduceIte] at hwts
      obtain ⟨lc, fl, loc, h4, hl, hr, -⟩ := hwts
      refine ⟨loc, fun _ ↦ ⟨hl, ?_⟩⟩
      have h5 : 5 ≤ cw.length := by simpa using hcwl
      rw [List.getD_eq_getElem _ _ (by omega), loadHolds_unique (hcw 4 (by omega)) h4]
      exact hr
    · exact ⟨[], fun h ↦ by omega⟩
  have HW : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList C rd σ (weightT first (layOff first)) next kret :=
    fun hn ↦ weight_complete hf hσ gW (not_mem_of_noneIn hRw) (by rw [a11]; exact hcw) hcwl
      hlanesL (by rw [elp]; exact hlanesR) hlocL hlocσ hlc hn
  have hWk : WeightOk first (layOff first) := by
    interval_cases first
    · exact weightOk_zero _
    · exact weightOk_one _
  obtain ⟨hwv, -⟩ := hWk C rd σ D.c D.y (D.locPt first) True
    (fun _ ↦ True) (by rw [a11]; exact ⟨hmuL, hptL, hval, hkap, hmus, ⟨pp, hpp, hppR⟩, lp, lanes,
      hlp, hlanesL, hlanesR, hwts⟩) hlocL hlocσ hfw (HW trivial)
  -- the tail
  have gTP : ∀ s ∈ tailPre (layOff first) (tW first) (tV first),
      GoodS rd (layerSt first) w σ s := fun s hs ↦ gTl s (by
    rw [tailT_split]; exact List.mem_append_left _ hs)
  have gT0 := fun s hs ↦ gT s (List.mem_append_left _ (List.mem_append_left _ hs))
  have gT1 := fun s hs ↦ gT s (List.mem_append_left _ (List.mem_append_right _ hs))
  have gT2 := fun s hs ↦ gT s (List.mem_append_right _ hs)
  have v0 := fsPack_vals_of_good (fun s hs ↦ gT0 s (List.mem_cons_of_mem _ hs))
  have v1 := fsPack_vals_of_good (fun s hs ↦ gT1 s (List.mem_cons_of_mem _ hs))
  have v2 := fsPack_vals_of_good (fun s hs ↦ gT2 s (List.mem_cons_of_mem _ hs))
  obtain ⟨-, hv625⟩ := rmfe_vals ho hσ gR
  have hfin' : σ (.n (tV first)) *
      (σ (.n (layOff first + 687)) * σ (.n (layOff first + 1162)) +
        (σ (.n (layOff first + 687)) + σ (.n (layOff first + 1165))) *
          σ (.n (layOff first + 1168))) = σ (.n (layOff first + 1161)) := by
    have e1111 : layOff first + 810 + 32 * (11 - 1) + 31 = layOff first + 1161 := by omega
    rw [e1111] at hvR
    have e687 : layOff first + 687 = preOff first + 688 := by omega
    rw [show tV first = weightVal first (layOff first) from rfl, hwv, e687, hv625, e531, et0,
      et1, et2, ← hvR]
    exact hfin
  obtain ⟨eβ, ecapB, HTl⟩ := layer_tail_complete (C := C) hf hσ gTP
    (not_mem_of_noneIn hRt) (not_mem_of_noneIn hRtop _ (by simp))
    (fun i hi ↦ not_mem_of_noneIn (hRf i hi))
    (fun i hi ↦ List.contains_iff_mem.mp (hRfl i hi)) v0 v1 v2 hlocL hlocσ hfw hfin'
  have eTail : tailSq (layOff first) σ = D.beta first := by
    have ecv : localRoundsT.capV' (layOff first + 810 + 32 * (11 - 1) + 19) =
        cap5 (layOff first + 1149) := by
      simp only [localRoundsT.capV', cap5]
    rw [LayerData.beta, layerBeta, show layerLocal D.c (D.s0 first) D.product D.nonce D.packMsgs
      D.localMsgs = D.loc first from rfl, hcR, ecv, tailSq, sq3, et0, et1, et2]
  rw [eTail] at eβ ecapB HTl
  have g27 : σ (.n (tW first + 25)) = w (tW first + 25) :=
    gTP (.atom (.hint (.alloc (.n (tW first + 25)) 25))) (by
      simp [tailPre, tailA1, tailP2])
  have gfl : σ (.n (topV (tW first) + 3)) = w (topV (tW first) + 3) :=
    gTP (.atom (.hint (.alloc (.n (topV (tW first) + 3)) 7))) (by
      simp [tailPre, tailA1, tailTop])
  have ho' : ∀ k < 6, LoadHolds rd (σ (.n (valf% «keccak_layer» "out"))) k ((D.outW first
      (w (preOff first + 782)) (w (tW first + 25)) (w (layOff first + 809))
      (w (topV (tW first) + 3))).getD k 0) :=
    fun k hk ↦ by rw [a12]; exact kk_readsAt_getD hout (by simp [LayerData.outW]; omega)
  have e781' : σ (.n (layOff first + 781)) = w (preOff first + 782) := by
    rw [hlo, show preOff first + 1 + 781 = preOff first + 782 by omega, e782]
  refine ⟨⟨ecapS, e780, e781, e796, h532⟩, ?_⟩
  -- the sections in turn
  rw [← List.append_assoc, holdsList_append]
  refine HA ?_
  rw [holdsList_append]; refine HR ?_
  rw [holdsList_append]; refine HH ?_
  rw [holdsList_append]; refine HP ?_
  rw [holdsList_append]; refine HLR (by rw [e809]; exact hloc) ?_
  rw [holdsList_append]; refine HT ?_
  rw [holdsList_append]; refine HE ?_
  rw [holdsList_append]; refine HW ?_
  refine HTl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have := ho' 0 (by norm_num)
    simpa [LayerData.outW, LayerData.next, layerClaim, LayerData.beta, et0, et1, et2] using this
  · have := ho' 2 (by norm_num)
    simpa [LayerData.outW, e781'] using this
  · have := ho' 4 (by norm_num)
    simpa [LayerData.outW, e809] using this
  · have := ho' 3 (by norm_num)
    simpa [LayerData.outW, g27] using this
  · rw [g27]; exact hlan
  · have := ho' 5 (by norm_num)
    simpa [LayerData.outW, gfl] using this
  · rw [gfl]; exact hfl
  · rw [ecapB, ecur, LayerData.rets, mul_assoc, ← pow_add]

end
end LeanVM.Guest.B1.VerifySub.KL
