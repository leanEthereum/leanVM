/-
  LeanVM.Guest.B1.KeccakGkr.LayerCG

  `keccak_layer`'s body holds on its honest valuation, on a memory holding the claim, the stream,
  the next claim's record and the layer's buffers, given its two calls.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerCG1
public import LeanVM.Guest.B1.KeccakGkr.LayerCPack
public import LeanVM.Guest.B1.KeccakGkr.LayerCD
public import LeanVM.Guest.B1.KeccakGkr.LayerHolds

/-!
# A layer's body, completely

`layer_body_complete`: for a layer's honest data `D` (the claim's projection and final checks
holding), on a memory holding the claim's record, the stream words `D.xs` at the cursor, the next
claim's record at `out` (`D.outW`, its pointers the layer's buffers), and the buffers the oracle
`w` places (the pack challenges, the round records, the local point, the next claim's lanes and
slices), the honest valuation satisfies the body and returns `D.rets`, given the nonce passing
the grind (`hgrind`), `grind_check__L3` complete on the tables `tb` (`hgr`), and the two pack
loops' relations.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd LeanVM.Protocol.KeccakGkr

@[expose] public section

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
  rw [List.length_singleton, flatMap_pairs_length, hpm, hpl, mul_assoc, ← pow_add,
    mul_assoc, ← pow_add] at h3
  rw [List.length_singleton, flatMap_pairs_length, flatMap_triples_length, hlm, hpm, hpl,
    mul_assoc, ← pow_add, mul_assoc, ← pow_add, mul_assoc, ← pow_add] at h4
  refine ⟨h1, by simpa using hn, by convert h3 using 2; ring_nf, by convert h4 using 2; ring_nf⟩

end LayerData

theorem five_of_length' {l : List E} (h : l.length = 5) :
    ∃ a b c d e, l = [a, b, c, d, e] := by
  match l, h with
  | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩

theorem one_add_gen_pow_isInK (k : ℕ) : IsInK (1 + gen ^ k) :=
  isInK_add ((isInK_iff _).mpr ⟨1, ofK_one.symm⟩) ((isInK_iff _).mpr ⟨_, gen_pow_eq_ofK k⟩)

theorem outW_mu {D : LayerData} {first : ℕ} {pt lp lc sl : E} {i : ℕ} :
    (D.outW first pt lp lc sl).getD (6 + i) 0 =
      (keccakInstanceWeights (D.sv first)).getD i 0 := by
  simp only [LayerData.outW, LayerData.next, layerClaim, LayerData.sv]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem layOff_ok {first : ℕ} (hf : first < 2) : LayOff (layOff first) := by
  interval_cases first
  · exact Or.inl rfl
  · exact Or.inr rfl

set_option maxRecDepth 20000 in
/-- **A layer's body, completely.** -/
theorem layer_body_complete {first : ℕ} (hf : first < 2) (D : LayerData)
    {rd : Reader} {w : ℕ → E} {p0 p1 cur claim out iota tb : E} {cw : List E}
    (hcl : D.cap.length = 5)
    (hw : first = 1 → (p0, p1) = Keccak.scalarCells D.w0 dsObserve)
    (hy1 : 1 ≤ D.y) (hy30 : D.y ≤ 30) (hpl : D.product.length = 47)
    (hpm : D.packMsgs.length = D.y) (hlm : D.localMsgs.length = 11)
    (hproj : projectedOf D.c D.product + iota * sumE D.c.mu = D.c.value)
    (hgrind : ((D.s0 first).absorbAll D.product dsObserve).GrindOk sGrindBits D.nonce)
    (hfin : LayerFinal D.c (D.s0 first) D.product D.nonce D.packMsgs D.localMsgs D.t)
    (hcr : ClaimRec rd (first = 1) claim D.c D.y) (hcw : ReadsAt rd claim cw)
    (hcwl : 22 ≤ cw.length) (hxs : ReadsAt rd cur D.xs)
    (hpt : ReadsAt rd (w (layOff first + 719)) (D.chs first))
    (hrec : ReadsAt rd (w (layOff first + 720)) (D.recWords first cur))
    (hloc : ReadsAt rd (w (layOff first + 748)) (D.locPt first))
    (hlan : ReadsAt rd (w (tW first + 27)) (lanesOut (D.locPt first) (D.beta first).1))
    (hfl : ReadsAt rd (w (topV (tW first) + 3))
      (flipsOf (laterWeights (lanesOut (D.locPt first) (D.beta first).1)
        (eqKernel ((D.locPt first).take 6)))))
    (hout : ReadsAt rd out (D.outW first (w (layOff first + 719)) (w (tW first + 27))
      (w (layOff first + 748)) (w (topV (tW first) + 3))))
    (hgr : ∀ v : E, (v.limb 0).lane.toNat % 2 ^ 3 = 0 →
      coreProgram.Rel rd (grindCheckName 3) [v, tb] [])
    (hloop : 1 + gen ^ (D.y / 8) ≠ 0 → coreProgram.Rel rd (packLoopName first)
      [1, gen ^ (D.y / 8), w (layOff first + 720), cw.getD 2 0, w (layOff first + 719), tb] [])
    (hrem : 1 + gen ^ (D.y % 8) ≠ 0 → coreProgram.Rel rd (remLoopName first)
      [1, gen ^ (D.y % 8), w (layOff first + 720) * gen ^ (D.y / 8),
        cw.getD 2 0 * (gen ^ (D.y / 8)) ^ 8, tb, w (layOff first + 719) * (gen ^ (D.y / 8)) ^ 8]
      []) :
    let σ := layerσ rd w (D.cap ++ [p0, p1, cur, gen ^ D.y, gen ^ (D.y / 8),
      gen ^ (D.y % 8), claim, out, iota, tb]) first
    (σ (.n (layOff first + 739)) = w (layOff first + 720) * gen ^ (D.y / 8) * gen ^ (D.y % 8) ∧
      σ (.n (layOff first + 532)) = cellsOfState (((D.s0 first).absorbAll D.product
        dsObserve).nonceState D.nonce) false ⟨1, by omega⟩ ∧
      σ (.n (layOff first + 745)) = cur * gen ^ (48 + 2 * D.y) ∧
      σ (.n (layOff first + 1190)) = cw.getD 3 0 ∧
      (first = 0 → σ (.n (layOff first + 1191)) = cw.getD 4 0) ∧
      σ (.n (layOff first + 718)) = cw.getD 2 0) ∧
    Stmt.HoldsList (coreProgram.Rel rd) rd σ (layerT first) False
      (fun r ↦ r = D.rets first cur) := by
  intro σ'
  obtain ⟨f0, f1, f2, f3, f4, hcapE⟩ := five_of_length' hcl
  have hl : (D.cap ++ [p0, p1, cur, gen ^ D.y, gen ^ (D.y / 8), gen ^ (D.y % 8), claim,
      out, iota, tb]).length = 15 := by simp [hcl]
  have hG := layer_good (rd := rd) (w := w) hf hl
  have hpar := fun i (hi : i < 15) ↦ layer_param (rd := rd) (w := w) hf hl hi
  have hσ := fun v ↦ layerσ_idx (rd := rd) (w := w) (first := first)
    (args := D.cap ++ [p0, p1, cur, gen ^ D.y, gen ^ (D.y / 8), gen ^ (D.y % 8),
    claim, out, iota, tb]) v
  generalize hσ' : layerσ rd w (D.cap ++ [p0, p1, cur, gen ^ D.y, gen ^ (D.y / 8),
    gen ^ (D.y % 8), claim, out, iota, tb]) first = σ at hG hpar hσ
  have eσ : σ' = σ := hσ'
  rw [eσ]
  clear eσ hσ'
  rw [hcapE] at hpar
  have a0 : σ (.n 0) = f0 := hpar 0 (by norm_num)
  have a1 : σ (.n 1) = f1 := hpar 1 (by norm_num)
  have a2 : σ (.n 2) = f2 := hpar 2 (by norm_num)
  have a3 : σ (.n 3) = f3 := hpar 3 (by norm_num)
  have a4 : σ (.n 4) = f4 := hpar 4 (by norm_num)
  have a5 : σ (.n 5) = p0 := hpar 5 (by norm_num)
  have a6 : σ (.n 6) = p1 := hpar 6 (by norm_num)
  have a7 : σ (.n 7) = cur := hpar 7 (by norm_num)
  have a9 : σ (.n 9) = gen ^ (D.y / 8) := hpar 9 (by norm_num)
  have a10 : σ (.n 10) = gen ^ (D.y % 8) := hpar 10 (by norm_num)
  have a11 : σ (.n 11) = claim := hpar 11 (by norm_num)
  have a12 : σ (.n 12) = out := hpar 12 (by norm_num)
  have a13 : σ (.n 13) = iota := hpar 13 (by norm_num)
  have a14 : σ (.n 14) = tb := hpar 14 (by norm_num)
  clear hpar
  have ho := layOff_ok hf
  rw [layerT_sections] at hG ⊢
  have hNS := layer_noStore hf
  have hS7 := not_mem_of_noStoreVia hNS (p := .n 7) (by simp)
  have hS11 := not_mem_of_noStoreVia hNS (p := .n 11) (by simp)
  have hS72 := not_mem_of_noStoreVia hNS (p := .n (layOff first + 739)) (by simp)
  have hS78 := not_mem_of_noStoreVia hNS (p := .n (layOff first + 745)) (by simp)
  obtain ⟨hRe, hRw, hRt, hRtop, hRf, hRfl⟩ := layer_residOk hf
  -- the claim's record
  obtain ⟨hmuL, hptL, hval, hkap, hmus, ⟨pp, hpp, hppR⟩, lp, lanes, hlp, hlanesL, hlanesR, hwts⟩ :=
    hcr
  have hcw' : ∀ k < 22, LoadHolds rd claim k (cw.getD k 0) := fun k hk ↦ by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hcw k (by omega)
  have elp : cw.getD 3 0 = lp := loadHolds_unique (hcw' 3 (by norm_num)) hlp
  -- the stream
  obtain ⟨hxP, hxN, hxL, hxT⟩ := LayerData.xs_split hpl hpm hlm hxs
  -- the sections' equations
  have gA : ∀ s ∈ secA1 first ++ secA2 first, GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by rcases List.mem_append.mp hs with h | h <;> simp [h])
  have gR : ∀ s ∈ rmfeBlockT (layOff first), GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by simp [hs])
  have gH : ∀ s ∈ hornerS first, GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by simp [hs])
  have gP : ∀ s ∈ packSetupT (layOff first) first, GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by simp [hs])
  have gL : ∀ s ∈ lastT (layOff first), GoodS rd (layerSt first) w σ s := fun s hs ↦
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
  have hs0 : plainStart first [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] D.w0 =
      D.s0 first := by rw [a0, a1, a2, a3, a4, LayerData.s0, hcapE]
  obtain ⟨-, hprodE, h532, hsq, HA⟩ := layerA_complete (C := coreProgram.Rel rd) hf hσ gA
    (hS7 · ·) (hS11 · ·) (w0 := D.w0) (fun h1 ↦ by rw [a5, a6]; exact hw h1) (c := D.c) hmuL
    (by rw [a11]; exact hval) (by rw [a11]; exact hkap) (fun i hi ↦ by rw [a11]; exact hmus i hi)
    hpl (by rw [a7]; exact hxP) (by rw [a13]; exact hproj) (n := D.nonce) (by rw [a7]; exact hxN)
    (by rw [hs0]; exact hgrind) (fun v hv ↦ by rw [a14]; exact hgr v hv)
  rw [hs0] at hsq h532
  have e544 : σ (.n (layOff first + 544)) = D.sv first := by rw [LayerData.sv, hsq]
  have ecapS : (cap5 (layOff first + 539)).map σ = D.capS first := by rw [LayerData.capS, hsq]
  -- the instance weights
  have HR : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (rmfeBlockT (layOff first)) next kret :=
    fun hn ↦ rmfe_complete (C := coreProgram.Rel rd) ho hσ gR
    (fun i hi ↦ by
      rw [a12, e544, ← outW_mu]
      exact kk_readsAt_getD hout (by simp [LayerData.outW, LayerData.next, layerClaim,
        keccakInstanceWeights_length]; omega))
    (by
      rw [a12, e544]
      have := kk_readsAt_getD hout (k := 1) (by simp [LayerData.outW])
      simpa [LayerData.outW, LayerData.next, layerClaim, LayerData.sv] using this) hn
  -- the product at `s`
  have HH : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (hornerS first) next kret :=
    fun hn ↦ horner_complete (C := coreProgram.Rel rd) hf hσ gH hn
  have e717 : σ (.n (layOff first + 717)) = polyEval D.product (D.sv first) := by
    obtain ⟨hl47, -⟩ := prodTab_facts first hf
    have := (hornerT_holds (cs := D.product) hpl (fun k hk ↦ by
      rw [← hprodE]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (show k < (prodTab first).length by omega), Option.map_some,
        Option.getD_some]) (HH (next := True) (kret := fun _ ↦ True) trivial)).1
    rwa [e544, show layOff first + 626 + 91 = layOff first + 717 by omega] at this
  -- the pack rounds' setup
  have g720 : σ (.n (layOff first + 720)) = w (layOff first + 720) :=
    gP (.atom (.hint (.alloc (.n (layOff first + 720)) 128))) (by simp [packSetupT])
  have g719 : σ (.n (layOff first + 719)) = w (layOff first + 719) :=
    gP (.atom (.hint (.allocDyn (.n (layOff first + 719)) (.n 8)))) (by simp [packSetupT])
  have hrec0 : RoundRec rd (σ (.n (layOff first + 720))) 0 ((cap5 (layOff first + 539)).map σ)
      (σ (.n 7) * gen ^ 48) (σ (.n (layOff first + 717))) 1 := by
    have := LayerData.recWords_rec hrec (j := 0) (by norm_num) (by omega)
    rw [g720, ecapS, a7, e717]
    simpa [LayerData.recK, LayerData.run_zero, LayerData.recCur] using this
  obtain ⟨e718, e727, HP⟩ := packSetup_complete (C := coreProgram.Rel rd) ho gP (hS11 _ _)
    (pp := cw.getD 2 0) (by rw [a11]; exact hcw' 2 (by norm_num)) hrec0
    (by rw [a9]; exact one_add_gen_pow_isInK _)
    (fun hne ↦ by rw [a9, g720, g719, a14]; exact hloop (by rwa [a9] at hne))
    (by rw [a10]; exact one_add_gen_pow_isInK _)
    (fun hne ↦ by rw [a9, a10, g720, g719, a14]; exact hrem (by rwa [a10] at hne))
  -- the last record
  have hkm : D.recK (D.y / 8 + D.y % 8) = D.y := by unfold LayerData.recK; split <;> omega
  have hrecm := LayerData.recWords_rec hrec (j := D.y / 8 + D.y % 8) (by omega) (by omega)
  rw [hkm, LayerData.run_full hpm] at hrecm
  have hcur : D.recCur cur (D.y / 8 + D.y % 8) = cur * gen ^ (48 + 2 * D.y) := by
    simp [LayerData.recCur, hkm]
  rw [hcur] at hrecm
  obtain ⟨e739, ecapL, e745, e746, e747, HL⟩ := last_complete (C := coreProgram.Rel rd) ho hσ gL
    (hS72 · ·) (by rw [e727, g720, a9, a10, mul_assoc, ← pow_add]; exact hrecm)
  have g748 : σ (.n (layOff first + 748)) = w (layOff first + 748) :=
    gL (.atom (.hint (.alloc (.n (layOff first + 748)) 11)))
      (by unfold lastT; exact List.mem_append_right _ (by simp))
  -- the position rounds
  have hpk := LayerData.run_cap (D := D) (first := first) D.y
  rw [LayerData.run_full hpm] at hpk
  have eLoc : localRunF D.localMsgs (σ (.n (layOff first + 746)))
      ⟨(cap5 (layOff first + 740)).map σ, []⟩ = D.loc first := by
    rw [e746, ecapL, LayerData.loc, layerLocal]
    conv_rhs => rw [show layerPack D.c (D.s0 first) D.product D.nonce D.packMsgs = D.pack first
      from rfl, hpk.2]
  obtain ⟨hvR, hcR, HLR⟩ := localRounds_complete (C := coreProgram.Rel rd)
    (cur := .n (layOff first + 745)) (loc := .n (layOff first + 748))
    (vIn := .n (layOff first + 746)) (capV := cap5 (layOff first + 740))
    (a0 := layOff first + 749) (hS78 · ·) 11 D.localMsgs hlm (by norm_num) gLR
    (by rw [e745]; exact hxL)
  rw [eLoc] at hvR hcR HLR
  -- `t`
  have hT : ∀ k < 3, LoadHolds rd (σ (.n (layOff first + 745))) (33 + k)
      ([D.t.1, D.t.2.1, D.t.2.2].getD k 0) := by
    intro k hk
    rw [e745, ← loadHolds_mul_gen_pow, mul_assoc, ← pow_add]
    exact kk_readsAt_getD hxT (by simp; omega)
  obtain ⟨et0, et1, et2, HT⟩ := tReads_complete (C := coreProgram.Rel rd) gT (hS78 · ·)
    (by simpa using hT 0 (by norm_num)) (by simpa using hT 1 (by norm_num))
    (by simpa using hT 2 (by norm_num))
  -- the lane weights of the local point
  have hlocL : (D.locPt first).length = 11 := by
    rw [LayerData.locPt, LayerData.loc, layerLocal, localRunF_length, hlm]
  have hlocσ : ReadsAt rd (σ (.n (layOff first + 748))) (D.locPt first) := by
    rw [g748]; exact hloc
  have HE : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (eqfS (layOff first)) next kret :=
    fun hn ↦ eqf_complete ho hσ gE (not_mem_of_noneIn hRe) hlocL hlocσ hn
  obtain ⟨⟨rs, hrsL, hrs, hent⟩, -⟩ := eqfT_holds (C := coreProgram.Rel rd) (rd := rd) (σ := σ)
    (pt := .n (layOff first + 748)) (off := 6) (n := 5) (count := 25) (b := layOff first + 1121)
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
      rw [loadHolds_unique (hcw' 4 (by norm_num)) h4]
      exact hr
    · exact ⟨[], fun h ↦ by omega⟩
  have HW : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (weightT first (layOff first)) next kret :=
    fun hn ↦ weight_complete hf hσ gW (not_mem_of_noneIn hRw) (by rw [a11]; exact hcw) hcwl
      hlanesL (by rw [elp]; exact hlanesR) hlocL hlocσ hlc hn
  have hWk : WeightOk first (layOff first) := by
    interval_cases first
    · exact weightOk_zero _
    · exact weightOk_one _
  obtain ⟨hwv, -⟩ := hWk (coreProgram.Rel rd) rd σ D.c D.y (D.locPt first) True
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
  have hfin' : σ (.n (layOff first + 747)) * σ (.n (tV first)) *
      (σ (.n (layOff first + 625)) * σ (.n (layOff first + 1112)) +
        (σ (.n (layOff first + 625)) + σ (.n (layOff first + 1115))) *
          σ (.n (layOff first + 1118))) = σ (.n (layOff first + 1111)) := by
    have e1111 : layOff first + 749 + 33 * (11 - 1) + 32 = layOff first + 1111 := by omega
    rw [e1111] at hvR
    rw [e747, show tV first = weightVal first (layOff first) from rfl, hwv, hv625, e544, et0,
      et1, et2, ← hvR]
    exact hfin
  obtain ⟨eβ, ecapB, HTl⟩ := layer_tail_complete (C := coreProgram.Rel rd) hf hσ gTP
    (not_mem_of_noneIn hRt) (not_mem_of_noneIn hRtop _ (by simp))
    (fun i hi ↦ not_mem_of_noneIn (hRf i hi))
    (fun i hi ↦ List.contains_iff_mem.mp (hRfl i hi)) v0 v1 v2 hlocL hlocσ hfw hfin'
  have eTail : tailSq (layOff first) σ = D.beta first := by
    have ecv : localRoundsT.capV' (layOff first + 749 + 33 * (11 - 1) + 19) =
        cap5 (layOff first + 1098) := by
      simp only [localRoundsT.capV', cap5]
    rw [LayerData.beta, layerBeta, show layerLocal D.c (D.s0 first) D.product D.nonce D.packMsgs
      D.localMsgs = D.loc first from rfl, hcR, ecv, tailSq, sq3, et0, et1, et2]
  rw [eTail] at eβ ecapB HTl
  have g27 : σ (.n (tW first + 27)) = w (tW first + 27) :=
    gTP (.atom (.hint (.alloc (.n (tW first + 27)) 25))) (by
      simp [tailPre, tailA1, tailP2])
  have gfl : σ (.n (topV (tW first) + 3)) = w (topV (tW first) + 3) :=
    gTP (.atom (.hint (.alloc (.n (topV (tW first) + 3)) 7))) (by
      simp [tailPre, tailA1, tailTop])
  have ho' : ∀ k < 6, LoadHolds rd (σ (.n 12)) k ((D.outW first (w (layOff first + 719))
      (w (tW first + 27)) (w (layOff first + 748)) (w (topV (tW first) + 3))).getD k 0) :=
    fun k hk ↦ by rw [a12]; exact kk_readsAt_getD hout (by simp [LayerData.outW]; omega)
  have e1190 : σ (.n (layOff first + 1190)) = cw.getD 3 0 := by
    have g := gW (.atom (.load (.n (layOff first + 1190)) (.n 11) 3)) (by
      unfold weightT; split <;> simp)
    exact load_val (w := w) g (hS11 _ _) (by rw [a11]; exact hcw' 3 (by norm_num))
  have e1191 : first = 0 → σ (.n (layOff first + 1191)) = cw.getD 4 0 := by
    intro h0
    have g := gW (.atom (.load (.n (layOff first + 1191)) (.n 11) 4)) (by
      unfold weightT; simp [h0])
    exact load_val (w := w) g (hS11 _ _) (by rw [a11]; exact hcw' 4 (by norm_num))
  refine ⟨⟨by rw [e739, e727, g720, a9, a10], h532, e745, e1190, e1191, e718⟩, ?_⟩
  -- the sections in turn
  rw [← List.append_assoc, holdsList_append]
  refine HA ?_
  rw [holdsList_append]; refine HR ?_
  rw [holdsList_append]; refine HH ?_
  rw [holdsList_append]; refine HP ?_
  rw [holdsList_append]; refine HL ?_
  rw [holdsList_append]; refine HLR (by rw [g748]; exact hloc) ?_
  rw [holdsList_append]; refine HT ?_
  rw [holdsList_append]; refine HE ?_
  rw [holdsList_append]; refine HW ?_
  refine HTl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have := ho' 0 (by norm_num)
    simpa [LayerData.outW, LayerData.next, layerClaim, LayerData.beta, et0, et1, et2] using this
  · have := ho' 2 (by norm_num)
    simpa [LayerData.outW, g719] using this
  · have := ho' 4 (by norm_num)
    simpa [LayerData.outW, g748] using this
  · have := ho' 3 (by norm_num)
    simpa [LayerData.outW, g27] using this
  · rw [g27]; exact hlan
  · have := ho' 5 (by norm_num)
    simpa [LayerData.outW, gfl] using this
  · rw [gfl]; exact hfl
  · rw [ecapB, e745, LayerData.rets, mul_assoc, ← pow_add]

end
end LeanVM.Guest.B1.VerifySub
