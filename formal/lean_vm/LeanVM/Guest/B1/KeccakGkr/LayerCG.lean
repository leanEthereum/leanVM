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
slices), the honest valuation satisfies the body and returns `D.rets`, given the pack loop's and
(with `y` odd) the last round's relations.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd LeanVM.Protocol.KeccakGkr

@[expose] public section

theorem localRunF_cap_canonical (ms : List (E × E × E)) (v : E) (s : Fs) (hne : ms ≠ []) :
    AllCanonical (localRunF ms v s).2.cap ∧ (localRunF ms v s).2.cap.length = 5 := by
  obtain ⟨ms', m, rfl⟩ : ∃ ms' m, ms = ms' ++ [m] :=
    ⟨ms.dropLast, ms.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  rw [localRunF_snoc]
  exact ⟨squeeze_cap_canonical _, by simp [Fs.squeeze, capOf]⟩

namespace LayerData

variable {D : LayerData} {first : ℕ} {rd : Reader}

/-- **The stream's parts**: the product at the cursor, the position rounds' messages and `t`
after the pack rounds' messages. -/
theorem xs_split (hpl : D.product.length = 47) (hpm : D.packMsgs.length = D.y)
    (hlm : D.localMsgs.length = 11) {cur : E} (h : ReadsAt rd cur D.xs) :
    ReadsAt rd cur D.product ∧
      ReadsAt rd (cur * gen ^ (47 + 2 * D.y)) (D.localMsgs.flatMap fun m ↦ [m.1, m.2.1, m.2.2]) ∧
      ReadsAt rd (cur * gen ^ (47 + 2 * D.y + 33)) [D.t.1, D.t.2.1, D.t.2.2] := by
  simp only [xs, List.append_assoc] at h
  rw [readsAt_append, readsAt_append, readsAt_append] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [flatMap_pairs_length, hpm, hpl, mul_assoc, ← pow_add] at h3
  rw [flatMap_pairs_length, flatMap_triples_length, hlm, hpm, hpl, mul_assoc, ← pow_add,
    mul_assoc, ← pow_add] at h4
  exact ⟨h1, h3, by convert h4 using 2⟩

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

set_option maxRecDepth 20000 in
/-- **A layer's body, completely.** -/
theorem layer_body_complete {first : ℕ} (hf : first < 2) (D : LayerData)
    {rd : Reader} {w : ℕ → E} {p0 p1 cur claim out iota : E} {cw : List E}
    (hcl : D.cap.length = 5) (hcap : AllCanonical D.cap)
    (hw : first = 1 → (p0, p1) = Keccak.scalarCells D.w0 dsObserve)
    (hy1 : 1 ≤ D.y) (hy30 : D.y ≤ 30) (hpl : D.product.length = 47)
    (hpm : D.packMsgs.length = D.y) (hlm : D.localMsgs.length = 11)
    (hproj : projectedOf D.c D.product + iota * sumE D.c.mu = D.c.value)
    (hfin : LayerFinal D.c (D.s0 first) D.product D.packMsgs D.localMsgs D.t)
    (hcr : ClaimRec rd (first = 1) claim D.c D.y) (hcw : ReadsAt rd claim cw)
    (hcwl : 22 ≤ cw.length) (hxs : ReadsAt rd cur D.xs)
    (hpt : ReadsAt rd (w 1052) (D.chs first)) (hrec : ReadsAt rd (w 1053) (D.recWords first cur))
    (hloc : ReadsAt rd (w 1081) (D.locPt first))
    (hlan : ReadsAt rd (w (weightEnd first + 33)) (lanesOut (D.locPt first) (D.beta first).1))
    (hfl : ReadsAt rd (w (topV (weightEnd first) + 3))
      (flipsOf (laterWeights (lanesOut (D.locPt first) (D.beta first).1)
        (eqKernel ((D.locPt first).take 6)))))
    (hout : ReadsAt rd out (D.outW first (w 1052) (w (weightEnd first + 33)) (w 1081)
      (w (topV (weightEnd first) + 3))))
    (hloop : 1 + gen ^ (D.y / 8) ≠ 0 → coreProgram.Rel rd (packLoopName first)
      [1, gen ^ (D.y / 8), w 1053, cw.getD 2 0, w 1052] [])
    (hrem : 1 + gen ^ (D.y % 8) ≠ 0 → coreProgram.Rel rd (remLoopName first)
      [1, gen ^ (D.y % 8), w 1053 * gen ^ (D.y / 8), cw.getD 2 0 * (gen ^ (D.y / 8)) ^ 8,
        w 1052 * (gen ^ (D.y / 8)) ^ 8] []) :
    let σ := layerσ rd w (D.cap ++ [p0, p1, cur, gen ^ D.y, gen ^ (D.y / 8),
      gen ^ (D.y % 8), claim, out, iota]) first
    (σ (.n 1072) = w 1053 * gen ^ (D.y / 8) * gen ^ (D.y % 8) ∧
      σ (.n 1078) = cur * gen ^ (47 + 2 * D.y) ∧
      σ (.n 1841) = cw.getD 3 0 ∧
      (first = 0 → σ (.n 1842) = cw.getD 4 0) ∧ σ (.n 1051) = cw.getD 2 0) ∧
    Stmt.HoldsList (coreProgram.Rel rd) rd σ (layerT first) False
      (fun r ↦ r = D.rets first cur) := by
  intro σ'
  obtain ⟨f0, f1, f2, f3, f4, hcapE⟩ := five_of_length' hcl
  have hl : (D.cap ++ [p0, p1, cur, gen ^ D.y, gen ^ (D.y / 8), gen ^ (D.y % 8), claim,
      out, iota]).length = 14 := by simp [hcl]
  have hG := layer_good (rd := rd) (w := w) hf hl
  have hpar := fun i (hi : i < 14) ↦ layer_param (rd := rd) (w := w) hf hl hi
  have hσ := fun v ↦ layerσ_idx (rd := rd) (w := w) (first := first)
    (args := D.cap ++ [p0, p1, cur, gen ^ D.y, gen ^ (D.y / 8), gen ^ (D.y % 8),
    claim, out, iota]) v
  generalize hσ' : layerσ rd w (D.cap ++ [p0, p1, cur, gen ^ D.y, gen ^ (D.y / 8),
    gen ^ (D.y % 8), claim, out, iota]) first = σ at hG hpar hσ
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
  clear hpar
  rw [layerT_sections] at hG ⊢
  have hNS := layer_noStore hf
  have hS7 := not_mem_of_noStoreVia hNS (p := .n 7) (by simp)
  have hS11 := not_mem_of_noStoreVia hNS (p := .n 11) (by simp)
  have hS72 := not_mem_of_noStoreVia hNS (p := .n 1072) (by simp)
  have hS78 := not_mem_of_noStoreVia hNS (p := .n 1078) (by simp)
  obtain ⟨hRe, hRw, hRt, hRtop, hRf, hRfl⟩ := layer_residOk hf
  -- the claim's record
  obtain ⟨hmuL, hptL, hval, hkap, hmus, ⟨pp, hpp, hppR⟩, lp, lanes, hlp, hlanesL, hlanesR, hwts⟩ :=
    hcr
  have hcw' : ∀ k < 22, LoadHolds rd claim k (cw.getD k 0) := fun k hk ↦ by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hcw k (by omega)
  have elp : cw.getD 3 0 = lp := loadHolds_unique (hcw' 3 (by norm_num)) hlp
  -- the stream
  obtain ⟨hxP, hxL, hxT⟩ := LayerData.xs_split hpl hpm hlm hxs
  -- the sections' equations
  have gA : ∀ s ∈ secA1 first ++ secA2 first, GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by rcases List.mem_append.mp hs with h | h <;> simp [h])
  have gR : ∀ s ∈ rmfeBlockT, GoodS rd (layerSt first) w σ s := fun s hs ↦ hG s (by simp [hs])
  have gH : ∀ s ∈ hornerS first, GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by simp [hs])
  have gP : ∀ s ∈ packSetupT first, GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by simp [hs])
  have gL : ∀ s ∈ lastT, GoodS rd (layerSt first) w σ s := fun s hs ↦ hG s (by simp [hs])
  have gLR : ∀ s ∈ localS, GoodS rd (layerSt first) w σ s := fun s hs ↦ hG s (by simp [hs])
  have gT : ∀ s ∈ tReadsT, GoodS rd (layerSt first) w σ s := fun s hs ↦ hG s (by simp [hs])
  have gE : ∀ s ∈ eqfS, GoodS rd (layerSt first) w σ s := fun s hs ↦ hG s (by simp [hs])
  have gW : ∀ s ∈ weightT first, GoodS rd (layerSt first) w σ s := fun s hs ↦
    hG s (by simp [hs])
  have gTl : ∀ s ∈ tailT (weightEnd first) (weightVal first),
      GoodS rd (layerSt first) w σ s := fun s hs ↦ hG s (by simp [hs])
  -- the product and `s`
  have HA : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (secA1 first ++ secA2 first) next kret :=
    fun hn ↦ layerA_complete (C := coreProgram.Rel rd) hf hσ gA (hS7 · ·) (hS11 · ·)
    (fun i hi ↦ by
      have := hcap (D.cap.getD i 0) (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
      rw [hcapE] at this
      interval_cases i
      · rwa [a0]
      · rwa [a1]
      · rwa [a2]
      · rwa [a3]
      · rwa [a4])
    (w0 := D.w0) (fun h1 ↦ by rw [a5, a6]; exact hw h1) (c := D.c) hmuL (by rw [a11]; exact hval)
    (by rw [a11]; exact hkap) (fun i hi ↦ by rw [a11]; exact hmus i hi) hpl (by rw [a7]; exact hxP)
    (by rw [a13]; exact hproj) hn
  obtain ⟨hrd, -, hsq, -⟩ := layerA_holds (rd := rd) (σ := σ) (C := coreProgram.Rel rd)
    (next := True) (kret := fun _ ↦ True) hf
    (c := D.c) (y := D.y) (w := D.w0)
    (by rw [a11]; exact ⟨hmuL, hptL, hval, hkap, hmus, ⟨pp, hpp, hppR⟩, lp, lanes, hlp, hlanesL,
      hlanesR, hwts⟩)
    (fun h1 _ ↦ by rw [a5, a6]; exact hw h1)
    (by have := HA (next := True) (kret := fun _ ↦ True) trivial
        simpa only [secA1, secA2, List.append_assoc] using this)
  have hprodE := prodTab_a_eq hf hpl (by rw [a7]; exact hxP) hrd
  rw [hprodE, show plainStart first [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)] D.w0 =
    D.s0 first by rw [a0, a1, a2, a3, a4, LayerData.s0, hcapE]] at hsq
  have e877 : σ (.n 877) = D.sv first := by rw [LayerData.sv, hsq]
  have ecapS : (cap5 866).map σ = D.capS first := by rw [LayerData.capS, hsq]
  -- the instance weights
  have HR : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (coreProgram.Rel rd) rd σ rmfeBlockT next kret :=
    fun hn ↦ rmfe_complete (C := coreProgram.Rel rd) hσ gR
    (fun i hi ↦ by
      rw [a12, e877, ← outW_mu]
      exact kk_readsAt_getD hout (by simp [LayerData.outW, LayerData.next, layerClaim,
        keccakInstanceWeights_length]; omega))
    (by
      rw [a12, e877]
      have := kk_readsAt_getD hout (k := 1) (by simp [LayerData.outW])
      simpa [LayerData.outW, LayerData.next, layerClaim, LayerData.sv] using this) hn
  -- the product at `s`
  have HH : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (hornerS first) next kret :=
    fun hn ↦ horner_complete (C := coreProgram.Rel rd) hf hσ gH hn
  have e1050 : σ (.n 1050) = polyEval D.product (D.sv first) := by
    obtain ⟨hl47, -⟩ := prodTab_facts first hf
    have := (hornerT_holds (cs := D.product) hpl (fun k hk ↦ by
      rw [← hprodE]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (show k < (prodTab first).length by omega), Option.map_some,
        Option.getD_some]) (HH (next := True) (kret := fun _ ↦ True) trivial)).1
    rwa [e877] at this
  -- the pack rounds' setup
  have g1053 : σ (.n 1053) = w 1053 := gP (.atom (.hint (.alloc (.n 1053) 128))) (by simp [packSetupT])
  have g1052 : σ (.n 1052) = w 1052 :=
    gP (.atom (.hint (.allocDyn (.n 1052) (.n 8)))) (by simp [packSetupT])
  have hrec0 : RoundRec rd (σ (.n 1053)) 0 ((cap5 866).map σ) (σ (.n 7) * gen ^ 47)
      (σ (.n 1050)) 1 := by
    have := LayerData.recWords_rec hrec (j := 0) (by norm_num) (by omega)
    rw [g1053, ecapS, a7, e1050]
    simpa [LayerData.recK, LayerData.run_zero, LayerData.recCur] using this
  obtain ⟨e1051, e1060, HP⟩ := packSetup_complete (C := coreProgram.Rel rd) gP (hS11 _ _)
    (pp := cw.getD 2 0) (by rw [a11]; exact hcw' 2 (by norm_num)) hrec0
    (by rw [a9]; exact one_add_gen_pow_isInK _)
    (fun hne ↦ by rw [a9, g1053, g1052]; exact hloop (by rwa [a9] at hne))
    (by rw [a10]; exact one_add_gen_pow_isInK _)
    (fun hne ↦ by rw [a9, a10, g1053, g1052]; exact hrem (by rwa [a10] at hne))
  -- the last record
  have hkm : D.recK (D.y / 8 + D.y % 8) = D.y := by unfold LayerData.recK; split <;> omega
  have hrecm := LayerData.recWords_rec hrec (j := D.y / 8 + D.y % 8) (by omega) (by omega)
  rw [hkm, LayerData.run_full hpm] at hrecm
  have hcur : D.recCur cur (D.y / 8 + D.y % 8) = cur * gen ^ (47 + 2 * D.y) := by
    simp [LayerData.recCur, hkm]
  rw [hcur] at hrecm
  obtain ⟨e1072, ecapL, e1078, e1079, e1080, HL⟩ := last_complete (C := coreProgram.Rel rd) hσ gL
    (hS72 · ·) (by rw [e1060, g1053, a9, a10, mul_assoc, ← pow_add]; exact hrecm)
  have g1081 : σ (.n 1081) = w 1081 :=
    gL (.atom (.hint (.alloc (.n 1081) 11))) (by unfold lastT; exact List.mem_append_right _ (by simp))
  -- the position rounds
  have hpk := LayerData.run_cap (D := D) (first := first) D.y
  rw [LayerData.run_full hpm] at hpk
  have eLoc : localRunF D.localMsgs (σ (.n 1079)) ⟨(cap5 1073).map σ, []⟩ = D.loc first := by
    rw [e1079, ecapL, LayerData.loc, layerLocal]
    conv_rhs => rw [show layerPack D.c (D.s0 first) D.product D.packMsgs = D.pack first from rfl,
      hpk.2]
  obtain ⟨hvR, hcR, HLR⟩ := localRounds_complete (C := coreProgram.Rel rd)
    (cur := .n 1078) (loc := .n 1081) (vIn := .n 1079) (capV := cap5 1073) (a0 := 1082)
    (by rw [ecapL]; exact hpk.1.2) (hS78 · ·) 11 D.localMsgs hlm (by norm_num) gLR
    (by rw [e1078]; exact hxL)
  rw [eLoc] at hvR hcR HLR
  -- `t`
  have hT : ∀ k < 3, LoadHolds rd (σ (.n 1078)) (33 + k) ([D.t.1, D.t.2.1, D.t.2.2].getD k 0) := by
    intro k hk
    rw [e1078, ← loadHolds_mul_gen_pow, mul_assoc, ← pow_add]
    exact kk_readsAt_getD hxT (by simp; omega)
  obtain ⟨et0, et1, et2, HT⟩ := tReads_complete (C := coreProgram.Rel rd) gT (hS78 · ·)
    (by simpa using hT 0 (by norm_num)) (by simpa using hT 1 (by norm_num))
    (by simpa using hT 2 (by norm_num))
  -- the lane weights of the local point
  have hlocL : (D.locPt first).length = 11 := by
    rw [LayerData.locPt, LayerData.loc, layerLocal, localRunF_length, hlm]
  have hlocσ : ReadsAt rd (σ (.n 1081)) (D.locPt first) := by rw [g1081]; exact hloc
  have HE : ∀ {next : Prop} {kret : List E → Prop}, next →
      Stmt.HoldsList (coreProgram.Rel rd) rd σ eqfS next kret :=
    fun hn ↦ eqf_complete hσ gE (not_mem_of_noneIn hRe) hlocL hlocσ hn
  obtain ⟨⟨rs, hrsL, hrs, hent⟩, -⟩ := eqfT_holds (C := coreProgram.Rel rd) (rd := rd) (σ := σ)
    (pt := .n 1081) (off := 6) (n := 5) (count := 25) (b := 1772)
    (by norm_num) (by norm_num) (by decide) (by decide) (HE (next := True) (kret := fun _ ↦ True) trivial)
  have hrs6 : rs = (D.locPt first).drop 6 := by
    apply List.ext_getElem (by simp [hrsL, hlocL])
    intro k h1 h2
    rw [List.getElem_drop]
    exact loadHolds_unique (hrs k h1) (hlocσ (6 + k) (by omega))
  have hfw : ∀ i < 25, σ (.n (laneW i)) = eqAt ((D.locPt first).drop 6) i := by
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
      Stmt.HoldsList (coreProgram.Rel rd) rd σ (weightT first) next kret :=
    fun hn ↦ weight_complete hf hσ gW (not_mem_of_noneIn hRw) (by rw [a11]; exact hcw) hcwl
      hlanesL (by rw [elp]; exact hlanesR) hlocL hlocσ hlc hn
  have hWk : WeightOk first := by
    interval_cases first
    · exact weightOk_zero
    · exact weightOk_one
  obtain ⟨hwv, -⟩ := hWk (coreProgram.Rel rd) rd σ D.c D.y (D.locPt first) True
    (fun _ ↦ True) (by rw [a11]; exact ⟨hmuL, hptL, hval, hkap, hmus, ⟨pp, hpp, hppR⟩, lp, lanes,
      hlp, hlanesL, hlanesR, hwts⟩) hlocL hlocσ hfw (HW trivial)
  -- the tail
  have gTP : ∀ s ∈ tailPre (weightEnd first) (weightVal first),
      GoodS rd (layerSt first) w σ s := fun s hs ↦ gTl s (by
    rw [tailT_split]; exact List.mem_append_left _ hs)
  have gT0 := fun s hs ↦ gT s (List.mem_append_left _ (List.mem_append_left _ hs))
  have gT1 := fun s hs ↦ gT s (List.mem_append_left _ (List.mem_append_right _ hs))
  have gT2 := fun s hs ↦ gT s (List.mem_append_right _ hs)
  have v0 := fsPack_vals_of_good (fun s hs ↦ gT0 s (List.mem_cons_of_mem _ hs))
  have v1 := fsPack_vals_of_good (fun s hs ↦ gT1 s (List.mem_cons_of_mem _ hs))
  have v2 := fsPack_vals_of_good (fun s hs ↦ gT2 s (List.mem_cons_of_mem _ hs))
  have hcanL := localRunF_cap_canonical D.localMsgs (D.pack first).1.1 ⟨(D.pack first).2.cap, []⟩
    (by rw [← List.length_pos_iff]; omega)
  have hcR' : (D.loc first).2.cap = (cap5 1722).map σ := by rw [hcR]; rfl
  have hcanR : AllCanonical ((cap5 1722).map σ) := by
    rw [← hcR', LayerData.loc, layerLocal]
    have := hcanL.1
    rwa [show layerPack D.c (D.s0 first) D.product D.packMsgs = D.pack first from rfl, hpk.2]
  have hA : ∀ i ∈ tailA, IsCanonical128 (σ (.n i)) := by
    intro i hi
    have c0 := fsPackVals_canonical (σ (.n 1742)) dsObserve
    have c1 := fsPackVals_canonical (σ (.n 1752)) dsObserve
    have c2 := fsPackVals_canonical (σ (.n 1762)) dsObserve
    have cap : ∀ j < 5, IsCanonical128 (σ (.n (1722 + j))) := fun j hj ↦ by
      have := hcanR _ (List.mem_map_of_mem (f := σ) (show V.n (1722 + j) ∈ cap5 1722 by
        simp only [cap5, List.mem_cons, List.not_mem_nil, or_false]
        interval_cases j <;> simp))
      exact this
    simp only [tailA, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show (1749 : ℕ) = 1742 + 1 + 6 by norm_num, v0 6 (by norm_num)]; exact c0.1
    · rw [show (1751 : ℕ) = 1742 + 1 + 8 by norm_num, v0 8 (by norm_num)]; exact c0.2
    · rw [show (1759 : ℕ) = 1752 + 1 + 6 by norm_num, v1 6 (by norm_num)]; exact c1.1
    · rw [show (1761 : ℕ) = 1752 + 1 + 8 by norm_num, v1 8 (by norm_num)]; exact c1.2
    · rw [show (1769 : ℕ) = 1762 + 1 + 6 by norm_num, v2 6 (by norm_num)]; exact c2.1
    · rw [show (1771 : ℕ) = 1762 + 1 + 8 by norm_num, v2 8 (by norm_num)]; exact c2.2
    · exact cap 0 (by norm_num)
    · exact cap 1 (by norm_num)
    · exact cap 2 (by norm_num)
    · exact cap 3 (by norm_num)
    · exact cap 4 (by norm_num)
  obtain ⟨-, hv958⟩ := rmfe_vals hσ gR
  have hfin' : σ (.n 1080) * σ (.n (weightVal first)) *
      (σ (.n 958) * σ (.n 1742) + (σ (.n 958) + σ (.n 1752)) * σ (.n 1762)) =
      σ (.n 1741) := by
    rw [e1080, hwv, hv958, e877, et0, et1, et2,
      show 1082 + 60 * (11 - 1) + 59 = 1741 by norm_num] at *
    rw [← hvR]
    exact hfin
  obtain ⟨eβ, ecapB, HTl⟩ := layer_tail_complete (C := coreProgram.Rel rd) hf hσ gTP
    (not_mem_of_noneIn hRt) (not_mem_of_noneIn hRtop _ (by simp))
    (fun i hi ↦ not_mem_of_noneIn (hRf i hi))
    (fun i hi ↦ List.contains_iff_mem.mp (hRfl i hi)) hA
    (fsPackOk_of_vals v0) (fsPackOk_of_vals v1) (fsPackOk_of_vals v2) hlocL hlocσ hfw hfin'
  have eTail : tailSq σ = D.beta first := by
    have ecv : localRoundsT.capV' (1082 + 60 * (11 - 1) + 40) = cap5 1722 := rfl
    rw [LayerData.beta, layerBeta, show layerLocal D.c (D.s0 first) D.product D.packMsgs
      D.localMsgs = D.loc first from rfl, hcR, ecv, tailSq, sq3, et0, et1, et2]
  rw [eTail] at eβ ecapB HTl
  have g33 : σ (.n (weightEnd first + 33)) = w (weightEnd first + 33) :=
    gTP (.atom (.hint (.alloc (.n (weightEnd first + 33)) 25))) (by
      simp [tailPre, tailA1, tailP2])
  have gfl : σ (.n (topV (weightEnd first) + 3)) = w (topV (weightEnd first) + 3) :=
    gTP (.atom (.hint (.alloc (.n (topV (weightEnd first) + 3)) 7))) (by
      simp [tailPre, tailA1, tailTop])
  have ho' : ∀ k < 6, LoadHolds rd (σ (.n 12)) k ((D.outW first (w 1052)
      (w (weightEnd first + 33)) (w 1081) (w (topV (weightEnd first) + 3))).getD k 0) :=
    fun k hk ↦ by rw [a12]; exact kk_readsAt_getD hout (by simp [LayerData.outW]; omega)
  have e1841 : σ (.n 1841) = cw.getD 3 0 := by
    have g := gW (.atom (.load (.n 1841) (.n 11) 3)) (by unfold weightT; split <;> simp)
    exact load_val (w := w) g (hS11 _ _) (by rw [a11]; exact hcw' 3 (by norm_num))
  have e1842 : first = 0 → σ (.n 1842) = cw.getD 4 0 := by
    intro h0
    have g := gW (.atom (.load (.n 1842) (.n 11) 4)) (by unfold weightT; simp [h0])
    exact load_val (w := w) g (hS11 _ _) (by rw [a11]; exact hcw' 4 (by norm_num))
  refine ⟨⟨by rw [e1072, e1060, g1053, a9, a10], e1078, e1841, e1842, e1051⟩, ?_⟩
  -- the sections in turn
  rw [← List.append_assoc, holdsList_append]
  refine HA ?_
  rw [holdsList_append]; refine HR ?_
  rw [holdsList_append]; refine HH ?_
  rw [holdsList_append]; refine HP ?_
  rw [holdsList_append]; refine HL ?_
  rw [holdsList_append]; refine HLR (by rw [g1081]; exact hloc) ?_
  rw [holdsList_append]; refine HT ?_
  rw [holdsList_append]; refine HE ?_
  rw [holdsList_append]; refine HW ?_
  refine HTl ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have := ho' 0 (by norm_num)
    simpa [LayerData.outW, LayerData.next, layerClaim, LayerData.beta, et0, et1, et2] using this
  · have := ho' 2 (by norm_num)
    simpa [LayerData.outW, g1052] using this
  · have := ho' 4 (by norm_num)
    simpa [LayerData.outW, g1081] using this
  · have := ho' 3 (by norm_num)
    simpa [LayerData.outW, g33] using this
  · rw [g33]; exact hlan
  · have := ho' 5 (by norm_num)
    simpa [LayerData.outW, gfl] using this
  · rw [gfl]; exact hfl
  · rw [ecapB, e1078, LayerData.rets, mul_assoc, ← pow_add]

end
end LeanVM.Guest.B1.VerifySub
