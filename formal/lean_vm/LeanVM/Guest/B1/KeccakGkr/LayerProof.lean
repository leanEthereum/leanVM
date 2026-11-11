/-
  LeanVM.Guest.B1.KeccakGkr.LayerProof

  `keccak_layer`'s two specializations against `MeaningKeccakLayer`, from the template's
  sections; the weight section enters as `WeightOk first o`.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.LayerSecA
public import LeanVM.Guest.B1.KeccakGkr.LayerSecB
public import LeanVM.Guest.B1.KeccakGkr.LayerSecC
public import LeanVM.Guest.B1.KeccakGkr.LayerWeight1

/-!
# A layer, assembled

`layer_sound`: a specialization whose body is `layerT first`, given `WeightOk first (layOff first)`
(the weight section computes the claim's weights against the local point's equality weights) and
`grind_check`'s meaning at `3` bits on the window table, meets `MeaningKeccakLayer first`: its
sections give the facts `LayerW` collects, and `layer_of_w` turns them into the meaning.
`weightOk_one`: the first claim's weight section.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr Finset

@[expose] public section

/-- **What the weight section must compute**: from the claim's record and the local point (at
`loc`, `o + 748`, its lane weights at `laneW o`), the weight value is the claim's weights against
the local point's equality weights. -/
def WeightOk (first o : ℕ) : Prop :=
  ∀ (C : CallRel) (rd : Reader) (σ : Val) (c : KeccakClaim) (y : ℕ) (locPt : List E)
    (next : Prop) (kret : List E → Prop),
    ClaimRec rd (first = 1) (σ (.n 11)) c y → locPt.length = 11 →
    ReadsAt rd (σ (.n (o + 748))) locPt →
    (∀ i < 25, σ (.n (laneW o i)) = eqAt (locPt.drop 6) i) →
    Stmt.HoldsList C rd σ (weightT first o) next kret →
    σ (.n (weightVal first o)) = dot ((eqKernel locPt).take keccakBits) c.weights ∧ next

/-- **The first claim's weight section** (G:2803-2809). -/
theorem weightOk_one (o : ℕ) : WeightOk 1 o := by
  intro C rd σ c y locPt next kret hcr hlocL hloc hf h
  obtain ⟨-, -, -, -, -, -, lp, lanes, hlp, hlen, hlanes, hw⟩ := hcr
  simp only [decide_true, ↓reduceIte] at hw
  simp only [weightT, ↓reduceIte, Stmt.HoldsList, Stmt.Holds, Atom.Holds] at h
  obtain ⟨hl3, h⟩ := h
  rw [← loadHolds_unique hl3 hlp] at hlanes
  obtain ⟨hv, hn⟩ := lanesEqT_holds (fl := locPt.drop 6) hf hlanes hlen hloc hlocL h
  refine ⟨?_, hn⟩
  rw [show weightVal 1 o = o + 1191 + 109 by simp [weightVal], hv, hw,
    firstWeight_eq locPt lanes hlocL]

theorem fsNext_load {cur : V} {off b : ℕ} {next : Prop} {kret : List E → Prop} {C : CallRel}
    {rd : Reader} {σ : Val} (h : Stmt.HoldsList C rd σ (fsNextT cur off b) next kret) :
    (LoadHolds rd (σ cur) off (σ (.n b)) ∧ FsPackOk σ (.n b) (b + 1) dsObserve) ∧ next :=
  (holds_fsNextT cur off b next kret).1 h

/-- **A layer, assembled.** -/
theorem layer_sound {first : ℕ} (hf : first < 2) (hW : WeightOk first (layOff first))
    {fn : Fn} (hfind : coreProgram.find? (layerName first) = some fn)
    (hbody : fn.body = layerT first)
    (hparams : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10,
      .n 11, .n 12, .n 13, .n 14])
    (rd : Reader)
    (hgr : ∀ w tabs : E, WinTabs rd tabs → coreProgram.Rel rd (grindCheckName 3) [w, tabs] [] →
      (w.limb 0).lane.toNat % 2 ^ 3 = 0)
    (args rets : List E) (h : coreProgram.Rel rd (layerName first) args rets) :
    MeaningKeccakLayer first rd args rets := by
  obtain ⟨σ, hpar, hb⟩ := (rel_iff_sem hfind args rets).mp h
  rw [hparams] at hpar
  simp only [List.map_cons, List.map_nil] at hpar
  subst hpar
  simp only [MeaningKeccakLayer]
  intro htabs y step c w hy1 hy32 hyg hsg hrg hcr hw hiota
  rw [hbody, layerT] at hb
  rw [holdsList_append, holdsList_append, holdsList_append, holdsList_append, holdsList_append,
    holdsList_append, holdsList_append, holdsList_append, holdsList_append] at hb
  generalize ho : layOff first = o at hb hW
  have hoff : LayOff o := by
    subst ho
    interval_cases first
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- the product, the grind and `s`
  replace hb := layerA_holds hf hcr hw (fun w' hw' ↦ hgr w' _ htabs hw') hb
  rw [ho] at hb
  obtain ⟨hrd, hproj, hnl, hgrind, hsq, hb⟩ := hb
  obtain ⟨hl, -, -, -, -⟩ := prodTab_facts first hf
  -- the instance weights
  obtain ⟨hmuOut, hkapOut⟩ := rmfeBlock_holds hoff hb
  have hkap := atom_of_block (rmfeBlock_atoms o) hb _ (rmfeBlock_kappa hoff)
  simp only [Atom.Holds] at hkap
  replace hb := ((holdsList_atoms (allAtoms_of_all (rmfeBlock_atoms o)) _ _).1 hb).2
  -- Horner
  replace hb := hornerT_holds (cs := (prodTab first).map fun p ↦ σ (.n p.a))
    (by simp [hl]) (fun k hk ↦ by
      rw [List.getD_eq_getElem ((prodTab first).map _) _ (by simp [hl]; omega), List.getElem_map,
        List.getD_eq_getElem (prodTab first) _ (by omega)]) hb
  obtain ⟨hhor, hb⟩ := hb
  have e717 : σ (.n (o + 717)) =
      polyEval ((prodTab first).map fun p ↦ σ (.n p.a)) (σ (.n (o + 544))) := hhor
  clear hhor
  have hprodL : ((prodTab first).map fun p ↦ σ (.n p.a)).length = productBits := by simp [hl]; rfl
  generalize (prodTab first).map (fun p ↦ σ (.n p.a)) = prod at hrd hproj hsq e717 hprodL hgrind
  clear hl
  -- the pack rounds
  replace hb := packSetupT_holds hb
  obtain ⟨hpp, hrec0, hik, hloopC, e727, hik', hremC, hb⟩ := hb
  replace hb := lastT_holds hb
  obtain ⟨e739, hlastR, hb⟩ := hb
  -- the local rounds
  replace hb := localRounds_run (cap := (cap5 (o + 740)).map σ) rfl 11 (by omega) hb
  obtain ⟨⟨msgs, hmL, hmR, hlocR, hvR, hcapR⟩, hb⟩ := hb
  simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.add_assoc] at hvR hcapR
  -- `t`
  rw [tReadsT, holdsList_append, holdsList_append] at hb
  replace hb := fsNext_load hb
  obtain ⟨⟨lt0, p1⟩, hb⟩ := hb
  replace hb := fsNext_load hb
  obtain ⟨⟨lt1, p2⟩, hb⟩ := hb
  replace hb := fsNext_load hb
  obtain ⟨⟨lt2, p3⟩, hb⟩ := hb
  -- the lane weights of the local point
  replace hb := eqfT_holds (by omega) (by omega) (by decide) (by decide) hb
  obtain ⟨⟨rs, hrsL, hrs, hent⟩, hb⟩ := hb
  generalize hlp : (localRunF msgs (σ (.n (o + 746))) ⟨(cap5 (o + 740)).map σ, []⟩).1.1 = locPt
    at hlocR
  have hlocL : locPt.length = 11 := by rw [← hlp, localRunF_length, hmL]
  have hrs6 : rs = locPt.drop 6 := by
    apply List.ext_getElem (by simp [hrsL, hlocL])
    intro k h1 h2
    rw [List.getElem_drop]
    exact loadHolds_unique (hrs k h1) (hlocR (6 + k) (by omega))
  have hf' : ∀ i < 25, σ (.n (laneW o i)) = eqAt (locPt.drop 6) i := by
    intro i hi
    rw [← hrs6]
    exact hent i hi
  clear hrs hent hrs6
  -- the weight
  replace hb := hW _ rd σ c y locPt _ _ hcr hlocL hlocR hf' hb
  obtain ⟨hwv, hb⟩ := hb
  -- the tail
  generalize weightEnd first o = WE at hb
  generalize weightVal first o = WV at hb hwv
  replace hb := tailT_holds hlocL hlocR hf' p1 p2 p3 hb
  obtain ⟨hfinal, hbeta, hout0, hout2, hout4, hout3, hlanes, hout5, hflips, hret⟩ := hb
  have hk625 : σ (.n (o + 625)) = sumE (keccakInstanceWeights (σ (.n (o + 544)))) :=
    loadHolds_unique hkap hkapOut
  rw [e739, e727] at hlastR
  have W : LayerW first rd (σ (.n 0)) (σ (.n 1)) (σ (.n 2)) (σ (.n 3)) (σ (.n 4)) (σ (.n 7))
      (σ (.n 9)) (σ (.n 10)) (σ (.n 11)) (σ (.n 12)) (σ (.n 13)) rets c w :=
    { prod := prod
      hprodL := hprodL
      hprod := hrd
      hproj := hproj
      nonce := σ (.n (nonceV first))
      hnonce := hnl
      hgrind := hgrind
      sv := σ (.n (o + 544))
      capS := (cap5 (o + 539)).map σ
      hsq := hsq
      hmuOut := hmuOut
      hkapOut := hkapOut
      rc := σ (.n (o + 720))
      pt := σ (.n (o + 719))
      pp := σ (.n (o + 718))
      hpp := hpp
      tb := σ (.n 14)
      h0 := by rw [← e717, show productBits + 1 = 48 from rfl]; exact hrec0
      hloop := ⟨hik, hloopC⟩
      hrem := ⟨hik', hremC⟩
      capL := (cap5 (o + 740)).map σ
      curL := σ (.n (o + 745))
      vL := σ (.n (o + 746))
      scL := σ (.n (o + 747))
      hlast := hlastR
      msgs := msgs
      hmsgsL := hmL
      hmsgs := hmR
      loc := σ (.n (o + 748))
      locPt := locPt
      vR := σ (.n (o + 1111))
      capR := (cap5 (o + 1098)).map σ
      hlocal := Prod.ext (Prod.ext hlp hvR) hcapR
      hloc := hlocR
      t0 := σ (.n (o + 1112))
      t1 := σ (.n (o + 1115))
      t2 := σ (.n (o + 1118))
      ht := by
        rw [readsAt_gen_pow_mul]
        intro k hk
        simp only [List.length_cons, List.length_nil] at hk
        interval_cases k
        · exact lt0
        · exact lt1
        · exact lt2
      hfin := by rw [← hk625, ← hwv]; exact hfinal
      beta := σ (.n (WE + 22))
      capB := (cap5 (WE + 17)).map σ
      hbeta := hbeta
      hout0 := hout0
      hout2 := hout2
      hout4 := hout4
      lo := σ (.n (WE + 27))
      fl := σ (.n (topV WE + 3))
      hout3 := hout3
      hlanes := hlanes
      hout5 := hout5
      hflips := hflips
      hrets := hret.symm }
  exact layer_of_w hf hy32 hsg hrg hcr hiota W

end
end LeanVM.Guest.B1.VerifySub
