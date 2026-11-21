module

public import NativeVm.Code.Phase7.FinalKit

/-!
# The final level

`finalC` refines `finalM` of the last level: the parameters, the fold rounds, `μ`, the folded
polynomial's count and elements, the queries, the openings, the subspace table, the queries' check,
the sumcheck from WHIR's running claim, the point, the basis at it, the weight's check.
-/

@[expose] public section

namespace NativeVm.Code.P7

open Native NativeVm.Model LeanVM.Parameters
open NativeVm.Transcript (wd Env wd_zero)

/-- Discharge the words' side conditions. -/
macro "finwtac" : tactic => `(tactic| (
  intro j hj
  try simp only [paramsW, muW, roundW, tableW, WB, WBe, gslot, basisWords, basis_off, vecWords,
      stackClaimCap, claimCap_val, levelsWords_val, BT.rowsWords_val] at *
  oomega))

variable {p : Par}

theorem finalC_b {L : List Whir.Level} {logN : Nat} {scales : Array EW} {sW : WhirStateW}
    {bc : Array UInt64} {layout : LayoutW} {rate : Nat} {claims : Array ColumnClaimW}
    {ood : StackClaimW} {target : EW} {coeffs point slices : Array EW}
    (hok : LadderOk logN L) (hq : ∀ lv ∈ L, 1 ≤ lv.queries) (hlog : logN = layout.stackLog)
    (h16 : 16 ≤ logN) (h30 : logN ≤ 30)
    (hW : WOk L (L.length - 1) sW)
    (hR : Regs p.s1.mem p.env.work bc layout rate claims ood target coeffs point slices)
    (hss : scales.size = (stackClaims layout target point coeffs claims ood).size) :
    Refines (fun t s ↦ Base p t s ∧ (LvB p L logN (L.length - 1) scales s.mem ∧
        WhirAt s.mem (whirR.at p.env.work) sW) ∧ True)
      finalC (finalM logN Whir.initialFold ⟨scales, stackClaims layout target point coeffs claims ood⟩
        (L.length - 1) (L.getD (L.length - 1) ⟨0, 0, 0⟩) sW)
      (fun _ t s ↦ Base p t s) (Err p) := by
  have hl6 : L.length ≤ 6 := hok.len.2
  have hK : L.length - 1 < L.length := by have := hok.len.1; omega
  obtain ⟨hg, ha, hgl⟩ := hW
  have hg10 : sW.glued.size ≤ gluedCap := by rw [hg, gluedCap_val]; omega
  unfold finalM
  rw [getD_lt hK]
  unfold finalC
  have hf := hok.folds _ hK
  have hrt := hok.rates _ hK
  have hfin := hok.final
  unfold muAfter at hfin hrt
  rw [sum_take_succ L hK, ← ha] at hf hrt hfin
  have hq1 := hq _ (List.getElem_mem hK)
  have hres : Whir.residualMaxLog = 5 := rfl
  rw [hres] at hfin
  generalize L.length - 1 = K at *
  -- the level's parameters
  refine pure_then (X' := fun m ↦ LvB p L logN K scales m ∧ WhirAt m (whirR.at p.env.work) sW)
    (R := fun s ↦ Prm p L[K] s.mem ∧ na p cK L[K].queries s.mem)
    ((dep_LvB hl6 _ _ _).and (dep_whirP sW hg10)) (by finwtac) (by finwtac) (fun _ h ↦ h)
    (fun t s hb hx _ ↦ (paramsC_spec hb.rdi hb.inp hb.workPtr hx.1.2.1 hx.1.1 hK).mono
      (fun _ h ↦ ⟨⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1⟩, h.2.2.2.1⟩, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩)
      (fun _ h ↦ h)) ?_
  -- the fold rounds
  refine m0_drop (X := fun m ↦ (LvB p L logN K scales m ∧ WhirAt m (whirR.at p.env.work) sW) ∧
      (Prm p L[K] m ∧ na p cK L[K].queries m)) (X' := fun m ↦ LvB p L logN K scales m ∧ (Prm p L[K] m ∧ na p cK L[K].queries m))
    (Y := fun (x : WhirStateW × Array FoldRoundW) m ↦ WRd p x.1 x.2 m)
    (R := fun x ↦ x.1.glued = sW.glued ∧ x.1.alphas.size = sW.alphas.size + L[K].fold ∧
      x.2.size = L[K].fold) (Wc := roundW)
    ((dep_LvB hl6 _ _ _).and ((dep_Prm _).and (dep_na _ _))) (by finwtac) (by finwtac)
    (by exact fun _ h ↦ ⟨h.1.1, h.2⟩)
    (fun m0 ↦ (foldRoundsC_b (p := p) (m0 := m0) (sW := sW) (n := L[K].fold) hf.2.1
        (by rw [stackCap_val]; omega)).mono
      (by exact fun t s ⟨hb, hm, hx, _⟩ ↦ ⟨hb, hm, hx.2.1.1, hx.1.2⟩)
      (by exact fun x t s ⟨hb, ⟨hw, hrs, ho⟩, h1, h2, h3⟩ ↦ ⟨hb, ⟨⟨hw, hrs⟩, h1, h2, h3⟩, ho⟩)
      (fun _ h ↦ h)) fun x hx ↦ ?_
  obtain ⟨sW1, rounds⟩ := x
  obtain ⟨hgl1, hal1, hrs1⟩ := hx
  dsimp only at hgl1 hal1 hrs1 ⊢
  set mu := logN - sW1.alphas.size with hmu
  have hmu5 : mu ≤ 5 := by omega
  have h2 : 2 ^ mu ≤ 32 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by omega) hmu5
    simpa using this
  -- `μ` and the queries' depth
  refine pure_then (X := fun m ↦ (LvB p L logN K scales m ∧ Prm p L[K] m ∧
      na p cK L[K].queries m) ∧ WRd p sW1 rounds m)
    (X' := fun m ↦ (na p cIdx K m ∧ EVec m (basisR.at p.env.work) stackClaimCap scales ∧
      WRd p sW1 rounds m) ∧ na p cFold L[K].fold m ∧ na p cK L[K].queries m)
    (R := fun s ↦ na p cMu mu s.mem ∧ na p cDepth (mu + L[K].logInvRate) s.mem) (Wc := muW)
    (((dep_na _ _).and ((dep_evec basisR.off _ _).and ((dep_whir sW1).and (dep_rounds rounds)))).and
      ((dep_na _ _).and (dep_na _ _))) (by finwtac) (by finwtac)
    (fun _ h ↦ ⟨⟨h.1.1.2.1, h.1.1.2.2.2.2, h.2⟩, h.1.2.1.1, h.1.2.2⟩)
    (fun t s hb hx _ ↦ (muC_spec hb.rdi hb.inp hb.workPtr hx.1.1.2.2.2.1 hx.2.1 hx.1.2.1.2.1
      (by omega) (by omega)).mono (fun _ h ↦ ⟨⟨h.1, h.2.1⟩, h.2.2.1, h.2.2.2.1⟩) (fun _ h ↦ h)) ?_
  -- the folded polynomial's count
  have d3 := (((dep_na (p := p) cIdx K).and ((dep_evec basisR.off stackClaimCap scales).and
    ((dep_whir sW1).and (dep_rounds rounds)))).and ((dep_na cFold L[K].fold).and
    (dep_na cK L[K].queries))).and ((dep_na cMu mu).and (dep_na cDepth (mu + L[K].logInvRate)))
  refine pure_then (X := fun m ↦ ((na p cIdx K m ∧ EVec m (basisR.at p.env.work) stackClaimCap scales ∧
      WRd p sW1 rounds m) ∧ na p cFold L[K].fold m ∧ na p cK L[K].queries m) ∧
      na p cMu mu m ∧ na p cDepth (mu + L[K].logInvRate) m)
    (R := fun s ↦ na p cJ (2 ^ mu + L[K].fold) s.mem) (Wc := fun j ↦ j = cJ)
    d3 (by finwtac) (by finwtac) (fun _ h ↦ h)
    (fun t s hb hx _ ↦ (cntC_spec hb.rdi hb.inp hb.workPtr hx.2.1 hx.1.2.1 (by omega) (by omega)).mono
      (fun _ h ↦ h) (fun _ h ↦ h)) ?_
  -- the folded polynomial
  have hn64 : 2 ^ mu + L[K].fold ≤ 64 := by omega
  have d4 := d3.and (dep_na (p := p) cJ (2 ^ mu + L[K].fold))
  refine m0_drop (X := fun m ↦ (((na p cIdx K m ∧ EVec m (basisR.at p.env.work) stackClaimCap scales ∧
      WRd p sW1 rounds m) ∧ na p cFold L[K].fold m ∧ na p cK L[K].queries m) ∧
      na p cMu mu m ∧ na p cDepth (mu + L[K].logInvRate) m) ∧ na p cJ (2 ^ mu + L[K].fold) m)
    (Y := fun xs m ↦ EWArr m (wd p.env.work hiO) xs) (R := fun xs ↦ xs.size = 2 ^ mu + L[K].fold)
    (Wc := fun k ↦ hiO ≤ k ∧ k < hiO + 128)
    d4 (by finwtac) (by finwtac) (fun _ h ↦ h)
    (fun m0 ↦ (readScalarsC_spec (p := p) (m0 := m0) (n := 2 ^ mu + L[K].fold) (by oomega)
        (by oomega) hn64).mono
      (by exact fun t s ⟨hb, hm, hx, _⟩ ↦ ⟨hb, hm, hx.2⟩)
      (by exact fun xs t s ⟨hb, ha, hs, ho⟩ ↦ ⟨hb, ⟨ha, hs⟩, ho.mono fun k hk ↦ ⟨hk.1, by omega⟩⟩)
      (fun _ h ↦ h)) fun folded hfs ↦ ?_
  -- the grind
  have d5 := d4.and (dep_ewarrB (p := p) hiO 64 (xs := folded) (by omega))
  refine (grind_then (p := p) (Rg := fun _ ↦ True) (bits := Whir.queryGrindingBits) (k := 17)
    (by decide) (by decide) rfl d5 (by finwtac) RegOk.true ?_ :)
  -- the queries
  refine m0_drop (X := fun m ↦ ((((na p cIdx K m ∧ EVec m (basisR.at p.env.work) stackClaimCap scales ∧
      WRd p sW1 rounds m) ∧ na p cFold L[K].fold m ∧ na p cK L[K].queries m) ∧
      na p cMu mu m ∧ na p cDepth (mu + L[K].logInvRate) m) ∧ na p cJ (2 ^ mu + L[K].fold) m) ∧
      EWArr m (wd p.env.work hiO) folded)
    (Y := fun qs m ↦ WVec m (wd p.env.work queriesR.off) queryCap qs)
    (R := fun qs ↦ qs.size = L[K].queries)
    (Wc := fun k ↦ queriesR.off ≤ k ∧ k < queriesR.off + wvecWords queryCap)
    d5 (by finwtac) (by finwtac) (fun _ h ↦ h)
    (fun m0 ↦ (sampleQueriesC_spec (p := p) (m0 := m0) (depth := mu + L[K].logInvRate)
        (count := L[K].queries) (by omega) (by omega) (by rw [queryCap_val]; omega)).mono
      (by exact fun t s ⟨hb, hm, hx, _⟩ ↦ ⟨hb, hm, hx.1.1.2.2, hx.1.1.1.2.2⟩)
      (by exact fun qs t s ⟨hb, hw, hs, ho⟩ ↦ ⟨hb, ⟨hw, hs⟩, ho⟩)
      (fun _ h ↦ h)) fun queries hqs ↦ ?_
  -- the openings
  have d6 := d5.and (dep_wvec (p := p) queriesR.off queries)
  refine m0_drop (X := fun m ↦ (((((na p cIdx K m ∧ EVec m (basisR.at p.env.work) stackClaimCap scales ∧
      WRd p sW1 rounds m) ∧ na p cFold L[K].fold m ∧ na p cK L[K].queries m) ∧
      na p cMu mu m ∧ na p cDepth (mu + L[K].logInvRate) m) ∧ na p cJ (2 ^ mu + L[K].fold) m) ∧
      EWArr m (wd p.env.work hiO) folded) ∧ WVec m (wd p.env.work queriesR.off) queryCap queries)
    (Y := fun words m ↦ RowsW p words queries.size m) (R := fun _ ↦ True)
    (Wc := fun j ↦ rowsR.off ≤ j ∧ j < rowsR.off + rowsWords ∨ j = tmpO + 24)
    d6 (by finwtac) (by finwtac) (fun _ h ↦ h)
    (fun m0 ↦ (queryC_spec (p := p) (m0 := m0) (k := K) (qs := queries) (by omega)
        (by omega)).mono
      (by exact fun t s ⟨hb, hm, hx, _⟩ ↦ ⟨hb, hm, hx.1.1.1.1.1.1, hx.2⟩)
      (by exact fun words t s ⟨w, hb, hr, hs, hw, hwd, ho⟩ ↦ ⟨hb, ⟨⟨w, hr, hs, hw, hwd⟩, trivial⟩, ho⟩)
      (fun _ h ↦ h)) fun words _ ↦ ?_
  -- the subspace table
  have d7 := d6.and (dep_RowsW (p := p) words queries.size)
  refine pure_then (X := fun m ↦ ((((((na p cIdx K m ∧ EVec m (basisR.at p.env.work) stackClaimCap scales ∧
      WRd p sW1 rounds m) ∧ na p cFold L[K].fold m ∧ na p cK L[K].queries m) ∧
      na p cMu mu m ∧ na p cDepth (mu + L[K].logInvRate) m) ∧ na p cJ (2 ^ mu + L[K].fold) m) ∧
      EWArr m (wd p.env.work hiO) folded) ∧ WVec m (wd p.env.work queriesR.off) queryCap queries) ∧
      RowsW p words queries.size m)
    (R := fun s ↦ TableAt s.mem (wd p.env.work tabO) (subspaceTable mu)) (Wc := tableW)
    d7 (by finwtac) (by finwtac) (fun _ h ↦ h)
    (fun t s hb hx _ ↦ tableC_spec hb.rdi hb.inp hb.workPtr hx.1.1.1.1.2.1 (by omega)) ?_
  -- the queries' check
  have d8 := d7.and (dep_table (p := p) mu (by omega))
  refine req_then (X := fun m ↦ (((((((na p cIdx K m ∧
      EVec m (basisR.at p.env.work) stackClaimCap scales ∧
      WRd p sW1 rounds m) ∧ na p cFold L[K].fold m ∧ na p cK L[K].queries m) ∧
      na p cMu mu m ∧ na p cDepth (mu + L[K].logInvRate) m) ∧ na p cJ (2 ^ mu + L[K].fold) m) ∧
      EWArr m (wd p.env.work hiO) folded) ∧ WVec m (wd p.env.work queriesR.off) queryCap queries) ∧
      RowsW p words queries.size m) ∧ TableAt m (wd p.env.work tabO) (subspaceTable mu))
    (R := fun _ ↦ True) (Wc := WB)
    d8 (by finwtac) (by finwtac) (fun _ h ↦ h) (fun t s hb hx _ ↦ ?_) ?_
  · obtain ⟨⟨⟨⟨⟨⟨⟨⟨hi, -, -, hr⟩, -, -⟩, hm, -⟩, hj⟩, hfo⟩, hqw⟩, ⟨w, hrw, hrs, hw, hwd⟩⟩, ht⟩ := hx
    exact WP.mono (finalCheckC_spec hb.rdi hb.inp hb.workPtr hi hm (by omega) hqw hrw hrs hw hwd hr
      hfo (by omega) (by rw [hfs]; exact hj) ht) (fun _ ⟨h1, h2, h3⟩ ↦ ⟨h1, trivial, h2, h3⟩)
      (fun _ ⟨h1, h2, _⟩ ↦ ⟨h1, h2⟩)
  -- what the rest reads
  refine Refines.mono (P := fun t s ↦ Base p t s ∧ (((EVec s.mem (basisR.at p.env.work) stackClaimCap scales ∧
      WhirAt s.mem (whirR.at p.env.work) sW1) ∧ na p cMu mu s.mem) ∧
      EWArr s.mem (wd p.env.work hiO) folded) ∧ True) ?_
    (by exact fun t s ⟨hb, ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hev, hw, _⟩, _, _⟩, hm, _⟩, _⟩, hfo⟩, _⟩, _⟩, _⟩, _⟩, _⟩ ↦
      ⟨hb, ⟨⟨⟨hev, hw⟩, hm⟩, hfo⟩, trivial⟩)
    (fun _ _ _ h ↦ h) (fun _ h ↦ h)
  have dZ := (((dep_evec (p := p) basisR.off stackClaimCap scales).and (dep_whir sW1)).and
    (dep_na cMu mu)).and (dep_ewarrB hiO 64 (xs := folded) (by omega))
  -- the running claim
  refine pure_then (X' := fun m ↦ ((EVec m (basisR.at p.env.work) stackClaimCap scales ∧
      WhirAt m (whirR.at p.env.work) sW1) ∧ na p cMu mu m) ∧ EWArr m (wd p.env.work hiO) folded)
    (R := fun s ↦ ea p (tmpO + 14) sW1.claim s.mem) (Wc := fun j ↦ j = tmpO + 14 ∨ j = tmpO + 15)
    dZ (by finwtac) (by finwtac) (fun _ h ↦ h)
    (fun t s hb hx _ ↦ clmC_spec hb.rdi hb.inp hb.workPtr hx.1.1.2.1) ?_
  -- the sumcheck
  refine m0_drop (X := fun m ↦ (((EVec m (basisR.at p.env.work) stackClaimCap scales ∧
      WhirAt m (whirR.at p.env.work) sW1) ∧ na p cMu mu m) ∧ EWArr m (wd p.env.work hiO) folded) ∧
      ea p (tmpO + 14) sW1.claim m)
    (Y := fun (r : Array EW × EW) m ↦ EWArr m (wd p.env.work spO) r.1 ∧ ea p (tmpO + 14) r.2 m)
    (R := fun r ↦ r.1.size = mu) (Wc := fun k ↦ spO ≤ k ∧ k < spO + 64 ∨ tmpO ≤ k ∧ k < tmpO + 32)
    dZ (by finwtac) (by finwtac) (fun _ h ↦ h.1)
    (fun m0 ↦ (sumcheckC_spec (p := p) (m0 := m0) (mu := mu) (claim := sW1.claim) (by omega)).mono
      (by exact fun t s ⟨hb, hm, hx, _⟩ ↦ ⟨hb, hm, hx.1.1.2, hx.2⟩)
      (by exact fun r t s ⟨hb, ha, hs, hc, ho⟩ ↦ ⟨hb, ⟨⟨ha, hc⟩, hs⟩, ho⟩)
      (fun _ h ↦ h)) fun r hr ↦ ?_
  obtain ⟨tail, claim⟩ := r
  dsimp only at hr ⊢
  have hPs : (sW1.alphas ++ tail).size = logN := by rw [Array.size_append]; omega
  -- the point
  have d11 := dZ.and ((dep_ewarrB (p := p) spO 32 (xs := tail) (by omega)).and
    (dep_ea (tmpO + 14) claim))
  refine pure_then (X' := fun m ↦ ((((EVec m (basisR.at p.env.work) stackClaimCap scales ∧
      WhirAt m (whirR.at p.env.work) sW1) ∧ na p cMu mu m) ∧ EWArr m (wd p.env.work hiO) folded) ∧
      (EWArr m (wd p.env.work spO) tail ∧ ea p (tmpO + 14) claim m)))
    (R := fun s ↦ EWArr s.mem (wd p.env.work ptO) (sW1.alphas ++ tail) ∧
      EWArr s.mem (wd p.env.work xO) ((sW1.alphas ++ tail).extract 6 (sW1.alphas ++ tail).size ++
        (sW1.alphas ++ tail).extract 0 6))
    (Wc := fun j ↦ ptO ≤ j ∧ j < ptO + 64 ∨ xO ≤ j ∧ j < xO + 64 ∨ sc 5 ≤ j ∧ j < sc 8)
    d11 (by finwtac) (by finwtac) (fun _ h ↦ h)
    (fun t s hb hx _ ↦ (pointC_spec hb.rdi hb.inp hb.workPtr hx.1.1.1.2 hx.2.1
      (by rw [hr]; exact hx.1.1.2) (by omega) (by omega)).mono
      (fun _ ⟨h1, h2, h3, h4⟩ ↦ ⟨⟨h1, h2⟩, h3, h4⟩) (fun _ h ↦ h)) ?_
  -- the basis
  have hxs : ((sW1.alphas ++ tail).extract 6 (sW1.alphas ++ tail).size ++
      (sW1.alphas ++ tail).extract 0 6).size = logN := by
    simp only [Array.size_append, Array.size_extract, hPs]
    omega
  have d12 := d11.and ((dep_ewarrB (p := p) ptO 32 (xs := sW1.alphas ++ tail) (by omega)).and
    (dep_ewarrB (p := p) xO 32 (xs := (sW1.alphas ++ tail).extract 6 (sW1.alphas ++ tail).size ++
      (sW1.alphas ++ tail).extract 0 6) (by omega)))
  refine pure_then (X' := fun m ↦ (((((EVec m (basisR.at p.env.work) stackClaimCap scales ∧
      WhirAt m (whirR.at p.env.work) sW1) ∧ na p cMu mu m) ∧ EWArr m (wd p.env.work hiO) folded) ∧
      (EWArr m (wd p.env.work spO) tail ∧ ea p (tmpO + 14) claim m))) ∧
      (EWArr m (wd p.env.work ptO) (sW1.alphas ++ tail) ∧
      EWArr m (wd p.env.work xO) ((sW1.alphas ++ tail).extract 6 (sW1.alphas ++ tail).size ++
        (sW1.alphas ++ tail).extract 0 6)))
    (R := fun s ↦ ea p (tmpO + 18) (BasisW.eval ⟨scales, stackClaims layout target point coeffs claims ood⟩
      ((sW1.alphas ++ tail).extract 6 (sW1.alphas ++ tail).size ++ (sW1.alphas ++ tail).extract 0 6))
      s.mem) (Wc := WBe)
    d12 (by finwtac) (by finwtac) (fun _ h ↦ h) (fun t s hb hx _ ↦ ?_) ?_
  · have hR' := Regs.congr hR fun _ _ h1 h2 ↦ low_of_base hb h1 h2
    exact basisEvalC_spec (env := p.env) (inp := p.inp) hb.rdi hb.workPtr hb.inp hR'.lay hR'.cl
      hR'.ood hR'.ring hR'.kec hx.1.1.1.1.1 hss hx.2.2 (by omega) (by omega)
  -- the weight's check
  refine Refines.require fun t s ⟨hb, ⟨⟨⟨⟨⟨⟨_, hw⟩, hm⟩, hfo⟩, hsp, hcl⟩, hpt, _⟩, hbv⟩, _⟩ ↦ ?_
  exact WP.mono (finalWC_spec hb.rdi hb.inp hb.workPtr hw hpt (by omega) (by rw [Array.size_append, hr])
      (fun g hg ↦ by have := (hgl g (hgl1 ▸ hg)).1; omega)
      (fun g hg ↦ (hgl g (hgl1 ▸ hg)).2) hbv hm hmu5 hsp hr hfo (by omega) (by omega) hcl)
    (fun _ ⟨h1, h2, _⟩ ↦ ⟨h1, hb.frM h2⟩) (fun _ ⟨h1, h2, _⟩ ↦ ⟨h1, hb.fr.trans h2.fr⟩)

end NativeVm.Code.P7
