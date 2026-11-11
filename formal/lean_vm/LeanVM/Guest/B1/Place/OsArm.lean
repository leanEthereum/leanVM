/-
  LeanVM.Guest.B1.Place.OsArm

  open_stacked at a configuration and rate is complete, placed, from its helpers' statements.
-/

module

public import LeanVM.Guest.B1.Place.KidsAt
public import LeanVM.Guest.B1.Place.OfrRegion
public import LeanVM.Guest.B1.Place.OsPlace
public import LeanVM.Guest.B1.Place.OsBos

/-!
# An arm, placed

`OsCfgOk c ri`: a configuration's decided facts at rate `ri` the lift uses (the names, the frames'
shapes, the buffers, the dispatches on the rate's selector, the helpers' table entries, the
levels' shapes). **`os_arm_completeAtO`**: a function whose body is `osBody c` is complete placed
on every accepting run of `whirOpen μ r target` with no zero challenge and openings that agree in
the caps, at an optional words bound (`osBos`), from the named callees' and the helpers' placed
statements, the values of the honest valuation (`OsCallVals`) and the trace's data
(`OsHelperFacts`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **A configuration's decided facts at rate `ri`.** -/
structure OsCfgOk (c : OsCfg) (ri : ℕ) : Prop where
  names : OsNames c ri
  shapes : OsKidShapes c
  sizes : OsSizes c
  pos : ∀ x ∈ osSizesL c, 0 < x
  tot : (osSizesL c).sum < 2 ^ 64 - 1
  posOff : ∀ l < c.levels.length, (lvAt c l).posOff = l * ligPosCap
  poN : c.levels.length * ligPosCap < 2 ^ 64 - 1
  addrs : (osBodyAc c).filterMap Main.Stmt.addrS = []
  disp : DispShort (osBodyAc c)
  rateD : ∀ s ∈ osBodyAc c, ∀ x fs a r, s = .dispatch x fs a r → x = .n osRate ∧ fs.length = 4
  per : ∀ l < c.levels.length, 0 < 192 / (lvAt c l).depth
  qs : ∀ l < c.levels.length, (lvAt c l).queries ≤ (lvAt c l).squeezes * (192 / (lvAt c l).depth)
  cd : ∀ l < c.levels.length, (lvAt c l).capDepth ≤ (lvAt c l).depth
  il : ∀ l < c.levels.length,
    rowLo (lvAt c l).interleave + (lvAt c l).interleave / rowLo (lvAt c l).interleave ≤ c.maxIl
  qend : ∀ l < c.levels.length, (lvAt c l).posOff + (lvAt c l).queries ≤ c.levels.length * ligPosCap
  lp : ∀ l < c.levels.length, ∃ loop : String,
    (osPositionsName (lvAt c l), (lvAt c l).squeezes, loop, (lvAt c l).depth, (lvAt c l).capDepth)
      ∈ lpTable
  lq : ∀ l < c.levels.length, ∃ leaf : ℕ,
    (osQueriesName l (lvAt c l), (lvAt c l).queries, lvBase l, (lvAt c l).interleave, leaf,
      (lvAt c l).depth, (lvAt c l).capDepth) ∈ lqTable
  lr : ∀ l < c.levels.length, ∃ l1 l2 : String,
    (osResidualName (lvAt c l), (lvAt c l).queries, (lvAt c l).logCols, l1, l2) ∈ lrTable

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

theorem dispOk_rate {σ : Val} {c : OsCfg} {ri : ℕ} (hri : ri < 4)
    (hR : σ (.n osRate) = ofK (addressOfIndex ri))
    (hD : ∀ s ∈ osBodyAc c, ∀ x fs a r, s = .dispatch x fs a r → x = .n osRate ∧ fs.length = 4) :
    ∀ s ∈ osBodyAc c, DispOk σ s := fun s hs ↦ by
  match s, hs with
  | .dispatch x fs a r, hs =>
    obtain ⟨hx, hl⟩ := hD _ hs x fs a r rfl
    subst hx
    exact ⟨ri, by omega, by omega, hR⟩
  | .atom _, _ => trivial
  | .call .., _ => trivial
  | .callIf .., _ => trivial
  | .ite .., _ => trivial
  | .match_ .., _ => trivial
  | .ret _, _ => trivial

set_option maxHeartbeats 1600000 in
set_option linter.constructorNameAsVariable false in
/-- **An arm, placed**, at a configuration and rate. -/
theorem os_arm_completeAtO {Bd : Option (String → ℕ)} {c : OsCfg} {μ r : ℕ}
    {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (hK : OsCfgOk c (r - 1))
    {name : String} {fn : Fn} (hfind : coreProgram.find? name = some fn)
    (hp : fn.params = osParams 10) (hb : fn.body = osBody c) (hloop : coreProgram.loop name = false)
    (hnamed : ∀ f ∈ osCalleeNames c, ∀ K, osKindOf f = some K → ∀ (args rets : List E)
      (L' : Layout), RegPtrs K.spec args (RegionL L') →
      (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtO fs cert κ f L' args (Returns rets) (Bd.map (· f)))
    (hB : ∀ f ∈ osCalleeNames c, BoundsAt fs f (Bd.map (· f)))
    (Dn : String → ℕ → ℕ → ℕ)
    (hlp : ∀ e ∈ lpTable, ∀ Bd', LpAtO fs cert κ e.1 e.2.1 e.2.2.2.1 e.2.2.2.2 (Dn e.1) Bd')
    (hlq : ∀ e ∈ lqTable, ∀ Bd', LqAtO fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1
      e.2.2.2.2.2.1 e.2.2.2.2.2.2 Bd')
    (hlr : ∀ e ∈ lrTable, ∀ Bd', LrAtO fs cert κ e.1 e.2.1 e.2.2.1 Bd')
    (hvals : ∀ (tr : OsTr) (σ0 : Val) (c0 c2 : E) (b0 : ℕ), tr.Ls.length = c.levels.length →
      OsCallVals c tr σ0 c0 c2 b0)
    {S : KeccakState} {root : Digest} {target cur : E} {xs : List E} {os : List (List Opening)}
    {w : WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots')
    (hnz : NoZeroChallenge μ r target S xs os root)
    (hhon : ∀ tr : OsTr, TrFit c tr → TrRun c μ r target S xs os root tr → OsHelperFacts c tr)
    {Lin : Layout} (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs) :
    CompleteAtO fs cert κ name Lin
      (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur])
      (OsOut μ w) (Bd.map fun Bk ↦ osBos fs Bk name c) := by
  obtain ⟨c0, c2, tr, hfit, hplen, hptC, hpt1C, hbody, hrunT⟩ := osBodyA_honest hF hK.sizes hrun hnz
  have hH := hhon tr hfit hrunT
  have hlen : tr.Ls.length = c.levels.length := hfit.len
  have hpt : (tr.point (c.levels.headD default).folds).length ≤ pointCap := by
    rw [hplen]; exact hF.mu40
  have htl : tr.Lf.ml ≤ yrLogCap := by rw [lf_ml' hF hfit]; exact hK.sizes.yr
  set args := rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur]
    with hargs
  set σ0 := Val.ofArgs args with hσ0
  have hb' : fn.body = osBodyAc c ++ [.ret (osFinRet c (osTlSt c).2.1 (osTlSt c).2.2)] := by
    rw [hb, osBody_splitC]
  have hcapl : (capOf S).length = 5 := by simp [capOf]
  obtain ⟨a0, a1, a2, a3, a4, h5⟩ : ∃ a0 a1 a2 a3 a4 : E, capOf S = [a0, a1, a2, a3, a4] := by
    match capOf S, hcapl with
    | [a0, a1, a2, a3, a4], _ => exact ⟨a0, a1, a2, a3, a4, rfl⟩
  have hargsE : args = [rateSel r, a0, a1, a2, a3, a4, target, (digestHalves root).1,
      (digestHalves root).2, cur] := by rw [hargs, h5]; rfl
  have harg : ∀ j < 10, σ0 (.n j) = args.getD j 0 := fun j _ ↦ ofArgs_n _ _
  refine os_completeAt_placeJFO hfind hloop κ Lin args (OsOut μ w) (Bd.map fun Bk ↦ osBos fs Bk name c)
    hb' (osBodyAc_flatF c) hK.addrs (osSizesL c) [osIxPT c, osIxPT1 c] (osJs_nodup c) (osJs_lt c)
    (C := fun _ _ _ ↦ True) fun fp ↦ ?_
  set b0 := fp + fs name with hb0
  set σ := osSigma c tr σ0 c0 c2 b0 with hσ
  set A := osAtOf c b0 with hA
  set Lk := osLk c tr b0 Lin with hLk
  have hag : AgreeBelow 10 σ0 σ := agree_fill _ _ _ _
  have hRσ : σ (.n osRate) = ofK (addressOfIndex (r - 1)) := by
    rw [hag 0 (by decide), harg 0 (by decide)]; rfl
  have hV := hvals tr σ0 c0 c2 b0 hlen
  -- the body on a memory
  have hcapS : [σ0 (.n 1), σ0 (.n 2), σ0 (.n 3), σ0 (.n 4), σ0 (.n 5)] = capOf S := by
    show [args.getD 1 0, args.getD 2 0, args.getD 3 0, args.getD 4 0, args.getD 5 0] = capOf S
    rw [hargsE, h5]; rfl
  have hblk : ∀ (C : CallRel) (rd : Reader), OsMem rd A c tr →
      OsCallsOk C rd (σ0 (.n osRate)) A c tr → ReadsAt rd cur xs →
      AllOk C rd σ (osBodyAc c) ∧
        (osFinRet c (osTlSt c).2.1 (osTlSt c).2.2).map σ = [w.target, A.PT, A.PT1, w.inner, w.residual] := by
    intro C rd hm hc hx
    have h6 : σ0 (.n 6) = target := by show args.getD 6 0 = target; rw [hargsE]; rfl
    have h7 : σ0 (.n 7) = (digestHalves root).1 := by
      show args.getD 7 0 = _; rw [hargsE]; rfl
    have h8 : σ0 (.n 8) = (digestHalves root).2 := by
      show args.getD 8 0 = _; rw [hargsE]; rfl
    have h9 : ReadsAt rd (σ0 (.n 9)) xs := by show ReadsAt rd (args.getD 9 0) xs; rw [hargsE]; exact hx
    have h := hbody C rd σ0 A hcapS h6 h7 h8 h9 hm hc σ hag (range_fill _ _ _ _)
    exact ⟨h.1, h.2.1⟩
  have hR0 : σ0 (.n osRate) = ofK (addressOfIndex (r - 1)) := by rw [harg 0 (by decide)]; rfl
  have hLkLin : ∀ rd, MemL rd Lk → MemL rd Lin := fun rd hm ↦ (Main.memL_append.mp hm).2
  have hall : ∀ rd, LowDef κ rd → MemL rd Lk →
      AllOk (osCR rd (osSp c tr A) (OsXOk κ Lk)) rd σ (osBodyAc c) := fun rd hl hm ↦
    (hblk _ rd (osMem_of_memLk hpt htl hm)
      (by rw [hR0]; exact osCallsOk_honest hF hfit hK.sizes hK.names hpt htl hm)
      (hLin rd hl (hLkLin rd hm))).1
  have hdo : ∀ s ∈ osBodyAc c, DispOk σ s := dispOk_rate (by have := hK.names.ri4; omega) hRσ hK.rateD
  have hparams : fn.params.map σ = args := by
    rw [hp]
    refine List.ext_getElem (by rw [hargsE]; simp [osParams]) fun j h1 h2 ↦ ?_
    have hj : j < 10 := by simpa [osParams] using h1
    simp only [osParams, List.getElem_map, List.getElem_range]
    rw [hag j hj, harg j hj, List.getD_eq_getElem _ _ h2]
  have hOut : ∀ bp, OsOut μ w [w.target, A.PT, A.PT1, w.inner, w.residual]
      (osLoutJ b0 (osSizesL c) (osOwnL c tr bp) [osIxPT c, osIxPT1 c]) := fun bp ↦ by
    rw [osLoutJ_eq]
    refine ⟨_, _, rfl, ?_⟩
    rw [hptC, hpt1C]
  have hmemBody : ∀ (bp : ℕ → ℕ → E) (rd : Reader), LowDef κ rd →
      MemL rd (bufL b0 (osSizesL c) (osOwnL c tr bp)) → MemL rd Lin →
      Stmt.HoldsList (fun _ _ _ ↦ True) rd σ fn.body False
          (fun r ↦ r = [w.target, A.PT, A.PT1, w.inner, w.residual]) ∧
        ((osBodyAc c).filterMap Main.Stmt.allocSz).map (fun x ↦ x.2.elim id fun s ↦ logG (σ s)) =
          osSizesL c ∧
        (((osBodyAc c).filterMap Main.Stmt.allocSz).map Prod.fst).map σ =
          (bases b0 (osSizesL c)).map (fun b ↦ ofK (addressOfIndex b)) := by
    intro bp rd hl hmB hmLin
    have hmLk : MemL rd Lk := osLk_memL hmB hmLin
    obtain ⟨hA1, hr⟩ := hblk _ rd (osMem_of_memLk hpt htl hmLk)
      (by rw [hR0]; exact osCallsOk_honest (κ := κ) hF hfit hK.sizes hK.names hpt htl hmLk)
      (hLin rd hl hmLin)
    refine ⟨?_, hV.sizes, hV.bufs⟩
    rw [hb', holdsList_flat_ret _ (by rw [osBodyAc_eq]; exact osBodyA_flat c)]
    exact ⟨os_allOk_mono (fun _ _ _ _ ↦ trivial) hA1, hr⟩
  by_cases hex : ∃ rd0, LowDef κ rd0 ∧ MemL rd0 Lk
  · -- the callees
    set D : ℕ → ℕ → ℕ → ℕ := fun l ↦ Dn (osPositionsName (lvAt c l)) with hD
    have hofrR : ∀ c' ∈ ((osBodyAc c).filterMap (Stmt.callSF σ)).map (Main.mkCall σ),
        c'.taken = true → ∀ b, osKindOf c'.f = some (.ofr b) →
        RegPtrs [(7, roundLen b)] (c'.args.map σ) (RegionL Lk) := by
      obtain ⟨rd0, hl0, hm0⟩ := hex
      set rd' := restrictL rd0 Lk
      have hm' : MemL rd' Lk := memL_restrictL hm0
      have hx' : ReadsAt rd' cur xs := readsAt_restrictL_of (hLin rd0 hl0 (hLkLin rd0 hm0)) fun t ht ↦ by
        obtain ⟨i, hi, hreg⟩ := os_addr_in_regionL (M := Lin) (A := cur.limb 0 * addressOfIndex t)
          (v := xs[t]) (fun rd hl hm ↦ (hLin rd hl hm t ht).2) hl0 (hLkLin rd0 hm0)
        obtain ⟨q, hq, h1, h2⟩ := hreg
        exact ⟨i, hi, q, List.mem_append_right _ hq, h1, h2⟩
      have h := (hblk (ofrC Lk) rd' (osMem_of_memLk hpt htl hm')
        (by rw [hR0]; exact osCallsOk_ofr hK.names A Lk rd0) hx').1
      intro c' hc' ht b hk
      exact os_calls_of_allOkF h hdo hK.disp c' hc' ht b hk
    have hlpK : ∀ l < c.levels.length, osPositionsName (lvAt c l) ∈ osCalleeNames c →
        CompleteAtPO fs cert κ (osPositionsName (lvAt c l))
        (fun p ↦ Lk ++ osW cert c D b0 l p) (osLpArgs c tr A l) (sqLast (lvAt c l) (tr.L l).F2.cap)
        (osS cert c tr D l) (Bd.map (· (osPositionsName (lvAt c l)))) := fun l hl hmn ↦ by
      obtain ⟨loop, he⟩ := hK.lp l hl
      exact os_lp_kid hpt htl hK.sizes hl (hK.per l hl) (hH l hl)
        (hlp _ he (Bd.map (· (osPositionsName (lvAt c l))))) (hB _ hmn)
    have hlqK : ∀ l < c.levels.length, osQueriesName l (lvAt c l) ∈ osCalleeNames c → ∀ p,
        CompleteAtO fs cert κ (osQueriesName l (lvAt c l)) (Lk ++ osW cert c D b0 l p ++ osS cert c tr D l p)
        (osLqArgs c tr A l) (Returns (osLqRets c tr l)) (Bd.map (· (osQueriesName l (lvAt c l)))) :=
      fun l hl hmn p ↦ by
        obtain ⟨leaf, he⟩ := hK.lq l hl
        exact os_lq_kid hpt htl hl (hK.per l hl) (hK.qs l hl) (hK.cd l hl) (hK.il l hl) (hH l hl)
          (hlq _ he (Bd.map (· (osQueriesName l (lvAt c l))))) (hB _ hmn) p
    have hlrK : ∀ l < c.levels.length, osResidualName (lvAt c l) ∈ osCalleeNames c →
        CompleteAtO fs cert κ (osResidualName (lvAt c l)) Lk (osLrArgs c tr A l)
        (Returns [finH c tr l]) (Bd.map (· (osResidualName (lvAt c l)))) := fun l hl hmn ↦ by
      obtain ⟨l1, l2, he⟩ := hK.lr l hl
      exact os_lr_kid hpt htl hK.sizes hl (hK.qend l hl) (hH l hl)
        (hlr _ he (Bd.map (· (osResidualName (lvAt c l))))) (hB _ hmn) hex
    obtain ⟨N, L, ps, hps, hW, hDj, hNb, hKid⟩ := os_kids_at (fs := fs) (cert := cert) (κ := κ)
      (Bd := Bd) (D := D) hK.names hK.shapes hK.pos hK.tot hK.posOff hK.poN
      (fun l hl ↦ (hH l hl).cap5) hRσ hV hall hdo hK.disp hex hnamed hofrR hlpK hlqK hlrK
      (b0 + (osSizesL c).sum)
    refine ⟨σ, osOwnL c tr (osBp cert c D fun l ↦ ps.getD l 0), [w.target, A.PT, A.PT1, w.inner,
      w.residual], N, L, fun _ ↦ False, _, rfl, hdo, osOwnL_fit c tr _ hpt htl, hOut _, hW, hDj,
      ?_, hparams, fun rd hl hmB hmLin ↦ hmemBody _ rd hl hmB hmLin, ?_⟩
    · intro B hB'
      obtain ⟨Bk, hBk, rfl⟩ := Option.mem_map.mp hB'
      have := hNb Bk hBk
      simp only [osBos]; omega
    · intro rd hl hmB hmL hmLin
      have hmLk : MemL rd Lk := osLk_memL hmB hmLin
      have hmW : ∀ i (h : i < ps.length), MemL rd (osW cert c D b0 i ps[i]) := fun i h ↦ by
        have := osW_memL (cert := cert) (D := D) hpt htl hK.sizes (l := i) (by rw [← hps]; exact h) hmB
        rwa [List.getD_eq_getElem _ _ h] at this
      have hRk : ∀ i, RegionL Lk i → RegionL Lin i ∨
          RegionL (bufL b0 (osSizesL c) (osOwnL c tr (osBp cert c D fun l ↦ ps.getD l 0))) i :=
        fun i hi ↦ regionL_osLk _ hi
      have hRw : ∀ l < c.levels.length, ∀ p i, RegionL (osW cert c D b0 l p) i → RegionL Lin i ∨
          RegionL (bufL b0 (osSizesL c) (osOwnL c tr (osBp cert c D fun l ↦ ps.getD l 0))) i :=
        fun l hl' p i hi ↦ Or.inr (regionL_osW _ hK.sizes hl' hi)
      exact hKid rd (fun i ↦ RegionL Lin i ∨
          RegionL (bufL b0 (osSizesL c) (osOwnL c tr (osBp cert c D fun l ↦ ps.getD l 0))) i)
        (fun _ ↦ False) hl hmL hmLk hmW hRk hRw
  · -- no memory holds the callees' words
    refine ⟨σ, osOwnL c tr fun _ _ ↦ 0, [w.target, A.PT, A.PT1, w.inner, w.residual], 0, [],
      fun _ ↦ False, _, rfl, hdo, osOwnL_fit c tr _ hpt htl, hOut _, fun q hq ↦ by simp at hq,
      disj_nil, ?_, hparams, fun rd hl hmB hmLin ↦ (hex ⟨rd, hl, osLk_memL hmB hmLin⟩).elim,
      fun rd hl hmB _ hmLin ↦ (hex ⟨rd, hl, osLk_memL hmB hmLin⟩).elim⟩
    intro B hB'
    obtain ⟨Bk, -, rfl⟩ := Option.mem_map.mp hB'
    simp only [osBos]; omega

end
end LeanVM.Guest.B1
