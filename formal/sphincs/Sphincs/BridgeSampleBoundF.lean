import Sphincs.BridgeSampleF

/-! **One sample of the small-budget route of the forest.** The stopped experiment with the
above-word values exposed is at most the linear potential `ρ q / 2^128`, the one-coin cover
potential, the coin part of A4, and `κ` times its near term, once
`2 - ρ + y / 2^128 + N rate ≤ κ ≤ 1`, `y = q - keygenCost`, `rate = 123 · 2^-b · 2^-15`. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenReveal
  SphincsFors.Security.Domination
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

open Completeness SeedModel Graph Assembly Reduce Internalize in
attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

omit [Params] in
theorem ofReal_le_two_halfF (c : ℚ) : ENNReal.ofReal (c : ℝ) ≤ 2 * ENNReal.ofReal ((c / 2 : ℚ) : ℝ) := by
  calc ENNReal.ofReal (c : ℝ) = ENNReal.ofReal (2 * ((c / 2 : ℚ) : ℝ)) := by
        congr 1
        push_cast
        ring
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal ((c / 2 : ℚ) : ℝ) := le_of_eq (ENNReal.ofReal_mul (by norm_num))
    _ = _ := by rw [ENNReal.ofReal_ofNat]

section SampleF

open Completeness SeedModel Graph Assembly Reduce Internalize

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **One sample of the small-budget route of the forest.** -/
theorem sample_boundF (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : Knowledge Coordinate)
    (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed)))
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (κ : ℝ) (hκ : 2 - ρ + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * (123 * ((2 : ℝ) ^ subtreeHeight * 2 ^ 15)⁻¹) ≤ κ) (hκ1 : κ ≤ 1)
    (b N : ℕ) (hbb : subtreeHeight = b) (hNN : signatureLimit = N)
    (t : H0.PoisT) (o : H0.OptF) (on : H0.OptN) (hpt : H0.checkPT t = true) (qtop : ℕ)
    (hrt : H0.checkRate b N qtop t = true) (hqtop : q - keygenCost ≤ qtop)
    (ho : H0.checkOptF b t o = true) (hon : H0.checkOptN t on = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining)))) known prepared.2] ≤
      ENNReal.ofReal (ρ * (q - keygenCost : ℕ) / 2 ^ 128) +
        (((q - keygenCost : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + failMass (failSet prepared.1)) +
          signatureLimit * failMass (failSet prepared.1)) +
        ν * (((Nat.choose (q - keygenCost) 2 : ℕ) : ℝ≥0∞) * rateS) +
        (ENNReal.ofReal κ * ((((q - keygenCost : ℕ) : ℝ≥0∞) * ν) *
            ((q - keygenCost : ℕ) * ENNReal.ofReal (((2 ^ b * on.En : ℚ) / 2 : ℚ) : ℝ))) +
          (((q - keygenCost : ℕ) : ℝ≥0∞) * ν) *
            ((q - keygenCost : ℕ) * failMass (failSet prepared.1) + signatureLimit * failMass (failSet prepared.1))) +
        2 * lam (H0.LmaxOf (q - keygenCost)) 0 (q - keygenCost) := by
  set param := truncateHash parameterOutput with hparam
  set data := sampleData parameterOutput fixed highs remaining with hdata
  set model := sampleModel parameterOutput highs with hmodel
  set tgA := targetingA parameterOutput fixed highs remaining prepared.1 with htgA
  set start : State := DebtState.start prepared.2 known with hstart
  set run := interp tgA prepared.2 model (costGameX param data (internalize adversary)) q start with hrun
  set b0 : ℝ≥0∞ := ENNReal.ofReal (ρ / 2 ^ 128) with hb0
  set pay := payoffA parameterOutput fixed highs remaining prepared known ρ with hpay'
  set q' := q - keygenCost with hq'
  set φ := failMass (failSet prepared.1) with hφ
  set c0 : ℝ≥0∞ := ENNReal.ofReal ((ρ - 1 - ((q' : ℕ) : ℝ) / 2 ^ 128) / 2 ^ 128) with hc0
  set IsF := IsFchainIn param with hIsF
  set κE : ℝ≥0∞ := ENNReal.ofReal κ with hκE
  set payB : ℝ≥0∞ := ν * ENNReal.ofReal (1 - κ) with hpayB
  set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hK
  set wbar := H0.wbarOf q' with hwbar
  set c := (2 ^ b * on.En : ℚ) with hc
  set Fset := failSet prepared.1 with hFset
  set Lmax := H0.LmaxOf q' with hLmax
  have hfair : FairS wbar (q' + 2 ^ 32) Lmax := H0.fair_of q' (H0.fair_of_rate b N qtop t hrt hbb q' hqtop)
  have hQ : q' ≤ q' + 2 ^ 32 := Nat.le_add_right _ _
  have hmsg : ∀ x, IsMsgInput x → tgA.kind x = .none := fun x h =>
    targetingA_msgF parameterOutput fixed highs remaining prepared.1 x h
  have hparse : ∀ p, model.parse (pblk param data p) = none := fun p => by
    rw [hmodel, sampleModel_parse]
    cases h : HiddenGraph.parse param (candidateActive param) (pblk param data p) with
    | none => rfl
    | some qq =>
        exfalso
        obtain ⟨hx, -⟩ := (parse_some_iff _ _ _ qq).1 h
        exact msg_not_graph param qq.1.position _ _ (msgInput_digestInput param data.root p.1 p.2) hx
  have hdigest : ∀ p, tgA.digest (pblk param data p) := fun p => msgInput_digestInput param data.root p.1 p.2
  have hclean : ∀ p, prepared.2 (pblk param data p) = none := fun p =>
    prepared_clean parameterOutput fixed highs remaining prepared hprepared _
      (msgInput_digestInput param data.root p.1 p.2)
  have hfail : ∀ m ρ' digest budget (s1 : State), Prepared prepared.2 s1 →
      ∀ out ∈ support (interp tgA prepared.2 model (finishRest param data m ρ' digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fset :=
    fun m ρ' digest budget s1 hprep out hout hnone => finishRest_fail parameterOutput fixed highs remaining
      prepared hprepared tgA m ρ' digest budget s1 hprep out hout hnone
  have hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p) := sampleModel_parse parameterOutput highs
  have hMi : model.incoming = Address.inputCoordinate := sampleModel_incoming parameterOutput highs
  have hMo : model.outgoing = Address.outputCoordinate := sampleModel_outgoing parameterOutput highs
  have hnr' := noRepeat_internalize_adversary adversary hnr ⟨data.root, param⟩
  -- the run after the keygen tick, or an aborted run
  have hrunK : ∀ hK : keygenCost ≤ q, run = (fun out => ((out.1.1, out.1.2.1, Sum.inr keygenCost :: out.1.2.2.1,
      out.1.2.2.2), out.2)) <$> interp tgA prepared.2 model
        (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start := fun hK => by
    rw [hrun]
    unfold costGameX
    rw [interp_tick_bind tgA prepared.2 model _ _ q start hK, costRestX_eq]
  have hrunA : ¬keygenCost ≤ q → run = pure ((none, [], [], []), start) := fun hK => by
    rw [hrun]
    unfold costGameX
    exact interp_tick_bind_abort tgA prepared.2 model _ _ q start hK
  -- the linear potential with both payments
  have hA3 : ∑' out, Pr[= out | run] * (endValue pay out.2 + b0 * (digestCount tgA out.1.2.2.1 : ℝ≥0∞) +
      c0 * (fleafCount IsF out.1.2.2.1 : ℝ≥0∞)) ≤ ENNReal.ofReal (ρ * (q' : ℕ) / 2 ^ 128) := by
    by_cases hK : keygenCost ≤ q
    · rw [hrunK hK, tsum_probOutput_map_mul]
      refine le_trans (le_of_eq ?_) (smallRoute_potentialF parameterOutput fixed highs remaining prepared known ρ hk
        tgA rfl q' hN (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []))
      refine tsum_congr fun out => ?_
      simp only [digestCount_cons_inrF, fleafCount_cons_inr]
      rfl
    · have hrunEq : run = interp tgA prepared.2 model (costGameX param data (internalize adversary)) 0 start := by
        rw [hrunA hK]
        unfold costGameX
        rw [interp_tick_bind_abort tgA prepared.2 model keygenCost _ 0 start (by omega)]
      rw [hrunEq]
      have hq0 : (q' : ℕ) = 0 := by omega
      rw [hc0, hq0]
      exact smallRoute_potentialF parameterOutput fixed highs remaining prepared known ρ hk tgA rfl 0
        (numeric_monoF hN (by rw [hq0]) (by norm_num)) (costGameX param data (internalize adversary))
  -- the cover potential
  have hcover : ∑' out, Pr[= out | run] * finalValue param data tgA prepared.2 [] out ≤
      (((q' : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + φ) + signatureLimit * φ) +
        lam Lmax 0 q' + b0 * ∑' out, Pr[= out | run] * (digestCount tgA out.1.2.2.1 : ℝ≥0∞) := by
    by_cases hK : keygenCost ≤ q
    · rw [hrunK hK, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
      have hgood := goodO_advProg param data wbar b0 Fset q' Lmax tgA prepared.2 model
        hparse hdigest hfail hfair hQ ((internalize adversary).main ⟨data.root, param⟩) [] hnr' q' start [] [] 0 []
        (start_prepared prepared.2 known) (start_pinv param data prepared.2 hclean known)
        (start_minv param data prepared.2 hclean known)
        (fun _ _ _ _ _ _ _ h => by cases h) (start_count param data prepared.2 hclean known q')
      have hval : startExcessO wbar b0 q' ≤ ENNReal.ofReal (o.B : ℝ) :=
        H0.startExcessO_le_opt b N qtop t o hrt hpt ho hbb hNN q' hqtop b0 (ENNReal.ofReal_le_ofReal hcthr)
      have hpot : potO param data wbar b0 Fset tgA prepared.2 Lmax start [] [] [] 0 q' ≤
          (((q' : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + φ) + signatureLimit * φ) + lam Lmax 0 q' := by
        refine le_trans (potO_start_le param data wbar b0 Fset tgA prepared.2 Lmax start q') ?_
        gcongr
      calc ∑' out, Pr[= out | interp tgA prepared.2 model
              (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start] *
            finalValue param data tgA prepared.2 [] _
          = ∑' out, Pr[= out | interp tgA prepared.2 model
              (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start] *
            finalValue param data tgA prepared.2 [] out := rfl
        _ ≤ potO param data wbar b0 Fset tgA prepared.2 Lmax start [] [] [] 0 q' +
            b0 * expectedFlagged tgA prepared.2 model
              (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start := hgood
        _ ≤ _ := by
            gcongr
            refine le_trans (expectedFlagged_le_digestF tgA prepared.2 model _ q' start) (le_of_eq ?_)
            refine tsum_congr fun out => ?_
            simp [digestCount]
    · rw [hrunA hK, tsum_probOutput_pure_mul]
      refine le_trans (le_of_eq ?_) bot_le
      rfl
  -- the contact bound A4
  have hκspl : ν ≤ payB + κE * ν := arm_splitF κ
  have hA4 : ∑' out, Pr[= out | run] * finalA4 K data.root out.1.1 out.1.2.1 out.2 ≤
      ν * (((Nat.choose q' 2 : ℕ) : ℝ≥0∞) * rateS) +
        κE * ν * ((q' : ℕ) * ((q' : ℕ) * (ENNReal.ofReal ((c / 2 : ℚ) : ℝ) + φ) + signatureLimit * φ)) +
        lam Lmax 0 q' +
        (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) *
          ∑' out, Pr[= out | run] * (fleafCount IsF out.1.2.2.1 : ℝ≥0∞) := by
    by_cases hK : keygenCost ≤ q
    · rw [hrunK hK, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
      have hinv := inv_start parameterOutput fixed highs remaining prepared known ρ hk
      have hb := a4F_bound K data wbar κE Fset model hMp hMi hMo hparse hclean hfail q' hfair hQ hκspl
        ((internalize adversary).main ⟨data.root, param⟩) hnr' known hinv
      unfold expCount at hb
      refine le_trans (le_trans (le_of_eq (tsum_congr fun out => rfl)) hb) ?_
      simp only [fleafCount_cons_inr]
      refine add_le_add ?_ le_rfl
      have hnear : startNearF wbar q' ≤ 2 * ENNReal.ofReal ((c / 2 : ℚ) : ℝ) :=
        le_trans (H0.hNearOf_le b N qtop hbb hNN t on hrt hpt hon q' hqtop) (ofReal_le_two_halfF c)
      have hsum := start_sum_leF hfair.le_one q' φ _ hnear
      refine add_le_add (add_le_add le_rfl ?_) le_rfl
      exact mul_le_mul_left' hsum _
    · rw [hrunA hK, tsum_probOutput_pure_mul]
      refine le_trans (le_of_eq ?_) bot_le
      rfl
  -- pointwise split and summation
  refine le_trans (stopped_le_interp_exposeV hb adversary q hq parameterOutput fixed highs remaining prepared
    hprepared tgA known hk) ?_
  change Pr[_ | run >>= fun result => (fun table => (table, result)) <$> completion result.2.known] ≤ _
  have hstep : ∀ out, Pr[= out | run] *
      Pr[fun x => CorrectGuess x.1 x.2.2 ∨ badAV parameterOutput fixed highs remaining prepared.1 x.1
          (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache) |
        (fun table => (table, out)) <$> completion out.2.known] ≤
      Pr[= out | run] * ((endValue pay out.2 + finalValue param data tgA prepared.2 [] out) +
        finalA4 K data.root out.1.1 out.1.2.1 out.2) := by
    intro out
    by_cases hout : out ∈ support run
    · refine mul_le_mul_right ?_ _
      rw [probEvent_map]
      set E4 : (Coordinate → Digest) → Prop := fun T => ∃ outcome, out.1.1 = some outcome ∧
        SigningTranscript.Valid outcome.2.1 ∧ A4ev K data.root T out.2 outcome out.1.2.1 with hE4
      have hE4le : Pr[E4 | completion out.2.known] ≤ finalA4 K data.root out.1.1 out.1.2.1 out.2 := by
        cases hres : out.1.1 with
        | none =>
            refine le_of_eq_of_le (probEvent_eq_zero fun T _ h => ?_) bot_le
            obtain ⟨outcome, h1, -⟩ := h
            rw [hres] at h1
            cases h1
        | some outcome =>
            simp only [finalA4, Option.elim]
            refine probEvent_mono fun T _ h => ?_
            obtain ⟨outcome', h1, h2, h3⟩ := h
            rw [hres] at h1
            cases h1
            exact ⟨h2, h3⟩
      calc Pr[_ | completion out.2.known]
          ≤ Pr[fun T => pay T out.2 = 1 ∨ (E4 T ∨ finalValue param data tgA prepared.2 [] out = 1) |
              completion out.2.known] := by
            refine probEvent_mono fun T hT h => ?_
            have hTe : tableExtending out.2.known T = T := by
              unfold completion at hT
              rw [support_map] at hT
              obtain ⟨t, _, rfl⟩ := hT
              funext c
              simp only [tableExtending]
              cases out.2.known c <;> rfl
            rcases small_pointwiseF parameterOutput fixed highs remaining prepared hprepared known hk ρ adversary q
              out hout T hTe h with h1 | h2 | h3
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
            · exact Or.inr (Or.inr h3)
        _ ≤ Pr[fun T => pay T out.2 = 1 | completion out.2.known] +
            Pr[fun T => E4 T ∨ finalValue param data tgA prepared.2 [] out = 1 | completion out.2.known] :=
            probEvent_or_le _ _ _
        _ ≤ endValue pay out.2 + (finalA4 K data.root out.1.1 out.1.2.1 out.2 +
              finalValue param data tgA prepared.2 [] out) := by
            refine add_le_add (probEvent_le_endValueF pay out.2 _ fun T h => h) ?_
            refine le_trans (probEvent_or_le _ _ _) (add_le_add hE4le ?_)
            by_cases hf : finalValue param data tgA prepared.2 [] out = 1
            · rw [hf]
              exact probEvent_le_one
            · exact le_of_eq_of_le (probEvent_eq_zero fun _ _ h => hf h) bot_le
        _ = _ := by ring
    · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
  rw [probEvent_bind_eq_tsum]
  refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
  have hsplit : ∑' out, Pr[= out | run] * ((endValue pay out.2 + finalValue param data tgA prepared.2 [] out) +
        finalA4 K data.root out.1.1 out.1.2.1 out.2) =
      (∑' out, Pr[= out | run] * endValue pay out.2 +
        ∑' out, Pr[= out | run] * finalValue param data tgA prepared.2 [] out) +
        ∑' out, Pr[= out | run] * finalA4 K data.root out.1.1 out.1.2.1 out.2 := by
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr fun out => ?_
    ring
  rw [hsplit]
  set Ev := ∑' out, Pr[= out | run] * endValue pay out.2 with hEv
  set Efin := ∑' out, Pr[= out | run] * finalValue param data tgA prepared.2 [] out with hEfin
  set Ed := ∑' out, Pr[= out | run] * (digestCount tgA out.1.2.2.1 : ℝ≥0∞) with hEd
  set Ef := ∑' out, Pr[= out | run] * (fleafCount IsF out.1.2.2.1 : ℝ≥0∞) with hEf
  have hA3' : Ev + b0 * Ed + c0 * Ef ≤ ENNReal.ofReal (ρ * (q' : ℕ) / 2 ^ 128) := by
    refine le_trans (le_of_eq ?_) hA3
    rw [hEv, hEd, hEf, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr fun out => ?_
    ring
  have hpc : ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB ≤ c0 := arm_paysF ρ _ κ hκ1 hκ
  set cov : ℝ≥0∞ := ((q' : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + φ) + signatureLimit * φ with hcov
  set coin : ℝ≥0∞ := ν * (((Nat.choose q' 2 : ℕ) : ℝ≥0∞) * rateS) with hcoin
  set lm : ℝ≥0∞ := lam Lmax 0 q' with hlm
  set nearM : ℝ≥0∞ := (((q' : ℕ) : ℝ≥0∞) * ν) * ((q' : ℕ) * ENNReal.ofReal ((c / 2 : ℚ) : ℝ)) with hnearM
  set nearF : ℝ≥0∞ := (((q' : ℕ) : ℝ≥0∞) * ν) * ((q' : ℕ) * φ + signatureLimit * φ) with hnearF
  have hκ1' : κE ≤ 1 := ENNReal.ofReal_le_one.2 hκ1
  have hnear' : κE * ν * ((q' : ℕ) * ((q' : ℕ) * (ENNReal.ofReal ((c / 2 : ℚ) : ℝ) + φ) + signatureLimit * φ)) ≤
      κE * nearM + nearF := by
    calc κE * ν * ((q' : ℕ) * ((q' : ℕ) * (ENNReal.ofReal ((c / 2 : ℚ) : ℝ) + φ) + signatureLimit * φ))
        = κE * nearM + κE * nearF := by rw [hnearM, hnearF]; ring
      _ ≤ κE * nearM + 1 * nearF := by gcongr
      _ = κE * nearM + nearF := by rw [one_mul]
  calc (Ev + Efin) + ∑' out, Pr[= out | run] * finalA4 K data.root out.1.1 out.1.2.1 out.2
      ≤ (Ev + (cov + lm + b0 * Ed)) + (coin + κE * ν * ((q' : ℕ) * ((q' : ℕ) *
          (ENNReal.ofReal ((c / 2 : ℚ) : ℝ) + φ) + signatureLimit * φ)) + lm +
          (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * Ef) :=
        add_le_add (add_le_add le_rfl hcover) hA4
    _ ≤ (Ev + (cov + lm + b0 * Ed)) + (coin + (κE * nearM + nearF) + lm +
          (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * Ef) := by gcongr
    _ = (Ev + b0 * Ed + (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * Ef) + cov + coin +
          (κE * nearM + nearF) + 2 * lm := by ring
    _ ≤ (Ev + b0 * Ed + c0 * Ef) + cov + coin + (κE * nearM + nearF) + 2 * lm := by gcongr
    _ ≤ ENNReal.ofReal (ρ * (q' : ℕ) / 2 ^ 128) + cov + coin + (κE * nearM + nearF) + 2 * lm := by gcongr

end SampleF

end Sphincs.Security.ForsPotential
