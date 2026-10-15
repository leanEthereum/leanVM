import Sphincs.BridgeHeavyW
import Sphincs.BridgeSatWRoutes

/-! The large-budget route with the weighted baseline and one heavy message. The one-coin FORS
potential is the one of `BridgeHeavyW`: the coin only pays the rate of a message with at most half of
the budget in cached digests, so the fair-rate hypothesis is needed at `(q - keygenCost) / 2` cached
digests, and the start value of the potential is the excess forecast with one spare slot
(`startExcessH`). -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenReveal SphincsFors.Security.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### The start of the run -/

section StartH

/-- The one-coin excess forecast of a new pair at the start of the run, with the spare slot of the
potential with one heavy message. -/
noncomputable def startExcessH (wbar b0 : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ wbar (excess b0) (signatureLimit + 1) I 0) k []

theorem hValueH_start (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) (wbar b0 : ℝ≥0∞) (s : State)
    (k : ℕ) : hValueH parameter data Qtot wbar b0 s [] [] 0 signatureLimit k = startExcessH wbar b0 k := rfl

/-- At the start no digest block is cached: the whole budget is left. -/
theorem start_total (parameter : PublicParameter) (data : PublicData)
    (initial : HiddenOutside.Cache HashInput HashOutput) (hclean : ∀ p, initial (pblk parameter data p) = none)
    (known : Knowledge Coordinate) (budget : ℕ) :
    TotalInv parameter data budget (DebtState.start initial known) budget := by
  have h0 : totalCount parameter data (DebtState.start initial known) = 0 := by
    unfold totalCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ h
    exact h (hclean p)
  unfold TotalInv
  rw [h0, zero_add]

/-- **The potential at the start of the run**: the excess forecasts of the future pairs, the failing
indices, and the cap term of the landed pairs. -/
theorem potH_start_le (parameter : PublicParameter) (data : PublicData) (Qtot : ℕ) (wbar b0 : ℝ≥0∞)
    (Fail : Finset (Fin (2 ^ subtreeHeight))) (tg : Targeting HashInput HashOutput Coordinate)
    (initial : HiddenOutside.Cache HashInput HashOutput) (Lmax : ℕ) (s : State) (k : ℕ) :
    potH parameter data Qtot wbar b0 Fail tg initial Lmax s [] [] [] 0 k ≤
      (k * (startExcessH wbar b0 k + failMass Fail) + signatureLimit * failMass Fail) + lam Lmax 0 k := by
  unfold potH
  refine add_le_add ?_ (le_of_eq rfl)
  split_ifs
  · exact bot_le
  · unfold coreH
    simp only [List.map_nil, List.sum_nil, zero_add, List.length_nil, Nat.sub_zero]
    rw [hValueH_start]

end StartH

/-! ### The rest of the game, weighted, one heavy message -/

section RestH

variable (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **The rest of the game with the weighted baseline and one heavy message.** For an adversary that
never repeats a message, a decided hit or a FORS cover has probability at most the weighted
saturation budget plus the one-coin FORS potential with one heavy message at the baseline
`baselineW total`. The coin pays the rate at `total / 2` cached digests. -/
theorem rest_boundH (hcompat : Compatible tg model) (htrunc : UniformTruncation (R := HashOutput) tg)
    (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hkind : ∀ p, tg.kind (pblk parameter data p) = .none)
    (hdigest : ∀ p, tg.digest (pblk parameter data p))
    (hclean : ∀ p, initial (pblk parameter data p) = none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (total : ℕ) (htotal : 2 * (total : ℝ) + 2 ≤ spaceReal) (Lmax : ℕ)
    (hfair : FairS wbar (total / 2) Lmax)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (known : Knowledge Coordinate) :
    Pr[fun r => Hit tg initial r.1 r.2.2 ∨ CoverOf parameter data r.2 |
        interp tg initial model (advProg parameter data M []) total (DebtState.start initial known) >>= fun result =>
          (fun table => (table, result)) <$> completion result.2.known] ≤
      (1 - budget 0 total) + (total * (hValueH parameter data total wbar (baselineW total)
        (DebtState.start initial known) [] [] 0 signatureLimit total + failMass Fail) + signatureLimit * failMass Fail) +
        lam Lmax 0 total := by
  set start := DebtState.start initial known (D := HashInput) (R := HashOutput) (ι := Coordinate) with hstart
  set b0 := baselineW total with hb0def
  have hb0 : b0 ≠ ⊤ := baselineW_ne_top total
  have htotal1 : (total : ℝ) + 1 < spaceReal := by
    have : (0 : ℝ) ≤ total := Nat.cast_nonneg _
    linarith
  have htotal2 : (total : ℝ) ≤ spaceReal := by
    have : (0 : ℝ) ≤ total := Nat.cast_nonneg _
    linarith
  -- the weighted FORS potential
  have hgood := goodHW_advProg parameter data total wbar b0 Fail Lmax tg initial model hparse hkind hdigest hfail hfair
    le_rfl M [] hnr total start [] [] 0 [] (start_prepared initial known)
    (start_pinv parameter data initial hclean known) (start_minv parameter data initial hclean known)
    (fun _ _ _ _ _ _ _ h => by cases h) (start_total parameter data initial hclean known total)
  have hw1 : weight tg initial start = 1 := weight_start tg initial known
  rw [hw1, one_mul] at hgood
  -- the weighted saturation
  have hsat : budget 0 total + b0 * wflag tg initial model (advProg parameter data M []) total start ≤
      ∑' out, Pr[= out | interp tg initial model (advProg parameter data M []) total start] *
        weight tg initial out.2 :=
    saturationW_start tg initial model hcompat htrunc total htotal1 b0
      (baselineW_payment total htotal2) (advProg parameter data M []) known
  set W := wflag tg initial model (advProg parameter data M []) total start with hW
  set E := ∑' out, Pr[= out | interp tg initial model (advProg parameter data M []) total start] *
    weight tg initial out.2 with hEdef
  have hE : E ≤ 1 :=
    le_trans (ENNReal.tsum_le_tsum fun out => mul_le_of_le_one_right' (weight_le_one tg initial out.2))
      tsum_probOutput_le_one
  have hcompl : ∑' out, Pr[= out | interp tg initial model (advProg parameter data M []) total start] *
      (1 - weight tg initial out.2) = 1 - E := by
    have hsum : ∑' out, Pr[= out | interp tg initial model (advProg parameter data M []) total start] *
        (1 - weight tg initial out.2) + E = 1 := by
      rw [hEdef, ← ENNReal.tsum_add]
      calc _ = ∑' out, Pr[= out | interp tg initial model (advProg parameter data M []) total start] :=
            tsum_congr fun out => by
              rw [← mul_add, tsub_add_cancel_of_le (weight_le_one tg initial out.2), mul_one]
        _ = 1 := tsum_probOutput_eq_one' probFailure_eq_zero
    exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top hE) hsum
  have hle : budget 0 total + b0 * W ≤ 1 := le_trans hsat hE
  have hW1 : b0 * W ≤ 1 - budget 0 total := ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top hle
  rw [probEvent_bind_eq_tsum]
  calc _ ≤ ∑' out, Pr[= out | interp tg initial model (advProg parameter data M []) total start] *
        ((1 - weight tg initial out.2) + weight tg initial out.2 * finalValue parameter data tg initial [] out) :=
        ENNReal.tsum_le_tsum fun out => mul_le_mul_right (hit_or_cover_le parameter data tg initial out) _
    _ = (1 - E) + ∑' out, Pr[= out | interp tg initial model (advProg parameter data M []) total start] *
          (weight tg initial out.2 * finalValue parameter data tg initial [] out) := by
        rw [← hcompl, ← ENNReal.tsum_add]
        exact tsum_congr fun out => mul_add _ _ _
    _ ≤ (1 - (budget 0 total + b0 * W)) +
          (potH parameter data total wbar b0 Fail tg initial Lmax start [] [] [] 0 total + b0 * W) :=
        add_le_add (tsub_le_tsub_left hsat _) hgood
    _ = (1 - budget 0 total) + potH parameter data total wbar b0 Fail tg initial Lmax start [] [] [] 0 total := by
        rw [tsub_add_eq_tsub_tsub,
          add_comm (potH parameter data total wbar b0 Fail tg initial Lmax start [] [] [] 0 total) (b0 * W),
          ← add_assoc, tsub_add_cancel_of_le hW1]
    _ ≤ _ := by
        refine le_trans (add_le_add le_rfl (potH_start_le parameter data total wbar b0 Fail tg initial Lmax start total))
          (le_of_eq ?_)
        rw [hValueH_start]
        ring

end RestH

section ChainH

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

set_option maxRecDepth 100000 in
/-- **One sample, weighted baseline, one heavy message.** -/
theorem sample_boundH (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate)
    (hhit : ∀ table, tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table →
      ∀ s : State, Prepared prepared.2 s → Agrees s.known table →
        (CorrectGuess table s ∨ CacheMatch.Bad (TargetAssignment.targets (truncateHash parameterOutput)
          (compTable parameterOutput fixed highs remaining table prepared.1)) s.cache) →
        Hit tg prepared.2 table s)
    (hcompat : Compatible tg (sampleModel parameterOutput highs)) (htrunc : UniformTruncation (R := HashOutput) tg)
    (hmsg : ∀ x, IsMsgInput x → tg.kind x = .none ∧ tg.digest x)
    (hclean : ∀ x, IsMsgInput x → prepared.2 x = none)
    (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared prepared.2 s1 →
      ∀ out ∈ support (interp tg prepared.2 (sampleModel parameterOutput highs)
        (finishRest (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining) m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (wbar : ℝ≥0∞) (htotal : 2 * ((q - keygenCost : ℕ) : ℝ) + 2 ≤ spaceReal) (Lmax : ℕ)
    (hfair : FairS wbar ((q - keygenCost) / 2) Lmax) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining))))
        (knownOf (truncateHash parameterOutput) fixed) prepared.2] ≤
      (1 - budget 0 (q - keygenCost)) + ((q - keygenCost : ℕ) * (hValueH (truncateHash parameterOutput)
        (sampleData parameterOutput fixed highs remaining) (q - keygenCost) wbar (baselineW (q - keygenCost))
        (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) [] [] 0 signatureLimit
        (q - keygenCost) + failMass Fail) + signatureLimit * failMass Fail) + lam Lmax 0 (q - keygenCost) := by
  set param := truncateHash parameterOutput with hparam
  set data := sampleData parameterOutput fixed highs remaining with hdata
  set known := knownOf param fixed with hknown
  set model := sampleModel parameterOutput highs with hmodel
  set start : State := DebtState.start prepared.2 known with hstart
  have hparse : ∀ p, model.parse (pblk param data p) = none := fun p =>
    hcompat.digestParse _ (hmsg _ (msgInput_digestInput param data.root p.1 p.2)).2
  refine le_trans (stopped_le_interp hb adversary q hq parameterOutput fixed highs remaining prepared hprepared tg) ?_
  -- a correct guess or a bad cache is a decided hit
  refine le_trans (probEvent_mono (q := fun r => Hit tg prepared.2 r.1 r.2.2 ∨ CoverOf param data r.2)
    fun x hx hp => ?_) ?_
  · rw [mem_support_bind_iff] at hx
    obtain ⟨out, hout, hx⟩ := hx
    rw [support_map] at hx
    obtain ⟨table, htab, rfl⟩ := hx
    have hext := interp_extends tg prepared.2 model _ q start out hout
    have hag : Agrees out.2.known table := by
      unfold completion at htab
      rw [support_map] at htab
      obtain ⟨t, _, rfl⟩ := htab
      exact fun c v hc => completion_known _ c v hc t
    have hag0 : Agrees known table := fun c v hc => hag c v (hext.2.1 c v hc)
    rcases hp with hg | hbad | ⟨outcome, hres, hfc⟩
    · exact Or.inl (hhit table ((agrees_iff_extending known table).1 hag0) out.2
        (fun i o hi => hext.1 i o hi) hag (Or.inl hg))
    · exact Or.inl (hhit table ((agrees_iff_extending known table).1 hag0) out.2
        (fun i o hi => hext.1 i o hi) hag (Or.inr hbad))
    · exact Or.inr ⟨outcome, hres, hfc⟩
  -- the keygen tick
  unfold costGameX
  by_cases hK : keygenCost ≤ q
  · rw [interp_tick_bind tg prepared.2 model _ _ q start hK, bind_map_left]
    refine le_trans (le_of_eq ?_) (rest_boundH param data wbar Fail tg prepared.2 model hcompat htrunc hparse
      (fun p => (hmsg _ (msgInput_digestInput param data.root p.1 p.2)).1)
      (fun p => (hmsg _ (msgInput_digestInput param data.root p.1 p.2)).2)
      (fun p => hclean _ (msgInput_digestInput param data.root p.1 p.2)) hfail (q - keygenCost) htotal Lmax hfair
      ((internalize adversary).main ⟨data.root, param⟩)
      (noRepeat_internalize_adversary adversary hnr _) known)
    rw [costRestX_eq, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine tsum_congr fun out => ?_
    rw [probEvent_map, probEvent_map]
    rfl
  · rw [interp_tick_bind_abort tg prepared.2 model _ _ q start hK, pure_bind]
    refine le_of_eq_of_le (probEvent_eq_zero fun x hx hp => ?_) bot_le
    rw [support_map] at hx
    obtain ⟨table, _, rfl⟩ := hx
    rcases hp with hh | ⟨outcome, hres, _⟩
    · exact not_hit_start tg prepared.2 known table hh
    · cases hres

set_option maxRecDepth 100000 in
/-- **Large budgets from the seed-free win, weighted baseline, one heavy message.** The seed-free
win is at most the weighted saturation budget, `q - keygenCost` times the one-coin excess forecast
with one spare slot at the baseline `baselineW (q - keygenCost)`, and the failing share of the
prepared searches. -/
theorem large_seedFree_boundH (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : q < 2 ^ 256)
    (htarget : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      ∃ tg : Targeting HashInput HashOutput Coordinate,
        Compatible tg (sampleModel parameterOutput highs) ∧ UniformTruncation (R := HashOutput) tg ∧
        (∀ x, IsMsgInput x → tg.kind x = .none ∧ tg.digest x) ∧
        ∀ table, tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table →
          ∀ s : State, Prepared prepared.2 s → Agrees s.known table →
            (CorrectGuess table s ∨ CacheMatch.Bad (TargetAssignment.targets (truncateHash parameterOutput)
              (compTable parameterOutput fixed highs remaining table prepared.1)) s.cache) →
            Hit tg prepared.2 table s)
    (hclean : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) → ∀ x, IsMsgInput x → prepared.2 x = none)
    (wbar : ℝ≥0∞) (Lmax : ℕ) (hfair : FairS wbar ((q - keygenCost) / 2) Lmax)
    (htotal : 2 * ((q - keygenCost : ℕ) : ℝ) + 2 ≤ spaceReal) :
    Pr[Win | seedFreeExperiment (internalize adversary) q] ≤
      ((1 - budget 0 (q - keygenCost)) + (q - keygenCost : ℕ) * startExcessH wbar (baselineW (q - keygenCost))
        (q - keygenCost) + lam Lmax 0 (q - keygenCost)) +
      ((q - keygenCost : ℕ) + signatureLimit) * expectedFail := by
  refine le_trans (HiddenBridge.seedFree_le_prep adversary q) ?_
  set A := (1 - budget 0 (q - keygenCost)) + (q - keygenCost : ℕ) * startExcessH wbar (baselineW (q - keygenCost))
    (q - keygenCost) + lam Lmax 0 (q - keygenCost) with hA
  set C : ℝ≥0∞ := ((q - keygenCost : ℕ) + signatureLimit) with hC
  -- one sample
  have hsample : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining))))
          (knownOf (truncateHash parameterOutput) fixed) prepared.2] ≤ A + C * failMass (failSet prepared.1) := by
    intro parameterOutput fixed highs remaining prepared hprepared
    obtain ⟨tg, hcompat, htrunc, hmsg, hhit⟩ := htarget parameterOutput fixed highs remaining prepared hprepared
    refine le_trans (sample_boundH hb adversary hnr q hq parameterOutput fixed highs remaining prepared hprepared tg hhit
      hcompat htrunc hmsg (hclean _ _ _ _ _ hprepared) (failSet prepared.1)
      (fun m ρ digest budget s1 hprep out hout hnone => finishRest_fail parameterOutput fixed highs remaining prepared
        hprepared tg m ρ digest budget s1 hprep out hout hnone) wbar htotal Lmax hfair) (le_of_eq ?_)
    rw [hValueH_start, hA, hC]
    push_cast
    ring
  -- average
  simp only [probEvent_bind_eq_tsum]
  refine le_trans (tsum_bound_le _ _ A C (fun parameterOutput => ∑' fixed, Pr[= fixed | ($ᵗ HiddenGraph.Table : ProbComp HiddenGraph.Table)] *
    ∑' highs, Pr[= highs | ($ᵗ CoordinateHighs : ProbComp CoordinateHighs)] *
    ∑' remaining, Pr[= remaining | ($ᵗ RemainingOutputs : ProbComp RemainingOutputs)] *
    ∑' prepared, Pr[= prepared | preparation parameterOutput fixed highs remaining] *
      failMass (failSet prepared.1)) fun parameterOutput _ => ?_) le_rfl
  refine tsum_bound_le _ _ A C _ fun fixed _ => ?_
  refine tsum_bound_le _ _ A C _ fun highs _ => ?_
  refine tsum_bound_le _ _ A C _ fun remaining _ => ?_
  exact tsum_bound_le _ _ A C _ fun prepared hprepared =>
    hsample parameterOutput fixed highs remaining prepared hprepared

set_option maxRecDepth 100000 in
/-- **Large budgets, deterministic signer, weighted baseline, one heavy message.** For a coin `wbar`
that pays the rate at `(q - keygenCost) / 2` cached digests and `Lmax` landed pairs, with a
negligible cap term: if the large-budget inequality `hH0` with the weighted baseline and the excess
forecast with one spare slot holds at the adversary's budget after key generation, the deterministic
signer's advantage is at most `q / 2^127`. -/
theorem det_largeH (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ)
    (hbound : Det.HasHashQueryBoundDet adversary q) (hq : q < 2 ^ 127) (hK : keygenCost ≤ q)
    (wbar : ℝ≥0∞) (Lmax : ℕ) (hfair : FairS wbar ((q - keygenCost) / 2) Lmax)
    (hlam : lam Lmax 0 (q - keygenCost) ≤ (2 : ℝ≥0∞)⁻¹ ^ 201)
    (hH0 : (1 - budget 0 (q - keygenCost)) + ((q - keygenCost : ℕ) : ℝ≥0∞) *
        startExcessH wbar (baselineW (q - keygenCost)) (q - keygenCost) +
        ((q - keygenCost + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q - keygenCost + keygenCost : ℕ) : ℝ≥0∞) / 2 ^ 127) :
    Det.forgeAdvantageDet adversary ≤ q / 2 ^ 127 := by
  set q' := q - keygenCost with hq'
  have hsum : q' + keygenCost = q := by omega
  have hq'le : 2 * q' ≤ 2 ^ 128 := by omega
  have htotal : 2 * ((q' : ℕ) : ℝ) + 2 ≤ spaceReal := by
    unfold spaceReal
    have : (2 * q' + 2 : ℕ) ≤ 2 ^ 128 := by omega
    exact_mod_cast this
  have hmain := large_seedFree_boundH hb (Memo.memoAdv adversary) (Memo.memoAdv_noRepeat adversary) q
    (by omega) (fun _ _ _ _ _ hprep => targetingAll hb _ _ _ _ _ hprep)
    (fun _ _ _ _ _ hprep => prepared_clean _ _ _ _ _ hprep) wbar Lmax hfair htotal
  refine le_trans (Det.forgeAdvantageDet_le_seedFree adversary q hbound) ?_
  have hE := expectedFail_le
  -- the negligible terms fit in the slack
  have hslack : ((q' : ℝ≥0∞) + signatureLimit) * expectedFail + 2 * ((q : ℝ≥0∞) / 2 ^ 256) +
      lam Lmax 0 q' ≤ ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 := by
    have h256 : 2 * ((q : ℝ≥0∞) / 2 ^ 256) ≤ (((q' + keygenCost : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 201 := by
      rw [div_two_pow, hsum, mul_left_comm]
      refine mul_le_mul' le_rfl ?_
      rw [show (256 : ℕ) = 55 + 201 by norm_num, pow_add, ← mul_assoc]
      calc 2 * (2 : ℝ≥0∞)⁻¹ ^ 55 * (2 : ℝ≥0∞)⁻¹ ^ 201 ≤ 1 * (2 : ℝ≥0∞)⁻¹ ^ 201 := by
            refine mul_le_mul' ?_ le_rfl
            rw [show (55 : ℕ) = 1 + 54 by norm_num, pow_add, pow_one, ← mul_assoc,
              ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
            exact pow_le_one₀ (by norm_num) (by norm_num)
        _ = _ := one_mul _
    have hnat : ((q' : ℝ≥0∞) + signatureLimit) + ((q' + keygenCost : ℕ) : ℝ≥0∞) + 1 ≤
        2 * ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) := by
      have hK1 : 1 ≤ keygenCost := by
        have := Nat.two_pow_pos subtreeHeight
        unfold keygenCost
        omega
      have h : (q' + signatureLimit) + (q' + keygenCost) + 1 ≤ 2 * (q' + keygenCost + signatureLimit) := by omega
      have h' : (((q' + signatureLimit) + (q' + keygenCost) + 1 : ℕ) : ℝ≥0∞) ≤
          ((2 * (q' + keygenCost + signatureLimit) : ℕ) : ℝ≥0∞) := by exact_mod_cast h
      push_cast at h' ⊢
      exact h'
    calc _ ≤ ((q' : ℝ≥0∞) + signatureLimit) * (2 : ℝ≥0∞)⁻¹ ^ 201 +
          (((q' + keygenCost : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 201 + 1 * (2 : ℝ≥0∞)⁻¹ ^ 201 :=
          add_le_add (add_le_add (mul_le_mul' le_rfl hE) h256) (by rw [one_mul]; exact hlam)
      _ = (((q' : ℝ≥0∞) + signatureLimit) + ((q' + keygenCost : ℕ) : ℝ≥0∞) + 1) * (2 : ℝ≥0∞)⁻¹ ^ 201 := by
          ring
      _ ≤ (2 * ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 201 :=
          mul_le_mul' hnat le_rfl
      _ = _ := by rw [mul_comm (2 : ℝ≥0∞), mul_assoc, two_mul_inv_pow_succ]
  calc _ ≤ (((1 - budget 0 q') + (q' : ℝ≥0∞) * startExcessH wbar (baselineW q') q' +
            lam Lmax 0 q') +
          ((q' : ℕ) + signatureLimit) * expectedFail) + 2 * ((q : ℝ≥0∞) / 2 ^ 256) := add_le_add hmain le_rfl
    _ = ((1 - budget 0 q') + (q' : ℝ≥0∞) * startExcessH wbar (baselineW q') q') +
          (((q' : ℝ≥0∞) + signatureLimit) * expectedFail + 2 * ((q : ℝ≥0∞) / 2 ^ 256) +
            lam Lmax 0 q') := by
        ring
    _ ≤ ((1 - budget 0 q') + (q' : ℝ≥0∞) * startExcessH wbar (baselineW q') q') +
          ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 := add_le_add le_rfl hslack
    _ ≤ ((q' + keygenCost : ℕ) : ℝ≥0∞) / 2 ^ 127 := hH0
    _ = (q : ℝ≥0∞) / 2 ^ 127 := by rw [hsum]

end ChainH

end Sphincs.Security.ForsPotential
