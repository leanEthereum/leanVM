module

public import FORS.LargeBudget.Route
public import FORS.LargeBudget.RouteStartH
public import FORS.LargeBudget.WeightedPotentialH
public import FORS.SmallBudget.Linear.HonestSignerFrom

@[expose] public section

/-! The large-budget route with the weighted baseline on the honest-reading game: the signer's reads
are honest (free), the adversary's and the verifier's charged. As `Route`, with the honest program's
potential (`goodWH_advProgH`), the saturation under `HonestOkFrom` (the signer reads only
message-digest inputs and prepared trials), and the honest seed-free win in the interpreted run
(`seedFree_le_prep`, `stopped_le_interp`). The closing is `forgeAdvantage_le_largeWH`, at the
budget `keygenHashCost + q + V` of an adversary making `q` hash queries and a verifier making `V`. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal FORS.Base.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

/-! ### The honest program's reads are harmless from a prepared state -/

section Ok

variable (parameter : PublicParameter) (data : PublicData) {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A hash computation read raw makes no honest read. -/
theorem honestOkFrom_rawH {α : Type} (computation : OracleComp HashSpec α) :
    HonestOkFrom tg initial model (simulateQ (fun q => liftM (CostSpecH.query (.inl (.inr (.inl q)))) :
      QueryImpl HashSpec (OracleComp CostSpecH)) computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact honestOkFrom_pure tg initial model value
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact honestOkFrom_bind tg initial model (honestOkFrom_query_of_ne tg initial model _ fun _ h => by cases h) ih

/-- **The honest program's reads are harmless** when the signer's are. -/
theorem honestOkFrom_advProgH (hgood : SignerReadsGood tg initial model parameter data)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) :
    ∀ L, HonestOkFrom tg initial model (advProgH parameter data M L) := by
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L
      rw [advProgH_pure]
      exact honestOkFrom_bind tg initial model (honestOkFrom_rawH tg initial model _)
        fun _ => honestOkFrom_pure tg initial model _
  | query_bind input next ih =>
      intro L
      rcases input with (draw | bytes) | message
      · rw [advProgH_draw]
        exact honestOkFrom_bind tg initial model (honestOkFrom_query_of_ne tg initial model _ fun _ h => by cases h)
          fun value => ih value L
      · rw [advProgH_hash]
        exact honestOkFrom_bind tg initial model (honestOkFrom_query_of_ne tg initial model _ fun _ h => by cases h)
          fun value => ih value L
      · rw [advProgH_sign]
        exact honestOkFrom_bind tg initial model
          (honestOkFrom_signCostSourceH tg initial model parameter data hgood message) fun r => ih r _

/-- A leading tick only shortens the budget, honest program. -/
theorem interp_tick_bind {β : Type} (amount : ℕ) (next : Unit → OracleComp CostSpecH β) (budget : ℕ) (s : State)
    (h : amount ≤ budget) :
    interp tg initial model (HiddenCost.tick amount >>= next) budget s =
      (fun out => ((out.1.1, out.1.2.1, Sum.inr amount :: out.1.2.2.1, out.1.2.2.2), out.2)) <$>
        interp tg initial model (next ()) (budget - amount) s := by
  unfold HiddenCost.tick
  rw [interp_query_bind]
  split_ifs with hc
  · change (pure ((), s) : ProbComp _) >>= _ = _
    rw [pure_bind]
    rfl
  · exact absurd h hc

theorem interp_tick_bind_abort {β : Type} (amount : ℕ) (next : Unit → OracleComp CostSpecH β) (budget : ℕ) (s : State)
    (h : ¬amount ≤ budget) :
    interp tg initial model (HiddenCost.tick amount >>= next) budget s = pure ((none, [], [], []), s) := by
  unfold HiddenCost.tick
  rw [interp_query_bind]
  split_ifs with hc
  · exact absurd hc h
  · rfl

end Ok

section RestW

variable (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **The rest of the game with the weighted baseline**, the signer honest. For an adversary that never repeats a
message, a decided hit or a FORS cover has probability at most the weighted saturation budget plus
the one-coin FORS potential at the baseline `baselineW total`. -/
theorem rest_boundW (hcompat : Compatible tg model) (htrunc : UniformTruncation (R := HashOutput) tg)
    (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hclean : ∀ p call, initial (pblk parameter data p call) = none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (total : ℕ) (htotal : 2 * (total : ℝ) + 2 ≤ spaceReal) (Lmax : ℕ)
    (hfair : FairS wbar (total + digestAttemptLimit) Lmax)
    (hgoodS : SignerReadsGood tg initial model parameter data)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (known : Knowledge Coordinate) :
    Pr{let r ← (interp tg initial model (advProgH parameter data M []) total (DebtState.start initial known) >>= fun result =>
          (fun table => (table, result)) <$> completion result.2.known)}[Hit tg initial r.1 r.2.2 ∨ CoverOf parameter data r.2] ≤
      (1 - budget 0 total) + (total * (hValueO parameter data wbar (baselineW total)
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
  have hgood := goodWH_advProgH parameter data wbar b0 Fail total Lmax tg initial model hparse hkind hdigest hfail hfair
    (Nat.le_add_right _ _) M [] hnr total start [] [] 0 [] (start_prepared initial known)
    (start_pinv parameter data initial hclean known) (start_minv parameter data initial hclean known)
    (fun _ _ _ _ h => by cases h)
    (countInvL_of_countInv parameter data total (start_count parameter data initial hclean known total))
  have hw1 : weight tg initial start = 1 := weight_start tg initial known
  rw [hw1, one_mul] at hgood
  -- the weighted saturation
  have hsat : budget 0 total + b0 * wflag tg initial model (advProgH parameter data M []) total start ≤
      ∑' out, Pr{let x ← interp tg initial model (advProgH parameter data M []) total start}[x = out] *
        weight tg initial out.2 :=
    saturationW_start tg initial model hcompat htrunc total htotal1 b0
      (baselineW_payment total htotal2) (advProgH parameter data M [])
      (honestOkFrom_advProgH parameter data tg initial model hgoodS M []) known
  set W := wflag tg initial model (advProgH parameter data M []) total start with hW
  set E := ∑' out, Pr{let x ← interp tg initial model (advProgH parameter data M []) total start}[x = out] *
    weight tg initial out.2 with hEdef
  have hE : E ≤ 1 :=
    le_trans (ENNReal.tsum_le_tsum fun out => mul_le_of_le_one_right' (weight_le_one tg initial out.2))
      (OracleComp.tsum_prEvent_le_one _)
  have hcompl : ∑' out, Pr{let x ← interp tg initial model (advProgH parameter data M []) total start}[x = out] *
      (1 - weight tg initial out.2) = 1 - E := by
    have hsum : ∑' out, Pr{let x ← interp tg initial model (advProgH parameter data M []) total start}[x = out] *
        (1 - weight tg initial out.2) + E = 1 := by
      rw [hEdef, ← ENNReal.tsum_add]
      calc _ = ∑' out, Pr{let x ← interp tg initial model (advProgH parameter data M []) total start}[x = out] :=
            tsum_congr fun out => by
              rw [← mul_add, tsub_add_cancel_of_le (weight_le_one tg initial out.2), mul_one]
        _ = 1 := OracleComp.tsum_prEvent_eq_one _
    exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top hE) hsum
  have hle : budget 0 total + b0 * W ≤ 1 := le_trans hsat hE
  have hW1 : b0 * W ≤ 1 - budget 0 total := ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top hle
  rw [OracleComp.prEvent_bind_eq_tsum]
  calc _ ≤ ∑' out, Pr{let x ← interp tg initial model (advProgH parameter data M []) total start}[x = out] *
        ((1 - weight tg initial out.2) + weight tg initial out.2 * finalValue parameter data tg initial [] out) :=
        ENNReal.tsum_le_tsum fun out => mul_le_mul_right (hit_or_cover_le parameter data tg initial out) _
    _ = (1 - E) + ∑' out, Pr{let x ← interp tg initial model (advProgH parameter data M []) total start}[x = out] *
          (weight tg initial out.2 * finalValue parameter data tg initial [] out) := by
        rw [← hcompl, ← ENNReal.tsum_add]
        exact tsum_congr fun out => mul_add _ _ _
    _ ≤ (1 - (budget 0 total + b0 * W)) + (potO parameter data wbar b0 Fail tg initial Lmax start [] [] [] 0 total + b0 * W) :=
        add_le_add (tsub_le_tsub_left hsat _) hgood
    _ = (1 - budget 0 total) + potO parameter data wbar b0 Fail tg initial Lmax start [] [] [] 0 total := by
        rw [tsub_add_eq_tsub_tsub, add_comm (potO parameter data wbar b0 Fail tg initial Lmax start [] [] [] 0 total) (b0 * W),
          ← add_assoc, tsub_add_cancel_of_le hW1]
    _ ≤ _ := by
        refine le_trans (add_le_add le_rfl (potO_start_le parameter data wbar b0 Fail tg initial Lmax start total))
          (le_of_eq ?_)
        rw [hValueO_start]
        ring

end RestW

section ChainW

open HiddenBridge Completeness SeedModel _root_.FORS.Security.Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- The sampled signer's reads are good at any targeting that leaves message-digest inputs
untargeted. -/
theorem signerReadsGood_large (parameterOutput : HashOutput) (highs : CoordinateHighs)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (tg : Targeting HashInput HashOutput Coordinate) (hmsg : ∀ x, IsMsgInput x → tg.kind x = .none ∧ tg.digest x)
    (fixed : HiddenGraph.Table) (remaining : RemainingOutputs) (steps : Message → Randomness)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining)) :
    SignerReadsGood tg prepared.2 (sampleModel parameterOutput highs) (truncateHash parameterOutput)
      (sampleData parameterOutput fixed highs remaining steps) := by
  have h := PotentialA.signerReadsGood_sample parameterOutput highs prepared tg fixed remaining hprepared
  exact ⟨fun parameter' root message randomness call =>
      ⟨(h.digest parameter' root message randomness call).1,
        Or.inr (hmsg _ ⟨parameter', root, message, randomness, call, rfl⟩).1⟩,
    h.trialParse, h.searched⟩

set_option maxRecDepth 100000 in
/-- **One sample, weighted baseline**, the signer honest. -/
theorem sample_boundW (hb : 0 < keptHeight topLayer) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate)
    (hhit : ∀ table, tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table →
      ∀ s : State, Prepared prepared.2 s → Agrees s.known table →
        (CorrectGuess table s ∨
          CacheMatch.Bad (digestFreeTargets parameterOutput fixed highs remaining table prepared.1) s.cache) →
        Hit tg prepared.2 table s)
    (hcompat : Compatible tg (sampleModel parameterOutput highs)) (htrunc : UniformTruncation (R := HashOutput) tg)
    (hmsg : ∀ x, IsMsgInput x → tg.kind x = .none ∧ tg.digest x)
    (hclean : ∀ x, IsMsgInput x → prepared.2 x = none)
    (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared prepared.2 s1 →
      ∀ out ∈ support (interp tg prepared.2 (sampleModel parameterOutput highs)
        (finishRest (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps) m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (wbar : ℝ≥0∞) (htotal : 2 * ((q - keygenCost : ℕ) : ℝ) + 2 ≤ spaceReal) (Lmax : ℕ)
    (hfair : FairS wbar (q - keygenCost + digestAttemptLimit) Lmax) :
    Pr{let x ← (HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining steps))))
        (knownOf (truncateHash parameterOutput) fixed) prepared.2)}[(HiddenReveal.StopOr RichWin) x] ≤
      (1 - budget 0 (q - keygenCost)) + ((q - keygenCost : ℕ) * (hValueO (truncateHash parameterOutput)
        (sampleData parameterOutput fixed highs remaining steps) wbar (baselineW (q - keygenCost))
        (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) [] [] 0 signatureLimit
        (q - keygenCost) + failMass Fail) + signatureLimit * failMass Fail) + lam Lmax 0 (q - keygenCost) := by
  set param := truncateHash parameterOutput with hparam
  set data := sampleData parameterOutput fixed highs remaining steps with hdata
  set known := knownOf param fixed with hknown
  set model := sampleModel parameterOutput highs with hmodel
  set start : State := DebtState.start prepared.2 known with hstart
  have hparse : ∀ p call, model.parse (pblk param data p call) = none := fun p call =>
    hcompat.digestParse _ (hmsg _ (msgInput_digestInput param data.root p.1 p.2 call)).2
  refine le_trans (stopped_le_interp hb adversary q hq parameterOutput fixed highs remaining steps prepared hprepared tg) ?_
  -- a correct guess or a bad cache is a decided hit
  refine le_trans (prEvent_mono_of_support _ _ (fun r => Hit tg prepared.2 r.1 r.2.2 ∨ CoverOf param data r.2)
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
  unfold costGameXH
  by_cases hK : keygenCost ≤ q
  · rw [interp_tick_bind tg prepared.2 model _ _ q start hK, bind_map_left]
    refine le_trans (le_of_eq ?_) (rest_boundW param data wbar Fail tg prepared.2 model hcompat htrunc hparse
      (fun p call => (hmsg _ (msgInput_digestInput param data.root p.1 p.2 call)).1)
      (fun p call => (hmsg _ (msgInput_digestInput param data.root p.1 p.2 call)).2)
      (fun p call => hclean _ (msgInput_digestInput param data.root p.1 p.2 call)) hfail (q - keygenCost) htotal Lmax hfair
      (signerReadsGood_large parameterOutput highs prepared tg hmsg fixed remaining steps hprepared)
      ((internalize adversary).main ⟨data.root, param⟩)
      (noRepeat_internalize_adversary adversary hnr _) known)
    rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
    refine tsum_congr fun out => ?_
    rw [prEvent_map, prEvent_map]
    rfl
  · rw [interp_tick_bind_abort tg prepared.2 model _ _ q start hK, pure_bind]
    refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun x hx hp => ?_) bot_le
    rw [support_map] at hx
    obtain ⟨table, _, rfl⟩ := hx
    rcases hp with hh | ⟨outcome, hres, _⟩
    · exact not_hit_start tg prepared.2 known table hh
    · cases hres

set_option maxRecDepth 100000 in
/-- **Large budgets from the honest seed-free win, weighted baseline.** The seed-free win is at most the
weighted saturation budget, `q - keygenCost` times the one-coin excess forecast at the baseline
`baselineW (q - keygenCost)`, and the failing share of the prepared searches. -/
theorem large_seedFree_boundW (hb : 0 < keptHeight topLayer) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (steps : Message → Randomness) (hq : q < 2 ^ 256)
    (htarget : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      ∃ tg : Targeting HashInput HashOutput Coordinate,
        Compatible tg (sampleModel parameterOutput highs) ∧ UniformTruncation (R := HashOutput) tg ∧
        (∀ x, IsMsgInput x → tg.kind x = .none ∧ tg.digest x) ∧
        ∀ table, tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table →
          ∀ s : State, Prepared prepared.2 s → Agrees s.known table →
            (CorrectGuess table s ∨
              CacheMatch.Bad (digestFreeTargets parameterOutput fixed highs remaining table prepared.1) s.cache) →
            Hit tg prepared.2 table s)
    (hclean : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) → ∀ x, IsMsgInput x → prepared.2 x = none)
    (wbar : ℝ≥0∞) (Lmax : ℕ) (hfair : FairS wbar (q - keygenCost + digestAttemptLimit) Lmax)
    (htotal : 2 * ((q - keygenCost : ℕ) : ℝ) + 2 ≤ spaceReal) :
    Pr{let z ← AdvCount.seedFreeExperiment (internalize adversary) q steps}[Win z] ≤
      ((1 - budget 0 (q - keygenCost)) + (q - keygenCost : ℕ) * startExcessO wbar (baselineW (q - keygenCost))
        (q - keygenCost) + lam Lmax 0 (q - keygenCost)) +
      ((q - keygenCost : ℕ) + signatureLimit) * expectedFail := by
  refine le_trans (HiddenBridge.seedFree_le_prep adversary q steps) ?_
  set A := (1 - budget 0 (q - keygenCost)) + (q - keygenCost : ℕ) * startExcessO wbar (baselineW (q - keygenCost))
    (q - keygenCost) + lam Lmax 0 (q - keygenCost) with hA
  set C : ℝ≥0∞ := ((q - keygenCost : ℕ) + signatureLimit) with hC
  -- one sample
  have hsample : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      Pr{let x ← (HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgramH (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining steps))))
          (knownOf (truncateHash parameterOutput) fixed) prepared.2)}[(HiddenReveal.StopOr RichWin) x] ≤ A + C * failMass (failSet prepared.1) := by
    intro parameterOutput fixed highs remaining prepared hprepared
    obtain ⟨tg, hcompat, htrunc, hmsg, hhit⟩ := htarget parameterOutput fixed highs remaining prepared hprepared
    refine le_trans (sample_boundW hb adversary hnr q hq parameterOutput fixed highs remaining steps prepared hprepared tg hhit
      hcompat htrunc hmsg (hclean _ _ _ _ _ hprepared) (failSet prepared.1)
      (fun m ρ digest budget s1 hprep out hout hnone => finishRest_fail parameterOutput fixed highs remaining steps prepared
        hprepared tg m ρ digest budget s1 hprep out hout hnone) wbar htotal Lmax hfair) (le_of_eq ?_)
    rw [hValueO_start, hA, hC]
    push_cast
    ring
  -- average
  simp only [OracleComp.prEvent_bind_eq_tsum]
  refine le_trans (tsum_bound_le _ _ A C (fun parameterOutput => ∑' fixed, Pr{let x ← ($ᵗ HiddenGraph.Table : ProbComp HiddenGraph.Table)}[x = fixed] *
    ∑' highs, Pr{let x ← ($ᵗ CoordinateHighs : ProbComp CoordinateHighs)}[x = highs] *
    ∑' remaining, Pr{let x ← ($ᵗ RemainingOutputs : ProbComp RemainingOutputs)}[x = remaining] *
    ∑' prepared, Pr{let x ← preparation parameterOutput fixed highs remaining}[x = prepared] *
      failMass (failSet prepared.1)) fun parameterOutput _ => ?_) le_rfl
  refine tsum_bound_le _ _ A C _ fun fixed _ => ?_
  refine tsum_bound_le _ _ A C _ fun highs _ => ?_
  refine tsum_bound_le _ _ A C _ fun remaining _ => ?_
  exact tsum_bound_le _ _ A C _ fun prepared hprepared =>
    hsample parameterOutput fixed highs remaining prepared hprepared

set_option maxRecDepth 100000 in
/-- **Large budgets, weighted baseline, honest-reading game.** For an adversary making at most `qA`
hash queries and a verifier making at most `V`, at the budget `q = keygenHashCost + qA + V`: if the
large-budget inequality `hH0` with the weighted baseline holds at `q`,
the forging advantage is at most `q / 2^127`. -/
theorem forgeAdvantage_le_largeWH (hb : 0 < keptHeight topLayer) (hN : signatureLimit ≤ 2 ^ 70) (adversary : Adversary)
    (qA V : ℕ) (hqA : ∀ pk, (adversary.main pk).IsQueryBoundP AdvCount.AdvHash qA)
    (hV : ∀ pk message signature,
      (Concrete.verify pk message signature : OracleComp HashSpec Bool).IsQueryBoundP (fun _ => True) V)
    (q : ℕ) (hqdef : q = Prefix.keygenHashCost + qA + V) (hq : q < 2 ^ 127)
    (hfairq : q - keygenCost + 2 ^ 32 + (H0.scanM - 1) * H0.LmaxOf (q - keygenCost) + (2 * H0.scanM - 1) ≤ 2 ^ 128)
    (hH0 : (1 - budget 0 (q - keygenCost)) + ((q - keygenCost : ℕ) : ℝ≥0∞) *
        startExcessO (H0.wbarOf (q - keygenCost)) (baselineW (q - keygenCost)) (q - keygenCost) +
        ((q - keygenCost + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q - keygenCost + keygenCost : ℕ) : ℝ≥0∞) / 2 ^ 127) :
    forgeAdvantage adversary ≤ q / 2 ^ 127 := by
  have hK : keygenCost ≤ q := by unfold keygenCost; omega
  set q' := q - keygenCost with hq'
  have hsum : q' + keygenCost = q := by omega
  have hq'le : 2 * q' ≤ 2 ^ 128 := by omega
  have htotal : 2 * ((q' : ℕ) : ℝ) + 2 ≤ spaceReal := by
    unfold spaceReal
    have : (2 * q' + 2 : ℕ) ≤ 2 ^ 128 := by omega
    exact_mod_cast this
  have hmain := fun steps => large_seedFree_boundW hb (Memo.memoAdv adversary) (Memo.memoAdv_noRepeat adversary) q
    steps (by omega) (fun _ _ _ _ _ hprep => targetingAll hb _ _ _ _ _ hprep)
    (fun _ _ _ _ _ hprep => prepared_clean _ _ _ _ _ hprep) (H0.wbarOf q') (H0.LmaxOf q') (H0.fair_of q' hfairq) htotal
  have hF := AdvCount.forgeAdvantage_le_seedFree adversary qA V hqA hV _ (by rw [← hqdef]; exact hmain)
  rw [← hqdef] at hF
  refine le_trans hF (le_trans (add_le_add le_rfl (mul_le_mul_left (by norm_num : (2 : ℝ≥0∞) ≤ 3) _)) ?_)
  have hE := expectedFail_le
  -- the negligible terms fit in the slack
  have hK1 : 1 ≤ keygenCost := by
    have := Nat.two_pow_pos (keptHeight topLayer)
    unfold keygenCost Prefix.keygenHashCost
    omega
  have hlam : lam (H0.LmaxOf q') 0 q' ≤ (2 : ℝ≥0∞)⁻¹ ^ 201 := by
    refine le_trans (H0.lam_start q') ?_
    have h2 : (2 : ℝ≥0∞)⁻¹ ^ 201 = ENNReal.ofReal ((1 / 2 : ℝ) ^ 201) := by
      rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [h2]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (64 / 65 : ℝ) ^ (2 ^ 15 : ℕ) = ((64 / 65 : ℝ) ^ 64) ^ 512 := by rw [← pow_mul]; norm_num
      _ ≤ (1 / 2 : ℝ) ^ 512 := pow_le_pow_left₀ (by norm_num) (by norm_num) 512
      _ ≤ (1 / 2 : ℝ) ^ 201 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
  have hslack : ((q' : ℝ≥0∞) + signatureLimit) * expectedFail + 3 * ((q : ℝ≥0∞) / 2 ^ 256) +
      lam (H0.LmaxOf q') 0 q' ≤ ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 := by
    have h256 : 3 * ((q : ℝ≥0∞) / 2 ^ 256) ≤ (((q' + keygenCost : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 201 := by
      rw [div_two_pow, hsum, mul_left_comm]
      refine mul_le_mul' le_rfl ?_
      rw [show (256 : ℕ) = 55 + 201 by norm_num, pow_add, ← mul_assoc]
      calc 3 * (2 : ℝ≥0∞)⁻¹ ^ 55 * (2 : ℝ≥0∞)⁻¹ ^ 201 ≤ 1 * (2 : ℝ≥0∞)⁻¹ ^ 201 := by
            refine mul_le_mul' ?_ le_rfl
            rw [show (55 : ℕ) = 2 + 53 by norm_num, pow_add, ← mul_assoc]
            calc 3 * (2 : ℝ≥0∞)⁻¹ ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 53 ≤ 1 * 1 := by
                  refine mul_le_mul' ?_ (pow_le_one₀ (by norm_num) (by norm_num))
                  rw [← ENNReal.inv_pow, ← div_eq_mul_inv, ENNReal.div_le_iff (by norm_num) (by norm_num), one_mul]
                  norm_num
              _ = 1 := one_mul 1
        _ = _ := one_mul _
    have hnat : ((q' : ℝ≥0∞) + signatureLimit) + ((q' + keygenCost : ℕ) : ℝ≥0∞) + 1 ≤
        2 * ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) := by
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
  calc _ ≤ (((1 - budget 0 q') + (q' : ℝ≥0∞) * startExcessO (H0.wbarOf q') (baselineW q') q' +
            lam (H0.LmaxOf q') 0 q') +
          ((q' : ℕ) + signatureLimit) * expectedFail) + 3 * ((q : ℝ≥0∞) / 2 ^ 256) := le_rfl
    _ = ((1 - budget 0 q') + (q' : ℝ≥0∞) * startExcessO (H0.wbarOf q') (baselineW q') q') +
          (((q' : ℝ≥0∞) + signatureLimit) * expectedFail + 3 * ((q : ℝ≥0∞) / 2 ^ 256) +
            lam (H0.LmaxOf q') 0 q') := by
        ring
    _ ≤ ((1 - budget 0 q') + (q' : ℝ≥0∞) * startExcessO (H0.wbarOf q') (baselineW q') q') +
          ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 := add_le_add le_rfl hslack
    _ ≤ ((q' + keygenCost : ℕ) : ℝ≥0∞) / 2 ^ 127 := hH0
    _ = (q : ℝ≥0∞) / 2 ^ 127 := by rw [hsum]

end ChainW

end FORS.Security.ForsPotential
