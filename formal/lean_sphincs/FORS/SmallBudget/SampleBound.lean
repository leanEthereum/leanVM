module

public import FORS.SmallBudget.SampleEvents
public import FORS.SmallBudget.Contact.SigningH
public import FORS.SmallBudget.Linear.HonestSignerFrom

@[expose] public section

/-! **One sample of the small-budget route, the signer honest.** The game whose signer reads
honestly (`costGameXH`: key generation's tick, then `advProgH`), interpreted from a prepared
state with the above-word values exposed, is paid by the linear potential, the one-coin cover
potential and the contact bound (`sample_boundF`): the linear potential holds under the honest reads of the route's class from a prepared state
(`smallRoute_potentialHFrom`, through `honestWithFrom_advProgH`), the one-coin cover potential
over `advProgH` (`goodOH_advProgH`) and the contact bound with the honest signing call paid
(`a4F_bound` with `psiF_sign` and `signInvH`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenDebt

variable [Params]

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false

variable {D R A ι : Type} [Fintype ι] [SampleableType R] {H : Type} [HonestInputs H D]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- **An invariant at every final state of a run whose honest reads are of a class `P` from a
prepared state**, when every step keeps it and it keeps the state prepared. -/
theorem interp_inv_from (P : D → Prop) (hP : ∀ x, P x → model.parse x = none) (Inv : DebtState D R ι → Prop)
    (hprep : ∀ state, Inv state → Prepared initial state)
    (hstep : ∀ (input : (SourceCostSpec D R ι H).Domain) state, Inv state →
      (∀ honest, input = .inr (.inr honest) → P (HonestInputs.toInput honest)) →
      ∀ result ∈ support (costStep model input state), Inv result.2)
    {α : Type} (computation : OracleComp (SourceCostSpec D R ι H) α) (hhonest : HonestWithFrom initial P computation) :
    ∀ budget state, Inv state → ∀ out ∈ support (interp tg initial model computation budget state), Inv out.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state hs out hout
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      rw [hout]
      exact hs
  | query_bind input next ih =>
      intro budget state hs out hout
      obtain ⟨hin, hrest⟩ := (honestWithFrom_query_bind initial P input next).1 hhonest
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, hresult, inner, hinner, rfl⟩ := hout
        have hallowed := allowed_of_prepared initial model input state (hprep state hs)
          (fun honest he => hP _ (hin honest he)) result hresult
        exact ih result.1 (hrest result.1 hallowed) _ result.2 (hstep input state hs hin result hresult) inner hinner
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout]
        exact hs

end FORS.Security.HiddenDebt

namespace FORS.Security.ForsPotential

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
  FORS.Base.Domination
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

open Completeness SeedModel _root_.FORS.Security.Graph Assembly Reduce Internalize in
attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-! ### The honest game with its outcome -/

section GameXH

variable (parameter : PublicParameter) (data : PublicData)

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A leading tick only shortens the budget. -/
theorem interp_tick_bind {β : Type} (amount : ℕ) (next : Unit → OracleComp CostSpecH β) (budget : ℕ) (s : State)
    (h : amount ≤ budget) :
    interp tg initial model (HiddenCost.tick (H := HashInput) amount >>= next) budget s =
      (fun out => ((out.1.1, out.1.2.1, Sum.inr amount :: out.1.2.2.1, out.1.2.2.2), out.2)) <$>
        interp tg initial model (next ()) (budget - amount) s := by
  unfold HiddenCost.tick
  rw [interp_query_bind]
  split_ifs with hc
  · change (pure ((), s) : ProbComp _) >>= _ = _
    rw [pure_bind]
    rfl
  · exact absurd h hc

theorem interp_tick_bind_abort {β : Type} (amount : ℕ) (next : Unit → OracleComp CostSpecH β) (budget : ℕ)
    (s : State) (h : ¬amount ≤ budget) :
    interp tg initial model (HiddenCost.tick (H := HashInput) amount >>= next) budget s = pure ((none, [], [], []), s) := by
  unfold HiddenCost.tick
  rw [interp_query_bind]
  split_ifs with hc
  · exact absurd hc h
  · rfl

/-! ### Honest reads of the honest game -/

/-- A raw-lifted hash computation reads nothing honestly. -/
theorem honestWithFrom_liftRawH (P : HashInput → Prop) {α : Type} (computation : OracleComp HashSpec α) :
    HonestWithFrom initial P (liftRawH computation) := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      rw [liftRawH_pure]
      exact honestWithFrom_pure initial P value
  | query_bind query rest ih =>
      rw [liftRawH_query_bind]
      exact (honestWithFrom_query_bind initial P _ _).2 ⟨fun _ he => (by cases he), fun value _ => ih value⟩

/-- **The honest reads of the honest game are the signer's**: the adversary's draws and hash
queries and the verification are raw. -/
theorem honestWithFrom_advProgH (P : HashInput → Prop)
    (hsign : ∀ message, HonestWithFrom initial P (signCostSourceH parameter data message)) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      HonestWithFrom initial P (advProgH parameter data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L
      rw [advProgH_pure]
      unfold finishGameH
      exact honestWithFrom_bind initial P (honestWithFrom_liftRawH initial P _) fun _ => honestWithFrom_pure initial P _
  | query_bind input next ih =>
      intro L
      rcases input with (draw | bytes) | message
      · rw [advProgH_draw]
        exact (honestWithFrom_query_bind initial P _ _).2 ⟨fun _ he => (by cases he), fun value _ => ih value L⟩
      · rw [advProgH_hash]
        exact (honestWithFrom_query_bind initial P _ _).2 ⟨fun _ he => (by cases he), fun value _ => ih value L⟩
      · rw [advProgH_sign]
        exact honestWithFrom_bind initial P (hsign message) fun r => ih r _

theorem honestWithFrom_costGameXH (P : HashInput → Prop) {adversary : Adversary}
    (h : HonestWithFrom initial P (advProgH parameter data (adversary.main ⟨data.root, parameter⟩) [])) :
    HonestWithFrom initial P (costGameXH parameter data adversary) := by
  unfold costGameXH HiddenCost.tick
  exact (honestWithFrom_query_bind initial P _ _).2 ⟨fun _ he => (by cases he), fun _ _ => h⟩

end GameXH

/-! ### The sampled signer's reads and the pointwise split -/

section Sample

open Completeness SeedModel _root_.FORS.Security.Graph Assembly Reduce Internalize

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)

/-- `signerReadsGood_sample` for any digest steps (the reads do not depend on them). -/
theorem signerReadsGood_steps (tg : Targeting HashInput HashOutput Coordinate)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining)) (steps : Message → Randomness) :
    SignerReadsGood (msgTargeting tg) prepared.2 (sampleModel parameterOutput highs) (truncateHash parameterOutput)
      (sampleData parameterOutput fixed highs remaining steps) :=
  have h := signerReadsGood_sample parameterOutput highs prepared tg fixed remaining hprepared
  ⟨h.digest, h.trialParse, h.searched⟩

/-- **Pointwise split** of a final state with the invariant and a table extending the fixed
knowledge, for any program. -/
theorem small_pointwise_of (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : Knowledge Coordinate) (ρ : ℝ)
    (steps : Message → Randomness) (out : Run HashInput Coordinate HiddenBridge.Outcome × State)
    (hinv : (ctxA parameterOutput fixed highs remaining prepared known ρ).Inv out.2)
    (T : Coordinate → Digest) (hTe : tableExtending out.2.known T = T)
    (hfix : tableExtending (knownOf (truncateHash parameterOutput) fixed) T = T)
    (h : CorrectGuess T out.2 ∨ badAV parameterOutput fixed highs remaining prepared.1 T
      (((out.1.1, out.1.2.1), out.1.2.2.1), out.2.cache)) :
    payoffA parameterOutput fixed highs remaining prepared known ρ T out.2 = 1 ∨
      (∃ outcome, out.1.1 = some outcome ∧ SigningTranscript.Valid outcome.2.1 ∧
        A4ev (ctxA parameterOutput fixed highs remaining prepared known ρ)
          (sampleData parameterOutput fixed highs remaining).root T out.2 outcome out.1.2.1) ∨
      finalValue (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
        (targetingA parameterOutput fixed highs remaining prepared.1) prepared.2 [] out = 1 := by
  set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hK
  have hpay : Hit K.tg prepared.2 T out.2 → payoffA parameterOutput fixed highs remaining prepared known ρ T out.2 = 1 := by
    intro hh
    unfold payoffA Ctx.payoff
    exact ite_eq_left (Or.inl hh)
  rcases h with hg | ⟨hbad, outcome, hres, hvalid⟩
  · exact Or.inl (hpay (hit_of_correctGuess parameterOutput fixed highs remaining prepared known ρ out.2 T hTe hg))
  · rcases badA_split parameterOutput fixed highs remaining prepared hprepared known ρ out.2 hinv T hTe hfix
      out.1.1 out.1.2.1 out.1.2.2.1 hbad with hp | ⟨index, c, sp, hrev, hrec⟩ | ⟨outcome', hres', hnear | hcov⟩
    · exact Or.inl hp
    · exact Or.inr (Or.inl ⟨outcome, hres, hvalid, Or.inl ⟨index, c, sp, hrev, hrec⟩⟩)
    · exact Or.inr (Or.inl ⟨outcome', hres', hnear.1, Or.inr hnear⟩)
    · by_cases hreal : Realized K.tg prepared.2 out.2
      · exact Or.inl (hpay (Or.inl hreal))
      · refine Or.inr (Or.inr ?_)
        unfold finalValue
        rw [hres']
        simp only [Option.elim, List.nil_append]
        exact ite_eq_left ⟨hcov, hreal⟩

end Sample

theorem ofReal_le_two_halfF (c : ℚ) : ENNReal.ofReal (c : ℝ) ≤ 2 * ENNReal.ofReal ((c / 2 : ℚ) : ℝ) := by
  calc ENNReal.ofReal (c : ℝ) = ENNReal.ofReal (2 * ((c / 2 : ℚ) : ℝ)) := by
        congr 1
        push_cast
        ring
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal ((c / 2 : ℚ) : ℝ) := le_of_eq (ENNReal.ofReal_mul (by norm_num))
    _ = _ := by rw [ENNReal.ofReal_ofNat]

section SampleFH

open Completeness SeedModel _root_.FORS.Security.Graph Assembly Reduce Internalize

set_option maxRecDepth 100000 in
/-- **One sample of the small-budget route, the signer honest.** The interpreted honest game with
the above-word values exposed: a correct guess or the refined bad event is paid by the linear
potential, the one-coin cover potential and the contact bound. -/
theorem sample_boundF (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness) (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : Knowledge Coordinate)
    (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed)))
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (κ : ℝ) (hκ : 2 - ρ + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * (((2 : ℝ) ^ subtreeHeight * 2 ^ forsHeight)⁻¹) ≤ κ) (hκ1 : κ ≤ 1)
    (H b k a N : ℕ) (hHH : totalHeight = H) (hbb : subtreeHeight = b) (hkk : forsTrees = k)
    (haa : forsHeight = a) (hNN : signatureLimit = N)
    (t : H0.PoisT) (o : H0.Opt) (on : H0.OptN) (hpt : H0.checkPT t = true) (qtop : ℕ)
    (hrt : H0.checkRate H b N qtop t = true) (hqtop : q - keygenCost ≤ qtop)
    (ho : H0.checkOpt H b k a t o = true) (hon : H0.checkOptN H k a t on = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128) :
    Pr{let x ← (interp (targetingA parameterOutput fixed highs remaining prepared.1) prepared.2
        (sampleModel parameterOutput highs)
        (costGameXH (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
          (internalize adversary)) q (DebtState.start prepared.2 known) >>=
        fun result => (fun table => (table, result)) <$> completion result.2.known)}[CorrectGuess x.1 x.2.2 ∨
        badAV parameterOutput fixed highs remaining prepared.1 x.1 (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache)] ≤
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
  set data := sampleData parameterOutput fixed highs remaining steps with hdata
  set model := sampleModel parameterOutput highs with hmodel
  set tgA := targetingA parameterOutput fixed highs remaining prepared.1 with htgA
  set start : State := DebtState.start prepared.2 known with hstart
  set run := interp tgA prepared.2 model (costGameXH param data (internalize adversary)) q start with hrun
  set b0 : ℝ≥0∞ := ENNReal.ofReal (ρ / 2 ^ 128) with hb0
  set pay := payoffA parameterOutput fixed highs remaining prepared known ρ with hpay'
  set q' := q - keygenCost with hq'
  set φ := failMass (failSet prepared.1) with hφ
  set c0 : ℝ≥0∞ := ENNReal.ofReal ((ρ - 1 - ((q' : ℕ) : ℝ) / 2 ^ 128) / 2 ^ 128) with hc0
  set IsF := IsFleafIn param with hIsF
  set κE : ℝ≥0∞ := ENNReal.ofReal κ with hκE
  set payB : ℝ≥0∞ := ν * ENNReal.ofReal (1 - κ) with hpayB
  set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hK
  set wbar := H0.wbarOf q' with hwbar
  set c := (2 ^ b * on.En : ℚ) with hc
  set Fset := failSet prepared.1 with hFset
  set Lmax := H0.LmaxOf q' with hLmax
  have hfair : FairS wbar (q' + 2 ^ 32) Lmax := H0.fair_of q' (H0.fair_of_rate H b N qtop t hrt hHH hbb q' hqtop)
  have hQ : q' ≤ q' + 2 ^ 32 := Nat.le_add_right _ _
  have hmsg : ∀ x, IsMsgInput x → tgA.kind x = .none := fun x h =>
    targetingA_msgF parameterOutput fixed highs remaining prepared.1 x h
  have hparse : ∀ p call, model.parse (pblk param data p call) = none := fun p call => by
    rw [hmodel, sampleModel_parse]
    cases h : HiddenGraph.parse param (candidateActive param) (pblk param data p call) with
    | none => rfl
    | some qq =>
        exfalso
        obtain ⟨hx, -⟩ := (parse_some_iff _ _ _ qq).1 h
        obtain ⟨p', root', message', randomness', call', heq⟩ := msgInput_digestInput param data.root p.1 p.2 call
        exact messageDigestInput_ne_tweakableHashInput p' param root' message' randomness' call' _
          (by rw [bytesLE_length]; omega) (heq.symm.trans hx)
  have hdigest : ∀ p call, tgA.digest (pblk param data p call) := fun p call =>
    msgInput_digestInput param data.root p.1 p.2 call
  have hclean : ∀ p call, prepared.2 (pblk param data p call) = none := fun p call =>
    prepared_clean parameterOutput fixed highs remaining prepared hprepared _
      (msgInput_digestInput param data.root p.1 p.2 call)
  have hfail : ∀ m ρ' digest budget (s1 : State), Prepared prepared.2 s1 →
      ∀ out ∈ support (interp tgA prepared.2 model (finishRest param data m ρ' digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fset :=
    fun m ρ' digest budget s1 hprep out hout hnone => finishRest_fail parameterOutput fixed highs remaining steps
      prepared hprepared tgA m ρ' digest budget s1 hprep out hout hnone
  have hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p) := sampleModel_parse parameterOutput highs
  have hMi : model.incoming = Address.inputCoordinate := sampleModel_incoming parameterOutput highs
  have hMo : model.outgoing = Address.outputCoordinate := sampleModel_outgoing parameterOutput highs
  have hnr' := noRepeat_internalize_adversary adversary hnr ⟨data.root, param⟩
  have hhon : ∀ M L, HonestWithFrom prepared.2 (SmallHonest parameterOutput highs prepared) (advProgH param data M L) :=
    honestWithFrom_advProgH param data prepared.2 _ (honestWithFrom_small_signCostSourceH parameterOutput highs
      prepared tgA param data (signerReadsGood_steps parameterOutput fixed highs remaining prepared tgA hprepared steps))
  -- the run after the keygen tick, or an aborted run
  have hrunK : ∀ hK : keygenCost ≤ q, run = (fun out => ((out.1.1, out.1.2.1, Sum.inr keygenCost :: out.1.2.2.1,
      out.1.2.2.2), out.2)) <$> interp tgA prepared.2 model
        (advProgH param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start := fun hK => by
    rw [hrun]
    unfold costGameXH
    rw [interp_tick_bind tgA prepared.2 model _ _ q start hK]
  have hrunA : ¬keygenCost ≤ q → run = pure ((none, [], [], []), start) := fun hK => by
    rw [hrun]
    unfold costGameXH
    exact interp_tick_bind_abort tgA prepared.2 model _ _ q start hK
  -- the linear potential with both payments
  have hA3 : ∑' out, Pr{let x ← run}[x = out] * (endValue pay out.2 + b0 * (digestCount tgA out.1.2.2.1 : ℝ≥0∞) +
      c0 * (fleafCount IsF out.1.2.2.1 : ℝ≥0∞)) ≤ ENNReal.ofReal (ρ * (q' : ℕ) / 2 ^ 128) := by
    by_cases hK : keygenCost ≤ q
    · rw [hrunK hK, OracleComp.tsum_prEvent_map_mul]
      refine le_trans (le_of_eq ?_) (smallRoute_potentialHFrom parameterOutput fixed highs remaining prepared known ρ hk
        tgA rfl q' hN (advProgH param data ((internalize adversary).main ⟨data.root, param⟩) []) (hhon _ _))
      refine tsum_congr fun out => ?_
      simp only [digestCount_cons_inrF, fleafCount_cons_inr]
      rfl
    · have hrunEq : run = interp tgA prepared.2 model (costGameXH param data (internalize adversary)) 0 start := by
        rw [hrunA hK]
        unfold costGameXH
        rw [interp_tick_bind_abort tgA prepared.2 model keygenCost _ 0 start (by omega)]
      rw [hrunEq]
      have hq0 : (q' : ℕ) = 0 := by omega
      rw [hc0, hq0]
      exact smallRoute_potentialHFrom parameterOutput fixed highs remaining prepared known ρ hk tgA rfl 0
        (numeric_monoF hN (by rw [hq0]) (by norm_num)) (costGameXH param data (internalize adversary))
        (honestWithFrom_costGameXH param data prepared.2 _ (hhon _ _))
  -- the cover potential
  have hcover : ∑' out, Pr{let x ← run}[x = out] * finalValue param data tgA prepared.2 [] out ≤
      (((q' : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + φ) + signatureLimit * φ) +
        lam Lmax 0 q' + b0 * ∑' out, Pr{let x ← run}[x = out] * (digestCount tgA out.1.2.2.1 : ℝ≥0∞) := by
    by_cases hK : keygenCost ≤ q
    · rw [hrunK hK, OracleComp.tsum_prEvent_map_mul, OracleComp.tsum_prEvent_map_mul]
      have hgood := goodOH_advProgH param data wbar b0 Fset q' Lmax tgA prepared.2 model
        hparse hdigest (fun p call => hmsg _ (msgInput_digestInput param data.root p.1 p.2 call))
        hfail hfair hQ ((internalize adversary).main ⟨data.root, param⟩) [] hnr' q' start [] [] 0 []
        (start_prepared prepared.2 known) (start_pinv param data prepared.2 hclean known)
        (start_minv param data prepared.2 hclean known)
        (fun _ _ _ _ h => by cases h)
        (countInvL_of_countInv param data q' (start_count param data prepared.2 hclean known q'))
      have hval : startExcessO wbar b0 q' ≤ ENNReal.ofReal (o.B : ℝ) :=
        H0.startExcessO_le_opt H b k a N qtop t o hrt hpt ho hHH hbb hkk haa hNN q' hqtop b0 (ENNReal.ofReal_le_ofReal hcthr)
      have hpot : potO param data wbar b0 Fset tgA prepared.2 Lmax start [] [] [] 0 q' ≤
          (((q' : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + φ) + signatureLimit * φ) + lam Lmax 0 q' := by
        refine le_trans (potO_start_le param data wbar b0 Fset tgA prepared.2 Lmax start q') ?_
        gcongr
      calc ∑' out, Pr{let x ← (interp tgA prepared.2 model
              (advProgH param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start)}[x = out] *
            finalValue param data tgA prepared.2 [] _
          = ∑' out, Pr{let x ← (interp tgA prepared.2 model
              (advProgH param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start)}[x = out] *
            finalValue param data tgA prepared.2 [] out := rfl
        _ ≤ potO param data wbar b0 Fset tgA prepared.2 Lmax start [] [] [] 0 q' +
            b0 * expectedFlagged tgA prepared.2 model
              (advProgH param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start := hgood
        _ ≤ _ := by
            gcongr
            refine le_trans (expectedFlagged_le_digestF tgA prepared.2 model _ q' start) (le_of_eq ?_)
            refine tsum_congr fun out => ?_
            simp [digestCount]
    · rw [hrunA hK, OracleComp.tsum_prEvent_pure_mul]
      refine le_trans (le_of_eq ?_) bot_le
      rfl
  -- the contact bound A4
  have hκspl : ν ≤ payB + κE * ν := arm_splitF κ
  have hA4 : ∑' out, Pr{let x ← run}[x = out] * finalA4 K data.root out.1.1 out.1.2.1 out.2 ≤
      ν * (((Nat.choose q' 2 : ℕ) : ℝ≥0∞) * rateS) +
        κE * ν * ((q' : ℕ) * ((q' : ℕ) * (ENNReal.ofReal ((c / 2 : ℚ) : ℝ) + φ) + signatureLimit * φ)) +
        lam Lmax 0 q' +
        (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) *
          ∑' out, Pr{let x ← run}[x = out] * (fleafCount IsF out.1.2.2.1 : ℝ≥0∞) := by
    by_cases hK : keygenCost ≤ q
    · rw [hrunK hK, OracleComp.tsum_prEvent_map_mul, OracleComp.tsum_prEvent_map_mul]
      have hinv := inv_start parameterOutput fixed highs remaining prepared known ρ hk
      have hb := a4F_bound K data wbar κE Fset model hMp hMi hparse hmsg hclean q' hfair hQ hκspl
        (psiF_sign K data wbar κE Fset q' model hMp hMi hMo hparse hmsg hfail hfair.le_one Lmax)
        (signInvH hMp hMi hparse) ((internalize adversary).main ⟨data.root, param⟩) hnr' known hinv
      unfold expCount at hb
      refine le_trans (le_trans (le_of_eq (tsum_congr fun out => rfl)) hb) ?_
      simp only [fleafCount_cons_inr]
      refine add_le_add ?_ le_rfl
      have hnear : startNearF wbar q' ≤ 2 * ENNReal.ofReal ((c / 2 : ℚ) : ℝ) :=
        le_trans (H0.hNearOf_le H b k a N qtop hHH hbb hkk haa hNN t on hrt hpt hon q' hqtop) (ofReal_le_two_halfF c)
      have hsum := start_sum_leF hfair.le_one q' φ _ hnear
      refine add_le_add (add_le_add le_rfl ?_) le_rfl
      exact mul_le_mul_right hsum _
    · rw [hrunA hK, OracleComp.tsum_prEvent_pure_mul]
      refine le_trans (le_of_eq ?_) bot_le
      rfl
  -- pointwise split and summation
  have hinvF : ∀ out ∈ support run, K.Inv out.2 := fun out hout =>
    interp_inv_from tgA prepared.2 model (SmallHonest parameterOutput highs prepared) (fun _ hx => hx.1) K.Inv
      (fun _ hs => hs.prepared) (fun input s hs hgood => K.inv_stepH model hMp hMi input s hs
        fun honest he => (hgood honest he).1)
      _ (honestWithFrom_costGameXH param data prepared.2 _ (hhon _ _)) q start
      (PotentialA.inv_start parameterOutput fixed highs remaining prepared known ρ hk) out hout
  have hfixF : ∀ out ∈ support run, ∀ T : Coordinate → Digest, tableExtending out.2.known T = T →
      tableExtending (knownOf param fixed) T = T := fun out hout T hT => by
    have hext := interp_extends tgA prepared.2 model _ q start out hout
    have hbase := (exposeR_known _ _ _ hk).1
    rw [← hT]
    exact tableExtending_of_extends _ _ (fun c v h => hext.2.1 c v (hbase c v h)) T
  show Pr{let x ← run >>= fun result => (fun table => (table, result)) <$> completion result.2.known}[
    CorrectGuess x.1 x.2.2 ∨ badAV parameterOutput fixed highs remaining prepared.1 x.1
      (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache)] ≤ _
  have hstep : ∀ out, Pr{let x ← run}[x = out] *
      Pr{let x ← (fun table => (table, out)) <$> completion out.2.known}[CorrectGuess x.1 x.2.2 ∨ badAV parameterOutput fixed highs remaining prepared.1 x.1
          (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache)] ≤
      Pr{let x ← run}[x = out] * ((endValue pay out.2 + finalValue param data tgA prepared.2 [] out) +
        finalA4 K data.root out.1.1 out.1.2.1 out.2) := by
    intro out
    by_cases hout : out ∈ support run
    · refine mul_le_mul_right ?_ _
      rw [prEvent_map]
      set E4 : (Coordinate → Digest) → Prop := fun T => ∃ outcome, out.1.1 = some outcome ∧
        SigningTranscript.Valid outcome.2.1 ∧ A4ev K data.root T out.2 outcome out.1.2.1 with hE4
      have hE4le : Pr{let x ← completion out.2.known}[E4 x] ≤ finalA4 K data.root out.1.1 out.1.2.1 out.2 := by
        cases hres : out.1.1 with
        | none =>
            refine le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun T _ h => ?_) bot_le
            obtain ⟨outcome, h1, -⟩ := h
            rw [hres] at h1
            cases h1
        | some outcome =>
            unfold finalA4
            rw [Option.elim_some]
            refine prEvent_mono_of_support _ _ _ fun T _ h => ?_
            obtain ⟨outcome', h1, h2, h3⟩ := h
            rw [hres] at h1
            cases h1
            exact ⟨h2, h3⟩
      calc _
          ≤ Pr{let T ← completion out.2.known}[pay T out.2 = 1 ∨ (E4 T ∨ finalValue param data tgA prepared.2 [] out = 1)] := by
            refine prEvent_mono_of_support _ _ _ fun T hT h => ?_
            have hTe : tableExtending out.2.known T = T := by
              unfold completion at hT
              rw [support_map] at hT
              obtain ⟨t, _, rfl⟩ := hT
              funext c
              simp only [tableExtending]
              cases out.2.known c <;> rfl
            rcases small_pointwise_of parameterOutput fixed highs remaining prepared hprepared known ρ
              steps out (hinvF out hout) T hTe (hfixF out hout T hTe) h with h1 | h2 | h3
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
            · exact Or.inr (Or.inr h3)
        _ ≤ Pr{let T ← completion out.2.known}[pay T out.2 = 1] +
            Pr{let T ← completion out.2.known}[E4 T ∨ finalValue param data tgA prepared.2 [] out = 1] :=
            prEvent_or_le _ _ _
        _ ≤ endValue pay out.2 + (finalA4 K data.root out.1.1 out.1.2.1 out.2 +
              finalValue param data tgA prepared.2 [] out) := by
            refine add_le_add (probEvent_le_endValueF pay out.2 _ fun T h => h) ?_
            refine le_trans (prEvent_or_le _ _ _) (add_le_add hE4le ?_)
            by_cases hf : finalValue param data tgA prepared.2 [] out = 1
            · rw [hf]
              exact (prEvent_le_one _)
            · exact le_of_eq_of_le (prEvent_eq_zero_of_forall_mem_support _ _ fun _ _ h => hf h) bot_le
        _ = _ := by ring
    · rw [(prEvent_eq_zero_of_not_mem_support _) hout, zero_mul, zero_mul]
  rw [OracleComp.prEvent_bind_eq_tsum]
  refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
  have hsplit : ∑' out, Pr{let x ← run}[x = out] * ((endValue pay out.2 + finalValue param data tgA prepared.2 [] out) +
        finalA4 K data.root out.1.1 out.1.2.1 out.2) =
      (∑' out, Pr{let x ← run}[x = out] * endValue pay out.2 +
        ∑' out, Pr{let x ← run}[x = out] * finalValue param data tgA prepared.2 [] out) +
        ∑' out, Pr{let x ← run}[x = out] * finalA4 K data.root out.1.1 out.1.2.1 out.2 := by
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr fun out => ?_
    ring
  rw [hsplit]
  set Ev := ∑' out, Pr{let x ← run}[x = out] * endValue pay out.2 with hEv
  set Efin := ∑' out, Pr{let x ← run}[x = out] * finalValue param data tgA prepared.2 [] out with hEfin
  set Ed := ∑' out, Pr{let x ← run}[x = out] * (digestCount tgA out.1.2.2.1 : ℝ≥0∞) with hEd
  set Ef := ∑' out, Pr{let x ← run}[x = out] * (fleafCount IsF out.1.2.2.1 : ℝ≥0∞) with hEf
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
  calc (Ev + Efin) + ∑' out, Pr{let x ← run}[x = out] * finalA4 K data.root out.1.1 out.1.2.1 out.2
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

end SampleFH

end FORS.Security.ForsPotential
