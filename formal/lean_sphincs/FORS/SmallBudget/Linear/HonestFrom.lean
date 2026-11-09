module

public import FORS.SmallBudget.Linear.ForsSteps
public import FORS.LazyRun.HonestReadFrom

@[expose] public section

/-! Honest reads of a class from a prepared state. `HonestWith P` asks every honest read along
every answer to be of the class `P`; an honest search that stops at its first success then fails
it at the trials past it, which no run from a prepared state reaches. `HonestWithFrom` asks it
only along the answers a prepared state gives (`AllowedAnswer`), and the small route's linear
potential holds under it: an unparsed honest read of a prepared input is answered from the
cache. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.HiddenDebt

variable [Params]

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable {D R A ι : Type} [Fintype ι] [SampleableType R] {H : Type} [HonestInputs H D]
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- Every honest read the computation can reach from a prepared state stands for a raw input of
the class `P`. -/
def HonestWithFrom (P : D → Prop) {α : Type} (computation : OracleComp (SourceCostSpec D R ι H) α) : Prop :=
  OracleComp.construct (fun _ => True)
    (fun input _ next =>
      (∀ honest, input = .inr (.inr honest) → P (HonestInputs.toInput honest)) ∧
        ∀ value, AllowedAnswer initial input value → next value)
    computation

omit [Fintype ι] [SampleableType R] in
theorem honestWithFrom_pure (P : D → Prop) {α : Type} (value : α) :
    HonestWithFrom (R := R) (ι := ι) (H := H) initial P (pure value : OracleComp (SourceCostSpec D R ι H) α) :=
  trivial

omit [Fintype ι] [SampleableType R] in
theorem honestWithFrom_query_bind (P : D → Prop) {α : Type} (input : (SourceCostSpec D R ι H).Domain)
    (next : (SourceCostSpec D R ι H).Range input → OracleComp (SourceCostSpec D R ι H) α) :
    HonestWithFrom initial P (liftM ((SourceCostSpec D R ι H).query input) >>= next) ↔
      (∀ honest, input = .inr (.inr honest) → P (HonestInputs.toInput honest)) ∧
        ∀ value, AllowedAnswer initial input value → HonestWithFrom initial P (next value) :=
  Iff.rfl

omit [Fintype ι] [SampleableType R] in
theorem honestWithFrom_bind (P : D → Prop) {α β : Type} {first : OracleComp (SourceCostSpec D R ι H) α}
    {next : α → OracleComp (SourceCostSpec D R ι H) β} (hfirst : HonestWithFrom initial P first)
    (hnext : ∀ value, HonestWithFrom initial P (next value)) : HonestWithFrom initial P (first >>= next) := by
  induction first using OracleComp.inductionOn with
  | pure value => simpa only [pure_bind] using hnext value
  | query_bind input rest ih =>
      rw [bind_assoc, honestWithFrom_query_bind]
      obtain ⟨hin, hrest⟩ := (honestWithFrom_query_bind initial P input rest).1 hfirst
      exact ⟨hin, fun value hv => ih value (hrest value hv)⟩

omit [Fintype ι] [SampleableType R] in
theorem honestWithFrom_mono {P Q : D → Prop} (hPQ : ∀ x, P x → Q x) {α : Type}
    {computation : OracleComp (SourceCostSpec D R ι H) α} (h : HonestWithFrom initial P computation) :
    HonestWithFrom initial Q computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact honestWithFrom_pure initial Q value
  | query_bind input next ih =>
      obtain ⟨hin, hrest⟩ := (honestWithFrom_query_bind initial P input next).1 h
      exact (honestWithFrom_query_bind initial Q input next).2
        ⟨fun honest he => hPQ _ (hin honest he), fun value hv => ih value (hrest value hv)⟩

omit [Fintype ι] in
/-- From a prepared state, a step answers every unparsed honest read with its prepared answer. -/
theorem allowed_of_prepared (input : (SourceCostSpec D R ι H).Domain) (state : DebtState D R ι)
    (hprepared : Prepared initial state)
    (hunparsed : ∀ honest, input = .inr (.inr honest) → model.parse (HonestInputs.toInput honest) = none) :
    ∀ result ∈ support (costStep model input state), AllowedAnswer initial input result.1 := by
  intro result hresult
  rcases input with (draw | bytes) | (amount | honest)
  · trivial
  · trivial
  · trivial
  · intro output hout
    rw [costStep_honest, costStep_inl, lazyStep_unparsed model _ state (hunparsed honest rfl),
      readOutside_cached _ state output (hprepared _ output hout), support_pure, Set.mem_singleton_iff] at hresult
    rw [hresult]

/-- **Linear potential with two payments on the interpreter, honest reads of a class `P` from a
prepared state.** The honest reads are constrained only along the
answers a prepared state gives; the class is unparsed and the invariant keeps the state
prepared. -/
theorem interp_potential2 {α : Type} (P : D → Prop) (hP : ∀ x, P x → model.parse x = none)
    (IsFleaf : D → Prop) (Inv : DebtState D R ι → Prop) (hprep : ∀ state, Inv state → Prepared initial state)
    (Φ : ℕ → DebtState D R ι → ℝ≥0∞) (payoff : (ι → Digest) → DebtState D R ι → ℝ≥0∞) (pay pay2 : ℝ≥0∞)
    (hfinal : ∀ budget state, Inv state → endValue payoff state ≤ Φ budget state)
    (hstep : ∀ (input : (SourceCostSpec D R ι H).Domain) budget state, Inv state → sourceCost input ≤ budget →
      (∀ honest, input = .inr (.inr honest) → P (HonestInputs.toInput honest)) →
      ∑' result, Pr{let x ← costStep model input state}[x = result] * Φ (budget - sourceCost input) result.2 +
        pay * digestCount tg (recorded input) + pay2 * fleafCount IsFleaf (recorded input) ≤ Φ budget state)
    (hinv : ∀ (input : (SourceCostSpec D R ι H).Domain) state, Inv state →
      (∀ honest, input = .inr (.inr honest) → P (HonestInputs.toInput honest)) →
      ∀ result ∈ support (costStep model input state), Inv result.2)
    (computation : OracleComp (SourceCostSpec D R ι H) α) (hhonest : HonestWithFrom initial P computation) :
    ∀ budget state, Inv state →
      ∑' out, Pr{let x ← interp tg initial model computation budget state}[x = out] *
        (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 + pay2 * fleafCount IsFleaf out.1.2.2.1) ≤
          Φ budget state := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state hstate
      rw [interp_pure, OracleComp.tsum_prEvent_pure_mul]
      simpa [digestCount, fleafCount] using hfinal budget state hstate
  | query_bind input next ih =>
      intro budget state hstate
      obtain ⟨hin, hrest⟩ := (honestWithFrom_query_bind initial P input next).1 hhonest
      rw [interp_query_bind]
      split_ifs with hcost
      · rw [OracleComp.tsum_prEvent_bind_mul]
        set c : ℝ≥0∞ := pay * digestCount tg (recorded input) + pay2 * fleafCount IsFleaf (recorded input)
          with hc
        calc ∑' result, Pr{let x ← costStep model input state}[x = result] *
              ∑' out, Pr{let x ← ((fun out => ((out.1.1, revealed input ++ out.1.2.1,
                  recorded input ++ out.1.2.2.1, touch tg initial state input ++ out.1.2.2.2), out.2)) <$>
                interp tg initial model (next result.1) (budget - sourceCost input) result.2)}[x = out] *
                (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 + pay2 * fleafCount IsFleaf out.1.2.2.1)
            ≤ ∑' result, Pr{let x ← costStep model input state}[x = result] *
                (Φ (budget - sourceCost input) result.2 + c) := by
              refine ENNReal.tsum_le_tsum fun result => ?_
              by_cases hr : result ∈ support (costStep model input state)
              · refine mul_le_mul_right ?_ _
                have hallowed := allowed_of_prepared initial model input state (hprep state hstate)
                  (fun honest he => hP _ (hin honest he)) result hr
                rw [OracleComp.tsum_prEvent_map_mul]
                simp only [digestCount_append, fleafCount_append, Nat.cast_add]
                calc ∑' out, Pr{let x ← (interp tg initial model (next result.1) (budget - sourceCost input)
                        result.2)}[x = out] *
                      (endValue payoff out.2 + pay * ((digestCount tg (recorded input) : ℝ≥0∞) +
                        digestCount tg out.1.2.2.1) + pay2 * ((fleafCount IsFleaf (recorded input) : ℝ≥0∞) +
                        fleafCount IsFleaf out.1.2.2.1))
                    = ∑' out, Pr{let x ← (interp tg initial model (next result.1) (budget - sourceCost input)
                          result.2)}[x = out] *
                        (endValue payoff out.2 + pay * digestCount tg out.1.2.2.1 +
                          pay2 * fleafCount IsFleaf out.1.2.2.1) +
                      (∑' out, Pr{let x ← (interp tg initial model (next result.1)
                        (budget - sourceCost input) result.2)}[x = out]) * c := by
                      rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
                      refine tsum_congr fun out => ?_
                      rw [hc]
                      ring
                  _ ≤ Φ (budget - sourceCost input) result.2 + 1 * c :=
                      add_le_add (ih result.1 (hrest result.1 hallowed) _ _ (hinv input state hstate hin result hr))
                        (mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl)
                  _ = _ := by rw [one_mul]
              · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul, zero_mul]
          _ = ∑' result, Pr{let x ← costStep model input state}[x = result] * Φ (budget - sourceCost input) result.2 +
                (∑' result, Pr{let x ← costStep model input state}[x = result]) * c := by
              rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
              refine tsum_congr fun result => ?_
              ring
          _ ≤ ∑' result, Pr{let x ← costStep model input state}[x = result] * Φ (budget - sourceCost input) result.2 +
                1 * c := add_le_add le_rfl (mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl)
          _ ≤ _ := by
              rw [one_mul, hc, ← add_assoc]
              exact hstep input budget state hstate hcost hin
      · rw [OracleComp.tsum_prEvent_pure_mul]
        simpa [digestCount, fleafCount] using hfinal budget state hstate

end FORS.Security.HiddenDebt

namespace FORS.Security.PotentialA

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost HiddenReveal EncodingCode

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

section Sample

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
  (known : Knowledge Coordinate) (ρ : ℝ)

/-- **Linear potential on the small-budget route, honest reads of the route's class from a
prepared state.** `SmallHonest` is asked only of the honest reads a run
from the prepared cache reaches (`HonestWithFrom`), which an honest search past its found counter
satisfies. -/
theorem smallRoute_potentialHFrom {H : Type} [HonestInputs H HashInput]
    (hknown : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed)))
    (tg : Targeting HashInput HashOutput Coordinate) (hdigest : tg.digest = ForsSigner.IsMsgInput)
    (total : ℕ) (hN : Numeric ρ ((total : ℝ) / 2 ^ 128))
    {α : Type} (comp : OracleComp (SourceCostSpec HashInput HashOutput Coordinate H) α)
    (hhonest : HonestWithFrom prepared.2 (SmallHonest parameterOutput highs prepared) comp) :
    ∑' out, Pr{let x ← (interp tg prepared.2 (sampleModel parameterOutput highs) comp total
        (DebtState.start prepared.2 known))}[x = out] *
      (endValue (payoffA parameterOutput fixed highs remaining prepared known ρ) out.2 +
        ENNReal.ofReal (ρ / 2 ^ 128) * digestCount tg out.1.2.2.1 +
        ENNReal.ofReal ((ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128) *
          fleafCount (IsFleafIn (truncateHash parameterOutput)) out.1.2.2.1) ≤
      ENNReal.ofReal (ρ * total / 2 ^ 128) := by
  set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hK
  have hMp : (sampleModel parameterOutput highs).parse = HiddenGraph.parse K.p (candidateActive K.p) :=
    sampleModel_parse parameterOutput highs
  have hMi := sampleModel_incoming parameterOutput highs
  have hMo := sampleModel_outgoing parameterOutput highs
  have h := interp_potential2 tg prepared.2 (sampleModel parameterOutput highs)
    (SmallHonest parameterOutput highs prepared) (fun _ hx => hx.1) (IsFleafIn K.p) K.Inv
    (fun _ hs => hs.prepared)
    (K.potCap total) K.payoff (ENNReal.ofReal (K.ρ / 2 ^ 128))
    (ENNReal.ofReal ((K.ρ - 1 - (total : ℝ) / 2 ^ 128) / 2 ^ 128))
    (fun budget state _ => K.endValue_le_cap total budget state)
    (fun input budget state hinv hcost hgood => K.stepFH (sampleModel parameterOutput highs) hMp hMi hMo tg
      hdigest hN (ctxA_sec parameterOutput fixed highs remaining prepared known ρ)
      (ctxA_msg parameterOutput fixed highs remaining prepared known ρ) input budget state hinv hcost hgood)
    (fun input state hinv hgood => K.inv_stepH (sampleModel parameterOutput highs) hMp hMi input state hinv
      fun honest he => (hgood honest he).1)
    comp hhonest total (DebtState.start prepared.2 known)
    (inv_start parameterOutput fixed highs remaining prepared known ρ hknown)
  refine h.trans (le_of_eq ?_)
  unfold Ctx.potCap
  rw [ite_eq_left le_rfl]
  exact pot_start K known (show (0 : ℝ) ≤ ρ by linarith [hN.low]) total

end Sample

end FORS.Security.PotentialA
