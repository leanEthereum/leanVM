import Sphincs.BridgePotentialA6

/-! **The linear potential on the small-budget route: the sample's setting.** The targeting,
context and payoff of the linear potential for the sample's comparison, started from the prepared
cache and the above-word exposure, and the start: the invariant holds and the potential with total
budget `q` is `ρ q / 2^128`. The payoff counts a hit of the first-order targeting (a correct guess,
a decided first-order hit, or a debt completed by the remaining table), the WOTS events and the forest contact events against
the completed table. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.PotentialA

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost HiddenReveal EncodingCode

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-- Exposing a list of coordinates keeps the known ones and exposes every listed one. -/
theorem exposeR_known : ∀ (cs : List Coordinate) (known k : Knowledge Coordinate),
    k ∈ support (exposeR cs known) →
      (∀ c v, known c = some v → k c = some v) ∧ ∀ c ∈ cs, k c ≠ none
  | [], known, k, hk => by
      rw [exposeR, support_pure, Set.mem_singleton_iff] at hk
      subst hk
      exact ⟨fun _ _ h => h, fun _ h => absurd h List.not_mem_nil⟩
  | c :: cs, known, k, hk => by
      rw [exposeR, mem_support_bind_iff] at hk
      obtain ⟨r, hr, hk⟩ := hk
      obtain ⟨ih1, ih2⟩ := exposeR_known cs r.2 k hk
      cases hc : known c with
      | some v₀ =>
          have hr' := randomOracle_run_some known c v₀ hc r hr
          subst hr'
          refine ⟨ih1, fun c' hc' => ?_⟩
          rcases List.mem_cons.1 hc' with rfl | hc'
          · rw [ih1 _ v₀ hc]
            simp
          · exact ih2 c' hc'
      | none =>
          have hr' := randomOracle_run_none known c hc r hr
          have hself : r.2 c = some r.1 := by
            rw [HiddenDebt.randomOracle_known_support known c r hr]
            simp
          refine ⟨fun c' v h => ih1 c' v ?_, fun c' hc' => ?_⟩
          · have hne : c' ≠ c := by
              rintro rfl
              rw [hc] at h
              cases h
            rw [hr' c' hne]
            exact h
          · rcases List.mem_cons.1 hc' with rfl | hc'
            · rw [ih1 _ _ hself]
              simp
            · exact ih2 c' hc'

variable [Params]

/-- The first-order targeting of the small-budget route: the sample's targets, removed at
second-order inputs. -/
noncomputable def targetingA (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (results : Index → Option (Counter × Encoding)) :
    Targeting HashInput HashOutput Coordinate where
  trunc := truncateHash
  kind x := if SecondOrderInput (truncateHash parameterOutput) results x then .none
    else sampleKind parameterOutput fixed highs remaining results x
  digest := ForestSigner.IsMsgInput

/-- The data of the potential for one sample, preparation and exposure. -/
noncomputable def ctxA (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (known : Knowledge Coordinate) (ρ : ℝ) : Ctx where
  p := truncateHash parameterOutput
  R := prepared.1
  initial := prepared.2
  F c := (known c).getD 0
  tg := targetingA parameterOutput fixed highs remaining prepared.1
  ρ := ρ
  trunc_eq := rfl

/-- The payoff of the small-budget route. -/
noncomputable def payoffA (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (known : Knowledge Coordinate) (ρ : ℝ) : (Coordinate → Digest) → St → ℝ≥0∞ :=
  (ctxA parameterOutput fixed highs remaining prepared known ρ).payoff

section Sample

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
  (known : Knowledge Coordinate) (ρ : ℝ)

theorem ctxA_sec : ∀ x, SecondOrderInput (ctxA parameterOutput fixed highs remaining prepared known ρ).p
    (ctxA parameterOutput fixed highs remaining prepared known ρ).R x →
    (ctxA parameterOutput fixed highs remaining prepared known ρ).tg.kind x = .none := by
  intro x hx
  exact ite_eq_left hx

theorem ctxA_msg : ∀ x, ForestSigner.IsMsgInput x →
    (ctxA parameterOutput fixed highs remaining prepared known ρ).tg.kind x = .none := by
  intro x hx
  change (if SecondOrderInput (truncateHash parameterOutput) prepared.1 x then _ else _) = _
  split_ifs
  · rfl
  · exact sampleTargeting_msg parameterOutput fixed highs remaining prepared.1 x hx

theorem fr_start (K : Ctx) (known' : Knowledge Coordinate) (x : HashInput) (u : HashOutput) :
    ¬K.Fr (DebtState.start K.initial known') x u := by
  rintro ⟨h1, h2⟩
  change K.initial x = some u at h1
  rw [h1] at h2
  cases h2

theorem inv_start (hknown : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed))) :
    (ctxA parameterOutput fixed highs remaining prepared known ρ).Inv (DebtState.start prepared.2 known) where
  prepared := fun _ _ h => h
  anchored c hc := by
    obtain ⟨hbase, hlist⟩ := exposeR_known _ _ _ hknown
    have hne : known c ≠ none := by
      rcases hc with ha | ⟨index, cc, sp, j, a, i, rfl⟩
      · exact hlist c (mem_aboveList.2 ha)
      · have : knownOf (truncateHash parameterOutput) fixed (.fchain index cc sp j a i ⟨chainTop, by omega⟩) =
            some (masked (truncateHash parameterOutput) fixed (.fchain index cc sp j a i ⟨chainTop, by omega⟩)) := by
          simp [knownOf, KnownCoordinate]
        rw [hbase _ _ this]
        simp
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hne
    change known c = some ((known c).getD 0)
    rw [hv]
    rfl
  guessed x u q hfr := absurd hfr (fr_start _ known x u)

end Sample

/-- The potential at the start: the plain rate of the whole budget. -/
theorem pot_start (K : Ctx) (known : Knowledge Coordinate) (_hρ : 0 ≤ K.ρ) (total : ℕ) :
    K.pot total (DebtState.start K.initial known) = ENNReal.ofReal (K.ρ * total / 2 ^ 128) := by
  have hfr : ∀ x u, ¬K.Fr (DebtState.start K.initial known) x u := fun x u => fr_start K known x u
  have hCB : ∀ l i, K.ContactB (DebtState.start K.initial known) l i = ∅ := fun l i => by
    ext v
    simp only [Ctx.ContactB, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨x, u, -, h, -⟩
    exact hfr x u h
  have hMk : ∀ l i, ¬K.Marker (DebtState.start K.initial known) l i := fun l i ⟨_, _, u, h, _⟩ => hfr _ u h
  have hcw : ∀ f, K.cw (DebtState.start K.initial known) f = 0 := fun f =>
    K.cw_of_not_fe fun ⟨u, h⟩ => hfr _ u h
  have hBL : ∀ l, ¬K.BadLeaf (DebtState.start K.initial known) l := by
    intro l
    rintro (⟨i, hne⟩ | ⟨i, -, hm⟩ | ⟨i, -, -, hne, -⟩)
    · rw [hCB] at hne
      simp at hne
    · exact hMk l i hm
    · rw [hCB] at hne
      simp at hne
  have hdone : K.done (DebtState.start K.initial known) = 0 := by
    unfold Ctx.done
    rw [ite_eq_right]
    rintro (hr | ⟨l, -, hb⟩)
    · rcases hr with ⟨input, output, value, hcache, hinitial, -⟩ | ⟨c, v, -, hv⟩
      · change K.initial input = some output at hcache
        rw [hcache] at hinitial
        cases hinitial
      · rw [debts_start] at hv
        exact hv
    · exact hBL l hb
  have hpend : K.pend (DebtState.start K.initial known) = 0 := by
    unfold Ctx.pend
    refine Finset.sum_eq_zero fun c _ => ?_
    split_ifs
    · rw [debts_start]
      simp
    · rfl
  have hUA : K.UAset (DebtState.start K.initial known) = ∅ := by
    ext x
    simp only [Ctx.UAset, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨l, i, u, -, -, h, -⟩
    exact hfr x u h
  have hrate : K.rate (DebtState.start K.initial known) = ENNReal.ofReal K.ρ := by
    have hA : ¬K.Armed (DebtState.start K.initial known) := by
      rintro ⟨l, -, -, ⟨i, hm⟩ | ⟨i, hne⟩⟩
      · exact hMk l i hm
      · rw [hCB] at hne
        simp at hne
    have hC : K.contactCount (DebtState.start K.initial known) = 0 := by
      unfold Ctx.contactCount Ctx.leafCount
      refine Finset.sum_eq_zero fun l _ => ?_
      split_ifs
      · rfl
      · simp [hCB]
      · rfl
    have hKF : K.kf (DebtState.start K.initial known) = 0 := by
      unfold Ctx.kf
      simp [hcw]
    unfold Ctx.rate Ctx.vrate
    rw [ite_eq_right hA, hC, hKF, mul_zero, add_zero, add_zero]
  have hlat : K.latent (DebtState.start K.initial known) = 0 := by
    unfold Ctx.latent Ctx.ng Ctx.pp
    simp [hcw]
  have hmain : K.pot total (DebtState.start K.initial known) = (total : ℝ≥0∞) * ν * ENNReal.ofReal K.ρ := by
    unfold Ctx.pot
    rw [hdone, hpend, hlat, hUA, hrate, Set.encard_empty, ENat.toENNReal_zero, mul_zero, add_zero, zero_add, zero_add,
      zero_add]
  rw [hmain, budget_ofReal, ← ENNReal.ofReal_mul (by positivity),
    show (total : ℝ) / 2 ^ 128 * K.ρ = K.ρ * total / 2 ^ 128 by ring]

end Sphincs.Security.PotentialA
