import FORS.LazyRun.ExposedUniform
import FORS.SmallBudget.Linear.ForsSteps
import FORS.ScanSigner.Scan

/-! Facts about interpreted runs used by the FORS contact potential: recorded guesses come from
cached parsed queries; a run that never queries a row writing a coordinate exposes it only by a
reveal; and the signing loop queries no FORS leaf input. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView ForsSigner HiddenBridge

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-! ### One ordinary step -/

section Step

variable {A : Type} {model : HiddenRows.Model HashInput HashOutput A Coordinate}

/-- The support of one ordinary step: an outside read, a recorded guess, or an exposure of the
written coordinate of a canonical row query. -/
theorem ordinaryStep_shape (bytes : HashInput) (s : State) (r : HashOutput × State)
    (hr : r ∈ support (ordinaryStep model bytes s.known s)) :
    ((∀ a v, model.parse bytes = some (a, v) → s.known (model.incoming a) ≠ none) ∧
      (r.2 = s ∨ (s.cache bytes = none ∧ r.2 = s.store bytes r.1))) ∨
    (∃ a v, model.parse bytes = some (a, v) ∧ s.known (model.incoming a) = none ∧
      ((s.cache bytes ≠ none ∧ r.2 = s.record (model.incoming a, v)) ∨
        (s.cache bytes = none ∧ r.2 = (s.record (model.incoming a, v)).store bytes r.1))) ∨
    (∃ a v val, model.parse bytes = some (a, v) ∧ r.2 = s.expose (model.outgoing a) val) := by
  cases hp : model.parse bytes with
  | none =>
      simp only [ordinaryStep, hp] at hr
      left
      exact ⟨fun a v h => (by cases h), readOutside_support bytes s r hr⟩
  | some query =>
      obtain ⟨a, v⟩ := query
      cases hk : s.known (model.incoming a) with
      | none =>
          simp only [ordinaryStep, hp, hk] at hr
          right; left
          refine ⟨a, v, rfl, hk, ?_⟩
          cases hc : s.cache bytes with
          | some out =>
              have hc' : (s.record (model.incoming a, v)).cache bytes = some out := hc
              rw [readOutside_cached bytes _ out hc', support_pure, Set.mem_singleton_iff] at hr
              left
              exact ⟨by simp, by rw [hr]⟩
          | none =>
              have hc' : (s.record (model.incoming a, v)).cache bytes = none := hc
              rw [readOutside_fresh bytes _ hc', support_map] at hr
              obtain ⟨u, _, rfl⟩ := hr
              right
              exact ⟨rfl, rfl⟩
      | some canonical =>
          by_cases heq : v = canonical
          · simp only [ordinaryStep, hp, hk, if_pos heq] at hr
            right; right
            rw [support_map] at hr
            obtain ⟨res, hres, rfl⟩ := hr
            exact ⟨a, v, _, rfl, sampleCoordinate_expose _ s res hres⟩
          · simp only [ordinaryStep, hp, hk, if_neg heq] at hr
            left
            refine ⟨fun a' v' h => ?_, readOutside_support bytes s r hr⟩
            cases h
            rw [hk]
            exact Option.some_ne_none _

theorem cache_ne_of_extends {s s' : State} (hext : Extends s s') {x : HashInput} (h : s.cache x ≠ none) :
    s'.cache x ≠ none := by
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 h
  rw [hext.1 x u hu]
  exact Option.some_ne_none _

theorem known_expose_ne (s : State) {c y : Coordinate} (val : Digest) (hy : y ≠ c) :
    (s.expose c val).known y = s.known y := by
  simp only [DebtState.expose]
  convert QueryCache.cacheQuery_of_ne (cache := s.known) val hy

end Step

/-! ### Recorded guesses come from cached parsed queries -/

section Guess

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- Every recorded guess is the read coordinate and payload of a cached parsed query. -/
def GuessCached (s : State) : Prop :=
  ∀ g ∈ s.guesses, ∃ x a v, model.parse x = some (a, v) ∧ g = (model.incoming a, v) ∧ s.cache x ≠ none

theorem guessCached_start (known : HiddenReveal.Knowledge Coordinate) :
    GuessCached model (DebtState.start initial known) := by
  intro g hg
  cases hg

theorem guessCached_ordinary (bytes : HashInput) (s : State) (h : GuessCached model s) :
    ∀ r ∈ support (ordinaryStep model bytes s.known s), GuessCached model r.2 := by
  intro r hr g hg
  have hext := ordinaryStep_extends model bytes s r hr
  have hold : g ∈ s.guesses → ∃ x a v, model.parse x = some (a, v) ∧ g = (model.incoming a, v) ∧
      r.2.cache x ≠ none := fun hg => by
    obtain ⟨x, a, v, hp, hgq, hc⟩ := h g hg
    exact ⟨x, a, v, hp, hgq, cache_ne_of_extends hext hc⟩
  rcases ordinaryStep_shape bytes s r hr with ⟨_, h1 | ⟨_, h1⟩⟩ | ⟨a, v, hp, _, ⟨hc, h1⟩ | ⟨hc, h1⟩⟩ |
      ⟨a, v, val, _, h1⟩
  · rw [h1] at hg
    exact hold hg
  · rw [h1] at hg
    exact hold hg
  · rw [h1] at hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact ⟨bytes, a, v, hp, rfl, by rw [h1]; exact hc⟩
    · exact hold hg
  · rw [h1] at hg
    rcases List.mem_cons.1 hg with rfl | hg
    · refine ⟨bytes, a, v, hp, rfl, ?_⟩
      rw [h1]
      simp [DebtState.store, QueryCache.cacheQuery_self]
    · exact hold hg
  · rw [h1] at hg
    exact hold hg

theorem guessCached_costStep (input : (SourceCostSpec HashInput HashOutput Coordinate).Domain) (s : State)
    (h : GuessCached model s) : ∀ r ∈ support (costStep model input s), GuessCached model r.2 := by
  intro r hr
  rcases input with (draw | (bytes | coordinate)) | amount
  · change r ∈ support ((fun v => (v, s)) <$> (liftM (unifSpec.query draw) : ProbComp _)) at hr
    rw [support_map] at hr
    obtain ⟨v, _, rfl⟩ := hr
    exact h
  · rw [costStep_ordinary] at hr
    exact guessCached_ordinary model bytes s h r hr
  · change r ∈ support (sampleCoordinate coordinate s) at hr
    rw [sampleCoordinate_expose _ s r hr]
    exact h
  · change r ∈ support (pure ((), s) : ProbComp _) at hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact h

/-- **Guesses stay backed by cached queries** along any run. -/
theorem interp_guessCached {α : Type} (computation : OracleComp CostSpec α) :
    ∀ budget (s : State), GuessCached model s →
      ∀ out ∈ support (interp tg initial model computation budget s), GuessCached model out.2 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget s h out hout
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact h
  | query_bind input next ih =>
      intro budget s h out hout
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, hresult, inner, hinner, rfl⟩ := hout
        exact ih result.1 _ result.2 (guessCached_costStep model input s h result hresult) inner hinner
      · rw [support_pure, Set.mem_singleton_iff] at hout
        subst hout
        exact h

end Guess

/-! ### Exposures by reveals only -/

section Known

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The inputs whose canonical continuation writes a coordinate. -/
def Writes (c : Coordinate) (x : HashInput) : Prop := ∃ a v, model.parse x = some (a, v) ∧ model.outgoing a = c

theorem costStep_known_new (input : (SourceCostSpec HashInput HashOutput Coordinate).Domain) (s : State)
    (c : Coordinate) (hin : ∀ bytes, input = .inl (.inr (.inl bytes)) → ¬Writes model c bytes) :
    ∀ r ∈ support (costStep model input s), r.2.known c ≠ none →
      s.known c ≠ none ∨ c ∈ HiddenBridge.revealed input := by
  intro r hr hk
  rcases input with (draw | (bytes | coordinate)) | amount
  · change r ∈ support ((fun v => (v, s)) <$> (liftM (unifSpec.query draw) : ProbComp _)) at hr
    rw [support_map] at hr
    obtain ⟨v, _, rfl⟩ := hr
    exact Or.inl hk
  · rw [costStep_ordinary] at hr
    left
    rcases ordinaryStep_shape bytes s r hr with ⟨_, h1 | ⟨_, h1⟩⟩ | ⟨a, v, hp, _, ⟨hc, h1⟩ | ⟨hc, h1⟩⟩ |
        ⟨a, v, val, hp, h1⟩
    · rwa [h1] at hk
    · rwa [h1] at hk
    · rwa [h1] at hk
    · rwa [h1] at hk
    · rw [h1] at hk
      have hne : c ≠ model.outgoing a := fun h => hin bytes rfl ⟨a, v, hp, h.symm⟩
      rwa [known_expose_ne s val hne] at hk
  · change r ∈ support (sampleCoordinate coordinate s) at hr
    rw [sampleCoordinate_expose _ s r hr] at hk
    by_cases hcc : c = coordinate
    · right
      subst hcc
      exact List.mem_singleton_self _
    · left
      rwa [known_expose_ne s _ hcc] at hk
  · change r ∈ support (pure ((), s) : ProbComp _) at hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact Or.inl hk

/-- **A run that never asks a row writing `c` exposes `c` only by revealing it.** -/
theorem interp_known_new {α : Type} (computation : OracleComp CostSpec α) (c : Coordinate)
    (h : Avoids (Writes model c) computation) :
    ∀ budget (s : State), ∀ out ∈ support (interp tg initial model computation budget s),
      out.2.known c ≠ none → s.known c ≠ none ∨ c ∈ out.1.2.1 := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget s out hout hk
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact Or.inl hk
  | query_bind input next ih =>
      intro budget s out hout hk
      obtain ⟨hin, hnext⟩ := (avoids_query_bind (Writes model c) input next).1 h
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, hresult, inner, hinner, rfl⟩ := hout
        change inner.2.known c ≠ none at hk
        change s.known c ≠ none ∨ c ∈ HiddenBridge.revealed input ++ inner.1.2.1
        rcases ih result.1 (hnext result.1) _ result.2 inner hinner hk with h1 | h1
        · rcases costStep_known_new model input s c hin result hresult h1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr (List.mem_append_left _ h2)
        · exact Or.inr (List.mem_append_right _ h1)
      · rw [support_pure, Set.mem_singleton_iff] at hout
        subst hout
        exact Or.inl hk

end Known

/-- A FORS coordinate: the secret or the value of a FORS leaf. -/
def IsFc (x : Coordinate) : Prop := ∃ index κ leaf q, x = Coordinate.fors index κ leaf q

/-! ### The signer queries no FORS leaf input -/

section Avoid

theorem avoids_finishRest_fleaf (p : PublicParameter) (parameter : PublicParameter) (data : PublicData)
    (message : Message) (randomness : Randomness) (digest : MessageDigest) :
    Avoids (D := HashInput) (R := HashOutput) (ι := Coordinate) (IsFleafIn p)
      (finishRest parameter data message randomness digest) := by
  unfold finishRest
  refine avoids_bind _ (avoids_tick _ _) fun _ => ?_
  refine avoids_bind _ (avoids_sequenceDep _ fun lay => ?_) fun found => ?_
  · unfold layerCostSearch layerSearch
    refine avoids_bind _ (avoids_tick _ _) fun _ => ?_
    refine avoids_bind _ (avoids_liftHash _ _ (noQ_search _ _ _ _ _ (fun payload => ?_) _ _)) fun found => ?_
    · rintro ⟨f, hf⟩
      have hd := (PotentialA.domain_eq_of_input hf trivial trivial).1
      cases hd
    rcases found with _ | pair
    · exact avoids_pure _ _
    · exact avoids_bind _ (avoids_tick _ _) fun _ => avoids_pure _ _
  rcases found with _ | found
  · exact avoids_pure _ _
  · refine avoids_bind _ (avoids_sequenceFin _ _ fun _ => avoids_sequenceFin _ _ fun _ => avoids_reveal _ _)
      fun _ => ?_
    refine avoids_bind _ (avoids_sequenceFin _ _ fun _ => avoids_treeCostSource _ _ _ _ _) fun _ => ?_
    exact avoids_pure _ _

/-- **The signing loop queries no FORS leaf input.** -/
theorem avoids_loop_fleaf (p : PublicParameter) (parameter : PublicParameter) (data : PublicData)
    (message : Message) : ∀ attempts ρ, Avoids (D := HashInput) (R := HashOutput) (ι := Coordinate) (IsFleafIn p)
      (signCostSourceLoop parameter data message (data.step message) attempts ρ) := by
  intro attempts
  induction attempts with
  | zero => intro ρ; exact avoids_pure _ _
  | succ attempts ih =>
      intro ρ
      rw [signCostSourceLoop_succ]
      refine (avoids_query_bind _ _ _).2 ⟨fun bytes hb hx => ?_, fun first => ?_⟩
      · cases hb
        obtain ⟨f, hf⟩ := hx
        exact PotentialA.msg_ne_fleaf (msgInput_digestInput parameter data.root message ρ firstCall) hf
      · split_ifs
        · rw [finishCostSource_eq]
          refine avoids_bind _ (avoids_sequenceFin _ _ fun call => avoids_read _ _ fun hx => ?_)
            fun outputs => avoids_finishRest_fleaf p parameter data message ρ _
          obtain ⟨f, hf⟩ := hx
          exact PotentialA.msg_ne_fleaf (msgInput_digestInput parameter data.root message ρ call) hf
        · exact ih _

end Avoid

end FORS.Security.ForsPotential
