import Sphincs.BridgeExposeMean
import Sphincs.BridgeFleafA3
import Sphincs.BridgeScan

/-! Facts about interpreted runs used by the forest contact potential: recorded guesses come from
cached parsed queries; a run that never queries a row writing a coordinate exposes it only by a
reveal; a completed signing call reveals, with every forest chain value, all values above it on its
chain; and the signing loop queries no forest step input. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open SphincsFors.Security
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView ForestSigner HiddenBridge

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### One ordinary step -/

section Step

variable {A : Type} {model : HiddenRows.Model HashInput HashOutput A Coordinate}

omit [Params] in
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

omit [Params] in
theorem cache_ne_of_extends {s s' : State} (hext : Extends s s') {x : HashInput} (h : s.cache x ≠ none) :
    s'.cache x ≠ none := by
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 h
  rw [hext.1 x u hu]
  exact Option.some_ne_none _

omit [Params] in
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

omit [Params] in
theorem guessCached_start (known : HiddenReveal.Knowledge Coordinate) :
    GuessCached model (DebtState.start initial known) := by
  intro g hg
  cases hg

omit [Params] in
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

omit [Params] in
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

omit [Params] in
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

omit [Params] in
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

omit [Params] in
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

/-! ### Completed runs reveal upward-closed chains -/

section Closed

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A reveal list holding, with every forest chain value, all values above it on its chain. -/
def UpClosed (L : List Coordinate) : Prop :=
  ∀ index c sp j a i (q k : FPos), Coordinate.fchain index c sp j a i q ∈ L → q.val ≤ k.val →
    Coordinate.fchain index c sp j a i k ∈ L

/-- Completed runs reveal upward-closed lists. -/
def ClosedRuns {α : Type} (computation : OracleComp CostSpec α) : Prop :=
  ∀ budget (s : State), ∀ out ∈ support (interp tg initial model computation budget s),
    out.1.1.isSome → UpClosed out.1.2.1

/-- Completed runs reveal `x`. -/
def MustReveal (x : Coordinate) {α : Type} (computation : OracleComp CostSpec α) : Prop :=
  ∀ budget (s : State), ∀ out ∈ support (interp tg initial model computation budget s),
    out.1.1.isSome → x ∈ out.1.2.1

/-- A forest chain coordinate. -/
def IsFc (x : Coordinate) : Prop := ∃ index c sp j a i q, x = Coordinate.fchain index c sp j a i q

omit [Params] in
theorem upClosed_append {L1 L2 : List Coordinate} (h1 : UpClosed L1) (h2 : UpClosed L2) : UpClosed (L1 ++ L2) := by
  intro index c sp j a i q k hq hk
  rcases List.mem_append.1 hq with h | h
  · exact List.mem_append_left _ (h1 _ _ _ _ _ _ _ _ h hk)
  · exact List.mem_append_right _ (h2 _ _ _ _ _ _ _ _ h hk)

omit [Params] in
theorem upClosed_of_noFc {L : List Coordinate} (h : ∀ x ∈ L, ¬IsFc x) : UpClosed L :=
  fun index c sp j a i q _ hq _ => absurd ⟨_, _, _, _, _, _, _, rfl⟩ (h _ hq)

omit [Params] in
theorem closedRuns_of_revealsIn {α : Type} {computation : OracleComp CostSpec α}
    (h : RevealsIn (fun x => ¬IsFc x) computation) : ClosedRuns tg initial model computation :=
  fun budget s out hout _ => upClosed_of_noFc (interp_reveals tg initial model computation h budget s out hout)

omit [Params] in
theorem closedRuns_pure {α : Type} (value : α) : ClosedRuns tg initial model (pure value : OracleComp CostSpec α) :=
  closedRuns_of_revealsIn tg initial model (revealsIn_pure _ value)

omit [Params] in
theorem closedRuns_bind {α β : Type} {first : OracleComp CostSpec α} {next : α → OracleComp CostSpec β}
    (h1 : ClosedRuns tg initial model first) (h2 : ∀ v, ClosedRuns tg initial model (next v)) :
    ClosedRuns tg initial model (first >>= next) := by
  intro budget s out hout hsome
  obtain ⟨o1, ho1, hcase⟩ := interp_bind_mem tg initial model first next budget s out hout
  rcases hcase with ⟨_, hnone, _, _⟩ | ⟨v, hv, o2, ho2, hres, hrev, _⟩
  · rw [hnone] at hsome
    cases hsome
  · rw [hrev]
    exact upClosed_append (h1 budget s o1 ho1 (by rw [hv]; rfl)) (h2 v _ _ o2 ho2 (by rw [← hres]; exact hsome))

omit [Params] in
theorem mustReveal_bind_left {x : Coordinate} {α β : Type} {first : OracleComp CostSpec α}
    {next : α → OracleComp CostSpec β} (h : MustReveal tg initial model x first) :
    MustReveal tg initial model x (first >>= next) := by
  intro budget s out hout hsome
  obtain ⟨o1, ho1, hcase⟩ := interp_bind_mem tg initial model first next budget s out hout
  rcases hcase with ⟨_, hnone, _, _⟩ | ⟨v, hv, o2, ho2, hres, hrev, _⟩
  · rw [hnone] at hsome
    cases hsome
  · rw [hrev]
    exact List.mem_append_left _ (h budget s o1 ho1 (by rw [hv]; rfl))

omit [Params] in
theorem mustReveal_bind_right {x : Coordinate} {α β : Type} {first : OracleComp CostSpec α}
    {next : α → OracleComp CostSpec β} (h : ∀ v, MustReveal tg initial model x (next v)) :
    MustReveal tg initial model x (first >>= next) := by
  intro budget s out hout hsome
  obtain ⟨o1, ho1, hcase⟩ := interp_bind_mem tg initial model first next budget s out hout
  rcases hcase with ⟨_, hnone, _, _⟩ | ⟨v, hv, o2, ho2, hres, hrev, _⟩
  · rw [hnone] at hsome
    cases hsome
  · rw [hrev]
    exact List.mem_append_right _ (h v _ _ o2 ho2 (by rw [← hres]; exact hsome))

omit [Params] in
theorem mustReveal_reveal (x : Coordinate) :
    MustReveal tg initial model x (HiddenCost.reveal (D := HashInput) (R := HashOutput) x) := by
  intro budget s out hout hsome
  unfold HiddenCost.reveal at hout
  rw [← bind_pure (liftM ((SourceCostSpec HashInput HashOutput Coordinate).query (.inl (.inr (.inr x))))),
    interp_query_bind] at hout
  split_ifs at hout with hcost
  · rw [support_bind] at hout
    simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
    obtain ⟨result, _, inner, _, rfl⟩ := hout
    exact List.mem_append_left _ (List.mem_singleton_self x)
  · rw [support_pure, Set.mem_singleton_iff] at hout
    subst hout
    cases hsome

omit [Params] in
theorem mustReveal_sequenceFin {x : Coordinate} {α : Type} :
    ∀ {n : ℕ} (g : Fin n → OracleComp CostSpec α) (k : Fin n), MustReveal tg initial model x (g k) →
      MustReveal tg initial model x (Concrete.sequenceFin g)
  | 0, _, k, _ => k.elim0
  | n + 1, g, k, h => by
      unfold Concrete.sequenceFin
      cases k using Fin.cases with
      | zero => exact mustReveal_bind_left tg initial model h
      | succ k' =>
          exact mustReveal_bind_right tg initial model fun _ => mustReveal_bind_left tg initial model
            (mustReveal_sequenceFin (fun i : Fin n => g i.succ) k' h)

omit [Params] in
theorem closedRuns_sequenceFin {α : Type} :
    ∀ {n : ℕ} (g : Fin n → OracleComp CostSpec α), (∀ k, ClosedRuns tg initial model (g k)) →
      ClosedRuns tg initial model (Concrete.sequenceFin g)
  | 0, _, _ => closedRuns_pure tg initial model _
  | n + 1, g, h => by
      unfold Concrete.sequenceFin
      exact closedRuns_bind tg initial model (h 0) fun _ => closedRuns_bind tg initial model
        (closedRuns_sequenceFin (fun i : Fin n => g i.succ) fun i => h i.succ) fun _ => closedRuns_pure tg initial model _

omit [Params] in
/-- **One opened chain is revealed up to its top.** -/
theorem closedRuns_revealChainCost (index : Index) (c : Coord) (mark : CoordMark) (j : SubIdx) (i : FChain) :
    ClosedRuns tg initial model (revealChainCost index c mark j i) := by
  intro budget s out hout hsome
  have hin : RevealsIn (fun x => ∃ k : FPos, (openedPos mark j i).val ≤ k.val ∧
      x = .fchain index c mark.super j (mark.child j) i k) (revealChainCost index c mark j i) := by
    unfold revealChainCost
    refine revealsIn_sequenceFin _ _ fun k => ?_
    split
    · rename_i hk
      exact revealsIn_reveal _ _ ⟨k, hk, rfl⟩
    · exact revealsIn_pure _ _
  have hall := interp_reveals tg initial model _ hin budget s out hout
  intro index' c' sp' j' a' i' q k hq hqk
  obtain ⟨k0, hk0, he⟩ := hall _ hq
  simp only [Coordinate.fchain.injEq] at he
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := he
  rw [h1, h2, h3, h4, h5, h6]
  have hk : (openedPos mark j i).val ≤ k.val := le_trans hk0 (h7 ▸ hqk)
  have hmust : MustReveal tg initial model (.fchain index c mark.super j (mark.child j) i k)
      (revealChainCost index c mark j i) := by
    unfold revealChainCost
    refine mustReveal_sequenceFin tg initial model _ k ?_
    rw [if_pos hk]
    exact mustReveal_reveal tg initial model _
  exact hmust budget s out hout hsome

omit [Params] in
theorem closedRuns_coordCostSource (data : PublicData) (index : Index) (c : Coord) (mark : CoordMark) :
    ClosedRuns tg initial model (coordCostSource data index c mark) := by
  unfold coordCostSource
  refine closedRuns_bind tg initial model (closedRuns_sequenceFin tg initial model _ fun j => ?_) fun _ =>
    closedRuns_pure tg initial model _
  exact closedRuns_bind tg initial model (closedRuns_sequenceFin tg initial model _ fun i =>
    closedRuns_revealChainCost tg initial model index c mark j i) fun _ => closedRuns_pure tg initial model _

omit [Params] in
theorem not_isFc_chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (st : Digit) :
    ¬IsFc (Coordinate.chain lay tree leaf chain st) := by
  rintro ⟨_, _, _, _, _, _, _, h⟩
  cases h

theorem closedRuns_finishRest (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) (digest : MessageDigest) :
    ClosedRuns tg initial model (finishRest parameter data message randomness digest) := by
  unfold finishRest
  refine closedRuns_bind tg initial model (closedRuns_of_revealsIn tg initial model (revealsIn_tick _ _)) fun _ => ?_
  refine closedRuns_bind tg initial model (closedRuns_of_revealsIn tg initial model (revealsIn_liftHash _ _))
    fun found => ?_
  rcases found with _ | ⟨counter, word⟩
  · exact closedRuns_pure tg initial model _
  · refine closedRuns_bind tg initial model (closedRuns_of_revealsIn tg initial model
      (revealsIn_sequenceFin _ _ fun chain => revealsIn_reveal _ _ (not_isFc_chain _ _ _ _ _))) fun _ => ?_
    refine closedRuns_bind tg initial model (closedRuns_sequenceFin tg initial model _ fun c =>
      closedRuns_coordCostSource tg initial model data _ c _) fun _ => ?_
    exact closedRuns_bind tg initial model (closedRuns_of_revealsIn tg initial model (revealsIn_tick _ _)) fun _ =>
      closedRuns_pure tg initial model _

omit [Params] in
theorem revealsIn_liftProb (allowed : Coordinate → Prop) {α : Type} (sample : ProbComp α) :
    RevealsIn allowed (liftM sample : OracleComp CostSpec α) := by
  induction sample using OracleComp.inductionOn with
  | pure value => exact revealsIn_pure allowed value
  | query_bind query rest ih =>
      rw [liftM_bind]
      exact (revealsIn_query_bind allowed (.inl (.inl query)) _).2 ⟨fun c h => (by cases h), ih⟩

omit [Params] in
theorem closedRuns_ordinary_bind (x : HashInput) {β : Type} (next : HashOutput → OracleComp CostSpec β)
    (h : ∀ v, ClosedRuns tg initial model (next v)) :
    ClosedRuns tg initial model (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) := by
  refine closedRuns_bind tg initial model (closedRuns_of_revealsIn tg initial model ?_) h
  rw [← bind_pure (liftM (CostSpec.query (.inl (.inr (.inl x)))))]
  exact (revealsIn_query_bind _ _ _).2 ⟨fun c hc => (by cases hc), fun _ => trivial⟩

/-- **A completed signing call reveals upward-closed chains.** -/
theorem closedRuns_loop (parameter : PublicParameter) (data : PublicData) (message : Message) :
    ∀ attempts ρ, ClosedRuns tg initial model (signCostSourceLoop parameter data message attempts ρ) := by
  intro attempts
  induction attempts with
  | zero => intro ρ; exact closedRuns_pure tg initial model _
  | succ attempts ih =>
      intro ρ
      rw [signCostSourceLoop_succ]
      refine closedRuns_ordinary_bind tg initial model _ _ fun first => ?_
      split_ifs
      · rw [finishCostSource_eq]
        exact closedRuns_ordinary_bind tg initial model _ _ fun a =>
          closedRuns_finishRest tg initial model parameter data message ρ _
      · exact ih _

end Closed

/-! ### The signer queries no forest step input -/

section Avoid

theorem avoids_finishRest_fchain (p : PublicParameter) (parameter : PublicParameter) (data : PublicData)
    (message : Message) (randomness : Randomness) (digest : MessageDigest) :
    Avoids (D := HashInput) (R := HashOutput) (ι := Coordinate) (IsFchainIn p)
      (finishRest parameter data message randomness digest) := by
  unfold finishRest
  refine avoids_bind _ (avoids_tick _ _) fun _ => ?_
  refine avoids_bind _ (avoids_liftHash _ _ (noQ_search _ _ _ _ _ (fun payload => ?_) _ _)) fun found => ?_
  · rintro ⟨f, hf⟩
    have hd := (PotentialA.domain_eq_of_input hf trivial trivial).1
    cases hd
  rcases found with _ | ⟨counter, word⟩
  · exact avoids_pure _ _
  · refine avoids_bind _ (avoids_sequenceFin _ _ fun _ => avoids_reveal _ _) fun _ => ?_
    refine avoids_bind _ (avoids_sequenceFin _ _ fun _ => avoids_coordCostSource _ _ _ _ _) fun _ => ?_
    exact avoids_bind _ (avoids_tick _ _) fun _ => avoids_pure _ _

/-- **The signing loop queries no forest step input.** -/
theorem avoids_loop_fchain (p : PublicParameter) (parameter : PublicParameter) (data : PublicData)
    (message : Message) : ∀ attempts ρ, Avoids (D := HashInput) (R := HashOutput) (ι := Coordinate) (IsFchainIn p)
      (signCostSourceLoop parameter data message attempts ρ) := by
  intro attempts
  induction attempts with
  | zero => intro ρ; exact avoids_pure _ _
  | succ attempts ih =>
      intro ρ
      rw [signCostSourceLoop_succ]
      refine (avoids_query_bind _ _ _).2 ⟨fun bytes hb hx => ?_, fun first => ?_⟩
      · cases hb
        obtain ⟨f, hf⟩ := hx
        exact PotentialA.msg_ne_fchain (msgInput_digestInput parameter data.root message ρ) hf
      · split_ifs
        · rw [finishCostSource_eq]
          refine (avoids_query_bind _ _ _).2 ⟨fun bytes hb hx => ?_, fun a => ?_⟩
          · cases hb
            obtain ⟨f, hf⟩ := hx
            exact PotentialA.msg_ne_fchain (msgInput_digestInput parameter data.root message ρ) hf
          exact avoids_finishRest_fchain p parameter data message ρ _
        · exact ih _

end Avoid

end Sphincs.Security.ForsPotential
