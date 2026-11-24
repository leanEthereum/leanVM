module

public import FORS.GraphView.HonestGame

@[expose] public section

/-! The honest form of a charged cost program (`toHonest`): its raw hash reads become honest reads,
its ticks disappear, draws and reveals stay. Interpreted, the honest form never stops for budget,
and its result, reveals and final state are distributed as the charged program's at any budget the
charged program cannot exhaust (`interp_toHonest`). So every bound on the charged program's
interpretation that reads only the result and the final state holds for the honest form at any
budget (`tsum_interp_toHonest`, `mem_support_interp_toHonest`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.GraphView

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt

set_option backward.isDefEq.respectTransparency false

/-- The honest form of a charged cost-interface query. -/
noncomputable def toHonest : QueryImpl CostSpec (OracleComp CostSpecH)
  | .inl (.inl draw) => liftM (CostSpecH.query (.inl (.inl draw)))
  | .inl (.inr (.inl bytes)) => honestRead (D := HashInput) (R := HashOutput) (ι := Coordinate) bytes
  | .inl (.inr (.inr coordinate)) => liftM (CostSpecH.query (.inl (.inr (.inr coordinate))))
  | .inr (.inl _) => pure ()
  | .inr (.inr honest) => Empty.elim honest

/-! ### Programs that a budget cannot stop -/

/-- Every path of the program costs at most the budget: it never stops for budget. -/
def CostAtMost {α : Type} (computation : OracleComp CostSpec α) : ℕ → Prop :=
  OracleComp.construct (fun _ _ => True)
    (fun input _ next budget => sourceCost input ≤ budget ∧ ∀ r, next r (budget - sourceCost input))
    computation

theorem costAtMost_query_bind {α : Type} (input : CostSpec.Domain)
    (next : CostSpec.Range input → OracleComp CostSpec α) (budget : ℕ) :
    CostAtMost (liftM (CostSpec.query input) >>= next) budget ↔
      sourceCost input ≤ budget ∧ ∀ r, CostAtMost (next r) (budget - sourceCost input) := Iff.rfl

theorem costAtMost_mono {α : Type} (computation : OracleComp CostSpec α) :
    ∀ {budget budget' : ℕ}, CostAtMost computation budget → budget ≤ budget' →
      CostAtMost computation budget' := by
  induction computation using OracleComp.inductionOn with
  | pure value => intro _ _ _ _; trivial
  | query_bind input next ih =>
      intro budget budget' h hle
      rw [costAtMost_query_bind] at h ⊢
      exact ⟨h.1.trans hle, fun r => ih r (h.2 r) (Nat.sub_le_sub_right hle _)⟩

/-- The answers of every charged query range over a finite type. -/
noncomputable instance rangeFintype : ∀ input : CostSpec.Domain, Fintype (CostSpec.Range input)
  | .inl (.inl draw) => inferInstanceAs (Fintype (Fin (draw + 1)))
  | .inl (.inr (.inl _)) => inferInstanceAs (Fintype HashOutput)
  | .inl (.inr (.inr _)) => inferInstanceAs (Fintype Digest)
  | .inr (.inl _) => inferInstanceAs (Fintype Unit)
  | .inr (.inr honest) => Empty.elim honest

/-- **Every charged program has a budget it cannot exhaust**: its answers range over finite types,
so its paths are finitely many. -/
theorem exists_costAtMost {α : Type} (computation : OracleComp CostSpec α) :
    ∃ budget, CostAtMost computation budget := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact ⟨0, trivial⟩
  | query_bind input next ih =>
      choose bound hbound using ih
      refine ⟨sourceCost input + Finset.univ.sup bound, ?_⟩
      rw [costAtMost_query_bind]
      refine ⟨Nat.le_add_right _ _, fun r => costAtMost_mono _ (hbound r) ?_⟩
      rw [Nat.add_sub_cancel_left]
      exact Finset.le_sup (Finset.mem_univ r)

/-! ### The coupling -/

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The result, the reveals and the final state of a run. -/
def runProj {α : Type} (out : Run HashInput Coordinate α × DebtState HashInput HashOutput Coordinate) :
    (Option α × List Coordinate) × DebtState HashInput HashOutput Coordinate :=
  ((out.1.1, out.1.2.1), out.2)

theorem map_runProj_prefix {α : Type} (rv : List Coordinate) (rc : List (Entry HashInput))
    (tc : List (HashInput × Bool))
    (X : ProbComp (Run HashInput Coordinate α × DebtState HashInput HashOutput Coordinate)) :
    runProj <$> ((fun out : Run HashInput Coordinate α × DebtState HashInput HashOutput Coordinate =>
        ((out.1.1, rv ++ out.1.2.1, rc ++ out.1.2.2.1, tc ++ out.1.2.2.2), out.2)) <$> X) =
      (fun p : (Option α × List Coordinate) × DebtState HashInput HashOutput Coordinate =>
        ((p.1.1, rv ++ p.1.2), p.2)) <$> (runProj <$> X) := by
  simp only [Functor.map_map]
  rfl

theorem interp_toHonest {α : Type} (computation : OracleComp CostSpec α) :
    ∀ budget, CostAtMost computation budget → ∀ honestBudget state,
      runProj <$> interp tg initial model (simulateQ toHonest computation) honestBudget state =
        runProj <$> interp tg initial model computation budget state := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget _ honestBudget state
      rw [simulateQ_pure, interp_pure, interp_pure]
  | query_bind input next ih =>
      intro budget hcost honestBudget state
      rw [costAtMost_query_bind] at hcost
      rw [simulateQ_bind, simulateQ_spec_query, interp_query_bind, ite_eq_left hcost.1, map_bind]
      rcases input with (draw | bytes | coordinate) | (amount | honest)
      · change runProj <$> interp tg initial model (liftM (CostSpecH.query (.inl (.inl draw))) >>= _)
          honestBudget state = _
        rw [interp_query_bind, ite_eq_left (show sourceCost (.inl (.inl draw) : CostSpecH.Domain) ≤ honestBudget
          from Nat.zero_le _), map_bind]
        refine bind_congr fun r => ?_
        rw [map_runProj_prefix, map_runProj_prefix,
          ih r.1 (budget - sourceCost (.inl (.inl draw) : CostSpec.Domain)) (hcost.2 r.1)]
        rfl
      · change runProj <$> interp tg initial model (honestRead (D := HashInput) (R := HashOutput)
          (ι := Coordinate) bytes >>= _) honestBudget state = _
        rw [honestRead, interp_query_bind, ite_eq_left (show sourceCost (.inr (.inr bytes) : CostSpecH.Domain) ≤
          honestBudget from Nat.zero_le _), map_bind]
        refine bind_congr fun r => ?_
        rw [map_runProj_prefix, map_runProj_prefix,
          ih r.1 (budget - sourceCost (.inl (.inr (.inl bytes)) : CostSpec.Domain)) (hcost.2 r.1)]
        rfl
      · change runProj <$> interp tg initial model
          (liftM (CostSpecH.query (.inl (.inr (.inr coordinate)))) >>= _) honestBudget state = _
        rw [interp_query_bind, ite_eq_left (show sourceCost (.inl (.inr (.inr coordinate)) : CostSpecH.Domain) ≤
          honestBudget from Nat.zero_le _), map_bind]
        refine bind_congr fun r => ?_
        rw [map_runProj_prefix, map_runProj_prefix,
          ih r.1 (budget - sourceCost (.inl (.inr (.inr coordinate)) : CostSpec.Domain)) (hcost.2 r.1)]
        rfl
      · change runProj <$> interp tg initial model (pure () >>= _) honestBudget state = _
        rw [pure_bind]
        change _ = (pure ((), state) : ProbComp _) >>= _
        rw [pure_bind, map_runProj_prefix, ih () (budget - amount) (hcost.2 ()) honestBudget state]
        exact (id_map _).symm
      · exact Empty.elim honest

/-- **Bounds transfer to the honest form**: a sum over the honest form's run, of a function of its
result, reveals and final state, is the same sum over the charged program's run at a budget it
cannot exhaust. -/
theorem tsum_interp_toHonest {α : Type} (computation : OracleComp CostSpec α)
    (G : (Option α × List Coordinate) × DebtState HashInput HashOutput Coordinate → ℝ≥0∞) (honestBudget : ℕ)
    (state : DebtState HashInput HashOutput Coordinate) :
    ∃ budget, CostAtMost computation budget ∧
      ∑' out, Pr{let x ← interp tg initial model (simulateQ toHonest computation) honestBudget state}[x = out] *
          G (runProj out) =
        ∑' out, Pr{let x ← interp tg initial model computation budget state}[x = out] * G (runProj out) := by
  obtain ⟨budget, hbudget⟩ := exists_costAtMost computation
  refine ⟨budget, hbudget, ?_⟩
  rw [← OracleComp.tsum_prEvent_map_mul _ runProj G, ← OracleComp.tsum_prEvent_map_mul _ runProj G,
    interp_toHonest tg initial model computation budget hbudget honestBudget state]

theorem mem_support_interp_toHonest {α : Type} (computation : OracleComp CostSpec α) (budget : ℕ)
    (hbudget : CostAtMost computation budget) (honestBudget : ℕ) (state : DebtState HashInput HashOutput Coordinate)
    (out : Run HashInput Coordinate α × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (simulateQ toHonest computation) honestBudget state)) :
    ∃ out' ∈ support (interp tg initial model computation budget state), runProj out' = runProj out := by
  have h : runProj out ∈ support (runProj <$> interp tg initial model computation budget state) := by
    rw [← interp_toHonest tg initial model computation budget hbudget honestBudget state, support_map]
    exact ⟨out, hout, rfl⟩
  rw [support_map] at h
  exact h

/-- **An honest run records nothing**: its trace and its touches are empty, so it spends no budget. -/
theorem interp_toHonest_quiet {α : Type} (computation : OracleComp CostSpec α) :
    ∀ honestBudget state, ∀ out ∈ support (interp tg initial model (simulateQ toHonest computation)
      honestBudget state), out.1.2.2.1 = [] ∧ out.1.2.2.2 = [] := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro honestBudget state out hout
      rw [simulateQ_pure, interp_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact ⟨rfl, rfl⟩
  | query_bind input next ih =>
      intro honestBudget state out hout
      rw [simulateQ_bind, simulateQ_spec_query] at hout
      rcases input with (draw | bytes | coordinate) | (amount | honest)
      · change out ∈ support (interp tg initial model (liftM (CostSpecH.query (.inl (.inl draw))) >>= _)
          honestBudget state) at hout
        rw [interp_query_bind, ite_eq_left (show sourceCost (.inl (.inl draw) : CostSpecH.Domain) ≤ honestBudget
          from Nat.zero_le _), support_bind] at hout
        obtain ⟨r, -, hout⟩ := Set.mem_iUnion₂.1 hout
        rw [support_map] at hout
        obtain ⟨o, ho, rfl⟩ := hout
        exact ih r.1 _ _ o ho
      · change out ∈ support (interp tg initial model (honestRead (D := HashInput) (R := HashOutput)
          (ι := Coordinate) bytes >>= _) honestBudget state) at hout
        rw [honestRead, interp_query_bind, ite_eq_left (show sourceCost (.inr (.inr bytes) : CostSpecH.Domain) ≤
          honestBudget from Nat.zero_le _), support_bind] at hout
        obtain ⟨r, -, hout⟩ := Set.mem_iUnion₂.1 hout
        rw [support_map] at hout
        obtain ⟨o, ho, rfl⟩ := hout
        exact ih r.1 _ _ o ho
      · change out ∈ support (interp tg initial model
          (liftM (CostSpecH.query (.inl (.inr (.inr coordinate)))) >>= _) honestBudget state) at hout
        rw [interp_query_bind, ite_eq_left (show sourceCost (.inl (.inr (.inr coordinate)) : CostSpecH.Domain) ≤
          honestBudget from Nat.zero_le _), support_bind] at hout
        obtain ⟨r, -, hout⟩ := Set.mem_iUnion₂.1 hout
        rw [support_map] at hout
        obtain ⟨o, ho, rfl⟩ := hout
        exact ih r.1 _ _ o ho
      · change out ∈ support (interp tg initial model (pure () >>= _) honestBudget state) at hout
        rw [pure_bind] at hout
        exact ih () _ _ out hout
      · exact Empty.elim honest

theorem interpThenH_some {α β : Type} (next : α → OracleComp CostSpecH β) (budget : ℕ)
    (o1 : Run HashInput Coordinate α × DebtState HashInput HashOutput Coordinate) (v : α) (hv : o1.1.1 = some v) :
    interpThen tg initial model next budget o1 =
      (fun o2 => ((o2.1.1, o1.1.2.1 ++ o2.1.2.1, o1.1.2.2.1 ++ o2.1.2.2.1, o1.1.2.2.2 ++ o2.1.2.2.2), o2.2)) <$>
        interp tg initial model (next v) (budget - traceCost o1.1.2.2.1) o1.2 := by
  unfold interpThen
  rw [hv]

theorem interpThenH_none {α β : Type} (next : α → OracleComp CostSpecH β) (budget : ℕ)
    (o1 : Run HashInput Coordinate α × DebtState HashInput HashOutput Coordinate) (hv : o1.1.1 = none) :
    interpThen tg initial model next budget o1 = pure ((none, o1.1.2.1, o1.1.2.2.1, o1.1.2.2.2), o1.2) := by
  unfold interpThen
  rw [hv]

end FORS.Security.GraphView

/-! ### The honest signer is the honest form of the charged signer -/

namespace FORS.Security.GraphView

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt

set_option backward.isDefEq.respectTransparency false

theorem toHonest_liftProb {β : Type} (computation : ProbComp β) :
    simulateQ toHonest (liftM computation : OracleComp CostSpec β) =
      (liftM computation : OracleComp CostSpecH β) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, simulateQ_pure]
  | query_bind draw next ih =>
      simp only [liftM_bind, simulateQ_bind]
      have hq : simulateQ toHonest (liftM (liftM (unifSpec.query draw) : ProbComp _) : OracleComp CostSpec _) =
          (liftM (liftM (unifSpec.query draw) : ProbComp _) : OracleComp CostSpecH _) := by
        change simulateQ toHonest (liftM (CostSpec.query (.inl (.inl draw)))) = _
        rw [simulateQ_spec_query]
        rfl
      rw [hq]
      exact bind_congr ih

theorem toHonest_liftHash {β : Type} (computation : OracleComp HashSpec β) :
    simulateQ toHonest (liftM computation : OracleComp CostSpec β) = liftHonest computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [liftM_pure, simulateQ_pure, liftHonest]
  | query_bind bytes next ih =>
      simp only [liftM_bind, simulateQ_bind, liftHonest] at ih ⊢
      have hq : simulateQ toHonest (liftM (liftM (HashSpec.query bytes) : OracleComp HashSpec _) :
          OracleComp CostSpec _) = honestHash bytes := by
        change simulateQ toHonest (liftM (CostSpec.query (.inl (.inr (.inl bytes))))) = _
        rw [simulateQ_spec_query]
        rfl
      rw [hq, simulateQ_spec_query]
      exact bind_congr ih

theorem toHonest_tick (amount : ℕ) :
    simulateQ toHonest (HiddenCost.tick amount : OracleComp CostSpec Unit) = pure () := by
  rw [HiddenCost.tick, simulateQ_spec_query]
  rfl

theorem toHonest_reveal (coordinate : Coordinate) :
    simulateQ toHonest (HiddenCost.reveal (H := Empty) (D := HashInput) (R := HashOutput) coordinate) =
      HiddenCost.reveal (H := HashInput) (D := HashInput) (R := HashOutput) coordinate := by
  rw [HiddenCost.reveal, simulateQ_spec_query]
  rfl

theorem toHonest_sequenceFin {β : Type} :
    ∀ {n : ℕ} (computation : Fin n → OracleComp CostSpec β),
      simulateQ toHonest (sequenceFin computation) = sequenceFin fun i => simulateQ toHonest (computation i)
  | 0, _ => by simp only [sequenceFin, simulateQ_pure]
  | n + 1, computation => by
      simp only [sequenceFin, simulateQ_bind, simulateQ_pure]
      refine bind_congr fun head => ?_
      rw [toHonest_sequenceFin (n := n) fun index => computation index.succ]

theorem toHonest_sequenceDep :
    ∀ {n : ℕ} {β : Fin n → Type} (computation : (i : Fin n) → OracleComp CostSpec (Option (β i))),
      simulateQ toHonest (sequenceDep computation) = sequenceDep fun i => simulateQ toHonest (computation i)
  | 0, _, _ => by simp only [sequenceDep, simulateQ_pure]
  | n + 1, β, computation => by
      simp only [sequenceDep, simulateQ_bind]
      refine bind_congr fun last => ?_
      cases last with
      | none => simp only [simulateQ_pure]
      | some last =>
          simp only [simulateQ_bind]
          rw [toHonest_sequenceDep (n := n) (β := fun i => β i.castSucc) fun i => computation i.castSucc]
          refine bind_congr fun init => ?_
          cases init <;> simp only [simulateQ_pure]

variable (parameter : PublicParameter) (data : PublicData)

theorem toHonest_layerCostSearch (index : Index) (lay : Layer) :
    simulateQ toHonest (layerCostSearch parameter data index lay) = layerCostSearchH parameter data index lay := by
  rw [layerCostSearch, layerCostSearchH, simulateQ_bind, toHonest_liftHash]
  conv_rhs => rw [← bind_pure (liftHonest (layerSearch parameter data index lay))]
  refine bind_congr fun found => ?_
  cases found with
  | none => simp only [simulateQ_pure]
  | some pair => simp only [simulateQ_bind, toHonest_tick, simulateQ_pure, pure_bind]

theorem toHonest_treeCostSource (index : Index) (κ : FTree) (leaf : FLeaf) :
    simulateQ toHonest (treeCostSource data index κ leaf) = treeCostSourceH data index κ leaf := by
  simp only [treeCostSource, treeCostSourceH, simulateQ_bind, simulateQ_pure, toHonest_sequenceFin,
    toHonest_reveal]

theorem toHonest_finishCostSource (message : Message) (randomness : Randomness) :
    simulateQ toHonest (finishCostSource parameter data message randomness) =
      finishCostSourceH parameter data message randomness := by
  simp only [finishCostSource, finishCostSourceH, simulateQ_bind, toHonest_liftHash, toHonest_tick, pure_bind]
  refine bind_congr fun digest => ?_
  rw [toHonest_sequenceDep]
  simp only [toHonest_layerCostSearch]
  refine bind_congr fun found => ?_
  cases found with
  | none => simp only [simulateQ_pure]
  | some found =>
      simp only [simulateQ_bind, toHonest_sequenceFin, toHonest_reveal, toHonest_treeCostSource, simulateQ_pure]

theorem toHonest_signCostSourceLoop (message : Message) (step : Randomness) :
    ∀ attempts randomness,
      simulateQ toHonest (signCostSourceLoop parameter data message step attempts randomness) =
        signCostSourceLoopH parameter data message step attempts randomness
  | 0, _ => by simp only [signCostSourceLoop, signCostSourceLoopH, simulateQ_pure]
  | attempts + 1, randomness => by
      rw [signCostSourceLoop, signCostSourceLoopH, simulateQ_bind, toHonest_liftHash]
      refine bind_congr fun first => ?_
      split
      · exact toHonest_finishCostSource parameter data message randomness
      · exact toHonest_signCostSourceLoop message step attempts (randomness + step)

/-- **The honest signer is the honest form of the charged signer.** -/
theorem signCostSourceH_eq (message : Message) :
    signCostSourceH parameter data message = simulateQ toHonest (signCostSource parameter data message) := by
  rw [signCostSource, signCostSourceH, simulateQ_bind, toHonest_liftProb]
  refine bind_congr fun start => ?_
  rw [toHonest_signCostSourceLoop]

end FORS.Security.GraphView
