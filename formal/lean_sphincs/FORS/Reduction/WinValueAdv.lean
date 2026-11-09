module

public import FORS.Reduction.AdvCountGame
public import FORS.Reduction.WinValue
public import FORS.Reduction.UntilSeedH

@[expose] public section

/-! `DetValue` for the cost interface with honest reads (`CostSpecH`): the budgeted win value
`valH` of a program on a fixed answer function, the adversary's interaction with the honest
deterministic signer (`advDet`) and with the honest fresh-randomizer signer (`advRand`), and
`win_avg_le`: with uniform base randomizers the deterministic game wins at most as often as the
fresh-randomizer game of the memoizing adversary. The signer reads honestly and is never charged,
so averaging a base randomizer is an equality (no derivation tick). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.AdvCount

variable [Params]

open HiddenCost GraphView Stop DetValue

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable (g : HashInput → HashOutput) (c : HiddenGraph.Table)

/-- The probability that the budget-capped run returns a value satisfying `E`. -/
noncomputable def valH {α : Type} (E : α → Prop) (P : OracleComp CostSpecH α) (b : ℕ) : ℝ≥0∞ :=
  Pr{let r ← costRunH g c (cap P b)}[∃ v, r.1 = some v ∧ E v]

theorem valH_pure {α : Type} (E : α → Prop) (v : α) (b : ℕ) :
    valH g c E (pure v) b = if E v then 1 else 0 := by
  rw [valH, capH_pure, costRunH_pure, prEvent_pure]
  by_cases h : E v
  · simp [h]
  · simp [h]

theorem valH_query_bind {α : Type} (E : α → Prop) (i : CostSpecH.Domain)
    (k : CostSpecH.Range i → OracleComp CostSpecH α) (b : ℕ) :
    valH g c E (liftM (CostSpecH.query i) >>= k) b =
      if sourceCost i ≤ b then
        ∑' a, Pr{let x ← fixedCostPH g c i}[x = a] * valH g c E (k a) (b - sourceCost i)
      else 0 := by
  rw [valH, capH_query_bind]
  split
  · rw [costRunH_query_bind, OracleComp.prEvent_bind_eq_tsum]
    refine tsum_congr fun a => ?_
    rw [prEvent_map]
    rfl
  · rw [costRunH_pure, prEvent_pure]
    simp

theorem valH_mono {α : Type} (E : α → Prop) (P : OracleComp CostSpecH α) :
    ∀ b b', b ≤ b' → valH g c E P b ≤ valH g c E P b' := by
  induction P using OracleComp.inductionOn with
  | pure v => intro b b' _; rw [valH_pure, valH_pure]
  | query_bind i k ih =>
      intro b b' hb
      rw [valH_query_bind, valH_query_bind]
      split
      · rename_i hcost
        rw [ite_eq_left (hcost.trans hb)]
        exact ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (ih a _ _ (by omega))
      · exact bot_le

/-- Averaging a family of continuations after a common program. -/
theorem valH_bind_le_avg {ρ α β : Type} (E : β → Prop) (w : ρ → ℝ≥0∞)
    (P : OracleComp CostSpecH α) (k : ρ → α → OracleComp CostSpecH β) (k' : α → OracleComp CostSpecH β)
    (h : ∀ x ∈ support (simulateQ (fixedCostPH g c) P), ∀ b',
      ∑' R, w R * valH g c E (k R x) b' ≤ valH g c E (k' x) b') :
    ∀ b, ∑' R, w R * valH g c E (P >>= k R) b ≤ valH g c E (P >>= k') b := by
  induction P using OracleComp.inductionOn with
  | pure x =>
      intro b
      simp only [pure_bind]
      exact h x (by simp) b
  | query_bind i p ih =>
      intro b
      simp only [bind_assoc]
      rw [valH_query_bind]
      simp_rw [valH_query_bind]
      split
      · rename_i hcost
        simp_rw [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        refine ENNReal.tsum_le_tsum fun a => ?_
        simp_rw [mul_left_comm (w _), ENNReal.tsum_mul_left]
        by_cases ha : a ∈ support (fixedCostPH g c i)
        · refine mul_le_mul' le_rfl (ih a (fun x hx b' => h x ?_ b') _)
          rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff]
          exact ⟨a, ha, hx⟩
        · rw [(prEvent_eq_zero_of_not_mem_support _) ha]
          simp
      · simp

/-- A continuation comparison on the support of a common program. -/
theorem valH_bind_mono {α β : Type} (E : β → Prop)
    (P : OracleComp CostSpecH α) (k k' : α → OracleComp CostSpecH β)
    (h : ∀ x ∈ support (simulateQ (fixedCostPH g c) P), ∀ b', valH g c E (k x) b' ≤ valH g c E (k' x) b')
    (b : ℕ) : valH g c E (P >>= k) b ≤ valH g c E (P >>= k') b := by
  have := valH_bind_le_avg g c E (fun _ : Unit => (1 : ℝ≥0∞)) P (fun _ => k) k'
    (fun x hx b' => by simpa using h x hx b') b
  simpa using this

/-- A program all of whose outputs lead to a value at most `V0` for every smaller budget. -/
theorem valH_bind_le_of {α β : Type} (E : β → Prop)
    (P : OracleComp CostSpecH α) (k : α → OracleComp CostSpecH β) (V0 : ℝ≥0∞) :
    ∀ b, (∀ x ∈ support (simulateQ (fixedCostPH g c) P), ∀ b' ≤ b, valH g c E (k x) b' ≤ V0) →
      valH g c E (P >>= k) b ≤ V0 := by
  induction P using OracleComp.inductionOn with
  | pure x =>
      intro b h
      simpa using h x (by simp) b le_rfl
  | query_bind i p ih =>
      intro b h
      rw [bind_assoc, valH_query_bind]
      split
      · calc
          _ ≤ ∑' a, Pr{let x ← fixedCostPH g c i}[x = a] * V0 := by
            refine ENNReal.tsum_le_tsum fun a => ?_
            by_cases ha : a ∈ support (fixedCostPH g c i)
            · refine mul_le_mul' le_rfl (ih a _ fun x hx b' hb' => h x ?_ b' (by omega))
              rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff]
              exact ⟨a, ha, hx⟩
            · rw [(prEvent_eq_zero_of_not_mem_support _) ha]
              simp
          _ ≤ V0 := by
            rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left bot_le (OracleComp.tsum_prEvent_le_one _)
      · exact bot_le

/-- Lifted private randomness is averaged with its own law. -/
theorem valH_liftProb_bind {γ α : Type} (E : α → Prop) (p : ProbComp γ)
    (k : γ → OracleComp CostSpecH α) (b : ℕ) :
    valH g c E ((liftM p : OracleComp CostSpecH γ) >>= k) b = ∑' x, Pr{let y ← p}[y = x] * valH g c E (k x) b := by
  induction p using OracleComp.inductionOn with
  | pure x => simp only [liftM_pure, pure_bind, OracleComp.tsum_prEvent_pure_mul]
  | query_bind draw next ih =>
      rw [liftM_bind, bind_assoc]
      change valH g c E (liftM (CostSpecH.query (.inl (.inl draw))) >>= fun a =>
        (liftM (next a) : OracleComp CostSpecH γ) >>= k) b = _
      rw [valH_query_bind]
      show (if (0 : ℕ) ≤ b then ∑' a : Fin (draw + 1),
          Pr{let x ← (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))}[x = a] *
            valH g c E ((liftM (next a) : OracleComp CostSpecH γ) >>= k) (b - 0) else 0) = _
      rw [ite_eq_left (Nat.zero_le _), Nat.sub_zero, OracleComp.tsum_prEvent_bind_mul]
      refine tsum_congr fun a => ?_
      rw [ih a]

/-! ### One message: a derived randomizer base read once is a fresh uniform start -/

/-- Averaging the planted base `R0` of one message, its step fixed: the honest deterministic
signer (the scan from the base, nothing charged) wins as often as the scan from a uniform start. -/
theorem row_le {α : Type} (E : α → Prop) (parameter : PublicParameter) (data : PublicData)
    (message : Message) (k : Option Signature → OracleComp CostSpecH α) (n b : ℕ) :
    ∑' r, Pr{let z ← ($ᵗ Randomness : ProbComp Randomness)}[z = r] *
        valH g c E (signCostSourceLoopH parameter data message (data.step message) n r >>= k) b =
      valH g c E (((liftM ($ᵗ Randomness : ProbComp Randomness) : OracleComp CostSpecH Randomness) >>=
        fun start => signCostSourceLoopH parameter data message (data.step message) n start) >>= k) b := by
  rw [bind_assoc, valH_liftProb_bind]

/-! ### The adversary's interaction as a cost program -/

open Internalize ForsPotential

noncomputable def finishBool (parameter : PublicParameter) (data : PublicData) (L : QueryLog SigningSpec)
    (forgery : Forgery) : OracleComp CostSpecH Bool := do
  let verified ← liftRawH (Concrete.verify (⟨data.root, parameter⟩ : PublicKey) forgery.message
    forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid L ∧ ¬SigningTranscript.Contains L forgery) && verified

/-- The rest of the deterministic game from an adversary computation and a log prefix. -/
noncomputable def advDet (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable)
    (M : OracleComp AdvSpec Forgery) (L : QueryLog SigningSpec) : OracleComp CostSpecH Bool :=
  (simulateQ (costInteractionDet parameter data rnd) M).run >>= fun r =>
    finishBool parameter data (L ++ r.2) r.1

/-- The rest of the fresh-randomizer game from an adversary computation and a log prefix. -/
noncomputable def advRand (parameter : PublicParameter) (data : PublicData)
    (M : OracleComp AdvSpec Forgery) (L : QueryLog SigningSpec) : OracleComp CostSpecH Bool :=
  (simulateQ (costInteractionH parameter data) M).run >>= fun r =>
    finishBool parameter data (L ++ r.2) r.1

theorem costRestDetH_eq (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable)
    (adversary : Adversary) :
    costRestDet parameter data rnd adversary =
      advDet parameter data rnd (adversary.main ⟨data.root, parameter⟩) [] := by
  unfold costRestDet advDet finishBool
  refine bind_congr fun r => ?_
  rcases r with ⟨forgery, log⟩
  simp only [List.nil_append]

theorem costRestH_eq (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    costRest parameter data adversary = advRand parameter data (adversary.main ⟨data.root, parameter⟩) [] := by
  unfold costRest advRand finishBool
  refine bind_congr fun r => ?_
  rcases r with ⟨forgery, log⟩
  simp only [List.nil_append]

theorem advDetH_pure (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable)
    (forgery : Forgery) (L : QueryLog SigningSpec) :
    advDet parameter data rnd (pure forgery) L = finishBool parameter data L forgery := by
  unfold advDet
  rw [simulateQ_pure, WriterT.run_pure, pure_bind]
  simp

theorem advRandH_pure (parameter : PublicParameter) (data : PublicData)
    (forgery : Forgery) (L : QueryLog SigningSpec) :
    advRand parameter data (pure forgery) L = finishBool parameter data L forgery := by
  unfold advRand
  rw [simulateQ_pure, WriterT.run_pure, pure_bind]
  simp

theorem advDetH_world (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable)
    (t : OracleWorld.Domain) (next : OracleWorld.Range t → OracleComp AdvSpec Forgery)
    (L : QueryLog SigningSpec) :
    advDet parameter data rnd (liftM (AdvSpec.query (.inl t)) >>= next) L =
      ordinaryCostSourceH t >>= fun v => advDet parameter data rnd (next v) L := by
  unfold advDet
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change (((fun v => (v, (∅ : QueryLog SigningSpec))) <$> ordinaryCostSourceH t) >>= _) >>= _ = _
  simp only [bind_map_left, bind_assoc]
  rfl

theorem advRandH_world (parameter : PublicParameter) (data : PublicData)
    (t : OracleWorld.Domain) (next : OracleWorld.Range t → OracleComp AdvSpec Forgery)
    (L : QueryLog SigningSpec) :
    advRand parameter data (liftM (AdvSpec.query (.inl t)) >>= next) L =
      ordinaryCostSourceH t >>= fun v => advRand parameter data (next v) L := by
  unfold advRand
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change (((fun v => (v, (∅ : QueryLog SigningSpec))) <$> ordinaryCostSourceH t) >>= _) >>= _ = _
  simp only [bind_map_left, bind_assoc]
  rfl

theorem advDetH_sign (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable)
    (message : Message) (next : Option Signature → OracleComp AdvSpec Forgery)
    (L : QueryLog SigningSpec) :
    advDet parameter data rnd (liftM (AdvSpec.query (.inr message)) >>= next) L =
      signCostDet parameter data rnd message >>= fun r =>
        advDet parameter data rnd (next r) (L ++ [⟨message, r⟩]) := by
  unfold advDet
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change ((QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpecH)
      (fun message => signCostDet parameter data rnd message) message).run >>= _) >>= _ = _
  rw [QueryImpl.run_withLogging_apply]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun r => ?_
  rw [bind_map_left]
  refine bind_congr fun r' => ?_
  simp only [List.append_assoc]

theorem advRandH_sign (parameter : PublicParameter) (data : PublicData)
    (message : Message) (next : Option Signature → OracleComp AdvSpec Forgery)
    (L : QueryLog SigningSpec) :
    advRand parameter data (liftM (AdvSpec.query (.inr message)) >>= next) L =
      signCostSourceH parameter data message >>= fun r =>
        advRand parameter data (next r) (L ++ [⟨message, r⟩]) := by
  unfold advRand
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change ((QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpecH)
      (fun message => signCostSourceH parameter data message) message).run >>= _) >>= _ = _
  rw [QueryImpl.run_withLogging_apply]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun r => ?_
  rw [bind_map_left]
  refine bind_congr fun r' => ?_
  simp only [List.append_assoc]

/-- A program that never signs a message of `S` reads no randomizer base of `S`. -/
theorem advDetH_update (parameter : PublicParameter) (data : PublicData) :
    ∀ (M : OracleComp AdvSpec Forgery) (S : List Message) (L : QueryLog SigningSpec) (rnd : Det.RTable)
      (m : Message) (row : HashOutput), NoRepeat M S → m ∈ S →
      advDet parameter data (Function.update rnd m row) M L = advDet parameter data rnd M L := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery => intro S L rnd m row _ _; rw [advDetH_pure, advDetH_pure]
  | query_bind t next ih =>
      intro S L rnd m row hnr hm
      rcases t with t | m'
      · rw [advDetH_world, advDetH_world]
        exact bind_congr fun v => ih v S L rnd m row (hnr v) hm
      · obtain ⟨hnot, hrest⟩ := hnr
        have hne : m' ≠ m := fun heq => hnot (heq ▸ hm)
        rw [advDetH_sign, advDetH_sign]
        have hsign : signCostDet parameter data (Function.update rnd m row) m' =
            signCostDet parameter data rnd m' := by
          unfold signCostDet
          rw [Function.update_of_ne hne]
        rw [hsign]
        exact bind_congr fun r => ih r (S ++ [m']) _ rnd m row (hrest r) (List.mem_append_left _ hm)

attribute [local irreducible] digestAttemptLimit

/-- **Averaging the derived base randomizers.** For a program that never repeats a request, the
deterministic game whose base randomizers are uniform and whose step halves are those of `data`
wins (within budget) at most as often as the fresh-randomizer game. -/
theorem avg_advDet (E : Bool → Prop) (parameter : PublicParameter) (data : PublicData) :
    ∀ (M : OracleComp AdvSpec Forgery) (S : List Message) (L : QueryLog SigningSpec), NoRepeat M S → ∀ b,
      ∑' lows, Pr{let z ← ($ᵗ Det.LTable : ProbComp Det.LTable)}[z = lows] *
          valH g c E (advDet parameter data (Det.joinTable lows data.steps) M L) b ≤
        valH g c E (advRand parameter data M L) b := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro S L _ b
      simp only [advDetH_pure, advRandH_pure]
      exact tsum_prob_mul_le _ _
  | query_bind t next ih =>
      intro S L hnr b
      rcases t with t | m
      · simp only [advDetH_world, advRandH_world]
        exact valH_bind_le_avg g c E _ _ _ _ (fun v _ b' => ih v S L (hnr v) b') b
      · obtain ⟨hnot, hrest⟩ := hnr
        simp only [advDetH_sign, advRandH_sign]
        rw [tsum_uniform_update m]
        have hloc : ∀ (low : Randomness) (lows : Det.LTable),
            (signCostDet parameter data (Det.joinTable (Function.update lows m low) data.steps) m >>= fun r =>
              advDet parameter data (Det.joinTable (Function.update lows m low) data.steps) (next r)
                (L ++ [⟨m, r⟩])) =
            (signCostSourceLoopH parameter data m (data.step m) digestAttemptLimit low >>= fun r =>
              advDet parameter data (Det.joinTable lows data.steps) (next r) (L ++ [⟨m, r⟩])) := by
          intro low lows
          rw [Det.joinTable_update]
          unfold signCostDet
          rw [Function.update_self, Det.truncateHash_joinHalves, Det.upperHash_joinHalves]
          exact bind_congr fun r => advDetH_update parameter data (next r) (S ++ [m]) _ _ m _ (hrest r)
            (List.mem_append_right _ (List.mem_singleton_self m))
        simp_rw [hloc]
        calc
          _ ≤ ∑' low, Pr{let z ← ($ᵗ Randomness : ProbComp Randomness)}[z = low] *
                valH g c E (signCostSourceLoopH parameter data m (data.step m) digestAttemptLimit low >>= fun r =>
                  advRand parameter data (next r) (L ++ [⟨m, r⟩])) b := by
            refine ENNReal.tsum_le_tsum fun low => mul_le_mul' le_rfl ?_
            exact valH_bind_le_avg g c E _ _ _ _ (fun r _ b' => ih r (S ++ [m]) _ (hrest r) b') b
          _ ≤ _ := by
            rw [signCostSourceH]
            exact (row_le g c E parameter data m _ digestAttemptLimit b).le

/-! ### The deterministic signer is deterministic on a fixed answer function -/

attribute [local irreducible] ReferenceChoice.search encodingAttemptLimit

theorem fixedCostPH_liftHonest {γ : Type} (oa : OracleComp HashSpec γ) :
    simulateQ (fixedCostPH g c) (liftHonest oa) = pure (evalWithAnswerFn g oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [liftHonest]
  | query_bind x next ih =>
      simp only [liftHonest] at ih
      simp only [liftHonest, simulateQ_bind, simulateQ_spec_query, honestHash, HiddenCost.honestRead, ih]
      change (pure (g x) : ProbComp HashOutput) >>= _ = _
      rw [pure_bind, evalWithAnswerFn_bind]
      rfl

theorem fixedCostPH_sequenceFin_pure {α : Type} {n : ℕ} (computation : Fin n → OracleComp CostSpecH α)
    (h : ∀ i, ∃ x, simulateQ (fixedCostPH g c) (computation i) = pure x) :
    ∃ x, simulateQ (fixedCostPH g c) (Concrete.sequenceFin computation) = pure x := by
  induction n with
  | zero => exact ⟨_, by simp only [Concrete.sequenceFin, simulateQ_pure]; rfl⟩
  | succ n ih =>
      obtain ⟨x0, h0⟩ := h 0
      obtain ⟨xs, hs⟩ := ih (fun index => computation index.succ) (fun i => h i.succ)
      refine ⟨Fin.cases x0 xs, ?_⟩
      simp only [Concrete.sequenceFin, simulateQ_bind, h0, pure_bind, hs, simulateQ_pure]

theorem fixedCostPH_reveal (which : HiddenGraph.Coordinate) :
    simulateQ (fixedCostPH g c) (HiddenCost.reveal (H := HashInput) (D := HashInput) (R := HashOutput) which) = pure (c which) := by
  rw [HiddenCost.reveal, simulateQ_spec_query]
  rfl

theorem fixedCostPH_fors_det (data : PublicData) (index : Index) (leaves : FTree → FLeaf) :
    ∃ x, simulateQ (fixedCostPH g c) (Concrete.sequenceFin fun κ => treeCostSourceH data index κ (leaves κ)) =
      pure x := by
  apply fixedCostPH_sequenceFin_pure
  intro κ
  obtain ⟨x, hx⟩ := fixedCostPH_sequenceFin_pure g c _ (fun k : Fin 2 => ⟨_, fixedCostPH_reveal g c
    (.fors index κ (leaves κ) k)⟩)
  exact ⟨_, by rw [treeCostSourceH, simulateQ_bind, hx, pure_bind, simulateQ_pure]⟩

theorem fixedCostPH_bind_det {α β : Type} (oa : OracleComp CostSpecH α) (next : α → OracleComp CostSpecH β)
    (h : ∃ x, simulateQ (fixedCostPH g c) oa = pure x)
    (hnext : ∀ y, ∃ z, simulateQ (fixedCostPH g c) (next y) = pure z) :
    ∃ w, simulateQ (fixedCostPH g c) (oa >>= next) = pure w := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨z, hz⟩ := hnext x
  exact ⟨z, by rw [simulateQ_bind, hx, pure_bind, hz]⟩

theorem fixedCostPH_sequenceDep_det : ∀ {n : Nat} {α : Fin n → Type}
    (computation : (i : Fin n) → OracleComp CostSpecH (Option (α i))),
    (∀ i, ∃ x, simulateQ (fixedCostPH g c) (computation i) = pure x) →
    ∃ x, simulateQ (fixedCostPH g c) (Concrete.sequenceDep computation) = pure x
  | 0, _, _, _ => ⟨_, by simp only [Concrete.sequenceDep, simulateQ_pure]; rfl⟩
  | n + 1, α, computation, h => by
      obtain ⟨x0, h0⟩ := h (Fin.last _)
      simp only [Concrete.sequenceDep, simulateQ_bind, h0, pure_bind]
      rcases x0 with _ | head
      · exact ⟨_, simulateQ_pure _ _⟩
      · obtain ⟨xs, hs⟩ := fixedCostPH_sequenceDep_det (α := fun i => α i.castSucc)
          (fun i => computation i.castSucc) (fun i => h i.castSucc)
        simp only [simulateQ_bind, hs, pure_bind]
        rcases xs with _ | tail <;> exact ⟨_, simulateQ_pure _ _⟩

theorem layerCostSearchH_det (parameter : PublicParameter) (data : PublicData) (index : Index)
    (lay : Layer) :
    ∃ x, simulateQ (fixedCostPH g c) (layerCostSearchH parameter data index lay) = pure x :=
  ⟨_, fixedCostPH_liftHonest g c _⟩

theorem finishCostSourceH_det (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) :
    ∃ x, simulateQ (fixedCostPH g c) (finishCostSourceH parameter data message randomness) = pure x := by
  simp only [finishCostSourceH, simulateQ_bind, fixedCostPH_liftHonest, pure_bind]
  obtain ⟨xs, hs⟩ := fixedCostPH_sequenceDep_det g c _
    (fun lay => layerCostSearchH_det g c parameter data _ lay)
  rw [hs, pure_bind]
  rcases xs with _ | found
  · exact ⟨_, simulateQ_pure _ _⟩
  · refine fixedCostPH_bind_det g c _ _ (fixedCostPH_sequenceFin_pure g c _ (fun lay =>
      fixedCostPH_sequenceFin_pure g c _ (fun chain => ⟨_, fixedCostPH_reveal g c _⟩))) (fun _ => ?_)
    refine fixedCostPH_bind_det g c _ _ (fixedCostPH_fors_det g c data _ _) (fun _ => ?_)
    exact ⟨_, simulateQ_pure _ _⟩

theorem signCostDetLoopH_det (parameter : PublicParameter) (data : PublicData)
    (message : Message) (step : Randomness) : ∀ (n : ℕ) (start : Randomness),
    ∃ x, simulateQ (fixedCostPH g c) (signCostSourceLoopH parameter data message step n start) = pure x := by
  intro n
  induction n with
  | zero => intro start; exact ⟨none, rfl⟩
  | succ n ih =>
      intro start
      simp only [signCostSourceLoopH, simulateQ_bind, pure_bind, fixedCostPH_liftHonest]
      split
      · exact finishCostSourceH_det g c parameter data message _
      · exact ih (start + step)

theorem signCostDetH_det (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable)
    (message : Message) :
    ∃ x, simulateQ (fixedCostPH g c) (signCostDet parameter data rnd message) = pure x := by
  obtain ⟨x, hx⟩ := signCostDetLoopH_det g c parameter data message
    (walkStep (upperHash (rnd message))) digestAttemptLimit (truncateHash (rnd message))
  exact ⟨x, by rw [signCostDet, hx]⟩

/-! ### Memoizing at the cost level -/

/-- The memo record holds the deterministic signatures, each also in the memo log; both logs
have the same entries and the memo log is no longer. -/
def MemoInv (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable) (record : Memo.Record)
    (L L' : QueryLog SigningSpec) : Prop :=
  (∀ m σ, record m = some σ →
    simulateQ (fixedCostPH g c) (signCostDet parameter data rnd m) = pure σ ∧
      (⟨m, σ⟩ : (_ : Message) × Option Signature) ∈ L') ∧
  (∀ e, e ∈ L ↔ e ∈ L') ∧ L'.length ≤ L.length

theorem finishBoolH_le (parameter : PublicParameter) (data : PublicData) (L L' : QueryLog SigningSpec)
    (forgery : Forgery) (hmem : ∀ e, e ∈ L ↔ e ∈ L') (hlen : L'.length ≤ L.length) (b : ℕ) :
    valH g c (· = true) (finishBool parameter data L forgery) b ≤
      valH g c (· = true) (finishBool parameter data L' forgery) b := by
  unfold finishBool
  refine valH_bind_mono g c _ _ _ _ (fun v _ b' => ?_) b
  rw [valH_pure, valH_pure]
  by_cases h : (decide (SigningTranscript.Valid L ∧ ¬SigningTranscript.Contains L forgery) && v) = true
  · have h' : (decide (SigningTranscript.Valid L' ∧ ¬SigningTranscript.Contains L' forgery) && v) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      obtain ⟨⟨hvalid, hcontains⟩, hv⟩ := h
      refine ⟨⟨le_trans hlen hvalid, fun ⟨entry, hentry, heq⟩ => hcontains ⟨entry, (hmem entry).2 hentry, heq⟩⟩, hv⟩
    rw [ite_eq_left h, ite_eq_left h']
  · rw [ite_eq_right h]
    exact bot_le

open Memo in
theorem memo_le (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable) :
    ∀ (M : OracleComp AdvSpec Forgery) (record : Record) (L L' : QueryLog SigningSpec),
      MemoInv g c parameter data rnd record L L' → ∀ b,
        valH g c (· = true) (advDet parameter data rnd M L) b ≤
          valH g c (· = true) (advDet parameter data rnd (Prod.fst <$> (simulateQ memoImpl M).run record) L') b := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro record L L' hinv b
      simp only [simulateQ_pure, StateT.run_pure, map_pure, advDetH_pure]
      exact finishBoolH_le g c parameter data L L' forgery hinv.2.1 hinv.2.2 b
  | query_bind t next ih =>
      intro record L L' hinv b
      rw [memo_run_query_bind]
      rcases t with t | m
      · rw [memoImpl_world, bind_map_left, map_bind, advDetH_world, advDetH_world]
        exact valH_bind_mono g c _ _ _ _ (fun v _ b' => ih v record L L' hinv b') b
      · cases hm : record m with
        | some σ =>
            rw [memoImpl_sign_some m record σ hm, pure_bind, advDetH_sign]
            obtain ⟨hdet, hmemσ⟩ := hinv.1 m σ hm
            refine valH_bind_le_of g c _ _ _ _ b fun x hx b' hb' => ?_
            rw [hdet, support_pure, Set.mem_singleton_iff] at hx
            subst hx
            refine le_trans (valH_mono g c _ _ _ _ hb') (ih x record _ L' ⟨hinv.1, fun e => ?_, ?_⟩ b)
            · rw [List.mem_append, List.mem_singleton, hinv.2.1 e]
              constructor
              · rintro (h | rfl)
                · exact h
                · exact hmemσ
              · exact Or.inl
            · rw [List.length_append]
              exact le_trans hinv.2.2 (Nat.le_add_right _ _)
        | none =>
            rw [memoImpl_sign_none m record hm, bind_map_left, map_bind, advDetH_sign, advDetH_sign]
            obtain ⟨x0, hdet⟩ := signCostDetH_det g c parameter data rnd m
            refine valH_bind_mono g c _ _ _ _ (fun x hx b' => ?_) b
            rw [hdet, support_pure, Set.mem_singleton_iff] at hx
            subst hx
            refine ih x _ _ _ ⟨fun m' σ hm' => ?_, fun e => ?_, ?_⟩ b'
            · change Function.update record m (some x) m' = some σ at hm'
              by_cases heq : m' = m
              · subst heq
                rw [Function.update_self] at hm'
                cases hm'
                exact ⟨hdet, List.mem_append_right _ (List.mem_singleton_self _)⟩
              · rw [Function.update_of_ne heq] at hm'
                obtain ⟨h1, h2⟩ := hinv.1 m' σ hm'
                exact ⟨h1, List.mem_append_left _ h2⟩
            · rw [List.mem_append, List.mem_append, hinv.2.1 e]
            · rw [List.length_append, List.length_append]
              exact Nat.add_le_add_right hinv.2.2 _

/-! ### Game level -/

theorem memo_game_le (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable)
    (adversary : Adversary) (b : ℕ) :
    valH g c (· = true) (costGameDet parameter data rnd adversary) b ≤
      valH g c (· = true) (costGameDet parameter data rnd (Memo.memoAdv adversary)) b := by
  unfold costGameDet
  refine valH_bind_mono g c _ _ _ _ (fun _ _ b' => ?_) b
  rw [costRestDetH_eq, costRestDetH_eq]
  change _ ≤ valH g c (· = true) (advDet parameter data rnd
    ((simulateQ Memo.memoImpl (adversary.main ⟨data.root, parameter⟩)).run' Memo.emptyRecord) []) b'
  rw [StateT.run'_eq]
  exact memo_le g c parameter data rnd _ Memo.emptyRecord [] []
    ⟨fun m σ h => by simp [Memo.emptyRecord] at h, fun e => Iff.rfl, le_rfl⟩ b'

theorem avg_game (parameter : PublicParameter) (data : PublicData) (adversary : Adversary)
    (hnr : adversary.NoRepeat) (b : ℕ) :
    ∑' lows, Pr{let z ← ($ᵗ Det.LTable : ProbComp Det.LTable)}[z = lows] *
        valH g c (· = true) (costGameDet parameter data (Det.joinTable lows data.steps) adversary) b ≤
      valH g c (· = true) (costGame parameter data adversary) b := by
  unfold costGameDet costGame
  refine valH_bind_le_avg g c _ _ _ _ _ (fun _ _ b' => ?_) b
  simp only [costRestDetH_eq, costRestH_eq]
  exact avg_advDet g c _ parameter data _ [] [] (hnr _) b'

/-- **Deterministic randomizers, memoized and averaged.** With uniform base randomizers and the step
halves of `data`, the deterministic game of any adversary wins (within budget) at most as often as
the fresh-randomizer game of its memoizing version. -/
theorem win_avg_le (parameter : PublicParameter) (data : PublicData) (adversary : Adversary)
    (hnr : (Memo.memoAdv adversary).NoRepeat) (b : ℕ) :
    Pr{let x ← (do
        let lows ← ($ᵗ Det.LTable : ProbComp Det.LTable)
        costRunH g c (cap (costGameDet parameter data (Det.joinTable lows data.steps) adversary) b))}[Reduce.Win x] ≤
      Pr{let x ← costRunH g c (cap (costGame parameter data (Memo.memoAdv adversary)) b)}[Reduce.Win x] := by
  rw [OracleComp.prEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' lows, Pr{let z ← ($ᵗ Det.LTable : ProbComp Det.LTable)}[z = lows] *
          valH g c (· = true) (costGameDet parameter data (Det.joinTable lows data.steps)
            (Memo.memoAdv adversary)) b :=
      ENNReal.tsum_le_tsum fun lows => mul_le_mul' le_rfl
        (memo_game_le g c parameter data _ adversary b)
    _ ≤ _ := avg_game g c parameter data _ hnr b

end FORS.Security.AdvCount
