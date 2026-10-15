import Sphincs.BridgeDetCost
import Sphincs.BridgeDetMemo
import Sphincs.BridgeStop
import Sphincs.BridgeReduce

/-! The budgeted win value of a graph-view cost program on a fixed answer function, and the
comparisons it supports: monotonicity in the budget, averaging a family of continuations, and
lifted private randomness. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.DetValue

open HiddenCost GraphView Stop

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable (g : HashInput → HashOutput) (c : HiddenGraph.Table)

/-- The probability that the budget-capped run returns a value satisfying `E`. -/
noncomputable def val {α : Type} (E : α → Prop) (P : OracleComp CostSpec α) (b : ℕ) : ℝ≥0∞ :=
  Pr[fun r => ∃ v, r.1 = some v ∧ E v | costRun g c (cap P b)]

theorem val_pure {α : Type} (E : α → Prop) (v : α) (b : ℕ) :
    val g c E (pure v) b = if E v then 1 else 0 := by
  rw [val, cap_pure', costRun_pure, probEvent_pure]
  by_cases h : E v
  · simp [h]
  · simp [h]

theorem val_query_bind {α : Type} (E : α → Prop) (i : CostSpec.Domain)
    (k : CostSpec.Range i → OracleComp CostSpec α) (b : ℕ) :
    val g c E (liftM (CostSpec.query i) >>= k) b =
      if sourceCost i ≤ b then
        ∑' a, Pr[= a | fixedCostP g c i] * val g c E (k a) (b - sourceCost i)
      else 0 := by
  rw [val, cap_query_bind']
  split
  · rw [costRun_query_bind, probEvent_bind_eq_tsum]
    refine tsum_congr fun a => ?_
    rw [probEvent_map]
    rfl
  · rw [costRun_pure, probEvent_pure]
    simp

theorem val_mono {α : Type} (E : α → Prop) (P : OracleComp CostSpec α) :
    ∀ b b', b ≤ b' → val g c E P b ≤ val g c E P b' := by
  induction P using OracleComp.inductionOn with
  | pure v => intro b b' _; rw [val_pure, val_pure]
  | query_bind i k ih =>
      intro b b' hb
      rw [val_query_bind, val_query_bind]
      split
      · rename_i hcost
        rw [if_pos (hcost.trans hb)]
        exact ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl (ih a _ _ (by omega))
      · exact bot_le

/-- Averaging a family of continuations after a common program. -/
theorem val_bind_le_avg {ρ α β : Type} (E : β → Prop) (w : ρ → ℝ≥0∞)
    (P : OracleComp CostSpec α) (k : ρ → α → OracleComp CostSpec β) (k' : α → OracleComp CostSpec β)
    (h : ∀ x ∈ support (simulateQ (fixedCostP g c) P), ∀ b',
      ∑' R, w R * val g c E (k R x) b' ≤ val g c E (k' x) b') :
    ∀ b, ∑' R, w R * val g c E (P >>= k R) b ≤ val g c E (P >>= k') b := by
  induction P using OracleComp.inductionOn with
  | pure x =>
      intro b
      simp only [pure_bind]
      exact h x (by simp) b
  | query_bind i p ih =>
      intro b
      simp only [bind_assoc]
      rw [val_query_bind]
      simp_rw [val_query_bind]
      split
      · rename_i hcost
        simp_rw [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        refine ENNReal.tsum_le_tsum fun a => ?_
        simp_rw [mul_left_comm (w _), ENNReal.tsum_mul_left]
        by_cases ha : a ∈ support (fixedCostP g c i)
        · refine mul_le_mul' le_rfl (ih a (fun x hx b' => h x ?_ b') _)
          rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff]
          exact ⟨a, ha, hx⟩
        · rw [probOutput_eq_zero_of_not_mem_support ha]
          simp
      · simp

/-- A continuation comparison on the support of a common program. -/
theorem val_bind_mono {α β : Type} (E : β → Prop)
    (P : OracleComp CostSpec α) (k k' : α → OracleComp CostSpec β)
    (h : ∀ x ∈ support (simulateQ (fixedCostP g c) P), ∀ b', val g c E (k x) b' ≤ val g c E (k' x) b')
    (b : ℕ) : val g c E (P >>= k) b ≤ val g c E (P >>= k') b := by
  have := val_bind_le_avg g c E (fun _ : Unit => (1 : ℝ≥0∞)) P (fun _ => k) k'
    (fun x hx b' => by simpa using h x hx b') b
  simpa using this

/-- A program all of whose outputs lead to a value at most `V0` for every smaller budget. -/
theorem val_bind_le_of {α β : Type} (E : β → Prop)
    (P : OracleComp CostSpec α) (k : α → OracleComp CostSpec β) (V0 : ℝ≥0∞) :
    ∀ b, (∀ x ∈ support (simulateQ (fixedCostP g c) P), ∀ b' ≤ b, val g c E (k x) b' ≤ V0) →
      val g c E (P >>= k) b ≤ V0 := by
  induction P using OracleComp.inductionOn with
  | pure x =>
      intro b h
      simpa using h x (by simp) b le_rfl
  | query_bind i p ih =>
      intro b h
      rw [bind_assoc, val_query_bind]
      split
      · calc
          _ ≤ ∑' a, Pr[= a | fixedCostP g c i] * V0 := by
            refine ENNReal.tsum_le_tsum fun a => ?_
            by_cases ha : a ∈ support (fixedCostP g c i)
            · refine mul_le_mul' le_rfl (ih a _ fun x hx b' hb' => h x ?_ b' (by omega))
              rw [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff]
              exact ⟨a, ha, hx⟩
            · rw [probOutput_eq_zero_of_not_mem_support ha]
              simp
          _ ≤ V0 := by
            rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left bot_le tsum_probOutput_le_one
      · exact bot_le

/-- Lifted private randomness is averaged with its own law. -/
theorem val_liftProb_bind {γ α : Type} (E : α → Prop) (p : ProbComp γ)
    (k : γ → OracleComp CostSpec α) (b : ℕ) :
    val g c E ((liftM p : OracleComp CostSpec γ) >>= k) b = ∑' x, Pr[= x | p] * val g c E (k x) b := by
  induction p using OracleComp.inductionOn with
  | pure x => simp only [liftM_pure, pure_bind, tsum_probOutput_pure_mul]
  | query_bind draw next ih =>
      rw [liftM_bind, bind_assoc]
      change val g c E (liftM (CostSpec.query (.inl (.inl draw))) >>= fun a =>
        (liftM (next a) : OracleComp CostSpec γ) >>= k) b = _
      rw [val_query_bind]
      show (if (0 : ℕ) ≤ b then ∑' a : Fin (draw + 1),
          Pr[= a | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
            val g c E ((liftM (next a) : OracleComp CostSpec γ) >>= k) (b - 0) else 0) = _
      rw [if_pos (Nat.zero_le _), Nat.sub_zero, tsum_probOutput_bind_mul]
      refine tsum_congr fun a => ?_
      rw [ih a]

theorem val_tick_le {α : Type} (E : α → Prop) (amount : ℕ) (k : Unit → OracleComp CostSpec α) (b : ℕ) :
    val g c E (HiddenCost.tick amount >>= k) b ≤ val g c E (k ()) b := by
  rw [HiddenCost.tick, val_query_bind]
  split
  · change ∑' a, Pr[= a | (pure () : ProbComp Unit)] * _ ≤ _
    rw [tsum_probOutput_pure_mul]
    exact val_mono g c E _ _ _ (Nat.sub_le _ _)
  · exact bot_le

/-! ### Averaging uniform tables -/

omit g c in
/-- Splitting one coordinate off a uniform table. -/
theorem tsum_uniform_update {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [Nonempty R]
    [SampleableType R] [SampleableType (D → R)] (i : D) (G : (D → R) → ℝ≥0∞) :
    ∑' table, Pr[= table | ($ᵗ (D → R) : ProbComp (D → R))] * G table =
      ∑' a, Pr[= a | ($ᵗ R : ProbComp R)] * ∑' table, Pr[= table | ($ᵗ (D → R) : ProbComp (D → R))] *
        G (Function.update table i a) := by
  have h := evalDist_uniformSample_bind_update (D := D) (R := R) i
  calc
    _ = ∑' table, Pr[= table | (do
          let u ← ($ᵗ R : ProbComp R)
          let table ← ($ᵗ (D → R) : ProbComp (D → R))
          pure (Function.update table i u))] * G table := by
      refine tsum_congr fun table => ?_
      rw [probOutput_congr rfl h.symm]
    _ = _ := by
      rw [tsum_probOutput_bind_mul]
      refine tsum_congr fun a => ?_
      rw [tsum_probOutput_bind_mul]
      simp only [tsum_probOutput_pure_mul]

omit g c in
theorem tsum_uniform_truncate (F : Randomness → ℝ≥0∞) :
    ∑' a, Pr[= a | ($ᵗ HashOutput : ProbComp HashOutput)] * F (truncateHash a) =
      ∑' r, Pr[= r | ($ᵗ Randomness : ProbComp Randomness)] * F r := by
  rw [← tsum_probOutput_map_mul]
  refine tsum_congr fun r => ?_
  rw [probOutput_congr rfl evalDist_truncateHash_uniform]

omit g c in
theorem tsum_prob_mul_le {ρ : Type} (p : ProbComp ρ) (C : ℝ≥0∞) :
    ∑' x, Pr[= x | p] * C ≤ C := by
  rw [ENNReal.tsum_mul_right]
  exact mul_le_of_le_one_left bot_le tsum_probOutput_le_one

/-! ### One message: a derived randomizer base read once is a fresh uniform start -/

variable [Params]

/-- Averaging the planted base `R0` of one message: the deterministic signer (one tick, then the
scan from the truncated base) wins at most as often as the scan from a uniform start. -/
theorem row_le {α : Type} (E : α → Prop) (parameter : PublicParameter) (data : PublicData)
    (message : Message) (k : Option Signature → OracleComp CostSpec α) (n b : ℕ) :
    ∑' a, Pr[= a | ($ᵗ HashOutput : ProbComp HashOutput)] *
        val g c E ((HiddenCost.tick 1 >>= fun _ =>
          signCostSourceLoop parameter data message n (truncateHash a)) >>= k) b ≤
      val g c E (((liftM ($ᵗ Randomness : ProbComp Randomness) : OracleComp CostSpec Randomness) >>=
        fun start => signCostSourceLoop parameter data message n start) >>= k) b := by
  calc
    _ ≤ ∑' a, Pr[= a | ($ᵗ HashOutput : ProbComp HashOutput)] *
          val g c E (signCostSourceLoop parameter data message n (truncateHash a) >>= k) b := by
      refine ENNReal.tsum_le_tsum fun a => mul_le_mul' le_rfl ?_
      rw [bind_assoc]
      exact val_tick_le g c E 1 _ b
    _ = ∑' r, Pr[= r | ($ᵗ Randomness : ProbComp Randomness)] *
          val g c E (signCostSourceLoop parameter data message n r >>= k) b :=
      tsum_uniform_truncate (fun r => val g c E (signCostSourceLoop parameter data message n r >>= k) b)
    _ = _ := by rw [bind_assoc, val_liftProb_bind]

/-! ### The adversary's interaction as a cost program -/

open Internalize ForsPotential

noncomputable def finishBool (parameter : PublicParameter) (data : PublicData) (L : QueryLog SigningSpec)
    (forgery : Forgery) : OracleComp CostSpec Bool := do
  let verified ← liftM (Concrete.verify (⟨data.root, parameter⟩ : PublicKey) forgery.message
    forgery.signature : OracleComp HashSpec Bool)
  return decide (SigningTranscript.Valid L ∧ ¬SigningTranscript.Contains L forgery) && verified

/-- The rest of the deterministic game from an adversary computation and a log prefix. -/
noncomputable def advDet (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable)
    (M : OracleComp AdvSpec Forgery) (L : QueryLog SigningSpec) : OracleComp CostSpec Bool :=
  (simulateQ (Det.costInteractionDet parameter data rnd) M).run >>= fun r =>
    finishBool parameter data (L ++ r.2) r.1

/-- The rest of the fresh-randomizer game from an adversary computation and a log prefix. -/
noncomputable def advRand (parameter : PublicParameter) (data : PublicData)
    (M : OracleComp AdvSpec Forgery) (L : QueryLog SigningSpec) : OracleComp CostSpec Bool :=
  (simulateQ (costInteraction parameter data) M).run >>= fun r =>
    finishBool parameter data (L ++ r.2) r.1

theorem costRestDet_eq (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable)
    (adversary : Adversary) :
    Det.costRestDet parameter data rnd adversary =
      advDet parameter data rnd (adversary.main ⟨data.root, parameter⟩) [] := by
  unfold Det.costRestDet advDet finishBool
  refine bind_congr fun r => ?_
  rcases r with ⟨forgery, log⟩
  simp only [List.nil_append]

theorem costRest_eq (parameter : PublicParameter) (data : PublicData) (adversary : Adversary) :
    costRest parameter data adversary = advRand parameter data (adversary.main ⟨data.root, parameter⟩) [] := by
  unfold costRest advRand finishBool
  refine bind_congr fun r => ?_
  rcases r with ⟨forgery, log⟩
  simp only [List.nil_append]

theorem advDet_pure (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable)
    (forgery : Forgery) (L : QueryLog SigningSpec) :
    advDet parameter data rnd (pure forgery) L = finishBool parameter data L forgery := by
  unfold advDet
  rw [simulateQ_pure, WriterT.run_pure, pure_bind]
  simp

theorem advRand_pure (parameter : PublicParameter) (data : PublicData)
    (forgery : Forgery) (L : QueryLog SigningSpec) :
    advRand parameter data (pure forgery) L = finishBool parameter data L forgery := by
  unfold advRand
  rw [simulateQ_pure, WriterT.run_pure, pure_bind]
  simp

theorem advDet_world (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable)
    (t : OracleWorld.Domain) (next : OracleWorld.Range t → OracleComp AdvSpec Forgery)
    (L : QueryLog SigningSpec) :
    advDet parameter data rnd (liftM (AdvSpec.query (.inl t)) >>= next) L =
      ordinaryCostSource t >>= fun v => advDet parameter data rnd (next v) L := by
  unfold advDet
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change (((fun v => (v, (∅ : QueryLog SigningSpec))) <$> ordinaryCostSource t) >>= _) >>= _ = _
  simp only [bind_map_left, bind_assoc]
  rfl

theorem advRand_world (parameter : PublicParameter) (data : PublicData)
    (t : OracleWorld.Domain) (next : OracleWorld.Range t → OracleComp AdvSpec Forgery)
    (L : QueryLog SigningSpec) :
    advRand parameter data (liftM (AdvSpec.query (.inl t)) >>= next) L =
      ordinaryCostSource t >>= fun v => advRand parameter data (next v) L := by
  unfold advRand
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change (((fun v => (v, (∅ : QueryLog SigningSpec))) <$> ordinaryCostSource t) >>= _) >>= _ = _
  simp only [bind_map_left, bind_assoc]
  rfl

theorem advDet_sign (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable)
    (message : Message) (next : Option Signature → OracleComp AdvSpec Forgery)
    (L : QueryLog SigningSpec) :
    advDet parameter data rnd (liftM (AdvSpec.query (.inr message)) >>= next) L =
      Det.signCostDet parameter data rnd message >>= fun r =>
        advDet parameter data rnd (next r) (L ++ [⟨message, r⟩]) := by
  unfold advDet
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change ((QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
      (fun message => Det.signCostDet parameter data rnd message) message).run >>= _) >>= _ = _
  rw [QueryImpl.run_withLogging_apply]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun r => ?_
  rw [bind_map_left]
  refine bind_congr fun r' => ?_
  simp only [List.append_assoc]

theorem advRand_sign (parameter : PublicParameter) (data : PublicData)
    (message : Message) (next : Option Signature → OracleComp AdvSpec Forgery)
    (L : QueryLog SigningSpec) :
    advRand parameter data (liftM (AdvSpec.query (.inr message)) >>= next) L =
      signCostSource parameter data message >>= fun r =>
        advRand parameter data (next r) (L ++ [⟨message, r⟩]) := by
  unfold advRand
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change ((QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
      (fun message => signCostSource parameter data message) message).run >>= _) >>= _ = _
  rw [QueryImpl.run_withLogging_apply]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun r => ?_
  rw [bind_map_left]
  refine bind_congr fun r' => ?_
  simp only [List.append_assoc]

/-- A program that never signs a message of `S` reads no randomizer base of `S`. -/
theorem advDet_update (parameter : PublicParameter) (data : PublicData) :
    ∀ (M : OracleComp AdvSpec Forgery) (S : List Message) (L : QueryLog SigningSpec) (rnd : Det.RTable)
      (m : Message) (row : HashOutput), NoRepeat M S → m ∈ S →
      advDet parameter data (Function.update rnd m row) M L = advDet parameter data rnd M L := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery => intro S L rnd m row _ _; rw [advDet_pure, advDet_pure]
  | query_bind t next ih =>
      intro S L rnd m row hnr hm
      rcases t with t | m'
      · rw [advDet_world, advDet_world]
        exact bind_congr fun v => ih v S L rnd m row (hnr v) hm
      · obtain ⟨hnot, hrest⟩ := hnr
        have hne : m' ≠ m := fun heq => hnot (heq ▸ hm)
        rw [advDet_sign, advDet_sign]
        have hsign : Det.signCostDet parameter data (Function.update rnd m row) m' =
            Det.signCostDet parameter data rnd m' := by
          unfold Det.signCostDet
          rw [Function.update_of_ne hne]
        rw [hsign]
        exact bind_congr fun r => ih r (S ++ [m']) _ rnd m row (hrest r) (List.mem_append_left _ hm)

attribute [local irreducible] digestAttemptLimit

noncomputable instance rtableSampleable : SampleableType Det.RTable := SampleableType.ofFintype Det.RTable

/-- **Averaging the derived-randomizer table.** For a program that never repeats a request, the
deterministic game with a uniform randomizer table wins (within budget) at most as often as the
fresh-randomizer game. -/
theorem avg_advDet (E : Bool → Prop) (parameter : PublicParameter) (data : PublicData) :
    ∀ (M : OracleComp AdvSpec Forgery) (S : List Message) (L : QueryLog SigningSpec), NoRepeat M S → ∀ b,
      ∑' rnd, Pr[= rnd | ($ᵗ Det.RTable : ProbComp Det.RTable)] *
          val g c E (advDet parameter data rnd M L) b ≤
        val g c E (advRand parameter data M L) b := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro S L _ b
      simp only [advDet_pure, advRand_pure]
      exact tsum_prob_mul_le _ _
  | query_bind t next ih =>
      intro S L hnr b
      rcases t with t | m
      · simp only [advDet_world, advRand_world]
        exact val_bind_le_avg g c E _ _ _ _ (fun v _ b' => ih v S L (hnr v) b') b
      · obtain ⟨hnot, hrest⟩ := hnr
        simp only [advDet_sign, advRand_sign]
        rw [tsum_uniform_update m]
        have hloc : ∀ (row : HashOutput) (rnd : Det.RTable),
            (Det.signCostDet parameter data (Function.update rnd m row) m >>= fun r =>
              advDet parameter data (Function.update rnd m row) (next r) (L ++ [⟨m, r⟩])) =
            ((HiddenCost.tick 1 >>= fun _ =>
                signCostSourceLoop parameter data m digestAttemptLimit (truncateHash row)) >>= fun r =>
              advDet parameter data rnd (next r) (L ++ [⟨m, r⟩])) := by
          intro row rnd
          unfold Det.signCostDet
          rw [Function.update_self]
          exact bind_congr fun r => advDet_update parameter data (next r) (S ++ [m]) _ rnd m row (hrest r)
            (List.mem_append_right _ (List.mem_singleton_self m))
        simp_rw [hloc]
        calc
          _ ≤ ∑' row, Pr[= row | ($ᵗ HashOutput : ProbComp HashOutput)] *
                val g c E ((HiddenCost.tick 1 >>= fun _ =>
                    signCostSourceLoop parameter data m digestAttemptLimit (truncateHash row)) >>= fun r =>
                  advRand parameter data (next r) (L ++ [⟨m, r⟩])) b := by
            refine ENNReal.tsum_le_tsum fun row => mul_le_mul' le_rfl ?_
            exact val_bind_le_avg g c E _ _ _ _ (fun r _ b' => ih r (S ++ [m]) _ (hrest r) b') b
          _ ≤ _ := by
            rw [signCostSource]
            exact row_le g c E parameter data m _ digestAttemptLimit b

/-! ### The deterministic signer is deterministic on a fixed answer function -/

attribute [local irreducible] ReferenceChoice.search encodingAttemptLimit

omit [Params] in
theorem fixedCostP_liftHash {γ : Type} (oa : OracleComp HashSpec γ) :
    simulateQ (fixedCostP g c) (liftM oa : OracleComp CostSpec γ) = pure (evalWithAnswerFn g oa) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind x next ih =>
      rw [liftM_bind]
      change simulateQ (fixedCostP g c) (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= fun a =>
        (liftM (next a) : OracleComp CostSpec γ)) = _
      rw [simulateQ_bind, simulateQ_spec_query]
      change (pure (g x) : ProbComp HashOutput) >>= _ = _
      rw [pure_bind, ih, evalWithAnswerFn_bind]
      rfl

omit [Params] in
theorem fixedCostP_tick (amount : ℕ) :
    simulateQ (fixedCostP g c) (HiddenCost.tick (D := HashInput) (R := HashOutput)
      (ι := HiddenGraph.Coordinate) amount) = pure () := by
  rw [HiddenCost.tick, simulateQ_spec_query]
  rfl

omit [Params] in
theorem fixedCostP_sequence_reveal {n : ℕ} (which : Fin n → HiddenGraph.Coordinate) :
    simulateQ (fixedCostP g c) (Concrete.sequenceFin fun index =>
      HiddenCost.reveal (D := HashInput) (R := HashOutput) (which index)) =
      pure (fun index => c (which index)) := by
  induction n with
  | zero =>
      simp only [Concrete.sequenceFin, simulateQ_pure]
      congr 1
      funext index
      exact index.elim0
  | succ n ih =>
      simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_pure]
      rw [HiddenCost.reveal, simulateQ_spec_query]
      change (pure (c (which 0)) : ProbComp Digest) >>= _ = _
      rw [pure_bind, ih (fun index => which index.succ), pure_bind]
      congr 1
      funext index
      cases index using Fin.cases <;> rfl

omit [Params] in
theorem fixedCostP_sequenceFin_pure {α : Type} {n : ℕ} (computation : Fin n → OracleComp CostSpec α)
    (h : ∀ i, ∃ x, simulateQ (fixedCostP g c) (computation i) = pure x) :
    ∃ x, simulateQ (fixedCostP g c) (Concrete.sequenceFin computation) = pure x := by
  induction n with
  | zero => exact ⟨_, by simp only [Concrete.sequenceFin, simulateQ_pure]; rfl⟩
  | succ n ih =>
      obtain ⟨x0, h0⟩ := h 0
      obtain ⟨xs, hs⟩ := ih (fun index => computation index.succ) (fun i => h i.succ)
      refine ⟨Fin.cases x0 xs, ?_⟩
      simp only [Concrete.sequenceFin, simulateQ_bind, h0, pure_bind, hs, simulateQ_pure]

omit [Params] in
theorem fixedCostP_reveal (which : HiddenGraph.Coordinate) :
    simulateQ (fixedCostP g c) (HiddenCost.reveal (D := HashInput) (R := HashOutput) which) = pure (c which) := by
  rw [HiddenCost.reveal, simulateQ_spec_query]
  rfl

omit [Params] in
theorem fixedCostP_coord_det (data : PublicData) (index : Index) (marks : Coord → CoordMark) :
    ∃ x, simulateQ (fixedCostP g c) (Concrete.sequenceFin fun coord => coordCostSource data index coord (marks coord)) =
      pure x := by
  apply fixedCostP_sequenceFin_pure
  intro coord
  have hsub : ∃ x, simulateQ (fixedCostP g c) (Concrete.sequenceFin fun j => do
      let cols ← Concrete.sequenceFin fun i => revealChainCost index coord (marks coord) j i
      return (⟨fun i => cols i (openedPos (marks coord) j i),
        data.subPath index coord (marks coord).super j ((marks coord).child j)⟩ : SubOpening)) = pure x := by
    apply fixedCostP_sequenceFin_pure
    intro j
    have hcols : ∃ x, simulateQ (fixedCostP g c)
        (Concrete.sequenceFin fun i => revealChainCost index coord (marks coord) j i) = pure x := by
      apply fixedCostP_sequenceFin_pure
      intro i
      apply fixedCostP_sequenceFin_pure
      intro k
      split
      · exact ⟨_, fixedCostP_reveal g c _⟩
      · exact ⟨_, simulateQ_pure _ _⟩
    obtain ⟨x, hx⟩ := hcols
    exact ⟨_, by rw [simulateQ_bind, hx, pure_bind, simulateQ_pure]⟩
  obtain ⟨x, hx⟩ := hsub
  exact ⟨_, by rw [coordCostSource, simulateQ_bind, hx, pure_bind, simulateQ_pure]⟩

theorem finishCostSource_det (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) :
    ∃ x, simulateQ (fixedCostP g c) (finishCostSource parameter data message randomness) = pure x := by
  simp only [finishCostSource, simulateQ_bind, fixedCostP_liftHash, pure_bind, fixedCostP_tick]
  split
  · rename_i counter word _
    obtain ⟨x, hx⟩ := fixedCostP_coord_det g c data _ _
    rw [simulateQ_bind, fixedCostP_sequence_reveal g c, pure_bind, simulateQ_bind,
      hx, pure_bind, simulateQ_bind, fixedCostP_tick, pure_bind, simulateQ_pure]
    exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem signCostDetLoop_det (parameter : PublicParameter) (data : PublicData)
    (message : Message) : ∀ (n : ℕ) (start : Randomness),
    ∃ x, simulateQ (fixedCostP g c) (signCostSourceLoop parameter data message n start) = pure x := by
  intro n
  induction n with
  | zero => intro start; exact ⟨none, rfl⟩
  | succ n ih =>
      intro start
      simp only [signCostSourceLoop, simulateQ_bind, pure_bind, fixedCostP_liftHash]
      split
      · exact finishCostSource_det g c parameter data message _
      · exact ih (start + 1)

theorem signCostDet_det (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable)
    (message : Message) :
    ∃ x, simulateQ (fixedCostP g c) (Det.signCostDet parameter data rnd message) = pure x := by
  obtain ⟨x, hx⟩ := signCostDetLoop_det g c parameter data message digestAttemptLimit
    (truncateHash (rnd message))
  exact ⟨x, by rw [Det.signCostDet, simulateQ_bind, fixedCostP_tick, pure_bind, hx]⟩

/-! ### Memoizing at the cost level -/

/-- The memo record holds the deterministic signatures, each also in the memo log; both logs
have the same entries and the memo log is no longer. -/
def MemoInv (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable) (record : Memo.Record)
    (L L' : QueryLog SigningSpec) : Prop :=
  (∀ m σ, record m = some σ →
    simulateQ (fixedCostP g c) (Det.signCostDet parameter data rnd m) = pure σ ∧
      (⟨m, σ⟩ : (_ : Message) × Option Signature) ∈ L') ∧
  (∀ e, e ∈ L ↔ e ∈ L') ∧ L'.length ≤ L.length

theorem finishBool_le (parameter : PublicParameter) (data : PublicData) (L L' : QueryLog SigningSpec)
    (forgery : Forgery) (hmem : ∀ e, e ∈ L ↔ e ∈ L') (hlen : L'.length ≤ L.length) (b : ℕ) :
    val g c (· = true) (finishBool parameter data L forgery) b ≤
      val g c (· = true) (finishBool parameter data L' forgery) b := by
  unfold finishBool
  refine val_bind_mono g c _ _ _ _ (fun v _ b' => ?_) b
  rw [val_pure, val_pure]
  by_cases h : (decide (SigningTranscript.Valid L ∧ ¬SigningTranscript.Contains L forgery) && v) = true
  · have h' : (decide (SigningTranscript.Valid L' ∧ ¬SigningTranscript.Contains L' forgery) && v) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
      obtain ⟨⟨hvalid, hcontains⟩, hv⟩ := h
      refine ⟨⟨le_trans hlen hvalid, fun ⟨entry, hentry, heq⟩ => hcontains ⟨entry, (hmem entry).2 hentry, heq⟩⟩, hv⟩
    rw [if_pos h, if_pos h']
  · rw [if_neg h]
    exact bot_le

open Memo in
theorem memo_le (parameter : PublicParameter) (data : PublicData) (rnd : Det.RTable) :
    ∀ (M : OracleComp AdvSpec Forgery) (record : Record) (L L' : QueryLog SigningSpec),
      MemoInv g c parameter data rnd record L L' → ∀ b,
        val g c (· = true) (advDet parameter data rnd M L) b ≤
          val g c (· = true) (advDet parameter data rnd (Prod.fst <$> (simulateQ memoImpl M).run record) L') b := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro record L L' hinv b
      simp only [simulateQ_pure, StateT.run_pure, map_pure, advDet_pure]
      exact finishBool_le g c parameter data L L' forgery hinv.2.1 hinv.2.2 b
  | query_bind t next ih =>
      intro record L L' hinv b
      rw [memo_run_query_bind]
      rcases t with t | m
      · rw [memoImpl_world, bind_map_left, map_bind, advDet_world, advDet_world]
        exact val_bind_mono g c _ _ _ _ (fun v _ b' => ih v record L L' hinv b') b
      · cases hm : record m with
        | some σ =>
            rw [memoImpl_sign_some m record σ hm, pure_bind, advDet_sign]
            obtain ⟨hdet, hmemσ⟩ := hinv.1 m σ hm
            refine val_bind_le_of g c _ _ _ _ b fun x hx b' hb' => ?_
            rw [hdet, support_pure, Set.mem_singleton_iff] at hx
            subst hx
            refine le_trans (val_mono g c _ _ _ _ hb') (ih x record _ L' ⟨hinv.1, fun e => ?_, ?_⟩ b)
            · rw [List.mem_append, List.mem_singleton, hinv.2.1 e]
              constructor
              · rintro (h | rfl)
                · exact h
                · exact hmemσ
              · exact Or.inl
            · rw [List.length_append]
              exact le_trans hinv.2.2 (Nat.le_add_right _ _)
        | none =>
            rw [memoImpl_sign_none m record hm, bind_map_left, map_bind, advDet_sign, advDet_sign]
            obtain ⟨x0, hdet⟩ := signCostDet_det g c parameter data rnd m
            refine val_bind_mono g c _ _ _ _ (fun x hx b' => ?_) b
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
    val g c (· = true) (Det.costGameDet parameter data rnd adversary) b ≤
      val g c (· = true) (Det.costGameDet parameter data rnd (Memo.memoAdv adversary)) b := by
  unfold Det.costGameDet
  refine val_bind_mono g c _ _ _ _ (fun _ _ b' => ?_) b
  rw [costRestDet_eq, costRestDet_eq]
  change _ ≤ val g c (· = true) (advDet parameter data rnd
    ((simulateQ Memo.memoImpl (adversary.main ⟨data.root, parameter⟩)).run' Memo.emptyRecord) []) b'
  rw [StateT.run'_eq]
  exact memo_le g c parameter data rnd _ Memo.emptyRecord [] []
    ⟨fun m σ h => by simp [Memo.emptyRecord] at h, fun e => Iff.rfl, le_rfl⟩ b'

theorem avg_game (parameter : PublicParameter) (data : PublicData) (adversary : Adversary)
    (hnr : adversary.NoRepeat) (b : ℕ) :
    ∑' rnd, Pr[= rnd | ($ᵗ Det.RTable : ProbComp Det.RTable)] *
        val g c (· = true) (Det.costGameDet parameter data rnd adversary) b ≤
      val g c (· = true) (costGame parameter data adversary) b := by
  unfold Det.costGameDet costGame
  refine val_bind_le_avg g c _ _ _ _ _ (fun _ _ b' => ?_) b
  simp only [costRestDet_eq, costRest_eq]
  exact avg_advDet g c _ parameter data _ [] [] (hnr _) b'

/-- **Deterministic randomizers, memoized and averaged.** With a uniform randomizer table, the
deterministic game of any adversary wins (within budget) at most as often as the fresh-randomizer
game of its memoizing version. -/
theorem win_avg_le (parameter : PublicParameter) (data : PublicData) (adversary : Adversary)
    (hnr : (Memo.memoAdv adversary).NoRepeat) (b : ℕ) :
    Pr[Reduce.Win | do
        let rnd ← ($ᵗ Det.RTable : ProbComp Det.RTable)
        costRun g c (cap (Det.costGameDet parameter data rnd adversary) b)] ≤
      Pr[Reduce.Win | costRun g c (cap (costGame parameter data (Memo.memoAdv adversary)) b)] := by
  rw [probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' rnd, Pr[= rnd | ($ᵗ Det.RTable : ProbComp Det.RTable)] *
          val g c (· = true) (Det.costGameDet parameter data rnd (Memo.memoAdv adversary)) b :=
      ENNReal.tsum_le_tsum fun rnd => mul_le_mul' le_rfl (memo_game_le g c parameter data rnd adversary b)
    _ ≤ _ := avg_game g c parameter data _ hnr b

end Sphincs.Security.DetValue
