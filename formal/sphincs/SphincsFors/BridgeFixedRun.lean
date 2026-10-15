import SphincsFors.BridgeEncodingPrep
import SphincsFors.SecurityHiddenOutside
import SphincsFors.SecurityHiddenCost
import SphincsFors.SecuritySeedGuess
import SphincsFors.SecurityHiddenGraph

/-! Support facts for fixed-function runs of the rich graph-view program: decomposition over
binds, hash-only and private-only phases, and reveals. -/

open OracleComp OracleSpec ENNReal

namespace SphincsFors.Security.HiddenBridge

open HiddenCost GraphView Stop Concrete Prefix

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

section Fixed

variable (f : HashInput → HashOutput) (table : HiddenGraph.Table)

abbrev RunResult (α : Type) := (α × List HiddenGraph.Coordinate) × List (Entry HashInput)

theorem costRun_withReveals_pure {α : Type} (value : α) :
    costRun f table (withReveals (pure value : OracleComp CostSpec α)) = pure ((value, []), []) := by
  rw [withReveals_pure, costRun_pure]

theorem costRun_withReveals_query_bind {α : Type} (input : CostSpec.Domain)
    (next : CostSpec.Range input → OracleComp CostSpec α) :
    costRun f table (withReveals (liftM (CostSpec.query input) >>= next)) =
      fixedCostP f table input >>= fun answer =>
        (fun result => ((result.1.1, revealed input ++ result.1.2), recorded input ++ result.2)) <$>
          costRun f table (withReveals (next answer)) := by
  rw [withReveals_query_bind', costRun_query_bind]
  congr 1
  funext answer
  rw [costRun_map, Functor.map_map]

/-- Support of a bind splits into the supports of its two phases. -/
theorem costRun_withReveals_bind {α β : Type} (x : OracleComp CostSpec α)
    (k : α → OracleComp CostSpec β) (result : RunResult β)
    (hresult : result ∈ support (costRun f table (withReveals (x >>= k)))) :
    ∃ first ∈ support (costRun f table (withReveals x)),
      ∃ second ∈ support (costRun f table (withReveals (k first.1.1))),
        result = ((second.1.1, first.1.2 ++ second.1.2), first.2 ++ second.2) := by
  induction x using OracleComp.inductionOn generalizing result with
  | pure value =>
      refine ⟨((value, []), []), by rw [costRun_withReveals_pure]; simp, result, ?_, by simp⟩
      simpa only [pure_bind] using hresult
  | query_bind input next ih =>
      rw [bind_assoc, costRun_withReveals_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨answer, hanswer, hresult⟩ := hresult
      rw [support_map] at hresult
      obtain ⟨inner, hinner, rfl⟩ := hresult
      obtain ⟨first, hfirst, second, hsecond, rfl⟩ := ih answer inner hinner
      refine ⟨((first.1.1, revealed input ++ first.1.2), recorded input ++ first.2), ?_, second, hsecond, ?_⟩
      · rw [costRun_withReveals_query_bind, mem_support_bind_iff]
        exact ⟨answer, hanswer, by rw [support_map]; exact ⟨first, hfirst, rfl⟩⟩
      · simp only [List.append_assoc]

theorem costRun_withReveals_map {α β : Type} (g : α → β) (x : OracleComp CostSpec α)
    (result : RunResult β) (hresult : result ∈ support (costRun f table (withReveals (g <$> x)))) :
    ∃ inner ∈ support (costRun f table (withReveals x)),
      result = ((g inner.1.1, inner.1.2), inner.2) := by
  rw [map_eq_bind_pure_comp] at hresult
  obtain ⟨first, hfirst, second, hsecond, rfl⟩ := costRun_withReveals_bind f table x _ result hresult
  refine ⟨first, hfirst, ?_⟩
  rw [Function.comp_apply, costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hsecond
  subst second
  simp

/-- A lifted hash computation evaluates with the fixed function, reveals nothing and records
exactly its queried inputs. -/
theorem costRun_withReveals_liftHash {α : Type} (oa : OracleComp HashSpec α) (result : RunResult α)
    (hresult : result ∈ support (costRun f table (withReveals (liftM oa : OracleComp CostSpec α)))) :
    result = ((evalWithAnswerFn f oa, []), (queriedInputs f oa).map Sum.inl) := by
  induction oa using OracleComp.inductionOn generalizing result with
  | pure value =>
      rw [liftM_pure, costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hresult
      rw [hresult]
      simp
  | query_bind input next ih =>
      rw [liftM_bind] at hresult
      change result ∈ support (costRun f table (withReveals
        (liftM (CostSpec.query (.inl (.inr (.inl input)))) >>= fun answer =>
          (liftM (next answer) : OracleComp CostSpec α)))) at hresult
      rw [costRun_withReveals_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨answer, hanswer, hresult⟩ := hresult
      have hanswer' : answer = f input := by
        simpa [fixedCostP] using hanswer
      subst answer
      rw [support_map] at hresult
      obtain ⟨inner, hinner, rfl⟩ := hresult
      rw [ih _ inner hinner]
      simp only [revealed, recorded, queriedInputs_query_bind, List.nil_append, List.map_cons,
        List.singleton_append]
      rfl

/-- A lifted private computation reveals and records nothing. -/
theorem costRun_withReveals_liftProb {α : Type} (oa : ProbComp α) (result : RunResult α)
    (hresult : result ∈ support (costRun f table (withReveals (liftM oa : OracleComp CostSpec α)))) :
    result.1.2 = [] ∧ result.2 = [] := by
  induction oa using OracleComp.inductionOn generalizing result with
  | pure value =>
      rw [liftM_pure, costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hresult
      rw [hresult]
      simp
  | query_bind input next ih =>
      rw [liftM_bind] at hresult
      change result ∈ support (costRun f table (withReveals
        (liftM (CostSpec.query (.inl (.inl input))) >>= fun answer =>
          (liftM (next answer) : OracleComp CostSpec α)))) at hresult
      rw [costRun_withReveals_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      rw [support_map] at hresult
      obtain ⟨inner, hinner, rfl⟩ := hresult
      obtain ⟨h1, h2⟩ := ih answer inner hinner
      simp [revealed, recorded, h1, h2]

theorem costRun_withReveals_tick (amount : Nat) (result : RunResult Unit)
    (hresult : result ∈ support (costRun f table (withReveals
      (HiddenCost.tick (D := HashInput) (R := HashOutput) (ι := HiddenGraph.Coordinate) amount)))) :
    result = (((), []), [.inr amount]) := by
  have h : HiddenCost.tick (D := HashInput) (R := HashOutput) (ι := HiddenGraph.Coordinate) amount =
      liftM (CostSpec.query (.inr amount)) >>= fun value => pure value := by
    rw [bind_pure]
    rfl
  rw [h, costRun_withReveals_query_bind, mem_support_bind_iff] at hresult
  obtain ⟨answer, _, hresult⟩ := hresult
  rw [costRun_withReveals_pure, map_pure, support_pure, Set.mem_singleton_iff] at hresult
  rw [hresult]
  rfl

theorem costRun_withReveals_reveal (coordinate : HiddenGraph.Coordinate) (result : RunResult Digest)
    (hresult : result ∈ support (costRun f table (withReveals
      (HiddenCost.reveal (D := HashInput) (R := HashOutput) coordinate)))) :
    result = ((table coordinate, [coordinate]), []) := by
  have h : HiddenCost.reveal (D := HashInput) (R := HashOutput) coordinate =
      liftM (CostSpec.query (.inl (.inr (.inr coordinate)))) >>= fun value => pure value := by
    rw [bind_pure]
    rfl
  rw [h, costRun_withReveals_query_bind, mem_support_bind_iff] at hresult
  obtain ⟨answer, hanswer, hresult⟩ := hresult
  have hanswer' : answer = table coordinate := by simpa [fixedCostP] using hanswer
  subst answer
  rw [costRun_withReveals_pure, map_pure, support_pure, Set.mem_singleton_iff] at hresult
  rw [hresult]
  rfl

/-- A completed capped run is a run of the uncapped program. -/
theorem costRun_withReveals_cap {α : Type} (computation : OracleComp CostSpec α) (budget : Nat)
    (value : α) (reveals : List HiddenGraph.Coordinate) (entries : List (Entry HashInput))
    (hresult : ((some value, reveals), entries) ∈
      support (costRun f table (withReveals (cap computation budget)))) :
    ((value, reveals), entries) ∈ support (costRun f table (withReveals computation)) := by
  induction computation using OracleComp.inductionOn generalizing budget reveals entries with
  | pure result =>
      change ((some value, reveals), entries) ∈ support
        (costRun f table (withReveals (pure (some result) : OracleComp CostSpec _))) at hresult
      rw [costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hresult
      simp only [Prod.mk.injEq, Option.some.injEq] at hresult
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hresult
      rw [costRun_withReveals_pure]
      simp
  | query_bind input next ih =>
      rw [cap_query_bind_gen] at hresult
      split at hresult
      · rw [costRun_withReveals_query_bind, mem_support_bind_iff] at hresult
        obtain ⟨answer, hanswer, hresult⟩ := hresult
        rw [support_map] at hresult
        obtain ⟨⟨⟨inner, innerReveals⟩, innerEntries⟩, hinner, heq⟩ := hresult
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        rw [costRun_withReveals_query_bind, mem_support_bind_iff]
        refine ⟨answer, hanswer, ?_⟩
        rw [support_map]
        exact ⟨_, ih answer _ _ _ hinner, rfl⟩
      · rw [costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hresult
        simp at hresult

theorem costRun_withReveals_sequenceReveal {n : Nat} (which : Fin n → HiddenGraph.Coordinate)
    (result : RunResult (Fin n → Digest))
    (hresult : result ∈ support (costRun f table (withReveals
      (Concrete.sequenceFin fun index => HiddenCost.reveal (D := HashInput) (R := HashOutput) (which index))))) :
    result = (((fun index => table (which index)), List.ofFn which), []) := by
  induction n with
  | zero =>
      rw [Concrete.sequenceFin, costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hresult
      rw [hresult]
      congr 2
      · funext index
        exact index.elim0
  | succ n ih =>
      rw [Concrete.sequenceFin] at hresult
      obtain ⟨first, hfirst, second, hsecond, rfl⟩ := costRun_withReveals_bind f table _ _ result hresult
      rw [costRun_withReveals_reveal f table _ first hfirst] at hsecond ⊢
      obtain ⟨third, hthird, fourth, hfourth, rfl⟩ := costRun_withReveals_bind f table _ _ second hsecond
      rw [ih (fun index => which index.succ) third hthird] at hfourth ⊢
      rw [costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hfourth
      subst fourth
      simp only [List.ofFn_succ, List.append_nil, List.singleton_append]
      congr 2
      funext index
      cases index using Fin.cases <;> rfl

variable [Params]

/-- The coordinates the signer reveals for a randomizer under a fixed function. -/
noncomputable def revealsOf (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) : List HiddenGraph.Coordinate :=
  let digest := evalWithAnswerFn f (messageDigest parameter data.root message randomness :
    OracleComp HashSpec MessageDigest)
  let index := digestIndex digest
  match firstEncoding f parameter topLayer rootTree index (data.forsKey index) encodingAttemptLimit 0 with
  | none => []
  | some pair => List.ofFn (fun chain => HiddenGraph.Coordinate.chain topLayer rootTree index chain (pair.2 chain)) ++
      List.ofFn (fun tree => HiddenGraph.Coordinate.ftsSecret index tree (digestLeaves digest tree))

attribute [local irreducible] ReferenceChoice.search encodingAttemptLimit Concrete.messageDigest
  Concrete.sequenceFin

theorem finish_support (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) (result : RunResult (Option Signature))
    (hresult : result ∈ support (costRun f table (withReveals
      (finishCostSource parameter data message randomness)))) :
    result.1.1 = assembled f parameter data table message randomness ∧
      result.1.2 = revealsOf f parameter data message randomness := by
  unfold finishCostSource at hresult
  obtain ⟨r1, h1, r2, h2, rfl⟩ := costRun_withReveals_bind f table _ _ result hresult
  obtain rfl := costRun_withReveals_liftHash f table _ r1 h1
  obtain ⟨r3, h3, r4, h4, rfl⟩ := costRun_withReveals_bind f table _ _ r2 h2
  obtain rfl := costRun_withReveals_tick f table _ r3 h3
  obtain ⟨r5, h5, r6, h6, rfl⟩ := costRun_withReveals_bind f table _ _ r4 h4
  obtain rfl := costRun_withReveals_liftHash f table _ r5 h5
  dsimp only at h6 ⊢
  simp only [ReferenceChoice.eval_search] at h6
  unfold assembled revealsOf
  cases hfound : firstEncoding f parameter topLayer rootTree
      (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest)))
      (data.forsKey (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest)))) encodingAttemptLimit 0 with
  | none =>
      rw [hfound] at h6
      rw [costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at h6
      subst r6
      constructor <;> dsimp only <;> rw [hfound] <;> rfl
  | some pair =>
      obtain ⟨counter, word⟩ := pair
      simp only [hfound] at h6
      obtain ⟨r7, h7, r8, h8, rfl⟩ := costRun_withReveals_bind f table _ _ r6 h6
      obtain rfl := costRun_withReveals_sequenceReveal f table _ r7 h7
      obtain ⟨r9, h9, r10, h10, rfl⟩ := costRun_withReveals_bind f table _ _ r8 h8
      obtain rfl := costRun_withReveals_sequenceReveal f table _ r9 h9
      obtain ⟨r11, h11, r12, h12, rfl⟩ := costRun_withReveals_bind f table _ _ r10 h10
      obtain rfl := costRun_withReveals_tick f table _ r11 h11
      rw [costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at h12
      subst r12
      constructor
      · dsimp only
        rw [hfound]
        rfl
      · dsimp only
        rw [hfound]
        simp only [List.nil_append, List.append_nil]

/-- The signer's outcome: either nothing revealed and no signature, or an honest landed
assembly whose reveals are exactly its own coordinates. -/
def SignOutcome (parameter : PublicParameter) (seed : MasterSeed) (data : PublicData)
    (message : Message) (result : Option Signature × List HiddenGraph.Coordinate) : Prop :=
  (result.1 = none → result.2 = []) ∧
  ∀ signature, result.1 = some signature → ∃ randomness,
    Landed parameter (digestIndex (Completeness.digestValue f ⟨seed, parameter, data.root⟩ message randomness)) ∧
    evalWithAnswerFn f (Randomized.finishSign ⟨seed, parameter, data.root⟩ message randomness) =
      some signature ∧
    result.2 = revealsOf f parameter data message randomness

omit [Params] in
theorem revealsOf_of_assembled_none (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) (h : assembled f parameter data table message randomness = none) :
    revealsOf f parameter data message randomness = [] := by
  unfold assembled at h
  unfold revealsOf
  dsimp only at h ⊢
  cases hfound : firstEncoding f parameter topLayer rootTree
      (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest)))
      (data.forsKey (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest)))) encodingAttemptLimit 0 with
  | none => rfl
  | some pair => rw [hfound] at h; cases h

theorem signWalk_support (parameter : PublicParameter) (seed : MasterSeed) (data : PublicData)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (message : Message) (attempts : Nat) (randomness : Randomness) (result : RunResult (Option Signature))
    (hresult : result ∈ support (costRun f table (withReveals
      (signCostSourceWalk parameter data message attempts randomness)))) :
    SignOutcome f parameter seed data message result.1 := by
  induction attempts generalizing result randomness with
  | zero =>
      rw [signCostSourceWalk, costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨fun _ => rfl, fun _ h => by cases h⟩
  | succ attempts ih =>
      rw [signCostSourceWalk] at hresult
      obtain ⟨r3, h3, r4, h4, rfl⟩ := costRun_withReveals_bind f table _ _ result hresult
      obtain rfl := costRun_withReveals_liftHash f table _ r3 h3
      dsimp only at h4 ⊢
      rw [List.nil_append]
      split at h4
      · rename_i hland
        have hland' : Landed parameter (digestIndex (Completeness.digestValue f
            ⟨seed, parameter, data.root⟩ message randomness)) := by
          simpa only [Completeness.digestValue, messageDigest, evalWithAnswerFn_bind,
            evalWithAnswerFn_pure, Completeness.digestIndex_truncate] using hland
        obtain ⟨hvalue, hreveals⟩ := finish_support f table parameter data message randomness r4 h4
        have hsign := eval_finishSign_assembled f parameter seed data table hdata htable message randomness hland'
        refine ⟨fun hnone => ?_, fun signature hsome => ⟨randomness, hland', ?_, hreveals⟩⟩
        · rw [hreveals]
          exact revealsOf_of_assembled_none f table parameter data message _ (hvalue ▸ hnone)
        · rw [hsign, ← hvalue, hsome]
      · exact ih (randomness + 1) r4 h4

theorem signLoop_support (parameter : PublicParameter) (seed : MasterSeed) (data : PublicData)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (message : Message) (attempts : Nat) (result : RunResult (Option Signature))
    (hresult : result ∈ support (costRun f table (withReveals
      (signCostSourceLoop parameter data message attempts)))) :
    SignOutcome f parameter seed data message result.1 := by
  rw [signCostSourceLoop] at hresult
  obtain ⟨r1, h1, r2, h2, rfl⟩ := costRun_withReveals_bind f table _ _ result hresult
  obtain ⟨hr1, -⟩ := costRun_withReveals_liftProb f table _ r1 h1
  dsimp only
  rw [hr1, List.nil_append]
  exact signWalk_support f table parameter seed data hdata htable message attempts r1.1.1 r2 h2

theorem sign_support (parameter : PublicParameter) (seed : MasterSeed) (data : PublicData)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (message : Message) (result : RunResult (Option Signature))
    (hresult : result ∈ support (costRun f table (withReveals (signCostSource parameter data message)))) :
    SignOutcome f parameter seed data message result.1 :=
  signLoop_support f table parameter seed data hdata htable message _ result hresult

/-- Every logged signature is an honest landed assembly, and every revealed coordinate is
revealed by some logged signature. -/
def LogGood (parameter : PublicParameter) (seed : MasterSeed) (data : PublicData)
    (log : QueryLog SigningSpec) (reveals : List HiddenGraph.Coordinate) : Prop :=
  (∀ entry ∈ log, ∀ signature, entry.2 = some signature → ∃ randomness,
    Landed parameter (digestIndex (Completeness.digestValue f ⟨seed, parameter, data.root⟩ entry.1 randomness)) ∧
    evalWithAnswerFn f (Randomized.finishSign ⟨seed, parameter, data.root⟩ entry.1 randomness) =
      some signature) ∧
  ∀ coordinate ∈ reveals, ∃ entry ∈ log, ∃ signature, entry.2 = some signature ∧
    coordinate ∈ revealsOf f parameter data entry.1 signature.randomness

theorem logGood_append (parameter : PublicParameter) (seed : MasterSeed) (data : PublicData)
    {log log' : QueryLog SigningSpec} {reveals reveals' : List HiddenGraph.Coordinate}
    (h : LogGood f parameter seed data log reveals) (h' : LogGood f parameter seed data log' reveals') :
    LogGood f parameter seed data (log ++ log') (reveals ++ reveals') := by
  refine ⟨fun entry hentry => ?_, fun coordinate hcoordinate => ?_⟩
  · rcases List.mem_append.mp hentry with hl | hr
    · exact h.1 entry hl
    · exact h'.1 entry hr
  · rcases List.mem_append.mp hcoordinate with hl | hr
    · obtain ⟨entry, hentry, rest⟩ := h.2 coordinate hl
      exact ⟨entry, List.mem_append_left _ hentry, rest⟩
    · obtain ⟨entry, hentry, rest⟩ := h'.2 coordinate hr
      exact ⟨entry, List.mem_append_right _ hentry, rest⟩

omit [Params] in
theorem costRun_withReveals_plainQuery (input : CostSpec.Domain)
    (hreveal : ∀ coordinate, input ≠ .inl (.inr (.inr coordinate)))
    (result : RunResult (CostSpec.Range input))
    (hresult : result ∈ support (costRun f table (withReveals (liftM (CostSpec.query input) :
      OracleComp CostSpec (CostSpec.Range input))))) :
    result.1.2 = [] := by
  have h : (liftM (CostSpec.query input) : OracleComp CostSpec (CostSpec.Range input)) =
      liftM (CostSpec.query input) >>= fun value => pure value := by rw [bind_pure]
  rw [h, costRun_withReveals_query_bind, mem_support_bind_iff] at hresult
  obtain ⟨answer, _, hresult⟩ := hresult
  rw [costRun_withReveals_pure, map_pure, support_pure, Set.mem_singleton_iff] at hresult
  subst result
  rcases input with (draw | (bytes | coordinate)) | amount
  · rfl
  · rfl
  · exact (hreveal coordinate rfl).elim
  · rfl

theorem interaction_support (parameter : PublicParameter) (seed : MasterSeed) (data : PublicData)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    {β : Type} (M : OracleComp Internalize.AdvSpec β)
    (result : RunResult (β × QueryLog SigningSpec))
    (hresult : result ∈ support (costRun f table (withReveals
      (simulateQ (costInteraction parameter data) M).run))) :
    LogGood f parameter seed data result.1.1.2 result.1.2 := by
  induction M using OracleComp.inductionOn generalizing result with
  | pure value =>
      change result ∈ support (costRun f table (withReveals
        (pure (value, (∅ : QueryLog SigningSpec)) : OracleComp CostSpec _))) at hresult
      rw [costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨fun entry h => by simp at h, fun coordinate h => by simp at h⟩
  | query_bind input next ih =>
      rw [simulateQ_bind, WriterT.run_bind] at hresult
      obtain ⟨first, hfirst, second, hsecond, rfl⟩ := costRun_withReveals_bind f table _ _ result hresult
      obtain ⟨inner, hinner, rfl⟩ := costRun_withReveals_map f table _ _ second hsecond
      have hrest := ih first.1.1.1 inner hinner
      refine logGood_append f parameter seed data ?_ hrest
      rw [simulateQ_spec_query] at hfirst
      rcases input with (draw | bytes) | message
      · change first ∈ support (costRun f table (withReveals
          (liftM (liftM (CostSpec.query (.inl (.inl draw))) : OracleComp CostSpec _) :
            WriterT (QueryLog SigningSpec) (OracleComp CostSpec) _).run)) at hfirst
        rw [WriterT.run_liftM] at hfirst
        obtain ⟨query, hquery, rfl⟩ := costRun_withReveals_map f table _ _ first hfirst
        have := costRun_withReveals_plainQuery f table _ (fun _ h => by cases h) query hquery
        refine ⟨fun entry h => by simp at h, fun coordinate h => ?_⟩
        simp [this] at h
      · change first ∈ support (costRun f table (withReveals
          (liftM (liftM (CostSpec.query (.inl (.inr (.inl bytes)))) : OracleComp CostSpec _) :
            WriterT (QueryLog SigningSpec) (OracleComp CostSpec) _).run)) at hfirst
        rw [WriterT.run_liftM] at hfirst
        obtain ⟨query, hquery, rfl⟩ := costRun_withReveals_map f table _ _ first hfirst
        have := costRun_withReveals_plainQuery f table _ (fun _ h => by cases h) query hquery
        refine ⟨fun entry h => by simp at h, fun coordinate h => ?_⟩
        simp [this] at h
      · change first ∈ support (costRun f table (withReveals
          ((QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
            (fun message => signCostSource parameter data message)) message).run)) at hfirst
        rw [QueryImpl.run_withLogging_apply] at hfirst
        obtain ⟨signed, hsigned, final, hfinal, rfl⟩ := costRun_withReveals_bind f table _ _ first hfirst
        rw [costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hfinal
        subst final
        obtain ⟨hnone, hsome⟩ := sign_support f table parameter seed data hdata htable message signed hsigned
        refine ⟨fun entry hentry signature hsig => ?_, fun coordinate hcoordinate => ?_⟩
        · simp only [List.mem_singleton] at hentry
          subst hentry
          obtain ⟨randomness, hland, hfinish, -⟩ := hsome signature hsig
          exact ⟨randomness, hland, hfinish⟩
        · simp only [List.append_nil] at hcoordinate
          cases hvalue : signed.1.1 with
          | none => rw [hnone hvalue] at hcoordinate; cases hcoordinate
          | some signature =>
              obtain ⟨randomness, _, hfinish, hreveals⟩ := hsome signature hvalue
              have hrandomness := SignatureWitness.finishSign_randomness f _ message randomness signature hfinish
              refine ⟨⟨message, some signature⟩, by simp, signature, rfl, ?_⟩
              rw [hrandomness, ← hreveals]
              simpa [hvalue] using hcoordinate

/-- Support of a completed fixed-function run of the rich program. -/
theorem rich_support (adversary : Adversary) (q : Nat) (parameter : PublicParameter)
    (seed : MasterSeed) (data : PublicData)
    (hdata : DataCorrect f parameter seed data) (htable : CoordinatesCorrect f parameter seed table)
    (outcome : Outcome) (reveals : List HiddenGraph.Coordinate) (entries : List (Entry HashInput))
    (hresult : ((some outcome, reveals), entries) ∈
      support (costRun f table (richProgram adversary q parameter data))) :
    outcome.2.2 = evalWithAnswerFn f (Concrete.verify ⟨data.root, parameter⟩ outcome.1.message
      outcome.1.signature : OracleComp HashSpec Bool) ∧
    (∀ input ∈ queriedInputs f (Concrete.verify ⟨data.root, parameter⟩ outcome.1.message
      outcome.1.signature : OracleComp HashSpec Bool), Sum.inl input ∈ entries) ∧
    LogGood f parameter seed data outcome.2.1 reveals := by
  have h := costRun_withReveals_cap f table _ q outcome reveals entries hresult
  unfold costGameX costRestX at h
  obtain ⟨r1, h1, r2, h2, heq⟩ := costRun_withReveals_bind f table _ _ _ h
  obtain rfl := costRun_withReveals_tick f table _ r1 h1
  obtain ⟨r3, h3, r4, h4, rfl⟩ := costRun_withReveals_bind f table _ _ r2 h2
  have hgood := interaction_support f table parameter seed data hdata htable _ r3 h3
  obtain ⟨⟨⟨forgery, log⟩, interactionReveals⟩, interactionEntries⟩ := r3
  dsimp only at h4 hgood
  obtain ⟨r5, h5, r6, h6, rfl⟩ := costRun_withReveals_bind f table _ _ r4 h4
  obtain rfl := costRun_withReveals_liftHash f table _ r5 h5
  rw [costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at h6
  subst r6
  simp only [Prod.mk.injEq] at heq
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
  refine ⟨rfl, fun input hinput => ?_, ?_⟩
  · simp [hinput]
  · simpa using hgood

end Fixed

end SphincsFors.Security.HiddenBridge
