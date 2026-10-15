import Sphincs.BridgeFixedRun

/-! Signed entries reveal their own coordinates. In every fixed-function run of the rich program,
each logged signature's leaf search succeeded, and the coordinates the signer reveals for the
signature's randomizer are in the run's reveal list. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.HiddenBridge

open HiddenCost GraphView Stop Concrete Prefix

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

section Fixed

variable (f : HashInput → HashOutput) (table : HiddenGraph.Table)

/-- Every logged signature's leaf search succeeded, and the coordinates revealed for its
randomizer are in the reveal list. -/
def SignedRevealed (parameter : PublicParameter) (data : PublicData) (log : QueryLog SigningSpec)
    (reveals : List HiddenGraph.Coordinate) : Prop :=
  ∀ entry ∈ log, ∀ signature, entry.2 = some signature →
    (∃ pair, firstEncoding f parameter topLayer rootTree
      (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root entry.1 signature.randomness :
        OracleComp HashSpec MessageDigest)))
      (data.forestKey (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root entry.1
        signature.randomness : OracleComp HashSpec MessageDigest)))) encodingAttemptLimit 0 = some pair) ∧
    ∀ coordinate ∈ revealsOf f parameter data entry.1 signature.randomness, coordinate ∈ reveals

omit [Params] in
theorem signedRevealed_append (parameter : PublicParameter) (data : PublicData)
    {log log' : QueryLog SigningSpec} {reveals reveals' : List HiddenGraph.Coordinate}
    (h : SignedRevealed f parameter data log reveals) (h' : SignedRevealed f parameter data log' reveals') :
    SignedRevealed f parameter data (log ++ log') (reveals ++ reveals') := by
  intro entry hentry signature hsig
  rcases List.mem_append.mp hentry with hl | hr
  · obtain ⟨hpair, hsub⟩ := h entry hl signature hsig
    exact ⟨hpair, fun coordinate hc => List.mem_append_left _ (hsub coordinate hc)⟩
  · obtain ⟨hpair, hsub⟩ := h' entry hr signature hsig
    exact ⟨hpair, fun coordinate hc => List.mem_append_right _ (hsub coordinate hc)⟩

omit [Params] in
/-- An assembled signature carries its randomizer, and its leaf search succeeded. -/
theorem assembled_some (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) (signature : Signature)
    (h : assembled f parameter data table message randomness = some signature) :
    signature.randomness = randomness ∧
      ∃ pair, firstEncoding f parameter topLayer rootTree
        (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
          OracleComp HashSpec MessageDigest)))
        (data.forestKey (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message
          randomness : OracleComp HashSpec MessageDigest)))) encodingAttemptLimit 0 = some pair := by
  unfold assembled at h
  dsimp only at h
  cases hfound : firstEncoding f parameter topLayer rootTree
      (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest)))
      (data.forestKey (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message randomness :
        OracleComp HashSpec MessageDigest)))) encodingAttemptLimit 0 with
  | none => rw [hfound] at h; cases h
  | some pair =>
      rw [hfound, Option.map_some, Option.some.injEq] at h
      subst h
      exact ⟨rfl, pair, rfl⟩

attribute [local irreducible] ReferenceChoice.search encodingAttemptLimit Concrete.messageDigest
  Concrete.sequenceFin

/-- A signing loop that returns a signature revealed exactly that signature's coordinates. -/
theorem signLoop_revealed (parameter : PublicParameter) (data : PublicData) (message : Message)
    (attempts : Nat) (randomness : Randomness) (result : RunResult (Option Signature))
    (hresult : result ∈ support (costRun f table (withReveals
      (signCostSourceLoop parameter data message attempts randomness)))) :
    ∀ signature, result.1.1 = some signature →
      (∃ pair, firstEncoding f parameter topLayer rootTree
        (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message signature.randomness :
          OracleComp HashSpec MessageDigest)))
        (data.forestKey (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message
          signature.randomness : OracleComp HashSpec MessageDigest)))) encodingAttemptLimit 0 = some pair) ∧
      result.1.2 = revealsOf f parameter data message signature.randomness := by
  induction attempts generalizing result randomness with
  | zero =>
      rw [signCostSourceLoop, costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      intro signature h
      cases h
  | succ attempts ih =>
      rw [signCostSourceLoop] at hresult
      obtain ⟨r3, h3, r4, h4, rfl⟩ := costRun_withReveals_bind f table _ _ result hresult
      obtain rfl := costRun_withReveals_liftHash f table _ r3 h3
      dsimp only at h4 ⊢
      rw [List.nil_append]
      split at h4
      · obtain ⟨hvalue, hreveals⟩ := finish_support f table parameter data message randomness r4 h4
        intro signature hsome
        obtain ⟨hrandomness, hpair⟩ := assembled_some f table parameter data message randomness signature
          (hvalue ▸ hsome)
        rw [hrandomness]
        exact ⟨hpair, hreveals⟩
      · exact ih (randomness + 1) r4 h4

/-- A signature returned by the signer revealed exactly that signature's coordinates. -/
theorem sign_revealed (parameter : PublicParameter) (data : PublicData) (message : Message)
    (result : RunResult (Option Signature))
    (hresult : result ∈ support (costRun f table (withReveals (signCostSource parameter data message)))) :
    ∀ signature, result.1.1 = some signature →
      (∃ pair, firstEncoding f parameter topLayer rootTree
        (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message signature.randomness :
          OracleComp HashSpec MessageDigest)))
        (data.forestKey (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root message
          signature.randomness : OracleComp HashSpec MessageDigest)))) encodingAttemptLimit 0 = some pair) ∧
      result.1.2 = revealsOf f parameter data message signature.randomness := by
  rw [signCostSource] at hresult
  obtain ⟨r1, h1, r2, h2, rfl⟩ := costRun_withReveals_bind f table _ _ result hresult
  obtain ⟨hr1, -⟩ := costRun_withReveals_liftProb f table _ r1 h1
  dsimp only
  rw [hr1, List.nil_append]
  exact signLoop_revealed f table parameter data message _ _ r2 h2

/-- **Signed entries reveal their coordinates, along the interaction.** -/
theorem interaction_revealed (parameter : PublicParameter) (data : PublicData)
    {β : Type} (M : OracleComp Internalize.AdvSpec β)
    (result : RunResult (β × QueryLog SigningSpec))
    (hresult : result ∈ support (costRun f table (withReveals
      (simulateQ (costInteraction parameter data) M).run))) :
    SignedRevealed f parameter data result.1.1.2 result.1.2 := by
  induction M using OracleComp.inductionOn generalizing result with
  | pure value =>
      change result ∈ support (costRun f table (withReveals
        (pure (value, (∅ : QueryLog SigningSpec)) : OracleComp CostSpec _))) at hresult
      rw [costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      intro entry h
      simp at h
  | query_bind input next ih =>
      rw [simulateQ_bind, WriterT.run_bind] at hresult
      obtain ⟨first, hfirst, second, hsecond, rfl⟩ := costRun_withReveals_bind f table _ _ result hresult
      obtain ⟨inner, hinner, rfl⟩ := costRun_withReveals_map f table _ _ second hsecond
      have hrest := ih first.1.1.1 inner hinner
      refine signedRevealed_append f parameter data ?_ hrest
      rw [simulateQ_spec_query] at hfirst
      rcases input with (draw | bytes) | message
      · change first ∈ support (costRun f table (withReveals
          (liftM (liftM (CostSpec.query (.inl (.inl draw))) : OracleComp CostSpec _) :
            WriterT (QueryLog SigningSpec) (OracleComp CostSpec) _).run)) at hfirst
        rw [WriterT.run_liftM] at hfirst
        obtain ⟨query, hquery, rfl⟩ := costRun_withReveals_map f table _ _ first hfirst
        intro entry h
        simp at h
      · change first ∈ support (costRun f table (withReveals
          (liftM (liftM (CostSpec.query (.inl (.inr (.inl bytes)))) : OracleComp CostSpec _) :
            WriterT (QueryLog SigningSpec) (OracleComp CostSpec) _).run)) at hfirst
        rw [WriterT.run_liftM] at hfirst
        obtain ⟨query, hquery, rfl⟩ := costRun_withReveals_map f table _ _ first hfirst
        intro entry h
        simp at h
      · change first ∈ support (costRun f table (withReveals
          ((QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
            (fun message => signCostSource parameter data message)) message).run)) at hfirst
        rw [QueryImpl.run_withLogging_apply] at hfirst
        obtain ⟨signed, hsigned, final, hfinal, rfl⟩ := costRun_withReveals_bind f table _ _ first hfirst
        rw [costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at hfinal
        subst final
        have hrev := sign_revealed f table parameter data message signed hsigned
        intro entry hentry signature hsig
        simp only [List.mem_singleton] at hentry
        subst hentry
        obtain ⟨hpair, hreveals⟩ := hrev signature hsig
        refine ⟨hpair, fun coordinate hcoordinate => ?_⟩
        simp only [List.append_nil]
        rw [hreveals]
        exact hcoordinate

/-- **Signed entries reveal their coordinates, in a completed run of the rich program.** -/
theorem rich_revealed (adversary : Adversary) (q : Nat) (parameter : PublicParameter)
    (data : PublicData) (outcome : Outcome) (reveals : List HiddenGraph.Coordinate)
    (entries : List (Entry HashInput))
    (hresult : ((some outcome, reveals), entries) ∈
      support (costRun f table (richProgram adversary q parameter data))) :
    SignedRevealed f parameter data outcome.2.1 reveals := by
  have h := costRun_withReveals_cap f table _ q outcome reveals entries hresult
  unfold costGameX costRestX at h
  obtain ⟨r1, h1, r2, h2, heq⟩ := costRun_withReveals_bind f table _ _ _ h
  obtain rfl := costRun_withReveals_tick f table _ r1 h1
  obtain ⟨r3, h3, r4, h4, rfl⟩ := costRun_withReveals_bind f table _ _ r2 h2
  have hrev := interaction_revealed f table parameter data _ r3 h3
  obtain ⟨⟨⟨forgery, log⟩, interactionReveals⟩, interactionEntries⟩ := r3
  dsimp only at h4 hrev
  obtain ⟨r5, h5, r6, h6, rfl⟩ := costRun_withReveals_bind f table _ _ r4 h4
  obtain rfl := costRun_withReveals_liftHash f table _ r5 h5
  rw [costRun_withReveals_pure, support_pure, Set.mem_singleton_iff] at h6
  subst r6
  simp only [Prod.mk.injEq] at heq
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
  simpa using hrev

omit [Params] in
/-- A signed entry's forest chain values at and above its opened positions are revealed. -/
theorem SignedRevealed.fchain_mem {parameter : PublicParameter} {data : PublicData}
    {log : QueryLog SigningSpec} {reveals : List HiddenGraph.Coordinate}
    (h : SignedRevealed f parameter data log reveals) (entry : (t : SigningSpec.Domain) × SigningSpec.Range t)
    (hentry : entry ∈ log) (signature : Signature) (hsig : entry.2 = some signature) (c : Coord) (j : SubIdx)
    (ch : FChain) (k : FPos)
    (hk : (GraphView.openedPos (digestMarks (evalWithAnswerFn f (messageDigest parameter data.root entry.1
      signature.randomness : OracleComp HashSpec MessageDigest)) c) j ch).val ≤ k.val) :
    HiddenGraph.Coordinate.fchain
      (digestIndex (evalWithAnswerFn f (messageDigest parameter data.root entry.1 signature.randomness :
        OracleComp HashSpec MessageDigest))) c
      (digestMarks (evalWithAnswerFn f (messageDigest parameter data.root entry.1 signature.randomness :
        OracleComp HashSpec MessageDigest)) c).super j
      ((digestMarks (evalWithAnswerFn f (messageDigest parameter data.root entry.1 signature.randomness :
        OracleComp HashSpec MessageDigest)) c).child j) ch k ∈ reveals := by
  obtain ⟨⟨pair, hpair⟩, hsub⟩ := h entry hentry signature hsig
  apply hsub
  unfold revealsOf
  dsimp only
  rw [hpair]
  refine List.mem_append_right _ (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨c, rfl⟩, ?_⟩)
  exact mem_treeReveals_of j ch k hk

end Fixed

end Sphincs.Security.HiddenBridge
