module

public import XmssSecurity.Proof.CachedSelectionBound
public import XmssSecurity.Proof.CappedJointExactLoss
public import XmssSecurity.Proof.OwnTotal

@[expose] public section

/-!
# Lane 2 at the adversary's own count

The cached-selection term counts the adversary's own encoding queries and the verification's, and the
structural term the adversary's own moved queries and the verification's: the signer's queries are
encoding queries, never moved. The adversary's two kinds are disjoint, so both terms together cost at
most the adversary's own hash calls and the verification's. The potential argument needs only the
adversary's own count below `2^127`: the ghost count of its queries never passes it.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option backward.isDefEq.respectTransparency false

section Expected

variable {ι σ : Type} {spec : OracleSpec ι} (implementation : QueryImpl spec (StateT σ ProbComp))

/-- A static bound on the queries a cost charges bounds its expectation. -/
theorem expectedSimulatedCost_le_of_isQueryBoundP {α : Type} (p : ι → Prop) [DecidablePred p]
    (cost : spec.Domain → σ → ℝ≥0∞) (hcost : ∀ t s, cost t s ≤ if p t then 1 else 0)
    (computation : OracleComp spec α) :
    ∀ (n : ℕ) (s : σ), IsQueryBoundP computation p n →
      expectedSimulatedCost implementation cost computation s ≤ n := by
  induction computation using OracleComp.inductionOn with
  | pure value => intros; simp
  | query_bind t next ih =>
      intro n s hbound
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [expectedSimulatedCost_query_bind]
      have hsum : ∑' r, Pr{let x ← (implementation t).run s}[x = r] *
          expectedSimulatedCost implementation cost (next r.1) r.2 ≤
          ((if p t then n - 1 else n : ℕ) : ℝ≥0∞) := by
        calc _ ≤ ∑' r, Pr{let x ← (implementation t).run s}[x = r] *
              ((if p t then n - 1 else n : ℕ) : ℝ≥0∞) :=
              ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl (ih r.1 _ r.2 (hbound.2 r.1))
          _ = (∑' r, Pr{let x ← (implementation t).run s}[x = r]) *
              ((if p t then n - 1 else n : ℕ) : ℝ≥0∞) := ENNReal.tsum_mul_right
          _ ≤ 1 * ((if p t then n - 1 else n : ℕ) : ℝ≥0∞) :=
              mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl
          _ = _ := one_mul _
      refine (add_le_add (hcost t s) hsum).trans ?_
      by_cases hp : p t
      · have hn := hbound.1.resolve_left (not_not.2 hp)
        rw [ite_eq_left hp, ite_eq_left hp]
        exact_mod_cast (show 1 + (n - 1) ≤ n by omega)
      · rw [ite_eq_right hp, ite_eq_right hp, zero_add]

theorem expectedSimulatedQueryCount_le_of_isQueryBoundP {α : Type} (p : ι → Prop) [DecidablePred p]
    (computation : OracleComp spec α) (n : ℕ) (s : σ) (h : IsQueryBoundP computation p n) :
    expectedSimulatedQueryCount implementation p computation s ≤ n := by
  rw [← expectedSimulatedCost_indicator]
  exact expectedSimulatedCost_le_of_isQueryBoundP implementation p _ (fun _ _ => le_rfl) computation n s h

end Expected

/-! ## The signer's queries are encoding queries -/

theorem isQueryBoundP_liftM_probComp_zero {α : Type} (computation : ProbComp α)
    (p : OracleWorld.Domain → Prop) [DecidablePred p] (hunif : ∀ n, ¬p (.inl n)) :
    IsQueryBoundP (liftM computation : OracleComp OracleWorld α) p 0 := by
  have hall : IsQueryBoundP computation (fun _ => False) 0 :=
    (isQueryBoundP_congr_pred (fun _ => by simp)).mp ((isQueryBoundP_zero_iff computation (fun _ => True)).2
      (allQueriesSatisfy_of_forall (fun _ => trivial) _))
  exact IsQueryBoundP.liftComp_subSpec (q := p) (fun t => iff_of_false not_false (hunif t)) hall

theorem precomputedSignAttempt_zero (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (randomness : Randomness) (p : OracleWorld.Domain → Prop) [DecidablePred p]
    (henc : ∀ payload, ¬p (.inr (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload))) :
    IsQueryBoundP (liftM (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld _) p 0 := by
  have hhash : IsQueryBoundP (Concrete.precomputedSignAttempt secretKey leafIndex message randomness :
      OracleComp HashSpec (Option Signature)) (fun x => p (.inr x)) 0 := by
    unfold Concrete.precomputedSignAttempt Concrete.encodingHash Concrete.tweakableHash Concrete.oracleHash
    rw [HasQuery.instOfMonadLift_query, bind_assoc, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl (henc (message, randomness)), fun u => ?_⟩
    simp only [pure_bind]
    split <;> exact isQueryBoundP_pure _ _ _
  exact IsQueryBoundP.liftComp_subSpec (q := p) (fun _ => Iff.rfl) hhash

theorem precomputedSignBoundedAttempts_zero (secretKey : SecretKey) (leafIndex : LeafIndex)
    (message : Message) (base : Randomness) (p : OracleWorld.Domain → Prop) [DecidablePred p]
    (henc : ∀ payload, ¬p (.inr (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload))) :
    ∀ attempts trial, IsQueryBoundP (Concrete.precomputedSignBoundedAttempts secretKey leafIndex message
      base attempts trial) p 0
  | 0, _ => isQueryBoundP_pure _ _ _
  | attempts + 1, trial => by
      rw [Concrete.precomputedSignBoundedAttempts]
      refine isQueryBoundP_bind_zero _ _ (precomputedSignAttempt_zero _ _ _ _ p henc) fun result => ?_
      split
      · exact isQueryBoundP_pure _ _ _
      · exact precomputedSignBoundedAttempts_zero secretKey leafIndex message base p henc attempts (trial + 1)

/-- The model signer makes no query outside its leaf index's encoding inputs. -/
theorem precomputedCappedSign_zero (secretKey : SecretKey) (leafIndex : LeafIndex) (message : Message)
    (p : OracleWorld.Domain → Prop) [DecidablePred p] (hunif : ∀ n, ¬p (.inl n))
    (henc : ∀ payload, ¬p (.inr (Concrete.CacheView.encodingInput secretKey.parameter leafIndex payload))) :
    IsQueryBoundP (Concrete.precomputedCappedSign secretKey leafIndex message) p 0 := by
  rw [Concrete.precomputedCappedSign]
  exact isQueryBoundP_bind_zero _ _ (isQueryBoundP_liftM_probComp_zero _ p hunif) fun base =>
    isQueryBoundP_bind_zero _ _ (precomputedSignBoundedAttempts_zero _ _ _ _ p henc _ _) fun _ =>
      isQueryBoundP_pure _ _ _

/-! ## The source game's queries through the adversary's -/

namespace Ghost

variable (publicKey : PublicKey) (secretKey : SecretKey)

theorem expectedSimulatedQueryCount_liftM_world (P : OracleWorld.Domain → Prop) [DecidablePred P]
    (input : OracleWorld.Domain) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl P (liftM (OracleWorld.query input) : OracleComp OracleWorld _) cache =
      if P input then 1 else 0 := by
  rw [← bind_pure (liftM (OracleWorld.query input) : OracleComp OracleWorld _),
    expectedSimulatedQueryCount_query_bind]
  simp

/-- **The source game's `P`-queries are the adversary's**, when the signer makes none. -/
theorem expectedSimulatedQueryCount_source_le (P : OracleWorld.Domain → Prop) [DecidablePred P]
    (hsign : ∀ (request : SignRequest) cache,
      expectedSimulatedQueryCount romImpl P (Concrete.scheme.sign secretKey request.leafIndex request.message)
        cache = 0)
    {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (cache : QueryCache HashSpec) (trace : SigningCacheTrace) (k : ℕ),
      expectedSimulatedQueryCount romImpl P
          (simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) computation) cache ≤
        expectedSimulatedCost (impl publicKey secretKey) (fun input _ => if OnWorld P input then 1 else 0)
          computation ((cache, trace), k) := by
  induction computation using OracleComp.inductionOn with
  | pure value => intros; simp
  | query_bind input next ih =>
      intro cache trace k
      rw [expectedSimulatedCost_query_bind, simulateQ_source_query_bind, expectedSimulatedQueryCount_bind,
        impl_run, OracleComp.tsum_prEvent_map_mul]
      refine add_le_add ?_ (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (ih _ _ _ _) _)
      cases input with
      | inl world =>
          rw [source_world, expectedSimulatedQueryCount_liftM_world]
          exact le_of_eq rfl
      | inr request =>
          rw [source_sign, hsign]
          exact zero_le

theorem isAdvHash_iff (input : (OracleWorld + SigningSpec).Domain) : IsAdvHash input ↔ IsAdvHashAction input := by
  rcases input with (_ | _) | _ <;> simp [IsAdvHash, IsAdvHashAction]

/-- **The ghost count stays within the adversary's own budget.** -/
theorem expectedSimulatedCost_overBudget (Q : ℕ) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ∀ (cache : QueryCache HashSpec) (trace : SigningCacheTrace) (k n : ℕ),
      IsQueryBoundP computation IsAdvHashAction n → k + n ≤ Q →
      expectedSimulatedCost (impl publicKey secretKey) (overBudget Q) computation ((cache, trace), k) = 0 := by
  induction computation using OracleComp.inductionOn with
  | pure value => intros; simp
  | query_bind input next ih =>
      intro cache trace k n hbound hk
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [expectedSimulatedCost_query_bind]
      have hcost : overBudget Q input ((cache, trace), k) = 0 := by
        unfold overBudget
        rw [ite_eq_right]
        rintro ⟨hadv, hQ⟩
        have := hbound.1.resolve_left (not_not.2 ((isAdvHash_iff input).1 hadv))
        simp only at hQ
        omega
      rw [hcost, zero_add]
      refine ENNReal.tsum_eq_zero.2 fun r => ?_
      by_cases hr : r ∈ support ((impl publicKey secretKey input).run ((cache, trace), k))
      · cases input with
        | inl world =>
            obtain ⟨r0, _, rfl⟩ := mem_support_world publicKey secretKey hr
            rw [ih r0.1 r0.2 trace _ _ (hbound.2 r0.1), mul_zero]
            by_cases hadv : IsAdvHashAction (.inl world : (OracleWorld + SigningSpec).Domain)
            · have h1 := hbound.1.resolve_left (not_not.2 hadv)
              have htick : tick (.inl world) k = k + 1 := by
                rw [tick, ite_eq_left ((isAdvHash_iff _).2 hadv)]
              rw [htick, ite_eq_left hadv]
              omega
            · have htick : tick (.inl world) k = k := by
                rw [tick, ite_eq_right (fun h => hadv ((isAdvHash_iff _).1 h))]
              rw [htick, ite_eq_right hadv]
              exact hk
        | inr request =>
            obtain ⟨r0, _, rfl⟩ := mem_support_sign publicKey secretKey hr
            have hadv : ¬IsAdvHashAction (.inr request : (OracleWorld + SigningSpec).Domain) := by
              simp [IsAdvHashAction]
            rw [ih r0.1 r0.2 _ k n (by simpa only [ite_eq_right hadv] using hbound.2 r0.1) hk, mul_zero]
      · rw [(prEvent_eq_zero_of_not_mem_support _) hr, zero_mul]

end Ghost

/-! ## Lane 2 -/

/-- One key's cached-selection term: the adversary's own encoding queries and the verification's. -/
noncomputable def ownDigestTerm (adversary : Adversary)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) : ℝ≥0∞ :=
  expectedSimulatedCost (Ghost.impl keyResult.1.1 keyResult.1.2)
      (fun input _ => if Ghost.IsAdvEncoding keyResult.1.2.parameter input then 1 else 0)
      (adversary.main keyResult.1.1) ((keyResult.2, []), 0) +
    ∑' y, Pr{let x ← ((simulateQ romImpl (simulateQ (cappedSourceUnloggedMappedAdversaryImpl keyResult.1.1
      keyResult.1.2) (adversary.main keyResult.1.1))).run keyResult.2)}[x = y] *
      expectedSimulatedQueryCount romImpl (CappedEncodingMonitor.IsEncodingHashQuery keyResult.1.2.parameter)
        (verifyCont keyResult.1.1 y.1) y.2

open Ghost in
/-- Lane 2's digest term, key by key. -/
theorem capped_cachedSelection_le (q : Nat) (adversary : Adversary)
    (hown : OwnHashBound adversary q) (hq : q < 2 ^ 127) :
    Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[WinningCachedSelectionOccurs x] ≤
      (∑' keyResult, Pr{let x ← (simulateQ romImpl Concrete.scheme.keygen).run ∅}[x = keyResult] *
        ownDigestTerm adversary keyResult) / ((2 ^ digestBits : Nat) : ENNReal) := by
  have hproj : Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[WinningCachedSelectionOccurs x] =
      Pr{let x ← cappedDetailedGameWithSigningTrace adversary}[WinningOutcomeBadEventOccurs x.2.1 x.1 .encoding ∧
            ∃ entry ∈ x.2.2, entry.CachedSelectionCollision x.1.secretKey x.2.1] := by
    rw [← cappedDetailedGameWithEncodingTrace_projection, prEvent_map]
    rfl
  rw [hproj, cappedDetailedGameWithSigningTrace, OracleComp.prEvent_bind_eq_tsum, div_eq_mul_inv,
    ← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun keyResult => ?_
  by_cases hkey : keyResult ∈ support ((simulateQ romImpl Concrete.scheme.keygen).run ∅)
  · rw [mul_assoc]
    refine mul_le_mul' le_rfl ?_
    obtain ⟨⟨publicKey, secretKey⟩, cache0⟩ := keyResult
    have hc0 : ∀ e y, cache0 (Partner.input secretKey.parameter e y) = none := fun e y =>
      Concrete.precomputedKeygen_cache_none_encodingInput _ (by simpa [Concrete.scheme] using hkey) e y
    have hcore := Ghost.collision_le_core publicKey secretKey hc0 _ hq (adversary.main publicKey)
      (verifyCont publicKey)
      (Ghost.expectedSimulatedCost_overBudget publicKey secretKey q _ cache0 [] 0 q (hown publicKey)
        (by omega))
    rw [← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl Ghost.N_ne_zero) (Or.inl Ghost.N_ne_top)]
    rw [mul_assoc, ENNReal.mul_le_mul_iff_right Ghost.N_ne_zero Ghost.N_ne_top] at hcore
    refine le_trans ?_ hcore
    rw [mul_comm]
    refine mul_le_mul' le_rfl ?_
    rw [cappedDetailedGameAfterKeygenWithSigningTrace_eq_map, prEvent_map]
    refine prEvent_mono_of_support _ _ _ fun y hy hev => ?_
    refine cachedSelection_event_le adversary publicKey secretKey cache0 _ ?_ hev
    rw [cappedDetailedGameAfterKeygenWithSigningTrace_eq_map, support_map]
    exact ⟨y, hy, rfl⟩
  · rw [(prEvent_eq_zero_of_not_mem_support _) hkey, zero_mul]
    exact zero_le

theorem verifyCont_bound (publicKey : PublicKey) (forgery : Forgery) :
    IsQueryBoundP (verifyCont publicKey forgery) IsWorldHashQuery verifyHashCalls := by
  unfold verifyCont
  rw [show verifyHashCalls = verifyHashCalls + 0 from rfl]
  exact isQueryBoundP_bind (isQueryBoundP_liftM_of_total _ _ (total_verify _ _ _ _)) fun _ _ =>
    isQueryBoundP_pure _ _ _

/-- The structural predicate of a key. -/
abbrev StructuralQuery (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    OracleWorld.Domain → Prop :=
  Rom.IsRelevantHashQuery fun input => keygenStructuralTargetInput keyResult.1.2 keyResult.2 input ≠ input

theorem sign_structural_zero (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (request : SignRequest) (cache : QueryCache HashSpec) :
    expectedSimulatedQueryCount romImpl (StructuralQuery keyResult)
      (Concrete.scheme.sign keyResult.1.2 request.leafIndex request.message) cache = 0 := by
  refine le_antisymm ?_ zero_le
  have h := expectedSimulatedQueryCount_le_of_isQueryBoundP romImpl (StructuralQuery keyResult)
    (Concrete.scheme.sign keyResult.1.2 request.leafIndex request.message) 0 cache
    (precomputedCappedSign_zero keyResult.1.2 request.leafIndex request.message _ (fun _ => id)
      fun payload h => h (keygenStructuralTargetInput_encodingInput _ _ _ payload))
  simpa using h

theorem advEncoding_add_structural_le (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (input : (OracleWorld + SigningSpec).Domain) :
    ((if Ghost.IsAdvEncoding keyResult.1.2.parameter input then 1 else 0) +
      (if OnWorld (StructuralQuery keyResult) input then 1 else 0) : ℝ≥0∞) ≤
      if IsAdvHashAction input then 1 else 0 := by
  rcases input with (n | x) | request
  · rw [ite_eq_right (show ¬Ghost.IsAdvEncoding _ (.inl (.inl n)) from id),
      ite_eq_right (show ¬OnWorld (StructuralQuery keyResult) (.inl (.inl n)) from id), zero_add]
    exact zero_le
  · rw [ite_eq_left (show IsAdvHashAction (.inl (.inr x) : (OracleWorld + SigningSpec).Domain) from rfl)]
    have hdisj := encodingHashQuery_structuralQuery_disjoint keyResult.1.2 keyResult.2 (.inr x)
    by_cases henc : Ghost.IsAdvEncoding keyResult.1.2.parameter (.inl (.inr x))
    · have hstr : ¬OnWorld (StructuralQuery keyResult) (.inl (.inr x) : (OracleWorld + SigningSpec).Domain) :=
        fun h => hdisj ⟨henc, h⟩
      rw [ite_eq_left henc, ite_eq_right hstr, add_zero]
    · rw [ite_eq_right henc, zero_add]
      split <;> simp
  · rw [ite_eq_right (show ¬Ghost.IsAdvEncoding _ (.inr request) from id),
      ite_eq_right (show ¬OnWorld (StructuralQuery keyResult) (.inr request) from id), zero_add]
    exact zero_le

/-- One key's two lane-2 terms cost at most the adversary's own calls and the verification's. -/
theorem ownDigestTerm_add_structural_le (q : Nat) (adversary : Adversary) (hown : OwnHashBound adversary q)
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec) :
    ownDigestTerm adversary keyResult +
        expectedSimulatedQueryCount romImpl (StructuralQuery keyResult)
          (cappedSourceUnloggedDetailedGameAfterKeygen adversary keyResult.1.1 keyResult.1.2) keyResult.2 ≤
      ((q + verifyHashCalls : Nat) : ℝ≥0∞) := by
  obtain ⟨⟨publicKey, secretKey⟩, cache0⟩ := keyResult
  set head := simulateQ (cappedSourceUnloggedMappedAdversaryImpl publicKey secretKey) (adversary.main publicKey)
  set I := Ghost.impl publicKey secretKey
  set run := (simulateQ romImpl head).run cache0
  have hgame : cappedSourceUnloggedDetailedGameAfterKeygen adversary publicKey secretKey =
      head >>= verifyCont publicKey := rfl
  rw [hgame, expectedSimulatedQueryCount_bind]
  have hhead := Ghost.expectedSimulatedQueryCount_source_le publicKey secretKey
    (StructuralQuery ((publicKey, secretKey), cache0))
    (fun request cache => sign_structural_zero ((publicKey, secretKey), cache0) request cache)
    (adversary.main publicKey) cache0 [] 0
  have hadv : expectedSimulatedCost I (fun input _ => if Ghost.IsAdvEncoding secretKey.parameter input then 1 else 0)
        (adversary.main publicKey) ((cache0, []), 0) +
      expectedSimulatedCost I (fun input _ => if OnWorld (StructuralQuery ((publicKey, secretKey), cache0)) input
        then 1 else 0) (adversary.main publicKey) ((cache0, []), 0) ≤ q := by
    rw [← expectedSimulatedCost_add]
    exact expectedSimulatedCost_le_of_isQueryBoundP I IsAdvHashAction _
      (fun input _ => advEncoding_add_structural_le ((publicKey, secretKey), cache0) input) _ q _ (hown publicKey)
  have hverify : (∑' y, Pr{let x ← run}[x = y] *
        expectedSimulatedQueryCount romImpl (CappedEncodingMonitor.IsEncodingHashQuery secretKey.parameter)
          (verifyCont publicKey y.1) y.2) +
      (∑' y, Pr{let x ← run}[x = y] *
        expectedSimulatedQueryCount romImpl (StructuralQuery ((publicKey, secretKey), cache0))
          (verifyCont publicKey y.1) y.2) ≤ verifyHashCalls := by
    rw [← ENNReal.tsum_add]
    calc _ ≤ ∑' y, Pr{let x ← run}[x = y] * (verifyHashCalls : ℝ≥0∞) := by
          refine ENNReal.tsum_le_tsum fun y => ?_
          rw [← mul_add, ← expectedSimulatedQueryCount_or_of_disjoint romImpl _ _
            (encodingHashQuery_structuralQuery_disjoint secretKey cache0)]
          refine mul_le_mul' le_rfl (expectedSimulatedQueryCount_le_of_isQueryBoundP romImpl _ _ _ _ ?_)
          refine IsQueryBoundP.of_imp (fun t ht => ?_) (verifyCont_bound publicKey y.1)
          rcases t with _ | _
          · rcases ht with h | h <;> exact absurd h id
          · exact rfl
      _ = (∑' y, Pr{let x ← run}[x = y]) * (verifyHashCalls : ℝ≥0∞) := ENNReal.tsum_mul_right
      _ ≤ 1 * (verifyHashCalls : ℝ≥0∞) := mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl
      _ = _ := one_mul _
  have key : ∀ a b c d e f g : ℝ≥0∞, c ≤ e → a + e ≤ f → b + d ≤ g → (a + b) + (c + d) ≤ f + g :=
    fun a b c d e f g hce h1 h2 => by
      rw [add_add_add_comm]
      exact add_le_add ((add_le_add le_rfl hce).trans h1) h2
  unfold ownDigestTerm
  refine (key _ _ _ _ _ _ _ hhead hadv hverify).trans_eq ?_
  push_cast; rfl

/-- **Lane 2 at the adversary's own count.** -/
theorem hasSecondLaneBound (q : Nat) (adversary : Adversary) (hown : OwnHashBound adversary q)
    (hq : q < 2 ^ 127) :
    HasSecondLaneBound (q + verifyHashCalls) adversary := by
  have hstructural :
      Pr{let execution ← cappedDetailedGameWithEncodingTrace adversary}[WinningStructuralCollisionOccurs
        execution.2.1.1 execution.1] ≤
      expectedPostKeygenStructuralQueries adversary / ((2 ^ digestBits : Nat) : ENNReal) := by
    calc
      _ = Pr{let execution ← detailedGameWithCache Concrete.scheme adversary}[WinningStructuralCollisionOccurs
          execution.2 execution.1] := by
        rw [← cappedDetailedGameWithEncodingTrace_cache_projection, prEvent_map]
      _ ≤ _ := winningStructuralCollision_probability_le_expectedPostKeygenStructuralQueries adversary
  unfold HasSecondLaneBound WinningSecondLaneBadEventOccurs
  calc
    _ ≤ Pr{let x ← cappedDetailedGameWithEncodingTrace adversary}[WinningCachedSelectionOccurs x] +
        Pr{let execution ← cappedDetailedGameWithEncodingTrace adversary}[WinningStructuralCollisionOccurs
          execution.2.1.1 execution.1] := prEvent_or_le _ _ _
    _ ≤ (∑' keyResult, Pr{let x ← (simulateQ romImpl Concrete.scheme.keygen).run ∅}[x = keyResult] *
          ownDigestTerm adversary keyResult) / ((2 ^ digestBits : Nat) : ENNReal) +
        expectedPostKeygenStructuralQueries adversary / ((2 ^ digestBits : Nat) : ENNReal) :=
      add_le_add (capped_cachedSelection_le q adversary hown hq) hstructural
    _ = (∑' keyResult, Pr{let x ← (simulateQ romImpl Concrete.scheme.keygen).run ∅}[x = keyResult] *
          (ownDigestTerm adversary keyResult + expectedSimulatedQueryCount romImpl
            (StructuralQuery keyResult) (cappedSourceUnloggedDetailedGameAfterKeygen adversary
              keyResult.1.1 keyResult.1.2) keyResult.2)) / ((2 ^ digestBits : Nat) : ENNReal) := by
      rw [← ENNReal.add_div, expectedPostKeygenStructuralQueries, ← ENNReal.tsum_add]
      simp_rw [mul_add]
    _ ≤ ((q + verifyHashCalls : Nat) : ENNReal) / ((2 ^ digestBits : Nat) : ENNReal) := by
      gcongr
      calc _ ≤ ∑' keyResult, Pr{let x ← (simulateQ romImpl Concrete.scheme.keygen).run ∅}[x = keyResult] *
              ((q + verifyHashCalls : Nat) : ENNReal) :=
            ENNReal.tsum_le_tsum fun keyResult =>
              mul_le_mul' le_rfl (ownDigestTerm_add_structural_le q adversary hown keyResult)
        _ = (∑' keyResult, Pr{let x ← (simulateQ romImpl Concrete.scheme.keygen).run ∅}[x = keyResult]) *
              ((q + verifyHashCalls : Nat) : ENNReal) := ENNReal.tsum_mul_right
        _ ≤ 1 * ((q + verifyHashCalls : Nat) : ENNReal) :=
            mul_le_mul' (OracleComp.tsum_prEvent_le_one _) le_rfl
        _ = _ := one_mul _

end XmssSecurity
