module

public import Common.MultiKey.Reduction
public import Common.CostCombinators

@[expose] public section

/-!
# The reduction's charged calls

The reduction makes at most the multi-key adversary's own hash calls of the real oracle
(`reduction_advHashCalls`): the other keys' key generation and signers ask the private oracle,
which the reduction samples with coins, and each hash call of the adversary becomes one call, of
the private or the real oracle. It makes at most the adversary's requests to key `i`
(`reduction_requestCalls`).
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal
open HashSig.OverPermutation (sequenceFin)

namespace Common.SufCma.MultiKey

variable {Seed PK SK Req Resp F : Type}

/-- The real oracle's calls, among the tagged oracles and the requests. -/
def realCalls : (TSpec + (Req →ₒ Resp)).Domain → ℕ
  | .inl (.inr (false, _)) => 1
  | _ => 0

/-- The requests, among the tagged oracles and the requests. -/
def reqCalls : (TSpec + (Req →ₒ Resp)).Domain → ℕ
  | .inr _ => 1
  | _ => 0

/-- A weight that charges no coin and no private query. -/
def Free (w : (TSpec + (Req →ₒ Resp)).Domain → ℕ) : Prop :=
  (∀ n, w (.inl (.inl n)) = 0) ∧ ∀ x, w (.inl (.inr (true, x))) = 0

theorem free_realCalls : Free (Req := Req) (Resp := Resp) realCalls :=
  ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩

theorem free_reqCalls : Free (Req := Req) (Resp := Resp) reqCalls :=
  ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩

variable {w : (TSpec + (Req →ₒ Resp)).Domain → ℕ}

/-- The tagged oracles inside the reduction weigh what they weigh there. -/
theorem toTR_cost {α : Type} {X : OracleComp TSpec α} {Q : ℕ}
    (h : QueryCostAtMost X (fun t ↦ w (.inl t)) Q) :
    QueryCostAtMost (simulateQ (toTR (Req := Req) (Resp := Resp)) X) w Q :=
  isWeightBound_simulateQ _ _ _ (fun t ↦ (isWeightBound_query (spec := TSpec + (Req →ₒ Resp))
    w (.inl t)).mono le_rfl) h

theorem coins_cost (hw : Free w) {α : Type} (p : ProbComp α) :
    QueryCostAtMost (simulateQ (toTR (Req := Req) (Resp := Resp)) (simulateQ coinsT p)) w 0 :=
  toTR_cost (isWeightBound_simulateQ _ (fun _ ↦ 0) _ (fun n ↦
    (isWeightBound_query (spec := TSpec) (fun t ↦ w (.inl t)) (.inl n)).mono
      (le_of_eq (hw.1 n))) (QueryCostAtMost.zero_weight p))

theorem private_cost (hw : Free w) {α : Type} (X : OracleComp SchemeHashSpec α) :
    QueryCostAtMost (simulateQ (toTR (Req := Req) (Resp := Resp)) (simulateQ tagG X)) w 0 :=
  toTR_cost (isWeightBound_simulateQ _ (fun _ ↦ 0) _ (fun x ↦
    (isWeightBound_query (spec := TSpec) (fun t ↦ w (.inl t)) (.inr (true, x))).mono
      (le_of_eq (hw.2 x))) (QueryCostAtMost.zero_weight X))

variable (S : SchemeWithHash Seed PK SK Req Resp F) {k : ℕ}

theorem setup_cost (hw : Free w) (i : Fin k) :
    QueryCostAtMost (simulateQ (toTR (Req := Req) (Resp := Resp)) (setup S i)) w 0 := by
  unfold setup
  rw [LeanXmss.simulateQ_sequenceFin]
  refine (sequenceFin_cost (K := 0) _ fun j ↦ ?_).mono (by simp)
  split
  · exact isWeightBound_pure _ _ 0
  · simp only [simulateQ_bind, simulateQ_map]
    exact ((coins_cost hw _).bind fun s ↦ isWeightBound_map _ (private_cost hw _)).mono
      (by simp)

/-- Each output of computations in sequence is an output of its computation. -/
theorem mem_support_sequenceFin {ι α : Type} {spec : OracleSpec.{0, 0} ι} :
    ∀ {n : ℕ} (c : Fin n → OracleComp spec α) {v : Fin n → α}, v ∈ support (sequenceFin c) →
      ∀ j, v j ∈ support (c j)
  | 0, _, _, _, j => j.elim0
  | n + 1, c, v, h, j => by
    simp only [sequenceFin, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · exact hhead
    · exact mem_support_sequenceFin (fun i ↦ c i.succ) htail j

/-- The private oracle's records are those of every key but `i`. -/
theorem setup_isSome (i : Fin k) {others : Fin k → Option (KeyRec PK SK)}
    (h : others ∈ support (setup S i)) (j : Fin k) (hj : j ≠ i) : (others j).isSome := by
  have hj' := mem_support_sequenceFin _ h j
  simp only [hj, ↓reduceIte, support_bind, support_map, Set.mem_iUnion, Set.mem_image] at hj'
  obtain ⟨_, _, z, _, hz⟩ := hj'
  rw [← hz]
  rfl

theorem support_toTR {α : Type} (X : OracleComp TSpec α) :
    support (simulateQ (toTR (Req := Req) (Resp := Resp)) X) = support X :=
  support_liftComp X

variable (ownedPub : PK → List UInt8 → Prop) [∀ pk, DecidablePred (ownedPub pk)]

/-- The reduction's run, its private oracle inside. -/
theorem innerR_cost (w' : (World + (Req →ₒ Resp)).Domain → ℕ) (hc : ∀ n, w' (.inl (.inl n)) = 0)
    (t : (TSpec + (Req →ₒ Resp)).Domain) (s : SchemeHashSpec.QueryCache)
    (hF : ∀ x, w' (.inl (.inr x)) ≤ w (.inl (.inr (false, x))))
    (hR : ∀ r, w' (.inr r) ≤ w (.inr r)) :
    QueryCostAtMost ((innerR (Req := Req) (Resp := Resp) t).run s) w' (w t) := by
  rcases t with (n | ⟨b, x⟩) | r
  · show QueryCostAtMost (simulateQ toWR ((fun u ↦ (u, s)) <$>
      (liftM (World.query (.inl n)) : OracleComp World _))) _ _
    rw [simulateQ_map, simulateQ_spec_query]
    exact isWeightBound_map _ ((isWeightBound_query _ _).mono (by simp [hc]))
  · cases b
    · show QueryCostAtMost (simulateQ toWR ((fun u ↦ (u, s)) <$>
        (liftM (World.query (.inr x)) : OracleComp World _))) _ _
      rw [simulateQ_map, simulateQ_spec_query]
      exact isWeightBound_map _ ((isWeightBound_query _ _).mono (hF x))
    · have h : QueryCostAtMost
          (liftM ((SchemeHashSpec.randomOracle x).run s) : OracleComp World _)
          (fun t ↦ w' (.inl t)) 0 :=
        isWeightBound_liftM_probComp _ (fun n ↦ hc n) _
      exact (isWeightBound_simulateQ (toWR (Req := Req) (Resp := Resp)) _ w'
        (fun t ↦ (isWeightBound_query (spec := World + (Req →ₒ Resp)) w' (.inl t)).mono le_rfl)
        h).mono (Nat.zero_le _)
  · show QueryCostAtMost ((fun u ↦ (u, s)) <$>
      (liftM ((World + (Req →ₒ Resp)).query (.inr r)) : OracleComp _ _)) _ _
    exact isWeightBound_map _ ((isWeightBound_query _ _).mono (hR r))

/-- **The reduction makes the adversary's own hash calls of the real oracle.** -/
theorem reduction_advHashCalls (i : Fin k)
    (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F)) (q : ℕ)
    (hq : ∀ pks, QueryCostAtMost (A pks) advHashCalls q) (pk : PK) :
    QueryCostAtMost (reduction S ownedPub i A pk) advHashCalls q := by
  unfold reduction
  refine isWeightBound_map _ ?_
  rw [StateT.run'_eq]
  refine isWeightBound_map _ ?_
  refine isWeightBound_run_simulateQ _ realCalls _ (fun t s ↦ innerR_cost advHashCalls
    (fun _ ↦ rfl) t s (fun _ ↦ le_rfl) (fun _ ↦ le_rfl)) ?_ ∅
  unfold reductionT
  refine ((setup_cost S free_realCalls i).bind fun others ↦
    (isWeightBound_simulateQ _ advHashCalls _ (fun t ↦ ?_) (hq _)).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono (by simp)
  rcases t with (n | x) | ⟨j, r⟩
  · exact (isWeightBound_query _ _).mono le_rfl
  · exact (isWeightBound_query _ _).mono (by
      simp only [realCalls, advHashCalls]
      split <;> simp_all)
  · simp only [advImpl]
    split
    · exact (isWeightBound_query _ _).mono le_rfl
    · split
      · exact private_cost free_realCalls _
      · exact (isWeightBound_query _ _).mono le_rfl

/-- **The reduction makes the adversary's requests to key `i`.** -/
theorem reduction_requestCalls (i : Fin k)
    (A : (Fin k → PK) → OracleComp (World + (Fin k × Req →ₒ Resp)) (Fin k × F)) (n : ℕ)
    (hn : ∀ pks, QueryCostAtMost (A pks) (requestToKeyCalls i) n) (pk : PK) :
    QueryCostAtMost (reduction S ownedPub i A pk) requestCalls n := by
  unfold reduction
  refine isWeightBound_map _ ?_
  rw [StateT.run'_eq]
  refine isWeightBound_map _ ?_
  refine isWeightBound_run_simulateQ _ reqCalls _ (fun t s ↦ innerR_cost requestCalls
    (fun _ ↦ rfl) t s (fun _ ↦ le_rfl) (fun _ ↦ le_rfl)) ?_ ∅
  unfold reductionT
  refine (QueryCostAtMost.bind_of_support (setup_cost S free_reqCalls i) fun others hothers ↦
    (isWeightBound_simulateQ _ (requestToKeyCalls i) _ (fun t ↦ ?_) (hn _)).bind fun _ ↦
      isWeightBound_pure _ _ 0).mono (by simp)
  rw [support_toTR] at hothers
  rcases t with (n | x) | ⟨j, r⟩
  · exact (isWeightBound_query _ _).mono le_rfl
  · exact (isWeightBound_query _ _).mono le_rfl
  · simp only [advImpl]
    split
    · exact (isWeightBound_query _ _).mono (by simp_all [reqCalls, reqWeight])
    · rename_i hj
      split
      · exact (private_cost free_reqCalls _).mono (Nat.zero_le _)
      · rename_i hnone
        have := setup_isSome S i hothers j hj
        rw [hnone] at this
        cases this

end Common.SufCma.MultiKey
