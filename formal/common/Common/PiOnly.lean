module

public import Common.Signature
public import Common.WithHash

@[expose] public section

/-!
# The statement's model: `π` and `π⁻¹`, nothing else

The statement's model has coins, `π` and `π⁻¹` (`RandomPermutationOracles`); every party hashes with Keccak-256 over
`π` (`keccak256OverPermutation`). The proofs reason in the model with a Keccak-256 oracle (`KSpecH`,
`Common.HashOracle`). A game of that model with each hash call expanded into its permutation
calls (`expand`) is a game of the statement's model:

* `runK_expand`: with the same distribution against the lazily sampled permutation;
* `isWeightBound_expand_iff`: with the same number of permutation calls on every path (a hash of
  `n` bytes is `⌊n / 136⌋ + 1` calls of `π` on every path, and its digest can be any);
* `simulateQ_expand_embed`: an adversary of the statement's model, read in the model with the
  hash oracle (`embed`), is itself once expanded.
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace Common

open LeanVM.Protocol

/-- The statement's Keccak state, `25` lanes (`Common.KState` is the bytes'). -/
local notation "LState" => LeanVM.Semantics.KeccakState

/-! ## Keccak-256 over `π`, through a simulation and in permutation calls -/

section Absorb

variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Absorbing commutes with a simulation. -/
theorem simulateQ_absorbWith (impl : QueryImpl spec m) (π : LState → OracleComp spec LState) :
    ∀ (n : ℕ) (s : LState) (d : List UInt8),
      simulateQ impl (KeccakHash.absorbWith π n s d) =
        KeccakHash.absorbWith (fun x ↦ simulateQ impl (π x)) n s d
  | 0, s, d => rfl
  | n + 1, s, d => by
    simp only [KeccakHash.absorbWith, simulateQ_bind]
    congr 1
    funext s'
    exact simulateQ_absorbWith impl π n s' _

/-- **Keccak-256 over `π` commutes with a simulation.** -/
theorem simulateQ_keccak256With (impl : QueryImpl spec m) (π : LState → OracleComp spec LState)
    (d : List UInt8) :
    simulateQ impl (KeccakHash.keccak256With π d) =
      KeccakHash.keccak256With (fun x ↦ simulateQ impl (π x)) d := by
  simp only [KeccakHash.keccak256With, simulateQ_bind, simulateQ_pure, simulateQ_absorbWith]

end Absorb

/-- Absorbing `n + 1` blocks over `π`, then `g`: within `Q' + (n + 1)` permutation calls when `g`
is within `Q'` from every state. -/
theorem isWeightBound_absorbWith {β : Type} {g : LState → OracleComp RandomPermutationOracles β} {Q' : ℕ}
    (hg : ∀ s, QueryCostAtMost (g s) permutationCallCost Q') :
    ∀ (n : ℕ) (s : LState) (d : List UInt8),
      QueryCostAtMost (KeccakHash.absorbWith queryPermutation n s d >>= g) permutationCallCost (Q' + (n + 1))
  | 0, s, d => by
    change QueryCostAtMost (liftM (RandomPermutationOracles.query (.inr (.forward _))) >>= g) permutationCallCost (Q' + 1)
    rw [isWeightBound_query_bind_iff]
    exact ⟨by simp [permutationCallCost], fun u ↦ by simpa [permutationCallCost] using hg u⟩
  | n + 1, s, d => by
    simp only [KeccakHash.absorbWith, bind_assoc]
    change QueryCostAtMost (liftM (RandomPermutationOracles.query (.inr (.forward _))) >>= fun s' ↦
      KeccakHash.absorbWith queryPermutation n s' _ >>= g) permutationCallCost (Q' + (n + 1 + 1))
    rw [isWeightBound_query_bind_iff]
    refine ⟨by simp only [permutationCallCost]; omega, fun u ↦ ?_⟩
    have h := isWeightBound_absorbWith hg n u (d.drop KeccakHash.rate)
    simpa [permutationCallCost, show Q' + (n + 1 + 1) - 1 = Q' + (n + 1) by omega] using h

/-- Absorbing `n + 1` blocks over `π`, then `g`, within `Q` permutation calls: `n + 1 ≤ Q`, and
`g` is within the rest from every state (the last call of `π` can answer any). -/
theorem isWeightBound_absorbWith_inv {β : Type} {g : LState → OracleComp RandomPermutationOracles β} :
    ∀ (n : ℕ) (s : LState) (d : List UInt8) (Q : ℕ),
      QueryCostAtMost (KeccakHash.absorbWith queryPermutation n s d >>= g) permutationCallCost Q →
        n + 1 ≤ Q ∧ ∀ s', QueryCostAtMost (g s') permutationCallCost (Q - (n + 1))
  | 0, s, d, Q, h => by
    change QueryCostAtMost (liftM (RandomPermutationOracles.query (.inr (.forward _))) >>= g) permutationCallCost Q at h
    rw [isWeightBound_query_bind_iff] at h
    exact ⟨by simpa [permutationCallCost] using h.1, fun s' ↦ by simpa [permutationCallCost] using h.2 s'⟩
  | n + 1, s, d, Q, h => by
    simp only [KeccakHash.absorbWith, bind_assoc] at h
    change QueryCostAtMost (liftM (RandomPermutationOracles.query (.inr (.forward _))) >>= fun s' ↦
      KeccakHash.absorbWith queryPermutation n s' _ >>= g) permutationCallCost Q at h
    rw [isWeightBound_query_bind_iff] at h
    obtain ⟨h1, h2⟩ := isWeightBound_absorbWith_inv n s (d.drop KeccakHash.rate) _ (h.2 s)
    refine ⟨by simp [permutationCallCost] at h1; omega, fun s' ↦ ?_⟩
    have := h2 s'
    simpa [permutationCallCost, show Q - 1 - (n + 1) = Q - (n + 1 + 1) by omega] using this

/-- A state whose first four lanes are the digest's words: Keccak-256's output can be any
digest. -/
def digestState (d : DigestBytes) : LState := Vector.ofFn fun i ↦ KeccakHash.littleEndianLane
    d.toList i

/-- The digest of a final state: the bytes of its first four lanes (`keccak256With`). -/
def digestOf (s : LState) : DigestBytes :=
  Digest.toBytes #v[LeanVM.Semantics.Keccak.lane s 0, LeanVM.Semantics.Keccak.lane s 1,
    LeanVM.Semantics.Keccak.lane s 2, LeanVM.Semantics.Keccak.lane s 3]

theorem digestOf_digestState (d : DigestBytes) : digestOf (digestState d) = d := by
  have h : (#v[LeanVM.Semantics.Keccak.lane (digestState d) 0,
      LeanVM.Semantics.Keccak.lane (digestState d) 1,
      LeanVM.Semantics.Keccak.lane (digestState d) 2,
      LeanVM.Semantics.Keccak.lane (digestState d) 3] : Digest) = LeanVM.Digest.ofRpm d := by
    simp [LeanVM.Semantics.Keccak.lane, digestState, LeanVM.Digest.ofRpm]
  rw [digestOf, h, LeanVM.Rpm.toBytes_ofRpm]

/-- The cost of Keccak-256 over `π` on `m`: one call per block of the padded message. -/
theorem keccakK_bind {β : Type} (m : List UInt8) (f : DigestBytes → OracleComp RandomPermutationOracles β) :
    keccak256OverPermutation m >>= f = KeccakHash.absorbWith queryPermutation (m.length / KeccakHash.rate)
      (Vector.replicate 25 0) m >>= fun s ↦ f (digestOf s) := by
  simp [keccak256OverPermutation, KeccakHash.keccak256With, digestOf]

/-- **Keccak-256 over `π` makes `⌊n / 136⌋ + 1` permutation calls.** -/
theorem isWeightBound_keccakK_bind {β : Type} (m : List UInt8) {f : DigestBytes → OracleComp RandomPermutationOracles β}
    {Q' : ℕ} (hf : ∀ d, QueryCostAtMost (f d) permutationCallCost Q') :
    QueryCostAtMost (keccak256OverPermutation m >>= f) permutationCallCost (Q' + (m.length / 136 + 1)) := by
  rw [keccakK_bind]
  exact isWeightBound_absorbWith (fun s ↦ hf _) _ _ _

/-- **Keccak-256 over `π` makes `⌊n / 136⌋ + 1` permutation calls on every path**, and its
digest can be any. -/
theorem isWeightBound_keccakK_bind_inv {β : Type} (m : List UInt8)
    {f : DigestBytes → OracleComp RandomPermutationOracles β} {Q : ℕ} (h : QueryCostAtMost (keccak256OverPermutation m >>= f) permutationCallCost Q) :
    m.length / 136 + 1 ≤ Q ∧ ∀ d, QueryCostAtMost (f d) permutationCallCost (Q - (m.length / 136 + 1)) := by
  rw [keccakK_bind] at h
  obtain ⟨h1, h2⟩ := isWeightBound_absorbWith_inv _ _ _ _ h
  refine ⟨h1, fun d ↦ ?_⟩
  have := h2 (digestState d)
  rwa [digestOf_digestState] at this

/-! ## Expanding the hash oracle -/

/-- **Each hash call expanded into its permutation calls**: coins, `π` and `π⁻¹` as they are,
Keccak-256 over `π` for the hash oracle. -/
def expand : QueryImpl KSpecH (OracleComp RandomPermutationOracles)
  | .inl n => liftM (RandomPermutationOracles.query (.inl n))
  | .inr (.inl m) => keccak256OverPermutation m
  | .inr (.inr q) => liftM (RandomPermutationOracles.query (.inr q))

/-- The statement's oracles among those with the hash oracle. -/
def embed : QueryImpl RandomPermutationOracles (OracleComp KSpecH)
  | .inl n => liftM (KSpecH.query (.inl n))
  | .inr q => liftM (KSpecH.query (.inr (.inr q)))

/-- The statement's answers to an expanded query are the answers with the hash oracle. -/
theorem kImpl_compose_expand : lazyRandomPermutationOracles ∘ₛ expand = kImplH := by
  funext t
  rcases t with n | m | q
  · simp only [QueryImpl.apply_compose, expand, simulateQ_spec_query]
    rfl
  · simp only [QueryImpl.apply_compose, expand, keccak256OverPermutation, simulateQ_map, simulateQ_keccak256With,
      queryPermutation, simulateQ_spec_query]
    rfl
  · simp only [QueryImpl.apply_compose, expand, simulateQ_spec_query]
    rfl

/-- **An expanded game has the game's distribution.** -/
theorem runK_expand {α : Type} (G : OracleComp KSpecH α) : runWithRandomPermutation (simulateQ expand G) = runKH G := by
  rw [runWithRandomPermutation, runKH, ← QueryImpl.simulateQ_compose, kImpl_compose_expand]

/-- **An adversary of the statement's model, embedded then expanded, is itself.** -/
theorem simulateQ_expand_embed {α : Type} (A : OracleComp RandomPermutationOracles α) :
    simulateQ expand (simulateQ embed A) = A := by
  rw [← QueryImpl.simulateQ_compose]
  conv_rhs => rw [← simulateQ_id' A]
  congr 1
  funext t
  rcases t with n | q
  · simp [embed, expand]
  · simp [embed, expand]

/-- **An expanded game makes the game's permutation calls.** -/
theorem isWeightBound_expand {α : Type} {G : OracleComp KSpecH α} {Q : ℕ}
    (h : QueryCostAtMost G permCallsH Q) : QueryCostAtMost (simulateQ expand G) permutationCallCost Q := by
  induction G using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at h
    rw [simulateQ_query_bind]
    rcases t with n | m | q
    · change QueryCostAtMost (liftM (RandomPermutationOracles.query (.inl n)) >>= fun u ↦ simulateQ expand (k u))
        permutationCallCost Q
      exact (isWeightBound_query_bind_iff _ _ _ _).mpr ⟨Nat.zero_le _, fun u ↦ ih u (h.2 u)⟩
    · change QueryCostAtMost (keccak256OverPermutation m >>= fun u ↦ simulateQ expand (k u)) permutationCallCost Q
      have h1 : m.length / 136 + 1 ≤ Q := h.1
      have := isWeightBound_keccakK_bind m (fun d ↦ ih d (h.2 d))
      rwa [show Q - permCallsH (.inr (.inl m)) + (m.length / 136 + 1) = Q by
        simp only [permCallsH]; omega] at this
    · change QueryCostAtMost (liftM (RandomPermutationOracles.query (.inr q)) >>= fun u ↦ simulateQ expand (k u))
        permutationCallCost Q
      exact (isWeightBound_query_bind_iff _ _ _ _).mpr ⟨h.1, fun u ↦ ih u (h.2 u)⟩

/-- **An expanded game's permutation calls bound the game's.** -/
theorem isWeightBound_expand_iff {α : Type} (G : OracleComp KSpecH α) (Q : ℕ) :
    QueryCostAtMost (simulateQ expand G) permutationCallCost Q ↔ QueryCostAtMost G permCallsH Q := by
  refine ⟨fun h ↦ ?_, isWeightBound_expand⟩
  induction G using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [simulateQ_query_bind] at h
    rw [isWeightBound_query_bind_iff]
    rcases t with n | m | q
    · change QueryCostAtMost (liftM (RandomPermutationOracles.query (.inl n)) >>= fun u ↦ simulateQ expand (k u))
        permutationCallCost Q at h
      rw [isWeightBound_query_bind_iff] at h
      exact ⟨Nat.zero_le _, fun u ↦ ih u _ (h.2 u)⟩
    · change QueryCostAtMost (keccak256OverPermutation m >>= fun u ↦ simulateQ expand (k u)) permutationCallCost Q at h
      obtain ⟨h1, h2⟩ := isWeightBound_keccakK_bind_inv m h
      exact ⟨h1, fun d ↦ ih d _ (h2 d)⟩
    · change QueryCostAtMost (liftM (RandomPermutationOracles.query (.inr q)) >>= fun u ↦ simulateQ expand (k u))
        permutationCallCost Q at h
      rw [isWeightBound_query_bind_iff] at h
      exact ⟨h.1, fun u ↦ ih u _ (h.2 u)⟩

/-! ## The SUF-CMA game -/

namespace SufCma

variable {Seed PK SK Req Resp F : Type}

/-- The adversary's oracles with the hash oracle: its queries of the model embedded, its signing
requests as they are. -/
def embedS : QueryImpl (RandomPermutationOracles + (Req →ₒ Resp)) (OracleComp (KSpecH + (Req →ₒ Resp)))
  | .inl t => simulateQ (fun u ↦ liftM ((KSpecH + (Req →ₒ Resp)).query (.inl u)) :
      QueryImpl KSpecH (OracleComp (KSpecH + (Req →ₒ Resp)))) (embed t)
  | .inr r => liftM ((KSpecH + (Req →ₒ Resp)).query (.inr r))

/-- The adversary's oracles expanded: its hash calls into permutation calls, its signing requests
as they are. -/
def expandS : QueryImpl (KSpecH + (Req →ₒ Resp)) (OracleComp (RandomPermutationOracles + (Req →ₒ Resp)))
  | .inl t => simulateQ (fun u ↦ liftM ((RandomPermutationOracles + (Req →ₒ Resp)).query (.inl u)) :
      QueryImpl RandomPermutationOracles (OracleComp (RandomPermutationOracles + (Req →ₒ Resp)))) (expand t)
  | .inr r => liftM ((RandomPermutationOracles + (Req →ₒ Resp)).query (.inr r))

theorem simulateQ_expandS_embedS {α : Type} (A : OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) α) :
    simulateQ expandS (simulateQ embedS A) = A := by
  rw [← QueryImpl.simulateQ_compose]
  conv_rhs => rw [← simulateQ_id' A]
  congr 1
  funext t
  rcases t with (n | q) | r
  · simp [embedS, expandS, embed, expand]
  · simp [embedS, expandS, embed, expand]
  · simp [embedS, expandS]

/-- The hash with the hash oracle, expanded, is the statement's hash. -/
theorem simulateQ_expand_hashKH {β : Type} (X : OracleComp SchemeHashSpec β) :
    simulateQ expand (simulateQ hashKH X) = simulateQ schemeHashOverPermutation X := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext m
  simp [QueryImpl.apply_compose, hashKH, schemeHashOverPermutation, expand]

/-- **The statement's RPM game is the game with the hash oracle, expanded**, against the
adversary embedded. -/
theorem rpmGame_eq_expand (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) F) :
    forgeryGameWithHash S main = simulateQ expand (rpmGameH S fun pk ↦ simulateQ embedS (main pk)) := by
  have hmid : ∀ (sk : SK) {α : Type} (oa : OracleComp (KSpecH + (Req →ₒ Resp)) α),
      simulateQ expand ((simulateQ (QueryImpl.ofLift KSpecH
        (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecH)) + signingOracleKH S sk) oa).run) =
      (simulateQ (QueryImpl.ofLift RandomPermutationOracles
        (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp RandomPermutationOracles)) + loggedSigningOracleWithHash S sk)
          (simulateQ expandS oa)).run := by
    intro sk α oa
    refine simulateQ_writer_run_comm _ _ _ _ (fun t ↦ ?_) oa
    rcases t with t | r
    · have h2 : ((QueryImpl.ofLift KSpecH (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecH)) +
          signingOracleKH S sk) (.inl t)).run =
            (·, ∅) <$> (liftM (KSpecH.query t) : OracleComp KSpecH _) := rfl
      have h5 : (QueryImpl.ofLift RandomPermutationOracles (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp RandomPermutationOracles)) +
          loggedSigningOracleWithHash S sk) ∘ₛ (fun u ↦ liftM ((RandomPermutationOracles + (Req →ₒ Resp)).query (.inl u)) :
            QueryImpl RandomPermutationOracles (OracleComp (RandomPermutationOracles + (Req →ₒ Resp)))) =
          QueryImpl.ofLift RandomPermutationOracles (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp RandomPermutationOracles)) := by
        funext u
        simp only [QueryImpl.apply_compose, simulateQ_spec_query]
        rfl
      rw [h2, simulateQ_map, simulateQ_spec_query, expandS, ← QueryImpl.simulateQ_compose, h5,
        run_simulateQ_ofLift_writer]
      rfl
    · have h3 : ((QueryImpl.ofLift KSpecH (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp KSpecH)) +
          signingOracleKH S sk) (.inr r)).run = (fun u ↦ (u, [⟨r, u⟩])) <$>
            simulateQ hashKH (S.sign sk r) := by
        simp [signingOracleKH]
      have h3' : ((QueryImpl.ofLift RandomPermutationOracles (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp RandomPermutationOracles)) +
          loggedSigningOracleWithHash S sk) (.inr r)).run = (fun u ↦ (u, [⟨r, u⟩])) <$>
            simulateQ schemeHashOverPermutation (S.sign sk r) := by
        simp [loggedSigningOracleWithHash]
      rw [h3, simulateQ_map, simulateQ_expand_hashKH, expandS, simulateQ_spec_query, h3']
  simp only [forgeryGameWithHash, rpmGameH, simulateQ_bind, simulateQ_pure, simulateQ_expand_hashKH, hmid,
    simulateQ_expandS_embedS]
  rw [simulateQ_liftM_of_coins _ (fun n ↦ rfl)]

end SufCma

end Common
