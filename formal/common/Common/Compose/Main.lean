module

public import Common.Compose.Forger

@[expose] public section

/-!
# The conditional composition theorem

`composed_sound`: in the composed experiment (`composedExperiment`, `Defs.lean`), the verifier
accepts a proof of the guest program on the digest of a statement whose deferred claim holds, and
the extracted execution's decoding does not explain the statement, or it does with a witness
holding a raw signature, under an honest key, that wins against that key's transcript (a fresh
signature the honest signer never returned), with probability at most the knowledge-soundness
bound, plus `δ` (`KeccakVerificationLikeIdeal`), plus the multi-key bound
`k · (q_h + slack + k) · 2^-bits` of the scheme over `π_h`.

The proof is a union bound over three events.

1. **The knowledge-soundness step** (`composed_outcome_evalDistEq`): the composed experiment's
   outcome is the knowledge-soundness experiment of the wrapped adversary `honest scheme k A`,
   the verdict's run over `π_h` (coins only, its result dropped) leaving the outcome's
   distribution alone; the wrapped adversary calls `π` and `π⁻¹` as `A` does (`honest_cost`), so
   `AggregateSound` bounds the first event.
2. **The event split**: a decoding that explains the statement with a winning raw signature under
   an honest key makes a candidate (`candidate`): its witness holds the statement
   (`NodeRelation`), so the deployed verification accepts the raw signature (`hraws`). The
   candidate's verification over `π_h` rejects it (the hypothesis `KeccakVerificationLikeIdeal`)
   or accepts it.
3. **The forger**: the candidate and its verdict are the joint world's
   (`composed_evalDistEq_jointGame`, `Joint.lean`), which is the multi-key forgery game against
   the forger, the roles of `π` and `π_h` swapped (`prob_jointGame_le`, `Forger.lean`); the forger
   makes the adversary's `q_h` calls of `π_h` and its requests (`forger_permutationCost`,
   `forger_requestCost`), so `MultiKeyStronglyUnforgeable` bounds the third event.
-/

open OracleComp OracleSpec
open scoped ENNReal
open LeanVM LeanVM.Node LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile
open Common.SufCma

namespace Common.Compose

variable {Seed PK SK Req Resp F : Type}
  (scheme : Scheme Seed PK SK Req Resp F) (k : ℕ)
  (guest : LeanIsaProgram) (decoder : Cost.MachineProgram)
  (extractor : StraightLineExtractor) (raws : NodeWitness → List (PK × F))
  (deployedVerify : PK → F → Bool)

/-! ## The knowledge-soundness step -/

/-- **The composed experiment's outcome is the knowledge-soundness experiment of the wrapped
adversary.** -/
theorem composed_outcome_evalDistEq (A : ComposedAdversary k PK Req Resp) :
    (·.1) <$> composedExperiment scheme k guest decoder extractor raws deployedVerify A =ᵈ
      knowledgeSoundnessExperiment ((·.1) <$> honest scheme k A) := by
  unfold composedExperiment knowledgeSoundnessExperiment runWithRandomPermutation
  simp only [StateT.run'_eq, Functor.map_map, simulateQ_bind, StateT.run_bind, map_bind,
    simulateQ_map, StateT.run_map, bind_map_left]
  refine EvalDistEq.bind_congr EvalDistEq.rfl fun p ↦ ?_
  obtain ⟨⟨⟨⟨⟨program, input⟩, proof⟩, pks, log, edges⟩, transcript⟩, E⟩ := p
  simp only [simulateQ_pure, StateT.run_pure, map_pure, run_lazy_liftM, bind_map_left]
  refine EvalDistEq.bind_congr EvalDistEq.rfl fun a ↦ ?_
  exact EvalDistEq.bind_const _ _

/-- **The wrapped adversary calls `π` and `π⁻¹` as the adversary does**: the honest side's
hashing over `π_h` draws coins only. -/
theorem honest_cost (A : ComposedAdversary k PK Req Resp) (Q : ℕ)
    (hQ : ∀ pks, QueryCostAtMost (A pks) piCost Q) :
    QueryCostAtMost ((·.1) <$> honest scheme k A) permutationCallCost Q := by
  refine isWeightBound_map _ ?_
  unfold honest
  refine (QueryCostAtMost.bind (isWeightBound_liftM_probComp _ (fun _ ↦ rfl) _) fun keys ↦
    isWeightBound_map _ (isWeightBound_run_simulateQ _ piCost _ (fun t s ↦ ?_) (hQ _) _)).mono
      (by simp)
  rcases t with ((n | q) | q) | r
  · show QueryCostAtMost ((liftM (RandomPermutationOracles.query (.inl n)) :
      OracleComp _ _) >>= fun a ↦ pure (a, s)) _ _
    rw [bind_pure_comp]
    exact isWeightBound_map _ (isWeightBound_query _ _)
  · show QueryCostAtMost ((liftM (RandomPermutationOracles.query (.inr q)) :
      OracleComp _ _) >>= fun a ↦ pure (a, s)) _ _
    rw [bind_pure_comp]
    exact isWeightBound_map _ (isWeightBound_query _ _)
  · exact isWeightBound_map _ ((isWeightBound_liftM_probComp _ (fun _ ↦ rfl) _).mono
      (Nat.zero_le _))
  · exact isWeightBound_map _ ((isWeightBound_liftM_probComp _ (fun _ ↦ rfl) _).mono
      (Nat.zero_le _))

/-! ## The candidate in the experiment -/

/-- **The experiment's candidate is the candidate of its outcome, keys and log.** -/
theorem candidate_of_mem_support (A : ComposedAdversary k PK Req Resp)
    {z : ExperimentOutcome × (Fin k → PK) × RequestLog k Req Resp × Option (Fin k × F) × Bool}
    (hz : z ∈ support
      (composedExperiment scheme k guest decoder extractor raws deployedVerify A)) :
    z.2.2.2.1 =
      candidate scheme k guest decoder extractor raws deployedVerify z.1 z.2.1 z.2.2.1 := by
  have h := support_simulateQ_run'_subset _ _ _ hz
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
  obtain ⟨⟨⟨⟨⟨program, input⟩, proof⟩, pks, log, edges⟩, transcript⟩, -, accepted, -, v, -, rfl⟩ :=
    h
  rfl

/-! ## The theorem -/

/-- **The conditional composition theorem.** For a guest program, its decoder program and a
straight-line extractor with `AggregateSound`, a signature scheme with multi-key SUF-CMA security
over `π_h` (`MultiKeyStronglyUnforgeable`, up to `maxKeys` keys and `n` signatures per key), and
an adversary against `1 ≤ k ≤ maxKeys` honest keys that makes at most `Q ≤ 2^128` calls of `π`,
`q_h` of `π_h` and `n` requests to each key: if the extractor reads the transcript only through
its permutation queries, every raw signature of a witness holding a statement is accepted by the
deployed verification (`hraws`), and the deployed Keccak's verification behaves like the ideal one
for this adversary up to `δ` (`KeccakVerificationLikeIdeal`), then the verifier accepts a proof
of the guest program on the digest of a statement whose deferred claim holds, and the extracted
execution's decoding does not explain the statement, or explains it with a witness holding a raw
signature under an honest key that wins against that key's transcript, with probability at most
the knowledge-soundness bound plus `δ` plus `k · (q_h + slack + k) · 2^-bits`. -/
theorem composed_sound [Inhabited F] {maxKeys n slack bits : ℕ}
    (hagg : AggregateSound guest decoder extractor)
    (hmk : MultiKeyStronglyUnforgeable scheme maxKeys n slack bits)
    (hk1 : 1 ≤ k) (hk : k ≤ maxKeys) (A : ComposedAdversary k PK Req Resp) (Q qh : ℕ)
    (hQ : ∀ pks, QueryCostAtMost (A pks) piCost Q) (hQ' : Q ≤ 2 ^ 128)
    (hqh : ∀ pks, QueryCostAtMost (A pks) piHCost qh)
    (hn : ∀ pks j, QueryCostAtMost (A pks) (requestToKey j) n)
    (hext : ExtractorReadsPermutationQueries extractor)
    (hraws : ∀ bytecode seed s w, NodeRelation bytecode seed s w →
      ∀ r ∈ raws w, deployedVerify r.1 r.2 = true)
    {δ : ℝ≥0∞} (hδ : KeccakVerificationLikeIdeal scheme k guest decoder extractor raws
      deployedVerify A δ) :
    Pr{let z ← composedExperiment scheme k guest decoder extractor raws deployedVerify A}[
      ∃ statement : NodeStatement,
        z.1.accepted ∧ z.1.program = guest ∧
        publicInputDigest z.1.input = statementDigest (deployedSeed guest) statement ∧
        statement.deferredClaim.HoldsWithShape (bytecodeWords guest) ∧
        ((¬ ∃ execution, ∃ decoding : SeedStatementAndWitness,
            extractor z.1.program z.1.input z.1.transcript z.1.proof = some execution ∧
            Cost.outputWithin decoder guestWitnessDecoderSizeBound
              (guestWitnessDecoderBudget execution)
              (Cost.encodeGuestWitnessDecoderInput z.1.program execution) =
                some (Cost.encodeValue decoding) ∧
            ExplainsStatement guest statement decoding) ∨
          ∃ execution, ∃ decoding : SeedStatementAndWitness,
            extractor z.1.program z.1.input z.1.transcript z.1.proof = some execution ∧
            Cost.outputWithin decoder guestWitnessDecoderSizeBound
              (guestWitnessDecoderBudget execution)
              (Cost.encodeGuestWitnessDecoderInput z.1.program execution) =
                some (Cost.encodeValue decoding) ∧
            decoding.seed = deployedSeed guest ∧ decoding.statement = statement ∧
            NodeRelation (bytecodeWords guest) (deployedSeed guest) statement decoding.witness ∧
            ∃ r ∈ raws decoding.witness, ∃ j, r.1 = z.2.1 j ∧
              scheme.winningCondition (keyLog j z.2.2.1) r.2 = true)] ≤
      ((Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256) + δ +
        (k : ℝ≥0∞) * ((qh : ℝ≥0∞) + slack + k) * (2 : ℝ≥0∞)⁻¹ ^ bits := by
  set ex := composedExperiment scheme k guest decoder extractor raws deployedVerify A with hex
  -- the first event: `AggregateSound`'s
  let E1 : ExperimentOutcome → Prop := fun outcome ↦ ∃ statement : NodeStatement,
    outcome.accepted ∧ outcome.program = guest ∧
    publicInputDigest outcome.input = statementDigest (deployedSeed guest) statement ∧
    statement.deferredClaim.HoldsWithShape (bytecodeWords guest) ∧
    ¬ ∃ execution, ∃ decoding : SeedStatementAndWitness,
      extractor outcome.program outcome.input outcome.transcript outcome.proof = some execution ∧
      Cost.outputWithin decoder guestWitnessDecoderSizeBound
        (guestWitnessDecoderBudget execution)
        (Cost.encodeGuestWitnessDecoderInput outcome.program execution) =
          some (Cost.encodeValue decoding) ∧
      ExplainsStatement guest statement decoding
  have h1 : Pr{let z ← ex}[E1 z.1] ≤ (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
      5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
    rw [← prEvent_map ex (·.1) E1, (composed_outcome_evalDistEq scheme k guest decoder extractor
      raws deployedVerify A).prEvent_eq E1]
    exact hagg _ Q (honest_cost scheme k A Q hQ) hQ'
  -- the third event: the forger's win
  have h3 : Pr{let z ← ex}[z.2.2.2.1.isSome ∧ z.2.2.2.2 = true] ≤
      (k : ℝ≥0∞) * ((qh : ℝ≥0∞) + slack + k) * (2 : ℝ≥0∞)⁻¹ ^ bits := by
    rw [← prEvent_map ex (fun z ↦ (z.2.2.2.1, z.2.2.2.2)) (fun c ↦ c.1.isSome ∧ c.2 = true),
      (composed_evalDistEq_jointGame scheme k guest decoder extractor raws deployedVerify hext
        A).prEvent_eq]
    refine (prob_jointGame_le scheme k guest decoder extractor raws deployedVerify
      (⟨0, hk1⟩, default) A).trans ?_
    exact hmk k hk1 hk qh _
      (forger_permutationCost scheme k guest decoder extractor raws deployedVerify _ A qh hqh)
      (forger_requestCost scheme k guest decoder extractor raws deployedVerify _ A n hn)
  -- the split
  refine (prEvent_mono_of_support ex _ (fun z ↦ E1 z.1 ∨ (z.2.2.2.1.isSome ∧ z.2.2.2.2 = false) ∨
    (z.2.2.2.1.isSome ∧ z.2.2.2.2 = true)) fun z hz h ↦ ?_).trans ?_
  · obtain ⟨statement, hacc, hprog, hdig, hshape, hD1 | ⟨execution, decoding, hextract, hout,
      hseed, hst, hrel, r, hr, j, hj, hwin⟩⟩ := h
    · exact Or.inl ⟨statement, hacc, hprog, hdig, hshape, hD1⟩
    · right
      have hr' : (z.2.1 j, r.2) ∈ raws decoding.witness := by
        rw [← hj]
        exact hr
      have hver : deployedVerify (z.2.1 j) r.2 = true := by
        rw [← hj]
        exact hraws _ _ _ _ hrel r hr
      have hc : (candidate scheme k guest decoder extractor raws deployedVerify z.1 z.2.1
          z.2.2.1).isSome := by
        unfold candidate
        split_ifs with hne
        · rfl
        · exact absurd ⟨j, r.2, hprog, execution, decoding, hextract, hout, hseed,
            by rw [hst]; exact hdig, by rw [hst]; exact hshape, by rw [hst]; exact hrel, hr', hver,
            hwin⟩ hne
      rw [candidate_of_mem_support scheme k guest decoder extractor raws deployedVerify A hz]
      cases z.2.2.2.2 <;> simp [hc]
  · calc _ ≤ Pr{let z ← ex}[E1 z.1] + Pr{let z ← ex}[(z.2.2.2.1.isSome ∧ z.2.2.2.2 = false) ∨
          (z.2.2.2.1.isSome ∧ z.2.2.2.2 = true)] := prEvent_or_le _ _ _
      _ ≤ Pr{let z ← ex}[E1 z.1] + (Pr{let z ← ex}[z.2.2.2.1.isSome ∧ z.2.2.2.2 = false] +
          Pr{let z ← ex}[z.2.2.2.1.isSome ∧ z.2.2.2.2 = true]) := by
        gcongr
        exact prEvent_or_le _ _ _
      _ ≤ _ := by
        rw [← add_assoc]
        exact add_le_add (add_le_add h1 hδ) h3

end Common.Compose

/-- info: 'Common.Compose.composed_sound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Common.Compose.composed_sound
