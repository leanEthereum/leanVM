module

public import LeanDa.RpmArg
public import Common.PiOnly
public import Common.WithHash
public import LeanDa.WithHashBridge

@[expose] public section

/-!
# LeanDA's end theorems in the statement's model: `π` and `π⁻¹`, nothing else

The statement's games (`Statement/LeanDa.lean`) have every party query coins, `π` and `π⁻¹` and
hash with Keccak-256 over `π` (`Common.keccak256OverPermutation`); the proofs hold them with a Keccak-256 oracle
(`LeanDa.HashOracle`). An argument of the statement's model is one with the hash oracle that never
queries it (`liftArg`), and so is an adversary (`liftAdv`); each game of the statement is the game
with the hash oracle, against them, with each hash call expanded into its permutation calls
(`posBindingGame_eq_expand`, `codeBindingGame_eq_expand`, `ksGame_eq_expand`), so with the same
distribution (`Common.runK_expand`) and the same number of permutation calls
(`Common.isWeightBound_expand_iff`). The extractor reads the transcript with the hash oracle
through its queries of the statement's model (`projLog`), the adversary's whole transcript when it
never queries the hash oracle (`projLog_embedLog`).

This module is part of the instantiation of Benedikt Wagner's framework for erasure code
commitments (`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec Common PqDas
open scoped ENNReal

namespace LeanDa

/-! ## Arguments, adversaries and transcripts -/

section Lift

variable {Stmt Wit Crs Proof : Type}

/-- **An argument of the statement's model, with the hash oracle**: its queries embedded. -/
def liftArg (ps : OracleArgument Stmt Wit Crs Proof) : NarkRpmH Stmt Wit Crs Proof where
  setup := ps.setup
  prove crs stmt wit := simulateQ embed (ps.prove crs stmt wit)
  verify crs stmt proof := simulateQ embed (ps.verify crs stmt proof)

/-- An adversary of the statement's model, with the hash oracle. -/
def liftAdv {X β : Type} (A : X → OracleComp RandomPermutationOracles β) : X → OracleComp KSpecH β :=
  fun x ↦ simulateQ embed (A x)

/-- The answers of a permutation `π` to an embedded query are its answers. -/
theorem permImplH_compose_embed (π : Equiv.Perm LeanVM.Semantics.KeccakState) :
    permImplH π ∘ₛ embed = oraclesFromPermutation π := by
  funext t
  rcases t with n | q | q <;> rfl

theorem simulateQ_permImplH_liftArg (π : Equiv.Perm LeanVM.Semantics.KeccakState)
    (ps : OracleArgument Stmt Wit Crs Proof) (crs : Crs) (stmt : Stmt) (wit : Wit) :
    simulateQ (permImplH π) ((liftArg ps).prove crs stmt wit >>= (liftArg ps).verify crs stmt) =
      simulateQ (oraclesFromPermutation π) (ps.prove crs stmt wit >>= ps.verify crs stmt) := by
  simp only [liftArg, ← simulateQ_bind, ← QueryImpl.simulateQ_compose, permImplH_compose_embed]

/-- A query of the statement's model and its answer, among those with the hash oracle. -/
def embedEntry : (t : RandomPermutationOracles.Domain) × RandomPermutationOracles.Range t → (t : KSpecH.Domain) × KSpecH.Range t
  | ⟨.inl n, u⟩ => ⟨.inl n, u⟩
  | ⟨.inr q, u⟩ => ⟨.inr (.inr q), u⟩

/-- A query with the hash oracle and its answer, if it is one of the statement's model. -/
def projEntry : (t : KSpecH.Domain) × KSpecH.Range t → Option ((t : RandomPermutationOracles.Domain) × RandomPermutationOracles.Range t)
  | ⟨.inl n, u⟩ => some ⟨.inl n, u⟩
  | ⟨.inr (.inl _), _⟩ => none
  | ⟨.inr (.inr q), u⟩ => some ⟨.inr q, u⟩

/-- A transcript of the statement's model, with the hash oracle. -/
def embedLog (l : OracleQueryLog) : TranscriptH := l.map embedEntry

/-- **A transcript with the hash oracle, read in the statement's model**: its hash queries
dropped. -/
def projLog (l : TranscriptH) : OracleQueryLog := l.filterMap projEntry

theorem projEntry_embedEntry (e : (t : RandomPermutationOracles.Domain) × RandomPermutationOracles.Range t) :
    projEntry (embedEntry e) = some e := by
  rcases e with ⟨n | q, u⟩ <;> rfl

theorem projLog_embedLog (l : OracleQueryLog) : projLog (embedLog l) = l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [projLog, embedLog, List.map_cons, List.filterMap_cons, projEntry_embedEntry] at ih ⊢
    rw [ih]

/-- An extractor of the statement's model, reading a transcript with the hash oracle. -/
def liftExt (ext : StraightLineExtractor Stmt Wit Crs Proof) : ExtractorRpmH Stmt Wit Crs Proof :=
  fun crs stmt proof log ↦ ext crs stmt proof (projLog log)

end Lift

/-! ## The oracle programs, expanded -/

theorem expand_hK (a : List UInt8) : simulateQ expand (hK a) = keccak256OverPermutation a := by
  simp [hK, expand]

theorem expand_pK (x : LeanVM.Semantics.KeccakState) : simulateQ expand (pK x) = queryPermutation x := by
  simp [pK, expand, queryPermutation]

theorem expand_verifyCellM (r : ℕ) (com : Common.DigestBytes) (p : Fin (r * 128)) (x : Cell)
    (τ : CellOpening) : simulateQ expand (verifyCellMWithHash hK r com p x τ) = verifyCellMWithHash keccak256OverPermutation r com p x τ := by
  rw [verifyCellM_map (fun x ↦ simulateQ expand x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [expand_hK]

theorem expand_relationM {r : ℕ} (root : Common.DigestBytes) (c : Fin (r * 128) → Cell) :
    simulateQ expand (relationMWithHash hK pK root c) = relationMWithHash keccak256OverPermutation queryPermutation root c := by
  simp only [relationMWithHash, simulateQ_bind, simulateQ_pure]
  rw [membershipChallengeM_map (fun x ↦ simulateQ expand x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _), commitCellsM_map (fun x ↦ simulateQ expand x)
    (fun _ ↦ simulateQ_pure _ _) (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [expand_hK, expand_pK]

/-- One logged query, expanded. -/
theorem expand_loggedKH_step (t : RandomPermutationOracles.Domain) (s : OracleQueryLog) :
    simulateQ expand ((simulateQ loggedKH (embed t)).run (embedLog s)) =
      (fun p ↦ (p.1, embedLog p.2)) <$> (loggedOracles t).run s := by
  have hK : (loggedOracles t).run s = (fun u ↦ (u, s ++ [⟨t, u⟩])) <$> liftM (RandomPermutationOracles.query t) := by
    simp [loggedOracles]
  rw [hK, Functor.map_map]
  rcases t with n | q <;>
  · simp only [embed, simulateQ_spec_query]
    rw [run_loggedK_query, simulateQ_map, simulateQ_spec_query]
    simp [expand, embedLog, embedEntry]

/-- **Logging, expanded**: the log of an embedded computation is the embedded log of its
queries. -/
theorem expand_loggedKH {α : Type} (X : OracleComp RandomPermutationOracles α) (s : OracleQueryLog) :
    simulateQ expand ((simulateQ loggedKH (simulateQ embed X)).run (embedLog s)) =
      (fun p ↦ (p.1, embedLog p.2)) <$> (simulateQ loggedOracles X).run s := by
  induction X using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind]
    rw [expand_loggedKH_step, bind_map_left, map_bind]
    congr 1
    funext p
    exact ih p.1 p.2

/-! ## The games, expanded -/

section Games

variable (r : ℕ) {Crs Proof : Type} (ps : LeanDaArgument r Crs Proof)
  (ext : StraightLineExtractor Common.DigestBytes (Fin (r * 128) → Cell) Crs Proof)

omit ps in
theorem expand_liftM_setup {β : Type} (p : ProbComp β) :
    simulateQ expand (liftM p : OracleComp KSpecH β) = liftM p :=
  simulateQ_liftM_of_coins _ (fun _ ↦ rfl) _

/-- **The position-binding game is the game with the hash oracle, expanded.** -/
theorem posBindingGame_eq_expand (A : PositionBindingAdversary r Crs Proof) :
    positionBindingGameWithHash r ps A = simulateQ expand (posBindingGameH r (liftArg ps) (liftAdv A)) := by
  simp only [positionBindingGameWithHash, posBindingGameH, simulateQ_bind, simulateQ_pure, expand_liftM_setup,
    liftAdv, simulateQ_expand_embed, liftArg, expand_verifyCellM]

/-- **The code-binding game is the game with the hash oracle, expanded.** -/
theorem codeBindingGame_eq_expand (A : CodeBindingAdversary r Crs Proof) :
    codeBindingGameWithHash r ps A = simulateQ expand (codeBindingGameH r (liftArg ps) (liftAdv A)) := by
  simp only [codeBindingGameWithHash, codeBindingGameH, simulateQ_bind, simulateQ_pure, expand_liftM_setup,
    liftAdv, simulateQ_expand_embed, liftArg]
  congr 1; funext crs; congr 1; funext out; congr 1; funext ok
  rw [mapM_map (fun x ↦ simulateQ expand x) (fun _ ↦ simulateQ_pure _ _)
    (fun _ _ ↦ simulateQ_bind _ _ _)]
  simp only [expand_verifyCellM]

/-- **The knowledge-soundness game is the game with the hash oracle, expanded**, against the
adversary embedded, the extractor reading the transcript in the statement's model. -/
theorem ksGame_eq_expand (B : KnowledgeSoundnessAdversary Crs Proof) :
    knowledgeSoundnessGameWithHash r ps ext B = simulateQ expand (ksGameH r (liftArg ps) (liftExt ext) (liftAdv B)) := by
  simp only [knowledgeSoundnessGameWithHash, ksGameH, simulateQ_bind, simulateQ_pure, expand_liftM_setup, liftAdv]
  congr 1; funext crs
  have h := expand_loggedKH (B crs) []
  simp only [embedLog, List.map_nil] at h
  rw [h, bind_map_left]
  congr 1; funext out
  simp only [liftArg, simulateQ_expand_embed, liftExt, expand_relationM]
  rw [show projLog (List.map embedEntry out.2) = out.2 from projLog_embedLog out.2]

end Games

/-! ## The end theorems -/

/-- **LeanDA is perfectly complete in the random-permutation model, for every permutation**
(`LeanDaPerfectlyComplete`): the argument with the hash oracle that never queries it
(`liftArg`) is perfectly complete there, and has the same completeness experiment. -/
theorem leanDa_perfectlyComplete_rpmWithHash : PerfectlyCompleteRpmWithHash := by
  intro r π Crs Proof ps hr hps msg p
  have h := leanDa_perfectlyComplete_rpmH r π (liftArg ps) hr (fun π crs hcrs stmt wit hrel ↦ by
    rw [simulateQ_permImplH_liftArg]
    exact hps π crs hcrs stmt wit hrel) msg p
  have e : completenessExpRpmH r π (liftArg ps) msg p = completenessExperimentWithHash r π ps msg p := by
    simp only [completenessExpRpmH, simulateQ_permImplH_liftArg]
    rfl
  rwa [e] at h

/-- **LeanDA is position binding in the random-permutation model** (`LeanDaPositionBinding`): the
game is the game with the hash oracle, expanded, with the same distribution and the same
permutation calls. -/
theorem leanDa_positionBinding_rpmWithHash : PositionBindingRpmWithHash := by
  intro r Crs Proof ps A Q hQ
  rw [posBindingGame_eq_expand, isWeightBound_expand_iff] at hQ
  rw [posBindingGame_eq_expand, runK_expand]
  exact leanDa_positionBinding_rpmH r (liftArg ps) (liftAdv A) Q hQ

/-- **LeanDA is code binding in the random-permutation model, for an argument knowledge sound in
it** (`LeanDaCodeBinding`): the game is the game with the hash oracle, expanded, and the knowledge
soundness the proof uses, of the code-binding adversary's own game (`ksB`), is the statement's
knowledge soundness of the same adversary (`ksGame_eq_expand`). -/
theorem leanDa_codeBinding_rpm_boundWithHash : CodeBindingRpmWithHash := by
  intro r Crs Proof ps ext c k hks _ hrM A Q hQ
  rw [codeBindingGame_eq_expand, isWeightBound_expand_iff] at hQ
  rw [codeBindingGame_eq_expand, runK_expand]
  refine leanDa_codeBinding_rpm_bound_at r (liftArg ps) (liftExt ext) c k (liftAdv A) ?_ hrM Q hQ
  intro q hq hq128
  have e : ksB r (liftAdv A) = liftAdv (fun crs ↦ (fun out ↦ (out.1.1, out.1.2)) <$> A ((), crs)) := by
    funext crs
    simp [ksB, liftAdv, simulateQ_map]
  rw [e, ← isWeightBound_expand_iff, ← ksGame_eq_expand] at hq
  rw [e, ← runK_expand, ← ksGame_eq_expand]
  exact hks _ q hq hq128

/-! The statement's algorithms and games hash with Keccak-256 over the permutation, the forms with
a hash so instantiated (`LeanDa.WithHashBridge`). -/

/-- **LeanDA is perfectly complete in the random-permutation model, for every permutation**
(`LeanDaPerfectlyComplete`). -/
theorem leanDa_perfectlyComplete_rpm : LeanDaPerfectlyComplete :=
  perfectlyCompleteRpm_of_withHash leanDa_perfectlyComplete_rpmWithHash

/-- **LeanDA is position binding in the random-permutation model** (`LeanDaPositionBinding`). -/
theorem leanDa_positionBinding_rpm : LeanDaPositionBinding :=
  positionBindingRpm_of_withHash leanDa_positionBinding_rpmWithHash

/-- **LeanDA is code binding in the random-permutation model, for an argument knowledge sound in
it** (`LeanDaCodeBinding`). -/
theorem leanDa_codeBinding_rpm_bound : LeanDaCodeBinding :=
  codeBindingRpm_of_withHash leanDa_codeBinding_rpm_boundWithHash

end LeanDa
