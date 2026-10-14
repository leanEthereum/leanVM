import Whir.SupportedCandidateFolding
import Whir.ExecutableOOD

/-! Fixed-list row cancellation, charged once before resetting any queries.
The witness list and both full row tables must be fixed before the fold seed.
The event ranges over the actual committed initial list, not extracted choices. -/
namespace Whir.SupportedCandidateExtraction
open Concrete
open scoped BigOperators

variable {F W Q : Type*} [Field F] [Fintype F] [DecidableEq F] [Inhabited F]
    [Fintype Q] [DecidableEq Q] [DecidableEq W] [CharP F 2]

noncomputable def RowCancellation (folds : Nat) (list : Finset W)
    (committed : Q → Array F) (encoded : W → Q → Array F) (seed : Fin folds → F) : Prop :=
  ∃ w ∈ list, ∃ q, committed q ≠ encoded w q ∧
    Concrete.mle (committed q) (Array.ofFn seed) =
      Concrete.mle (encoded w q) (Array.ofFn seed)

omit [DecidableEq Q] [DecidableEq W] in
open Classical in
/-- One nonzero multilinear difference per fixed witness and domain coordinate.
For Root0's six folds this is exactly L*N*6/|E|, rather than L² or a
post-extraction union over adversarially chosen witnesses. -/
theorem rowCancellation_probability (folds : Nat) (list : Finset W)
    (committed : Q → Array F) (encoded : W → Q → Array F)
    (committedShape : ∀ q, (committed q).size = 2 ^ folds)
    (encodedShape : ∀ w ∈ list, ∀ q, (encoded w q).size = 2 ^ folds) :
    Soundness.uniformProb (Finset.univ.filter (RowCancellation folds list committed encoded)) ≤
      (list.card : ℚ) * Fintype.card Q * ((folds : ℚ) / Fintype.card F) := by
  classical
  let events (i : list × Q) : Finset (Fin folds → F) := Finset.univ.filter fun seed =>
    committed i.2 ≠ encoded i.1 i.2 ∧
      Concrete.mle (committed i.2) (Array.ofFn seed) =
        Concrete.mle (encoded i.1 i.2) (Array.ofFn seed)
  have equal : Finset.univ.filter (RowCancellation folds list committed encoded) =
      Finset.univ.biUnion events := by
    ext seed
    simp [RowCancellation, events]
  rw [equal]
  calc
    _ ≤ ∑ i, Soundness.uniformProb (events i) := Soundness.union_bound events
    _ ≤ ∑ _i : list × Q, ((folds : ℚ) / Fintype.card F) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases different : committed i.2 ≠ encoded i.1 i.2
      · simpa [events, different] using ExecutableOOD.mle_collision_probability
          (committed i.2) (encoded i.1 i.2) (committedShape i.2)
          (encodedShape i.1 i.1.2 i.2) different
      · simp [events, different, Soundness.uniformProb]
        positivity
    _ = _ := by simp [Fintype.card_prod, mul_assoc]

omit [Fintype F] [Fintype Q] [DecidableEq Q] [DecidableEq W] [CharP F 2] in
/-- Outside the charged event, equality of the folded scalar forces literal
row equality for EVERY coordinate and EVERY member of the fixed initial list. -/
theorem rowEquality_of_not_cancellation (folds : Nat) (list : Finset W)
    (committed : Q → Array F) (encoded : W → Q → Array F) (seed : Fin folds → F)
    (safe : ¬ RowCancellation folds list committed encoded seed)
    (w : W) (member : w ∈ list) (q : Q)
    (equal : Concrete.mle (committed q) (Array.ofFn seed) =
      Concrete.mle (encoded w q) (Array.ofFn seed)) : committed q = encoded w q := by
  by_contra different
  exact safe ⟨w, member, q, different, equal⟩

def committedRow (input : CausalGame.Public) (q : Fin (blockLength input.config)) : Array E :=
  Array.ofFn fun lane : Fin (laneCount input.config) =>
    E.ofK (InitialCandidates.fullRow input.config input.lanes input.root lane q)

def witnessRow (input : CausalGame.Public) (w : CausalGame.Witness input.config input.lanes)
    (q : Fin (blockLength input.config)) : Array E :=
  Array.ofFn fun lane : Fin (laneCount input.config) =>
    (encode (input.config.logN - input.config.folds[0]!) input.config.rates[0]!
      (Array.ofFn (CandidateFolding.unpack true (laneCount input.config) (width input.config)
        (CausalGame.paddedWitness input.config input.lanes w) lane)))[q.val]!

noncomputable def initialRowCancellation (input : CausalGame.Public)
    (seed : Fin input.config.folds[0]! → E) : Prop :=
  RowCancellation input.config.folds[0]!
    (InitialCandidates.witnesses input.config input.lanes input.root)
    (committedRow input) (witnessRow input) seed

open Classical in
theorem production_rowCancellation_probability (profile : ParameterBounds.Profile)
    (lanes : Nat) (root : CausalGame.BaseOracle) (claims : Array CausalGame.Claim) :
    let input := ExecutionShapes.Input profile lanes root claims
    Soundness.uniformProb (Finset.univ.filter (initialRowCancellation input)) ≤
      (2 ^ 32 : ℚ) * blockLength input.config * ((input.config.folds[0]! : ℚ) / 2 ^ 192) := by
  dsimp only
  let input := ExecutionShapes.Input profile lanes root claims
  have bound := rowCancellation_probability input.config.folds[0]!
    (InitialCandidates.witnesses input.config input.lanes input.root)
    (committedRow input) (witnessRow input) (by intro q; simp [committedRow])
    (by intro w hw q; simp [witnessRow])
  rw [FieldModel.card_E] at bound
  simp only [Nat.cast_pow, Nat.cast_ofNat] at bound
  apply bound.trans
  simp only [Fintype.card_fin]
  gcongr
  exact_mod_cast InitialCandidates.production_witnesses_card profile lanes root

#print axioms rowCancellation_probability
#print axioms rowEquality_of_not_cancellation
end Whir.SupportedCandidateExtraction
