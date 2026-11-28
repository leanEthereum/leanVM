/-
  LeanVM.Guest.Batch.Transcript

  The batching's transcript over any permutation (`batchWith`) is the verifier program
  `nodeBatchingProgram` run on its stream; so `BatchingSound`.
-/

module

public import LeanVM.Guest.Batch.Rpm
public import LeanVM.Guest.Batch.Node
import LeanVM.Guest.Start

/-!
# The batching's transcript is the verifier program

`batchWith` (`Statement/LeanVmGuestBatching.lean`) makes the calls the verifier program
`nodeBatchingProgram` makes on the batching's stream, over any permutation in any monad
(`batchWith_eq_runBatching`): the program's reads absorb what the transcript observes, the proof of
work and the samples are the same calls, and the final value's read, after a squeeze, calls nothing.
Where `batchWith`'s checks fail it defers nothing; so `BatchingSound` follows from
`batch_node_sound` (`batch_sound_holds`).
-/

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

section Generic

variable {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → m KeccakState)

/-- Absorb scalars, in order. -/
def absorbAll : Sponge → List E → m Sponge
  | sp, [] => pure sp
  | sp, x :: xs => Compile.absorb F sp x dsObserve >>= fun sp ↦ absorbAll sp xs

theorem absorbAll_append (sp : Sponge) (xs ys : List E) :
    absorbAll F sp (xs ++ ys) = absorbAll F sp xs >>= fun sp ↦ absorbAll F sp ys := by
  induction xs generalizing sp with
  | nil => simp [absorbAll]
  | cons x xs ih => simp [absorbAll, ih]

theorem absorbAll_append_bind {β : Type} (sp : Sponge) (xs ys : List E) (k : Sponge → m β) :
    (absorbAll F sp xs >>= fun sp ↦ absorbAll F sp ys >>= k) = absorbAll F sp (xs ++ ys) >>= k := by
  rw [absorbAll_append, bind_assoc]

/-- Absorbing into an empty queue permutes nothing. -/
theorem absorb_nil (st : KeccakState) (x : E) (t : ℕ) :
    Compile.absorb F ⟨st, [], none⟩ x t = pure ⟨st, [(x, t)], none⟩ := by
  simp [Compile.absorb, rateScalars]

/-- Nor into a queue of one. -/
theorem absorb_single (st : KeccakState) (p : E × ℕ) (x : E) (t : ℕ) :
    Compile.absorb F ⟨st, [p], none⟩ x t = pure ⟨st, [p, (x, t)], none⟩ := by
  simp [Compile.absorb, rateScalars]

/-- Scalars absorbed in order keep the waiting challenge. -/
theorem absorbAll_ground : ∀ (sp : Sponge) (xs : List E),
    absorbAll F sp xs =
      (fun sp' : Sponge ↦ ({ sp' with ground := sp.ground } : Sponge)) <$> absorbAll F sp xs
  | ⟨st, pe, g⟩, [] => by simp [absorbAll]
  | sp, x :: xs => by
    simp only [absorbAll]
    rw [absorb_eq_map_ground F sp x, bind_map_left, map_bind]
    exact bind_congr fun sp' ↦ absorbAll_ground _ xs

omit [LawfulMonad m] in
/-- `observe` is `absorb`. -/
theorem observe_run (x : E) (sp : Sponge) :
    (observe F x).run sp = (fun sp' ↦ (PUnit.unit, sp')) <$> Compile.absorb F sp x dsObserve := rfl

omit [LawfulMonad m] in
/-- `sample` is `squeeze`. -/
theorem sample_run' (sp : Sponge) : (sample F).run sp = Compile.squeeze F sp := rfl

omit [LawfulMonad m] in
/-- `grind` is `absorbNonce` and the check. -/
theorem grind_run' (bits : ℕ) (n : E) (sp : Sponge) :
    (grind F bits n).run sp = (fun p ↦ (powOk bits p.1, p.2)) <$> Compile.absorbNonce F sp n := rfl

theorem forIn_observe (xs : List E) (sp : Sponge) :
    (forIn xs PUnit.unit (fun x _ ↦ do
        observe F x
        pure (ForInStep.yield PUnit.unit)) : StateT Sponge m PUnit).run sp =
      (fun sp' ↦ (PUnit.unit, sp')) <$> absorbAll F sp xs := by
  induction xs generalizing sp with
  | nil => simp [absorbAll]
  | cons x xs ih =>
    simp only [List.forIn_cons, StateT.run_bind, observe_run, bind_map_left, pure_bind, bind_assoc,
      absorbAll, map_bind]
    exact bind_congr fun sp' ↦ ih sp'

theorem forIn_children (cs : List ChildClaims) (sp : Sponge) :
    (forIn cs PUnit.unit (fun c _ ↦ do
        forIn (padToRate c.words) PUnit.unit fun x _ ↦ do
          observe F x
          pure (ForInStep.yield PUnit.unit)
        pure (ForInStep.yield PUnit.unit)) : StateT Sponge m PUnit).run sp =
      (fun sp' ↦ (PUnit.unit, sp')) <$> absorbAll F sp (cs.flatMap childCells) := by
  induction cs generalizing sp with
  | nil => simp [absorbAll]
  | cons c cs ih =>
    simp only [List.forIn_cons, StateT.run_bind, forIn_observe, bind_map_left, pure_bind, bind_assoc,
      List.flatMap_cons, absorbAll_append, map_bind, childCells]
    exact bind_congr fun sp' ↦ ih sp'

/-- **The program's reads absorb the scalars read.** -/
theorem run_reads {α : Type} : ∀ (xs : List E) (k : List E → VerifierProgram α) (sp : Sponge)
    (rest : List E) (os : List (List Opening)) (roots : List (Digest × ℕ × ℕ)), sp.ground = none →
    Compile.run F ((VerifierProgram.readScalars xs.length).bind k) ⟨sp, xs ++ rest, os, roots⟩ =
      absorbAll F sp xs >>= fun sp' ↦ Compile.run F (k xs) ⟨sp', rest, os, roots⟩
  | [], k, sp, rest, os, roots, _ => by
    simp [VerifierProgram.readScalars, absorbAll]
  | x :: xs, k, ⟨st, pe, g⟩, rest, os, roots, hg => by
    cases hg
    have e : (VerifierProgram.readScalars (x :: xs).length).bind k =
        .read fun y ↦ (VerifierProgram.readScalars xs.length).bind fun ys ↦ k (y :: ys) := by
      simp only [List.length_cons, VerifierProgram.readScalars, VerifierProgram.readScalar,
        VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind,
        VerifierProgram.bind_assoc]
    rw [e, List.cons_append]
    simp only [Compile.run, absorbAll, bind_assoc]
    rw [absorb_eq_map_ground F ⟨st, pe, none⟩ x, bind_map_left, bind_map_left]
    exact bind_congr fun sp1 ↦ run_reads xs (fun ys ↦ k (x :: ys)) _ rest os roots rfl

/-- **The program's rounds are `batchRounds`**, from a sponge after a squeeze. -/
theorem run_rounds {α : Type} :
    ∀ (K : List E × E → VerifierProgram α) (msgs : List (E × E)) (claim : E) (st : KeccakState)
      (rest : List E) (os : List (List Opening)) (roots : List (Digest × ℕ × ℕ)),
      Compile.run F ((sumcheckRoundsProgram claim msgs.length).bind K)
          ⟨⟨st, [], none⟩, msgs.flatMap (fun g ↦ [g.1, g.2]) ++ rest, os, roots⟩ =
        (batchRounds F claim msgs).run ⟨st, [], none⟩ >>= fun p ↦
          Compile.run F (K p.1) ⟨⟨p.2.state, [], none⟩, rest, os, roots⟩
  | K, [], claim, st, rest, os, roots => by
    simp [sumcheckRoundsProgram, batchRounds]
  | K, (g1, gInf) :: msgs, claim, st, rest, os, roots => by
    rw [List.length_cons, sumcheckRoundsProgram_succ]
    simp only [VerifierProgram.readScalar, VerifierProgram.sampleChallenge, VerifierProgram.bind_eq,
      VerifierProgram.pure_eq, VerifierProgram.bind, VerifierProgram.bind_assoc, List.flatMap_cons,
      List.cons_append, List.nil_append]
    simp only [Compile.run, batchRounds, StateT.run_bind, observe_run, sample_run', absorb_nil,
      absorb_single, map_pure, pure_bind, Compile.squeeze, Compile.duplex, bind_assoc]
    refine bind_congr fun st' ↦ ?_
    rw [run_rounds _ msgs _ st' rest os roots]
    simp

end Generic

/-! ## The program -/

section Generic

variable {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → m KeccakState)

open Classical in
/-- **The transcript is the program**: for hints of `log₂ |bytecode|` rounds, the batching's
transcript from a seed defers a claim that holds exactly where the program accepts the stream, call
for call. -/
theorem batchWith_go_eq (seed : KeccakState) {bytecode : List K} (cs : List ChildClaims)
    (h : BatchingHints) (hr : h.sumcheckMessages.length = Nat.log2 bytecode.length) :
    (fun d ↦ decide (∃ c, d = some c ∧ c.HoldsWithShape bytecode)) <$>
        (batchWith.go F cs h).run' ⟨seed, [], none⟩ =
      runProof F (nodeBatchingProgram (DeferredBytecodeClaim.HoldsWithShape bytecode) bytecode cs)
        seed ⟨batchingStream cs h, []⟩ := by
  rw [batchStream_eq]
  unfold runProof nodeBatchingProgram
  simp only [VerifierProgram.bind_eq]
  rw [run_reads F (cellsBeforeChallenge cs) _ ⟨seed, [], none⟩ _ _ _ rfl,
    absorbAll_ground F ⟨seed, [], none⟩, bind_map_left]
  simp only [batchWith.go, StateT.run'_eq, StateT.run_bind, forIn_observe, forIn_children,
    bind_map_left, map_bind]
  rw [show padToRate [gpow cs.length] = childCountCells cs.length from rfl, absorbAll_append_bind,
    show childCountCells cs.length ++ cs.flatMap childCells = cellsBeforeChallenge cs from rfl,
    bind_assoc]
  conv_lhs => rw [absorbAll_ground F ⟨seed, [], none⟩, bind_map_left]
  refine bind_congr fun ⟨st, pe, g⟩ ↦ ?_
  simp only [VerifierProgram.require, ↓reduceIte, VerifierProgram.ret_bind, batchingAfterChildren,
    VerifierProgram.grindProofOfWork, show batchLambdaGrindBits ≠ 0 by decide, ↓reduceIte,
    VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind,
    VerifierProgram.sampleChallenge, VerifierProgram.readScalar]
  simp only [Compile.run, grind_run', Compile.absorbNonce, Compile.duplex, bind_assoc, map_bind,
    pure_bind, bind_map_left]
  refine bind_congr fun sp ↦ bind_congr fun state ↦ ?_
  split
  · simp only [sample_run', Compile.squeeze, StateT.run_bind, pure_bind, map_bind]
    rw [← hr, run_rounds F _ h.sumcheckMessages _ state _ [] [], bind_assoc]
    refine bind_congr fun p ↦ ?_
    simp only [Compile.run, Compile.absorb, rateScalars, List.length_nil,
      show ¬ (0 = 4) by decide, ↓reduceIte, pure_bind]
    split_ifs with h1 h2 h2 <;> simp_all [Compile.run]
  · simp

open Classical in
/-- **The batching over `F` is the program run from its seeding**, where its checks pass. -/
theorem batchWith_eq_runBatching {bytecode : List K} (cs : List ChildClaims) (h : BatchingHints)
    (hc : BatchChecks (Nat.log2 bytecode.length) cs h) :
    (fun d ↦ decide (∃ c, d = some c ∧ c.HoldsWithShape bytecode)) <$>
        batchWith F (Nat.log2 bytecode.length) cs h =
      runBatching F (nodeBatchingProgram (DeferredBytecodeClaim.HoldsWithShape bytecode) bytecode cs)
        ⟨batchingStream cs h, []⟩ := by
  classical
  unfold BatchChecks at hc
  unfold batchWith runBatching
  rw [ite_eq_left hc]
  simp only [map_bind]
  exact bind_congr fun _ ↦ bind_congr fun seed ↦ by
    convert batchWith_go_eq F seed cs h hc.2.1

end Generic

/-! ## The end statement -/

/-- **`BatchingSound`, its event on the outcome's projections**: where its checks pass, the batching
over `π` is the program `batch_node_sound` bounds (`batchWith_eq_runBatching`), at the guest's
bytecode (`2^23` words) and `M = 17`, where `QV = 261` and `31 · 2^-130 ≤ 2^-125`; elsewhere it
defers nothing. -/
theorem batch_sound_aux (A : BatchingAdversary) (Q : ℕ)
    (hA : Common.QueryCostAtMost A Common.permutationCallCost Q) :
    Pr{let outcome ← Common.runWithRandomPermutation (batchingGame A)}[
      (∃ claim ∈ outcome.2, claim.HoldsWithShape (bytecodeWords guestProgram)) ∧
        ¬ ChildClaimsHold (bytecodeWords guestProgram) outcome.1] ≤
      (Q + 2 ^ 9 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 + 5 * (Q + 2 ^ 9 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  unfold batchingGame
  have hb : (bytecodeWords guestProgram).length = 2 ^ 23 := LeanVM.Guest.End.bytecode_length
  have hlog : Nat.log2 (bytecodeWords guestProgram).length = 23 := by rw [hb, Nat.log2_two_pow]
  have hQV : batchingQueryBound (bytecodeWords guestProgram) (maxRecursions + 1) ≤ 511 := by
    rw [batchingQueryBound, hlog]
    decide
  refine le_trans ?_ ((batch_node_sound (M := maxRecursions + 1) (by rw [hlog, hb])
    (by norm_num [maxRecursions]) A hA (hQV.trans (by norm_num))).trans ?_)
  · rw [rpmGame_bind, rpmGame_bind]
    refine prEvent_bind_le_of_pointwise _ _ _ _ _ fun ⟨⟨cs, h⟩, s⟩ ↦ ?_
    dsimp only
    classical
    by_cases hg : BatchChecks (Nat.log2 (bytecodeWords guestProgram).length) cs h
    · rw [← batchWith_eq_runBatching _ cs h hg, bind_map_left]
      refine prEvent_run'_bind_pure_le _ _ _ _ _ _ _ (Or.inl ⟨rfl, fun d hE ↦ ?_⟩)
      obtain ⟨⟨c, hc, hcs⟩, hnot⟩ := hE
      exact ⟨decide_eq_true ⟨c, Option.mem_def.mp hc, hcs⟩, Nat.lt_succ_of_le hg.1, hg.2.2,
        fun hall ↦ hnot fun x hx ↦
          ⟨⟨by rw [(hg.2.2 x hx).1, hlog, hb], (hall x hx).1⟩, (hall x hx).2⟩⟩
    · have e : batchWith Common.queryPermutation (Nat.log2 (bytecodeWords guestProgram).length) cs h =
          pure none := by
        unfold batchWith
        exact ite_eq_right hg
      rw [e, run'_bind_pure, prEvent_map]
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, prEvent_pure_prop]
      simp
  · generalize batchingQueryBound (bytecodeWords guestProgram) (maxRecursions + 1) = QV at hQV
    rw [show max (2 * (maxRecursions + 1) - 3) 8 = 31 by decide]
    have h125 : (2 : ℝ≥0∞)⁻¹ ^ 125 = 32 * (2 : ℝ≥0∞)⁻¹ ^ 130 := by
      have h1 : (32 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 5 = 1 := by
        rw [show (32 : ℝ≥0∞) = 2 ^ 5 by norm_num, ← mul_pow,
          ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
      calc (2 : ℝ≥0∞)⁻¹ ^ 125 = (2 : ℝ≥0∞)⁻¹ ^ 125 * (32 * (2 : ℝ≥0∞)⁻¹ ^ 5) := by
            rw [h1, mul_one]
        _ = 32 * (2 : ℝ≥0∞)⁻¹ ^ 130 := by ring
    have hn : ((Q + QV : ℕ) : ℝ≥0∞) + 1 ≤ (Q : ℝ≥0∞) + 2 ^ 9 := by
      have : Q + QV + 1 ≤ Q + 2 ^ 9 := by rw [show (2 : ℕ) ^ 9 = 512 by norm_num]; omega
      exact_mod_cast this
    have hn' : ((Q + QV : ℕ) : ℝ≥0∞) ≤ (Q : ℝ≥0∞) + 2 ^ 9 := le_self_add.trans hn
    calc _ ≤ ((Q : ℝ≥0∞) + 2 ^ 9) * 32 * (2 : ℝ≥0∞)⁻¹ ^ 130 +
          5 * ((Q : ℝ≥0∞) + 2 ^ 9) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
          gcongr ?_ * ?_ * _ + 5 * ?_ ^ 2 * _
          norm_num
      _ = _ := by rw [h125]; ring

/-- **`BatchingSound`** (`batch_sound_aux`). -/
theorem batch_sound_holds : BatchingSound := by
  dsimp only [BatchingSound]
  intro A Q hA
  refine le_trans (le_of_eq ?_) (batch_sound_aux A Q hA)
  congr 1

end
end LeanVM.Guest.Batch
