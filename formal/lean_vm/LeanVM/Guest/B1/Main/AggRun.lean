/-
  LeanVM.Guest.B1.Main.AggRun

  The batching program (`Batch.nodeBatchingProgram`) run on the sponge the guest carries: it
  accepts the stream of the children's claims and the hints when the carried sponge's proof of
  work passes and its final check holds.
-/

module

public import LeanVM.Guest.B1.Common.Run
public import LeanVM.Guest.B1.Sumcheck.MeaningP
public import LeanVM.Guest.BatchConsts
public import LeanVM.Guest.WithHashBridge

/-!
# The batching program, on the carried sponge

* `aggS0`: the batching seed's capacity, nothing waiting; `aggAbs cs`: after the count's and the
  children's cells (`cellsBeforeChallenge`); `aggN cs n`: the permutation that absorbs the proof of
  work's nonce `n`; `aggCols cs n`: the `SPLIT_LOG` column challenges squeezed after `λ`, the
  nonce permutation's challenge, and the sponge after them; `aggRun cs h`: the sumcheck's
  challenges and final claim (`bsRun`) on the lambdas' and columns' batched claim.
* `runsTo_rounds`: `sumcheckRoundsProgram` on the carried sponge is `bsRun`.
* `runBatching_of_carried`: the batching program, run on the stream of the children and the hints,
  accepts with outcome `d` when the nonce's proof of work passes, the hints have
  `deferredVariableCount bytecode` rounds, the sumcheck's final claim is the hinted value times the
  batched weight, and `d` is the sumcheck's challenges with the hinted value.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest.B1

@[expose] public section

/-- The batching's initial sponge, carried: the seed's capacity, nothing waiting. -/
def aggS0 : Fs := ⟨capOf batchSeed, []⟩

theorem carries_aggS0 : aggS0.Carries ⟨batchSeed, [], none⟩ := ⟨rfl, rfl, rfl⟩

/-- The sponge after the batching's words. -/
def aggAbs (cs : List ChildClaims) : Fs := aggS0.absorbAll (Batch.cellsBeforeChallenge cs) dsObserve

/-- The permutation that absorbs the batching's grinding nonce `n`. -/
def aggN (cs : List ChildClaims) (n : E) : KeccakState := (aggAbs cs).nonceState n

/-- The column challenges, squeezed after `λ`, and the sponge after them. -/
def aggCols (cs : List ChildClaims) (n : E) : List E × Fs :=
  (⟨capOf (aggN cs n), []⟩ : Fs).squeezeN splitLog

/-- The lambdas: the powers of the nonce permutation's challenge `λ`. -/
def aggLam (cs : List ChildClaims) (n : E) : List (E × E) :=
  Batch.lambdaPowers (challengeOf (aggN cs n)) cs.length

/-- The sumcheck's run: its challenges and final claim, and the sponge after it. -/
def aggRun (cs : List ChildClaims) (h : BatchingHints) : (List E × E) × Fs :=
  bsRun h.sumcheckMessages
    (Batch.batchedClaim cs (aggLam cs h.lambdaGrindNonce) (aggCols cs h.lambdaGrindNonce).1)
    (aggCols cs h.lambdaGrindNonce).2

/-- **A check passes**. -/
theorem runsTo_require {c : Prop} {_ : Decidable c} (hc : c) (s : Fs) :
    RunsTo (VerifierProgram.require c) s [] () s := by
  intro sp hs rest os roots
  refine ⟨sp, hs, ?_⟩
  simp only [VerifierProgram.require, hc, ↓reduceIte, List.nil_append]
  rfl

/-- **The batching sumcheck's rounds on the carried sponge are `bsRun`.** -/
theorem runsTo_rounds : ∀ (rounds : List (E × E)) (claim : E) (s : Fs),
    RunsTo (Batch.sumcheckRoundsProgram claim rounds.length) s
      (rounds.flatMap fun g ↦ [g.1, g.2]) (bsRun rounds claim s).1 (bsRun rounds claim s).2
  | [], claim, s => runsTo_ret _ _
  | (g1, gInf) :: rest, claim, s => by
    rw [List.length_cons, Batch.sumcheckRoundsProgram_succ]
    have h1 := runsTo_readE s g1
    have h2 := runsTo_readE (s.absorb g1 dsObserve) gInf
    have h3 := runsTo_sampleE ((s.absorb g1 dsObserve).absorb gInf dsObserve)
    have h4 := runsTo_rounds rest (Batch.sumcheckRoundPolynomial claim (g1, gInf)
      ((s.absorb g1 dsObserve).absorb gInf dsObserve).squeeze.1)
      ((s.absorb g1 dsObserve).absorb gInf dsObserve).squeeze.2
    have h := h1.bind (f := fun g1 => do
      let gInfinity ← VerifierProgram.readScalar
      let challenge ← VerifierProgram.sampleChallenge
      let rest ← Batch.sumcheckRoundsProgram
        (Batch.sumcheckRoundPolynomial claim (g1, gInfinity) challenge) rest.length
      return (challenge :: rest.1, rest.2))
      (h2.bind (f := fun gInfinity => do
        let challenge ← VerifierProgram.sampleChallenge
        let rest ← Batch.sumcheckRoundsProgram
          (Batch.sumcheckRoundPolynomial claim (g1, gInfinity) challenge) rest.length
        return (challenge :: rest.1, rest.2))
        (h3.bind (f := fun challenge => do
          let rest ← Batch.sumcheckRoundsProgram
            (Batch.sumcheckRoundPolynomial claim (g1, gInf) challenge) rest.length
          return (challenge :: rest.1, rest.2))
          (h4.bind (f := fun r => (pure (_ :: r.1, r.2) : VerifierProgram (List E × E)))
            (runsTo_ret _ _))))
    refine h.of_eq rfl (by simp) ?_ rfl
    simp only [bsRun, Batch.sumcheckRoundPolynomial]

/-- The batching stream's parts: the count's and the children's cells, the nonce, the rounds, the
final value. -/
theorem batchingStream_eq (cs : List ChildClaims) (h : BatchingHints) :
    Batch.batchingStream cs h = Batch.cellsBeforeChallenge cs ++
      ([h.lambdaGrindNonce] ++ (h.sumcheckMessages.flatMap (fun g ↦ [g.1, g.2]) ++
        [h.finalBytecodeValue])) := by
  simp only [Batch.batchingStream, Batch.lambdaGrindNonceCells_eq, Batch.sumcheckRoundCells_eq,
    List.append_assoc]

/-- **The batching program accepts on the carried sponge**: when the nonce's proof of work passes,
the hints have `deferredVariableCount bytecode` rounds, and the sumcheck's final claim is the
hinted value times the batched weight at its challenges, the program accepts the stream with the
outcome the challenges and the hinted value. -/
theorem runBatching_of_carried {cs : List ChildClaims} {h : BatchingHints} {bytecode : List K}
    (hpow : powOk Batch.batchLambdaGrindBits (Keccak.lane (aggN cs h.lambdaGrindNonce) 2) = true)
    (hrl : h.sumcheckMessages.length = deferredVariableCount bytecode)
    (hfin : (aggRun cs h).1.2 = h.finalBytecodeValue *
      Batch.batchedBytecodeWeight cs (aggLam cs h.lambdaGrindNonce)
        (aggCols cs h.lambdaGrindNonce).1 (aggRun cs h).1.1) :
    Batch.runBatching (m := Id) keccakF1600
      (Batch.nodeBatchingProgram (· = ⟨(aggRun cs h).1.1, h.finalBytecodeValue⟩) bytecode cs)
      ⟨Batch.batchingStream cs h, []⟩ = true := by
  have hb : Batch.batchLambdaGrindBits ≠ 0 := by decide
  -- the program, step by step
  have hread := runsTo_readN aggS0 (Batch.cellsBeforeChallenge cs)
  have hgrind := runsToG_grind hb (aggAbs cs) h.lambdaGrindNonce hpow
  have hlam := runsFromG_sample (capOf (aggN cs h.lambdaGrindNonce))
    (challengeOf (aggN cs h.lambdaGrindNonce))
  have hcol := runsTo_sampleN splitLog (⟨capOf (aggN cs h.lambdaGrindNonce), []⟩ : Fs)
  have hrnd := runsTo_rounds h.sumcheckMessages
    (Batch.batchedClaim cs (aggLam cs h.lambdaGrindNonce) (aggCols cs h.lambdaGrindNonce).1)
    (aggCols cs h.lambdaGrindNonce).2
  rw [hrl] at hrnd
  have hfv := runsTo_readE (aggRun cs h).2 h.finalBytecodeValue
  have hafter : RunsTo (Batch.batchingAfterChildren (· = ⟨(aggRun cs h).1.1, h.finalBytecodeValue⟩)
      bytecode cs) (aggAbs cs)
      ([h.lambdaGrindNonce] ++ ([] ++ ([] ++ (h.sumcheckMessages.flatMap (fun g ↦ [g.1, g.2]) ++
        ([h.finalBytecodeValue] ++ ([] ++ [])))))) true
      (((aggRun cs h).2.absorb h.finalBytecodeValue dsObserve)) := by
    refine hgrind.bindFrom (hlam.bind (hcol.bind (hrnd.bind (hfv.bind
      (RunsTo.bind (xs := []) (a := ()) ?_ (runsTo_ret _ _))))))
    exact runsTo_require ⟨hfin, rfl⟩ _
  have hall : RunsTo (Batch.nodeBatchingProgram (· = ⟨(aggRun cs h).1.1, h.finalBytecodeValue⟩)
      bytecode cs) aggS0
      (Batch.cellsBeforeChallenge cs ++ ([] ++ ([h.lambdaGrindNonce] ++ ([] ++ ([] ++
        (h.sumcheckMessages.flatMap (fun g ↦ [g.1, g.2]) ++ ([h.finalBytecodeValue] ++
          ([] ++ []))))))))
      true (((aggRun cs h).2.absorb h.finalBytecodeValue dsObserve)) := by
    refine hread.bind (RunsTo.bind (xs := []) (a := ()) ?_ hafter)
    exact runsTo_require rfl _
  have hstream : Batch.cellsBeforeChallenge cs ++ ([] ++ ([h.lambdaGrindNonce] ++ ([] ++ ([] ++
      (h.sumcheckMessages.flatMap (fun g ↦ [g.1, g.2]) ++ ([h.finalBytecodeValue] ++
        ([] ++ []))))))) = Batch.batchingStream cs h := by
    rw [batchingStream_eq]; simp
  obtain ⟨sp', -, hrun⟩ := (hall.of_eq rfl hstream rfl rfl) ⟨batchSeed, [], none⟩ carries_aggS0 [] [] []
  rw [Guest.Batch.runBatching_deployed]
  simp only [Batch.runBatchingWithHash, runProofWithHash]
  show (match runId _ ⟨⟨keccakF1600 (seedInput (keccak256 batchingLabel) (Vector.replicate 4 0)),
      [], none⟩, Batch.batchingStream cs h, [], []⟩ with
    | some (true, s) => s.stream.isEmpty && s.openings.isEmpty
    | _ => false) = true
  rw [show keccakF1600 (seedInput (keccak256 batchingLabel) (Vector.replicate 4 0)) = batchSeed
    from rfl, ← List.append_nil (Batch.batchingStream cs h), hrun]
  rfl

end
end LeanVM.Guest.B1.Main
