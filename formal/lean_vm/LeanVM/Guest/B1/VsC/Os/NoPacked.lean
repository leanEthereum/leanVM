/-
  LeanVM.Guest.B1.VsC.Os.NoPacked

  The stacked WHIR opening makes no packed read or draw.
-/

module

public import LeanVM.Guest.B1.VsC.Os.RunF
public import LeanVM.Guest.B1.Whir.Split
public import LeanVM.Guest.B1.Whir.LevelSpec

/-!
# No packed step in the opening

`NoPacked` (`Os/RunF.lean`) of the WHIR opening's programs: the primitives, `sumcheck`,
`sampleQueries`, `foldRounds`, `whirLevelsOpen` and `whirOpen`, so that the carried run follows
the Spec's on them (`runT_of_runId`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Guest.B1.Whir

@[expose] public section

variable {α β : Type}

theorem NoPacked.bind' {p : VerifierProgram α} {f : α → VerifierProgram β} (hp : NoPacked p)
    (hf : ∀ a, NoPacked (f a)) : NoPacked (p >>= f) :=
  NoPacked.bind hp hf

theorem noPacked_pure (a : α) : NoPacked (pure a : VerifierProgram α) := trivial

theorem noPacked_ret (a : α) : NoPacked (VerifierProgram.ret a) := trivial

theorem noPacked_fail : NoPacked (VerifierProgram.fail : VerifierProgram α) := trivial

theorem noPacked_readScalar : NoPacked VerifierProgram.readScalar := fun _ => trivial

theorem noPacked_sampleChallenge : NoPacked VerifierProgram.sampleChallenge := fun _ => trivial

theorem noPacked_readScalars : ∀ n, NoPacked (VerifierProgram.readScalars n)
  | 0 => trivial
  | n + 1 => NoPacked.bind' noPacked_readScalar fun _ =>
      NoPacked.bind' (noPacked_readScalars n) fun _ => trivial

theorem noPacked_sampleChallenges : ∀ n, NoPacked (VerifierProgram.sampleChallenges n)
  | 0 => trivial
  | n + 1 => NoPacked.bind' noPacked_sampleChallenge fun _ =>
      NoPacked.bind' (noPacked_sampleChallenges n) fun _ => trivial

theorem noPacked_grindProofOfWork (bits : ℕ) : NoPacked (VerifierProgram.grindProofOfWork bits) := by
  unfold VerifierProgram.grindProofOfWork
  split
  · exact trivial
  · exact (trivial : True)

theorem noPacked_require (c : Prop) [Decidable c] : NoPacked (VerifierProgram.require c) := by
  unfold VerifierProgram.require
  split <;> exact trivial

theorem noPacked_readCommitment (h w : ℕ) : NoPacked (VerifierProgram.readCommitment h w) :=
  (trivial : True)

theorem noPacked_queryOpenings (i : ℕ) (ps : List ℕ) :
    NoPacked (VerifierProgram.queryOpenings i ps) := fun _ => trivial

theorem noPacked_liftOption (o : Option α) : NoPacked (liftOption o) := by
  cases o <;> exact trivial

theorem noPacked_sumcheckRoundPoly (count : ℕ) (claim : E) (eq : Option E) :
    NoPacked (sumcheckRoundPoly count claim eq) := by
  cases eq with
  | none =>
    exact NoPacked.bind' noPacked_readScalar fun _ => NoPacked.bind' (noPacked_readScalars _) fun _ =>
      NoPacked.bind' (noPacked_grindProofOfWork _) fun _ => trivial
  | some _ =>
    exact NoPacked.bind' (noPacked_readScalars _) fun _ =>
      NoPacked.bind' (noPacked_grindProofOfWork _) fun _ => trivial

theorem noPacked_sumcheck (claim : E) (count : ℕ) :
    ∀ eqs : List (Option E), NoPacked (sumcheck claim count eqs)
  | [] => trivial
  | _ :: eqs => NoPacked.bind' (noPacked_sumcheckRoundPoly _ _ _) fun _ =>
      NoPacked.bind' noPacked_sampleChallenge fun _ =>
        NoPacked.bind' (noPacked_sumcheck _ count eqs) fun _ => trivial

theorem noPacked_sampleQueriesAux (depth : ℕ) :
    ∀ fuel remaining, NoPacked (sampleQueriesAux depth fuel remaining)
  | 0, _ => trivial
  | fuel + 1, remaining => by
    unfold sampleQueriesAux
    split
    · exact trivial
    · exact NoPacked.bind' noPacked_sampleChallenge fun _ =>
        NoPacked.bind' (noPacked_sampleQueriesAux depth fuel _) fun _ => trivial

theorem noPacked_sampleQueries (depth count : ℕ) : NoPacked (sampleQueries depth count) :=
  noPacked_sampleQueriesAux depth count count

theorem noPacked_foldRound (s : WhirState) : NoPacked (foldRound s) :=
  NoPacked.bind' noPacked_readScalar fun _ => NoPacked.bind' noPacked_readScalar fun _ =>
    NoPacked.bind' noPacked_readScalar fun _ => NoPacked.bind' noPacked_readScalar fun _ =>
      NoPacked.bind' (noPacked_grindProofOfWork _) fun _ => NoPacked.bind' noPacked_sampleChallenge fun _ =>
        NoPacked.bind' noPacked_sampleChallenge fun _ => trivial

theorem noPacked_foldRounds : ∀ (n : ℕ) (s : WhirState), NoPacked (foldRounds n s)
  | 0, _ => trivial
  | n + 1, s => NoPacked.bind' (noPacked_foldRound s) fun _ =>
      NoPacked.bind' (noPacked_foldRounds n _) fun _ => trivial

theorem noPacked_whirLevelsOpen (logN laneFolds : ℕ) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState),
      NoPacked (whirLevelsOpen logN laneFolds index levels s)
  | _, [], _ => trivial
  | index, level :: rest, s => by
    unfold whirLevelsOpen
    refine NoPacked.bind' (noPacked_foldRounds _ _) fun r => ?_
    cases rest with
    | nil =>
      exact NoPacked.bind' (noPacked_readScalars _) fun _ =>
        NoPacked.bind' (noPacked_grindProofOfWork _) fun _ =>
        NoPacked.bind' (noPacked_sampleQueries _ _) fun _ =>
        NoPacked.bind' (noPacked_queryOpenings _ _) fun _ =>
        NoPacked.bind' (noPacked_require _) fun _ =>
        NoPacked.bind' (noPacked_sumcheck _ _ _) fun _ => trivial
    | cons next rest' =>
      exact NoPacked.bind' (noPacked_readCommitment _ _) fun _ =>
        NoPacked.bind' (noPacked_readScalars _) fun _ =>
        NoPacked.bind' (noPacked_grindProofOfWork _) fun _ =>
        NoPacked.bind' (noPacked_sampleChallenges _) fun _ =>
        NoPacked.bind' noPacked_readScalar fun _ =>
        NoPacked.bind' (noPacked_grindProofOfWork _) fun _ =>
        NoPacked.bind' (noPacked_sampleQueries _ _) fun _ =>
        NoPacked.bind' noPacked_sampleChallenge fun _ =>
        NoPacked.bind' (noPacked_queryOpenings _ _) fun _ =>
        noPacked_whirLevelsOpen logN laneFolds (index + 1) (next :: rest') _

theorem noPacked_levelNext (logN index : ℕ) (level next : Whir.Level) (s : WhirState)
    (rounds : List FoldRound) : NoPacked (levelNext logN index level next s rounds) :=
  NoPacked.bind' (noPacked_readCommitment _ _) fun _ =>
    NoPacked.bind' (noPacked_readScalars _) fun _ =>
    NoPacked.bind' (noPacked_grindProofOfWork _) fun _ =>
    NoPacked.bind' (noPacked_sampleChallenges _) fun _ =>
    NoPacked.bind' noPacked_readScalar fun _ =>
    NoPacked.bind' (noPacked_grindProofOfWork _) fun _ =>
    NoPacked.bind' (noPacked_sampleQueries _ _) fun _ =>
    NoPacked.bind' noPacked_sampleChallenge fun _ =>
    NoPacked.bind' (noPacked_queryOpenings _ _) fun _ => trivial

theorem noPacked_levelLast (logN laneFolds index : ℕ) (level : Whir.Level) (s : WhirState)
    (rounds : List FoldRound) : NoPacked (levelLast logN laneFolds index level s rounds) :=
  NoPacked.bind' (noPacked_readScalars _) fun _ =>
    NoPacked.bind' (noPacked_grindProofOfWork _) fun _ =>
    NoPacked.bind' (noPacked_sampleQueries _ _) fun _ =>
    NoPacked.bind' (noPacked_queryOpenings _ _) fun _ =>
    NoPacked.bind' (noPacked_require _) fun _ =>
    NoPacked.bind' (noPacked_sumcheck _ _ _) fun _ => trivial

theorem noPacked_whirOpen (logN logInvRate : ℕ) (target : E) :
    NoPacked (whirOpen logN logInvRate target) :=
  NoPacked.bind' (noPacked_liftOption _) fun _ => noPacked_whirLevelsOpen _ _ _ _ _

end
end LeanVM.Guest.B1.Tables
