/-
  LeanVM.Protocol.Whir.Sound.Cut

  The ghost opening cut right after the final polynomial is read: it returns the same trace, on a
  prefix of every history the full one returns on.
-/

module

public import LeanVM.Protocol.Whir.Sound.Spec
public import LeanVM.Protocol.EndToEnd.Sound.Frame

/-!
# The opening, cut at the final polynomial

The agreement-set extractor needs the trace of an accepting run (`WhirTrace`: the rounds, the high
parts, the final polynomial), and reads its challenges off the adversary's permutation queries. An
honest prover need not query the permutations after the final polynomial (the final positions'
are its own business, the last tail challenge it never uses), so the extractor runs the opening
only up to the final polynomial.

* `whirLevelsGF logN fin`: the ghost levels with the final level's step after its rounds a
  parameter; `whirLevelsG` is it at `finFull` (`whirLevelsG_eq`), the cut at `finCut`, which reads
  the final polynomial and returns.
* `verifyWhirCut`, `verifyStackedOpeningCut`: the opening cut at the final polynomial
  (`EndToEnd/Sound/CutXrun.lean` relates its runs to the ghost opening's).
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.Whir
  LeanVM.Protocol.EndToEnd.Sound VerifierProgram

@[expose] public section

/-- **The ghost levels with the final step a parameter**: `fin index level s rounds` runs after the
final level's rounds. -/
def whirLevelsGF (logN : ℕ)
    (fin : ℕ → Whir.Level → WhirState → List FoldRound → VerifierProgram WhirTrace) :
    ℕ → List Whir.Level → WhirState → VerifierProgram WhirTrace
  | _, [], _ => VerifierProgram.fail
  | index, [level], s => foldRounds level.fold s >>= fun r ↦ fin index level r.1 r.2
  | index, level :: next :: rest, s => foldRounds level.fold s >>= fun r ↦
      midTailC logN index level next (fun high s' ↦
        whirLevelsGF logN fin (index + 1) (next :: rest) s' >>= fun tr ↦
          VerifierProgram.ret (.mid r.2 high tr)) r.1 r.2

/-- The full final step: `finalTailG`, then the trace's leaf. -/
def finFull (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) : VerifierProgram WhirTrace :=
  finalTailG logN laneFolds eb index level s rounds >>= fun folded ↦
    VerifierProgram.ret (.final rounds folded)

/-- **The cut final step**: read the final polynomial and return the trace's leaf. -/
def finCut (logN : ℕ) (_ : ℕ) (level : Whir.Level) (s : WhirState) (rounds : List FoldRound) :
    VerifierProgram WhirTrace :=
  readScalars (2 ^ (logN - s.alphas.length) + level.fold) >>= fun folded ↦
    VerifierProgram.ret (.final rounds folded)

theorem whirLevelsG_eq (logN laneFolds : ℕ) (eb : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState),
      whirLevelsG logN laneFolds eb index levels s =
        whirLevelsGF logN (finFull logN laneFolds eb) index levels s
  | _, [], _ => rfl
  | _, [_], _ => rfl
  | index, level :: next :: rest, s => by
    rw [whirLevelsG, whirLevelsGF]
    refine congrArg (Bind.bind (foldRounds level.fold s)) (funext fun r ↦ ?_)
    refine congrArg (fun k ↦ midTailC logN index level next k r.1 r.2) (funext fun high ↦
      funext fun s' ↦ ?_)
    rw [whirLevelsG_eq logN laneFolds eb (index + 1) (next :: rest) s']

/-- `midTailC` is its part before the continuation, then the continuation. -/
def midTailPre (logN index : ℕ) (level next : Whir.Level) (s : WhirState)
    (rounds : List FoldRound) : VerifierProgram (List E × WhirState) :=
  midTailC logN index level next (fun high s' ↦ VerifierProgram.ret (high, s')) s rounds

theorem midTailC_eq_pre {α : Type} (logN index : ℕ) (level next : Whir.Level)
    (k : List E → WhirState → VerifierProgram α) (s : WhirState) (rounds : List FoldRound) :
    midTailC logN index level next k s rounds =
      (midTailPre logN index level next s rounds).bind fun p ↦ k p.1 p.2 := by
  simp only [midTailPre, midTailC, VerifierProgram.bind_eq, VerifierProgram.bind_assoc,
    VerifierProgram.ret_bind]

/-- The final level after its final polynomial: the query group and the tail, as in
`finalTailG`. -/
def finalTailRest (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) (folded : List E) : VerifierProgram Unit :=
  grindProofOfWork Whir.queryGrindingBits >>= fun _ ↦
  (sampleQueries (logN - s.alphas.length + level.logInvRate) level.queries >>= fun qs ↦
    queryOpenings index qs >>= fun words ↦
    VerifierProgram.require ((List.zip qs words).all fun (qq, row) ↦
      foldRow (lanesOf index row) (K.ofBits qq) rounds =
        novelEval folded (subspaceAt (logN - s.alphas.length) (K.ofBits qq)))) >>= fun _ ↦
  sumcheck s.claim 3 (List.replicate (logN - s.alphas.length) none) >>= fun r ↦
  VerifierProgram.require (s.glued.foldl
      (fun weight glued ↦ weight + glued.scalar * glued.weightAt ((s.alphas ++ r.1).drop glued.foldStart))
      (eb ((s.alphas ++ r.1).drop laneFolds ++ (s.alphas ++ r.1).take laneFolds)) *
    multilinearEval (folded.take (2 ^ (logN - s.alphas.length))) r.1 = r.2)

/-- The rest of the final level, given the trace's leaf. -/
def finRest (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) : WhirTrace → VerifierProgram Unit
  | .final _ folded => finalTailRest logN laneFolds eb index level s rounds folded
  | .mid _ _ _ => VerifierProgram.fail

/-- **The full final step is the cut one, then the rest returning the same trace.** -/
theorem finFull_eq (logN laneFolds : ℕ) (eb : List E → E) (index : ℕ) (level : Whir.Level)
    (s : WhirState) (rounds : List FoldRound) :
    finFull logN laneFolds eb index level s rounds =
      (finCut logN index level s rounds).bind fun tr ↦
        (finRest logN laneFolds eb index level s rounds tr).bind fun _ ↦ VerifierProgram.ret tr := by
  simp only [finFull, finCut, finalTailG, finRest, finalTailRest, VerifierProgram.bind_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

/-- `verifyWhirG` cut at the final polynomial (where its weight is not yet read). -/
def verifyWhirCut (logN logInvRate : ℕ) (target : E) : VerifierProgram WhirTrace :=
  liftOption (Whir.ladder logN logInvRate) >>= fun config ↦
    whirLevelsGF logN (finCut logN) 0 config ⟨target, [], []⟩

/-- `verifyStackedOpeningG` cut at the final polynomial. -/
def verifyStackedOpeningCut (stackLog logInvRate : ℕ) (claims : List StackClaim) :
    VerifierProgram WhirTrace :=
  (VerifierProgram.require (StackedOk claims)).bind fun _ ↦ VerifierProgram.sampleChallenge.bind fun c ↦
    verifyWhirCut stackLog logInvRate (dot (powers c claims.length) (claims.map (·.2)))

end
end LeanVM.Protocol.Whir.Sound
