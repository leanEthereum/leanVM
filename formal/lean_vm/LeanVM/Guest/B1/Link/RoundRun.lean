/-
  LeanVM.Guest.B1.Link.RoundRun

  A plain sum-check round with its grind, as a run on the carried sponge.
-/

module

public import LeanVM.Guest.B1.Common.Run
public import LeanVM.Protocol.Verifier.Deferred

/-!
# A sum-check round as a run

`runsTo_sumcheck_round`: one round of `sumcheck claim count (none :: rest)` reads `c0` and the
`count - 2` tail coefficients, absorbing each, grinds `grindingBits (count - 1)` (its nonce read
unless zero bits) and samples `y`: on the carried sponge it is `Fs.absorbAll` then
`Fs.grindSqueeze`, whatever the grind (`runsTo_grindSample`); then the rest from the claim
`polyEval [c0, claim + Σ tail, tail…] y`.
-/

namespace LeanVM.Guest.B1.Link

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **One plain round of `sumcheck`**, its grind included. -/
theorem runsTo_sumcheck_round (s : Fs) (claim c0 : E) (tail : List E) (count : ℕ)
    (htail : tail.length = count - 2) (n : E) {rest : List (Option E)}
    (hok : ((s.absorb c0 dsObserve).absorbAll tail dsObserve).GrindOk (grindingBits (count - 1)) n)
    {ys pt : List E} {fin : E} {s2 : Fs}
    (h2 : RunsTo (sumcheck (polyEval (c0 :: (claim + sumE tail) :: tail)
        (((s.absorb c0 dsObserve).absorbAll tail dsObserve).grindSqueeze (grindingBits (count - 1)) n).1)
        count rest)
      (((s.absorb c0 dsObserve).absorbAll tail dsObserve).grindSqueeze (grindingBits (count - 1)) n).2
      ys (pt, fin) s2) :
    RunsTo (sumcheck claim count (none :: rest)) s
      (c0 :: tail ++ grindWords (grindingBits (count - 1)) n ++ ys)
      ((((s.absorb c0 dsObserve).absorbAll tail dsObserve).grindSqueeze
        (grindingBits (count - 1)) n).1 :: pt, fin) s2 := by
  set b := grindingBits (count - 1)
  set s1 := (s.absorb c0 dsObserve).absorbAll tail dsObserve
  set msg := c0 :: (claim + sumE tail) :: tail
  have hg := runsTo_grindSample b s1 n hok
  have e : sumcheck claim count (none :: rest) =
      VerifierProgram.readScalar.bind fun c ↦
        (VerifierProgram.readScalars (count - 2)).bind fun t ↦
          (grindSample b).bind fun y ↦
            (sumcheck (polyEval (c :: (claim + sumE t) :: t) y) count rest).bind fun p ↦
              VerifierProgram.ret (y :: p.1, p.2) := by
    simp only [sumcheck, sumcheckRoundPoly, grindSample, VerifierProgram.bind_eq',
      VerifierProgram.pure_eq', VerifierProgram.bind_assoc', VerifierProgram.ret_bind']
    rfl
  rw [e]
  have h3 : RunsTo ((sumcheck (polyEval msg (s1.grindSqueeze b n).1) count rest).bind fun p ↦
      VerifierProgram.ret ((s1.grindSqueeze b n).1 :: p.1, p.2)) (s1.grindSqueeze b n).2 ys
      ((s1.grindSqueeze b n).1 :: pt, fin) s2 := by
    have := h2.bind (f := fun p ↦ (VerifierProgram.ret ((s1.grindSqueeze b n).1 :: p.1, p.2) :
      VerifierProgram (List E × E))) (runsTo_ret _ _)
    simpa [VerifierProgram.bind_eq'] using this
  have h4 := hg.bind (f := fun y ↦ (sumcheck (polyEval msg y) count rest).bind fun p ↦
      VerifierProgram.ret (y :: p.1, p.2)) h3
  have hr := runsTo_readN (s.absorb c0 dsObserve) tail
  rw [htail] at hr
  have h5 := hr.bind (f := fun t ↦ (grindSample b).bind fun y ↦
      (sumcheck (polyEval (c0 :: (claim + sumE t) :: t) y) count rest).bind fun p ↦
        VerifierProgram.ret (y :: p.1, p.2)) h4
  have h6 := (runsTo_readE s c0).bind (f := fun c ↦ (VerifierProgram.readScalars (count - 2)).bind
      fun t ↦ (grindSample b).bind fun y ↦
        (sumcheck (polyEval (c :: (claim + sumE t) :: t) y) count rest).bind fun p ↦
          VerifierProgram.ret (y :: p.1, p.2)) h5
  refine h6.of_eq rfl ?_ rfl rfl
  simp

end
end LeanVM.Guest.B1.Link
