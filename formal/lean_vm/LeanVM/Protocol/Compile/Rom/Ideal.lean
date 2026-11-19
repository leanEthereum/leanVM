/-
  LeanVM.Protocol.Compile.Rom.Ideal

  The ideal failure probability of a verifier program against an interactive strategy, every
  challenge uniform and independent.
-/

module

public import LeanVM.Protocol.Compile.Prover
public import Statement.LeanDa

/-!
# The ideal failure probability

`S.failFrom P h g`: the probability that `P`, run from the history `h` against the strategy `S`,
fails, every challenge uniform in `E` and independent of the others (`g`, a challenge already
drawn and waiting, as a proof of work's permutation leaves one). The proof of work is free here:
its challenge is drawn at the `grind` node and taken at the next `sample`.

Where the honest prover's transcript passes every check of a refining program (`traceOk`), its
compiled verifier accepts the honest proof (`runProof_prove_trace`, both in
`LeanVM.Protocol.Compile.Prover`): the only failures left are those `failFrom` counts.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.KeccakHash LeanVM.Protocol
open scoped ENNReal

@[expose] public section

/-! ## The ideal failure probability -/

/-- The uniform average over `E`; irreducible, so that no unification unfolds it into a sum over
the `2^128` elements. -/
@[irreducible] noncomputable def avgE (f : E → ℝ≥0∞) : ℝ≥0∞ := (∑ c : E, f c) / Fintype.card E

/-- `|E|⁻¹`, the probability of one value of a uniform challenge. -/
@[irreducible] noncomputable def epsE : ℝ≥0∞ := (Fintype.card E : ℝ≥0∞)⁻¹

namespace Strategy

open Classical in
/-- **The ideal failure probability** of a program from a history, every challenge uniform in `E`
and independent, the challenge `g` waiting; the verifier's run fails where something is
absorbed while a challenge waits. -/
noncomputable def failFrom (S : Strategy) : VerifierProgram Bool → List Ev → Option E → ℝ≥0∞
  | .ret b, _, _ => if b = true then 0 else 1
  | .fail, _, _ => 1
  | .read k, h, g => if g.isSome then 1 else
      failFrom S (k (S.msg h)) (h ++ [Ev.read (S.msg h)]) none
  | .sample k, h, g => match g with
    | some c => failFrom S (k c) (h ++ [Ev.sample c]) none
    | none => avgE fun c ↦ failFrom S (k c) (h ++ [Ev.sample c]) none
  | .grind b k, h, g => if g.isSome then 1 else
      avgE fun c ↦ failFrom S k (h ++ [Ev.grind b]) (some c)
  | .commit ht w k, h, g => if g.isSome ∨ ¬ WellShaped w (S.word h) then 1 else
      failFrom S k (h ++ [Ev.commit ht w (S.word h)]) none
  | .query i ps k, h, g => match answer h i ps with
    | some rows => failFrom S (k rows) (h ++ [Ev.query rows]) g
    | none => 1

end Strategy

end
end LeanVM.Protocol.Compile
