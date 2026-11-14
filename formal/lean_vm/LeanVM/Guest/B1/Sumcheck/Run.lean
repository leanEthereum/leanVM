/-
  LeanVM.Guest.B1.Sumcheck.Run

  The sumcheck functions' meanings are the Spec programs they mirror, run on the carried sponge.
-/

module

public import LeanVM.Guest.B1.Sumcheck.MeaningP
public import LeanVM.Guest.B1.Common.Run

/-!
# The sumcheck rounds as Spec runs

* `runsTo_roundPolyNone`, `runsTo_roundPolySome`: `sumcheckRoundPoly` reads its coefficients,
  absorbing each, its grind zero bits (`runsTo_grind0`).
* `sumcheck_round4_run`: `MeaningSumcheckRound4`'s values are `sumcheck claim 4 [none]`.
* `gkrRun_run`: `gkrRun` is `sumcheck claim 5 (es.map some)`, the rounds of `gkrStep 2`.
* `batchRounds_run`: `bsRun` is `Node.batchRounds` on a sponge it carries.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A grind of zero bits is no step. -/
theorem runsTo_grind0 {bits : ℕ} (h : bits = 0) (s : Fs) :
    RunsTo (VerifierProgram.grindProofOfWork bits) s [] () s := by
  subst h
  exact runsTo_ret () s

/-- A plain round polynomial whose grind is zero bits (every deployed count, `count ≤ 9`): the
constant, then the coefficients from `c2`, each absorbed. -/
theorem runsTo_roundPolyNone (s : Fs) (claim c : E) (tail : List E) (count : ℕ)
    (h : tail.length = count - 2) (hg : grindingBits (count - 1) = 0) :
    RunsTo (sumcheckRoundPoly count claim none) s (c :: tail)
      (c :: (claim + sumE tail) :: tail) ((s.absorb c dsObserve).absorbAll tail dsObserve) := by
  have h1 := runsTo_readE s c
  have h2 := runsTo_readN (s.absorb c dsObserve) tail
  rw [h] at h2
  refine (h1.bind (f := fun constant ↦ do
      let tail ← VerifierProgram.readScalars (count - 2)
      VerifierProgram.grindProofOfWork (grindingBits (count - 1))
      return constant :: (claim + sumE tail) :: tail)
    (h2.bind (f := fun t ↦ (do
        VerifierProgram.grindProofOfWork (grindingBits (count - 1))
        pure (c :: (claim + sumE t) :: t) : VerifierProgram (List E)))
      ((runsTo_grind0 hg _).bind (f := fun _ ↦
        (pure (c :: (claim + sumE tail) :: tail) : VerifierProgram (List E)))
        (runsTo_ret _ _)))).of_eq rfl ?_ rfl rfl
  simp

/-- An equality-mode round polynomial whose grind is zero bits: the `count - 1` coefficients from
`c1`, each absorbed, the constant derived. -/
theorem runsTo_roundPolySome (s : Fs) (claim e : E) (tail : List E) (count : ℕ)
    (h : tail.length = count - 1) (hg : grindingBits (count - 1 + 1) = 0) :
    RunsTo (sumcheckRoundPoly count claim (some e)) s tail
      ((claim + e * sumE tail) :: tail) (s.absorbAll tail dsObserve) := by
  have h2 := runsTo_readN s tail
  rw [h] at h2
  refine (h2.bind (f := fun t ↦ (do
        VerifierProgram.grindProofOfWork (grindingBits (count - 1 + 1))
        pure ((claim + e * sumE t) :: t) : VerifierProgram (List E)))
      ((runsTo_grind0 hg _).bind (f := fun _ ↦
        (pure ((claim + e * sumE tail) :: tail) : VerifierProgram (List E)))
        (runsTo_ret _ _))).of_eq rfl ?_ rfl rfl
  simp

/-- One round of `sumcheck`: its polynomial, a sample, the rounds after it. -/
theorem runsTo_sumcheck_cons {s s1 s2 : Fs} {claim : E} {count : ℕ} {eq : Option E}
    {eqs : List (Option E)} {xs ys msg pt : List E} {fin : E}
    (h1 : RunsTo (sumcheckRoundPoly count claim eq) s xs msg s1)
    (h2 : RunsTo (sumcheck (polyEval msg s1.squeeze.1) count eqs) s1.squeeze.2 ys (pt, fin) s2) :
    RunsTo (sumcheck claim count (eq :: eqs)) s (xs ++ ys) (s1.squeeze.1 :: pt, fin) s2 := by
  have h := h1.bind (f := fun message ↦ do
      let challenge ← VerifierProgram.sampleChallenge
      let (point, final) ← sumcheck (polyEval message challenge) count eqs
      return (challenge :: point, final))
    ((runsTo_sampleE s1).bind (f := fun challenge ↦ do
      let (point, final) ← sumcheck (polyEval msg challenge) count eqs
      return (challenge :: point, final))
      (h2.bind (f := fun p ↦ (pure (s1.squeeze.1 :: p.1, p.2) : VerifierProgram (List E × E)))
        (runsTo_ret _ _)))
  refine h.of_eq rfl ?_ rfl rfl
  simp

theorem runsTo_sumcheck_nil (s : Fs) (claim : E) (count : ℕ) :
    RunsTo (sumcheck claim count []) s [] ([], claim) s := runsTo_ret _ _

/-- **`sumcheck_round4` is a plain round of `sumcheck`.** -/
theorem sumcheck_round4_run (cap : List E) (c0 c2 c3 claim : E) :
    let s := (⟨cap, []⟩ : Fs).absorbAll [c0, c2, c3] dsObserve
    RunsTo (sumcheck claim 4 [none]) ⟨cap, []⟩ [c0, c2, c3]
      ([s.squeeze.1], polyEval [c0, claim + sumE [c2, c3], c2, c3] s.squeeze.1) s.squeeze.2 := by
  intro s
  have h := runsTo_sumcheck_cons
    (runsTo_roundPolyNone ⟨cap, []⟩ claim c0 [c2, c3] 4 rfl (by decide))
    (runsTo_sumcheck_nil _ (polyEval [c0, claim + sumE [c2, c3], c2, c3]
      (((⟨cap, []⟩ : Fs).absorb c0 dsObserve).absorbAll [c2, c3] dsObserve).squeeze.1) 4)
  exact h.of_eq rfl rfl rfl rfl

/-- **`bsRun` is `Node.batchRounds`** on a sponge the guest carries. -/
theorem batchRounds_run : ∀ (rounds : List (E × E)) (claim : E) (s : Fs) (sp : Sponge),
    s.Carries sp → ∃ sp', (bsRun rounds claim s).2.Carries sp' ∧
      (Node.batchRounds claim rounds).run sp = ((bsRun rounds claim s).1, sp')
  | [], claim, s, sp, h => ⟨sp, h, rfl⟩
  | (g1, gInf) :: rest, claim, s, sp, h => by
    have ha := carries_absorb (carries_absorb h g1 dsObserve) gInf dsObserve
    obtain ⟨e1, e2⟩ := carries_squeeze ha
    obtain ⟨sp', h', hrun⟩ := batchRounds_run rest
      ((gInf * ((s.absorb g1 dsObserve).absorb gInf dsObserve).squeeze.1 +
        (claim + g1 + g1 + gInf)) * ((s.absorb g1 dsObserve).absorb gInf dsObserve).squeeze.1 +
        (claim + g1)) _ _ e2
    refine ⟨sp', h', ?_⟩
    set X := Id.run (Compile.absorb (m := Id) keccakF1600
      (Id.run (Compile.absorb (m := Id) keccakF1600 sp g1 dsObserve)) gInf dsObserve) with hX
    set c := (Id.run (Compile.squeeze (m := Id) keccakF1600 X)).1 with hc
    have key : (Node.batchRounds claim ((g1, gInf) :: rest)).run sp =
        ((c :: ((Node.batchRounds ((gInf * c + (claim + g1 + g1 + gInf)) * c + (claim + g1))
          rest).run (Id.run (Compile.squeeze (m := Id) keccakF1600 X)).2).1.1,
          ((Node.batchRounds ((gInf * c + (claim + g1 + g1 + gInf)) * c + (claim + g1))
          rest).run (Id.run (Compile.squeeze (m := Id) keccakF1600 X)).2).1.2),
          ((Node.batchRounds ((gInf * c + (claim + g1 + g1 + gInf)) * c + (claim + g1))
          rest).run (Id.run (Compile.squeeze (m := Id) keccakF1600 X)).2).2) := rfl
    rw [key, e1, hrun]
    rfl

end
end LeanVM.Guest.B1
