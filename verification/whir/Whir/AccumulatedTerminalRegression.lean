import Whir.AccumulatedTerminalRefinement
import Whir.ProductionTransitions

namespace Whir.AccumulatedTerminalRegression
open Concrete Protocol AccumulatedTerminalRefinement

/-- All 56 production profiles discharge the native subspace recurrence bound;
the profile constructor and its checked dimension ledger are not recopied. -/
theorem production_native_guard (p : ParameterBounds.Profile)
    (i : Fin (ParameterBounds.config p).folds.size) :
    CausalGame.remaining (ParameterBounds.config p) i ≤ 64 := by
  have h := (ProductionTransitions.production_fold_facts p i).1
  omega

theorem production_level_valid (p : ParameterBounds.Profile)
    (i : Fin (ParameterBounds.config p).folds.size) (folds : Array E)
    (oods : Array (Array E)) (qs : Array Nat) (lambda : E)
    (ho : ∀ j < oods.size, oods[j]!.size = CausalGame.remaining (ParameterBounds.config p) i) :
    Valid (level folds (CausalGame.remaining (ParameterBounds.config p) i) oods qs lambda)
      (CausalGame.remaining (ParameterBounds.config p) i) :=
  valid_level folds _ oods qs lambda (production_native_guard p i) ho

private def e (n : Nat) : E := E.ofK (UInt64.ofNat n)
private def caller : Array E := #[e 1, e 7, e 19, e 5, e 42, e 99, e 31, e 11]
private def residual : Array E := #[e 23, e 41]
private def z00 : Array E := #[e 13, e 17]
private def z01 : Array E := #[e 29, e 31]
private def z10 : Array E := #[e 37]
private def qs0 : Array Nat := #[0, 1, 3]
private def qs1 : Array Nat := #[0, 2]

/-- Independent eager dense transitions: fixed source chronology, no source
context compiler and no native basis evaluator are used on this side. -/
private def denseWeight (original : Array E) (lambda0 lambda1 : E) : Array E := Id.run do
  let mut b := foldLane original 4 (e 2)
  b := weightGlue b (eqTable z00) lambda0
  b := weightGlue b (eqTable z01) (lambda0 * lambda0)
  b := weightGlue b (induced 2 qs0 (powers lambda0 qs0.size)) (lambda0 ^ 3)
  b := foldLow b (e 3)
  b := weightGlue b (eqTable z10) lambda1
  b := weightGlue b (induced 1 qs1 (powers lambda1 qs1.size)) (lambda1 * lambda1)
  b := foldLow b (e 5)
  return b

private def dense (lambda0 lambda1 : E) : E :=
  (foldLow residual (e 5))[0]! * (denseWeight caller lambda0 lambda1)[0]!

private def program (lambda0 lambda1 : E) : List Step :=
  levelBatch 2 #[z00, z01] qs0 lambda0 ++ level #[e 3] 1 #[z10] qs1 lambda1

private def native (lambda0 lambda1 : E) : E :=
  let st := record (program lambda0 lambda1) ⟨[e 2], []⟩
  sourceTerminal (Concrete.mle caller (rotatePoint 1 #[e 2, e 3, e 5]))
    st.saved st.ris [e 5] residual

/-- Deliberately wrong coordinate convention. It rotates each saved suffix,
instead of rotating only the caller's full point. -/
private def perLevelRotation (lambda0 lambda1 : E) : E :=
  let saved := save (program lambda0 lambda1) 1
  let wrong := (saved.map fun s => s.beta *
    s.basis.native (([e 2, e 3, e 5].drop s.risStart).rotate 1)).sum
  Concrete.mle residual #[e 5] *
    (Concrete.mle caller (rotatePoint 1 #[e 2, e 3, e 5]) + wrong)

private def checkCase (label : String) (a b : E) : IO Unit := do
  let d := dense a b
  let s := native a b
  unless d == s do throw (IO.userError s!"{label}: dense/native mismatch {repr d} / {repr s}")
  let good : VerifierState E := ⟨denseWeight caller a b, s, ⟨0, 0⟩⟩
  let bad : VerifierState E := { good with claim := s + 1 }
  let yr := Concrete.mle residual #[e 5]
  unless good.checkTerminal yr && !(bad.checkTerminal yr) do
    throw (IO.userError s!"{label}: dense terminal Boolean mismatch")
  IO.println s!"{label}: dense=native={d.toNat}"

#eval do
  checkCase "two levels / three OOD / residual / nonzero glue" (e 7) (e 11)
  checkCase "zero first-level glue" 0 (e 11)
  checkCase "zero second-level glue" (e 7) 0
  checkCase "zero all glue" 0 0
  let wrong := perLevelRotation (e 7) (e 11)
  unless wrong != dense (e 7) (e 11) do
    throw (IO.userError "coordinate-order discriminator failed")
  IO.println s!"per-level rotation rejected: wrong={wrong.toNat}"
  let state := record (program (e 7) (e 11)) ⟨[e 2], []⟩
  let wrongCaller := sourceTerminal (Concrete.mle caller #[e 2, e 3, e 5])
    state.saved state.ris [e 5] residual
  unless wrongCaller != dense (e 7) (e 11) do
    throw (IO.userError "initial top-variable rotation discriminator failed")
  IO.println s!"unrotated caller rejected: wrong={wrongCaller.toNat}"

private def family : Fin 2 → RingPCSGame.FamilyClaim := fun j =>
  if j.val = 0 then ⟨0, #[e 13, e 17], fun _ => 0⟩
  else ⟨4, #[e 19, e 23], fun _ => 0⟩

private def pointClaims : Array RingPCSGame.PointClaim :=
  #[.point 0 #[e 29, e 31] 0, .strided 4 1 1 #[e 37] 0]

private def seed : RingPCSGame.Prefix := (⟨3, 1, 0⟩, fun i => e (i.val + 2))

private theorem family_shape : SuccinctRingWeight.FamilyShape 3 family := by
  intro j
  fin_cases j <;> simp [family]

private theorem point_shapes : ∀ i : Fin pointClaims.size,
    SuccinctPointWeight.Shape 3 pointClaims[i] := by
  decide +kernel

#eval do
  let b := (CausalGame.batchClaims 8 (RingPCSGame.transformedClaims 8 family pointClaims seed) (e 41)).weight
  let d := (foldLow residual (e 5))[0]! * (denseWeight b (e 7) (e 11))[0]!
  let st := record (program (e 7) (e 11)) ⟨[e 2], []⟩
  let original := SuccinctRingGroups.sourceStackWeightAt family pointClaims seed (e 41)
    (rotatePoint 1 #[e 2, e 3, e 5])
  let s := sourceTerminal original st.saved st.ris [e 5] residual
  unless d == s do throw (IO.userError "full ring/point caller accumulated terminal mismatch")
  IO.println s!"full ring family + ordinary/strided points + two levels: dense=native={d.toNat}"

#print axioms AccumulatedTerminalAlgebra.mle_eqTable
#print axioms InitialTerminalRefinement.mle_foldLane_initial
#print axioms AccumulatedTerminalRefinement.levelBatch_weight
#print axioms AccumulatedTerminalRefinement.level_weight
#print axioms AccumulatedTerminalRefinement.save_chronology
#print axioms AccumulatedTerminalRefinement.initial_residual_terminal
#print axioms AccumulatedTerminalRefinement.initial_source_terminal
#print axioms AccumulatedTerminalRefinement.saved_suffix
#print axioms AccumulatedTerminalRefinement.record_chronology
#print axioms AccumulatedTerminalRefinement.source_terminal_acceptance
#print axioms AccumulatedTerminalRefinement.checkTerminal_source
#print axioms AccumulatedTerminalRefinement.stack_terminal_equivalence
#print axioms AccumulatedTerminalRefinement.stack_checkTerminal_source
#print axioms production_level_valid

end Whir.AccumulatedTerminalRegression
