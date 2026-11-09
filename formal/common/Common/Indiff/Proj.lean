module

public import Common.Indiff.Games

@[expose] public section

/-!
# Indifferentiability: exact projections between the games

The combined game's ideal side is the visible game once the full view is forgotten
(`map_run_combIdeal`), and the visible game without the sponge's path queries is the simulator
over path values once the hashed messages and the collision flag are forgotten
(`map_run_visImpl_false`). Both are equalities of oracle computations.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)

/-- The full view's walk makes the queries of `skel`. -/
theorem map_allWalk (used : List (Dg × E) → Bool) (pre : List (Dg × E)) (s : SpState Dg E C)
    (A : PermutationEdges (SpState Dg E C)) (bs : List (Dg × E)) :
    (fun _ ↦ ()) <$> allWalk (Msg := Msg) P used pre s A bs = skel (C := C) P pre bs := by
  induction bs generalizing pre s A with
  | nil => simp [allWalk, skel]
  | cons B bs ih =>
    simp only [allWalk, skel, map_bind]
    refine bind_congr fun v ↦ bind_congr fun u ↦ ?_
    split <;> exact ih _ _ _

/-- One step of the combined game's ideal side, projected to the visible state, is one step of
the visible game with the sponge's path queries. -/
theorem combIdeal_proj (t : (dSpec Msg Dg (SpState Dg E C)).Domain)
    (cs : CState Dg E C Msg) :
    Prod.map id CState.vis <$> (combIdeal P iv t).run cs = (visImpl P iv true t).run cs.vis := by
  rcases t with n | m | x | y
  · simp [combIdeal, combStep, visImpl, CState.vis]
  · simp only [combIdeal, combStep, combHash, visImpl, StateT.run_map, StateT.run_mk,
      map_bind, map_pure, ite_true]
    rw [← map_allWalk P (usedPath P cs.sim.chains cs.hashed) [] iv cs.all (P.pad m)]
    simp only [bind_map_left]
    rfl
  · simp only [combIdeal, combStep, combFwd, visImpl, StateT.run_map, StateT.run_mk,
      map_bind, map_pure]
    rfl
  · simp only [combIdeal, combStep, combInv, visImpl, StateT.run_map, StateT.run_mk,
      map_bind, map_pure]
    rfl

/-- **The combined game's ideal side is the visible game** once the full view is forgotten. -/
theorem map_run_combIdeal {α : Type} (oa : OracleComp (dSpec Msg Dg (SpState Dg E C)) α)
    (cs : CState Dg E C Msg) :
    Prod.map id CState.vis <$> (simulateQ (combIdeal P iv) oa).run cs =
      (simulateQ (visImpl P iv true) oa).run cs.vis :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _ (combIdeal_proj P iv) oa cs

/-- One step of the visible game without path queries, projected to the simulator state, is one
step of the simulator over path values. -/
theorem visImpl_false_proj (t : (dSpec Msg Dg (SpState Dg E C)).Domain)
    (vs : VState Dg E C Msg) :
    Prod.map id Prod.fst <$> (visImpl P iv false t).run vs = (idealTImpl P t).run vs.1 := by
  rcases t with n | m | x | y
  · simp [visImpl, idealTImpl]
  · simp [visImpl, idealTImpl]
  · simp [visImpl, idealTImpl]
  · simp [visImpl, idealTImpl]

/-- **The visible game without path queries is the simulator over path values** once the hashed
messages and the collision flag are forgotten. -/
theorem map_run_visImpl_false {α : Type} (oa : OracleComp (dSpec Msg Dg (SpState Dg E C)) α)
    (vs : VState Dg E C Msg) :
    Prod.map id Prod.fst <$> (simulateQ (visImpl P iv false) oa).run vs =
      (simulateQ (idealTImpl P) oa).run vs.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _ (visImpl_false_proj P iv) oa vs

end Setting

end Common
