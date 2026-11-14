/-
  LeanVM.Guest.Backend.Sound.Flush

  The parts of the placement walk that only move the state: the trace, the cells of the values
  made before a statement, and the hints.
-/

module

public import LeanVM.Guest.Backend.Sound.Helpers

/-!
# The trace, the cells of new values, the hints

The trace is advice: nothing here gives a fact a core relation is proved from. Reading the trace
(`flushN`, `onAlloc`, `expect`) places values, each once, and may make the product of an address
the next statement wants in a cell (`materialize`, whose instructions keep the pools true); a
hint only queues what the prover is told. So each is a walk of straight-line instructions with
no guarantee (`Spec … True`), whatever the trace holds.
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

variable {κ : ℕ} {Γ : Site κ} {fp : K} {F : VMap Loc} {ctx : Ctx} {α : Type}

/-- One step of a walk of straight-line steps with no guarantee. -/
macro "straight_step" : tactic => `(tactic| first
  | with_reducible exact SpecAt.fail
  | with_reducible exact SpecAt.fail_bind
  | with_reducible exact SpecAt.pure fun _ _ _ => trivial
  | with_reducible exact SpecAt.modify quiet
  | with_reducible exact SpecAt.modifyGet quiet
  | with_reducible refine SpecAt.get_bind ?_
  | with_reducible refine SpecAt.read_bind ?_
  | with_reducible refine SpecAt.peek_bind ?_
  | with_reducible exact SpecAt.lastT (cellOf_spec _)
  | with_reducible exact SpecAt.lastT (cellAt_spec _)
  | with_reducible exact SpecAt.lastT (pointer_spec _ _)
  | with_reducible exact SpecAt.lastT (pushHint_spec _)
  | with_reducible exact SpecAt.lastT (materialize_spec _ _)
  | with_reducible exact SpecAt.lastT (takeRun_spec _)
  | with_reducible exact SpecAt.lastT (bindRun_spec _ _)
  | with_reducible exact SpecAt.lastT advance_spec
  | with_reducible exact SpecAt.lastT fresh_spec
  | with_reducible exact SpecAt.lastT (by apply_assumption)
  | with_reducible refine SpecAt.guard fun _ => ?_
  | with_reducible refine SpecAt.bindTT ?_ fun _ _ => ?_
  | split
  | extract_lets)

/-- A walk of straight-line steps with no guarantee: every step is one, or fails. -/
macro "straight" : tactic => `(tactic| repeat' straight_step)

theorem expect_spec (e : Event → Bool) (what : String) :
    Spec Γ fp F ctx (expect e what) (fun _ => True) := by
  intro st
  unfold expect
  straight

theorem spongeInPlace_spec (vs : List V) (up : List Stmt) :
    Spec Γ fp F ctx (spongeInPlace vs up) (fun _ => True) := by
  intro st
  unfold spongeInPlace
  refine SpecAt.get_bind ?_
  extract_lets srcs
  clear_value srcs
  cases srcs <;> exact SpecAt.pure fun _ _ _ => trivial

theorem onAlloc_spec (vs : List V) (kind : Kind) (up : List Stmt) :
    Spec Γ fp F ctx (onAlloc vs kind up) (fun _ => True) := by
  intro st
  unfold onAlloc
  have h1 := @spongeInPlace_spec κ Γ fp F ctx
  straight

theorem discard_spec {m : P α} {Q : α → Prop} (hm : Spec Γ fp F ctx m Q) :
    Spec Γ fp F ctx (discard m) (fun _ => True) := by
  intro st
  rw [Functor.discard, map_const, Function.comp_apply, map_eq_pure_bind]
  exact SpecAt.bindTT (SpecAt.lastT hm) fun _ _ => SpecAt.pure fun _ _ _ => trivial

/-- **Reading the trace up to the next statement**: values are placed and an address wanted in
a cell is made, whatever the trace holds. -/
theorem flushN_spec (up : List Stmt) :
    ∀ fuel, Spec Γ fp F ctx (flushN up fuel) (fun _ => True)
  | 0 => fun st => SpecAt.pure fun _ _ _ => trivial
  | fuel + 1 => fun st => by
      rw [flushN]
      have h1 := @onAlloc_spec κ Γ fp F ctx
      have h2 := flushN_spec up fuel
      have h3 : ∀ n e, Spec Γ fp F ctx (discard (materialize n e)) (fun _ => True) :=
        fun n e => discard_spec (materialize_spec n e)
      refine SpecAt.peek_bind ?_
      split <;> straight

theorem flush_spec (up : List Stmt) : Spec Γ fp F ctx (flush up) (fun _ => True) := by
  intro st
  unfold flush
  exact SpecAt.read_bind (SpecAt.lastT (flushN_spec up _))

theorem beginStmt_spec (up : List Stmt) : Spec Γ fp F ctx (beginStmt up) (fun _ => True) := by
  intro st
  unfold beginStmt
  exact SpecAt.bindTT (SpecAt.lastT (flush_spec up)) fun _ _ => SpecAt.lastT (expect_spec _ _)

/-! ## Hints -/

theorem destBits_spec (d : Dest) : Spec Γ fp F ctx (destBits d) (fun _ => True) := by
  intro st
  unfold destBits
  straight

theorem optionMapM_spec (o : Option V) : Spec Γ fp F ctx (o.mapM cellOf) (fun _ => True) := by
  intro st
  cases o with
  | none => exact SpecAt.pure fun _ _ _ => trivial
  | some v =>
      rw [Option.mapM, map_eq_pure_bind]
      exact SpecAt.bindTT (SpecAt.lastT (cellOf_spec v)) fun _ _ =>
        SpecAt.pure fun _ _ _ => trivial

set_option maxHeartbeats 400000 in
/-- A hint queues what the prover is told: no relation of the core IR depends on it. -/
theorem placeHint_spec (h : Hint) : Spec Γ fp F ctx (placeHint h) (fun _ => True) := by
  intro st
  unfold placeHint
  have h1 := @destBits_spec κ Γ fp F ctx
  have h2 := @optionMapM_spec κ Γ fp F ctx
  straight

end
end LeanVM.Guest.Backend
