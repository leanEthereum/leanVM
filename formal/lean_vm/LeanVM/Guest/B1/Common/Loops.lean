/-
  LeanVM.Guest.B1.Common.Loops

  A `mul_range` loop helper whose body is a block of atoms, then its conditional self-call.
-/

module

public import LeanVM.Guest.B1.Common.Atoms

/-!
# Loops of atoms

A `mul_range` helper (`__loopN`, parameters `x, N, …`) whose body is a block of atoms `A`, then
`callIf (x·g + N) self [x·g, N, …]` and `ret []`, satisfies `loop_iff`'s step with the body's
meaning `∃ σ, params ∧ A holds` (`loop_step_atoms`): the guard and the next call's arguments are
values `A` computes.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

/-- The meaning of a loop body of atoms at the arguments `args`: some valuation takes the
parameters to them and satisfies every atom. -/
def AtomsBody (rd : Reader) (params : List V) (A : List Stmt) (args : List E) : Prop :=
  ∃ σ : Val, params.map σ = args ∧ ∀ a, Stmt.atom a ∈ A → a.Holds rd σ

/-- **A loop of atoms**: its relation at depth `d + 1` is its body's meaning, the guard `x·g + N`
in `K` and, when it is nonzero, the call at `x·g`, when the body computes the guard at `c` and the
call's arguments. -/
theorem loop_step_atoms {P : Core.Program} {rd : Reader} {f : String} {fn : Fn}
    (hf : P.find? f = some fn) {A : List Stmt} {c : ℕ} {args : List V}
    (hb : fn.body = A ++ [.callIf (.n c) f args, .ret []]) (hA : AllAtoms A)
    {x N : E} {rest : List E}
    (hc : ∀ σ : Val, fn.params.map σ = x :: N :: rest → (∀ a, Stmt.atom a ∈ A → a.Holds rd σ) →
      σ (.n c) = x * gen + N ∧ args.map σ = x * gen :: N :: rest) (d : ℕ) :
    P.relN rd (d + 1) f (x :: N :: rest) [] ↔
      AtomsBody rd fn.params A (x :: N :: rest) ∧ IsInK (x * gen + N) ∧
        (x * gen + N ≠ 0 → P.relN rd d f (x * gen :: N :: rest) []) := by
  rw [relN_succ_iff hf, hb]
  constructor
  · rintro ⟨σ, hp, h⟩
    rw [holdsList_append, holdsList_atoms hA] at h
    obtain ⟨hall, hK, hcall, -⟩ := h
    obtain ⟨e1, e2⟩ := hc σ hp hall
    rw [e1] at hK hcall
    rw [e2] at hcall
    exact ⟨⟨σ, hp, hall⟩, hK, hcall⟩
  · rintro ⟨⟨σ, hp, hall⟩, hK, hcall⟩
    obtain ⟨e1, e2⟩ := hc σ hp hall
    refine ⟨σ, hp, ?_⟩
    rw [holdsList_append, holdsList_atoms hA]
    refine ⟨hall, ?_, ?_, rfl⟩
    · rw [e1]; exact hK
    · rw [e1, e2]; exact hcall

end
end LeanVM.Guest.B1
