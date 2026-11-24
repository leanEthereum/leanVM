/-
  LeanVM.Guest.Ref.Verified

  A reference function bundled with its meaning and the proof that it means it.
-/

module

public import LeanVM.Guest.Ref.Link

/-!
# Verified reference functions

`Verified Const X` bundles a source function's reference function at each value of its
compile-time arguments (`ref`), the relation it should denote, stated semantically (`Meaning`),
and the proof that it does (`sem`), in the style of Clean's `FormalCircuit`. Consumers read a
reference function only through its `Meaning`: `Verified.rel_iff_of_check` is what a link check
(`LeanVM.Guest.Ref.Link`) of a compiled specialization gives, in every program that finds it.
-/

namespace LeanVM.Guest.Ref

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.B1

@[expose] public section

/-- A reference function family and its meaning: `ref c` at the compile-time arguments `c` relates
the memory, the arguments and the return words exactly as `Meaning c` does. -/
structure Verified (Const X : Type) where
  /-- The reference function at the compile-time arguments. -/
  ref : Const → Func X
  /-- What it computes, on the memory, the arguments and the return words. -/
  Meaning : Const → Reader → List E → List E → Prop
  /-- The reference function's relation is its meaning. -/
  sem : ∀ c rd args rets, (ref c).Sem rd args rets ↔ Meaning c rd args rets

/-- **A compiled function a map links to a verified reference function means what the reference
function means**, in every program that finds it. -/
theorem Verified.rel_iff_of_check {Const X : Type} [DecidableEq X] [Coded X] (V : Verified Const X) {c : Const}
    {P : Program} {rd : Reader} {name : String} {f : Fn} {m : Map X}
    (hf : P.find? name = some f) (h : m.check f (V.ref c) = true) (args rets : List E) :
    P.Rel rd name args rets ↔ V.Meaning c rd args rets := by
  rw [rel_iff_sem hf]
  exact (Map.check_sem_iff h args rets).trans (V.sem c rd args rets)

end
end LeanVM.Guest.Ref
