/-
  LeanVM.Guest.B1.Place.IsZeroE

  `is_zero`'s valid trees are exact at every node: its limbs hint is forced.
-/

module

public import LeanVM.Guest.Exact.Free
public import LeanVM.Guest.Memory.LiftPure

/-!
# `is_zero`, exact

`is_zero`'s body hints the low limb of its word `w` and checks both it and `(w + lo)·y⁻¹` in `K`
(`split_iff`), so on a valid path the hint is `w`'s low limb: what the executor writes.
`isZero_every_exact`: every valid tree of `is_zero` is exact at every node.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.Lift (anyAtom walk_leafOk calls_nil_of_leafOk)

@[expose] public section

theorem find_is_zero : coreProgram.find? "is_zero" = some Fn.«is_zero».core :=
  coreProgram_find?_at (j := idx% «is_zero») rfl

/-- `is_zero`'s limbs hint. -/
def izHint : Atom := .hint (.limbs (.n 0) [.n 1])

theorem iz_pinned : Stmt.blockNextOk (fun a => isComputed a && !decide (a = izHint)) pinsInverse
    Fn.«is_zero».core.body = true := by
  decide +kernel

theorem iz_leaf : Lift.Stmt.leafOkList anyAtom Fn.«is_zero».core.body = true := by decide +kernel

/-- **A valid path of `is_zero` is exact**: its limbs hint is its word's low limb. -/
theorem iz_events_exact {rd : Reader} {σ : Val} {es : List Ev} {vs : List V}
    (hw : walk σ Fn.«is_zero».core.body = .ret es vs) (hes : ∀ e ∈ es, e.Holds rd σ) :
    ∀ e ∈ es, e.Exact rd σ := by
  refine exact_of_pinned_except iz_pinned hw hes fun a _ ha ↦ ?_
  obtain rfl : a = izHint := of_decide_eq_true ha
  have e : ∃ es', es = .atom izHint :: .atom (.add (.n 2) (.n 0) (.n 1)) ::
      .atom (.const (.n 3) (word 2 1)) :: .atom (.mul (.n 4) (.n 2) (.n 3)) ::
      .atom (.assertInK (.n 1) (.n 4)) :: es' := by
    rw [show Fn.«is_zero».core.body = .atom izHint :: .atom (.add (.n 2) (.n 0) (.n 1)) ::
        .atom (.const (.n 3) (word 2 1)) :: .atom (.mul (.n 4) (.n 2) (.n 3)) ::
        .atom (.assertInK (.n 1) (.n 4)) :: (Fn.«is_zero».core.body.drop 5) from rfl,
      walk, walk, walk, walk, walk] at hw
    simp only [walk1, Out.seq] at hw
    generalize walk σ (Fn.«is_zero».core.body.drop 5) = o at hw
    cases o with
    | fall _ => simp [Out.pre] at hw
    | stuck => simp [Out.pre] at hw
    | ret es' _ =>
      simp only [Out.pre, Out.ret.injEq, List.cons_append, List.nil_append] at hw
      exact ⟨es', hw.1.symm⟩
  obtain ⟨es', rfl⟩ := e
  have h2 : σ (.n 2) = σ (.n 0) + σ (.n 1) := hes (.atom (.add (.n 2) (.n 0) (.n 1))) (by simp)
  have h3 : σ (.n 3) = word 2 1 := hes (.atom (.const (.n 3) (word 2 1))) (by simp)
  have h4 : σ (.n 4) = σ (.n 2) * σ (.n 3) := hes (.atom (.mul (.n 4) (.n 2) (.n 3))) (by simp)
  have h5 : IsInK (σ (.n 1)) ∧ IsInK (σ (.n 4)) := hes (.atom (.assertInK (.n 1) (.n 4))) (by simp)
  rw [h4, h2, h3, word_y_inv] at h5
  have hlo := (split_iff (σ (.n 0)) (σ (.n 1))).mp h5
  show [σ (.n 1)] =
    (List.range 1).map fun j ↦ ofK (if j = 0 then (σ (.n 0)).limb 0 else (σ (.n 0)).limb 1)
  simp [hlo]

/-- **Every valid tree of `is_zero` is exact at every node.** -/
theorem isZero_every_exact {rd : Reader} {t : Tree} {args rets : List E} (hn : t.name = "is_zero")
    (hv : t.Valid coreProgram rd args rets) : t.Every (ExactAt coreProgram rd) := by
  cases t with
  | phantom => exact hv.elim
  | node g σ bufs kids =>
    simp only [Tree.name] at hn
    subst hn
    obtain ⟨fn, hf, -, es, vs, hw, -, hes, hkv⟩ := hv
    rw [find_is_zero, Option.some.injEq] at hf
    subst hf
    rw [Tree.every_node]
    refine ⟨exactAt_of_walk find_is_zero hw (iz_events_exact hw hes), ?_⟩
    have hL : (Out.ret es vs).All (Lift.EvLeafOk anyAtom) := hw ▸ walk_leafOk (σ := σ) _ iz_leaf
    rw [calls_nil_of_leafOk hL] at hkv
    match kids, hkv with
    | [], _ => trivial

end
end LeanVM.Guest.B1
