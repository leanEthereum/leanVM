/-
  LeanVM.Guest.B1.Digest.PlacedLib

  What the placed completeness of the claim lists' digests shares: the walk through a branch
  between straight runs, `list_split` placed, pure singletons.
-/

module

public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Digest.CompleteSmall
import LeanVM.Guest.StmtsAppend

/-!
# Placed completeness of the claim lists, the shared part

* `walk_ite`: a straight run, a branch whose taken arm falls through, a straight run and a `ret`
  walk the run's events, the condition, the arm's events, then the run's.
* `pure_one`: a function whose body places nothing and calls only itself is pure on its own.
* `list_split_leafOk`, `list_split_pure`: `list_split` is a leaf without loads, pure on its own.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (LowDef CompleteAtD Returns)
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **A branch between straight runs**: its taken arm's events after the condition. -/
theorem walk_ite (σ : Val) (post : List Stmt) (hpost : post.all Main.Stmt.straight = true)
    (c : V) (z n : List Stmt) (vs : List V) (esb : List Ev)
    (hb : (if σ c = 0 then walk σ z else walk σ n) = .fall esb) : ∀ pre : List Stmt,
    pre.all Main.Stmt.straight = true →
    walk σ (pre ++ .ite c z n :: (post ⧺ [.ret vs])) =
      .ret (pre.flatMap (Main.slEvs σ) ++ .inK c :: (esb ++ post.flatMap (Main.slEvs σ))) vs
  | [], _ => by
    rw [List.nil_append, walk, walk1, hb, Main.walk_straight σ vs post hpost]
    rfl
  | s :: pre, hpre => by
    simp only [List.all_cons, Bool.and_eq_true] at hpre
    rw [List.cons_append, walk, walk_ite σ post hpost c z n vs esb hb pre hpre.2,
      Main.walk1_straight σ s hpre.1, Out.seq, Out.pre, List.flatMap_cons, List.append_assoc]

/-- A function whose body places nothing and calls only itself is pure on its own. -/
theorem pure_one {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hb : Stmt.pureList [f] fn.body = true) : coreProgram.PureIn [f] := by
  intro g hg fn' hf'
  rw [List.mem_singleton] at hg
  subst hg
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  exact hb

/-- An atom other than a load. -/
def noLoad : Atom → Bool
  | .load .. => false
  | _ => true

theorem loads_none {σ : Val} {es : List Ev} (h : ∀ e ∈ es, Lift.EvLeafOk noLoad e) :
    loadAddrs σ es = [] := by
  refine List.filterMap_eq_nil_iff.mpr fun e he => ?_
  have hok := h e he
  cases e with
  | atom a =>
    cases a with
    | load => simp [Lift.EvLeafOk, noLoad] at hok
    | _ => rfl
  | _ => rfl

set_option maxRecDepth 100000 in
theorem list_split_leafOk : Lift.Stmt.leafOkList noLoad (fn% «list_split»).body = true :=
  by decide +kernel

theorem list_split_pure : coreProgram.PureIn ["list_split"] :=
  Lift.pureIn_of_leafOk find_list_split list_split_leafOk

/-! ## The events of a body with a dispatch -/

section Es3

variable (σ : Val) (B C : List Ev) (g : String) (a r : List V)

theorem es3_allocs : allocs σ (B ++ .call g a r :: C) = allocs σ B ++ allocs σ C := by
  simp [allocs, List.filterMap_append, List.filterMap_cons, Ev.alloc?]

theorem es3_allocDsts : allocDsts (B ++ .call g a r :: C) = allocDsts B ++ allocDsts C := by
  simp [allocDsts, List.filterMap_append, List.filterMap_cons, Ev.allocDst?]

theorem es3_addrs : addrs (B ++ .call g a r :: C) = addrs B ++ addrs C := by
  simp [addrs, List.filterMap_append, List.filterMap_cons, Ev.addr?]

theorem es3_loads : loadAddrs σ (B ++ .call g a r :: C) = loadAddrs σ B ++ loadAddrs σ C := by
  simp [loadAddrs, List.filterMap_append, List.filterMap_cons, Ev.loadAddr?]

theorem es3_calls : calls (B ++ .call g a r :: C) = calls B ++ ⟨g, a, r, true⟩ :: calls C := by
  simp [calls, List.filterMap_append, Ev.call?]

end Es3

end
end LeanVM.Guest.B1.Digest
