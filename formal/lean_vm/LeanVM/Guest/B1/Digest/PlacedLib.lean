/-
  LeanVM.Guest.B1.Digest.PlacedLib

  What the placed completeness of the claim lists' digests shares: the walk through a branch
  between straight runs, `list_split` placed, pure singletons.
-/

module

public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.Memory.LiftPure
public import LeanVM.Guest.B1.Digest.CompleteSmall

/-!
# Placed completeness of the claim lists, the shared part

* `walk_ite`: a straight run, a branch whose taken arm falls through, a straight run and a `ret`
  walk the run's events, the condition, the arm's events, then the run's.
* `pure_one`: a function whose body places nothing and calls only itself is pure on its own.
* `list_split_completeAt`: `list_split` (a leaf without loads, its range checks reading below
  `2^20`) is `CompleteAtD` with its split's returns, reading no caller's word.
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
    walk σ (pre ++ .ite c z n :: (post ++ [.ret vs])) =
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

/-- **`list_split` is complete, placed**: its split's returns, no caller's word read. -/
theorem list_split_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {a b c : ℕ}
    (ha : a < bigFramesCap) (hb : b < bigGroups) (hc : c < claimGroup) :
    CompleteAtD fs cert 20 "list_split" [] [gen ^ (claimBig * a + claimGroup * b + c)]
      (Returns [gen ^ a, gen ^ b, gen ^ c]) :=
  Lift.completeAtD_of_relIn list_split_pure (List.mem_singleton_self _) fun rd hl _ =>
    Lift.relIn_of_leaf find_list_split list_split_leafOk
      (fun σ es vs _ hw A hA => by
        have hall : (Out.ret es vs).All (Lift.EvLeafOk noLoad) := by
          have := Lift.walk_leafOk (σ := σ) (fn% «list_split»).body list_split_leafOk
          exact (show walk σ (fn% «list_split»).body = .ret es vs from hw) ▸ this
        rw [loads_none hall] at hA
        exact absurd hA List.not_mem_nil)
      (list_split_complete' rd hl _ _ ⟨a, ha, b, hb, c, hc, rfl, rfl⟩)

/-! ## The events of a branch with a dispatch -/

section Es5

variable (σ : Val) (A B C D : List Ev) (c : V) (g : String) (a r : List V)

theorem es5_allocs : allocs σ (A ++ .inK c :: ((B ++ .call g a r :: C) ++ D)) =
    allocs σ A ++ (allocs σ B ++ (allocs σ C ++ allocs σ D)) := by
  simp [allocs, List.filterMap_append, List.filterMap_cons, List.append_assoc, Ev.alloc?]

theorem es5_allocDsts : allocDsts (A ++ .inK c :: ((B ++ .call g a r :: C) ++ D)) =
    allocDsts A ++ (allocDsts B ++ (allocDsts C ++ allocDsts D)) := by
  simp [allocDsts, List.filterMap_append, List.filterMap_cons, List.append_assoc, Ev.allocDst?]

theorem es5_addrs : addrs (A ++ .inK c :: ((B ++ .call g a r :: C) ++ D)) =
    addrs A ++ (addrs B ++ (addrs C ++ addrs D)) := by
  simp [addrs, List.filterMap_append, List.filterMap_cons, List.append_assoc, Ev.addr?]

theorem es5_loads : loadAddrs σ (A ++ .inK c :: ((B ++ .call g a r :: C) ++ D)) =
    loadAddrs σ A ++ (loadAddrs σ B ++ (loadAddrs σ C ++ loadAddrs σ D)) := by
  simp [loadAddrs, List.filterMap_append, List.filterMap_cons, List.append_assoc, Ev.loadAddr?]

theorem es5_calls : calls (A ++ .inK c :: ((B ++ .call g a r :: C) ++ D)) =
    calls A ++ (calls B ++ (⟨g, a, r, true⟩ :: (calls C ++ calls D))) := by
  simp [calls, List.filterMap_append, List.filterMap_cons, List.append_assoc, Ev.call?]

end Es5

end
end LeanVM.Guest.B1.Digest
