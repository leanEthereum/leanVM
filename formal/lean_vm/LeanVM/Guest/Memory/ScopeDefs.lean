/-
  LeanVM.Guest.Memory.ScopeDefs

  A check of every statement of a body in its context: the atoms and calls every path through the
  blocks it sits in passes.
-/

module

public import LeanVM.Guest.Bridge.PairDefs
public import LeanVM.Guest.Memory.Eval

/-!
# Statements in their context

`spineE ss`: the atoms and calls of a block before the first statement that may return, as events;
a path through the block that falls through or returns has them all (`Memory.spineE_sub`).

`allB p ss ctx`: every statement of `ss`, at any depth, passes `p` in its context, `ctx` then the
spine of each block it sits in, by the recursor (which the kernel reduces faster than structural
recursion). A body is checked as `allB p body (spineE body)`.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Guest.Core
open LeanVM.Guest.Bridge (noRet noRetArms)

@[expose] public section

/-- **The events on every path through a block** that falls through or returns: its atoms and
calls before the first statement that may return. -/
noncomputable def spineE : List Stmt → List Ev
  | .atom a :: ss => .atom a :: spineE ss
  | .call f args rets :: ss => .call f args rets :: spineE ss
  | .callIf .. :: ss => spineE ss
  | .dispatch .. :: ss => spineE ss
  | .ite _ z n :: ss => bif noRet z && noRet n then spineE ss else []
  | .match_ _ arms :: ss => bif noRetArms arms then spineE ss else []
  | _ => []

/-- Every statement of a statement passes `p` in its context, by the recursor. -/
noncomputable def allS (p : List Ev → Stmt → Bool) (s : Stmt) : List Ev → Bool :=
  Stmt.rec (motive_1 := fun _ ↦ List Ev → Bool) (motive_2 := fun _ ↦ List Ev → Bool)
    (motive_3 := fun _ ↦ List Ev → Bool)
    (fun a ctx ↦ p ctx (.atom a))
    (fun c z n hz hn ctx ↦ p ctx (.ite c z n) && hz (ctx ++ spineE z) && hn (ctx ++ spineE n))
    (fun x arms ha ctx ↦ p ctx (.match_ x arms) && ha ctx)
    (fun f args rets ctx ↦ p ctx (.call f args rets)) (fun c f args ctx ↦ p ctx (.callIf c f args))
    (fun x fs args rets ctx ↦ p ctx (.dispatch x fs args rets)) (fun vs ctx ↦ p ctx (.ret vs))
    (fun _ ↦ true) (fun _ _ hs hss ctx ↦ hs ctx && hss ctx)
    (fun _ ↦ true) (fun a _ ha has ctx ↦ ha (ctx ++ spineE a) && has ctx) s

/-- **Every statement of a block passes `p` in its context**, `ctx` then the spine of each block
it sits in. -/
noncomputable def allB (p : List Ev → Stmt → Bool) (ss : List Stmt) : List Ev → Bool :=
  Stmt.rec_1 (motive_1 := fun _ ↦ List Ev → Bool) (motive_2 := fun _ ↦ List Ev → Bool)
    (motive_3 := fun _ ↦ List Ev → Bool)
    (fun a ctx ↦ p ctx (.atom a))
    (fun c z n hz hn ctx ↦ p ctx (.ite c z n) && hz (ctx ++ spineE z) && hn (ctx ++ spineE n))
    (fun x arms ha ctx ↦ p ctx (.match_ x arms) && ha ctx)
    (fun f args rets ctx ↦ p ctx (.call f args rets)) (fun c f args ctx ↦ p ctx (.callIf c f args))
    (fun x fs args rets ctx ↦ p ctx (.dispatch x fs args rets)) (fun vs ctx ↦ p ctx (.ret vs))
    (fun _ ↦ true) (fun _ _ hs hss ctx ↦ hs ctx && hss ctx)
    (fun _ ↦ true) (fun a _ ha has ctx ↦ ha (ctx ++ spineE a) && has ctx) ss

/-- Every statement of arms passes `p` in its context, each arm's spine added. -/
noncomputable def allA (p : List Ev → Stmt → Bool) (as : List (List Stmt)) : List Ev → Bool :=
  Stmt.rec_2 (motive_1 := fun _ ↦ List Ev → Bool) (motive_2 := fun _ ↦ List Ev → Bool)
    (motive_3 := fun _ ↦ List Ev → Bool)
    (fun a ctx ↦ p ctx (.atom a))
    (fun c z n hz hn ctx ↦ p ctx (.ite c z n) && hz (ctx ++ spineE z) && hn (ctx ++ spineE n))
    (fun x arms ha ctx ↦ p ctx (.match_ x arms) && ha ctx)
    (fun f args rets ctx ↦ p ctx (.call f args rets)) (fun c f args ctx ↦ p ctx (.callIf c f args))
    (fun x fs args rets ctx ↦ p ctx (.dispatch x fs args rets)) (fun vs ctx ↦ p ctx (.ret vs))
    (fun _ ↦ true) (fun _ _ hs hss ctx ↦ hs ctx && hss ctx)
    (fun _ ↦ true) (fun a _ ha has ctx ↦ ha (ctx ++ spineE a) && has ctx) as

end

end LeanVM.Guest.Memory
