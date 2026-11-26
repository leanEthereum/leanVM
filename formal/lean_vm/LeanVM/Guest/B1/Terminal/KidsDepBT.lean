/-
  LeanVM.Guest.B1.Terminal.KidsDepBT

  `KidsDepB`'s lift with the node's shape exposed: a flat function with dependent callees, each
  within its bound, is complete within its bound by a node whose `j`-th entered callee is a call of
  its `j`-th name within its `j`-th bound (`Budget.FlatShape`).
-/

module

public import LeanVM.Guest.B1.Terminal.KidsDepB
public import LeanVM.Guest.Budget.FlatShape
public import LeanVM.Guest.Budget.Bounded
public import LeanVM.Guest.B1.Tables.FlatAtT

/-!
# Dependent callees within their bounds, by name

`kidsAt_length`: the callees on the results have one entry per callee.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem kidsAt_length : ∀ (ks : List KidD) (prev outs : List (List E × Layout)),
    outs.length = ks.length → (kidsAt ks prev outs).length = ks.length
  | [], _, _, _ => by simp [kidsAt]
  | _ :: _, _, [], h => by simp at h
  | _ :: ks, prev, _ :: outs, h => by
    simp only [kidsAt, List.length_cons, kidsAt_length ks _ outs (by simpa using h)]

end
end LeanVM.Guest.B1
