/-
  LeanVM.Guest.Memory.Size

  The weight of a call tree (a per-function cost summed over its instances, phantoms free), and
  bounds on the weight and on the words allocated, uniform over the valid trees of a function.
-/

module

public import LeanVM.Guest.Memory.Retemp

/-!
# Weights of call trees

`Tree.weight ω t` sums `ω f` over the instances of `t` that run (`node`s), a phantom costing
nothing: with `ω` the instructions a function's frame executes at most, it bounds the trace's
length, and `Tree.total` the memory. `WeightLe P ω f B` and `TotalLe P fs f B` bound them over
every valid tree of `f`, by a function of the arguments. Re-choosing the temporaries changes
neither (`weight_retemp`, `total_retemp`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

mutual
/-- **The weight of a call tree**: `ω f` per instance that runs. -/
def Tree.weight (ω : String → ℕ) : Tree → ℕ
  | .node f _ _ kids => ω f + Tree.weightKids ω kids
  | .phantom .. => 0

/-- The weight of a list of call trees. -/
def Tree.weightKids (ω : String → ℕ) : List Tree → ℕ
  | [] => 0
  | k :: ks => k.weight ω + Tree.weightKids ω ks
end

/-- Every valid tree of `f` on `args`, its `HeapBuf`s its paths', weighs at most `B args`. -/
def WeightLe (P : Core.Program) (ω : String → ℕ) (f : String) (B : List E → ℕ) : Prop :=
  ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = f → t.Valid P rd args rets →
    t.BufsOk P → t.weight ω ≤ B args

/-- Every valid tree of `f` on `args`, its `HeapBuf`s its paths', allocates at most `B args` words
(`Tree.Valid` leaves the sizes free, `Tree.BufsOk` fixes them). -/
def TotalLe (P : Core.Program) (fs : String → ℕ) (f : String) (B : List E → ℕ) : Prop :=
  ∀ (rd : Reader) (t : Tree) (args rets : List E), t.name = f → t.Valid P rd args rets →
    t.BufsOk P → t.total fs ≤ B args

variable {P : Core.Program} {fs : String → ℕ} {ν : ℕ → String → Val → V → E} {ω : String → ℕ}

mutual
/-- **Re-choosing the temporaries keeps the weight.** -/
theorem weight_retemp : ∀ (t : Tree) (fp : ℕ), (t.retemp P fs ν fp).weight ω = t.weight ω
  | .node f σ bufs kids, fp => by
      rw [retemp_node, Tree.weight, Tree.weight, weightKids_retempKids kids _
        (by rw [length_kidPos, List.length_map])]
  | .phantom .., fp => by rw [retemp_phantom]

theorem weightKids_retempKids : ∀ (ks : List Tree) (ps : List ℕ), ps.length = ks.length →
    Tree.weightKids ω (Tree.retempKids P fs ν ps ks) = Tree.weightKids ω ks
  | [], _, _ => by rw [retempKids_nil]
  | _ :: _, [], h => absurd h (by simp)
  | k :: ks, p :: ps, h => by
      rw [retempKids_cons, Tree.weightKids, Tree.weightKids, weight_retemp k p,
        weightKids_retempKids ks ps (by simpa using h)]
end

end
end LeanVM.Guest.Memory
