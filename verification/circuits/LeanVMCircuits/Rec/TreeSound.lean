module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
The statement-bound tests, over the tree.

Every node's circuit has one test bound only with its statement: the reduction's last check, against the values its
statement exposes (the reduced claims), which its own transcript cannot fix. A node's statement words are the next
verifier's claims: its parent's circuit reads a child's statement (its digest, its dense and matrix claims) as claims
on that child, reduces them with its own into its statement, and the root's statement is checked natively.

A tree is its nodes with a root at depth zero, each other node's parent and its depth. At each node, the outcomes `bad v` are those
at which its verifier accepts with a true statement but false input claims: `Bind.sumcheck_test_sound` bounds them for
a certified reduction (a test that holds with the other side the instance's final value, from a false input claim).

`tree_sound`: if at each node off `bad v` a true statement makes its input claims true, each child's statement is
true when its parent's input claims are, and the root's statement is true, then off every node's `bad` every node's
statement and input claims are true. `tree_sound_frac`: the outcomes at which some node's are not are at most the sum
of the nodes' `bad` fractions; `tree_sound_eps`: at most `∑ ε v` when each node's is at most `ε v`.
-/

namespace LeanVMCircuits.Rec.TreeSound

open Finset

variable {α Ω : Type}

/-- A tree's presentation: its nodes, its root, each node's parent and depth. Every node but the root has its parent
among the nodes, one level up, and only the root is at depth zero. -/
structure Tree (α : Type) where
  nodes : Finset α
  root : α
  parent : α → α
  depth : α → ℕ
  root_mem : root ∈ nodes
  depth_root : depth root = 0
  root_of_depth : ∀ v ∈ nodes, depth v = 0 → v = root
  parent_mem : ∀ v ∈ nodes, v ≠ root → parent v ∈ nodes ∧ depth v = depth (parent v) + 1

/-- Soundness over the tree. `stmt v ω`: node `v`'s statement words are true at outcome `ω`; `ins v ω`: its input
claims are (its children's statements, its hinted evaluations). If off `bad v` a true statement makes the node's input
claims true, a child's statement is true when its parent's input claims are, and the root's statement is true, then
off every node's `bad` every node's statement and input claims are true. -/
theorem tree_sound (T : Tree α) (stmt ins : α → Ω → Prop) (bad : α → Set Ω)
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v → stmt v ω → ins v ω)
    (hedge : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, ins (T.parent v) ω → stmt v ω)
    (hroot : ∀ ω, stmt T.root ω) (ω : Ω) (hω : ∀ v ∈ T.nodes, ω ∉ bad v) :
    ∀ v ∈ T.nodes, stmt v ω ∧ ins v ω := by
  have key : ∀ k, ∀ v ∈ T.nodes, T.depth v = k → stmt v ω ∧ ins v ω := by
    intro k
    induction k with
    | zero =>
      intro v hv hd
      have hst : stmt v ω := T.root_of_depth v hv hd ▸ hroot ω
      exact ⟨hst, hstep v hv ω (hω v hv) hst⟩
    | succ k ih =>
      intro v hv hd
      have hne : v ≠ T.root := by
        rintro rfl
        rw [T.depth_root] at hd
        omega
      obtain ⟨hp, hpd⟩ := T.parent_mem v hv hne
      have hst : stmt v ω := hedge v hv hne ω (ih (T.parent v) hp (by omega)).2
      exact ⟨hst, hstep v hv ω (hω v hv) hst⟩
  exact fun v hv => key _ v hv rfl

open Classical in
/-- The outcomes at which some node's statement or input claims are false are at most the sum of the nodes' `bad`
fractions. -/
theorem tree_sound_frac [Fintype Ω] (T : Tree α) (stmt ins : α → Ω → Prop) (bad : α → Finset Ω)
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v → stmt v ω → ins v ω)
    (hedge : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, ins (T.parent v) ω → stmt v ω) (hroot : ∀ ω, stmt T.root ω) :
    (#{ω | ∃ v ∈ T.nodes, ¬ (stmt v ω ∧ ins v ω)} : ℚ≥0) / Fintype.card Ω ≤
      ∑ v ∈ T.nodes, (#(bad v) : ℚ≥0) / Fintype.card Ω := by
  have hsub : ({ω | ∃ v ∈ T.nodes, ¬ (stmt v ω ∧ ins v ω)} : Finset Ω) ⊆ T.nodes.biUnion bad := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    by_contra hn
    simp only [mem_biUnion, not_exists, not_and] at hn
    obtain ⟨v, hv, hf⟩ := hω
    exact hf (tree_sound T stmt ins (fun v => (bad v : Set Ω)) (fun v hv ω h => hstep v hv ω h) hedge hroot ω
      (fun v hv h => hn v hv h) v hv)
  rw [← sum_div]
  gcongr
  exact_mod_cast (card_le_card hsub).trans card_biUnion_le

open Classical in
/-- With each node's `bad` at most an `ε v` fraction, the outcomes at which some node's statement or input claims are
false are at most a `∑ ε v` fraction. -/
theorem tree_sound_eps [Fintype Ω] (T : Tree α) (stmt ins : α → Ω → Prop) (bad : α → Finset Ω) (ε : α → ℚ≥0)
    (hstep : ∀ v ∈ T.nodes, ∀ ω, ω ∉ bad v → stmt v ω → ins v ω)
    (hedge : ∀ v ∈ T.nodes, v ≠ T.root → ∀ ω, ins (T.parent v) ω → stmt v ω) (hroot : ∀ ω, stmt T.root ω)
    (hε : ∀ v ∈ T.nodes, (#(bad v) : ℚ≥0) / Fintype.card Ω ≤ ε v) :
    (#{ω | ∃ v ∈ T.nodes, ¬ (stmt v ω ∧ ins v ω)} : ℚ≥0) / Fintype.card Ω ≤ ∑ v ∈ T.nodes, ε v :=
  (tree_sound_frac T stmt ins bad hstep hedge hroot).trans (sum_le_sum hε)

end LeanVMCircuits.Rec.TreeSound
