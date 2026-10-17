import Sphincs.SecurityPosition
import Sphincs.SecurityTargetAssignment
import Sphincs.Statement
import Sphincs.RandomizedSupport
import Sphincs.SecurityTreeWitness

/-! Canonical structural graph preparation. The retained positions can be any subset;
positions omitted by pruning retain their initial labels (in particular surrogate values).
Graph edges and their exact inputs follow leanVM b7a107256, specialized to the candidate. -/

open OracleComp OracleSpec

namespace Sphincs.Security.Graph

open Concrete Completeness
set_option backward.isDefEq.respectTransparency false

abbrev CanonicalGraphLabels := Position → HashOutput

def canonicalGraphSlots
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : ForestSecrets)
    (labels : CanonicalGraphLabels) : Position → List Digest
  | .chain lay tree leaf chain step =>
      if step.val = 0 then [otsSecret lay tree leaf chain]
      else (Position.chain lay tree leaf chain step).children.map (fun child => truncateHash (labels child))
  | .fchain index c s j a i t =>
      if t.val = 0 then [ftsSecret index c s j a i]
      else (Position.fchain index c s j a i t).children.map (fun child => truncateHash (labels child))
  | position => position.children.map (fun child => truncateHash (labels child))

def canonicalGraphInput (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : ForestSecrets)
    (position : Position) (labels : CanonicalGraphLabels) : HashInput :=
  tweakableHashInput parameter position.domain
    ((canonicalGraphSlots otsSecret ftsSecret labels position).flatMap (bytesLE 16))

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : ForestSecrets)

theorem canonicalGraphInput_separated :
    ∀ left right : Position, left ≠ right → ∀ before after,
      canonicalGraphInput parameter otsSecret ftsSecret left before ≠
        canonicalGraphInput parameter otsSecret ftsSecret right after := by
  intro left right hne before after heq
  exact Position.input_separated parameter hne _ _ heq

theorem canonicalGraphInput_congr (position : Position) (left right : CanonicalGraphLabels)
    (hchildren : ∀ child ∈ position.children, truncateHash (left child) = truncateHash (right child)) :
    canonicalGraphInput parameter otsSecret ftsSecret position left =
      canonicalGraphInput parameter otsSecret ftsSecret position right := by
  have hmap := List.map_congr_left hchildren
  apply congrArg (fun values : List Digest =>
    tweakableHashInput parameter position.domain (values.flatMap (bytesLE 16)))
  cases position <;> simp only [canonicalGraphSlots] <;>
    first | rfl | exact hmap | (split_ifs <;> first | rfl | exact hmap)

noncomputable def graphOrder (active : Position → Prop) : List Position := by
  classical
  exact ((Finset.univ : Finset Position).filter active).toList.mergeSort
    (fun left right => decide (left.depth ≤ right.depth))

theorem graphOrder_nodup (active : Position → Prop) : (graphOrder active).Nodup := by
  classical
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem mem_graphOrder (active : Position → Prop) (position : Position) :
    position ∈ graphOrder active ↔ active position := by
  classical
  rw [graphOrder, List.mem_mergeSort]
  simp

theorem graphOrder_sorted (active : Position → Prop) :
    (graphOrder active).Pairwise (fun left right => left.depth ≤ right.depth) := by
  classical
  have h := List.pairwise_mergeSort
    (le := fun left right : Position => decide (left.depth ≤ right.depth))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp [Bool.or_eq_true]; omega)
    ((Finset.univ : Finset Position).filter active).toList
  simpa only [graphOrder, decide_eq_true_eq] using h

def prepare : List Position → CanonicalGraphLabels → OracleComp HashSpec CanonicalGraphLabels
  | [], labels => pure labels
  | position :: rest, labels => do
      let answer ← liftM (HashSpec.query (canonicalGraphInput parameter otsSecret ftsSecret position labels))
      prepare rest (Function.update labels position answer)

end Sphincs.Security.Graph
