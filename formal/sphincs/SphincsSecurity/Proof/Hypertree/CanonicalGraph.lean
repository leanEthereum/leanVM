import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.FiniteGraphSampling
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false

abbrev CanonicalGraphLabels := Position → HashOutput

def canonicalGraphSlots
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (labels : CanonicalGraphLabels) : Position → List Digest
  | .chain lay tree leaf chain step =>
      if step.val = 0 then [otsSecret lay tree leaf chain]
      else (Position.chain lay tree leaf chain step).children.map (fun child => truncateHash (labels child))
  | .ftsLeaf index tree leaf => [ftsSecret index tree leaf]
  | position => position.children.map (fun child => truncateHash (labels child))

def canonicalGraphInput (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (position : Position) (labels : CanonicalGraphLabels) : HashInput :=
  tweakableHashInput parameter position.domain
    ((canonicalGraphSlots otsSecret ftsSecret labels position).flatMap digestBytes)

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

theorem canonicalGraphInput_separated :
    FiniteGraphSampling.Separated (canonicalGraphInput parameter otsSecret ftsSecret) := by
  intro left right hne before after heq
  exact hne (Position.domain_injective
    (tweakableHashInput_injective parameter left.domain_inRange right.domain_inRange heq).1)

theorem canonicalGraphInput_congr (position : Position) (left right : CanonicalGraphLabels)
    (hchildren : ∀ child ∈ position.children, truncateHash (left child) = truncateHash (right child)) :
    canonicalGraphInput parameter otsSecret ftsSecret position left =
      canonicalGraphInput parameter otsSecret ftsSecret position right := by
  have hmap := List.map_congr_left hchildren
  apply congrArg (fun values : List Digest =>
    tweakableHashInput parameter position.domain (values.flatMap digestBytes))
  cases position <;> simp only [canonicalGraphSlots] <;>
    first | rfl | exact hmap | (split_ifs <;> first | rfl | exact hmap)

theorem canonicalGraphInput_eq_honest (f : QueryImpl HashSpec Id) (position : Position)
    (hvalid : position.Valid) (labels : CanonicalGraphLabels)
    (hchildren : ∀ child ∈ position.children,
      truncateHash (labels child) = honestValue f parameter otsSecret ftsSecret child) :
    canonicalGraphInput parameter otsSecret ftsSecret position labels =
      honestInput f parameter otsSecret ftsSecret position := by
  rw [honestInput, honestPayload_eq_slots f parameter otsSecret ftsSecret hvalid]
  have hmap := List.map_congr_left hchildren
  apply congrArg (fun values : List Digest =>
    tweakableHashInput parameter position.domain (values.flatMap digestBytes))
  cases position <;> simp only [canonicalGraphSlots, slots, childValues] <;>
    first | rfl | exact hmap | (split_ifs <;> first | rfl | exact hmap)

def readCanonicalGraph (f : QueryImpl HashSpec Id) (positions : List Position)
    (labels : CanonicalGraphLabels) : CanonicalGraphLabels :=
  FiniteGraphSampling.read (canonicalGraphInput parameter otsSecret ftsSecret)
    (fun position output values => Function.update values position output) f positions labels

theorem readCanonicalGraph_preserves (f : QueryImpl HashSpec Id) (positions : List Position)
    (labels : CanonicalGraphLabels) (position : Position) (hposition : position ∉ positions) :
    readCanonicalGraph parameter otsSecret ftsSecret f positions labels position = labels position := by
  induction positions generalizing labels with
  | nil => rfl
  | cons first rest ih =>
      have hne : position ≠ first := fun h => hposition (by simp [h])
      have hrest : position ∉ rest := fun h => hposition (List.mem_cons_of_mem _ h)
      change readCanonicalGraph parameter otsSecret ftsSecret f rest
        (Function.update labels first (f (canonicalGraphInput parameter otsSecret ftsSecret first labels))) position = _
      rw [ih _ hrest, Function.update_of_ne hne]

theorem readCanonicalGraph_consistent (f : QueryImpl HashSpec Id) (positions : List Position)
    (hnodup : positions.Nodup)
    (hsorted : positions.Pairwise (fun left right => left.depth ≤ right.depth))
    (labels : CanonicalGraphLabels) :
    ∀ position ∈ positions,
      readCanonicalGraph parameter otsSecret ftsSecret f positions labels position =
        f (canonicalGraphInput parameter otsSecret ftsSecret position
          (readCanonicalGraph parameter otsSecret ftsSecret f positions labels)) := by
  induction positions generalizing labels with
  | nil => simp
  | cons first rest ih =>
      obtain ⟨hfirst, hrest⟩ := List.nodup_cons.mp hnodup
      obtain ⟨hdepth, hsorted⟩ := List.pairwise_cons.mp hsorted
      intro position hposition
      rcases List.mem_cons.mp hposition with hposition | hposition
      · subst position
        have hinput : canonicalGraphInput parameter otsSecret ftsSecret first
            (readCanonicalGraph parameter otsSecret ftsSecret f (first :: rest) labels) =
              canonicalGraphInput parameter otsSecret ftsSecret first labels := by
          apply canonicalGraphInput_congr
          intro child hchild
          apply congrArg truncateHash
          apply readCanonicalGraph_preserves
          intro hmem
          have hlt := Position.depth_lt_of_mem_children hchild
          rcases List.mem_cons.mp hmem with heq | hmem
          · subst child
            omega
          · have := hdepth child hmem
            omega
        rw [hinput]
        change readCanonicalGraph parameter otsSecret ftsSecret f rest
          (Function.update labels first (f (canonicalGraphInput parameter otsSecret ftsSecret first labels))) first = _
        rw [readCanonicalGraph_preserves _ _ _ _ _ _ _ hfirst, Function.update_self]
      · exact ih hrest hsorted _ position hposition

noncomputable def canonicalGraphOrder : List Position :=
  (Finset.univ : Finset Position).toList.mergeSort (fun left right => decide (left.depth ≤ right.depth))

theorem canonicalGraphOrder_nodup : canonicalGraphOrder.Nodup := by
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

theorem mem_canonicalGraphOrder (position : Position) : position ∈ canonicalGraphOrder := by
  rw [canonicalGraphOrder, List.mem_mergeSort]
  simp

theorem canonicalGraphOrder_sorted :
    canonicalGraphOrder.Pairwise (fun left right => left.depth ≤ right.depth) := by
  have h := List.pairwise_mergeSort
    (le := fun left right : Position => decide (left.depth ≤ right.depth))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp [Bool.or_eq_true]; omega)
    (Finset.univ : Finset Position).toList
  simpa only [canonicalGraphOrder, decide_eq_true_eq] using h

noncomputable def canonicalGraphLabels (f : QueryImpl HashSpec Id) : CanonicalGraphLabels :=
  readCanonicalGraph parameter otsSecret ftsSecret f canonicalGraphOrder (fun _ => 0)

theorem canonicalGraphLabels_consistent (f : QueryImpl HashSpec Id) (position : Position) :
    canonicalGraphLabels parameter otsSecret ftsSecret f position =
      f (canonicalGraphInput parameter otsSecret ftsSecret position
        (canonicalGraphLabels parameter otsSecret ftsSecret f)) :=
  readCanonicalGraph_consistent parameter otsSecret ftsSecret f canonicalGraphOrder
    canonicalGraphOrder_nodup canonicalGraphOrder_sorted _ position (mem_canonicalGraphOrder position)

end SphincsSecurity.Concrete
