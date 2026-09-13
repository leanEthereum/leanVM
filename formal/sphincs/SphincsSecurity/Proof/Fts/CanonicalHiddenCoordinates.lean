import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.CanonicalGraph
import SphincsSecurity.Proof.Hypertree.FrontierSignerErasure
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

inductive CanonicalCoordinate where
  | otsStart (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
  | ftsStart (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
  | graph (position : Position)
  deriving DecidableEq, Fintype

namespace CanonicalCoordinate

def value (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels) : CanonicalCoordinate → Digest
  | .otsStart lay tree leaf chain => otsSecret lay tree leaf chain
  | .ftsStart index tree leaf => ftsSecret index tree leaf
  | .graph position => truncateHash (labels position)

def slots : Position → List CanonicalCoordinate
  | .chain lay tree leaf chain step =>
      if step.val = 0 then [.otsStart lay tree leaf chain]
      else (Position.chain lay tree leaf chain step).children.map .graph
  | .ftsLeaf index tree leaf => [.ftsStart index tree leaf]
  | position => position.children.map .graph

def Hidden (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop) : CanonicalCoordinate → Prop
  | .otsStart lay tree leaf chain => 0 < (words lay tree leaf chain).val
  | .ftsStart index tree leaf => ¬disclosed index tree leaf
  | .graph (.chain lay tree leaf chain step) => step.val + 1 < (words lay tree leaf chain).val
  | .graph _ => False

def chainChild (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) : CanonicalCoordinate :=
  if step.val = 0 then .otsStart lay tree leaf chain
  else .graph (.chain lay tree leaf chain ⟨step.val - 1, by have := step.isLt; omega⟩)

theorem slots_chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (step : ChainStep) :
    slots (.chain lay tree leaf chain step) = [chainChild lay tree leaf chain step] := by
  by_cases hzero : step.val = 0
  · simp only [slots, chainChild, if_pos hzero]
  · have hpos : 0 < step.val := by omega
    simp only [slots, chainChild, if_neg hzero, Position.children, dif_pos hpos, List.map_cons, List.map_nil]

theorem hidden_chain_child_iff (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chain : ChainIndex) (step : ChainStep) :
    Hidden words disclosed (chainChild lay tree leaf chain step) ↔ step.val < (words lay tree leaf chain).val := by
  by_cases hzero : step.val = 0
  · simp [chainChild, Hidden, hzero]
  · simp only [chainChild, if_neg hzero, Hidden]
    omega

theorem values_slots (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels) (position : Position) :
    (slots position).map (value otsSecret ftsSecret labels) = canonicalGraphSlots otsSecret ftsSecret labels position := by
  cases position <;> simp only [slots, canonicalGraphSlots] <;>
    first | (split <;> simp only [List.map_cons, List.map_nil, value, List.map_map, Function.comp_def]) |
      simp only [List.map_cons, List.map_nil, value, List.map_map, Function.comp_def]

theorem slots_ne_parent (position : Position) (coordinate : CanonicalCoordinate)
    (hcoordinate : coordinate ∈ slots position) : coordinate ≠ .graph position := by
  have hchildren (position : Position) (coordinate : CanonicalCoordinate)
      (hmem : coordinate ∈ position.children.map CanonicalCoordinate.graph) : coordinate ≠ .graph position := by
    obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hmem
    intro heq
    have heq := CanonicalCoordinate.graph.inj heq
    subst child
    have hlt := Position.depth_lt_of_mem_children hchild
    omega
  cases position <;> simp only [slots] at hcoordinate
  case chain lay tree leaf chain step =>
    split at hcoordinate
    · simp only [List.mem_singleton] at hcoordinate
      subst coordinate
      simp
    · exact hchildren _ _ hcoordinate
  case ftsLeaf index tree leaf =>
    simp only [List.mem_singleton] at hcoordinate
    subst coordinate
    simp
  all_goals exact hchildren _ _ hcoordinate

theorem hidden_slot_unary (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop)
    (position : Position) (coordinate : CanonicalCoordinate)
    (hcoordinate : coordinate ∈ slots position) (hhidden : Hidden words disclosed coordinate) :
    slots position = [coordinate] := by
  cases position with
  | chain lay tree leaf chain step =>
      simp only [slots] at hcoordinate ⊢
      by_cases hzero : step.val = 0
      · simp only [if_pos hzero, List.mem_singleton] at hcoordinate ⊢
        rw [hcoordinate]
      · have hpos : 0 < step.val := by omega
        simp only [if_neg hzero, Position.children, dif_pos hpos, List.map_cons, List.map_nil,
          List.mem_singleton] at hcoordinate ⊢
        rw [hcoordinate]
  | ftsLeaf index tree leaf =>
      simp only [slots, List.mem_singleton] at hcoordinate
      subst coordinate
      rfl
  | leaf lay tree leaf =>
      simp only [slots, Position.children, List.map_ofFn, List.mem_ofFn] at hcoordinate
      obtain ⟨chain, rfl⟩ := hcoordinate
      have hdigit := (words lay tree leaf chain).isLt
      norm_num [Hidden, Position.lastChainStep, chainLength, winternitzBits, Function.comp_def] at hhidden
      simp only [chainLength, winternitzBits] at hdigit
      omega
  | node lay tree level index =>
      simp only [slots, Position.children] at hcoordinate
      split_ifs at hcoordinate <;>
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hcoordinate
      · rcases hcoordinate with rfl | rfl <;> exact hhidden.elim
      · rcases hcoordinate with rfl | rfl <;> exact hhidden.elim
  | ftsNode index tree level leaf =>
      simp only [slots, Position.children] at hcoordinate
      split_ifs at hcoordinate <;>
        simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hcoordinate
      · rcases hcoordinate with rfl | rfl <;> exact hhidden.elim
      · rcases hcoordinate with rfl | rfl <;> exact hhidden.elim
  | ftsRoots index =>
      simp only [slots, Position.children, List.map_ofFn, List.mem_ofFn] at hcoordinate
      obtain ⟨tree, rfl⟩ := hcoordinate
      exact hhidden.elim

end CanonicalCoordinate

end SphincsSecurity.Concrete
