import Sphincs.SecurityGraphCache
import Sphincs.SecuritySurrogateAddress

/-! The candidate's retained structural positions and off-spine surrogate boundary.
Forest instances and auxiliary layer/tree coordinates are conservatively prepared as well;
exact serialized addresses keep those extra nodes from adding targets to an individual query. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.PrunedGraph

open Concrete Completeness Graph TargetAssignment
attribute [local instance] Classical.propDecidable

variable [Params]

def active (parameter : PublicParameter) : Position → Prop
  | .chain _ _ leaf _ _ => Landed parameter leaf
  | .leaf _ _ leaf => Landed parameter leaf
  | .node _ _ level index => KeptNode parameter (level.val + 1) index.val
  | _ => True

def boundary (parameter : PublicParameter) (surrogates : Fin totalHeight → Digest) :
    Position → Option Digest
  | .leaf _ _ leaf =>
      if subtreeHeight = 0 ∧ leaf.val = boundaryIndex parameter 0 then
        some (surrogates ⟨0, by decide⟩) else none
  | .node _ _ level index =>
      if h : level.val + 1 < totalHeight then
        if subtreeHeight ≤ level.val + 1 ∧ index.val = boundaryIndex parameter (level.val + 1) then
          some (surrogates ⟨level.val + 1, h⟩) else none
      else none
  | _ => none

theorem boundary_inactive (parameter : PublicParameter) (surrogates : Fin totalHeight → Digest)
    (position : Position) (value : Digest) (hboundary : boundary parameter surrogates position = some value) :
    ¬active parameter position := by
  cases position with
  | chain | fchain | childLeaf | subNode | superChild | topNode | roots => simp [boundary] at hboundary
  | leaf lay tree leaf =>
      simp only [boundary] at hboundary
      split at hboundary
      next h =>
        change ¬Landed parameter leaf
        unfold Landed
        rw [h.1, pow_zero, Nat.div_one, h.2]
        simpa only [boundaryIndex, spineIndex, h.1, Nat.sub_self, pow_zero, Nat.div_one]
          using xor_one_ne (subtreePosition parameter)
      next => simp at hboundary
  | node lay tree level index =>
      simp only [boundary] at hboundary
      split at hboundary
      next hlevel =>
        split at hboundary
        next h =>
          change ¬KeptNode parameter (level.val + 1) index.val
          rw [h.2]
          exact boundary_not_kept parameter (level.val + 1) h.1
        next => simp at hboundary
      next => simp at hboundary

theorem spineIndex_lt (parameter : PublicParameter) (level : Nat) :
    spineIndex parameter level < 2 ^ maxLayerHeight := by
  have hsub := subtreePosition_lt parameter
  have hpow : 2 ^ (totalHeight - subtreeHeight) ≤ (2 : Nat) ^ maxLayerHeight :=
    Nat.pow_le_pow_right (by decide) (by change totalHeight - subtreeHeight ≤ totalHeight; omega)
  exact (Nat.div_le_self _ _).trans_lt (hsub.trans_le hpow)

theorem boundaryIndex_lt (parameter : PublicParameter) (level : Nat) :
    boundaryIndex parameter level < 2 ^ maxLayerHeight :=
  Nat.xor_lt_two_pow (spineIndex_lt parameter level) (by decide)

/-- A positive-height surrogate is targeted at a node-domain address. -/
def boundaryPosition (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (level : Fin totalHeight) (hpositive : 0 < level.val) : Position :=
  .node lay tree ⟨level.val - 1, by have := level.isLt; change level.val - 1 < totalHeight; omega⟩
    ⟨boundaryIndex parameter level.val, boundaryIndex_lt parameter level.val⟩

theorem boundaryPosition_domain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (level : Fin totalHeight) (hpositive : 0 < level.val) :
    (boundaryPosition parameter lay tree level hpositive).domain =
      .node lay tree level.val (boundaryIndex parameter level.val) := by
  simp only [boundaryPosition, Position.domain, Nat.sub_add_cancel hpositive]

theorem boundaryPosition_value (parameter : PublicParameter) (surrogates : Fin totalHeight → Digest)
    (lay : Layer) (tree : TreeIndex) (level : Fin totalHeight) (hpositive : 0 < level.val)
    (hlower : subtreeHeight ≤ level.val) :
    boundary parameter surrogates (boundaryPosition parameter lay tree level hpositive) =
      some (surrogates level) := by
  simp only [boundaryPosition, boundary, Nat.sub_add_cancel hpositive, level.isLt,
    ↓reduceDIte, hlower, and_self, ↓reduceIte]

/-- Full outputs at the boundary retain exactly the seed-derived low 128 bits. -/
def initialLabels (parameter : PublicParameter) (surrogates : Fin totalHeight → Digest) :
    CanonicalGraphLabels := fun position =>
  match boundary parameter surrogates position with
  | none => 0
  | some value => (0 : BitVec 128) ++ value

theorem initialLabels_boundary (parameter : PublicParameter) (surrogates : Fin totalHeight → Digest)
    (position : Position) (value : Digest) (hboundary : boundary parameter surrogates position = some value) :
    truncateHash (initialLabels parameter surrogates position) = value := by
  simp only [initialLabels, hboundary]
  change ((0 : BitVec 128) ++ value).extractLsb' 0 128 = value
  exact BitVec.extractLsb'_append_eq_right

/-- The precise address extracted from an outside-subtree forgery has one surrogate target
and no exempt canonical input in the retained graph. -/
theorem referenceTable_surrogate (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : ForestSecrets) (surrogates : Fin totalHeight → Digest)
    (labels : CanonicalGraphLabels) (lay : Layer) (tree : TreeIndex)
    (level : Fin totalHeight) (hpositive : 0 < level.val) (hlower : subtreeHeight ≤ level.val) :
    referenceTable parameter otsSecret ftsSecret (active parameter) (boundary parameter surrogates)
      labels (hashDomainFields (.node lay tree level.val (boundaryIndex parameter level.val))) =
        some ⟨none, surrogates level⟩ := by
  rw [← boundaryPosition_domain parameter lay tree level hpositive]
  have hb := boundaryPosition_value parameter surrogates lay tree level hpositive hlower
  exact referenceTable_boundary parameter otsSecret ftsSecret (active parameter)
    (boundary parameter surrogates) labels (boundaryPosition parameter lay tree level hpositive)
    (boundary_inactive parameter surrogates _ _ hb) _ hb

end Sphincs.Security.PrunedGraph
