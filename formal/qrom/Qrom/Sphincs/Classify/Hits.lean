module

public import Qrom.Sphincs.Hit

@[expose] public section

/-!
# Hits of the classification's match branches

Each match branch of the classical classification, read on the hash that answers the honest inputs
from the data, is an input of the verifier's trace that is no honest input and whose value under
`G` hits the honest value at its address (`Qrom.Sphincs.HitAt`).
-/

open OracleComp OracleSpec FORS FORS.Security FORS.Security.Graph FORS.Security.GraphCorrectness
  FORS.Security.GraphView Concrete

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Qrom.Sphincs

variable [Params]

/-- The trace input `l` is no honest input and `G` hits the honest value at its address. -/
def HitAt (d : Data) (G : Input → HashOutput) (l : HashInput) : Prop :=
  ∃ x : Input, x.1 = l ∧ (∀ k, inputD d k ≠ l) ∧ good d x (G x)

theorem canonical_eq_input (d : Data) (G : Input → HashOutput) (p : Position) :
    canonicalGraphInput (param (hOf d)) (otsSecrets (QueryImpl.ofFn (ovFun (d none) (hOf d) G))
      (param (hOf d)) (d none)) (ftsSecrets (QueryImpl.ofFn (ovFun (d none) (hOf d) G))
      (param (hOf d)) (d none)) p (labelsOf (hOf d)) = inputD d (.pos p) := by
  rw [otsSecrets_ovFun, ftsSecrets_ovFun]
  rfl

/-- A non-canonical input at a position's address hitting its label. -/
theorem hit_of_position (d : Data) (G : Input → HashOutput) (p : Position) (pl : HashInput)
    (hpl : 16 ∣ pl.length) (hlen : pl.length ≤ 1024)
    (hne : tweakableHashInput (param (hOf d)) p.domain pl ≠ inputD d (.pos p))
    (hout : truncateHash (ovFun (d none) (hOf d) G (tweakableHashInput (param (hOf d)) p.domain pl)) =
      truncateHash (hOf d (.pos p))) :
    HitAt d G (tweakableHashInput (param (hOf d)) p.domain pl) := by
  have hl : (tweakableHashInput (param (hOf d)) p.domain pl).length ≤ maxLen := by
    rw [tweakableHashInput_length]
    unfold maxLen
    omega
  set x : Input := ⟨_, hl⟩
  have hnh := not_honest_of_position d p (param (hOf d)) pl rfl hne hpl
  refine ⟨x, rfl, hnh, Or.inl ⟨p, param (hOf d), pl, rfl, ?_⟩⟩
  rw [← (ans_of_not_honest d Log.empty G x hnh).1]
  exact hout

/-! ## The tree branch -/

theorem treeHit_hit (d : Data) (G : Input → HashOutput) (message : Message) (signature : Signature)
    (j : Nat) (h : SignatureWitness.TreeHit (QueryImpl.ofFn (ovFun (d none) (hOf d) G))
      (keysH (d none) (hOf d)).1 (d none) message signature j) :
    ∃ l ∈ SignatureWitness.trace (QueryImpl.ofFn (ovFun (d none) (hOf d) G))
      (keysH (d none) (hOf d)).1 message signature, HitAt d G l := by
  set f := QueryImpl.ofFn (ovFun (d none) (hOf d) G)
  set pk := (keysH (d none) (hOf d)).1
  have hcons := consistent_ovFun (d none) (hOf d) G
  have hbound := boundaryCorrect_ovFun (d none) (hOf d) G
  obtain ⟨-, value, -, hrun, hcase⟩ := h
  generalize hlay : layerUp j = lay at hrun hcase
  generalize htree : SignatureWitness.keyTree (SignatureWitness.index f pk message signature) lay = tree
    at hrun hcase
  generalize hleaf : SignatureWitness.keyLeaf (SignatureWitness.index f pk message signature) lay = leaf
    at hrun hcase
  generalize hpath : signaturePath signature lay = path at hrun hcase
  have hmem : ∀ level, level < layerHeight lay →
      merkleInput f pk.parameter (fun height index ↦ .node lay tree height index) leaf.val path
        value level ∈ SignatureWitness.trace f pk message signature := by
    intro level hlevel
    apply hrun
    rw [← merkleFold_treeFold]
    exact merkleInput_mem f pk.parameter _ leaf.val path value (layerHeight lay) level hlevel
  rcases hcase with ⟨reference, hreference, level, hlevel, hparent, hne, hout⟩ |
    ⟨hlaytop, level, hlevel, ⟨hlower, -, -⟩, -⟩
  · refine ⟨_, hmem level hlevel, ?_⟩
    have hinput : merkleInput f pk.parameter (fun height index ↦ .node lay tree height index) leaf.val
        path value level = tweakableHashInput (param (hOf d))
          (treePosition lay tree (level + 1) (hlevel.trans_le (layerHeight_le lay))
            ⟨reference.val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt reference.isLt⟩).domain
          (orderedPayload (leaf.val.testBit level)
            (merkleValue f pk.parameter (fun height index ↦ .node lay tree height index) leaf.val
              path value level) (path level)) := by
      unfold merkleInput
      rw [hparent]
      rfl
    rw [hinput]
    refine hit_of_position d G _ _ (by rw [HiddenBridge.orderedPayload_length]; omega)
      (by rw [HiddenBridge.orderedPayload_length]; omega) ?_ ?_
    · rw [← hinput, ← canonical_eq_input d G, tree_path_input f _ (d none) _ hcons hbound lay tree
        reference hreference level hlevel]
      intro heq
      apply hne
      exact heq
    · rw [← hinput]
      have hv := tree_path_value f _ (d none) _ hcons hbound lay tree reference hreference (level + 1)
        hlevel
      change truncateHash (f _) = _
      rw [hout]
      exact hv.symm
  · subst hlaytop
    have hk := keptHeight_top_full
    have hm := layerHeight_le topLayer
    rw [Completeness.layerHeight_top] at hlevel
    omega

end Qrom.Sphincs
