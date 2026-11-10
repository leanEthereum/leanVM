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

/-! ## The FORS branches -/

theorem forsException_hit (d : Data) (G : Input → HashOutput) (message : Message)
    (signature : Signature)
    (h : Fors.Exception (QueryImpl.ofFn (ovFun (d none) (hOf d) G)) (param (hOf d))
      (SignatureWitness.index (QueryImpl.ofFn (ovFun (d none) (hOf d) G)) (keysH (d none) (hOf d)).1
        message signature) (d none)
      (digestLeaves (verificationDigest (QueryImpl.ofFn (ovFun (d none) (hOf d) G))
        (keysH (d none) (hOf d)).1 message signature)) signature.fors) :
    ∃ l ∈ SignatureWitness.trace (QueryImpl.ofFn (ovFun (d none) (hOf d) G))
      (keysH (d none) (hOf d)).1 message signature, HitAt d G l := by
  set f := QueryImpl.ofFn (ovFun (d none) (hOf d) G)
  set pk := (keysH (d none) (hOf d)).1
  set index := SignatureWitness.index f pk message signature
  set leaves := digestLeaves (verificationDigest f pk message signature)
  have hcons := consistent_ovFun (d none) (hOf d) G
  have hrunAll := SignatureWitness.verification_fors_run f pk message signature
  have hrun := hrunAll.bind_left
  rcases h with ⟨κ, hsec, hval⟩ | ⟨κ, level, hlevel, -, hneq, hout⟩ | ⟨hroots, hkey⟩
  · -- a leaf match
    refine ⟨_, hrun _ (Fors.leafInput_mem f pk.parameter index leaves signature.fors κ), ?_⟩
    refine hit_of_position d G (.fleaf index κ (leaves κ)) _ (by rw [bytesLE_length]) (by
      rw [bytesLE_length]; omega) ?_ ?_
    · rw [← canonical_eq_input d G, fleaf_input f _ (d none) _ index κ]
      intro heq
      exact hsec (bytesLE_injective (tweakableInput_injective heq).2.2)
    · have hv := fleaf_value f _ (d none) _ hcons index κ (leaves κ)
      have hc := Fors.leafValue_canonical f (param (hOf d)) index κ (d none) (leaves κ)
      rw [Completeness.forsNodeValue_zero] at hc
      simp only [Fors.leafValue, forsLeafHash, Completeness.eval_tweakableHash] at hval hc
      change truncateHash (f _) = _
      exact hval.trans (hc.trans hv.symm)
  · -- a node match
    have hcanon : Fors.leafValue f (param (hOf d)) index κ (leaves κ)
        (Completeness.forsSecretValue f (param (hOf d)) index κ (d none) (leaves κ)) =
          Completeness.forsLeafValue f (param (hOf d)) index κ (d none) (leaves κ) := by
      rw [Fors.leafValue_canonical, Completeness.forsNodeValue_zero]
    have hl1 : level + 1 ≤ forsHeight := hlevel
    rw [hcanon] at hneq hout
    have hdom : Fors.forsDomain index κ (level + 1) ((leaves κ).val / 2 ^ (level + 1)) =
        (forsPosition index κ (level + 1) hl1
          ⟨(leaves κ).val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt (leaves κ).isLt⟩).domain := by
      rw [Fors.forsDomain, dite_eq_left ⟨by omega, by omega⟩]
      simp only [forsPosition, Position.domain]
      congr 2
      exact Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt (leaves κ).isLt)
    have hinput : merkleInput f (param (hOf d)) (Fors.forsDomain index κ) (leaves κ).val
        (Fors.extendPath (signature.fors κ).path)
        (Fors.leafValue f (param (hOf d)) index κ (leaves κ) (signature.fors κ).secret) level =
        tweakableHashInput (param (hOf d)) (forsPosition index κ (level + 1) hl1
          ⟨(leaves κ).val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt (leaves κ).isLt⟩).domain
          (orderedPayload ((leaves κ).val.testBit level)
            (merkleValue f (param (hOf d)) (Fors.forsDomain index κ) (leaves κ).val
              (Fors.extendPath (signature.fors κ).path)
              (Fors.leafValue f (param (hOf d)) index κ (leaves κ) (signature.fors κ).secret) level)
            (Fors.extendPath (signature.fors κ).path level)) := by
      unfold merkleInput
      rw [hdom]
    refine ⟨_, hrun _ (Fors.nodeInput_mem f pk.parameter index leaves signature.fors κ level hlevel), ?_⟩
    change HitAt d G (merkleInput f (param (hOf d)) (Fors.forsDomain index κ) (leaves κ).val
      (Fors.extendPath (signature.fors κ).path)
      (Fors.leafValue f (param (hOf d)) index κ (leaves κ) (signature.fors κ).secret) level)
    rw [hinput]
    refine hit_of_position d G _ _ (by rw [HiddenBridge.orderedPayload_length]; omega)
      (by rw [HiddenBridge.orderedPayload_length]; omega) ?_ ?_
    · rw [← hinput, ← canonical_eq_input d G, fors_path_input f _ (d none) _ hcons index κ _ level hlevel]
      exact hneq
    · rw [← hinput]
      exact hout.trans (fors_path_value f _ (d none) _ hcons index κ (leaves κ) (level + 1) hl1).symm
  · -- a roots match
    refine ⟨_, hrunAll _ (Fors.rootsInput_mem f pk.parameter index leaves signature.fors), ?_⟩
    refine hit_of_position d G (.froots index) _ (by rw [rootsPayload_length]; omega) (by
      rw [rootsPayload_length]; have := Params.forsTrees_le; omega) ?_ ?_
    · rw [← canonical_eq_input d G, HiddenBridge.froots_input f _ (d none) _ hcons index]
      intro heq
      exact hroots (rootsPayload_injective (tweakableInput_injective heq).2.2)
    · have hk := fors_key_value f _ (d none) _ hcons index
      rw [Completeness.forsKey_eq] at hk
      simp only [Completeness.eval_forsPublicKey] at hkey hk
      change truncateHash (f _) = _
      exact hkey.trans hk.symm

end Qrom.Sphincs
