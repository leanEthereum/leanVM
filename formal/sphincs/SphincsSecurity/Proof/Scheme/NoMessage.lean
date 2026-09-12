import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.RootCache
/-!
# Hash-only computations outside the digest loop make no message query

After the signer's digest loop has selected an admissible digest, all remaining hash calls use
structural or encoding domains. This module records the corresponding execution-path fact.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

def AvoidsMessageQueries {alpha : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec alpha) : Prop :=
  ∀ payload, tweakableHashInput parameter .message payload ∉ queriedInputs f oa

theorem AvoidsMessageQueries.pure {alpha : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (value : alpha) :
    AvoidsMessageQueries parameter f (pure value) := by
  simp [AvoidsMessageQueries]

theorem AvoidsMessageQueries.bind {alpha beta : Type} {parameter : PublicParameter}
    {f : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    {next : alpha → OracleComp HashSpec beta}
    (hleft : AvoidsMessageQueries parameter f oa)
    (hright : AvoidsMessageQueries parameter f (next (evalWithAnswerFn f oa))) :
    AvoidsMessageQueries parameter f (oa >>= next) := by
  intro payload hmem
  rw [queriedInputs_bind] at hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft payload hmem
  · exact hright payload hmem

theorem AvoidsMessageQueries.tweakableHash (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (domain : HashDomain) (hdomain : domain ≠ .message)
    (payload : HashInput) :
    AvoidsMessageQueries parameter f
      (Concrete.tweakableHash parameter domain payload) := by
  intro messagePayload hmem
  simp only [queriedInputs_tweakableHash, List.mem_singleton] at hmem
  exact tweakableHashInput_ne_message parameter domain hdomain payload messagePayload hmem.symm

theorem QueriesAtPositions.avoidsMessage {alpha : Type} {parameter : PublicParameter}
    {f : QueryImpl HashSpec Id} {oa : OracleComp HashSpec alpha}
    (h : QueriesAtPositions parameter f oa) : AvoidsMessageQueries parameter f oa := by
  intro payload hmem
  obtain ⟨p, structuralPayload, heq⟩ := h _ hmem
  exact tweakableHashInput_ne_message parameter p.domain (by cases p <;> simp [Position.domain])
    structuralPayload payload heq.symm

namespace Concrete

theorem avoidsMessage_sequenceFin {alpha : Type} {n : Nat}
    (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : Fin n → OracleComp HashSpec alpha)
    (hcomputation : ∀ index, AvoidsMessageQueries parameter f (computation index)) :
    AvoidsMessageQueries parameter f (sequenceFin computation) := by
  induction n with
  | zero => exact AvoidsMessageQueries.pure parameter f _
  | succ n ih =>
      rw [sequenceFin]
      apply AvoidsMessageQueries.bind (hcomputation 0)
      apply AvoidsMessageQueries.bind
      · exact ih (fun index : Fin n => computation index.succ)
          (fun index => hcomputation index.succ)
      · exact AvoidsMessageQueries.pure parameter f _

theorem avoidsMessage_chainWalk (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
    (start steps : Nat) (value : Digest) :
    AvoidsMessageQueries parameter f
      (chainWalk parameter lay tree leafIdx chainIdx start steps value) :=
  (queriesAtPositions_chainWalk parameter f lay tree leafIdx chainIdx start steps value).avoidsMessage

theorem avoidsMessage_oneTimePublicKey (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) :
    AvoidsMessageQueries parameter f
      (oneTimePublicKey parameter lay tree leafIdx secret) :=
  (queriesAtPositions_oneTimePublicKey parameter f lay tree leafIdx secret).avoidsMessage

theorem avoidsMessage_treeNode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)
    (level nodeIdx : Nat) :
    AvoidsMessageQueries parameter f (treeNode parameter lay tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [treeNode_zero_eq]
      apply AvoidsMessageQueries.bind
      · exact avoidsMessage_oneTimePublicKey parameter f lay tree (leafOfNat nodeIdx)
          (secret (leafOfNat nodeIdx))
      · exact AvoidsMessageQueries.tweakableHash parameter f _ (by simp) _
  | succ level ih =>
      rw [treeNode_succ_eq]
      apply AvoidsMessageQueries.bind (ih (2 * nodeIdx))
      apply AvoidsMessageQueries.bind (ih (2 * nodeIdx + 1))
      exact AvoidsMessageQueries.tweakableHash parameter f _ (by simp) _

theorem avoidsMessage_treeRoot (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) :
    AvoidsMessageQueries parameter f (treeRoot parameter lay tree secret) := by
  exact avoidsMessage_treeNode parameter f lay tree secret (layerHeight lay) 0

theorem avoidsMessage_treePath (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest)
    (leafIdx : LeafIndex) :
    AvoidsMessageQueries parameter f (treePath parameter lay tree secret leafIdx) := by
  apply avoidsMessage_sequenceFin
  intro level
  split
  · exact avoidsMessage_treeNode parameter f lay tree secret _ _
  · exact AvoidsMessageQueries.pure parameter f _

theorem avoidsMessage_encode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (message : Digest) (counter : Counter) :
    AvoidsMessageQueries parameter f (encode parameter lay tree leafIdx message counter) := by
  simp only [encode]
  apply AvoidsMessageQueries.bind
  · exact AvoidsMessageQueries.tweakableHash parameter f _ (by simp) _
  · exact AvoidsMessageQueries.pure parameter f _

theorem avoidsMessage_otsSignFrom (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) (attempts counter : Nat) :
    AvoidsMessageQueries parameter f
      (otsSignFrom parameter lay tree leafIdx secret message attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact AvoidsMessageQueries.pure parameter f _
  | succ attempts ih =>
      rw [otsSignFrom]
      apply AvoidsMessageQueries.bind
      · exact avoidsMessage_encode parameter f lay tree leafIdx message _
      split
      · apply AvoidsMessageQueries.bind
        · apply avoidsMessage_sequenceFin
          intro chainIdx
          exact avoidsMessage_chainWalk parameter f lay tree leafIdx chainIdx 0 _ _
        · exact AvoidsMessageQueries.pure parameter f _
      · exact ih (counter + 1)

theorem avoidsMessage_otsSign (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) :
    AvoidsMessageQueries parameter f
      (otsSign parameter lay tree leafIdx secret message) := by
  exact avoidsMessage_otsSignFrom parameter f lay tree leafIdx secret message
    encodingAttemptLimit 0

theorem avoidsMessage_ftsLeafHash (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf) (secret : Digest) :
    AvoidsMessageQueries parameter f (ftsLeafHash parameter index tree leafIdx secret) := by
  exact AvoidsMessageQueries.tweakableHash parameter f _ (by simp) _

theorem avoidsMessage_ftsNode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (tree : FtsTree) (secret : FtsLeaf → Digest)
    (level nodeIdx : Nat) :
    AvoidsMessageQueries parameter f (ftsNode parameter index tree secret level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [ftsNode_zero_eq]
      exact avoidsMessage_ftsLeafHash parameter f index tree _ _
  | succ level ih =>
      rw [ftsNode_succ_eq]
      apply AvoidsMessageQueries.bind (ih (2 * nodeIdx))
      apply AvoidsMessageQueries.bind (ih (2 * nodeIdx + 1))
      exact AvoidsMessageQueries.tweakableHash parameter f _ (by simp) _

theorem avoidsMessage_ftsKey (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    AvoidsMessageQueries parameter f (ftsKey parameter index secret) := by
  rw [ftsKey]
  apply AvoidsMessageQueries.bind
  · apply avoidsMessage_sequenceFin
    intro tree
    exact avoidsMessage_ftsNode parameter f index tree (secret tree) ftsTreeHeight 0
  · exact AvoidsMessageQueries.tweakableHash parameter f _ (by simp) _

theorem avoidsMessage_ftsOpen (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) :
    AvoidsMessageQueries parameter f (ftsOpen parameter index leaves secret) := by
  apply avoidsMessage_sequenceFin
  intro tree
  apply avoidsMessage_sequenceFin
  intro level
  exact avoidsMessage_ftsNode parameter f index tree (secret tree) level.val _

theorem avoidsMessage_layerMessage (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (index : Index) (lay : Layer) :
    AvoidsMessageQueries secretKey.parameter f (layerMessage secretKey index lay) := by
  rw [layerMessage]
  split
  · exact avoidsMessage_treeRoot secretKey.parameter f _ _ _
  · exact avoidsMessage_ftsKey secretKey.parameter f index (secretKey.ftsSecret index)

theorem avoidsMessage_signLayer (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (index : Index) (lay : Layer) :
    AvoidsMessageQueries secretKey.parameter f (signLayer secretKey index lay) := by
  rw [signLayer]
  apply AvoidsMessageQueries.bind
  · exact avoidsMessage_layerMessage f secretKey index lay
  apply AvoidsMessageQueries.bind
  · exact avoidsMessage_otsSign secretKey.parameter f lay (treeIndexAt index lay)
      (leafIndexAt index lay) _ _
  split
  · exact AvoidsMessageQueries.pure secretKey.parameter f _
  · apply AvoidsMessageQueries.bind
    · exact avoidsMessage_treePath secretKey.parameter f lay (treeIndexAt index lay) _
        (leafIndexAt index lay)
    · exact AvoidsMessageQueries.pure secretKey.parameter f _

def signAfterDigest (secretKey : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) : OracleComp HashSpec (Option Signature) := do
  let ftsPath ← ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index)
  let layers ← sequenceLayers fun lay => signLayer secretKey index lay
  match layers with
  | none => return none
  | some parts => do
      let _ ← treeRoot secretKey.parameter topLayer rootTree (secretKey.otsSecret topLayer rootTree)
      return some
        { randomness := randomness
          ftsSecret := fun tree => secretKey.ftsSecret index tree (leaves (ftsIndexOf tree))
          ftsPath := ftsPath
          counter := fun lay => (parts lay).1
          chainValue := fun lay => (parts lay).2.1
          authPath := flattenPaths fun lay => (parts lay).2.2 }

theorem avoidsMessage_signAfterDigest (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    AvoidsMessageQueries secretKey.parameter f
      (signAfterDigest secretKey randomness index leaves) := by
  rw [signAfterDigest]
  apply AvoidsMessageQueries.bind
  · exact avoidsMessage_ftsOpen secretKey.parameter f index leaves (secretKey.ftsSecret index)
  apply AvoidsMessageQueries.bind
  · unfold sequenceLayers
    apply AvoidsMessageQueries.bind (avoidsMessage_signLayer f secretKey index bottomLayer)
    split
    · exact AvoidsMessageQueries.pure secretKey.parameter f _
    · apply AvoidsMessageQueries.bind (avoidsMessage_signLayer f secretKey index middleLayer)
      split
      · exact AvoidsMessageQueries.pure secretKey.parameter f _
      · apply AvoidsMessageQueries.bind (avoidsMessage_signLayer f secretKey index topLayer)
        split <;> exact AvoidsMessageQueries.pure secretKey.parameter f _
  · split
    · exact AvoidsMessageQueries.pure secretKey.parameter f _
    · apply AvoidsMessageQueries.bind
      · exact avoidsMessage_treeRoot secretKey.parameter f topLayer rootTree _
      · exact AvoidsMessageQueries.pure secretKey.parameter f _

theorem sign_eq_digestLoop_afterDigest (secretKey : SecretKey) (message : Message) :
    sign secretKey message = (do
      match ← signDigestLoop digestAttemptLimit secretKey message with
      | none => return none
      | some (randomness, index, leaves) =>
          liftM (signAfterDigest secretKey randomness index leaves)) := by
  rw [sign_eq]
  apply bind_congr
  intro loopResult
  cases loopResult with
  | none => rfl
  | some data =>
      rcases data with ⟨randomness, index, leaves⟩
      simp only [signAfterDigest, liftM_bind]
      apply bind_congr
      intro ftsPath
      apply bind_congr
      intro layers
      cases layers <;> simp

end Concrete

end SphincsSecurity
