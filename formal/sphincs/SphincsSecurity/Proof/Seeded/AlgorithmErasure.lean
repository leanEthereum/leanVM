import SphincsSecurity.Proof.Seeded.Erasure
import SphincsSecurity.Proof.Seeded.DerivationTable
import SphincsSecurity.Proof.Scheme.StatementLemmas

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem sequenceFin_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    {n : Nat} (values : Fin n → α) : Concrete.sequenceFin (fun i => (pure (values i) : m α)) = pure values := by
  induction n with
  | zero =>
      simp only [Concrete.sequenceFin]
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      simp only [Concrete.sequenceFin, pure_bind, ih]
      congr 1
      funext i
      cases i using Fin.cases <;> rfl

theorem Erases.sequenceFin {ι : Type} {spec : OracleSpec ι} {α : Type} {n : Nat}
    (known : QueryCache spec) (left right : Fin n → OracleComp spec α)
    (h : ∀ i, Erases known (left i) (right i)) :
    Erases known (Concrete.sequenceFin left) (Concrete.sequenceFin right) := by
  induction n with
  | zero => exact .pure _
  | succ n ih =>
      simp only [Concrete.sequenceFin]
      apply (h 0).bind
      intro head
      apply (ih _ _ (fun i => h i.succ)).bind
      intro tail
      exact .pure _

theorem Erases.sequenceLayers {α : Type} (known : QueryCache HashSpec)
    (left right : Layer → OracleComp HashSpec (Option α))
    (h : ∀ lay, Erases known (left lay) (right lay)) :
    Erases known (Concrete.sequenceLayers left) (Concrete.sequenceLayers right) := by
  unfold Concrete.sequenceLayers
  apply (h bottomLayer).bind
  intro bottom
  cases bottom with
  | none => exact .pure _
  | some bottom =>
      apply (h middleLayer).bind
      intro middle
      cases middle with
      | none => exact .pure _
      | some middle =>
          apply (h topLayer).bind
          intro top
          cases top <;> exact .pure _

def tableOts (outputs : SecretOutputs) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) : Digest := truncateHash (outputs (.inl (lay, tree, leaf, chain)))

def tableFts (outputs : SecretOutputs) (index : Index) (tree : FtsTree) (leaf : FtsLeaf) : Digest :=
  truncateHash (outputs (.inr (index, tree, leaf)))

def tableKey (parameter : PublicParameter) (root : Digest) (outputs : SecretOutputs) : SphincsSecurity.SecretKey where
  parameter := parameter
  root := root
  otsSecret := tableOts outputs
  ftsSecret := tableFts outputs

section Algorithms

variable (known : QueryCache HashSpec) (parameter : PublicParameter) (seed : MasterSeed)
  (outputs : SecretOutputs)
  (hknown : ∀ position, known (secretInputs parameter seed position) = some (outputs position))

include hknown

theorem erases_deriveKey (position : SecretPosition) :
    Erases known (deriveKey parameter (secretDomain position) seed : OracleComp HashSpec Digest)
      (pure (truncateHash (outputs position))) := by
  unfold deriveKey Concrete.oracleHash
  exact Erases.skip _ _ (hknown position) _ _ (.pure _)

theorem erases_oneTimePublicKey (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    Erases known (oneTimePublicKey parameter lay tree leaf seed : OracleComp HashSpec _)
      (Concrete.oneTimePublicKey parameter lay tree leaf (tableOts outputs lay tree leaf)) := by
  unfold oneTimePublicKey Concrete.oneTimePublicKey
  apply Erases.sequenceFin
  intro chain
  simpa only [pure_bind, secretDomain, tableOts, tableFts] using (erases_deriveKey known parameter seed outputs hknown (.inl (lay, tree, leaf, chain))).bind
    (fun secret => Concrete.chainWalk parameter lay tree leaf chain 0 (chainLength - 1) secret)
    (fun secret => Concrete.chainWalk parameter lay tree leaf chain 0 (chainLength - 1) secret)
    (fun _ => Erases.refl known _)

theorem erases_otsSignFrom (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest)
    (attempts counter : Nat) :
    Erases known (otsSignFrom parameter lay tree leaf seed message attempts counter : OracleComp HashSpec _)
      (Concrete.otsSignFrom parameter lay tree leaf (tableOts outputs lay tree leaf) message attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact .pure _
  | succ attempts ih =>
      simp only [otsSignFrom, Concrete.otsSignFrom]
      apply (Erases.refl known (Concrete.encode parameter lay tree leaf message (BitVec.ofNat counterBits counter))).bind
      intro encoding
      cases encoding with
      | none => exact ih _
      | some encoding =>
          apply Erases.bind _ _ _ (fun _ => Erases.pure _)
          apply Erases.sequenceFin
          intro chain
          simpa only [pure_bind, secretDomain, tableOts, tableFts] using (erases_deriveKey known parameter seed outputs hknown (.inl (lay, tree, leaf, chain))).bind
            (fun secret => Concrete.chainWalk parameter lay tree leaf chain 0 (encoding chain).val secret)
            (fun secret => Concrete.chainWalk parameter lay tree leaf chain 0 (encoding chain).val secret)
            (fun _ => Erases.refl known _)

theorem erases_otsSign (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) :
    Erases known (otsSign parameter lay tree leaf seed message : OracleComp HashSpec _)
      (Concrete.otsSign parameter lay tree leaf (tableOts outputs lay tree leaf) message) :=
  erases_otsSignFrom known parameter seed outputs hknown lay tree leaf message _ _

theorem erases_treeNode (lay : Layer) (tree : TreeIndex) (level node : Nat) :
    Erases known (treeNode parameter lay tree seed level node : OracleComp HashSpec _)
      (Concrete.treeNode parameter lay tree (tableOts outputs lay tree) level node) := by
  induction level generalizing node with
  | zero =>
      rw [treeNode, Concrete.treeNode_zero_eq]
      apply (erases_oneTimePublicKey known parameter seed outputs hknown lay tree _).bind
      intro endpoints
      exact .refl known _
  | succ level ih =>
      rw [treeNode, Concrete.treeNode_succ_eq]
      apply (ih (2 * node)).bind
      intro left
      apply (ih (2 * node + 1)).bind
      intro right
      exact .refl known _

theorem erases_treeRoot (lay : Layer) (tree : TreeIndex) :
    Erases known (treeRoot parameter lay tree seed : OracleComp HashSpec _)
      (Concrete.treeRoot parameter lay tree (tableOts outputs lay tree)) :=
  erases_treeNode known parameter seed outputs hknown lay tree _ _

theorem erases_treePath (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    Erases known (treePath parameter lay tree seed leaf : OracleComp HashSpec _)
      (Concrete.treePath parameter lay tree (tableOts outputs lay tree) leaf) := by
  unfold treePath Concrete.treePath
  apply Erases.sequenceFin
  intro level
  split
  · exact erases_treeNode known parameter seed outputs hknown lay tree _ _
  · exact .pure _

theorem erases_ftsNode (index : Index) (tree : FtsTree) (level node : Nat) :
    Erases known (ftsNode parameter index tree seed level node : OracleComp HashSpec _)
      (Concrete.ftsNode parameter index tree (tableFts outputs index tree) level node) := by
  induction level generalizing node with
  | zero =>
      rw [ftsNode, Concrete.ftsNode_zero_eq]
      simpa only [pure_bind, secretDomain, tableOts, tableFts] using (erases_deriveKey known parameter seed outputs hknown
        (.inr (index, tree, Concrete.ftsLeafOfNat node))).bind
        (fun secret => Concrete.ftsLeafHash parameter index tree (Concrete.ftsLeafOfNat node) secret)
        (fun secret => Concrete.ftsLeafHash parameter index tree (Concrete.ftsLeafOfNat node) secret)
        (fun _ => Erases.refl known _)
  | succ level ih =>
      rw [ftsNode, Concrete.ftsNode_succ_eq]
      apply (ih (2 * node)).bind
      intro left
      apply (ih (2 * node + 1)).bind
      intro right
      exact .refl known _

theorem erases_ftsKey (index : Index) :
    Erases known (ftsKey parameter index seed : OracleComp HashSpec _)
      (Concrete.ftsKey parameter index (tableFts outputs index)) := by
  unfold ftsKey Concrete.ftsKey
  apply Erases.bind _ _ _ (fun _ => Erases.refl known _)
  exact Erases.sequenceFin known _ _ (fun tree => erases_ftsNode known parameter seed outputs hknown index tree _ _)

theorem erases_ftsOpen (index : Index) (leaves : IndexGroup → FtsLeaf) :
    Erases known (ftsOpen parameter index leaves seed : OracleComp HashSpec _)
      (Concrete.ftsOpen parameter index leaves (tableFts outputs index)) := by
  unfold ftsOpen Concrete.ftsOpen
  apply Erases.sequenceFin
  intro tree
  apply Erases.sequenceFin
  intro level
  exact erases_ftsNode known parameter seed outputs hknown index tree _ _

theorem erases_layerMessage (root : Digest) (index : Index) (lay : Layer) :
    Erases known (layerMessage ⟨seed, parameter, root⟩ index lay : OracleComp HashSpec _)
      (Concrete.layerMessage (tableKey parameter root outputs) index lay) := by
  simp only [layerMessage, Concrete.layerMessage, tableKey]
  split
  · exact erases_treeRoot known parameter seed outputs hknown _ _
  · exact erases_ftsKey known parameter seed outputs hknown _

theorem erases_signLayer (root : Digest) (index : Index) (lay : Layer) :
    Erases known (signLayer ⟨seed, parameter, root⟩ index lay : OracleComp HashSpec _)
      (Concrete.signLayer (tableKey parameter root outputs) index lay) := by
  simp only [signLayer, Concrete.signLayer]
  apply (erases_layerMessage known parameter seed outputs hknown root index lay).bind
  intro message
  apply (erases_otsSign known parameter seed outputs hknown lay _ _ message).bind
  intro signed
  cases signed with
  | none => exact .pure _
  | some signed =>
      apply (erases_treePath known parameter seed outputs hknown lay _ _).bind
      intro path
      exact .pure _

theorem erases_selectedSecrets (index : Index) (leaves : IndexGroup → FtsLeaf) :
    Erases known
      (Concrete.sequenceFin (fun tree => deriveKey parameter (.fts index tree (leaves (Concrete.ftsIndexOf tree))) seed) :
        OracleComp HashSpec (FtsTree → Digest))
      (pure (fun tree => tableFts outputs index tree (leaves (Concrete.ftsIndexOf tree)))) := by
  have h := Erases.sequenceFin known _ _ (fun tree =>
    erases_deriveKey known parameter seed outputs hknown (.inr (index, tree, leaves (Concrete.ftsIndexOf tree))))
  simpa only [sequenceFin_pure, secretDomain, tableFts] using h

omit hknown in
theorem signDigestLoop_tableKey (root : Digest) (message : Message) (attempts : Nat) :
    signDigestLoop attempts ⟨seed, parameter, root⟩ message =
      Concrete.signDigestLoop attempts (tableKey parameter root outputs) message := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
      simp only [signDigestLoop, Concrete.signDigestLoop, signAttempt, Concrete.signAttempt, tableKey, ih]
      rfl

theorem erases_sign (root : Digest) (message : Message) :
    Erases (worldKnown known) (sign ⟨seed, parameter, root⟩ message)
      (Concrete.sign (tableKey parameter root outputs) message) := by
  unfold sign Concrete.sign
  rw [signDigestLoop_tableKey parameter seed outputs root message]
  apply (Erases.refl (worldKnown known) _).bind
  intro attempt
  cases attempt with
  | none => exact .pure _
  | some attempt =>
      rcases attempt with ⟨randomness, index, leaves⟩
      have hselected := (erases_selectedSecrets known parameter seed outputs hknown index leaves).lift_hash
      simp only [liftM_pure] at hselected
      apply hselected.bind_known
      apply (erases_ftsOpen known parameter seed outputs hknown index leaves).lift_hash.bind
      intro path
      apply (Erases.sequenceLayers known _ _
        (fun lay => erases_signLayer known parameter seed outputs hknown root index lay)).lift_hash.bind
      intro layers
      cases layers with
      | none => exact .pure _
      | some parts =>
          apply (erases_treeRoot known parameter seed outputs hknown topLayer Concrete.rootTree).lift_hash.bind
          intro rootValue
          exact .pure _

end Algorithms
end SphincsSecurity.Seeded
