import SphincsSecurity.Proof.Scheme.Support
import SphincsSecurity.Proof.Scheme.Bytes
import SphincsSecurity.Proof.Seeded.KeyDerivation

/-!
# Inputs a computation leaves alone

The search bound of `Search.lean` needs its trials to be uncached when the search starts. What
supplies that is domain separation: key generation and the rest of signing hash under structural
tweaks and under the derivation domains, never under the encoding tweak a counter search uses, so
those inputs are still absent from the cache when the search reaches them.

`Avoids f target oa` is that fact for one input, and it composes along the computation.
-/

open OracleComp OracleSpec

namespace SphincsSecurity.Completeness

open Concrete

/-- Two hash inputs whose tweak fields differ in the tag differ, whatever their payloads. -/
theorem fieldInput_ne_of_tag_ne (parameter : PublicParameter) {fields1 fields2 : TweakFields}
    (htag : fields1.tag ≠ fields2.tag) (payload1 payload2 : HashInput) :
    fieldBytes fields1 ++ bytesLE 16 parameter ++ payload1
      ≠ fieldBytes fields2 ++ bytesLE 16 parameter ++ payload2 := by
  intro h
  apply htag
  obtain ⟨hprefix, _⟩ := List.append_inj h (by
    simp [fieldBytes, bytesLE_length])
  obtain ⟨hfields, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  rw [SphincsSecurity.fieldBytes_injective hfields]

/-- Two tweakable inputs with different tweak tags differ, whatever their payloads. -/
theorem tweakableHashInput_ne_of_tag_ne (parameter : PublicParameter) {d1 d2 : HashDomain}
    (htag : (hashDomainFields d1).tag ≠ (hashDomainFields d2).tag)
    (payload1 payload2 : HashInput) :
    tweakableHashInput parameter d1 payload1 ≠ tweakableHashInput parameter d2 payload2 := by
  intro h
  apply htag
  simp only [tweakableHashInput] at h
  obtain ⟨hprefix, _⟩ := List.append_inj h (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  rw [SphincsSecurity.tweakBytes_eq_iff.mp htweak]

/-- The tag byte precedes the parameter, so inputs under different tags differ even across parameters. -/
theorem fieldInput_ne_of_tag_ne' (parameter parameter' : PublicParameter)
    {fields1 fields2 : TweakFields} (htag : fields1.tag ≠ fields2.tag) (payload1 payload2 : HashInput) :
    fieldBytes fields1 ++ bytesLE 16 parameter ++ payload1
      ≠ fieldBytes fields2 ++ bytesLE 16 parameter' ++ payload2 := by
  intro h
  apply htag
  obtain ⟨hprefix, _⟩ := List.append_inj h (by simp [fieldBytes, bytesLE_length])
  obtain ⟨hfields, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  rw [SphincsSecurity.fieldBytes_injective hfields]

theorem tweakableHashInput_ne_of_tag_ne' (parameter parameter' : PublicParameter)
    {d1 d2 : HashDomain} (htag : (hashDomainFields d1).tag ≠ (hashDomainFields d2).tag)
    (payload1 payload2 : HashInput) :
    tweakableHashInput parameter d1 payload1 ≠ tweakableHashInput parameter' d2 payload2 :=
  fieldInput_ne_of_tag_ne' parameter parameter' htag payload1 payload2

variable (f : QueryImpl HashSpec Id) (target : HashInput)

/-- The computation never queries `target`. -/
def Avoids {α : Type} (oa : OracleComp HashSpec α) : Prop := target ∉ queriedInputs f oa

theorem Avoids.pure' {α : Type} (value : α) : Avoids f target (Pure.pure value) := by
  simp [Avoids]

theorem Avoids.bind {α β : Type} {oa : OracleComp HashSpec α}
    {next : α → OracleComp HashSpec β} (hleft : Avoids f target oa)
    (hright : Avoids f target (next (evalWithAnswerFn f oa))) :
    Avoids f target (oa >>= next) := by
  intro hmem
  rw [queriedInputs_bind] at hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft hmem
  · exact hright hmem

theorem Avoids.tweakableHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) (hne : tweakableHashInput parameter domain payload ≠ target) :
    Avoids f target (Concrete.tweakableHash parameter domain payload) := by
  intro hmem
  simp only [queriedInputs_tweakableHash, List.mem_singleton] at hmem
  exact hne hmem.symm

theorem Avoids.sequenceFin {α : Type} {n : Nat} (computation : Fin n → OracleComp HashSpec α)
    (h : ∀ index, Avoids f target (computation index)) :
    Avoids f target (sequenceFin computation) := by
  induction n with
  | zero => exact Avoids.pure' f target _
  | succ n ih =>
      rw [Concrete.sequenceFin]
      refine Avoids.bind f target (h 0) ?_
      exact Avoids.bind f target (ih _ (fun index => h index.succ)) (Avoids.pure' f target _)

theorem queriedInputs_deriveKey (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) :
    queriedInputs f (deriveKey parameter domain seed : OracleComp HashSpec Digest)
      = [keygenHashInput parameter domain seed] := rfl

theorem Avoids.deriveKey (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed)
    (hne : keygenHashInput parameter domain seed ≠ target) :
    Avoids f target (deriveKey parameter domain seed : OracleComp HashSpec Digest) := by
  intro hmem
  rw [queriedInputs_deriveKey, List.mem_singleton] at hmem
  exact hne hmem.symm

theorem Avoids.chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex)
    (hne : ∀ (step : ChainStep) (payload : HashInput),
      tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload ≠ target) :
    ∀ (start steps : Nat) (value : Digest),
      Avoids f target (Concrete.chainWalk parameter lay tree leaf chainIdx start steps value
        : OracleComp HashSpec Digest) := by
  intro start steps
  induction steps with
  | zero => intro value; exact Avoids.pure' f target _
  | succ steps ih =>
      intro value
      rw [Concrete.chainWalk]
      refine Avoids.bind f target (ih value) ?_
      split
      · exact Avoids.tweakableHash f target parameter _ _ (hne _ _)
      · exact Avoids.pure' f target _

theorem Avoids.oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed)
    (hchain : ∀ (chainIdx : ChainIndex) (step : ChainStep) (payload : HashInput),
      tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload ≠ target)
    (hderive : ∀ chainIdx : ChainIndex,
      keygenHashInput parameter (.ots lay tree leaf chainIdx) seed ≠ target) :
    Avoids f target (Seeded.oneTimePublicKey parameter lay tree leaf seed
      : OracleComp HashSpec (ChainIndex → Digest)) := by
  rw [Seeded.oneTimePublicKey]
  refine Avoids.sequenceFin f target _ (fun chainIdx => ?_)
  exact Avoids.bind f target (Avoids.deriveKey f target parameter _ seed (hderive chainIdx))
    (Avoids.chainWalk f target parameter lay tree leaf chainIdx (hchain chainIdx) _ _ _)

theorem Avoids.treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed)
    (hchain : ∀ (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep) (payload : HashInput),
      tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload ≠ target)
    (hleaf : ∀ (leaf : LeafIndex) (payload : HashInput),
      tweakableHashInput parameter (.leaf lay tree leaf) payload ≠ target)
    (hnode : ∀ (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput parameter (.node lay tree level nodeIdx) payload ≠ target)
    (hderive : ∀ (leaf : LeafIndex) (chainIdx : ChainIndex),
      keygenHashInput parameter (.ots lay tree leaf chainIdx) seed ≠ target) :
    ∀ (level nodeIdx : Nat),
      Avoids f target (Seeded.treeNode parameter lay tree seed level nodeIdx
        : OracleComp HashSpec Digest) := by
  intro level
  induction level with
  | zero =>
      intro nodeIdx
      rw [Seeded.treeNode]
      refine Avoids.bind f target
        (Avoids.oneTimePublicKey f target parameter lay tree _ seed (fun c => hchain _ c)
          (fun c => hderive _ c)) ?_
      exact Avoids.tweakableHash f target parameter _ _ (hleaf _ _)
  | succ level ih =>
      intro nodeIdx
      rw [Seeded.treeNode]
      refine Avoids.bind f target (ih _) (Avoids.bind f target (ih _) ?_)
      exact Avoids.tweakableHash f target parameter _ _ (hnode _ _ _)

theorem Avoids.treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed)
    (hchain : ∀ (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep) (payload : HashInput),
      tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload ≠ target)
    (hleaf : ∀ (leaf : LeafIndex) (payload : HashInput),
      tweakableHashInput parameter (.leaf lay tree leaf) payload ≠ target)
    (hnode : ∀ (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput parameter (.node lay tree level nodeIdx) payload ≠ target)
    (hderive : ∀ (leaf : LeafIndex) (chainIdx : ChainIndex),
      keygenHashInput parameter (.ots lay tree leaf chainIdx) seed ≠ target) :
    Avoids f target (Seeded.treeRoot parameter lay tree seed : OracleComp HashSpec Digest) :=
  Avoids.treeNode f target parameter lay tree seed hchain hleaf hnode hderive _ _

/-- Key generation derives the public parameter and builds the top tree, and nothing else. -/
theorem Avoids.keygenFromSeed (seed : MasterSeed)
    (hparam : keygenHashInput 0 KeygenDomain.parameter seed ≠ target)
    (hchain : ∀ (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep) (payload : HashInput),
      tweakableHashInput (evalWithAnswerFn f (SphincsSecurity.deriveKey 0 KeygenDomain.parameter seed
        : OracleComp HashSpec Digest)) (.chain topLayer rootTree leaf chainIdx step) payload ≠ target)
    (hleaf : ∀ (leaf : LeafIndex) (payload : HashInput),
      tweakableHashInput (evalWithAnswerFn f (SphincsSecurity.deriveKey 0 KeygenDomain.parameter seed
        : OracleComp HashSpec Digest)) (.leaf topLayer rootTree leaf) payload ≠ target)
    (hnode : ∀ (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput (evalWithAnswerFn f (SphincsSecurity.deriveKey 0 KeygenDomain.parameter seed
        : OracleComp HashSpec Digest)) (.node topLayer rootTree level nodeIdx) payload ≠ target)
    (hderive : ∀ (leaf : LeafIndex) (chainIdx : ChainIndex),
      keygenHashInput (evalWithAnswerFn f (SphincsSecurity.deriveKey 0 KeygenDomain.parameter seed
        : OracleComp HashSpec Digest)) (.ots topLayer rootTree leaf chainIdx) seed ≠ target) :
    Avoids f target (Seeded.keygenFromSeed seed) := by
  rw [Seeded.keygenFromSeed]
  refine Avoids.bind f target (Avoids.deriveKey f target 0 _ seed hparam) ?_
  exact Avoids.bind f target
    (Avoids.treeRoot f target _ topLayer rootTree seed hchain hleaf hnode hderive)
    (Avoids.pure' f target _)

/-! ## The signing side

The digest loop hashes under the randomizer tweak and the message tweak, never under the encoding
tweak a counter search walks. -/

theorem queriedInputs_deriveRandomizer (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32) :
    queriedInputs f (deriveRandomizer parameter seed message trial
        : OracleComp HashSpec Randomness)
      = [randomizerHashInput parameter seed message trial] := rfl

theorem Avoids.deriveRandomizer (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32)
    (hne : randomizerHashInput parameter seed message trial ≠ target) :
    Avoids f target (SphincsSecurity.deriveRandomizer parameter seed message trial
      : OracleComp HashSpec Randomness) := by
  intro hmem
  rw [queriedInputs_deriveRandomizer, List.mem_singleton] at hmem
  exact hne hmem.symm

theorem queriedInputs_messageDigest (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) :
    queriedInputs f (Concrete.messageDigest parameter root message randomness
        : OracleComp HashSpec MessageDigest)
      = [tweakableHashInput parameter .message
          (Concrete.messageDigestPayload root message randomness)] := rfl

theorem Avoids.messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness)
    (hne : tweakableHashInput parameter .message
      (Concrete.messageDigestPayload root message randomness) ≠ target) :
    Avoids f target (Concrete.messageDigest parameter root message randomness
      : OracleComp HashSpec MessageDigest) := by
  intro hmem
  rw [queriedInputs_messageDigest, List.mem_singleton] at hmem
  exact hne hmem.symm

theorem Avoids.signAttempt (secretKey : Seeded.SecretKey) (message : Message)
    (randomness : Randomness)
    (hne : tweakableHashInput secretKey.parameter .message
      (Concrete.messageDigestPayload secretKey.root message randomness) ≠ target) :
    Avoids f target (Seeded.signAttempt secretKey message randomness
      : OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) := by
  rw [Seeded.signAttempt]
  refine Avoids.bind f target (Avoids.messageDigest f target _ _ _ _ hne) ?_
  split <;> exact Avoids.pure' f target _

theorem Avoids.signDigestLoop (secretKey : Seeded.SecretKey) (message : Message)
    (hrand : ∀ trial : BitVec 32,
      randomizerHashInput secretKey.parameter secretKey.seed message trial ≠ target)
    (hmsg : ∀ randomness : Randomness, tweakableHashInput secretKey.parameter .message
      (Concrete.messageDigestPayload secretKey.root message randomness) ≠ target) :
    ∀ (attempts trial : Nat),
      Avoids f target (Seeded.signDigestLoop secretKey message attempts trial
        : OracleComp HashSpec (Option (Randomness × Index × (IndexGroup → FtsLeaf)))) := by
  intro attempts
  induction attempts with
  | zero => intro trial; exact Avoids.pure' f target _
  | succ attempts ih =>
      intro trial
      rw [Seeded.signDigestLoop]
      refine Avoids.bind f target (Avoids.deriveRandomizer f target _ _ _ _ (hrand _)) ?_
      refine Avoids.bind f target (Avoids.signAttempt f target _ _ _ (hmsg _)) ?_
      split
      · exact Avoids.pure' f target _
      · exact ih _

/-! ## The few-time forest

Opening the forest hashes under the few-time tweaks and derives its secrets, so it too leaves the
encoding inputs alone. -/

theorem Avoids.ftsNode (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (seed : MasterSeed)
    (hleafHash : ∀ (leaf : FtsLeaf) (payload : HashInput),
      tweakableHashInput parameter (.ftsLeaf index tree leaf) payload ≠ target)
    (hnode : ∀ (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput parameter (.ftsNode index tree level nodeIdx) payload ≠ target)
    (hderive : ∀ leaf : FtsLeaf,
      keygenHashInput parameter (.fts index tree leaf) seed ≠ target) :
    ∀ (level nodeIdx : Nat),
      Avoids f target (Seeded.ftsNode parameter index tree seed level nodeIdx
        : OracleComp HashSpec Digest) := by
  intro level
  induction level with
  | zero =>
      intro nodeIdx
      rw [Seeded.ftsNode]
      refine Avoids.bind f target (Avoids.deriveKey f target parameter _ seed (hderive _)) ?_
      exact Avoids.tweakableHash f target parameter _ _ (hleafHash _ _)
  | succ level ih =>
      intro nodeIdx
      rw [Seeded.ftsNode]
      refine Avoids.bind f target (ih _) (Avoids.bind f target (ih _) ?_)
      exact Avoids.tweakableHash f target parameter _ _ (hnode _ _ _)

theorem Avoids.ftsKey (parameter : PublicParameter) (index : Index) (seed : MasterSeed)
    (hleafHash : ∀ (tree : FtsTree) (leaf : FtsLeaf) (payload : HashInput),
      tweakableHashInput parameter (.ftsLeaf index tree leaf) payload ≠ target)
    (hnode : ∀ (tree : FtsTree) (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput parameter (.ftsNode index tree level nodeIdx) payload ≠ target)
    (hroots : ∀ payload : HashInput,
      tweakableHashInput parameter (.ftsRoots index) payload ≠ target)
    (hderive : ∀ (tree : FtsTree) (leaf : FtsLeaf),
      keygenHashInput parameter (.fts index tree leaf) seed ≠ target) :
    Avoids f target (Seeded.ftsKey parameter index seed : OracleComp HashSpec Digest) := by
  rw [Seeded.ftsKey]
  refine Avoids.bind f target
    (Avoids.sequenceFin f target _ (fun tree =>
      Avoids.ftsNode f target parameter index tree seed (hleafHash tree) (hnode tree)
        (hderive tree) _ _)) ?_
  exact Avoids.tweakableHash f target parameter _ _ (hroots _)

theorem Avoids.ftsOpen (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (seed : MasterSeed)
    (hleafHash : ∀ (tree : FtsTree) (leaf : FtsLeaf) (payload : HashInput),
      tweakableHashInput parameter (.ftsLeaf index tree leaf) payload ≠ target)
    (hnode : ∀ (tree : FtsTree) (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput parameter (.ftsNode index tree level nodeIdx) payload ≠ target)
    (hderive : ∀ (tree : FtsTree) (leaf : FtsLeaf),
      keygenHashInput parameter (.fts index tree leaf) seed ≠ target) :
    Avoids f target (Seeded.ftsOpen parameter index leaves seed
      : OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest)) := by
  rw [Seeded.ftsOpen]
  refine Avoids.sequenceFin f target _ (fun tree => ?_)
  exact Avoids.sequenceFin f target _ (fun level =>
    Avoids.ftsNode f target parameter index tree seed (hleafHash tree) (hnode tree)
      (hderive tree) _ _)

/-! ## A layer

A layer's own work is its counter search, its authentication path, and the message it signs. -/

theorem Avoids.treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex)
    (hchain : ∀ (leaf' : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep) (payload : HashInput),
      tweakableHashInput parameter (.chain lay tree leaf' chainIdx step) payload ≠ target)
    (hleaf : ∀ (leaf' : LeafIndex) (payload : HashInput),
      tweakableHashInput parameter (.leaf lay tree leaf') payload ≠ target)
    (hnode : ∀ (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput parameter (.node lay tree level nodeIdx) payload ≠ target)
    (hderive : ∀ (leaf' : LeafIndex) (chainIdx : ChainIndex),
      keygenHashInput parameter (.ots lay tree leaf' chainIdx) seed ≠ target) :
    Avoids f target (Seeded.treePath parameter lay tree seed leaf
      : OracleComp HashSpec (Fin (layerHeight lay) → Digest)) := by
  rw [Seeded.treePath]
  exact Avoids.sequenceFin f target _ (fun level =>
    Avoids.treeNode f target parameter lay tree seed hchain hleaf hnode hderive _ _)

theorem Avoids.otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : Digest)
    (hencode : ∀ (counter : Counter) (payload : HashInput),
      tweakableHashInput parameter (.encoding lay tree leaf) payload ≠ target)
    (hchain : ∀ (chainIdx : ChainIndex) (step : ChainStep) (payload : HashInput),
      tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload ≠ target)
    (hderive : ∀ chainIdx : ChainIndex,
      keygenHashInput parameter (.ots lay tree leaf chainIdx) seed ≠ target) :
    ∀ (attempts start : Nat),
      Avoids f target (Seeded.otsSignFrom parameter lay tree leaf seed message attempts start
        : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) := by
  intro attempts
  induction attempts with
  | zero => intro start; exact Avoids.pure' f target _
  | succ attempts ih =>
      intro start
      rw [Seeded.otsSignFrom]
      refine Avoids.bind f target ?_ ?_
      · rw [Concrete.encode]
        exact Avoids.bind f target
          (Avoids.tweakableHash f target parameter _ _ (hencode 0 _)) (Avoids.pure' f target _)
      · split
        · refine Avoids.bind f target (Avoids.sequenceFin f target _ (fun chainIdx => ?_))
            (Avoids.pure' f target _)
          exact Avoids.bind f target (Avoids.deriveKey f target parameter _ seed (hderive chainIdx))
            (Avoids.chainWalk f target parameter lay tree leaf chainIdx (hchain chainIdx) _ _ _)
        · exact ih _

theorem Avoids.layerMessage (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer)
    (htree : ∀ (lay' : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
        (step : ChainStep) (payload : HashInput),
      tweakableHashInput secretKey.parameter (.chain lay' tree leaf chainIdx step) payload ≠ target)
    (hleaf : ∀ (lay' : Layer) (tree : TreeIndex) (leaf : LeafIndex) (payload : HashInput),
      tweakableHashInput secretKey.parameter (.leaf lay' tree leaf) payload ≠ target)
    (hnode : ∀ (lay' : Layer) (tree : TreeIndex) (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput secretKey.parameter (.node lay' tree level nodeIdx) payload ≠ target)
    (hotsDerive : ∀ (lay' : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex),
      keygenHashInput secretKey.parameter (.ots lay' tree leaf chainIdx) secretKey.seed ≠ target)
    (hftsLeaf : ∀ (tree : FtsTree) (leaf : FtsLeaf) (payload : HashInput),
      tweakableHashInput secretKey.parameter (.ftsLeaf index tree leaf) payload ≠ target)
    (hftsNode : ∀ (tree : FtsTree) (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput secretKey.parameter (.ftsNode index tree level nodeIdx) payload ≠ target)
    (hftsRoots : ∀ payload : HashInput,
      tweakableHashInput secretKey.parameter (.ftsRoots index) payload ≠ target)
    (hftsDerive : ∀ (tree : FtsTree) (leaf : FtsLeaf),
      keygenHashInput secretKey.parameter (.fts index tree leaf) secretKey.seed ≠ target) :
    Avoids f target (Seeded.layerMessage secretKey index lay : OracleComp HashSpec Digest) := by
  rw [Seeded.layerMessage]
  split
  · exact Avoids.treeRoot f target _ _ _ secretKey.seed (htree _ _) (hleaf _ _)
      (hnode _ _) (hotsDerive _ _)
  · exact Avoids.ftsKey f target _ index secretKey.seed hftsLeaf hftsNode hftsRoots hftsDerive

/-- The five layers' counter searches hash under different layer fields, so none of them caches another's inputs. -/
theorem encodingInput_ne_of_layer_ne (parameter : PublicParameter) {lay lay' : Layer}
    (hlay : lay ≠ lay') (tree tree' : TreeIndex) (leaf leaf' : LeafIndex)
    (payload payload' : HashInput) :
    tweakableHashInput parameter (.encoding lay tree leaf) payload
      ≠ tweakableHashInput parameter (.encoding lay' tree' leaf') payload' := by
  intro h
  apply hlay
  simp only [tweakableHashInput] at h
  obtain ⟨hprefix, _⟩ := List.append_inj h (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  have hfields := SphincsSecurity.tweakBytes_eq_iff.mp htweak
  simp only [hashDomainFields, tweakFields, TweakFields.mk.injEq] at hfields
  have hv := congrArg BitVec.toNat hfields.2.1
  simp only [BitVec.toNat_ofNat] at hv
  have hl : lay.val < 2 ^ 8 := by have := lay.isLt; simp only [numLayers] at this; omega
  have hl' : lay'.val < 2 ^ 8 := by have := lay'.isLt; simp only [numLayers] at this; omega
  rw [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hl'] at hv
  exact Fin.ext hv

/-! ## Packaging

Every hypothesis above says the same thing: the target is not the input some honest step hashes. For
an encoding input all of them hold at once, by the tag alone, so it is worth naming the bundle. -/

/-- The target is none of the inputs the honest algorithms hash under a structural or derivation tweak. -/
structure Structural (parameter : PublicParameter) (seed : MasterSeed) (target : HashInput) : Prop where
  chain : ∀ (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep) (payload : HashInput),
    tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload ≠ target
  leafHash : ∀ (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (payload : HashInput),
    tweakableHashInput parameter (.leaf lay tree leaf) payload ≠ target
  node : ∀ (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) (payload : HashInput),
    tweakableHashInput parameter (.node lay tree level nodeIdx) payload ≠ target
  ftsLeaf : ∀ (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (payload : HashInput),
    tweakableHashInput parameter (.ftsLeaf index tree leaf) payload ≠ target
  ftsNodeHash : ∀ (index : Index) (tree : FtsTree) (level nodeIdx : Nat) (payload : HashInput),
    tweakableHashInput parameter (.ftsNode index tree level nodeIdx) payload ≠ target
  ftsRoots : ∀ (index : Index) (payload : HashInput),
    tweakableHashInput parameter (.ftsRoots index) payload ≠ target
  msg : ∀ payload : HashInput, tweakableHashInput parameter .message payload ≠ target
  randomizer : ∀ (message : Message) (trial : BitVec 32),
    randomizerHashInput parameter seed message trial ≠ target
  derive : ∀ domain : KeygenDomain, keygenHashInput parameter domain seed ≠ target

/-- An encoding input is structural for no honest step: its tag is `4`, which none of them use, and the derivation domains are a different byte layout. -/
theorem structural_encoding (parameter : PublicParameter) (seed : MasterSeed) (lay' : Layer)
    (tree' : TreeIndex) (leaf' : LeafIndex) (payload' : HashInput) :
    Structural parameter seed (tweakableHashInput parameter (.encoding lay' tree' leaf') payload') where
  chain _ _ _ _ _ _ := tweakableHashInput_ne_of_tag_ne parameter
    (by simp [hashDomainFields, tweakFields]) _ _
  leafHash _ _ _ _ := tweakableHashInput_ne_of_tag_ne parameter
    (by simp [hashDomainFields, tweakFields]) _ _
  node _ _ _ _ _ := tweakableHashInput_ne_of_tag_ne parameter
    (by simp [hashDomainFields, tweakFields]) _ _
  ftsLeaf _ _ _ _ := tweakableHashInput_ne_of_tag_ne parameter
    (by simp [hashDomainFields, tweakFields, ftsTweakFields]) _ _
  ftsNodeHash _ _ _ _ _ := tweakableHashInput_ne_of_tag_ne parameter
    (by simp [hashDomainFields, tweakFields, ftsTweakFields]) _ _
  ftsRoots _ _ := tweakableHashInput_ne_of_tag_ne parameter
    (by simp [hashDomainFields, tweakFields, ftsTweakFields]) _ _
  msg _ := tweakableHashInput_ne_of_tag_ne parameter
    (by simp [hashDomainFields, tweakFields]) _ _
  randomizer _ _ := fieldInput_ne_of_tag_ne parameter (by simp [hashDomainFields, tweakFields]) _ _
  derive _ := keygenHashInput_ne_tweakableHashInput parameter parameter _ _ seed _

/-! ## What the bundle gives

With the bundle, each honest step's avoidance needs no further argument. -/

theorem Avoids.signDigestLoop_of_structural (secretKey : Seeded.SecretKey) (message : Message)
    (hstruct : Structural secretKey.parameter secretKey.seed target) :
    ∀ (attempts trial : Nat),
      Avoids f target (Seeded.signDigestLoop secretKey message attempts trial
        : OracleComp HashSpec (Option (Randomness × Index × (IndexGroup → FtsLeaf)))) :=
  Avoids.signDigestLoop f target secretKey message
    (fun trial => hstruct.randomizer message trial) (fun _ => hstruct.msg _)

theorem Avoids.ftsOpen_of_structural (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (seed : MasterSeed)
    (hstruct : Structural parameter seed target) :
    Avoids f target (Seeded.ftsOpen parameter index leaves seed
      : OracleComp HashSpec (FtsTree → Fin ftsTreeHeight → Digest)) :=
  Avoids.ftsOpen f target parameter index leaves seed
    (fun tree leaf payload => hstruct.ftsLeaf index tree leaf payload)
    (fun tree level nodeIdx payload => hstruct.ftsNodeHash index tree level nodeIdx payload)
    (fun tree leaf => hstruct.derive _)

theorem Avoids.treeRoot_of_structural (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (seed : MasterSeed) (hstruct : Structural parameter seed target) :
    Avoids f target (Seeded.treeRoot parameter lay tree seed : OracleComp HashSpec Digest) :=
  Avoids.treeRoot f target parameter lay tree seed
    (fun leaf chainIdx step payload => hstruct.chain lay tree leaf chainIdx step payload)
    (fun leaf payload => hstruct.leafHash lay tree leaf payload)
    (fun level nodeIdx payload => hstruct.node lay tree level nodeIdx payload)
    (fun leaf chainIdx => hstruct.derive _)

theorem Avoids.treePath_of_structural (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (seed : MasterSeed) (leaf : LeafIndex)
    (hstruct : Structural parameter seed target) :
    Avoids f target (Seeded.treePath parameter lay tree seed leaf
      : OracleComp HashSpec (Fin (layerHeight lay) → Digest)) :=
  Avoids.treePath f target parameter lay tree seed leaf
    (fun leaf' chainIdx step payload => hstruct.chain lay tree leaf' chainIdx step payload)
    (fun leaf' payload => hstruct.leafHash lay tree leaf' payload)
    (fun level nodeIdx payload => hstruct.node lay tree level nodeIdx payload)
    (fun leaf' chainIdx => hstruct.derive _)

theorem Avoids.layerMessage_of_structural (secretKey : Seeded.SecretKey) (index : Index)
    (lay : Layer) (hstruct : Structural secretKey.parameter secretKey.seed target) :
    Avoids f target (Seeded.layerMessage secretKey index lay : OracleComp HashSpec Digest) :=
  Avoids.layerMessage f target secretKey index lay
    (fun lay' tree leaf chainIdx step payload => hstruct.chain lay' tree leaf chainIdx step payload)
    (fun lay' tree leaf payload => hstruct.leafHash lay' tree leaf payload)
    (fun lay' tree level nodeIdx payload => hstruct.node lay' tree level nodeIdx payload)
    (fun _ _ _ _ => hstruct.derive _)
    (fun tree leaf payload => hstruct.ftsLeaf index tree leaf payload)
    (fun tree level nodeIdx payload => hstruct.ftsNodeHash index tree level nodeIdx payload)
    (fun payload => hstruct.ftsRoots index payload)
    (fun _ _ => hstruct.derive _)

/-! ## The invariant a signature keeps

Signing runs its five counter searches one after another. Before each, no encoding input of a
layer still to come is cached: key generation and every earlier step avoid them. -/

/-- A computation that avoids an input, run from a cache missing it, leaves it missing. -/
theorem cache_none_of_avoids {α : Type} (oa : OracleComp HashSpec α) (cache : QueryCache HashSpec)
    (r : α × QueryCache HashSpec)
    (hr : r ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache))
    (target : HashInput) (hnone : cache target = none)
    (havoid : ∀ f : QueryImpl HashSpec Id, Avoids f target oa) : r.2 target = none := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) r.2
  exact cache_eq_none_of_not_mem_queriedInputs oa cache r.1 r.2 hr f hf target hnone (havoid f)

/-- No encoding input of a layer in `pending` is cached. -/
def EncodingFresh (parameter : PublicParameter) (pending : Layer → Prop)
    (cache : QueryCache HashSpec) : Prop :=
  ∀ lay, pending lay → ∀ (tree : TreeIndex) (leaf : LeafIndex) (payload : HashInput),
    cache (tweakableHashInput parameter (.encoding lay tree leaf) payload) = none

theorem EncodingFresh.step {α : Type} {parameter : PublicParameter} {pending : Layer → Prop}
    {cache : QueryCache HashSpec} (hfresh : EncodingFresh parameter pending cache)
    (oa : OracleComp HashSpec α) (r : α × QueryCache HashSpec)
    (hr : r ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache))
    (havoid : ∀ (f : QueryImpl HashSpec Id) (lay : Layer), pending lay →
      ∀ (tree : TreeIndex) (leaf : LeafIndex) (payload : HashInput),
        Avoids f (tweakableHashInput parameter (.encoding lay tree leaf) payload) oa) :
    EncodingFresh parameter pending r.2 := fun lay hlay tree leaf payload =>
  cache_none_of_avoids oa cache r hr _ (hfresh lay hlay tree leaf payload)
    (fun f => havoid f lay hlay tree leaf payload)

/-- A layer's whole signing step leaves another layer's encoding inputs alone. -/
theorem Avoids.signLayer_of_layer_ne (secretKey : Seeded.SecretKey) (index : Index) (lay : Layer)
    {lay' : Layer} (hne : lay ≠ lay') (tree' : TreeIndex) (leaf' : LeafIndex)
    (payload' : HashInput) :
    Avoids f (tweakableHashInput secretKey.parameter (.encoding lay' tree' leaf') payload')
      (Seeded.signLayer secretKey index lay : OracleComp HashSpec (Option (LayerSignature lay))) := by
  have hstruct := structural_encoding secretKey.parameter secretKey.seed lay' tree' leaf' payload'
  rw [Seeded.signLayer]
  refine Avoids.bind f _ (Avoids.layerMessage_of_structural f _ secretKey index lay hstruct) ?_
  refine Avoids.bind f _ (Avoids.otsSignFrom f _ secretKey.parameter lay _ _ secretKey.seed _
    (fun _ _ => encodingInput_ne_of_layer_ne _ hne _ _ _ _ _ _)
    (fun chainIdx step payload => hstruct.chain _ _ _ chainIdx step payload)
    (fun _ => hstruct.derive _) _ _) ?_
  split
  · exact Avoids.bind f _ (Avoids.treePath_of_structural f _ _ lay _ secretKey.seed _ hstruct)
      (Avoids.pure' f _ _)
  · exact Avoids.pure' f _ _

end SphincsSecurity.Completeness
