module

public import Sphincs.Model
public import FORS.Crate

@[expose] public section

/-!
# The crate's key generation and signer: FORS's copy is the statement's

`FORS/Crate.lean` writes the crate's `key_gen_from_seed` and `sign` (leanVM main `40f877dc`,
`crates/lean_sphincs/src/scheme.rs`) in FORS's primitives and types, function for
function as `Statement/LeanSphincs.lean` transcribes them (`KeyGenerationAndSigning`). Here, their
queries answered by Keccak-256 over `π` (`schemeHashOverPermutation`), they are the statement's
(`simulateQ_keygen`, `simulateQ_sign`), through the maps of the keys and signatures of
`Sphincs/Model.lean`: the layers reversed (`toLayer`), each node's domain the statement's
(`toDomain`), and a FORS node's index in its tree, as every tree built level by level computes it
(`simulateQ_merkleLevelsFrom`: the levels' lengths halve). Mapped back to the statement's types
(`ofModelPublicKey`, `ofModelSignature`) they are `Sphincs.Model.simulateQ_crateKeygen` and
`Sphincs.Model.simulateQ_crateSign`, which `Sphincs/Bridge.lean` reads.
-/

open OracleComp OracleSpec

namespace Sphincs.CrateSim

open HashSig HashSig.OverPermutation Common Common.SufCma
open Sphincs.Model (params toLayer toLeaf toDomain InRange simulateQ_oracleHash
  fieldBytes_tweakFields layerHeight_toLayer sim_bind sim_pure bind_eq_of simulateQ_tweakableHash
  simulateQ_sequenceFin simulateQ_chainWalk simulateQ_leafHash simulateQ_encode toModelPublicKey
  toModelTreeOpening toModelSignature simulateQ_messageDigestCall digestIndex_eq digestLeaves_eq
  asModel)

attribute [local instance] params

local notation "σ" => schemeHashOverPermutation

/-! ## Binds, lists and sequences -/

theorem sim_ite {α : Type} (c : Prop) [Decidable c] (a b : OracleComp FORS.HashSpec α) :
    simulateQ σ (@ite (OracleComp FORS.HashSpec α) c _ a b) =
      if c then simulateQ σ a else simulateQ σ b := by
  split <;> rfl

theorem simulateQ_mapM {α β : Type} (f : α → OracleComp FORS.HashSpec β) :
    ∀ l : List α, simulateQ σ (List.mapM (m := OracleComp FORS.HashSpec) f l) =
      l.mapM fun a ↦ simulateQ σ (f a)
  | [] => by rw [List.mapM_nil, List.mapM_nil, sim_pure]
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons, sim_bind]
    simp only [sim_bind, sim_pure, simulateQ_mapM f l]

/-- `mapM` of functions that agree on the list. -/
theorem mapM_congr_mem {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} {f g : α → m β} :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.mapM_cons]
    rw [h a (List.mem_cons_self ..),
      mapM_congr_mem l fun b hb ↦ h b (List.mem_cons_of_mem _ hb)]

/-- What follows a `mapM` reads a list of its length. -/
theorem mapM_bind_congr {m : Type → Type} [Monad m] [LawfulMonad m] {α β γ : Type}
    (f : α → m β) : ∀ (l : List α) (k₁ k₂ : List β → m γ),
      (∀ ys : List β, ys.length = l.length → k₁ ys = k₂ ys) → l.mapM f >>= k₁ = l.mapM f >>= k₂
  | [], k₁, k₂, h => by simp only [List.mapM_nil, pure_bind]; exact h [] rfl
  | a :: l, k₁, k₂, h => by
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    refine bind_congr fun b ↦ ?_
    exact mapM_bind_congr f l (fun ys ↦ k₁ (b :: ys)) (fun ys ↦ k₂ (b :: ys))
      fun ys hys ↦ h (b :: ys) (by simp [hys])

/-! ## Hashes -/

/-- A seed derivation's input: the model's address of a chain start is the statement's
`WOTS_PRF` address, `PK.seed ‖ ADRS ‖ SK.seed`. -/
theorem keygenHashInput_ots (parameter : FORS.PublicParameter) (lay : FORS.Layer)
    (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex) (chain : FORS.ChainIndex)
    (seed : FORS.MasterSeed) :
    FORS.keygenHashInput parameter (.ots lay tree leaf chain) seed =
      addressedHashInput parameter
        (keygenDomainFields (.oneTimeChain (toLayer lay) tree (toLeaf leaf) chain))
        (littleEndianBytes 32 seed) := by
  simp only [FORS.keygenHashInput, FORS.keygenDomainFields, FORS.treeFields,
    keygenDomainFields, addressedHashInput, hasherInput,
    ← fieldBytes_tweakFields .wotsPrf _ _ _ _ _ (lt_trans tree.isLt (by decide))]
  rfl

theorem keygenHashInput_fors (parameter : FORS.PublicParameter) (index : FORS.Index)
    (κ : FORS.FTree) (leaf : FORS.FLeaf) (seed : FORS.MasterSeed) :
    FORS.keygenHashInput parameter (.fors index κ leaf) seed =
      addressedHashInput parameter (keygenDomainFields (.forsSecret index κ leaf))
        (littleEndianBytes 32 seed) := by
  have hidx : FORS.forsTreeIndex κ 0 leaf.val =
      forsTreeIndex (show ForsTreeIndex from κ) 0 leaf.val := by
    unfold FORS.forsTreeIndex forsTreeIndex
    split
    · rfl
    · next hn => exact absurd (by simp) hn
  simp only [FORS.keygenHashInput, FORS.keygenDomainFields, FORS.forsFields, hidx,
    keygenDomainFields, addressedHashInput, hasherInput, Model.treeOfIndex_zero,
    Model.leafOfIndex_zero,
    ← fieldBytes_tweakFields .forsPrf _ _ _ _ _ (Model.forsTree_lt index)]
  rfl

/-! ## The key -/

/-- The statement's expanded key as the copy's. -/
def ofExpandedKey (key : KeyGenerationAndSigning.ExpandedKey) : FORS.Crate.ExpandedKey :=
  ⟨key.secretSeed, key.secretPrfKey, key.publicSeed⟩

/-- The copy's expanded key as the statement's. -/
def toExpandedKey (key : FORS.Crate.ExpandedKey) : KeyGenerationAndSigning.ExpandedKey :=
  ⟨key.secretSeed, key.secretPrfKey, key.publicSeed⟩

theorem toExpandedKey_ofExpandedKey (key : KeyGenerationAndSigning.ExpandedKey) :
    toExpandedKey (ofExpandedKey key) = key := rfl

theorem simulateQ_expandKey (seed : FORS.MasterSeed) :
    simulateQ σ (FORS.Crate.expandKey (m := OracleComp FORS.HashSpec) seed) =
      ofExpandedKey <$> KeyGenerationAndSigning.expandKey queryPermutation seed := by
  simp only [FORS.Crate.expandKey, KeyGenerationAndSigning.expandKey, sim_bind, sim_pure,
    simulateQ_oracleHash, map_bind, map_pure]
  rfl

theorem simulateQ_prf_ots (key : FORS.Crate.ExpandedKey) (lay : FORS.Layer)
    (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex) (chain : FORS.ChainIndex) :
    simulateQ σ (FORS.Crate.prf (m := OracleComp FORS.HashSpec) key (.ots lay tree leaf chain)) =
      KeyGenerationAndSigning.prf queryPermutation (toExpandedKey key)
        (.oneTimeChain (toLayer lay) tree (toLeaf leaf) chain) := by
  simp only [FORS.Crate.prf, FORS.deriveKey, KeyGenerationAndSigning.prf,
    Verification.addressedHash, sim_bind, sim_pure, simulateQ_oracleHash, keygenHashInput_ots]
  rfl

theorem simulateQ_prf_fors (key : FORS.Crate.ExpandedKey) (index : FORS.Index) (κ : FORS.FTree)
    (leaf : FORS.FLeaf) :
    simulateQ σ (FORS.Crate.prf (m := OracleComp FORS.HashSpec) key (.fors index κ leaf)) =
      KeyGenerationAndSigning.forsSecret queryPermutation (toExpandedKey key) index κ leaf := by
  simp only [FORS.Crate.prf, FORS.deriveKey, KeyGenerationAndSigning.forsSecret,
    KeyGenerationAndSigning.prf, Verification.addressedHash, sim_bind, sim_pure,
    simulateQ_oracleHash, keygenHashInput_fors]
  rfl

theorem simulateQ_prfMessage (secretPrfKey : FORS.HashOutput) (publicSeed : FORS.PublicParameter)
    (message : FORS.Message) :
    simulateQ σ (FORS.Crate.prfMessage (m := OracleComp FORS.HashSpec) secretPrfKey publicSeed
      message) =
      KeyGenerationAndSigning.prfMessage queryPermutation secretPrfKey publicSeed message := by
  simp only [FORS.Crate.prfMessage, KeyGenerationAndSigning.prfMessage, sim_bind, sim_pure,
    simulateQ_oracleHash]
  rfl

/-! ## One-time keys -/

theorem simulateQ_otsSecrets (key : FORS.Crate.ExpandedKey) (lay : FORS.Layer)
    (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex) :
    simulateQ σ (FORS.Seeded.otsSecrets (m := OracleComp FORS.HashSpec) key.publicSeed lay tree
      leaf key.secretSeed) =
      KeyGenerationAndSigning.otsSecrets queryPermutation (toExpandedKey key) (toLayer lay) tree
        (toLeaf leaf) := by
  simp only [FORS.Seeded.otsSecrets, KeyGenerationAndSigning.otsSecrets, simulateQ_sequenceFin]
  exact congrArg sequenceFin (funext fun chain ↦ simulateQ_prf_ots key lay tree leaf chain)

theorem simulateQ_otsPublicLeaf (key : FORS.Crate.ExpandedKey) (lay : FORS.Layer)
    (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex) :
    simulateQ σ (FORS.Crate.otsPublicLeaf (m := OracleComp FORS.HashSpec) key lay tree leaf) =
      KeyGenerationAndSigning.otsPublicLeaf queryPermutation (toExpandedKey key) (toLayer lay)
        tree (toLeaf leaf) := by
  simp only [FORS.Crate.otsPublicLeaf, FORS.Seeded.oneTimePublicKey,
    KeyGenerationAndSigning.otsPublicLeaf, sim_bind, bind_assoc, simulateQ_otsSecrets,
    simulateQ_sequenceFin, simulateQ_chainWalk, simulateQ_leafHash]
  rfl

theorem simulateQ_otsSignFrom (key : FORS.Crate.ExpandedKey) (lay : FORS.Layer)
    (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex) (message : FORS.Digest) :
    ∀ (attempts counter : ℕ),
      simulateQ σ (FORS.Seeded.otsSignFrom (m := OracleComp FORS.HashSpec) key.publicSeed lay tree
        leaf key.secretSeed (FORS.Concrete.rootPayload message) attempts counter) =
        KeyGenerationAndSigning.otsSignFrom queryPermutation (toExpandedKey key) (toLayer lay) tree
          (toLeaf leaf) message attempts counter
  | 0, _ => by
    simp only [FORS.Seeded.otsSignFrom, KeyGenerationAndSigning.otsSignFrom]
    exact sim_pure _
  | attempts + 1, counter => by
    simp only [FORS.Seeded.otsSignFrom, KeyGenerationAndSigning.otsSignFrom, sim_bind,
      simulateQ_encode]
    refine bind_congr fun found ↦ ?_
    rcases found with _ | encoding
    · exact simulateQ_otsSignFrom key lay tree leaf message attempts (counter + 1)
    · simp only [sim_bind, sim_pure, simulateQ_otsSecrets, simulateQ_sequenceFin,
        simulateQ_chainWalk]
      rfl

theorem simulateQ_otsSign (key : FORS.Crate.ExpandedKey) (lay : FORS.Layer)
    (tree : FORS.TreeIndex) (leaf : FORS.LeafIndex) (message : FORS.Digest) :
    simulateQ σ (FORS.Crate.otsSign (m := OracleComp FORS.HashSpec) key lay tree leaf message) =
      KeyGenerationAndSigning.otsSign queryPermutation (toExpandedKey key) (toLayer lay) tree
        (toLeaf leaf) message :=
  simulateQ_otsSignFrom key lay tree leaf message _ _

/-! ## Trees, level by level -/

/-- **A tree's levels**: the copy's are the statement's when their nodes are, at every height
`h` and index `j` the levels reach: node `j` of the level `k + 1` above `below` exists for
`j < |below| / 2^(k + 1)`. -/
theorem simulateQ_merkleLevelsFrom
    (node : ℕ → ℕ → FORS.HashInput → OracleComp FORS.HashSpec FORS.Digest)
    (node' : ℕ → ℕ → HashInput → OracleComp RandomPermutationOracles Digest)
    (P : ℕ → ℕ → Prop)
    (hnode : ∀ h j payload, P h j → simulateQ σ (node h j payload) = node' h j payload) :
    ∀ (remaining height : ℕ) (below : List FORS.Digest),
      (∀ k j, k < remaining → j < below.length / 2 ^ (k + 1) → P (height + k + 1) j) →
      simulateQ σ (FORS.Crate.merkleLevelsFrom (m := OracleComp FORS.HashSpec) node height below
        remaining) =
        KeyGenerationAndSigning.merkleLevelsFrom node' height below remaining
  | 0, height, below, _ => by
    simp only [FORS.Crate.merkleLevelsFrom, KeyGenerationAndSigning.merkleLevelsFrom]
    exact sim_pure _
  | remaining + 1, height, below, hP => by
    simp only [FORS.Crate.merkleLevelsFrom, KeyGenerationAndSigning.merkleLevelsFrom, sim_bind,
      sim_pure, simulateQ_mapM]
    rw [mapM_congr_mem _ fun j hj ↦ hnode _ _ _
      (hP 0 j (by omega) (by simpa using List.mem_range.mp hj))]
    refine mapM_bind_congr _ _ _ _ fun above habove ↦ ?_
    rw [simulateQ_merkleLevelsFrom node node' P hnode remaining (height + 1) above
      fun k j hk hj ↦ by
      have h := hP (k + 1) j (by omega) (by
        rw [habove, List.length_range, Nat.div_div_eq_div_mul, ← Nat.pow_succ'] at hj
        exact hj)
      rwa [show height + (k + 1) + 1 = height + 1 + k + 1 by omega] at h]
    rfl

theorem toLeaf_leafOfNat (value : ℕ) :
    toLeaf (FORS.Concrete.leafOfNat value) = leafOfNat value := rfl

theorem simulateQ_treeLevels (key : FORS.Crate.ExpandedKey) (lay : FORS.Layer)
    (tree : FORS.TreeIndex) :
    simulateQ σ (FORS.Crate.treeLevels (m := OracleComp FORS.HashSpec) key lay tree) =
      KeyGenerationAndSigning.treeLevels queryPermutation (toExpandedKey key) (toLayer lay)
        tree := by
  simp only [FORS.Crate.treeLevels, KeyGenerationAndSigning.treeLevels, sim_bind,
    simulateQ_mapM, simulateQ_otsPublicLeaf, toLeaf_leafOfNat, layerHeight_toLayer,
    FORS.Crate.merkleLevels, KeyGenerationAndSigning.merkleLevels]
  refine bind_congr fun leaves ↦ ?_
  exact simulateQ_merkleLevelsFrom _ _ (fun _ _ ↦ True)
    (fun h j payload _ ↦ simulateQ_tweakableHash _ (.node _ _ h j) trivial payload) _ _ _
    fun _ _ _ _ ↦ trivial

/-! ## FORS -/

/-- Where a FORS tree's levels reach: heights `1 .. a`, node `j` of height `h` below `2^(a - h)`. -/
def ForsNodeInRange (height node : ℕ) : Prop :=
  1 ≤ height ∧ height ≤ 10 ∧ node < 2 ^ (10 - height)

theorem simulateQ_forsNodeHash (parameter : FORS.PublicParameter) (index : FORS.Index)
    (κ : FORS.FTree) (height node : ℕ) (payload : FORS.HashInput)
    (h : ForsNodeInRange height node) :
    simulateQ σ (FORS.Crate.forsNodeHash (m := OracleComp FORS.HashSpec) parameter index κ height
      node payload) =
      Verification.tweakableHash queryPermutation parameter (.forsNode index κ height node)
        payload := by
  obtain ⟨h1, h2, h3⟩ := h
  have hlt : height - 1 < FORS.forsHeight := by show height - 1 < 10; omega
  have hnode : node < 2 ^ FORS.forsHeight := by
    show node < 2 ^ 10
    exact lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by decide) (by omega))
  unfold FORS.Crate.forsNodeHash
  rw [dite_eq_left hlt, simulateQ_tweakableHash]
  · simp only [toDomain, FORS.Crate.forsLeafOfNat, Nat.mod_eq_of_lt hnode,
      show height - 1 + 1 = height by omega]
    rfl
  · show node % 2 ^ FORS.forsHeight < 2 ^ (10 - (height - 1 + 1))
    rw [Nat.mod_eq_of_lt hnode, show height - 1 + 1 = height by omega]
    exact h3

theorem simulateQ_forsTreeOpen (key : FORS.Crate.ExpandedKey) (index : FORS.Index)
    (κ : FORS.FTree) (leaf : FORS.FLeaf) :
    simulateQ σ (FORS.Crate.forsTreeOpen (m := OracleComp FORS.HashSpec) key index κ leaf) =
      Prod.map id toModelTreeOpening <$>
        KeyGenerationAndSigning.forsTreeOpen queryPermutation (toExpandedKey key) index κ leaf := by
  simp only [FORS.Crate.forsTreeOpen, KeyGenerationAndSigning.forsTreeOpen, sim_bind, sim_pure,
    simulateQ_mapM, simulateQ_prf_fors, map_bind, map_pure, FORS.Crate.merkleLevels,
    KeyGenerationAndSigning.merkleLevels]
  refine bind_congr fun secrets ↦ ?_
  simp only [FORS.Concrete.forsLeafHash]
  simp only [simulateQ_tweakableHash _ (.forsLeaf _ _ _) trivial]
  refine mapM_bind_congr _ _ _ _ fun leafHashes hleaves ↦ ?_
  rw [simulateQ_merkleLevelsFrom _ _ ForsNodeInRange
    (fun h j payload hj ↦ simulateQ_forsNodeHash _ _ _ h j payload hj) _ _ _ fun k j hk hj ↦ by
      change k < 10 at hk
      rw [hleaves, List.length_range] at hj
      change j < 2 ^ 10 / 2 ^ (k + 1) at hj
      rw [Nat.pow_div (by omega) (by decide)] at hj
      exact ⟨by omega, by omega, by rwa [Nat.zero_add]⟩]
  rfl

/-- `sequenceFin` through a map of its entries. -/
theorem sequenceFin_map {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} (g : α → β) :
    ∀ (n : ℕ) (f : Fin n → m α),
      sequenceFin (fun i ↦ g <$> f i) = (fun v ↦ g ∘ v) <$> sequenceFin f
  | 0, f => by
    simp only [sequenceFin, map_pure]
    congr 1
    funext i
    exact i.elim0
  | n + 1, f => by
    simp only [sequenceFin, map_bind, bind_map_left, map_pure]
    refine bind_congr fun head ↦ ?_
    rw [sequenceFin_map g n (fun i : Fin n ↦ f i.succ), bind_map_left]
    refine bind_congr fun tail ↦ ?_
    congr 1
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

theorem simulateQ_forsPublicKey (parameter : FORS.PublicParameter) (index : FORS.Index)
    (roots : FORS.FTree → FORS.Digest) :
    simulateQ σ (FORS.Concrete.forsPublicKey (m := OracleComp FORS.HashSpec) parameter index
      roots) = Verification.forsPublicKey queryPermutation parameter index roots :=
  simulateQ_tweakableHash _ (.forsRoots _) trivial _

theorem simulateQ_forsOpen (key : FORS.Crate.ExpandedKey) (index : FORS.Index)
    (leaves : FORS.FTree → FORS.FLeaf) :
    simulateQ σ (FORS.Crate.forsOpen (m := OracleComp FORS.HashSpec) key index leaves) =
      Prod.map id (fun opening forsTree ↦ toModelTreeOpening (opening forsTree)) <$>
        KeyGenerationAndSigning.forsOpen queryPermutation (toExpandedKey key) index leaves := by
  simp only [FORS.Crate.forsOpen, KeyGenerationAndSigning.forsOpen, sim_bind, sim_pure,
    simulateQ_sequenceFin, simulateQ_forsTreeOpen, map_bind,
    map_pure, simulateQ_forsPublicKey]
  refine (congrArg (· >>= _) (sequenceFin_map _ _ _)).trans ?_
  exact (bind_map_left _ _ _).trans (bind_congr fun trees ↦ rfl)

/-! ## Key generation -/

theorem simulateQ_keygenInternal (key : FORS.Crate.ExpandedKey) :
    simulateQ σ (FORS.Crate.keygenInternal (m := OracleComp FORS.HashSpec) key) =
      Prod.map toModelPublicKey id <$>
        KeyGenerationAndSigning.keygenInternal queryPermutation (toExpandedKey key) := by
  simp only [FORS.Crate.keygenInternal, KeyGenerationAndSigning.keygenInternal, sim_bind,
    sim_pure, simulateQ_treeLevels, map_bind, map_pure]
  rfl

/-- **Key generation**: the crate's, as FORS's copy writes it, is the statement's. -/
theorem simulateQ_keygen (seed : FORS.MasterSeed) :
    simulateQ σ (FORS.Crate.keygen (m := OracleComp FORS.HashSpec) seed) =
      Prod.map toModelPublicKey id <$>
        KeyGenerationAndSigning.keygenFromSeed queryPermutation seed := by
  simp only [FORS.Crate.keygen, KeyGenerationAndSigning.keygenFromSeed, sim_bind, sim_pure,
    simulateQ_expandKey, bind_map_left, map_bind, simulateQ_keygenInternal,
    toExpandedKey_ofExpandedKey]
  refine bind_congr fun key ↦ ?_
  exact (bind_map_left _ _ _).trans (bind_congr fun keys ↦ rfl)

/-! ## Signing -/

/-- A statement digest as the model's (the same bits). -/
def toModelDigest (digest : Digest) : FORS.Digest := digest

/-- A statement layer signature as the model's. -/
def toModelLayer (lay : FORS.Layer) (part : LayerSignature (toLayer lay)) :
    FORS.LayerSignature lay :=
  ⟨part.counter, part.chainValues,
    fun level ↦ part.authenticationPath (Fin.cast (layerHeight_toLayer lay).symm level)⟩

theorem simulateQ_signLayer (key : FORS.Crate.ExpandedKey) (top : List (List FORS.Digest))
    (index : FORS.Index) (lay : FORS.Layer) (message : FORS.Digest) :
    simulateQ σ (FORS.Crate.signLayer (m := OracleComp FORS.HashSpec) key top index lay message) =
      Option.map (Prod.map (toModelLayer lay) toModelDigest) <$>
        KeyGenerationAndSigning.signLayer queryPermutation (toExpandedKey key) top index
          (toLayer lay) message := by
  have htree := Model.treeIndexAt_eq index lay
  have hleaf := Model.leafIndexAt_eq index lay
  have hleafv : (FORS.Concrete.leafIndexAt index lay).val =
      (leafOfIndex (toLayer lay) index).val := congrArg Fin.val hleaf
  simp only [FORS.Crate.signLayer, KeyGenerationAndSigning.signLayer, sim_bind,
    simulateQ_otsSign, map_bind]
  refine bind_eq_of (by rw [htree, hleaf]) fun found ↦ ?_
  rcases found with _ | ⟨counter, values⟩
  · simp only [sim_pure, map_pure, Option.map_none]
  have hpair : ∀ levels : List (List Digest),
      (some (⟨counter, values, fun z ↦ FORS.Crate.levelNode levels z.val
          ((FORS.Concrete.leafIndexAt index lay).val >>> z.val ^^^ 1)⟩,
        FORS.Crate.levelNode levels (FORS.layerHeight lay) 0) :
          Option (FORS.LayerSignature lay × FORS.Digest)) =
        Option.map (Prod.map (toModelLayer lay) toModelDigest)
          (some (⟨counter, values, fun z ↦ KeyGenerationAndSigning.levelNode levels z.val
              ((leafOfIndex (toLayer lay) index).val >>> z.val ^^^ 1)⟩,
            KeyGenerationAndSigning.levelNode levels (layerHeight (toLayer lay)) 0)) := by
    intro levels
    simp only [Option.map_some, Prod.map, toModelLayer, hleafv, layerHeight_toLayer]
    rfl
  by_cases htop : lay = FORS.topLayer
  · have htop' : toLayer lay = topLayer := by rw [htop]; rfl
    simp only [sim_bind, sim_ite]
    rw [ite_eq_left htop, ite_eq_left htop']
    simp only [sim_pure, pure_bind]
    exact congrArg pure (hpair top)
  · have htop' : ¬toLayer lay = topLayer := fun h ↦ htop (by
      rw [← Model.ofLayer_toLayer lay, h]; rfl)
    simp only [sim_bind, sim_ite]
    rw [ite_eq_right htop, ite_eq_right htop']
    simp only [sim_pure, simulateQ_treeLevels, map_bind, map_pure]
    rw [htree]
    exact bind_congr fun levels ↦ congrArg pure (hpair levels)

theorem sim_signLayer_bind {β : Type} (key : FORS.Crate.ExpandedKey)
    (top : List (List FORS.Digest)) (index : FORS.Index) (lay : FORS.Layer)
    (message : FORS.Digest)
    (k : Option (FORS.LayerSignature lay × FORS.Digest) → OracleComp FORS.HashSpec β) :
    simulateQ σ (@Bind.bind (OracleComp FORS.HashSpec) _ _ _
      (FORS.Crate.signLayer key top index lay message) k) =
      KeyGenerationAndSigning.signLayer queryPermutation (toExpandedKey key) top index
        (toLayer lay) message >>= fun r ↦
          simulateQ σ (k (Option.map (Prod.map (toModelLayer lay) toModelDigest) r)) := by
  rw [sim_bind, simulateQ_signLayer]
  exact bind_map_left _ _ _

/-- One step of `sequenceThread`: the last index first. -/
theorem sequenceThread_succ {m : Type → Type} [Monad m] {S : Type} {n : ℕ}
    {α : Fin (n + 1) → Type} (c : (i : Fin (n + 1)) → S → m (Option (α i × S))) (s : S) :
    FORS.Concrete.sequenceThread c s = (do
      let some (last, next) ← c (Fin.last n) s | return none
      let some init ← FORS.Concrete.sequenceThread (α := fun i ↦ α i.castSucc)
          (fun i ↦ c i.castSucc) next | return none
      return some (Fin.lastCases (motive := α) last init)) := rfl

theorem sequenceThread_zero {m : Type → Type} [Monad m] {S : Type} {α : Fin 0 → Type}
    (c : (i : Fin 0) → S → m (Option (α i × S))) (s : S) :
    FORS.Concrete.sequenceThread c s = pure (some fun i ↦ Fin.elim0 i) := rfl

/-- The statement's layer signatures as the model's. -/
def toModelLayers (layers : (layer : Layer) → LayerSignature layer) :
    (lay : FORS.Layer) → FORS.LayerSignature lay :=
  fun lay ↦ toModelLayer lay (layers (toLayer lay))

theorem simulateQ_signLayers (key : FORS.Crate.ExpandedKey) (top : List (List FORS.Digest))
    (index : FORS.Index) (forsKey : FORS.Digest) :
    simulateQ σ (FORS.Concrete.sequenceThread (m := OracleComp FORS.HashSpec)
      (fun lay below ↦ FORS.Crate.signLayer key top index lay below) forsKey) = (do
      let some (bottom, bottomRoot) ← KeyGenerationAndSigning.signLayer queryPermutation
          (toExpandedKey key) top index 0 forsKey | return none
      let some (middle, middleRoot) ← KeyGenerationAndSigning.signLayer queryPermutation
          (toExpandedKey key) top index 1 bottomRoot | return none
      let some (topSignature, _) ← KeyGenerationAndSigning.signLayer queryPermutation
          (toExpandedKey key) top index 2 middleRoot | return none
      return some (toModelLayers
        (KeyGenerationAndSigning.layerSignatures bottom middle topSignature))) := by
  rw [sequenceThread_succ, sim_signLayer_bind]
  refine bind_eq_of rfl fun r ↦ ?_
  rcases r with _ | ⟨bottom, bottomRoot⟩
  · exact sim_pure _
  simp only [Option.map_some, Prod.map]
  rw [sequenceThread_succ, bind_assoc, sim_signLayer_bind]
  refine bind_eq_of rfl fun r ↦ ?_
  rcases r with _ | ⟨middle, middleRoot⟩
  · simp only [Option.map_none, pure_bind, sim_pure]
  simp only [Option.map_some, Prod.map]
  rw [sequenceThread_succ]
  simp only [bind_assoc]
  rw [sim_signLayer_bind]
  refine bind_eq_of rfl fun r ↦ ?_
  rcases r with _ | ⟨topSignature, topRoot⟩
  · simp only [Option.map_none, pure_bind, sim_pure]
  simp only [Option.map_some, Prod.map, sequenceThread_zero, pure_bind, sim_pure]
  congr 2
  funext lay
  fin_cases lay <;> rfl

theorem simulateQ_signWithExpandedKey (key : FORS.Crate.ExpandedKey) (message : FORS.Message) :
    simulateQ σ (FORS.Crate.signWithExpandedKey (m := OracleComp FORS.HashSpec) key message) =
      Option.map toModelSignature <$>
        KeyGenerationAndSigning.signWithExpandedKey queryPermutation (toExpandedKey key)
          message := by
  simp only [FORS.Crate.signWithExpandedKey, KeyGenerationAndSigning.signWithExpandedKey, sim_bind,
    map_bind]
  rw [simulateQ_keygenInternal]
  refine (bind_map_left _ _ _).trans (bind_eq_of rfl fun keys ↦ ?_)
  obtain ⟨publicKey, top⟩ := keys
  simp only [Prod.map, id]
  rw [simulateQ_prfMessage]
  refine bind_eq_of rfl fun randomizer ↦ ?_
  simp only [FORS.Concrete.messageDigest, Verification.messageDigest, bind_assoc, pure_bind,
    sim_bind, simulateQ_sequenceFin, simulateQ_messageDigestCall]
  refine bind_eq_of rfl fun outputs ↦ ?_
  have hindex : FORS.Concrete.digestIndex (FORS.truncateMessageDigest outputs) =
      digestIndex (truncateMessageDigest outputs) := digestIndex_eq outputs
  have hleaves : FORS.Concrete.digestLeaves (FORS.truncateMessageDigest outputs) =
      digestForsLeaves (truncateMessageDigest outputs) := digestLeaves_eq outputs
  simp only [sim_pure, pure_bind]
  rw [simulateQ_forsOpen]
  refine (bind_map_left _ _ _).trans ?_
  rw [← hindex, ← hleaves]
  refine bind_eq_of rfl fun fors ↦ ?_
  obtain ⟨forsKey, opening⟩ := fors
  revert forsKey top
  intro (top : List (List FORS.Digest)) (forsKey : FORS.Digest)
  simp only [Prod.map, id]
  rw [simulateQ_signLayers]
  simp only [bind_assoc]
  refine bind_eq_of rfl fun r ↦ ?_
  rcases r with _ | ⟨bottom, bottomRoot⟩
  · simp only [pure_bind, sim_pure, map_pure, Option.map_none]
  simp only [bind_assoc, map_bind]
  refine bind_eq_of rfl fun r ↦ ?_
  rcases r with _ | ⟨middle, middleRoot⟩
  · simp only [pure_bind, sim_pure, map_pure, Option.map_none]
  simp only [bind_assoc, map_bind]
  refine bind_eq_of rfl fun r ↦ ?_
  rcases r with _ | ⟨topSignature, topRoot⟩
  · simp only [pure_bind, sim_pure, map_pure, Option.map_none]
  simp only [pure_bind, sim_pure, map_pure, Option.map_some]
  rfl

/-- **Signing**: the crate's, as FORS's copy writes it, is the statement's. -/
theorem simulateQ_sign (seed : FORS.MasterSeed) (message : FORS.Message) :
    simulateQ σ (FORS.Crate.sign (m := OracleComp FORS.HashSpec) seed message) =
      Option.map toModelSignature <$>
        KeyGenerationAndSigning.sign queryPermutation seed message := by
  simp only [FORS.Crate.sign, KeyGenerationAndSigning.sign, sim_bind, simulateQ_expandKey,
    map_bind]
  exact (bind_map_left _ _ _).trans (bind_eq_of rfl fun key ↦
    simulateQ_signWithExpandedKey (ofExpandedKey key) message)

end Sphincs.CrateSim

namespace Sphincs.Model

open HashSig HashSig.OverPermutation Common Common.SufCma

attribute [local instance] params

local notation "σ" => schemeHashOverPermutation

/-- **The crate's key generation** (`key_gen_from_seed`, FORS's copy `FORS.Crate.keygen`), its
queries answered by Keccak-256 over `π`, is the statement's, through the map of public keys. -/
theorem simulateQ_crateKeygen (seed : FORS.MasterSeed) :
    (fun keys ↦ (ofModelPublicKey keys.1, keys.2)) <$>
      simulateQ σ (FORS.Crate.keygen seed : OracleComp FORS.HashSpec _) =
    KeyGenerationAndSigning.keygenFromSeed queryPermutation seed := by
  rw [CrateSim.simulateQ_keygen, Functor.map_map]
  exact (congrArg (· <$> _) (funext fun _ ↦ rfl)).trans (id_map _)

/-- **The crate's signer** (`sign`, FORS's copy `FORS.Crate.sign`), its queries answered by
Keccak-256 over `π`, is the statement's, through the map of signatures. -/
theorem simulateQ_crateSign (seed : FORS.MasterSeed) (message : FORS.Message) :
    Option.map ofModelSignature <$>
      simulateQ σ (FORS.Crate.sign seed message : OracleComp FORS.HashSpec _) =
    KeyGenerationAndSigning.sign queryPermutation seed message := by
  rw [CrateSim.simulateQ_sign, Functor.map_map]
  refine (congrArg (· <$> _) (funext fun signature ↦ ?_)).trans (id_map _)
  rcases signature with _ | signature
  · rfl
  · exact congrArg some (signatureEquiv.right_inv signature)

end Sphincs.Model
