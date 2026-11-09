module

public import FORS.Crate
public import FORS.Reduction.InternalizeGame

@[expose] public section

/-!
# The crate's algorithms make short queries only

Every hash input of the crate's key generation and signer (`Crate.lean`) has at most
`Short.bound = 2084` bytes, as FORS's own (`Short.Seeded.Only.keygen`, `Det.Only.seededSign`).
-/

open OracleComp

namespace FORS.Crate

variable [Params]

open Concrete Security Security.Short

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] digestAttemptLimit encodingAttemptLimit

theorem Only.mapM {α β : Type} (φ : α → OracleComp HashSpec β) (h : ∀ a, Short.Only (φ a)) :
    ∀ l : List α, Short.Only (l.mapM φ)
  | [] => Short.Only.pure' _
  | a :: l => by
      rw [List.mapM_cons]
      exact Short.Only.bind (h a) fun _ =>
        Short.Only.bind (Only.mapM φ h l) fun _ => Short.Only.pure' _

theorem Only.merkleLevelsFrom (node : Nat → Nat → HashInput → OracleComp HashSpec Digest)
    (hnode : ∀ height j left right, Short.Only (node height j (nodePayload left right))) :
    ∀ remaining height below, Short.Only (merkleLevelsFrom node height below remaining)
  | 0, _, _ => Short.Only.pure' _
  | remaining + 1, height, below => by
      rw [Crate.merkleLevelsFrom]
      exact Short.Only.bind (Only.mapM _ (fun _ => hnode _ _ _ _) _) fun _ =>
        Short.Only.bind (Only.merkleLevelsFrom node hnode remaining _ _) fun _ => Short.Only.pure' _

theorem Only.expandKey (seed : MasterSeed) :
    Short.Only (expandKey seed : OracleComp HashSpec ExpandedKey) := by
  unfold Crate.expandKey
  exact Short.Only.bind (Short.Only.derivePrf seed) fun _ =>
    Short.Only.bind (Short.Only.derivePublicSeed seed) fun _ => Short.Only.pure' _

theorem Only.treeLevels (key : ExpandedKey) (lay : Layer) (tree : TreeIndex) :
    Short.Only (treeLevels key lay tree : OracleComp HashSpec (List (List Digest))) := by
  unfold Crate.treeLevels Crate.otsPublicLeaf merkleLevels
  exact Short.Only.bind (Only.mapM _ (fun _ => Short.Only.bind
      (Short.Seeded.Only.oneTimePublicKey _ _ _ _ _) fun _ => Short.Only.leafHash _ _ _ _ _) _)
    fun _ => Only.merkleLevelsFrom _ (fun _ _ _ _ => Short.Only.tweakableHash _ _ _
      (by rw [nodePayload_length]; omega)) _ _ _

theorem Only.keygenInternal (key : ExpandedKey) :
    Short.Only (keygenInternal key : OracleComp HashSpec (PublicKey × List (List Digest))) := by
  unfold Crate.keygenInternal
  exact Short.Only.bind (Only.treeLevels _ _ _) fun _ => Short.Only.pure' _

theorem Only.keygen (seed : MasterSeed) :
    Short.Only (keygen seed : OracleComp HashSpec (PublicKey × MasterSeed)) := by
  unfold Crate.keygen
  exact Short.Only.bind (Only.expandKey seed) fun _ =>
    Short.Only.bind (Only.keygenInternal _) fun _ => Short.Only.pure' _

theorem Only.forsTreeOpen (key : ExpandedKey) (index : Index) (κ : FTree) (leaf : FLeaf) :
    Short.Only (forsTreeOpen key index κ leaf : OracleComp HashSpec (Digest × TreeOpening)) := by
  unfold Crate.forsTreeOpen merkleLevels
  refine Short.Only.bind (Only.mapM _ (fun _ => Short.Only.deriveKey _ _ _) _) fun _ =>
    Short.Only.bind (Only.mapM _ (fun _ => Short.Only.forsLeafHash _ _ _ _ _) _) fun _ =>
      Short.Only.bind (Only.merkleLevelsFrom _ (fun _ _ _ _ => ?_) _ _ _) fun _ => Short.Only.pure' _
  unfold forsNodeHash
  split
  · exact Short.Only.tweakableHash _ _ _ (by rw [nodePayload_length]; omega)
  · exact Short.Only.pure' _

theorem Only.forsOpen (key : ExpandedKey) (index : Index) (leaves : FTree → FLeaf) :
    Short.Only (forsOpen key index leaves : OracleComp HashSpec (Digest × (FTree → TreeOpening))) := by
  unfold Crate.forsOpen
  exact Short.Only.bind (Short.Only.sequenceFin _ fun _ => Only.forsTreeOpen _ _ _ _) fun _ =>
    Short.Only.bind (Short.Only.forsPublicKey _ _ _) fun _ => Short.Only.pure' _

theorem Only.signLayer (key : ExpandedKey) (top : List (List Digest)) (index : Index) (lay : Layer)
    (message : Digest) :
    Short.Only (signLayer key top index lay message :
      OracleComp HashSpec (Option (LayerSignature lay × Digest))) := by
  unfold Crate.signLayer Crate.otsSign Seeded.otsSign
  refine Short.Only.bind (Short.Seeded.Only.otsSignFrom _ _ _ _ _ _ (shortMessage_root message) _ _)
    fun result => ?_
  rcases result with _ | result
  · exact Short.Only.pure' _
  · obtain ⟨counter, values⟩ := result
    dsimp only
    split
    · exact Short.Only.bind (Short.Only.pure' _) fun _ => Short.Only.pure' _
    · exact Short.Only.bind (Only.treeLevels _ _ _) fun _ => Short.Only.pure' _

theorem Only.prfMessage (secretPrfKey : HashOutput) (publicSeed : PublicParameter)
    (message : Message) :
    Short.Only (prfMessage secretPrfKey publicSeed message : OracleComp HashSpec Randomness) := by
  unfold Crate.prfMessage
  exact Short.Only.bind (Short.Only.query (Det.randomizerHashInput_short _ _ _)) fun _ =>
    Short.Only.pure' _

theorem Only.sign (seed : MasterSeed) (message : Message) :
    Short.Only (sign seed message : OracleComp HashSpec (Option Signature)) := by
  unfold Crate.sign Crate.signWithExpandedKey
  refine Short.Only.bind (Only.expandKey seed) fun key => ?_
  refine Short.Only.bind (Only.keygenInternal key) fun pair => ?_
  refine Short.Only.bind (Only.prfMessage _ _ _) fun randomizer => ?_
  refine Short.Only.bind (Short.Only.messageDigest _ _ _ _) fun digest => ?_
  refine Short.Only.bind (Only.forsOpen _ _ _) fun opened => ?_
  refine Short.Only.bind (Short.Only.sequenceThread
    (fun i state => Only.signLayer key pair.2 (digestIndex digest) i state) _)
    fun layers => ?_
  rcases layers with _ | layers <;> exact Short.Only.pure' _

end FORS.Crate
