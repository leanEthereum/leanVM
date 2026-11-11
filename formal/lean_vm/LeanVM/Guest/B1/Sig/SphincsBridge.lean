/-
  LeanVM.Guest.B1.Sig.SphincsBridge

  The statement's leanSPHINCS verification (`Sphincs.verifyWithKeccak`, `Statement/LeanSphincs.lean`
  at leanVM main `40f877dc`) stage by stage: its message digest, its FORS key, and its walk up the layers.
-/

module

public import LeanVM.Guest.B1.Sig.Interface

/-!
# leanSPHINCS's verification by stages

The guest computes `Sphincs.verifyWithKeccak` in stages (`Id` over `keccakF1600`):

* `sDigestOf`, `sForsKeyOf`: the message digest a signature's randomizer gives, and the FORS public
  key its openings recover at the digest's index and leaves;
* `layerRoot`, `LayerReaches`, `layerReaches_iff`: the root a layer reaches from the value its
  one-time key signs;
* `verifyWithKeccak_iff_stages`: verification holds exactly when, from the FORS key, each layer's
  one-time key recovers a leaf whose path reaches a root, the next layer signing that root, the top
  one reaching the key's root.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Semantics
open HashSig HashSig.OverPermutation
open Sphincs Sphincs.Verification

@[expose] public section

/-! ## Verification by stages -/

/-- The message digest a signature's randomizer gives. -/
def sDigestOf (pk : Sphincs.PublicKey) (m : Message) (sig : Sphincs.Signature) : MessageDigest :=
  Id.run (messageDigest (m := Id) (keccakHash keccakF1600) pk sig.randomizer m)

/-- The FORS key a signature's openings recover at its digest. -/
def sForsKeyOf (pk : Sphincs.PublicKey) (m : Message) (sig : Sphincs.Signature) : HashSig.Digest :=
  Id.run (forsRecover (m := Id) (keccakHash keccakF1600) pk.publicSeed (digestIndex (sDigestOf pk m sig))
    (digestForsLeaves (sDigestOf pk m sig)) sig.forsOpening)

/-- **The root layer `l` reaches from `msg`**: its one-time key `K_l(idx)` recovers a leaf from the
message `msg` and the layer's counter and chain values, and the layer's path folds it to the root;
nothing when the counter does not encode `msg`. -/
def layerRoot (P : PublicParameter) (idx : Index) (sig : Sphincs.Signature) (l : Layer)
    (msg : HashSig.Digest) : Option HashSig.Digest :=
  match Id.run (otsLeaf (m := Id) (keccakHash keccakF1600) P l (treeOfIndex l idx) (leafOfIndex l idx) msg
      (sig.layers l).counter (sig.layers l).chainValues) with
  | none => none
  | some v => some (Id.run (treeFold (m := Id) (keccakHash keccakF1600) P l (treeOfIndex l idx) (leafOfIndex l idx)
      (layerPath sig l) (layerHeight l) v))

/-- **Layer `l` of the signature reaches `root` from `msg`.** -/
def LayerReaches (P : PublicParameter) (idx : Index) (sig : Sphincs.Signature) (l : Layer)
    (msg : HashSig.Digest) (root : HashSig.Digest) : Prop :=
  layerRoot P idx sig l msg = some root

/-- A layer reaches `root`: its one-time leaf is recovered, and its path folds the leaf to `root`. -/
theorem layerReaches_iff (P : PublicParameter) (idx : Index) (sig : Sphincs.Signature) (l : Layer)
    (msg : HashSig.Digest) (root : HashSig.Digest) :
    LayerReaches P idx sig l msg root ↔
      ∃ v, Id.run (otsLeaf (m := Id) (keccakHash keccakF1600) P l (treeOfIndex l idx) (leafOfIndex l idx) msg
          (sig.layers l).counter (sig.layers l).chainValues) = some v ∧
        Id.run (treeFold (m := Id) (keccakHash keccakF1600) P l (treeOfIndex l idx) (leafOfIndex l idx)
          (layerPath sig l) (layerHeight l) v) = root := by
  unfold LayerReaches layerRoot
  split <;> simp_all

/-- One layer of the walk up, in `Id`. -/
theorem verifyLayers_succ_eq (P : PublicParameter) (idx : Index) (sig : Sphincs.Signature) (n : Nat)
    (hn : n < layerCount) (msg : HashSig.Digest) :
    Id.run (verifyLayers (m := Id) (keccakHash keccakF1600) P idx sig (n + 1) msg) =
      (layerRoot P idx sig ⟨layerCount - 1 - n, by omega⟩ msg).bind fun r =>
        if n = 0 then some r else Id.run (verifyLayers (m := Id) (keccakHash keccakF1600) P idx sig n r) := by
  rw [verifyLayers.eq_2]
  simp only [hn, ↓reduceDIte, Id.run_bind, layerRoot]
  generalize Id.run (otsLeaf (m := Id) (keccakHash keccakF1600) P ⟨layerCount - 1 - n, by omega⟩
    (treeOfIndex ⟨layerCount - 1 - n, by omega⟩ idx) (leafOfIndex ⟨layerCount - 1 - n, by omega⟩ idx) msg
    (sig.layers ⟨layerCount - 1 - n, by omega⟩).counter (sig.layers ⟨layerCount - 1 - n, by omega⟩).chainValues) = o
  rcases o with _ | v
  · rfl
  · simp only [Option.bind_some, Id.run_bind]
    split <;> rfl

/-- The walk up the three layers, in `Id`. -/
theorem verifyLayers_three (P : PublicParameter) (idx : Index) (sig : Sphincs.Signature)
    (msg : HashSig.Digest) :
    Id.run (verifyLayers (m := Id) (keccakHash keccakF1600) P idx sig layerCount msg) =
      (layerRoot P idx sig 0 msg).bind fun r0 => (layerRoot P idx sig 1 r0).bind
        fun r1 => layerRoot P idx sig 2 r1 := by
  conv_lhs => rw [show layerCount = 2 + 1 from rfl]
  rw [verifyLayers_succ_eq P idx sig 2 (by decide)]
  simp only [show (2 : Nat) ≠ 0 by decide, ↓reduceIte,
    verifyLayers_succ_eq P idx sig 1 (by decide), show (1 : Nat) ≠ 0 by decide,
    verifyLayers_succ_eq P idx sig 0 (by decide), show (⟨layerCount - 1 - 2, by decide⟩ : Layer) = 0 from rfl,
    show (⟨layerCount - 1 - 1, by decide⟩ : Layer) = 1 from rfl,
    show (⟨layerCount - 1 - 0, by decide⟩ : Layer) = 2 from rfl]
  simp only [Option.bind_fun_some]

/-- The walk reaches `root` exactly when each layer reaches the next one's message. -/
theorem verifyLayers_some (P : PublicParameter) (idx : Index) (sig : Sphincs.Signature)
    (msg : HashSig.Digest) (root : HashSig.Digest) :
    Id.run (verifyLayers (m := Id) (keccakHash keccakF1600) P idx sig layerCount msg) = some root ↔
      ∃ r0 r1, LayerReaches P idx sig 0 msg r0 ∧ LayerReaches P idx sig 1 r0 r1 ∧
        LayerReaches P idx sig 2 r1 root := by
  rw [verifyLayers_three]
  simp only [LayerReaches, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨a, h0, b, h1, h2⟩
    exact ⟨a, b, h0, h1, h2⟩
  · rintro ⟨a, b, h0, h1, h2⟩
    exact ⟨a, h0, b, h1, h2⟩

/-- leanSPHINCS verification in `Id`, over any permutation: the walk up the layers reaches the
key's root. -/
theorem verify_id_eq_true (π : KeccakState → KeccakState) (pk : Sphincs.PublicKey) (m : Message)
    (sig : Sphincs.Signature) :
    Id.run (Verification.verify (m := Id) (HashSig.OverPermutation.keccakHash π) pk m sig) = true ↔
      Id.run (verifyLayers (m := Id) (keccakHash π) pk.publicSeed
          (digestIndex (Id.run (messageDigest (m := Id) (keccakHash π) pk sig.randomizer m))) sig layerCount
          (Id.run (forsRecover (m := Id) (keccakHash π) pk.publicSeed
            (digestIndex (Id.run (messageDigest (m := Id) (keccakHash π) pk sig.randomizer m)))
            (digestForsLeaves (Id.run (messageDigest (m := Id) (keccakHash π) pk sig.randomizer m)))
            sig.forsOpening))) = some pk.root := by
  unfold Verification.verify
  simp only [Id.run_bind]
  split <;> simp_all

/-- **leanSPHINCS verification by stages**: a signature verifies exactly when, from the FORS key
its openings recover at its digest, the bottom layer reaches a root `r0`, the middle one from `r0`
a root `r1`, and the top one from `r1` the key's root. -/
theorem verifyWithKeccak_iff_stages (pk : Sphincs.PublicKey) (m : Message) (sig : Sphincs.Signature) :
    Sphincs.verifyWithKeccak pk m sig = true ↔
      ∃ r0 r1, LayerReaches pk.publicSeed (digestIndex (sDigestOf pk m sig)) sig 0
          (sForsKeyOf pk m sig) r0 ∧
        LayerReaches pk.publicSeed (digestIndex (sDigestOf pk m sig)) sig 1 r0 r1 ∧
        LayerReaches pk.publicSeed (digestIndex (sDigestOf pk m sig)) sig 2 r1 pk.root := by
  rw [← verifyLayers_some, Sphincs.verifyWithKeccak, verify_id_eq_true]
  rfl

end
end LeanVM.Guest.B1.Sig
