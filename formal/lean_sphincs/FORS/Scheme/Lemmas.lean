import FORS.Scheme

/-! Facts about the specification (`Scheme.lean`): the definitions that only the proofs use, the
randomizer walk, which does not come back within `2^128` steps (`walk_iterate_ne`), and the bounds
that the parameters (`Params`) give. -/

namespace FORS

variable [Params]

/-! ### Definitions of the proofs

Values that the specification does not use but the proofs name: the bottom layer, the order of the
layers in a signature, the key on the path of an index, the kept leaves, the start of a single
chain, and the end of a signature once a randomizer lands. -/

/-- The bottom layer, whose WOTS+C keys sign the FORS keys. -/
def bottomLayer : Layer := ⟨numLayers - 1, Nat.sub_lt Params.numLayers_pos Nat.one_pos⟩

/-- The layer `k` steps above the bottom one (the top layer from `k = numLayers - 1` on): the
signature lists the layers in that order. -/
def layerUp (k : Nat) : Layer := ⟨numLayers - 1 - k, by have := Params.numLayers_pos; omega⟩

/-- A leaf of a layer's tree that its kept part holds: one of the top layer's kept subtree, any leaf
below the top layer. -/
def Kept (parameter : PublicParameter) (lay : Layer) (leaf : LeafIndex) : Prop :=
  leaf.val / 2 ^ keptHeight lay = keptPosition parameter lay

namespace Concrete

/-- A WOTS+C key of the hypertree: its layer, its tree and its leaf in that tree. -/
abbrev OtsKey := Layer × TreeIndex × LeafIndex

/-- The key of layer `lay` on the path of `idx`. -/
def keyAt (index : Index) (lay : Layer) : OtsKey := (lay, treeIndexAt index lay, leafIndexAt index lay)

end Concrete

namespace Seeded

open Concrete

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The start of one chain of a one-time key, by its own derivation. The signer calls `otsSecrets`;
this is the value of each of its entries (`Completeness.eval_otsSecrets`). -/
def otsStart (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (seed : MasterSeed) : m Digest := do
  let output ← deriveOutput parameter (.ots lay tree leaf (chainPair chainIdx)) seed
  return hashHalf chainIdx.val output

/-- Assemble the signature once a randomizer lands: the digest, the FORS opening and the layers. -/
def finishSign (sk : SecretKey) (message : Message) (randomness : Randomness) :
    OracleComp HashSpec (Option Signature) := do
  let digest ← messageDigest sk.parameter sk.root message randomness
  let index := digestIndex digest
  let opening ← forsOpen sk.parameter index (digestLeaves digest) sk.seed
  let some layers ← sequenceLayers (fun lay => signLayer sk index lay) | return none
  return some ⟨randomness, opening, layers⟩

end Seeded

/-! ### The randomizer walk -/

theorem walkStep_toNat_mod_two (half : Randomness) : (walkStep half).toNat % 2 = 1 := by
  unfold walkStep
  rw [BitVec.toNat_or, Nat.or_mod_two_eq_one]
  right
  rfl

/-- `j` steps of the walk from `y`. -/
theorem walk_iterate (step y : Randomness) (j : Nat) :
    (fun x : Randomness => x + step)^[j] y = y + (j : Randomness) * step := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      push_cast
      ring

/-- A walk with an odd step does not come back within `2^128` steps. -/
theorem walk_iterate_ne (half y : Randomness) (j : Nat) (hj : j + 1 < 2 ^ 128) :
    (fun x : Randomness => x + walkStep half)^[j] (y + walkStep half) ≠ y := by
  rw [walk_iterate]
  intro h
  have hzero : ((j + 1 : Nat) : Randomness) * walkStep half = 0 := by
    push_cast
    linear_combination h
  have h2 := congrArg BitVec.toNat hzero
  have hd : (2 : Nat) ^ digestBits = 2 ^ 128 := rfl
  rw [BitVec.toNat_mul, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, hd, Nat.mod_eq_of_lt hj] at h2
  have hdvd : 2 ^ 128 ∣ (j + 1) * (walkStep half).toNat := Nat.dvd_of_mod_eq_zero h2
  have hcop : Nat.Coprime (2 ^ 128) (walkStep half).toNat :=
    Nat.Coprime.pow_left 128 (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (walkStep_toNat_mod_two half)))
  have := Nat.le_of_dvd (Nat.succ_pos j) (hcop.dvd_of_dvd_mul_right hdvd)
  omega

/-! ### Bounds of the parameters -/

/-- A bit vector determines the natural it encodes, below the wrap. -/
theorem ofNat_inj_of_lt' {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : BitVec.ofNat w a = BitVec.ofNat w b) : a = b := by
  have htoNat := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at htoNat

theorem totalHeight_le_28 : totalHeight ≤ 28 := Params.totalHeight_le

theorem subtreeHeight_le_total : subtreeHeight ≤ totalHeight := Params.subtreeHeight_le

theorem numLayers_pos : 0 < numLayers := Params.numLayers_pos

/-- The index field lies inside the first digest call. -/
theorem totalHeight_le_hashOutput : totalHeight ≤ hashOutputBits := by
  have := totalHeight_le_28
  unfold hashOutputBits
  omega

/-- The index field lies inside the truncated digest. -/
theorem totalHeight_le_digest : totalHeight ≤ messageDigestBits := by
  unfold messageDigestBits
  omega

theorem two_pow_totalHeight_le : 2 ^ totalHeight ≤ 2 ^ 28 :=
  Nat.pow_le_pow_right (by decide) totalHeight_le_28

theorem index_lt_two_pow_32 (index : Index) : index.val < 2 ^ 32 :=
  lt_of_lt_of_le index.isLt (two_pow_totalHeight_le.trans (by decide))

theorem maxLayerHeight_le : maxLayerHeight ≤ totalHeight := Nat.sub_le _ _

/-- The top layer is at least as tall as a lower one. -/
theorem lowerHeight_le_max : lowerHeight ≤ maxLayerHeight := by
  have h1 := Params.lower_le
  have h2 := Params.numLayers_pos
  unfold maxLayerHeight
  have : lowerHeight * numLayers = lowerHeight * (numLayers - 1) + lowerHeight := by
    rw [← Nat.mul_succ]; congr 1; omega
  omega

theorem lowerHeight_pos : 0 < lowerHeight := lt_of_lt_of_le (by decide) Params.lowerHeight_ge

theorem maxLayerHeight_pos : 0 < maxLayerHeight :=
  lt_of_lt_of_le lowerHeight_pos lowerHeight_le_max

/-- The truncated digest lies inside the concatenated calls. -/
theorem messageDigestBits_le : messageDigestBits ≤ hashOutputBits * digestCalls := by
  unfold digestCalls hashOutputBits
  have h := Nat.div_add_mod (messageDigestBits + 256 - 1) 256
  have h2 := Nat.mod_lt (messageDigestBits + 256 - 1) (by decide : 0 < 256)
  omega

theorem forsHeight_pos : 0 < forsHeight := lt_of_lt_of_le (by decide) Params.forsHeight_ge

/-- A leaf index field lies inside the truncated digest. -/
theorem leafOffset_add_le (κ : FTree) : Concrete.leafOffset κ + forsHeight ≤ messageDigestBits := by
  unfold Concrete.leafOffset messageDigestBits
  have h := κ.isLt
  have : forsHeight * κ.val + forsHeight = forsHeight * (κ.val + 1) := by ring
  have : forsHeight * (κ.val + 1) ≤ forsTrees * forsHeight := by
    rw [mul_comm]; exact Nat.mul_le_mul_right _ h
  omega

/-- At most 4 layers: the layers below the top have height at least 6 and `h ≤ 28`. -/
theorem numLayers_le : numLayers ≤ 4 := by
  have h1 := Params.lower_le
  have := totalHeight_le_28
  have h2 : 6 * numLayers ≤ lowerHeight * numLayers := Nat.mul_le_mul_right numLayers Params.lowerHeight_ge
  omega

theorem tree_lt_two_pow_32 (tree : TreeIndex) : tree.val < 2 ^ 32 :=
  lt_of_lt_of_le tree.isLt (two_pow_totalHeight_le.trans (by decide))

theorem leaf_lt_two_pow_32 (leaf : LeafIndex) : leaf.val < 2 ^ 32 :=
  lt_of_lt_of_le leaf.isLt ((Nat.pow_le_pow_right (by decide) maxLayerHeight_le).trans
    (two_pow_totalHeight_le.trans (by decide)))

/-- The layer byte names the layer. -/
theorem layerByte_lt (lay : Layer) : layerByte lay < 2 ^ 8 := by
  have := numLayers_le
  unfold layerByte
  omega

theorem layerByte_injective {lay lay' : Layer} (h : layerByte lay = layerByte lay') : lay = lay' := by
  have := lay.isLt; have := lay'.isLt
  unfold layerByte at h
  exact Fin.ext (by omega)

/-- The layer byte, as encoded, names the layer. -/
theorem layerByte_ofNat_injective {lay lay' : Layer}
    (h : BitVec.ofNat 8 (layerByte lay) = BitVec.ofNat 8 (layerByte lay')) : lay = lay' :=
  layerByte_injective (ofNat_inj_of_lt' (layerByte_lt lay) (layerByte_lt lay') h)

end FORS
