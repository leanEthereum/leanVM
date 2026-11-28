module

public import NativeRustc.Sphincs.Digest
public import Native.Sphincs.LayerSpec

/-!
# The Rust functions are the statement's

Each function of `NativeRustc.Sphincs.Model` on the bytes of the statement's values (a digest `d`
as `le16 d`, `PK.seed` as `littleEndianBytes 16`) is the statement's function of
`Sphincs.Verification` over Keccak-f[1600]: `th` at an address (`th_eq`, `th_adrs`, and its
streaming form through the `Hasher`, `th_hasher`), the key of an index (`ofIndex_tree`,
`ofIndex_leaf`), a chain (`chain_eq`), the encoding (`encodeDigest_eq`), the one-time leaf
(`wotsLeaf_eq`), `path_fold` (`pathFold_eq`), `tree_fold` (`treeFold_eq`) and FORS
(`forsRecover_eq`).
-/

@[expose] public section

namespace NativeRustc.Sphincs

open _root_.Sphincs HashSig HashSig.OverPermutation LeanVM.Protocol.KeccakHash NativeRustc.Keccak
  Native.Keccak

/-! ## The tweakable hash -/

/-- **`th` is the statement's addressed hash** on `PK.seed`'s bytes and the address's. -/
theorem th_eq (seed : PublicParameter) (address : Address) (m : HashInput) :
    th (littleEndianBytes 16 seed) address.toBytes m =
      le16 (Id.run (Verification.addressedHash (m := Id) LeanVM.Semantics.keccakF1600 seed address
        m)) := by
  rw [Verification.addressedHash, Id.run_bind, Id.run_pure, Native.truncate_keccakHash,
    le16_ofWords, th, hashBytes, take16_digestBytes]
  rfl

/-- `th` at the address of the eight words' numbers. -/
theorem th_adrs (seed : PublicParameter) (m : HashInput) {layer : UInt32} {tree : UInt64}
    {t kp ch h : UInt32} {aty : AddressType} {layerN treeN kpN chN hN : Nat}
    (hl : layer.toNat = layerN) (htr : tree.toNat = treeN) (ht : t.toNat = aty.word)
    (hkp : kp.toNat = kpN) (hch : ch.toNat = chN) (hh : h.toNat = hN) :
    th (littleEndianBytes 16 seed) (adrsBytes layer tree t kp ch h) m =
      le16 (Id.run (Verification.addressedHash (m := Id) LeanVM.Semantics.keccakF1600 seed
        (makeAddress layerN treeN aty kpN chN hN) m)) := by
  rw [adrsBytes_eq hl htr ht hkp hch hh, th_eq]

/-- **`th` through the `Hasher`**: new, updated with `PK.seed`, the address and the payload,
finalized, truncated. -/
theorem th_hasher (seed adrs m : List UInt8) :
    th seed adrs m = (finalize (update (update (update new seed) adrs) m)).take 16 := by
  rw [finalize_eq (holds_update (holds_update (holds_update holds_new seed) _) m), th, hashBytes,
    List.nil_append]

/-- **`encode`'s digest through the `Hasher`**: the `encoder` (new, updated with `PK.seed`, the
address and the message), updated with the counter, finalized, truncated. -/
theorem encodeDigest_hasher (seed : List UInt8) (key : OtsKey) (message : List UInt8) (c : UInt32) :
    encodeDigest seed key message c =
      (finalize (update (update (update (update new seed) (key.adrs 7)) message) (be32 c))).take
        16 := by
  rw [finalize_eq (holds_update (holds_update (holds_update (holds_update holds_new seed) _) _) _),
    encodeDigest, hashBytes, List.nil_append]

/-- **`h_msg`'s call `i` through the `Hasher`**: the hasher updated with `R`, `PK.seed`, `PK.root`
and `M`, updated with `BE_32(i)`, finalized. -/
theorem hMsgCall_hasher (r seed root m : List UInt8) (i : UInt32) :
    hashBytes (r ++ seed ++ root ++ m ++ be32 i) =
      finalize (update (update (update (update (update new r) seed) root) m) (be32 i)) := by
  rw [finalize_eq (holds_update (holds_update (holds_update (holds_update (holds_update holds_new
    r) _) _) _) _), hashBytes, List.nil_append]

/-! ## The keys -/

/-- The key of an index on layer `l` is on layer `l`. -/
theorem ofIndex_layer (l : Nat) (idx : UInt64) : (OtsKey.ofIndex l idx).layer = l := rfl

/-- **The key's tree** is the statement's. -/
theorem ofIndex_tree (layer : Layer) {idx : UInt64} {index : Index} (h : idx.toNat = index.val) :
    (OtsKey.ofIndex layer.val idx).tree.toNat = (treeOfIndex layer index).val := by
  obtain ⟨l, hl⟩ := layer
  have : l < 3 := hl
  interval_cases l <;>
    simp [OtsKey.ofIndex, layerHeights, UInt64.toNat_shiftRight, treeOfIndex, bitsBelowLayer,
      layerHeight, Nat.shiftRight_eq_div_pow, h, Nat.div_div_eq_div_mul]

/-- `e & ((1 << h) - 1)` is `e mod 2^h`. -/
theorem toNat_and_mask (e : UInt64) {h : Nat} (hh : h < 64) :
    (e &&& ((1 <<< h.toUInt64) - 1)).toNat = e.toNat % 2 ^ h := by
  have hp : 2 ^ h < 2 ^ 64 := Nat.pow_lt_pow_right (by omega) hh
  have h1 : ((1 : UInt64) <<< h.toUInt64).toNat = 2 ^ h := by
    rw [UInt64.toNat_shiftLeft, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega : h < 2 ^ 64), Nat.mod_eq_of_lt hh]
    simp only [UInt64.reduceToNat, Nat.one_mul]
    exact Nat.mod_eq_of_lt hp
  have hle : (1 : UInt64) ≤ 1 <<< h.toUInt64 := by
    rw [UInt64.le_iff_toNat_le, h1]
    exact Nat.one_le_two_pow
  rw [UInt64.toNat_and, UInt64.toNat_sub_of_le _ _ hle, h1, show (1 : UInt64).toNat = 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- **The key's leaf** is the statement's. -/
theorem ofIndex_leaf (layer : Layer) {idx : UInt64} {index : Index} (h : idx.toNat = index.val) :
    (OtsKey.ofIndex layer.val idx).leaf.toNat = (leafOfIndex layer index).val := by
  obtain ⟨l, hl⟩ := layer
  have hl3 : l < 3 := hl
  have hi : index.val < 2 ^ 26 := index.isLt
  have hh : layerHeights.getD l 0 < 64 := by interval_cases l <;> decide
  simp only [OtsKey.ofIndex]
  rw [UInt64.toNat_toUInt32, toNat_and_mask _ hh, UInt64.toNat_shiftRight, h]
  interval_cases l <;>
    simp [layerHeights, leafOfIndex, bitsBelowLayer, layerHeight, Nat.shiftRight_eq_div_pow] <;>
    omega

theorem layer_toUInt32 (layer : Layer) : layer.val.toUInt32.toNat = layer.val := by
  have : layer.val < 3 := layer.isLt
  rw [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]

/-! ## WOTS+C -/

/-- **`chain` is the statement's chain walk** of the key `(layer, tree, leaf)`. -/
theorem chain_eq (seed : PublicParameter) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    {key : OtsKey} (hl : key.layer = layer.val) (ht : key.tree.toNat = tree.val)
    (hf : key.leaf.toNat = leaf.val) (i : ChainIndex) (start : Nat) :
    ∀ steps, start + steps ≤ 3 → ∀ v : Digest,
      chain (littleEndianBytes 16 seed) key i.val start steps (le16 v) =
        le16 (Id.run (Verification.chainWalk (m := Id) LeanVM.Semantics.keccakF1600 seed layer tree
          leaf i start steps v))
  | 0, _, _ => rfl
  | steps + 1, hs, v => by
    have ih := chain_eq seed layer tree leaf hl ht hf i start steps (by omega) v
    rw [chain, List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil, ← chain, ih]
    unfold Verification.chainWalk
    rw [walkChain, Id.run_bind, dite_eq_left (by unfold chainLength winternitzBits; omega)]
    have hi : i.val < 64 := i.isLt
    rw [OtsKey.adrs_eq, withChain_eq, withHash_eq, th_adrs seed _ (aty := .wotsHash)
      (by rw [hl, layer_toUInt32]) ht rfl hf
      (by rw [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)])
      (by rw [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)])]
    simp only [Nat.one_mul]
    rfl

/-- **`encode`'s digest** is the statement's encoding hash. -/
theorem encodeDigest_eq (seed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) {key : OtsKey} (hl : key.layer = layer.val)
    (ht : key.tree.toNat = tree.val) (hf : key.leaf.toNat = leaf.val) (msg : Digest) {c : UInt32}
    {c' : EncodingCounter} (hc : c.toNat = c'.toNat) :
    encodeDigest (littleEndianBytes 16 seed) key (le16 msg) c =
      le16 (Native.SphincsVerifier.encDigest seed layer tree leaf msg c') := by
  have hc' : BitVec.ofNat 32 c.toNat = c' :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, hc]; exact Nat.mod_eq_of_lt c'.isLt)
  rw [encodeDigest, List.append_assoc _ (le16 msg), ← th, OtsKey.adrs_eq,
    th_adrs seed _ (aty := .wotsEncoding) (by rw [hl, layer_toUInt32]) ht rfl hf rfl rfl, be32_eq,
    hc']
  rfl

/-- **`wots_leaf`'s leaf is the statement's one-time leaf** of the key `(layer, tree, leaf)`. -/
theorem wotsLeaf_eq (seed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) {key : OtsKey} (hl : key.layer = layer.val)
    (ht : key.tree.toNat = tree.val) (hf : key.leaf.toNat = leaf.val) (msg : Digest) {c : UInt32}
    {c' : EncodingCounter} (hc : c.toNat = c'.toNat) (values : ChainIndex → Digest) :
    (wotsLeaf (littleEndianBytes 16 seed) key (le16 msg) c
        (List.ofFn fun i ↦ le16 (values i))).map Prod.snd =
      (Id.run (Verification.otsLeaf (m := Id) LeanVM.Semantics.keccakF1600 seed layer tree leaf msg
        c' values)).map le16 := by
  rw [Native.SphincsVerifier.otsLeaf_id]
  unfold wotsLeaf encode
  rw [encodeDigest_eq seed layer tree leaf hl ht hf msg hc, codeword_eq]
  generalize Native.SphincsVerifier.encDigest seed layer tree leaf msg c' = D
  unfold TargetSum.Valid targetSum
  by_cases hv : TargetSum.sum (TargetSum.base2bDigits D) = 128
  · rw [ite_eq_left hv, ite_eq_left hv]
    have hends : ((List.range 64).map fun i ↦ chain (littleEndianBytes 16 seed) key i
        ((digits (beNat (le16 D))).getD i 0).toNat (3 - ((digits (beNat (le16 D))).getD i 0).toNat)
        ((List.ofFn fun i ↦ le16 (values i)).getD i [])) =
        List.ofFn fun i : ChainIndex ↦ le16 (Id.run (Verification.chainWalk (m := Id)
          LeanVM.Semantics.keccakF1600 seed layer tree leaf i (TargetSum.base2bDigits D i).val
          (3 - (TargetSum.base2bDigits D i).val) (values i))) := by
      apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_ofFn]; rfl)
      intro i h1 h2
      have hi : i < 64 := by simpa using h1
      rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      have hv : (List.ofFn fun i ↦ le16 (values i)).getD i [] = le16 (values ⟨i, hi⟩) := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hi), Option.getD_some,
          List.getElem_ofFn]
      have hd3 : (TargetSum.base2bDigits D ⟨i, hi⟩).val ≤ 3 :=
        Nat.le_of_lt_succ (TargetSum.base2bDigits D ⟨i, hi⟩).isLt
      rw [hv, getD_digits D hi]
      exact chain_eq seed layer tree leaf hl ht hf ⟨i, hi⟩ _ _ (by omega) _
    dsimp only
    rw [hends, Option.map_some, Option.map_some, wotsLeafHash, OtsKey.adrs_eq,
      th_adrs seed _ (aty := .wotsPublicKey) (by rw [hl, layer_toUInt32]) ht rfl hf rfl rfl,
      flatten_ofFn]
    rfl
  · rw [ite_eq_right hv, ite_eq_right hv]
    rfl

/-! ## Merkle paths -/

/-- The node's side: bit `j` of the index. -/
theorem and_one_iff {e j : Nat} : e >>> j &&& 1 = 0 ↔ e.testBit j = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod,
    decide_eq_false_iff_not]
  omega

/-- **`path_fold` is `foldPath`** when each node is the statement's on the children's bytes. -/
theorem pathFold_eq {n : Nat} (nodeB : Nat → Nat → List UInt8 → List UInt8)
    (nodeS : Nat → Nat → HashInput → Id Digest) (e : Nat) (path : Fin n → Digest) (leaf : Digest)
    (hnode : ∀ l < n, ∀ a b : Digest, nodeB (l + 1) (e >>> (l + 1)) (le16 a ++ le16 b) =
      le16 (Id.run (nodeS l (e / 2 ^ (l + 1)) (nodePayload a b)))) :
    pathFold (le16 leaf) e (List.ofFn fun j ↦ le16 (path j)) nodeB =
      le16 (Id.run (foldPath nodeS e (fun l ↦ if h : l < n then path ⟨l, h⟩ else 0) n leaf)) := by
  suffices key : ∀ j, j ≤ n →
      (List.range j).foldl (fun current z ↦
        nodeB (z + 1) (e >>> (z + 1))
          (if e >>> z &&& 1 = 0
            then current ++ (List.ofFn fun j ↦ le16 (path j)).getD z []
            else (List.ofFn fun j ↦ le16 (path j)).getD z [] ++ current)) (le16 leaf) =
      le16 (Id.run (foldPath nodeS e (fun l ↦ if h : l < n then path ⟨l, h⟩ else 0) j leaf)) by
    rw [pathFold, List.length_ofFn]
    exact key n le_rfl
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega),
      foldPath, Id.run_bind]
    have hjn : j < n := by omega
    have hsib : (List.ofFn fun j ↦ le16 (path j)).getD j [] = le16 (path ⟨j, hjn⟩) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hjn),
        Option.getD_some, List.getElem_ofFn]
    rw [hsib, dite_eq_left hjn]
    cases hb : e.testBit j
    · rw [ite_eq_left (and_one_iff.mpr hb), ite_eq_right Bool.false_ne_true]
      exact hnode j hjn _ _
    · rw [ite_eq_right (fun h ↦ absurd (and_one_iff.mp h) (by rw [hb]; decide)),
        ite_eq_left (rfl : true = true)]
      exact hnode j hjn _ _

/-- **`tree_fold` is the statement's fold up the key's tree**, its path of `n ≤ 10` nodes. -/
theorem treeFold_eq (seed : PublicParameter) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) {key : OtsKey} (hl : key.layer = layer.val)
    (ht : key.tree.toNat = tree.val) (hf : key.leaf.toNat = leaf.val) {n : Nat} (hn : n ≤ 10)
    (path : Fin n → Digest) (v : Digest) :
    treeFold (littleEndianBytes 16 seed) key (le16 v) (List.ofFn fun j ↦ le16 (path j)) =
      le16 (Id.run (Verification.treeFold (m := Id) LeanVM.Semantics.keccakF1600 seed layer tree
        leaf (fun l ↦ if h : l < n then path ⟨l, h⟩ else 0) n v)) := by
  rw [treeFold, hf]
  refine pathFold_eq _ _ _ _ _ fun l hl' a b ↦ ?_
  have hlf : leaf.val < 1024 := leaf.isLt
  rw [node, OtsKey.treeAdrs_eq, withType_eq, withTreeHeight_eq, withTreeIndex_eq,
    th_adrs seed _ (aty := .tree) (by rw [hl, layer_toUInt32]) ht rfl rfl
      (by rw [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)])
      (by rw [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.shiftRight_eq_div_pow,
        Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))])]
  rfl

/-! ## FORS -/

/-- The fields of a FORS address. -/
theorem forsNodeAdrs_eq (idx : UInt64) (c z j : Nat) :
    forsNodeAdrs idx c z j = adrsBytes (0 : Nat).toUInt32 (OtsKey.ofIndex 0 idx).tree 3
      (OtsKey.ofIndex 0 idx).leaf z.toUInt32 ((c <<< (10 - z)) + j).toUInt32 := by
  rw [forsNodeAdrs, forsAdrs, OtsKey.adrs_eq, withTreeHeight_eq, withTreeIndex_eq, ofIndex_layer]

/-- **`fors_recover` is the statement's FORS key** of the opening at the leaves. -/
theorem forsRecover_eq (seed : PublicParameter) {idx : UInt64} {index : Index}
    (h : idx.toNat = index.val) (leaves : ForsTreeIndex → ForsLeafIndex)
    (op : ForsTreeIndex → _root_.Sphincs.ForsTreeOpening) :
    forsRecover (littleEndianBytes 16 seed) idx (List.ofFn fun c ↦ (leaves c).val)
        (List.ofFn fun c ↦ ⟨le16 (op c).secret, List.ofFn fun z ↦ le16 ((op c).path z)⟩) =
      le16 (Id.run (Verification.forsRecover (m := Id) LeanVM.Semantics.keccakF1600 seed index
        leaves op)) := by
  have ht0 : (OtsKey.ofIndex 0 idx).tree.toNat = (treeOfIndex 0 index).val := ofIndex_tree 0 h
  have hf0 : (OtsKey.ofIndex 0 idx).leaf.toNat = (leafOfIndex 0 index).val := ofIndex_leaf 0 h
  have hroots : ((List.range 24).map fun c ↦
      pathFold (forsLeaf (littleEndianBytes 16 seed) idx c
        ((List.ofFn fun c ↦ (leaves c).val).getD c 0)
        ((List.ofFn fun c ↦ (⟨le16 (op c).secret, List.ofFn fun z ↦ le16 ((op c).path z)⟩ :
          ForsTreeOpening)).getD c ⟨[], []⟩).secret)
        ((List.ofFn fun c ↦ (leaves c).val).getD c 0)
        ((List.ofFn fun c ↦ (⟨le16 (op c).secret, List.ofFn fun z ↦ le16 ((op c).path z)⟩ :
          ForsTreeOpening)).getD c ⟨[], []⟩).path
        fun z j pair ↦ forsNode (littleEndianBytes 16 seed) idx c z j pair) =
      List.ofFn fun c : ForsTreeIndex ↦ le16 (Id.run (Verification.forsTreeRecover (m := Id)
        LeanVM.Semantics.keccakF1600 seed index c (leaves c) (op c))) := by
    apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_ofFn]; rfl)
    intro c h1 h2
    have hc : c < 24 := by simpa using h1
    have hl : (List.ofFn fun c ↦ (leaves c).val).getD c 0 = (leaves ⟨c, hc⟩).val := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hc), Option.getD_some,
        List.getElem_ofFn]
    have ho : (List.ofFn fun c ↦ (⟨le16 (op c).secret, List.ofFn fun z ↦ le16 ((op c).path z)⟩ :
        ForsTreeOpening)).getD c ⟨[], []⟩ =
        ⟨le16 (op ⟨c, hc⟩).secret, List.ofFn fun z ↦ le16 ((op ⟨c, hc⟩).path z)⟩ := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact hc), Option.getD_some,
        List.getElem_ofFn]
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn, hl, ho]
    have hs := (leaves ⟨c, hc⟩).isLt
    unfold forsTreeHeight at hs
    have hleaf : forsLeaf (littleEndianBytes 16 seed) idx c (leaves ⟨c, hc⟩).val
        (le16 (op ⟨c, hc⟩).secret) = le16 (Id.run (Verification.forsLeafHash (m := Id)
          LeanVM.Semantics.keccakF1600 seed index ⟨c, hc⟩ (leaves ⟨c, hc⟩) (op ⟨c, hc⟩).secret)) := by
      rw [forsLeaf, forsNodeAdrs_eq, th_adrs seed _ (aty := .forsTree) rfl ht0 rfl hf0 rfl
        (by rw [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by
          rw [Nat.shiftLeft_eq]; omega), Nat.shiftLeft_eq])]
      rfl
    rw [hleaf]
    unfold Verification.forsTreeRecover
    rw [Id.run_bind]
    refine pathFold_eq _ _ _ _ _ fun l hl' a b ↦ ?_
    unfold forsTreeHeight at hl'
    rw [forsNode, forsNodeAdrs_eq, th_adrs seed _ (aty := .forsTree) rfl ht0 rfl hf0
      (by rw [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega)])
      (by rw [Nat.toUInt32_eq, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by
          rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
          have : (leaves ⟨c, hc⟩).val / 2 ^ (l + 1) < 2 ^ 10 :=
            lt_of_le_of_lt (Nat.div_le_self _ _) hs
          have : 2 ^ (10 - (l + 1)) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by omega) (by omega)
          nlinarith), Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow])]
    rfl
  rw [forsRecover, hroots, forsKey, forsAdrs, OtsKey.adrs_eq,
    th_adrs seed _ (aty := .forsRoots) rfl ht0 rfl hf0 rfl rfl, flatten_ofFn,
    Verification.forsRecover, Id.run_bind, Native.XmssVerifier.sequenceFin_id]
  rfl

end NativeRustc.Sphincs
